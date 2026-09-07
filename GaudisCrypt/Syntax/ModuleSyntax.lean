import GaudisCrypt.Syntax.ProgramSyntax
import GaudisCrypt.Language.Modules

open GaudisCrypt

/-!
# Concrete syntax for modules

Surface syntax for module types (`procmod`, `×ₘ`, `→ₘ`), for the `moduletype` and `module`
commands, and the tactics the commands use in the proofs they emit.  Program and procedure
syntax is in `ProgramSyntax.lean`.

## Module types — `moduletype Name { … }`

A top-level command declaring a record-like module type, e.g.:
```
moduletype TwoProcs {
  proc enc (Nat, Nat) -> Bool;
  module aux : ModuleTypeRep.arr (ModuleTypeRep.proc (procsig (Nat) -> Nat)) ModuleTypeRep.unit;
}
```
where each field's type is a `ModuleTypeRep`.  A field may also be written `proc fᵢ (A₁, …) -> R;` as
shorthand for `module fᵢ : ModuleTypeRep.proc (procsig (A₁, …) -> R);`.  It generates `Name`
(the corresponding `Module`), a record `Name.Structure` with fields `fᵢ : Module Tᵢ` — a `proc`
field getting the `Module.Proc (procsig …)` spelling of that, the one a `module`-declared procedure
carries — accessors `Name.fᵢ`, a constructor `Name.mk`, a destructor `Name.structure`, and
round-trip `@[simp]` lemmas relating them.
-/

namespace GaudisCrypt

/-! ### Module type of a procedure — `procmod (…) -> R`

`procmod (T, …) -> R` is `Module.Proc (procsig (T,…) -> R)`: the same surface as `proctype`, but
producing the *module* type of a procedure rather than the `Procedure` type.  It is a `Type`, and
so composes with the other module type formers (`Module.Arr`/`→ₘ`, `Module.Prod`/`×ₘ`), not with
the `ModuleTypeRep` constructors — for a type rep write `.proc (procsig (…) -> R)`.

The return type is parsed at precedence `36`, above the usual infix operators, so a trailing one
groups as `(procmod (…) -> R) ⊙ …` rather than folding into `R`.  A product/function *return* type
therefore needs parentheses: `procmod (…) -> (A × B)`.  (No `uses` clause: for a
procedure-with-holes module type write `ModuleTypeRep.arr` explicitly.) -/

syntax "procmod " "(" term,* ")" (" → " <|> " -> ") term:36 : term

macro_rules
  | `(procmod ( $params:term,* ) → $ret:term) => `(procmod ( $params,* ) -> $ret)
  | `(procmod ( $params:term,* ) -> $ret:term) =>
      `(_root_.GaudisCrypt.Module.Proc (procsig ( $params,* ) -> $ret))

open Lean PrettyPrinter in
@[app_unexpander _root_.GaudisCrypt.Module.Proc]
def unexpandProcMod : Unexpander
  | `($_ $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      `(procmod ( $ps,* ) → $r)
  | _ => throw ()

end GaudisCrypt

open GaudisCrypt

/-! ## Concrete syntax for module types

`M →ₘ N` is `Module.Arr M N` and `M ×ₘ N` is `Module.Prod M N`: the arrow and the product on the
*types* of modules (`Module T`, a name declared by `moduletype`, …), each side classified by an
`IsModule` instance.  Precedences mirror `→`/`×`: `×ₘ` (35) binds tighter than `→ₘ` (25), both
right-associative.  Both are `scoped` to `GaudisCrypt`, so `open`ing that namespace activates them.

`procmod (…) -> R` is the third of them: the module type `Module.Proc (procsig (…) -> R)`.

`ModuleTypeRep` itself has no infix notation; its constructors are written
`.proc`/`.arr`/`.prod`/`.unit` by dot notation. -/
namespace GaudisCrypt
scoped infixr:35 " ×ₘ " => _root_.GaudisCrypt.Module.Prod
scoped infixr:25 " →ₘ " => _root_.GaudisCrypt.Module.Arr
end GaudisCrypt

/-! ## Reporting what a command declared

`moduletype` and `module` both emit a whole batch of declarations from one command.  `logDeclared`
is the shared way of telling the user what they were: an info message listing every generated name
as a link that inserts `#check <name>` after the command.  It lives here, ahead of both commands,
because `moduletype` (below) is the first user. -/
namespace GaudisCrypt.ModuleDecl

open Lean Elab Command

/-- A link that inserts `suggestion` over `range` and then moves the cursor to `newSelection`.
Same idea as `Lean.Meta.Hint.textInsertionWidget` — whose link text is fixed to `[apply]` and
which leaves the cursor where it was — and as ProofWidgets' `MakeEditLink`, which needs the
document's URI up front; here it is read from the infoview's position context instead. -/
@[widget_module]
def insertLinkWidget : Widget.Module where
  javascript := "
import * as React from 'react';
import { EditorContext, EnvPosContext } from '@leanprover/infoview';

const e = React.createElement;
export default function ({ range, suggestion, newSelection, hoverText, linkText }) {
  const pos = React.useContext(EnvPosContext)
  const ec = React.useContext(EditorContext)
  async function onClick() {
    await ec.api.applyEdit({ changes: { [pos.uri]: [{ range, newText: suggestion }] } })
    if (newSelection) await ec.revealLocation({ uri: pos.uri, range: newSelection })
  }
  return e('span', {
      onClick,
      title: hoverText,
      className: 'link pointer dim font-code',
      style: { color: 'var(--vscode-textLink-foreground)' }
    },
    linkText)
}"

/-- The width of `s` in UTF-16 code units — what LSP positions count in. -/
private def utf16Width (s : String) : Nat := s.foldl (fun w c => w + c.utf16Size.toNat) 0

/-- Report the declarations a `module`/`moduletype` command generated, as
```
Defined:
  X.g.procedure — body of proc g
```
where each *name* is a link that inserts `#check <name>` right after the command and puts the
cursor at the end of the inserted line (the same edit is also offered as a code action).
`declared` pairs each name with a short description of what it is. -/
def logDeclared (ref : Syntax) (declared : Array (Name × String)) : CommandElabM Unit := do
  if declared.isEmpty then return
  -- the edit's range is empty and sits at the command's tail, so applying it *inserts* the
  -- `#check` on the following line rather than overwriting anything
  let some tailPos := ref.getTailPos? | return
  let range : Lean.Syntax.Range := ⟨tailPos, tailPos⟩
  let lspRange := (← getFileMap).utf8RangeToLspRange range
  let mut msg : MessageData := "Defined:"
  for (n, descr) in declared do
    let line := s!"#check {n}"
    let newText := "\n" ++ line
    let title := s!"Insert `{line}`"
    -- end of the inserted line: one line below the command, past the text just written
    let caret : Lsp.Position := ⟨lspRange.start.line + 1, utf16Width line⟩
    -- the code-action (lightbulb) counterpart of the link
    pushInfoLeaf <| .ofCustomInfo {
      stx := Syntax.ofRange (ref.getRange?.getD range)
      value := Dynamic.mk ({ edit := { range := lspRange, newText := newText }
                             codeActionTitle := title
                             suggestion := { suggestion := newText } } :
                           Lean.Meta.Tactic.TryThis.TryThisInfo) }
    let link : MessageData := .ofWidget
      { id := ``insertLinkWidget
        javascriptHash := insertLinkWidget.javascriptHash
        props := return json%
          { range: $(lspRange),
            suggestion: $(newText),
            newSelection: $(({ start := caret, «end» := caret } : Lsp.Range)),
            hoverText: $(title),
            linkText: $(n.toString) } }
      n.toString
    msg := msg ++ m!"\n• {link} — {descr}"
  msg := msg ++ "\n\n(Click to insert `#check symbolname`.)"
  logInfoAt ref msg

end GaudisCrypt.ModuleDecl

/-! ## Lean parameters of a `module`/`moduletype` declaration

Both commands take, after the name, a list of ordinary Lean binders — types, values, implicit and
instance arguments — exactly as `def` and `theorem` do:
```
moduletype Sized (n : Nat) { proc f (Fin n) -> Bool; }
module Twice (n : Nat) using (S : Sized n) { … }
```
Every declaration the command generates is abstracted over those binders, and every reference one
generated declaration makes to another passes them along by name (`X.typeRep (n := n)`, so that
implicit and instance parameters travel too).  That is the whole of the semantics: a parameterised
declaration is the declaration it would be with those binders written on it by hand.

A parameter may also come from a section `variable`, and then need not be written at all:
```
variable (n : Nat)

moduletype Sized { proc f (Fin n) -> Bool; }
module Twice using (S : Sized n) { … }
```
means the same as the pair above.  A section variable the declaration mentions anywhere — in a
field type, in a procedure body, in a module parameter's type — becomes a Lean parameter of it,
in front of the ones it writes itself, together with the variables it depends on and the instance
variables that are about them (`variable {α} [Inhabited α]`; using `α` brings the instance too).
Lean's own auto-inclusion is left the variables no declaration of the batch mentions,
`[ProgramSpec]` and its like: it works per declaration, by use, and the generated declarations of
one command refer to one another and so all have to take the same parameters.

The *module* parameters are a different thing and are now written after `using`.  They used to be
written in the same position as the Lean parameters are, and they look like a Lean binder list
that got a comma in it — which is not valid Lean binder syntax.  Rather than let that fail in the
parser with a message about the comma, `gaudi_param` parses such a group and the commands reject it
themselves, pointing at `using`.  A single module parameter, `(S : CommitmentScheme)`, *is* valid
Lean binder syntax and so parses as a Lean parameter; that is a warning (`linter.gaudisCrypt.using`,
below), not an error, since a module-typed Lean parameter is a legitimate — if unusual — thing to
want. -/

open Lean Parser Term in
/-- `Lean.Parser.Term.bracketedBinder` under a name that `syntax` will accept: the core one is not
tagged for use in generated parsers ("refusing to generate code for imported parser declaration"),
and the attribute is what makes an alias of it usable. -/
@[run_parser_attribute_hooks] def gaudiBinder : Parser := bracketedBinder

/-- One entry of a `module`/`moduletype` parameter list: an ordinary Lean binder, or a
parenthesised comma-separated group, which is only ever the old spelling of *module* parameters
and exists here to be rejected with a message naming `using`. -/
declare_syntax_cat gaudi_param

syntax (name := gaudiParamBinder) gaudiBinder : gaudi_param
syntax (name := gaudiParamGroup) "(" proc_binder ("," proc_binder)+ ")" : gaudi_param

register_option linter.gaudisCrypt.using : Bool := {
  defValue := true
  descr := "(GaudisCrypt) warn when the last Lean parameter of a `module` declaration has a \
module type (`IsModule`), which usually means `using` was meant instead"
}

namespace GaudisCrypt.ModuleDecl

open Lean Elab Command Meta Term

/-- The binder syntax of a `gaudi_param` list, with the comma groups rejected.  `what` names the
command, for the error message. -/
def paramBinders (what : String) (ps : Array (TSyntax `gaudi_param)) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :=
  ps.mapM fun (p : TSyntax `gaudi_param) =>
    if p.raw.getKind == ``gaudiParamBinder then
      pure ⟨p.raw[0]!⟩
    else
      throwErrorAt p
        s!"{what}: a comma-separated group is not a Lean parameter list.  If these are the \
module parameters, write them after `using`."

/-- A binder one of the commands invents for itself — the module an accessor takes, the record
`mk` takes, and so on.  Hygienic, so that a Lean parameter of the same name cannot capture it: the
generated declarations refer to these binders by name, and a user parameter called `m` used to
shadow the module binder in `def X.gen (m : Nat) (m : X (m := m)) : … (Fin (m+1))`, whereupon the
field type read the module where it wanted the number and the whole batch failed from there.

The names are also spelled out rather than single letters, which is a separate matter from the
capture: these are what shows up in every `#check` of a generated declaration and in every goal
one appears in, and the delaborator strips the macro scopes again, so what a reader sees is
`theRecord`, not `theRecord✝`.  Renaming alone would only have moved the collision to a less
likely name; hygiene alone would have left the single letters on display. -/
def internalIdent (base : Name) : CommandElabM Ident :=
  return mkIdent (← MonadQuotation.addMacroScope base)

/-- A name for an anonymous binder position. -/
private def freshParamName (i : Nat) : Ident := mkIdent (Name.mkSimple s!"_gaudiParam{i}")

/-- The Lean parameters of a `module`/`moduletype` declaration: the binders every generated
declaration is abstracted over, and the names that pass them from one to the next. -/
structure LeanParams where
  /-- The binders, every position named (see `nameParams`). -/
  binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  /-- Their names, in order. -/
  args : Array Ident := #[]

/-- Give every binder position a name, and return the binders so named together with the arguments
that pass them on.  A reference from one generated declaration to another names each parameter, so
it needs a name even for the positions the user left anonymous (`[Inhabited α]`, `(_ : T)`). -/
def nameParams (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    CommandElabM LeanParams := do
  let mut out : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  let mut args : Array Ident := #[]
  let mut n := 0
  for b in bs do
    let k := b.raw.getKind
    if k == ``Lean.Parser.Term.instBinder then
      let opt := b.raw[1]
      if opt.getNumArgs == 0 then
        let id := freshParamName n
        n := n + 1
        let ty : Term := ⟨b.raw[2]⟩
        out := out.push (← `(bracketedBinder| [$id : $ty]))
        args := args.push id
      else
        out := out.push b
        args := args.push ⟨opt[0]⟩
    else if k == ``Lean.Parser.Term.explicitBinder || k == ``Lean.Parser.Term.implicitBinder ||
        k == ``Lean.Parser.Term.strictImplicitBinder then
      let mut ids : Array Syntax := #[]
      for idStx in b.raw[1].getArgs do
        if idStx.isIdent then
          ids := ids.push idStx
          args := args.push ⟨idStx⟩
        else
          let id := freshParamName n
          n := n + 1
          ids := ids.push id.raw
          args := args.push id
      out := out.push ⟨b.raw.setArg 1 (Syntax.node .none nullKind ids)⟩
    else
      throwErrorAt b "module: unsupported parameter binder"
  return { binders := out, args }

/-- Does `s` mention one of the identifiers `names`?  A name also counts as mentioned when it heads
a field access (`types.Value` is one identifier, not two). -/
partial def mentions (names : List Name) (s : Syntax) : Bool :=
  if s.isIdent then names.any fun n => n == s.getId || n.isPrefixOf s.getId
  else s.getArgs.any (mentions names)

/-- The section variables (`variable (types : CommitmentTypes)`) that a declaration written as
`stx` uses, to go in front of the parameters `own` it writes itself: the ones whose names `stx`
mentions, the ones those in turn mention, and the instance variables among them that are about
variables already taken.  A variable whose name `own` binds is left alone — the written binder
wins.

The section variables a declaration uses have to *become* Lean parameters of it rather than be
left to Lean's own auto-inclusion, because a `module`/`moduletype` is a batch of declarations that
refer to one another by name (`X.typeRep (types := types)`): auto-inclusion puts a variable only
in those declarations whose body happens to mention it, and a reference from one of the batch to
another would then be missing an argument.  Only the variables that no declaration of the batch
takes a stand on — `[ProgramSpec]` and its like, mentioned by none of them — are left to it. -/
def sectionBinders (stx : Syntax) (own : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let vars := (← getScope).varDecls
  if vars.isEmpty then return #[]
  let ownNames ← own.flatMapM fun b => getBracketedBinderIds b.raw
  -- what each section binder declares, without the anonymous positions (`[Inhabited α]`) and
  -- without the names the declaration binds itself
  let names ← vars.mapM fun b => return (← getBracketedBinderIds b.raw).toList.filter fun n =>
    n != .anonymous && !ownNames.contains n
  let mut used := vars.map fun _ => false
  for i in [0 : vars.size] do
    if !names[i]!.isEmpty && mentions names[i]! stx then used := used.set! i true
  -- a used variable drags in the ones its own type mentions, and an instance variable comes along
  -- with the variables it is about; either can uncover more, hence the fixpoint
  for _ in [0 : vars.size] do
    let mut changed := false
    for i in [0 : vars.size] do
      let isInst := vars[i]!.raw.getKind == ``Lean.Parser.Term.instBinder
      for j in [0 : vars.size] do
        if i == j || names[j]!.isEmpty || !mentions names[j]! vars[i]!.raw then continue
        if used[i]! && !used[j]! then
          used := used.set! j true
          changed := true
        if used[j]! && !used[i]! && isInst then
          used := used.set! i true
          changed := true
    unless changed do break
  return (Array.range vars.size).filterMap fun i => if used[i]! then some vars[i]! else none

/-- How a generated declaration refers to another one: bare when there are no parameters, and
`X.f (a₁ := a₁) … (aₙ := aₙ)` when there are.  *Named* arguments, not `@`: `@` would also expose
the section variables auto-included in the referenced declaration (`[ProgramSpec]` and friends),
which are none of this command's business, while a name reaches an implicit or instance parameter
without disturbing them. -/
def LeanParams.ref (P : LeanParams) (id : Ident) : CommandElabM Term := do
  if P.args.isEmpty then return id
  let named : Array (TSyntax ``Lean.Parser.Term.namedArgument) ←
    P.args.mapM fun a => `(Lean.Parser.Term.namedArgument| ($a := $a))
  `($id $(named.map fun a => (⟨a.raw⟩ : Term))*)

/-- Run `k` with the Lean parameters in the local context, so that a term mentioning them (a
procedure body, a signature to be read back) can be elaborated. -/
def LeanParams.withBinders {α} (P : LeanParams) (k : TermElabM α) : TermElabM α :=
  Term.elabBinders (P.binders.map (·.raw)) fun _ => k

/-- Warn when the last Lean parameter of a `module` declaration has a module type, which almost
always means the module parameters were written without `using`.  Silent when the declaration has a
`using` clause (the author has then clearly chosen), and suppressed by
`set_option linter.gaudisCrypt.using false`. -/
def warnModuleTypedParam (P : LeanParams) : CommandElabM Unit := do
  let bs := P.binders
  unless (← getOptions).get linter.gaudisCrypt.using.name true do return
  let some last := bs.back? | return
  unless last.raw.getKind == ``Lean.Parser.Term.explicitBinder do return
  unless last.raw[1].getNumArgs == 1 && last.raw[2].getNumArgs == 2 do return
  let x : Term := ⟨last.raw[1][0]⟩
  let ty : Term := ⟨last.raw[2][1]⟩
  let isMod ← runTermElabM fun _ => do
    try
      Term.elabBinders (bs.pop.map (·.raw)) fun _ => do
        let tyE ← Term.elabType ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let cls ← mkAppM ``GaudisCrypt.IsModule #[← instantiateMVars tyE]
        return (← synthInstance? cls).isSome
    catch _ => return false
  if isMod then
    logWarningAt last m!"module: the Lean parameter `{x}` has a module type ({ty}).  If it is \
meant to be a module parameter, write it after `using`.\n\n\
Disable this warning with `set_option linter.gaudisCrypt.using false`."

end GaudisCrypt.ModuleDecl

/-- Proves the `apply_simp` field of the `X.f.utilities : ModuleTypeUtilities …` that `moduletype`
emits for each field — `∀ m, Module.app accessorModule m = X.f m`, relating the accessor *as a
module* (a projection `.abs` of `ModuleExpression`s) to the accessor *as a Lean function* (a chain
of `Module.fst'`s and `Module.snd'`s).  `acc` is the accessor, unfolded by name; the module needs no
name, being the sibling field's value and hence already inlined in the goal.

Same shape as `module_apply`: normalise both sides.  Unfolding `acc` and the `Module`-level
combinators leaves `ModuleExpression`s under `.reduce`; the stripping lemmas remove the inner
`.reduce`s that `toModule` left behind, exposing the β-redex `.app (.abs proj) m.expression`, and
`reduce_simp` takes it.  The two trailing steps are `try`: for the *single-field* case the accessor
is the identity, the first `simp only` already closes the goal, and a bare `reduce_simp` would then
fail with "no goals". -/
syntax "accessor_apply " ident : tactic

macro_rules
  | `(tactic| accessor_apply $acc:ident) =>
    `(tactic|
        (intro _
         simp only [$acc:ident]
         apply GaudisCrypt.Module.ext
         simp only [GaudisCrypt.Module.app, GaudisCrypt.Module.app',
           GaudisCrypt.Module.fst, GaudisCrypt.Module.fst',
           GaudisCrypt.Module.snd, GaudisCrypt.Module.snd',
           GaudisCrypt.Module.moduleTypeRep, GaudisCrypt.ModuleExpression.toModule,
           GaudisCrypt.ModuleExpression.reduce_app_left,
           GaudisCrypt.ModuleExpression.reduce_app_right,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]
         try reduce_simp
         try simp only [GaudisCrypt.Module.reduce_expression,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]))

/-- Proves the `expression_eq` field of `X.f.utilities` — `∀ m, (X.f m).expression =
(proj m.expression).reduce`, the accessor read at the level of expressions.  `acc` is the accessor.

No normalisation here, only unfolding: `Module.fst'`/`snd'` are `toModule`s of the projection, and
each of them leaves a `.reduce` *inside* the next, which the two stripping lemmas pull out until
what is left is one `.reduce` of the whole chain — the right-hand side.  `Module.reduce_expression`
is for the single-field case, where the chain is empty and the two sides differ by exactly the
outermost `.reduce`. -/
syntax "accessor_expression " ident : tactic

macro_rules
  | `(tactic| accessor_expression $acc:ident) =>
    `(tactic|
        (intro _
         simp only [$acc:ident, GaudisCrypt.Module.cast,
           GaudisCrypt.Module.fst', GaudisCrypt.Module.snd',
           GaudisCrypt.ModuleExpression.toModule, GaudisCrypt.Module.reduce_expression,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]))

/-- A field `f : Module T` of a `moduletype` declaration. -/
/- A field of a `moduletype` declaration: either `module f : T;` (explicit module type)
or the shorthand `proc f (T₁, …) -> R;` (a procedure field). -/
declare_syntax_cat moduletypeField
syntax "module " ident " : " term ";" : moduletypeField
syntax "proc " ident " (" term,* ")" (" → " <|> " -> ") term ";" : moduletypeField

/-- `moduletype Name { module f₁ : T₁; … ; module fₙ : Tₙ }` declares a record-like module
type, where each `Tᵢ` is a `ModuleTypeRep`.  A field may also be written
`proc fᵢ (A₁, …) -> R;`, shorthand for `module fᵢ : ModuleTypeRep.proc (procsig (A₁, …) -> R);`.
It expands to: `Name := Module (ModuleTypeRep.prod T₁ (… Tₙ))` (right-nested product of the
field types), a record `Name.Structure` with fields `fᵢ : Module Tᵢ` — written `Module.Proc sig`
for a `proc` field, so that the record and the procedures a `module` declaration puts into it are
stated in the same terms, which is what lets `simp` chain `X.apply_simp` into `X.f.apply_simp` —
accessors `Name.fᵢ`
(via `Module.fst'`/`Module.snd'`), a constructor `Name.mk`, a destructor `Name.structure`, and
the two round-trip `@[simp]` lemmas `Name.mk_destruct` / `Name.destruct_mk`.

What is derivable about an accessor goes into a single `Name.fᵢ.utilities :
ModuleTypeUtilities …` per field — the accessor as a *module* (a projection is a module morphism),
`Name.fᵢ.utilities.accessorModule : Name →ₘ Tᵢ`, plus `…utilities.apply_simp`
(`Module.app …accessorModule m = Name.fᵢ m`) and `…utilities.expression_eq` (the accessor at the
level of expressions: `(Name.fᵢ m).expression = (proj m.expression).reduce`).  Bundling them keeps
one name per field in the namespace instead of one per fact.

`Name` may take ordinary Lean parameters, written as for a `def`:
`moduletype Sized (n : Nat) { proc f (Fin n) -> Bool; }`.  Every declaration above is then
abstracted over them and refers to its siblings with them applied (see the section on Lean
parameters).

Everything it declares is reported by `logDeclared`. -/
-- `atomic`, because an implicit parameter `{α : Type}` and the `{ … }` body start with the same
-- token: without it the parser commits to reading the body as one more parameter
syntax "moduletype " ident (atomic(ppSpace gaudi_param))* "{" moduletypeField* "}" : command

open Lean Elab Command GaudisCrypt.ModuleDecl in
elab_rules : command
  | `(moduletype $nm:ident $params:gaudi_param* { $fields:moduletypeField* }) => do
      let n := fields.size
      if n == 0 then throwError "moduletype needs at least one field"
      let ownBs ← paramBinders "moduletype" params
      let P ← nameParams ((← sectionBinders (← getRef) ownBs) ++ ownBs)
      let bs := P.binders
      -- per field: the field name and its `ModuleTypeRep`
      let fns ← fields.mapM fun f => match f with
        | `(moduletypeField| module $fn:ident : $_ ;)         => pure fn
        | `(moduletypeField| proc $fn:ident ( $_,* ) -> $_ ;) => pure fn
        | `(moduletypeField| proc $fn:ident ( $_,* ) → $_ ;)  => pure fn
        | _ => throwUnsupportedSyntax
      let Ts ← fields.mapM fun f => match f with
        | `(moduletypeField| module $_ : $T:term ;) => pure T
        | `(moduletypeField| proc $_ ( $ps,* ) -> $ret:term ;)
        | `(moduletypeField| proc $_ ( $ps,* ) → $ret:term ;) =>
            `(_root_.GaudisCrypt.ModuleTypeRep.proc (ProcedureSignature.mk [$ps,*] $ret))
        | _ => throwUnsupportedSyntax
      -- the field/accessor types are `Module Tᵢ` — except for a `proc` field, which gets the
      -- `Module.Proc sig` spelling of it, the one `module`-declared procedures carry (so that the
      -- record built by `mk` and the procedures put into it are stated in the same terms)
      let fts ← fields.mapM fun f => match f with
        | `(moduletypeField| module $_ : $T:term ;) => `(_root_.GaudisCrypt.Module $T)
        | `(moduletypeField| proc $_ ( $ps,* ) -> $ret:term ;)
        | `(moduletypeField| proc $_ ( $ps,* ) → $ret:term ;) =>
            `(_root_.GaudisCrypt.Module.Proc (ProcedureSignature.mk [$ps,*] $ret))
        | _ => throwUnsupportedSyntax
      -- right-nested product of the underlying types
      let prodT ← Ts.pop.foldrM
        (fun T acc => `(_root_.GaudisCrypt.ModuleTypeRep.prod $T $acc)) Ts.back!
      -- generated names
      let nb := nm.getId
      let structId := mkIdent (nb.str "Structure")
      let ctorId   := mkIdent ((nb.str "Structure").str "mk")
      let mkId     := mkIdent (nb.str "mk")
      let structFn := mkIdent (nb.str "structure")
      let moduleTypeId := mkIdent (nb.str "typeRep")
      let accIds   := fns.map fun f => mkIdent (nb ++ f.getId)
      let projId : Nat → Ident := fun i => mkIdent ((nb.str "Structure") ++ fns[i]!.getId)
      let mId ← internalIdent `theModule
      let sId ← internalIdent `theRecord
      -- how the generated declarations refer to one another: with the Lean parameters applied
      let typeRepR ← P.ref moduleTypeId
      let nmR      ← P.ref nm
      let structR  ← P.ref structId
      let ctorR    ← P.ref ctorId
      let mkR      ← P.ref mkId
      let structFnR ← P.ref structFn
      let accRs    ← accIds.mapM P.ref
      let projRs   ← (Array.range n).mapM fun i => P.ref (projId i)
      -- (1) `X.typeRep` names the underlying `ModuleTypeRep`; `X := Module X.typeRep`.  `X` is a
      -- plain (non-reducible) def, so the `IsModule (Module t)` instance does not apply to it and
      -- it gets its own — without which `X` could not appear in a `Module.Arr`/`Module.Prod`.
      elabCommand (← `(def $moduleTypeId $bs* : _root_.GaudisCrypt.ModuleTypeRep := $prodT))
      elabCommand (← `(def $nm $bs* := _root_.GaudisCrypt.Module $typeRepR))
      -- the instance is named explicitly with the very name Lean's own `mkInstanceName` would
      -- have invented for it (`instIsModuleX`), so that it can be reported below — the two cannot
      -- drift apart, since it is the same function that picks it
      let instTy ← `(_root_.GaudisCrypt.IsModule $nmR)
      let instId := mkIdent (← mkInstanceName (bs.map (·.raw)) instTy)
      elabCommand (← `(instance $instId:ident $bs* : $instTy where moduleTypeRep := $typeRepR))
      -- (2) the record structure
      elabCommand (← `(structure $structId $bs* where $[$fns:ident : $fts:term]*))
      -- (3) accessors: field `i` is `fst (snd^i m)`, or `snd^(n-1) m` for the last.  Beside the
      -- accessor `X.fᵢ` itself, what is derivable about it goes into one `X.fᵢ.utilities :
      -- ModuleTypeUtilities …` — the accessor as a *module* (a projection is a module morphism),
      -- and the two lemmas relating that module and the accessor's expression to the projection.
      -- One declaration per field, rather than one per fact.
      let utilIds := accIds.map fun a => mkIdent (a.getId.str "utilities")
      let eId ← internalIdent `theExpression
      for i in [0:n] do
        let accId := accIds[i]!
        let ft := fts[i]!
        let mut e : Term := mId
        let mut me ← `(_root_.GaudisCrypt.ModuleExpression.var 0)
        let mut pe : Term := eId
        for _ in [0:i] do
          e ← `(_root_.GaudisCrypt.Module.snd' $e)
          me ← `(_root_.GaudisCrypt.ModuleExpression.snd $me)
          pe ← `(_root_.GaudisCrypt.ModuleExpression.snd $pe)
        if i + 1 < n then
          e ← `(_root_.GaudisCrypt.Module.fst' $e)
          me ← `(_root_.GaudisCrypt.ModuleExpression.fst $me)
          pe ← `(_root_.GaudisCrypt.ModuleExpression.fst $pe)
        elabCommand (← `(@[module_accessor] noncomputable def $accId $bs* ($mId : $nmR) : $ft :=
          $e))
        elabCommand (← `(noncomputable def $(utilIds[i]!) $bs* :
            _root_.GaudisCrypt.ModuleTypeUtilities $nmR $ft $(accRs[i]!) where
          proj := fun $eId => $pe
          accessorModule := _root_.GaudisCrypt.ModuleExpression.toModule
            (m := _root_.GaudisCrypt.ModuleExpression.abs $me)
          apply_simp := by accessor_apply $accId
          expression_eq := by accessor_expression $accId))
      -- (4) constructor: right-nested `Module.pair`
      let mut mkBody : Term ← `($(projRs[n-1]!) $sId)
      for i in [0:n-1] do
        let j := n - 2 - i
        let pj := projRs[j]!
        mkBody ← `(_root_.GaudisCrypt.Module.pair' ($pj $sId) $mkBody)
      elabCommand (← `(@[reducible] noncomputable def $mkId $bs* ($sId : $structR) : $nmR :=
        $mkBody))
      -- (5) destructor
      let args ← (Array.range n).mapM fun i => do
        let accR : Term := accRs[i]!
        `($accR $mId)
      elabCommand (← `(noncomputable def $structFn $bs* ($mId : $nmR) : $structR :=
        $ctorR $args*))
      -- (6) / (7) round-trip lemmas
      let baseLemmas : Array Ident := #[mkId, structFn] ++ accIds
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "mk_destruct")) $bs*
          ($sId : $structR) :
          $structFnR ($mkR $sId) = $sId := by simp [$[$baseLemmas:ident],*]))
      let dmLemmas : Array Ident := baseLemmas.push (mkIdent `Module.pair_fst_snd')
      elabCommand (← `(@[simp] theorem $(mkIdent (nb.str "destruct_mk")) $bs* ($mId : $nmR) :
          $mkR ($structFnR $mId) = $mId := by simp [$[$dmLemmas:ident],*]))
      -- (8) report the batch, the same way the `module` command does
      let mut declared : Array (Name × String) :=
        #[(moduleTypeId.getId, "the underlying ModuleTypeRep"),
          (nb, "the module type itself"),
          (instId.getId, "its IsModule instance"),
          (structId.getId, "the record of its fields")]
      for i in [0:n] do
        declared := declared.push (accIds[i]!.getId, s!"the field {fns[i]!.getId}")
        declared := declared.push (utilIds[i]!.getId,
          s!"that field as a module, and the lemmas about it")
      declared := declared ++
        #[(mkId.getId, "the module built from a record"),
          (structFn.getId, "the record of a module's fields"),
          (nb.str "mk_destruct", "round-trip: destructing a built module"),
          (nb.str "destruct_mk", "round-trip: rebuilding a destructed module")]
      GaudisCrypt.ModuleDecl.logDeclared (← getRef) declared

/-! ## Module definitions — `module X … using (…) : T { proc f (…) : R { … }; … }`

```
module X using (A : Module.Arr TestModule (procmod () → Unit), B : TestModule) : M2 {
  proc g () : Unit {
    _ <- call (Module.app A myMod) ();
    _ <- call (myMod.main) ("hello", 5);
    return ();
  };
  proc h () : Unit { return (); };
}
```
declares a module `X` with module *parameters* `A`, `B` (the `using` clause is optional) whose
fields are the procedures `g`, `h`.  Procedure bodies use the ordinary statement syntax, except
that the callee of a `call` is a *module* (`Module.Proc sig`) rather than a bare `Procedure sig`.

Between the name and `using` come ordinary Lean parameters, as for a `def` — `module Twice (n : Nat)
using (S : CommitmentScheme) { … }`.  Every declaration listed below is abstracted over them and
refers to its siblings with them applied; see the section on Lean parameters.  They are a different
thing from the module parameters, which is why the latter now need `using` to introduce them: a
module parameter list is *almost* a Lean binder list, and one that happens to be exactly a Lean
binder list — a single `(S : CommitmentScheme)` — would otherwise be read as either at the parser's
whim.  Written without `using`, that is now a Lean parameter, with a warning
(`linter.gaudisCrypt.using`) saying so.

Elaboration is in two passes.  First the whole body of each procedure is type-checked *as
written* — with the module parameters in the local context and every callee in place (each callee
that mentions a parameter ascribed to `Module (.proc ?sig)`).  Only then, from the signatures that
this typing assigns to those `?sig`, is each procedure emitted as a constant
`X.<f>.procedure : ProcedureWithHoles …`, in which
* a `call` whose callee mentions a module parameter has become a **hole** (the callee, having
  done its job for typing, is dropped).  Two calls with the same callee syntax share one hole.
  The hole is named after that callee, `S.gen` giving the hole `S_gen`, so that a printed
  procedure still says which call each of its holes stands for;
* every other callee is a closed module expression, converted with `Module.Proc.procedure`.

Each procedure also gets a *module* `X.<f>`.  When it uses no module parameter that is simply
`Module.proc X.<f>.procedure`.  Otherwise it is curried over the parameters it does use, in
declaration order — `X.<f> : Module.Arr T₁ (… (Module.Arr Tₖ (Module.Proc sig)))` — as
`Module.procWithHoles X.<f>.procedure` applied to the tuple of its callees, under `k` `.abs`
binders.  The callees are *read back* from their elaborated form for this: each is either closed
(then it is used as it stands) or built from the parameters with `Module.app`/`fst`/`snd`/`pair`,
possibly after unfolding — a callee that is anything else has no `ModuleExpression` counterpart
and is rejected.

Finally `X` itself is the record of those procedures (a right-nested `.pair`, as `moduletype`
nests its fields), abstracted over *all* the parameters — used or not — which it takes as one
right-nested tuple: `X : Module.Arr (Module.Prod T₁ (… Tₙ)) M`, where `M` is the module type
written after the `:`, or `Module.Prod (Module.Proc sig₁) (… (Module.Proc sigₙ))` — the anonymous
record of the procedures' own types — when there is none.  With an empty parameter list that tuple
is `Module.Unit`; with no parameter list at all `X` is not a function but an `M`.

A declaration *with* a parameter list also gets the `@[simp]` lemma `X.apply_simp` for applying
`X`: `Module.app X (Module.pair A (… Z)) = M.mk { f₁ := Module.app X.f₁ A, … }`, i.e. the record of
the procedures, each applied to the parameters it uses (`Module.pair` in place of `M.mk` when `M`
is not a `moduletype` name).  So the two ways of instantiating a module — applying the record `X`
or applying the individual `X.f` — agree, by `simp`.

Every procedure gets one of its own, `X.<f>.apply_simp`, which carries the application all the way
down to a procedure: `Module.app (… (Module.app X.f A) …) Z = Module.proc
(X.f.procedure.instantiate …)`, the holes filled by the callees they were made from (each of them
as written, with the arguments in place of the module parameters).  A procedure with no holes uses
no parameter either, and the lemma is then just `X.f = Module.proc X.f.procedure`.

The last step — getting rid of the `instantiate` — is `X.<f>.procedure.apply_simp`, also `@[simp]`:
```
theorem X.f.procedure.apply_simp (args : ‹hole context›.Instantiation) :
    X.f.procedure.instantiate args = proc (x : T, …) : R { … }
```
whose right-hand side is the procedure as it was declared, only with each hole call written back as
an ordinary `call args ‹the hole's index›` (so the callees of the body appear as
`args HoleIndex.zero`, `args HoleIndex.zero.succ`, …, the last-declared hole being `.zero`).  After
`X.<f>.apply_simp` — and with `HoleSigs.Instantiation.push_zero`/`_succ` to look the indices up —
`simp` takes an application of `X` all the way to a hole-free `Procedure`. -/

/-- One procedure of a `module` declaration: `proc f (x : T, …) : R { … };`.  Same shape as
the `proc` *term* syntax (which it expands to), plus a name and a trailing `;`. -/
declare_syntax_cat gaudi_module_proc

-- the type ascriptions are parsed at `term:max` (as in the `proc` term syntax): a lower
-- precedence would let the type swallow the `{ … }` block that follows it as a structure instance
syntax "proc " ident "(" proc_binder,* ")" (" : " term:max)? "{"
         ("var" proc_binder,* ";")*
         gaudi_stmt*
         "return" term (";")?
       "}" (";")? : gaudi_module_proc

-- `atomic` on the Lean parameters, because an implicit one (`{α : Type}`) and the `{ … }` body
-- start with the same token: without it the parser commits to reading the body as one more
-- parameter
syntax "module " ident (atomic(ppSpace gaudi_param))*
         (ppSpace "using" " (" proc_binder,* ")")? (" : " term:max)? "{"
         gaudi_module_proc*
       "}" : command

/-- Proves `Module.app X (Module.pair A (… Z)) = <record of the procedures of X, applied to the
parameters each of them uses>` for the module `X` of a `module X (…) { … }` declaration — the
`X.apply_simp` lemma the command emits (`ModuleDecl.elabApplySimp`).  `X` must be given as its
name, which the script unfolds.

Both sides are `.reduce`s of concrete expressions, so this is a normalisation proof: unfold both
sides down to `ModuleExpression`s, normalise, compare.

* the first `simp only` unfolds — `X` itself, then the `Module`-level combinators, down to the
  `toModule`s they are built from.  The four `reduce_app_left`/`_right`/`reduce_pair_left`/`_right`
  (and the `fst`/`snd` variants) strip the `.reduce`s those `toModule`s leave behind *inside* a
  composite expression, which is what exposes the β-redex `.app (.abs body) (.pair …)` to the next
  step;
* `reduce_simp` then normalises: β, the substitution it produces, and the projections
  `.fst`/`.snd` of the argument tuple that the substitution puts in place;
* the last `simp only` finishes at the `Module` level, where `reduce_simp` cannot reach:
  `Module.substituteSimultaneously_expression` (a procedure's own expression is closed, so the
  substitution passes through it) and `Module.reduce_expression` (a module's expression is already
  normal) — `Module` is defined *after* `reduce_simp` in `Modules.lean`, so its simp set can't know
  either.  The stripping lemmas run once more, to put the `.reduce`s that surface here in the same
  places on both sides. -/
syntax "module_apply " ident : tactic

macro_rules
  | `(tactic| module_apply $x:ident) =>
    `(tactic|
        (apply GaudisCrypt.Module.ext
         simp only [$x:ident, GaudisCrypt.Module.app, GaudisCrypt.Module.app',
           GaudisCrypt.Module.pair, GaudisCrypt.Module.pair',
           GaudisCrypt.Module.fst, GaudisCrypt.Module.fst',
           GaudisCrypt.Module.snd, GaudisCrypt.Module.snd',
           GaudisCrypt.Module.moduleTypeRep, GaudisCrypt.ModuleExpression.toModule,
           GaudisCrypt.ModuleExpression.reduce_app_left,
           GaudisCrypt.ModuleExpression.reduce_app_right,
           GaudisCrypt.ModuleExpression.reduce_pair_left,
           GaudisCrypt.ModuleExpression.reduce_pair_right,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]
         reduce_simp
         simp only [GaudisCrypt.Module.substituteSimultaneously_expression,
           GaudisCrypt.Module.reduce_expression,
           GaudisCrypt.ModuleExpression.reduce_app_left,
           GaudisCrypt.ModuleExpression.reduce_app_right,
           GaudisCrypt.ModuleExpression.reduce_pair_left,
           GaudisCrypt.ModuleExpression.reduce_pair_right,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]))

/-- Discharges one component of the callee tuple in `proc_apply`: `c.reduce = m.expression`, where
`c` is the adapter expression the `module` command derived from the call site and `m` the callee
module itself.

Both sides are the same term up to `reduce`s sitting at *inner* positions, and `reduce ∘ reduce =
reduce` is propositional, not definitional — so `rfl` only works when the adapter is trivial:

* callee a bare module parameter (`c = B.expression`): `Module.reduce_expression`;
* callee a field of a module parameter (`c = S.expression.snd.snd`): the accessor `S.verify` is a
  chain of `Module.fst'`/`Module.snd'`, each of which wraps its argument in a `toModule`, i.e. in a
  `reduce`.  Unfolding the accessor — hence the `module_accessor` simp set, since its name is not
  known here — and pushing those `reduce`s out with `reduce_fst_inner`/`reduce_snd_inner` makes the
  two sides equal. -/
syntax "module_callee" : tactic

macro_rules
  | `(tactic| module_callee) =>
    `(tactic|
        (first
          | rfl
          | simp only [module_accessor, GaudisCrypt.Module.cast, GaudisCrypt.Module.cast',
              GaudisCrypt.Module.fst', GaudisCrypt.Module.snd',
              GaudisCrypt.ModuleExpression.toModule, GaudisCrypt.Module.reduce_expression,
              GaudisCrypt.ModuleExpression.reduce_fst_inner,
              GaudisCrypt.ModuleExpression.reduce_snd_inner]))

/-- Proves `Module.app (… (Module.app X.f A₁) …) Aₖ = Module.proc (X.f.procedure.instantiate …)`
for one procedure `f` of a `module X (…) { … }` declaration — the `X.f.apply_simp` lemma the
command emits (`ModuleDecl.elabProcApplySimp`).  `X.f` must be given as its name, which the script
unfolds.

Like `module_apply` this is a normalisation proof, but it ends at the δ-rule rather than at a
record: `X.f` is `Module.procWithHoles X.f.procedure` applied to the tuple of its callees, under
one `.abs` per parameter it uses.

* the first `simp only` unfolds `X.f` and the `Module`-level combinators down to `toModule`s, the
  stripping lemmas removing the `.reduce`s those leave inside a composite expression (as in
  `module_apply`);
* the loop then alternates `reduce_simp` with the `Module`-level rewrites it cannot do itself:
  β-reducing one parameter at a time leaves both a substitution and a `rename` (from `liftSubst`,
  going under the *next* binder) sitting on the argument's expression, and only
  `Module.substituteSimultaneously_expression`/`Module.rename_expression` — a module's expression
  being closed — get them out of the way so that the next redex becomes visible.  `Module` is
  defined after `reduce_simp` in `Modules.lean`, hence the alternation;
* what is left is `reduce (.app (Module.procWithHoles p).expression <tuple of callees>)`, which
  `Module.reduce_app_procWithHoles` turns into the instantiated procedure once its side goal — the
  tuple reduces to the instantiation's own tuple — is peeled off component by component with
  `Module.reduce_tuple_cons`, each component being discharged by `module_callee`. -/
syntax "proc_apply " ident : tactic

macro_rules
  | `(tactic| proc_apply $x:ident) =>
    `(tactic|
        (apply GaudisCrypt.Module.ext
         simp only [$x:ident, GaudisCrypt.Module.app, GaudisCrypt.Module.app',
           GaudisCrypt.Module.pair, GaudisCrypt.Module.pair',
           GaudisCrypt.Module.fst, GaudisCrypt.Module.fst',
           GaudisCrypt.Module.snd, GaudisCrypt.Module.snd',
           GaudisCrypt.Module.moduleTypeRep, GaudisCrypt.ModuleExpression.toModule,
           GaudisCrypt.ModuleExpression.reduce_app_left,
           GaudisCrypt.ModuleExpression.reduce_app_right,
           GaudisCrypt.ModuleExpression.reduce_pair_left,
           GaudisCrypt.ModuleExpression.reduce_pair_right,
           GaudisCrypt.ModuleExpression.reduce_fst_inner,
           GaudisCrypt.ModuleExpression.reduce_snd_inner]
         repeat (first
           | reduce_simp
           | simp only [GaudisCrypt.Module.substituteSimultaneously_expression,
               GaudisCrypt.Module.rename_expression, GaudisCrypt.Module.reduce_expression,
               GaudisCrypt.Module.proc, GaudisCrypt.Module.toModule_expression,
               GaudisCrypt.ModuleExpression.reduce_proc,
               GaudisCrypt.ModuleExpression.reduce_app_left,
               GaudisCrypt.ModuleExpression.reduce_app_right,
               GaudisCrypt.ModuleExpression.reduce_pair_left,
               GaudisCrypt.ModuleExpression.reduce_pair_right,
               GaudisCrypt.ModuleExpression.reduce_fst_inner,
               GaudisCrypt.ModuleExpression.reduce_snd_inner])
         refine GaudisCrypt.Module.reduce_app_procWithHoles _ _ _ ?_
         repeat (first
           | exact GaudisCrypt.Module.reduce_tuple_nil
           | refine GaudisCrypt.Module.reduce_tuple_cons _ _ _ _ ?_ ?_
           | module_callee)))

namespace GaudisCrypt.ModuleDecl

open Lean Elab Command Meta Term

/-- The positional name of the `i`-th generated hole.  Only a fallback: a hole is normally
named after the callee it stands for, see `holeIdentsOfCallees`. -/
def holeIdent (i : Nat) : Ident := mkIdent (Name.mkSimple s!"_hole{i}")

/-- `holeIdent` in callee position.  Used for the first, throw-away rewriting pass, the one
that only collects the callees — the names the holes end up with are made from those. -/
def holeCallee (i : Nat) : Term := holeIdent i

/-- Strip the redundant parentheses a callee is usually written with (`(S.gen)`).  A tuple and
a type ascription have kinds of their own, so only real parentheses are stripped. -/
partial def unparen (s : Syntax) : Syntax :=
  if s.getKind == ``Lean.Parser.Term.paren then unparen (s.getArg 1) else s

/-- The name a hole takes from the callee it was made from: that callee's own name with the
dots turned into underscores, `S.gen ↦ S_gen`.  `none` for a callee that is not a plain
identifier (an applied one, say), which then falls back to `holeIdent`. -/
def holeNameOfCallee? (callee : Term) : Option Name := do
  let raw := unparen callee.raw
  guard raw.isIdent
  let n := raw.getId
  guard !n.hasMacroScopes
  let cs ← n.components.mapM fun
    | .str .anonymous s => some s
    | _ => none
  guard !cs.isEmpty
  return Name.mkSimple (String.intercalate "_" cs)

/-- Names for the holes made from `callees`, in hole order.  A hole is named after its callee,
and the name is kept clear of `used` (the binders already in scope where the hole will be) and
of the other holes' names by appending `2`, `3`, … — two calls of `B.bind` on different
parameters give `B_bind` and `B_bind2`. -/
def holeIdentsOfCallees (used : Array Name) (callees : Array Term) : Array Ident := Id.run do
  let mut taken := used
  let mut out := #[]
  for i in [0 : callees.size] do
    let base := (holeNameOfCallee? callees[i]!).getD (holeIdent i).getId
    let mut nm := base
    let mut k := 2
    while taken.contains nm do
      nm := Name.mkSimple s!"{base}{k}"
      k := k + 1
    taken := taken.push nm
    out := out.push (mkIdent nm)
  return out

/-- The names a `proc_binder` declares (`x y : T` declares two). -/
def binderNames (b : TSyntax `proc_binder) : Array Ident :=
  match b with
  | `(proc_binder| $id:ident : $_:term) => #[id]
  | `(proc_binder| $id:ident $ids:ident* : $_:term) => #[id] ++ ids
  | _ => #[]

/-- Syntactic equality ignoring source positions — two calls of the same module argument
should share a single hole. -/
partial def sameSyntax : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .atom _ v, .atom _ v' => v == v'
  | .ident _ _ v _, .ident _ _ v' _ => v == v'
  | .node _ k as, .node _ k' as' =>
      k == k' && as.size == as'.size && (as.zip as').all fun (a, b) => sameSyntax a b
  | _, _ => false

/-- Rewrite the `call`s of a module body (recursing through the whole statement tree).  A callee
that mentions a module parameter is replaced by `mkCallee i` for its (deduplicated) hole number
`i`, and the state accumulates those callees in hole order.  Any other callee is a `Module.Proc`,
so `Module.Proc.procedure` extracts the procedure the `call` statement expects.

Two runs with the same `params` produce the same hole numbering, which is what lets the
type-checking pass and the final pass agree on it. -/
partial def rewriteCalls (params : List Name) (mkCallee : Nat → Term) (s : Syntax) :
    StateM (Array Term) Syntax := do
  let k := s.getKind
  if k == ``GaudisCrypt.callStore || k == ``GaudisCrypt.callVoid then
    let i := if k == ``GaudisCrypt.callStore then 3 else 1
    let callee : Term := ⟨s.getArg i⟩
    if mentions params callee.raw then
      let holes ← get
      let idx := (holes.findIdx? fun c => sameSyntax c.raw callee.raw).getD holes.size
      if idx == holes.size then set (holes.push callee)
      return s.setArg i (mkCallee idx)
    else
      return s.setArg i (Syntax.mkCApp ``GaudisCrypt.Module.Proc.procedure #[callee])
  else match s with
    | .node info k args => return .node info k (← args.mapM (rewriteCalls params mkCallee))
    | _ => return s

/-- The named metavariable `?_holeSigᵢ` standing for the signature of the `i`-th hole: it is
solved by elaborating the body with the real callees in place, and read back afterwards. -/
def sigHole (i : Nat) : Term :=
  ⟨mkNode ``Lean.Parser.Term.syntheticHole #[mkAtom "?", mkIdent (sigName i)]⟩
  where sigName (i : Nat) : Name := Name.mkSimple s!"_holeSig{i}"

/-- Bring the module parameters into the local context (with their declared types) so that a
callee mentioning them can be elaborated.  The continuation gets their free variables, in
declaration order. -/
def withParams {α} : List (Ident × Term) → (Array Lean.Expr → TermElabM α) → TermElabM α
  | [], k => k #[]
  | (id, ty) :: rest, k => do
      let tyE ← Term.elabType ty
      Term.synthesizeSyntheticMVarsNoPostponing
      withLocalDeclD id.getId (← instantiateMVars tyE) fun x =>
        withParams rest fun xs => k (#[x] ++ xs)

/-- Read a `List` literal off an `Expr`. -/
partial def listLit? (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    return some []
  else if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    match ← listLit? args[2]! with
    | some rest => return some (args[1]! :: rest)
    | none => return none
  else
    return none

/-- How many errors a message log holds (used to tell whether the type-checking pass failed). -/
def errorCount (msgs : MessageLog) : Nat :=
  msgs.toList.countP (·.severity == MessageSeverity.error)

/-- Split a solved `?_holeSigᵢ` into the syntax of its parameter types and its return type (for
the `uses` clause of the generated `proc`). -/
def sigSyntax (callee : Term) (sigMVar : Lean.Expr) : TermElabM (Array Term × Term) := do
  let sig ← whnf (← instantiateMVars sigMVar)
  let fail {α} : TermElabM α :=
    throwErrorAt callee
      "module: the signature of this call must elaborate to a literal `procsig (…) -> …`, \
       but it is{indentExpr sig}"
  unless sig.isAppOfArity ``GaudisCrypt.ProcedureSignature.mk 2 do fail
  let args := sig.getAppArgs
  let some ps ← listLit? args[0]! | fail
  let psStx ← ps.toArray.mapM fun p => PrettyPrinter.delab p
  return (psStx, ← PrettyPrinter.delab args[1]!)

/-- The name of the placeholder standing for the module parameter declared at position `i`
inside a callee's `ModuleExpression`. -/
def paramName (i : Nat) : Name := Name.mkSimple s!"_param{i}"

/-- The placeholder for the `i`-th module parameter.  A callee is read back with these in place of
the parameters, because the two consumers need different things there: `X.<f>` substitutes a de
Bruijn `.var` (it is curried over the parameters it uses), `X` a projection of its single argument
tuple. -/
def paramPlaceholder (i : Nat) : Term := mkIdent (paramName i)

/-- Replace the parameter placeholders of `s`: the one for position `i` by `subst[i]`. -/
partial def substParams (subst : Array Term) (s : Syntax) : Syntax :=
  if s.isIdent then
    match (Array.range subst.size).find? fun i => s.getId == paramName i with
    | some i => subst[i]!
    | none => s
  else match s with
    | .node info k args => .node info k (args.map (substParams subst))
    | _ => s

/-- Translate a module-valued term into `ModuleExpression` *syntax*, with the module parameters
(given as `params`, each with the position at which it was declared) becoming `paramPlaceholder`s.

A subterm mentioning no parameter is closed, so it is emitted as `Module.expression ‹subterm›`.
Otherwise the head has to be one of the module operations handled below; anything else is
unfolded and retried, and if that gets stuck the term is rejected.  (Rejecting is the only
option: a Lean function `T → Module _` cannot in general be reflected into a `.abs`.) -/
partial def toModuleExpr (params : List (FVarId × Nat)) (e : Lean.Expr) : TermElabM Term := do
  let e ← instantiateMVars e
  let isParam := fun id => (params.find? (·.1 == id)).isSome
  unless e.hasAnyFVar isParam do
    -- `.expression` as an explicit application: field notation would look the field up under the
    -- head of the type, which for a module type synonym (`TestModule`, `Module.Arr …`) is not
    -- `Module`
    return Syntax.mkCApp ``GaudisCrypt.Module.expression #[← PrettyPrinter.delab e]
  if let .fvar id := e then
    if let some (_, i) := params.find? (·.1 == id) then
      return paramPlaceholder i
  let args := e.getAppArgs
  let n := args.size
  -- the arguments of interest are the last ones (`Module.app` & co. carry leading implicit and
  -- instance arguments), so we count from the end
  let un (ctor : Name) : TermElabM Term := do
    return Syntax.mkCApp ctor #[← toModuleExpr params args[n-1]!]
  let bin (ctor : Name) : TermElabM Term := do
    return Syntax.mkCApp ctor #[← toModuleExpr params args[n-2]!, ← toModuleExpr params args[n-1]!]
  if let .const c _ := e.getAppFn then
    if n ≥ 2 && (c == ``GaudisCrypt.Module.app || c == ``GaudisCrypt.Module.app') then
      return ← bin ``GaudisCrypt.ModuleExpression.app
    if n ≥ 2 && (c == ``GaudisCrypt.Module.pair || c == ``GaudisCrypt.Module.pair') then
      return ← bin ``GaudisCrypt.ModuleExpression.pair
    if n ≥ 1 && (c == ``GaudisCrypt.Module.fst || c == ``GaudisCrypt.Module.fst') then
      return ← un ``GaudisCrypt.ModuleExpression.fst
    if n ≥ 1 && (c == ``GaudisCrypt.Module.snd || c == ``GaudisCrypt.Module.snd') then
      return ← un ``GaudisCrypt.ModuleExpression.snd
    -- `cast`/`cast'` only move between `Module T` and a type synonym for it
    if n ≥ 1 && (c == ``GaudisCrypt.Module.cast || c == ``GaudisCrypt.Module.cast') then
      return ← toModuleExpr params args[n-1]!
  let e' ← whnfCore e
  if e' != e then return ← toModuleExpr params e'
  match ← unfoldDefinition? e with
  | some e' => toModuleExpr params e'
  | none =>
      throwError "module: cannot read{indentExpr e}\nas a module expression built from the \
        module parameters — its head is none of `Module.app`, `Module.fst`, `Module.snd`, \
        `Module.pair` and it cannot be unfolded any further"

/-- The signature of an already-declared procedure, as syntax (`procsig (…) -> …`).  Used for the
type of the generated module, where `ProcedureWithHoles.signature p` would work too but would show
up unevaluated in every hover. -/
def procSig (P : LeanParams) (procRef : Term) : TermElabM Term :=
  P.withBinders do
    let e ← Term.elabTerm (← `(GaudisCrypt.ProcedureWithHoles.signature $procRef)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    PrettyPrinter.delab (← whnf (← instantiateMVars e))

/-- Type-check a procedure body with the module parameters in the local context and the *real*
callees in place (each hole callee ascribed to `Module (.proc ?_holeSigᵢ)`), and return, for each
hole, the signature that this elaboration assigns to its `?_holeSigᵢ` together with the callee
read back as a `ModuleExpression` over the parameters (which appear in it as `paramPlaceholder`s).

Holes are made only afterwards, from these signatures — so a call is typed exactly as written
before it loses its callee. -/
def checkBody (P : LeanParams) (paramBs : List (Ident × Term)) (callees : Array Term)
    (body : Term) : TermElabM (Array (Array Term × Term) × Array Term) :=
  P.withBinders <| withParams paramBs fun fvars => do
    -- create the `?_holeSigᵢ` up front: `elabSyntheticHole` reuses a metavariable of that name
    let mvars ← (Array.range callees.size).mapM fun i =>
      mkFreshExprMVar (Lean.mkConst ``GaudisCrypt.ProcedureSignature)
        (userName := sigHole.sigName i)
    discard <| Term.elabTerm body none
    Term.synthesizeSyntheticMVarsNoPostponing
    let sigs ← (callees.zip mvars).mapM fun (c, mv) => sigSyntax c mv
    let params : List (FVarId × Nat) :=
      (fvars.toList.zipIdx).map fun (x, i) => (x.fvarId!, i)
    -- re-elaborate each callee on its own (same ascription as in the body, whose elaboration has
    -- by now solved `?_holeSigᵢ`) to get hold of its `Expr`
    let exprs ← callees.mapIdxM fun i c => do
      let stx ← `(($c : GaudisCrypt.Module (GaudisCrypt.ModuleTypeRep.proc $(sigHole i))))
      toModuleExpr params (← instantiateMVars (← Term.elabTerm stx none))
    return (sigs, exprs)

/-- What `elabProcedure` leaves for `elabProcModule` to work with. -/
structure ProcResult where
  /-- The procedure's name as written in the declaration. -/
  fn : Ident
  /-- The constant just declared: `X.<f>.procedure`. -/
  declId : Ident
  /-- The same constant, with the Lean parameters applied — how everything else refers to it. -/
  declRef : Term
  /-- The positions (in the module's parameter list) of the parameters this procedure uses,
  in declaration order. -/
  usedPos : Array Nat
  /-- Its hole callees as `ModuleExpression`s over the module parameters (which appear in them as
  `paramPlaceholder`s), in hole order. -/
  calleeExprs : Array Term
  /-- The same callees as they were written — module terms, mentioning the module parameters by
  name, in hole order.  `X.<f>.apply_simp` states what applying `X.<f>` to those parameters is, and
  names the callees this way (`Module.Proc.procedure` of each). -/
  callees : Array Term
  /-- The name of the `X.<f>.procedure.apply_simp` lemma declared alongside `X.<f>.procedure`. -/
  instThmId : Ident

/-- Declare `X.<f>.procedure` for one `proc f (…) : R { … }` of a `module X (…)` declaration.
Returns `none` if the body does not type-check (the errors have then been reported already). -/
def elabProcedure (nm : Ident) (P : LeanParams) (paramBs : Array (Ident × Term))
    (p : TSyntax `gaudi_module_proc) : CommandElabM (Option ProcResult) := do
  let bs := P.binders
  let `(gaudi_module_proc| proc $fn:ident ( $ps:proc_binder,* ) $[: $rty:term]? {
          $[var $locals:proc_binder,* ;]*
          $stmts:gaudi_stmt*
          return $rv:term $[;]?
        } $[;]?) := p | throwUnsupportedSyntax
  -- (`uses` is a keyword, hence the name `hbs?`)
  let mkProc (body : Array (TSyntax `gaudi_stmt))
      (hbs? : Option (Array (TSyntax `hole_binder))) : CommandElabM Term :=
    match hbs? with
    | none | some #[] =>
        `(proc ( $ps,* ) $[: $rty]? { $[var $locals,* ;]* $body* return $rv })
    | some hbs =>
        `(proc ( $ps,* ) uses ( $hbs,* ) $[: $rty]? { $[var $locals,* ;]* $body* return $rv })
  let paramNames := paramBs.toList.map (·.1.getId)
  -- the callees, in hole order — the hole names are made from them, so this pass throws its
  -- rewritten body away and only keeps the state
  let callees := ((stmts.mapM fun s => rewriteCalls paramNames holeCallee s.raw).run #[]).2
  let procBinders := ps.getElems ++ (locals.map (·.getElems)).flatten
  let bound := paramBs.map (·.1.getId)
      ++ (procBinders.map fun b => (binderNames b).map (·.getId)).flatten
  let holeIds := holeIdentsOfCallees bound callees
  -- the final (hole) form of the body
  let (holeStmts, _) :=
    (stmts.mapM fun s => rewriteCalls paramNames (holeIds[·]!) s.raw).run #[]
  -- pass 1: the body with its callees intact, elaborated with the module parameters in the
  -- local context — this is where the whole body (holes included) is type-checked, and what
  -- determines the hole signatures
  let checked ← callees.mapIdxM fun i c =>
    `(GaudisCrypt.Module.Proc.procedure
        ($c : GaudisCrypt.Module (GaudisCrypt.ModuleTypeRep.proc $(sigHole i))))
  let (checkStmts, _) :=
    (stmts.mapM fun s => rewriteCalls paramNames (checked[·]!) s.raw).run #[]
  let checkTerm ← mkProc (checkStmts.map (⟨·⟩)) none
  -- the parameters this procedure uses
  let usedPos := (Array.range paramBs.size).filter fun i =>
    callees.any fun c => mentions [paramBs[i]!.1.getId] c.raw
  let errsBefore := errorCount (← get).messages
  let (holeSigs, calleeExprs) ←
    runTermElabM fun _ => checkBody P paramBs.toList callees checkTerm
  -- a body that does not type-check has already been reported against its real callees;
  -- elaborating the hole version too would only duplicate the errors
  if errorCount (← get).messages > errsBefore then return none
  -- pass 2: now that they are typed, the parameter calls become holes
  let holeBinders ← holeSigs.mapIdxM fun i (hps, hret) =>
    `(hole_binder| $(holeIds[i]!):ident : ( $hps,* ) → $hret)
  let procTerm ← mkProc (holeStmts.map (⟨·⟩)) (some holeBinders)
  let declId := mkIdent (nm.getId ++ fn.getId ++ `procedure)
  elabCommand (← `(command| noncomputable def $declId:ident $bs* := $procTerm))
  let declRef ← P.ref declId
  -- pass 3: the same body once more, with each hole call `call args ‹its index›` instead — the
  -- right-hand side of `X.<f>.procedure.apply_simp`
  let argsId ← internalIdent `holeArgs
  let nh := callees.size
  let instCallees ← (Array.range nh).mapM fun k => do
    let mut idx ← `(GaudisCrypt.HoleIndex.zero)
    for _ in [0 : nh - 1 - k] do idx ← `(GaudisCrypt.HoleIndex.succ $idx)
    `($argsId $idx)
  let (instStmts, _) :=
    (stmts.mapM fun s => rewriteCalls paramNames (instCallees[·]!) s.raw).run #[]
  let instTerm ← mkProc (instStmts.map (⟨·⟩)) none
  let mut hCtx ← `(GaudisCrypt.HoleSigs.empty)
  for (hps, hret) in holeSigs do
    hCtx ← `(GaudisCrypt.HoleSigs.append $hCtx (procsig ( $hps,* ) -> $hret))
  let instThmId := mkIdent (declId.getId ++ `apply_simp)
  elabCommand (← `(command| @[simp] theorem $instThmId:ident $bs* :
    ($argsId : GaudisCrypt.HoleSigs.Instantiation $hCtx) →
      GaudisCrypt.ProcedureWithHoles.instantiate $declRef $argsId = $instTerm :=
    fun $argsId => rfl))
  return some { fn, declId, declRef, usedPos, calleeExprs, callees := callees.map (⟨·⟩),
                instThmId }

/-- The `ModuleExpression` of the procedure `r`, with `subst[i]` put for the module parameter
declared at position `i`: either the closed `Module.proc X.<f>.procedure`, or
`Module.procWithHoles X.<f>.procedure` applied to the tuple of its callees.  That tuple is
right-nested and *reversed*, matching `HoleSigs.toModuleTypeRepTuple` (the last-declared hole is
the outermost `.fst`). -/
def procApplied (r : ProcResult) (subst : Array Term) : CommandElabM Term := do
  if r.calleeExprs.isEmpty then
    `(GaudisCrypt.Module.expression (GaudisCrypt.Module.proc $(r.declRef)))
  else
    let mut tuple ← `(GaudisCrypt.ModuleExpression.unit)
    for c in r.calleeExprs do
      tuple ← `(GaudisCrypt.ModuleExpression.pair $(⟨substParams subst c⟩) $tuple)
    `(GaudisCrypt.ModuleExpression.app
        (GaudisCrypt.Module.expression (GaudisCrypt.Module.procWithHoles $(r.declRef))) $tuple)

/-- The constant `X.<f>` that `elabProcModule` declares for the procedure `r` of `module X`. -/
def procModId (nm : Ident) (r : ProcResult) : Ident := mkIdent (nm.getId ++ r.fn.getId)

/-- Declare the module `X.<f>` of a procedure already declared by `elabProcedure`: either
`Module.proc X.<f>.procedure` (no module parameter used), or `procApplied` abstracted over the
parameters it does use, of type `Module.Arr T₁ (… (Module.Arr Tₖ (Module.Proc sig)))`.  Returns
the constant it declared. -/
def elabProcModule (nm : Ident) (P : LeanParams) (paramBs : Array (Ident × Term))
    (r : ProcResult) : CommandElabM Ident := do
  let bs := P.binders
  let modId := procModId nm r
  if r.calleeExprs.isEmpty then
    elabCommand (← `(command| noncomputable def $modId:ident $bs* :=
      GaudisCrypt.Module.proc $(r.declRef)))
  else
    let mut ty ← `(GaudisCrypt.Module.Proc $(← runTermElabM fun _ => procSig P r.declRef))
    for i in r.usedPos.reverse do ty ← `(GaudisCrypt.Module.Arr $(paramBs[i]!.2) $ty)
    -- the `j`-th used parameter is `.var (k-1-j)`: the first one is the outermost binder.  A
    -- parameter outside `usedPos` does not occur, so what it maps to is immaterial.
    let subst := (Array.range paramBs.size).map fun i =>
      match r.usedPos.findIdx? (· == i) with
      | some j => Syntax.mkCApp ``GaudisCrypt.ModuleExpression.var
                    #[Syntax.mkNatLit (r.usedPos.size - 1 - j)]
      | none => paramPlaceholder i
    let mut body ← procApplied r subst
    for _ in r.usedPos do body ← `(GaudisCrypt.ModuleExpression.abs $body)
    elabCommand (← `(command| noncomputable def $modId:ident $bs* : $ty :=
      GaudisCrypt.ModuleExpression.toModule (m := $body)))
  return modId

/-- Declare `X.<f>.apply_simp`, the `@[simp]` lemma that applies the procedure module `X.<f>` to the
parameters `f` uses:
```
theorem X.f.apply_simp (A : T₁) … (Z : Tₖ) :
    Module.app (… (Module.app X.f A) …) Z
      = Module.proc (X.f.procedure.instantiate
          (HoleSigs.Instantiation.nil.push (Module.Proc.procedure c₁) |>.push … ))
```
— the procedure with its holes filled by the callees `c₁ …` they were made from, each written as it
was in the body (with `A … Z` in place of the module parameters) and turned into a `Procedure` by
`Module.Proc.procedure`.  Pushed in hole order, so the *last* declared hole ends up at
`HoleIndex.zero`, which is how `HoleSigs.Instantiation.toModuleExpr` reads a tuple back.

A procedure with no holes uses no parameter either (a hole is exactly a call to a callee mentioning
one), and `X.<f>` is then `Module.proc X.<f>.procedure` by definition — the lemma says just that.

Proved by the `proc_apply` tactic. -/
def elabProcApplySimp (nm : Ident) (P : LeanParams) (paramBs : Array (Ident × Term))
    (r : ProcResult) : CommandElabM Ident := do
  let bs := P.binders
  let modId := procModId nm r
  let modRef ← P.ref modId
  let thmId := mkIdent (modId.getId ++ `apply_simp)
  if r.callees.isEmpty then
    elabCommand (← `(command| @[simp] theorem $thmId:ident $bs* :
      $modRef = GaudisCrypt.Module.proc $(r.declRef) := rfl))
    return thmId
  let mut inst ← `(GaudisCrypt.HoleSigs.Instantiation.nil)
  for c in r.callees do
    inst ← `(GaudisCrypt.HoleSigs.Instantiation.push $inst (GaudisCrypt.Module.Proc.procedure $c))
  let mut lhs : Term := modRef
  for i in r.usedPos do lhs ← `(GaudisCrypt.Module.app $lhs $(paramBs[i]!.1))
  -- the statement, as a `(x : T) → …` chain (there is no binder syntax to splice into a `theorem`)
  let mut stmt ← `($lhs = GaudisCrypt.Module.proc
    (GaudisCrypt.ProcedureWithHoles.instantiate $(r.declRef) $inst))
  for i in [0 : r.usedPos.size] do
    let (x, ty) := paramBs[r.usedPos[r.usedPos.size - 1 - i]!]!
    stmt ← `(($x : $ty) → $stmt)
  let ids := r.usedPos.map (paramBs[·]!.1)
  elabCommand (← `(command| @[simp] theorem $thmId:ident $bs* : $stmt := by
    intro $ids*
    proc_apply $modId))
  return thmId

/-- `f x₁ (f x₂ (… xₙ))` — every tuple built here is right-nested, and a one-element one is just
its element (as in `moduletype`, whose product of `n` field types has `n-1` `.prod`s).  `xs` must
not be empty. -/
def rightNest (f : Term → Term → CommandElabM Term) (xs : Array Term) : CommandElabM Term := do
  let mut acc := xs[xs.size - 1]!
  for j in [0 : xs.size - 1] do acc ← f xs[xs.size - 2 - j]! acc
  return acc

/-- If the declared module type is one introduced by `moduletype` whose fields are exactly the
procedures declared here (same names, order immaterial), its constructor `N.mk`; `none` otherwise.
`N.mk` takes the record `N.Structure`, so the module can then be written
`N.mk { f₁ := …, fₙ := … }` rather than as a nest of `Module.pair`s.

The declared type may be applied to Lean parameters of its own — `: (Sized n)` for a `moduletype
Sized (n : Nat)` — and the constructor is then applied to the same arguments, `Sized.mk n`.  That
works positionally because the command gives `N` and `N.mk` the very same binders, so an argument
list that fits the type fits the constructor: `Sized n` ⟹ `Sized.mk n`, and a `Poly` whose
parameters are all implicit stays bare at both. -/
def moduletypeMk? (mt? : Option Term) (fns : Array Name) : CommandElabM (Option Term) := do
  let some mt := mt? | return none
  -- the declared type is parsed at `term:max`, so an applied one arrives parenthesised
  let mt ← match mt with
    | `(($t:term)) => pure t
    | _            => pure mt
  -- the head has to be a name, but it may carry arguments — taken off the raw syntax rather than
  -- matched as `$as:term*`, so that a named one (`Poly (α := α)`, the only way to write a
  -- moduletype whose parameters are implicit) passes through as it stands
  let (id, args) : Ident × Array Term ←
    if mt.raw.isIdent then
      pure ((⟨mt.raw⟩ : Ident), #[])
    else if mt.raw.getKind == ``Lean.Parser.Term.app && mt.raw[0]!.isIdent then
      pure ((⟨mt.raw[0]!⟩ : Ident), mt.raw[1]!.getArgs.map fun a => (⟨a⟩ : Term))
    else
      return none
  let some n ← (try pure (some (← resolveGlobalConstNoOverload id)) catch _ => pure none)
    | return none
  let env ← getEnv
  let structName := n.str "Structure"
  unless env.contains (n.str "mk") && isStructure env structName do return none
  let fields := getStructureFields env structName
  unless fields.size == fns.size && fns.all fields.contains do return none
  let mkId := mkIdent (n.str "mk")
  if args.isEmpty then return some mkId else return some (← `($mkId $args*))

/-- The record whose field `i` is `fields[i]`: `N.mk { f₁ := …, fₙ := … }` when `mk?` is the
constructor of a `moduletype` with exactly these fields (see `moduletypeMk?`), and the right-nested
`Module.pair` of them — which is the same record, only anonymous — otherwise. -/
def mkRecord (mk? : Option Term) (procs : Array ProcResult) (fields : Array Term) :
    CommandElabM Term := do
  match mk? with
  | some mk =>
      let fs ← procs.mapIdxM fun i r =>
        `(Lean.Parser.Term.structInstField| $(r.fn):ident := $(fields[i]!))
      `($mk { $fs:structInstField,* })
  | none => rightNest (fun a b => `(GaudisCrypt.Module.pair $a $b)) fields

/-- Declare `X.apply_simp`, the `@[simp]` lemma that applies `X` to its parameters:
```
theorem X.apply_simp (A : T₁) … (Z : Tₙ) :
    Module.app X (Module.pair A (… Z)) = N.mk { f₁ := Module.app X.f₁ A, … }
```
— the record of the procedures, each applied to the parameters *it* uses (`Module.pair` in place of
`N.mk` when the module type is not a `moduletype` name, as in `mkRecord`).  For an empty parameter
list the tuple is the only argument `X` can take, a variable of `Module.Unit`.

Proved by the `module_apply` tactic, which normalises both sides. -/
def elabApplySimp (nm : Ident) (P : LeanParams) (paramBs : Array (Ident × Term))
    (mkId? : Option Term) (procs : Array ProcResult) : CommandElabM Ident := do
  let bs := P.binders
  let n := paramBs.size
  let tId ← internalIdent `paramTuple
  -- the record of the procedures, each applied to the arguments at its `usedPos`
  let paramTerms : Array Term := paramBs.map fun b => b.1
  let rhs ← mkRecord mkId? procs (← procs.mapM fun r => do
    let mut e : Term ← P.ref (procModId nm r)
    for i in r.usedPos do e ← `(GaudisCrypt.Module.app $e $(paramTerms[i]!))
    pure e)
  let argTuple : Term ←
    if n == 0 then pure (tId : Term)
    else rightNest (fun a b => `(GaudisCrypt.Module.pair $a $b)) paramTerms
  -- the statement, as a `(x : T) → …` chain (there is no binder syntax to splice into a `theorem`)
  let mut stmt ← `(GaudisCrypt.Module.app $(← P.ref nm) $argTuple = $rhs)
  if n == 0 then
    stmt ← `(($tId : GaudisCrypt.Module.Unit) → $stmt)
  else
    for i in [0 : n] do
      let (x, ty) := paramBs[n - 1 - i]!
      stmt ← `(($x : $ty) → $stmt)
  let ids := if n == 0 then #[tId] else paramBs.map (·.1)
  let thmId := mkIdent (nm.getId ++ `apply_simp)
  elabCommand (← `(command| @[simp] theorem $thmId:ident $bs* : $stmt := by
    intro $ids*
    module_apply $nm))
  return thmId

/-- Declare the module `X` itself: the record of its procedures (a right-nested `.pair`, as
`moduletype` nests its fields) — each of them the constant `X.<f>` declared by `elabProcModule`,
applied to the parameters that `f` uses — abstracted over *all* the parameters at once, used or
not, which it takes as one right-nested tuple.  So `X : Module.Arr (Module.Prod T₁ (… Tₙ)) M`, with
`M` the declared module type, degenerating to `Module.Arr Module.Unit M` for an empty parameter list
and to plain `M` when the declaration has no parameter list at all.

A declaration without a module type gets the record of the procedures' own types for `M`, i.e.
`Module.Prod (Module.Proc sig₁) (… (Module.Proc sigₙ))` — which is what a `moduletype` of these
procedures unfolds to anyway, only anonymous.

With no parameter list there is no `.abs`, and no procedure can call a parameter either, so the
whole thing stays at the `Module` level: `X` is then `Module.pair X.f₁ (… X.fₙ)`, with no detour
through `ModuleExpression` and `toModule` — and when the declared module type is a `moduletype`
name `N` with exactly these fields, the named form `N.mk { f₁ := X.f₁, … }` instead.

With a parameter list `X` also gets the `@[simp]` lemma `X.apply_simp` for applying it to one (see
`elabApplySimp`).

Declares nothing (and returns `#[]`) if the declaration has no procedures.  The result lists what
was declared, for `logDeclared`. -/
def elabModule (nm : Ident) (P : LeanParams) (params? : Option (Array (Ident × Term)))
    (mt? : Option Term) (procs : Array ProcResult) : CommandElabM (Array (Name × String)) := do
  if procs.isEmpty then return #[]
  let bs := P.binders
  let paramBs := params?.getD #[]
  let n := paramBs.size
  let prod := fun (a b : Term) => `(GaudisCrypt.Module.Prod $a $b)
  let mkId? ← moduletypeMk? mt? (procs.map (·.fn.getId))
  let mt ← match mt? with
    | some mt => pure mt
    | none => rightNest prod (← procs.mapM fun r => do
        `(GaudisCrypt.Module.Proc $(← runTermElabM fun _ => procSig P r.declRef)))
  let paramProd ←
    if n == 0 then `(GaudisCrypt.Module.Unit) else rightNest prod (paramBs.map (·.2))
  let ty ← match params? with
    | none => pure mt
    | some _ => `(GaudisCrypt.Module.Arr $paramProd $mt)
  if params?.isNone then
    let body ← mkRecord mkId? procs (← procs.mapM fun r => P.ref (procModId nm r))
    elabCommand (← `(command| noncomputable def $nm:ident $bs* : $ty := $body))
    return #[(nm.getId, "the module itself")]
  -- the parameter at position `i` is the `i`-th component of the argument tuple `.var 0`
  let subst ← (Array.range n).mapM fun i => do
    let mut e ← `(GaudisCrypt.ModuleExpression.var 0)
    for _ in [0 : i] do e ← `(GaudisCrypt.ModuleExpression.snd $e)
    if i + 1 < n then e ← `(GaudisCrypt.ModuleExpression.fst $e)
    pure e
  -- each field is the already-declared `X.<f>`, applied to the parameters that `f` uses (in
  -- declaration order, the order `elabProcModule` abstracted them in)
  let fields ← procs.mapM fun r => do
    let mut e ← `(GaudisCrypt.Module.expression $(← P.ref (procModId nm r)))
    for i in r.usedPos do e ← `(GaudisCrypt.ModuleExpression.app $e $(subst[i]!))
    pure e
  let mut body ← rightNest (fun a b => `(GaudisCrypt.ModuleExpression.pair $a $b)) fields
  if params?.isSome then body ← `(GaudisCrypt.ModuleExpression.abs $body)
  elabCommand (← `(command| noncomputable def $nm:ident $bs* : $ty :=
    GaudisCrypt.ModuleExpression.toModule (m := $body)))
  let thmId ← elabApplySimp nm P paramBs mkId? procs
  return #[(nm.getId, "the module itself"), (thmId.getId, "applying it to its parameters")]

end GaudisCrypt.ModuleDecl

open Lean Elab Command GaudisCrypt.ModuleDecl in
elab_rules : command
  | `(module $nm:ident $lps:gaudi_param* $[using ( $params:proc_binder,* )]? $[: $mt:term]? {
        $procs:gaudi_module_proc*
      }) => do
    let ownBs ← paramBinders "module" lps
    let P ← nameParams ((← sectionBinders (← getRef) ownBs) ++ ownBs)
    if params.isNone then warnModuleTypedParam P
    -- as in `proc`, a binder may name several parameters of one module type
    let paramBs? ← params.mapM fun ps => return (← ps.getElems.mapM fun b => match b with
      | `(proc_binder| $id:ident : $ty:term) => pure #[(id, ty)]
      | `(proc_binder| $id:ident $ids:ident* : $ty:term) => pure ((#[id] ++ ids).map (·, ty))
      | _ => throwUnsupportedSyntax).flatten
    let paramBs := paramBs?.getD #[]
    let mut declared : Array (Name × String) := #[]
    let mut results : Array ProcResult := #[]
    for p in procs do
      let some r ← elabProcedure nm P paramBs p | continue
      results := results.push r
      -- the short names: the `#check`s are inserted right after the command, in the same namespace
      declared := declared.push (r.declId.getId, s!"body of proc {r.fn.getId}")
      declared := declared.push (r.instThmId.getId,
        s!"instantiating the holes of proc {r.fn.getId}")
      let modId ← elabProcModule nm P paramBs r
      let used := ", ".intercalate (r.usedPos.toList.map (paramBs[·]!.1.getId.toString))
      declared := declared.push (modId.getId,
        if r.usedPos.isEmpty then s!"proc {r.fn.getId} as a module"
        else s!"proc {r.fn.getId} as a module, in {used}")
      let procThmId ← elabProcApplySimp nm P paramBs r
      declared := declared.push (procThmId.getId,
        if r.usedPos.isEmpty then s!"proc {r.fn.getId} as the procedure itself"
        else s!"applying proc {r.fn.getId} to {used}")
    -- `X` itself — only when every procedure made it (a missing field would not type-check)
    if results.size == procs.size then
      declared := declared ++ (← elabModule nm P paramBs? mt results)
    logDeclared (← getRef) declared

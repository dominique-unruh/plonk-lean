import GaudisCrypt.Syntax.ExpressionSyntax

open GaudisCrypt

/-!
# Concrete syntax for programs and procedures

Surface syntax for the imperative probabilistic language (`StmtWithHoles` /
`ProcedureWithHoles` from `GaudisCrypt`).  Expression syntax (`GaudiExpr[ ]` and the `$`
sigil) is in `ExpressionSyntax.lean`; module syntax is in `ModuleSyntax.lean`.  See
`syntax-ideas.md` for design notes.

## Statements / programs — `GaudiProg[ … ]`

A `;`-terminated sequence of statements.  The statement forms are:
* `skip;`
* `x <- e;`                       — assignment;
* `a, b <- e;`  /  `(a, b) <- e;` — tuple assignment (the parentheses are optional);
* `x <$ e;`                       — sample `x` from distribution `e`;
* `x <- call p (e₁, …, eₙ);`      — call procedure `p`, storing the result in `x`;
* `call p (e₁, …, eₙ);`           — call `p`, discarding the result;
* `if (e) { … } else { … }`       — the `else` branch is optional;
* `while (e) { … }`
* `{ … }`                         — a nested block;
* `let x := e;` / `have h : P := prf;` / `letI …;` / `haveI …;` — an ordinary *Lean*
  binder (not a program statement), scoping over the statements that follow it in the
  same block.

The argument list `( … )` of a `call` is always required (write `()` for no arguments).

Example (`a b c : Lens Nat State`, `inc : Procedure …`):
```
GaudiProg[
  a <- $a + 1;
  b, c <- ($a, $a * 2);
  if ($a == 0) { a <- 1; } else { skip; }
  while ($b == 0) { b <- $b + 1; }
  a <- call inc ($a);
]
```

## Procedures — `proc (…) [uses (…)] [: R] { … }`

A procedure *term*:
```
proc (x : T, y : U) uses (A : (Nat) → Bool, B : (Bool) → Nat) : R {
  var u : V, w : W;     -- zero or more `var …;` lines of local variables
  <statements>
  return e
}
```
* parameters `(x : T, …)` (possibly none).  A binder may name several variables of one type,
  `(x y : T, …)`, and stands for the same list as writing them out one by one — so may a
  local-variable binder, and a module parameter after `using`;
* an optional `uses (…)` clause declaring *holes* (abstract sub-procedures), each written
  `name : (T₁, …, Tₙ) → R`.  Inside the body a hole is invoked with the ordinary
  `call A (…)` syntax — `A` resolves to a hole when it is one of the declared names, and to
  a concrete procedure otherwise;
* an optional return type `: R` (inferred from `return e` when omitted);
* local variables via one or more `var name : T, …;` lines (`var u w : V;` declares two);
* a body of statements ending in `return e`.

A `let`/`have`/`letI`/`haveI` statement in the body scopes over the rest of the body *and*
over `return e`.  Body and return value are two separate fields of `ProcedureWithHoles`, so
the binders on the body's *spine* — those of the procedure's own block, each carrying the
rest of it — are repeated around the return value.  A binder nested inside an `if`/`while`/
block, on the other hand, ends with that block and does not reach `return e`.

## Procedure types and signatures

* `proctype (T, U, …) -> W`                    — the type of a closed procedure;
* `proctype (T, …) -> W uses ((T₁,…) → R, …)`   — the type of a procedure with holes;
* `procsig (T, U, …) -> W`                      — the bare `ProcedureSignature`.

`->` is used (rather than `:`) so these nest inside type ascriptions without extra
parentheses; they also pretty-print back into this form.

## Printing

Statements, procedures and the two type forms all *print* in this syntax again, and do so
round-trip faithfully: parsing what was printed gives the same term back.  A variable read
prints as `§x`, the printable spelling of `$x`.  See the *Printing* section at the end of
this file for the delaborators and for the two places where the printed form differs from
what one would write by hand.

e.g. `proctype (Nat, Bool) -> Nat`, `proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat)`,
`procsig (Nat, Bool) -> Nat`.  Note `Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat`.

The *module* type of a procedure, `procmod (…) -> R`, is in `ModuleSyntax.lean`.
-/

/-! ## Syntax for programs (`StmtWithHoles`)

Statement syntax over `StmtWithHoles h l`.  Each expression position (assignment
RHS, sampling distribution, `if`/`while` condition) is wrapped with `GaudiExpr[ ]`
so the `$x` sigil works.  An l-value (assignment/sample LHS) is a *lens*, lifted
into the current full state `State × l` by `liftLens` — so a global `Lens a State`
may be written bare and is lifted with `.ofst`.

Surface forms (`gaudi_stmt`):

    skip;
    x <- e;                       -- assignment
    a, b <- e;   (a,b) <- e;      -- tuple l-value (parens optional), via `Lens.pair`
    x <$ e;                       -- sampling (e : a distribution expression)
    x <- call p (e₁, …, eₙ);      -- procedure call, result stored in `x`
    call p (e₁, …, eₙ);           -- procedure call, result discarded (Lens.throwaway)
    if (e) { … } else { … }       -- the `else` branch is optional
    while (e) { … }
    { … }                         -- a block (sequence)
    let x := e;   have h : P := prf;   letI …;   haveI …;   -- a Lean binder

The call argument list `( … )` is always required (even `()`); the arguments form a
tuple matching the callee's `ParamType`.  (`hole` is still deferred.)

The four binder forms are not `StmtWithHoles` constructors: they are the ordinary Lean
term binders.  Each *carries* the statements it scopes over as a nested statement list, so
`let x := e;` followed by more statements is a single `gaudi_stmt` holding them, and the
binder is visible exactly there — in the statements that follow it in its own block, and
nowhere else. -/

namespace GaudisCrypt

variable [ProgramSpec]

/-- Lift a program variable used as an l-value into a lens on the full current state
`State × S`.  Dispatch is on the lens's *container* `M`: a global lens (`M = State`)
is lifted with `.ofst`, a full-state lens (`M = State × S`) is kept as-is.  The
content type `A` is deliberately *not* a class parameter — resolution then only needs
`M` (always concrete from the argument), and the result's content unifies with the
expected type as an ordinary, postponable constraint.  (That is what lets a `call`
result l-value resolve even before the callee's `sig` is known.) -/
class LiftLens (S : Type) (M : Type) where
  lift {A : Type} : Lens A M → Setter A (ProcedureState S)

instance {S : Type} : LiftLens S State where
  lift x := (ProcedureState.globalL.chain x).toSetter
instance {S : Type} : LiftLens S (ProcedureState S) where lift x := x.toSetter

/-- User-facing l-value lift; `S`, the container `M`, and the content `A` are inferred.
The result is a `Setter` (l-values only ever `set`). -/
def liftLens {S A M} [LiftLens S M] (x : Lens A M) : Setter A (ProcedureState S) :=
  LiftLens.lift x

/-- The raw (un-lifted) lens for an l-value: a tuple `(x, y, …)` becomes a nested
`Lens.pair`; a single term is itself.  Pairing needs the components to be disjoint
lenses in the same container — the `disjoint` instance is resolved at the concrete
lenses, so `(a, b)` requires `disjoint a b`. -/
scoped syntax "[lvalRaw| " term "]" : term
macro_rules
  | `([lvalRaw| ($x:term, $y:term)]) => `(Lens.pair [lvalRaw| $x] [lvalRaw| $y])
  | `([lvalRaw| $x:term]) => `($x)

/-- Raw nested `Lens.pair` of a comma-list of l-value components (each component
may itself be a paren-tuple, handled by `[lvalRaw|]`). -/
scoped syntax "[lvalRawList| " term,+ "]" : term
macro_rules
  | `([lvalRawList| $x:term]) => `([lvalRaw| $x])
  | `([lvalRawList| $x:term, $xs:term,*]) => `(Lens.pair [lvalRaw| $x] [lvalRawList| $xs,*])

/-- An l-value lifted into the current full state `State × S`.  Accepts a single
lens, a parenthesised tuple `(a, b)`, or a bare comma-list `a, b` (top-level
parens optional) — all interpreted via `Lens.pair`. -/
scoped syntax "[lval| " term,+ "]" : term
macro_rules
  | `([lval| $xs:term,*]) => `(liftLens [lvalRawList| $xs,*])

/-- A single `_` l-value discards the value written to it (`Setter.throwaway`).  Declared
after the general rule so it takes priority. -/
macro_rules
  | `([lval| _]) => `(Setter.throwaway)

/- ### Concrete syntax -/

declare_syntax_cat gaudi_stmt

-- The `ppLine`/`ppSpace` sprinkled over these productions are pretty-printer hints only
-- (they parse as nothing and add no syntax arguments); they are what makes a printed
-- program come out one statement per line.  See the *Printing* section at the end.
syntax ppLine "skip" ";" : gaudi_stmt
syntax ppLine term:max,+ " <- " term ";" : gaudi_stmt
syntax ppLine term:max,+ " <$ " term ";" : gaudi_stmt
syntax (name := callStore) ppLine term:max,+ " <- " "call" ppSpace term:max
  " (" term,* ")" ";" : gaudi_stmt
syntax (name := callVoid) ppLine "call" ppSpace term:max " (" term,* ")" ";" : gaudi_stmt
-- internal: generated by `proc` from `call <holeName>` (users never write `holecall`)
syntax (name := holecallStore) ppLine term:max,+ " <- " "holecall" ppSpace term:max
  " (" term,* ")" ";" : gaudi_stmt
syntax (name := holecallVoid) ppLine "holecall" ppSpace term:max " (" term,* ")" ";" : gaudi_stmt
-- the `ppGroup`s keep a header on one line: a group holding a statement list holds hard
-- line breaks, and would otherwise break at every optional space as well
syntax ppLine ppGroup("if" " (" term ") " "{") gaudi_stmt* ppLine ppGroup("}" " else " "{")
  gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine ppGroup("if" " (" term ") " "{") gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine ppGroup("while" " (" term ") " "{") gaudi_stmt* ppLine "}" : gaudi_stmt
syntax ppLine "{" gaudi_stmt* ppLine "}" : gaudi_stmt
-- Lean binders in statement position.  The atoms are spelled exactly as in the core term
-- parsers (`Lean.Parser.Term.let` etc.), whose `letDecl` opens with its own `ppSpace`.
--
-- Each of these *carries the statements it scopes over* rather than being a statement in its
-- own right, and each is declared at a higher priority than the productions above.  Both are
-- forced by `letI`/`haveI`: unlike `let`/`have` (which are `leadPrec` term parsers), the core
-- `letI`/`haveI` parsers are `maxPrec`, so in
--     letI n : Nat := 1; a <- e;
-- the l-value parser `term:max` of the assignment production happily reads the whole
-- `letI n : Nat := 1; a` as one term.  That parse ends exactly where ours does, so it is only
-- taking the rest of the sequence into the production that makes ours a contender at all
-- (`longestMatch` prefers the longer parse), and only the priority that then settles the tie
-- (without it the two are returned as an ambiguous `choice` node).
-- the `ppGroup` keeps the binder itself on one line; the statements it carries print at the
-- same level as it does, since they are a continuation of the same block, not a nested one
syntax (priority := high) ppLine ppGroup("let" Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("have" Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("letI " Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt
syntax (priority := high) ppLine ppGroup("haveI " Lean.Parser.Term.letDecl ";")
  ppDedent(gaudi_stmt*) : gaudi_stmt

/-- Translate one statement to a `StmtWithHoles` term. -/
scoped syntax "[gstmt| " gaudi_stmt "]" : term
/-- Translate a statement sequence (fold with `seq`; empty ↦ `skip`). -/
scoped syntax "[gseq| " gaudi_stmt* "]" : term
/-- Top-level program bracket. -/
scoped syntax "GaudiProg[" gaudi_stmt* ppDedent(ppDedent(ppLine)) "]" : term

macro_rules
  | `([gseq| ]) => `(StmtWithHoles.skip)
  | `([gseq| $s:gaudi_stmt]) => `([gstmt| $s])
  | `([gseq| $s:gaudi_stmt $ss:gaudi_stmt*]) =>
      `(StmtWithHoles.seq [gstmt| $s] [gseq| $ss*])


macro_rules
  | `([gstmt| skip;]) => `(StmtWithHoles.skip)
  | `([gstmt| $xs:term,* <- $e:term;]) =>
      `(StmtWithHoles.assign [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| $xs:term,* <$ $e:term;]) =>
      `(StmtWithHoles.sample [lval| $xs,*] (GaudiExpr[ $e ]))
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] [gseq| $e*])
  | `([gstmt| if ($c:term) { $t:gaudi_stmt* }]) =>
      `(StmtWithHoles.ifThenElse (GaudiExpr[ $c ]) [gseq| $t*] StmtWithHoles.skip)
  | `([gstmt| while ($c:term) { $body:gaudi_stmt* }]) =>
      `(StmtWithHoles.while (GaudiExpr[ $c ]) [gseq| $body*])
  | `([gstmt| { $ss:gaudi_stmt* }]) => `([gseq| $ss*])
  -- a Lean binder around the translation of the statements it carries
  | `([gstmt| let $d:letDecl; $ss:gaudi_stmt*]) => `(let $d:letDecl; [gseq| $ss*])
  | `([gstmt| have $d:letDecl; $ss:gaudi_stmt*]) => `(have $d:letDecl; [gseq| $ss*])
  | `([gstmt| letI $d:letDecl; $ss:gaudi_stmt*]) => `(letI $d:letDecl; [gseq| $ss*])
  | `([gstmt| haveI $d:letDecl; $ss:gaudi_stmt*]) => `(haveI $d:letDecl; [gseq| $ss*])

open Lean in
/-- Build the (right-nested) argument tuple from a comma-list of arg expressions:
`[]` ↦ `()`, `[e]` ↦ `e`, `e :: es` ↦ `(e, <es>)` — matching `paramListToTuple`. -/
private def mkArgTuple (args : List Term) : MacroM Term := do
  match args with
  | []      => `(())
  | [e]     => pure e
  | e :: es => do `(($e, $(← mkArgTuple es)))

-- `call` (procedure) and `holecall` (hole) statements.  `holecall` is *internal*: the
-- `proc` macro rewrites `call <holeName>` to it; users only ever write `call`.  In both
-- cases the callee is listed first so its `sig` is unified before the result l-value/args.
open Lean in
macro_rules
  | `([gstmt| $xs:term,* <- call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call [lval| $xs,*] $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| call $p:term ( $args:term,* );]) => do
      `(StmtWithHoles.call Setter.throwaway $p (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| $xs:term,* <- holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n [lval| $xs,*] (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))
  | `([gstmt| holecall $n:term ( $args:term,* );]) => do
      `(StmtWithHoles.hole $n Setter.throwaway (GaudiExpr[ $(← mkArgTuple args.getElems.toList) ]))

macro_rules
  | `(GaudiProg[ $ss:gaudi_stmt* ]) => `([gseq| $ss*])

/- ### Procedures

`proc (x : T, …) [: R] { var u : U, …; <stmts> ; return e }` builds a
`ProcedureWithHoles .empty sig`.  Each param/local name is `let`-bound — the user's
identifier spliced in, so hygiene lines up — to its projection lens into the full
state `State × l`, written as a plain `Lens.id.ofst.osnd…` chain.  The body's `$x`
and `x <- …` then resolve via the ordinary expression machinery.  `: R` is optional;
without it the return type is inferred from `return e`. -/

open Lean in section

declare_syntax_cat proc_binder
syntax ident " : " term : proc_binder
-- several names of the same type in one binder, as in `var m m' : Message;`.  The single-name
-- form above is kept as its own production (it is what the delaborators build), so the two do
-- not overlap: this one needs at least two names.
syntax ident ident+ " : " term : proc_binder

/-- `Lens.id` followed by a chain of `.ofst` (`true`) / `.osnd` (`false`). -/
private def mkChain (steps : List Bool) : MacroM Term := do
  let mut acc ← `(Lens.id)
  for s in steps do
    acc ← if s then `($(acc).ofst) else `($(acc).osnd)
  pure acc

/-- Steps to reach slot `k` of a right-nested `n`-tuple (the last element is
un-wrapped, so it needs no final `.ofst`). -/
private def navSteps (k n : Nat) : List Bool :=
  if k + 1 == n then List.replicate k false else true :: List.replicate k false

/-- The names a binder declares, each paired with the (shared) declared type. -/
private def parseBinder : TSyntax `proc_binder → MacroM (List (Ident × Term))
  | `(proc_binder| $id:ident : $ty:term) => pure [(id, ty)]
  | `(proc_binder| $id:ident $ids:ident* : $ty:term) =>
      pure ((id :: ids.toList).map (·, ty))
  | _ => Macro.throwUnsupported

/-- A hole declaration `A : (T₁, …, Tₙ) → R` (an abstract procedure with no locals). -/
declare_syntax_cat hole_binder
syntax ident " : " "(" term,* ")" " → " term : hole_binder

private def parseHoleBinder : TSyntax `hole_binder → MacroM (Ident × List Term × Term)
  | `(hole_binder| $id:ident : ( $ps:term,* ) → $ret:term) => pure (id, ps.getElems.toList, ret)
  | _ => Macro.throwUnsupported

/-- Rewrite `call A (…)` → `holecall A (…)` for every callee `A` whose name is a hole
(recursing into `if`/`while`/block bodies); everything else is left untouched. -/
partial def rewriteHoles (holeNames : List Name) (s : TSyntax `gaudi_stmt) :
    MacroM (TSyntax `gaudi_stmt) := do
  let k := s.raw.getKind
  -- `call`/`holecall` statements carry a sepBy arg-list inside parens, which category
  -- quotations cannot match, so we dispatch on the production kind at the `Syntax` level.
  if k == ``callStore || k == ``callVoid then
    -- callee position: `callStore` is `xs,* "<-" "call" callee …`; `callVoid` is `"call" callee …`.
    let calleeIdx := if k == ``callStore then 3 else 1
    let args := s.raw.getArgs
    let callee := args[calleeIdx]!
    if callee.isIdent && holeNames.contains callee.getId then
      -- swap kind to the `holecall*` production and the `"call"` atom → `"holecall"`.
      let newKind := if k == ``callStore then ``holecallStore else ``holecallVoid
      let newArgs := args.map fun a =>
        match a with
        | .atom info "call" => .atom info "holecall"
        | _ => a
      return ⟨(s.raw.setArgs newArgs).setKind newKind⟩
    else
      return s
  match s with
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* } else { $e:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* }
                          else { $(← e.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| if ($c:term) { $t:gaudi_stmt* }) => do
      `(gaudi_stmt| if ($c) { $(← t.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| while ($c:term) { $b:gaudi_stmt* }) => do
      `(gaudi_stmt| while ($c) { $(← b.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| { $ss:gaudi_stmt* }) => do
      `(gaudi_stmt| { $(← ss.mapM (rewriteHoles holeNames))* })
  | `(gaudi_stmt| let $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| let $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| have $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| have $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| letI $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| letI $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | `(gaudi_stmt| haveI $d:letDecl; $ss:gaudi_stmt*) => do
      `(gaudi_stmt| haveI $d:letDecl; $(← ss.mapM (rewriteHoles holeNames))*)
  | _ => pure s

/-- Wrap `e` in the Lean binders on the *spine* of the statement sequence `ss`: the
`let`/`have`/`letI`/`haveI` statements of the sequence itself, not those nested inside an
`if`/`while`/block.  Each such statement carries the rest of its sequence, so the spine is a
chain — at most one binder per level, recursed into.  `proc` uses this to repeat the body's
binders around the return value, which is a separate field of `ProcedureWithHoles`. -/
partial def wrapSpineBinders (ss : Array (TSyntax `gaudi_stmt)) (e : Term) : MacroM Term := do
  for s in ss do
    match s with
    | `(gaudi_stmt| let $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(let $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| have $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(have $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| letI $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(letI $d:letDecl; $(← wrapSpineBinders rest e))
    | `(gaudi_stmt| haveI $d:letDecl; $rest:gaudi_stmt*) =>
        return ← `(haveI $d:letDecl; $(← wrapSpineBinders rest e))
    | _ => pure ()
  return e

syntax ppGroup("proc" " (" proc_binder,* ")" (ppSpace "uses" " (" hole_binder,* ")")?
         (" : " term:max)? " {")
         (ppIndent(ppLine ppGroup("var " proc_binder,* ";")))*
         gaudi_stmt*
         ppIndent(ppLine ppGroup("return " term (";")?))
       ppDedent(ppDedent(ppLine)) "}" : term

macro_rules
  | `(proc ( $params:proc_binder,* ) $[uses ( $holes:hole_binder,* )]? $[: $retTy:term]? {
        $[var $locals:proc_binder,* ;]*
        $stmts:gaudi_stmt*
        return $ret:term $[;]?
      }) => do
    -- a binder may declare several names of one type, and is flattened into one entry each
    let paramBs := (← params.getElems.toList.mapM parseBinder).flatten.toArray
    -- multiple `var …;` lines are concatenated into a single local-variable list
    let localBs :=
      (← (locals.toList.flatMap (·.getElems.toList)).mapM parseBinder).flatten.toArray
    let holeBs := (← match holes with
      | some hs => hs.getElems.toList.mapM parseHoleBinder
      | none    => pure []).toArray
    let np := paramBs.size
    let nl := localBs.size
    -- the signature and local-variable list; the local-state `L` is the
    -- `LocalVariableState` *structure* (params tuple + vars tuple).
    let paramTys := paramBs.map (·.2)
    let localSigmas ← localBs.mapM fun (_, ty) => `(⟨$ty, inferInstance⟩)
    let retTyTerm ← match retTy with | some r => pure r | none => `(_)
    let sigTerm ← `(({ params := [$paramTys,*], ret := $retTyTerm } : ProcedureSignature))
    let localsTerm ← `([$localSigmas,*])
    -- `L` is the local-state structure, indexed by param *types* (no `ret`), so it is
    -- fully determined even when the return type is omitted.
    let L ← `(LocalVariableState [$paramTys,*] $localsTerm)
    -- one `let` per name, binding it to its lens into `ProcedureState L`.  A variable
    -- lens navigates `ProcedureState L` → (`localL`) `L` → (`paramsL`/`varsL`) the
    -- params/vars tuple → (`mkChain`/`navSteps`) the individual slot.
    let mut binds : Array (Ident × Term × Term) := #[]
    for k in [0:np] do
      let (id, ty) := paramBs[k]!
      let slot ← mkChain (navSteps k np)
      let chain ← `(Lens.intoParams $slot)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), chain)
    for j in [0:nl] do
      let (id, ty) := localBs[j]!
      let slot ← mkChain (navSteps j nl)
      let chain ← `(Lens.intoVars $slot)
      binds := binds.push (id, ← `(Lens $ty (ProcedureState $L)), chain)
    -- holes: a `ProcedureSignature` (no locals) each, folded into a `HoleSigs` context,
    -- and one `let` per name binding it to its `HoleIndex` (last-declared = `.zero`).
    let nh := holeBs.size
    let holeSigTerms ← holeBs.mapM fun (_, ps, ret) =>
      `(({ params := [$(ps.toArray),*], ret := $ret } : ProcedureSignature))
    let mut hCtx ← `(HoleSigs.empty)
    for sigT in holeSigTerms do hCtx ← `(($hCtx).append $sigT)
    let mut holeBinds : Array (Ident × Term × Term) := #[]
    for k in [0:nh] do
      let (id, _, _) := holeBs[k]!
      let mut idx ← `(HoleIndex.zero)
      for _ in [0 : nh - 1 - k] do idx ← `(HoleIndex.succ $idx)
      holeBinds := holeBinds.push (id, ← `(HoleIndex $hCtx $(holeSigTerms[k]!)), idx)
    let wrap (bs : Array (Ident × Term × Term)) (inner : Term) : MacroM Term :=
      bs.foldrM (fun (id, ty, val) acc => `(let $id : $ty := $val; $acc)) inner
    -- annotate with the explicit local-state `L` (so expressions see `S = L`) and hole
    -- context `hCtx`; the `L = sig.LocalVariableState` check happens in ordinary elaboration.
    -- rewrite `call A (…)` → `holecall A (…)` for every callee `A` that is a declared hole
    let holeNames := holeBs.toList.map (·.1.getId)
    let stmts' ← stmts.mapM (rewriteHoles holeNames)
    let body ← wrap (binds ++ holeBinds) (← `((GaudiProg[ $stmts'* ] : StmtWithHoles $hCtx $L)))
    -- the return value repeats the parameter/local `let`s and the body's spine binders
    let retval ← wrap binds
      (← wrapSpineBinders stmts' (← `((GaudiExpr[ $ret ] : Getter _ (ProcedureState $L)))))
    `((⟨$localsTerm, $body, $retval⟩ : ProcedureWithHoles $hCtx $sigTerm))

end

/-! ### Procedure *type* syntax

`proctype (T, U, V) -> W` is the type `Procedure { params := [T, U, V], ret := W }`, and
`proctype (…) -> W uses ((A₁,…) → R₁, …)` is the corresponding `ProcedureWithHoles`, whose
hole context is built from the listed (nameless) procedure signatures.  (Uses `->` rather
than `:` so it needs no extra parentheses inside a type ascription.) -/

/-- A nameless hole signature `(T₁, …, Tₙ) → R` inside a `proctype … uses (…)` clause. -/
declare_syntax_cat hole_sig
syntax "(" term,* ")" " → " term : hole_sig

syntax "proctype " "(" term,* ")" (" → " <|> " -> ") term (" uses " "(" hole_sig,* ")")? : term

open Lean in
macro_rules
  -- unicode `→` spelling delegates to the `->` arm below (distinguished by the arrow atom)
  | `(proctype ( $params:term,* ) → $ret:term $[uses ( $holes:hole_sig,* )]?) =>
      `(proctype ( $params,* ) -> $ret $[uses ( $holes,* )]?)
  | `(proctype ( $params:term,* ) -> $ret:term $[uses ( $holes:hole_sig,* )]?) => do
      let sigTerm ← `(ProcedureSignature.mk [$params,*] $ret)
      match holes with
      | none    => `(Procedure $sigTerm)
      | some hs =>
        let mut hCtx ← `(HoleSigs.empty)
        for h in hs.getElems do
          match h with
          | `(hole_sig| ( $ps:term,* ) → $r:term) =>
              hCtx ← `(($hCtx).append (ProcedureSignature.mk [$ps,*] $r))
          | _ => Macro.throwUnsupported
        `(ProcedureWithHoles $hCtx $sigTerm)

/-! `proctype` unexpanders.  A signature already prints as `procsig (…) -> …` (the
`ProcedureSignature.mk` unexpander), so we just rewrite `Procedure (procsig …)` and
`ProcedureWithHoles … (procsig …)` to `proctype …`.  Parameter lists are read off the raw
`procsig` node (a category quotation can't match the sepBy inside the parens). -/

open Lean PrettyPrinter in
/-- If `s` is a `procsig ( … ) -> …` node, return its parameter list and return type.
    (Not `private`: `ModuleSyntax.lean` unexpands `procmod` with it.) -/
def procsigParts? (s : Syntax) : Option (Syntax.TSepArray `term "," × TSyntax `term) :=
  let a := s.getArgs
  if a.size == 6 && a[0]!.getAtomVal == "procsig" then some (⟨a[2]!.getArgs⟩, ⟨a[5]!⟩) else none

open Lean PrettyPrinter in
@[app_unexpander Procedure]
def unexpandProcedure : Unexpander
  | `($_ $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      `(proctype ( $ps,* ) → $r)
  | _ => throw ()

open Lean PrettyPrinter in
/-- Collect every `procsig ( … ) -> …` node in `s`, left to right.  (Matching field
notation on `HoleSigs.append` in a quotation is brittle, so we just gather the leaves.)
A hole context `HoleSigs.empty.append s₁ … .append sₙ` has the hole signatures as its
only `procsig` nodes, in declaration order. -/
private partial def collectProcsigParts (s : Syntax) :
    Array (Syntax.TSepArray `term "," × TSyntax `term) :=
  match procsigParts? s with
  | some pr => #[pr]
  | none    => s.getArgs.foldl (fun acc a => acc ++ collectProcsigParts a) #[]

open Lean PrettyPrinter in
@[app_unexpander ProcedureWithHoles]
def unexpandProcedureWithHoles : Unexpander
  | `($_ $holes $sig) => do
      let some (ps, r) := procsigParts? sig.raw | throw ()
      let holeParts := collectProcsigParts holes.raw
      if holeParts.isEmpty then `(proctype ( $ps,* ) -> $r)
      else
        let holeSyns ← holeParts.mapM fun (hps, hr) => `(hole_sig| ( $hps,* ) → $hr)
        `(proctype ( $ps,* ) → $r uses ( $holeSyns,* ))
  | _ => throw ()

/-! ### Procedure *signature* syntax

`procsig (T, U, V) -> W` is the bare `ProcedureSignature.mk [T, U, V] W` (the same surface
form as `proctype`, minus the holes — a signature has none).  By construction
`Procedure (procsig …) = proctype …`.  The unexpander is on `ProcedureSignature.mk`, so any
signature with a literal parameter list prints back as `procsig (…) -> …`. -/

syntax "procsig " "(" term,* ")" (" → " <|> " -> ") term : term

macro_rules
  | `(procsig ( $params:term,* ) → $ret:term) => `(procsig ( $params,* ) -> $ret)
  | `(procsig ( $params:term,* ) -> $ret:term) => `(ProcedureSignature.mk [$params,*] $ret)

open Lean PrettyPrinter in
@[app_unexpander ProcedureSignature.mk]
def unexpandProcSig : Unexpander
  | `($_ [$ps,*] $r) => `(procsig ( $ps,* ) → $r)
  | _ => throw ()

/-! ## Printing

Delaborators that render elaborated terms back into the surface syntax above: a procedure
built by `proc` prints as `proc (…) uses (…) : R { … }`, and a statement prints as
`GaudiProg[ … ]` (with variable reads as the `§x` sigil, the printable spelling of `$x`).

Printing is *round-trip faithful*: parsing what was printed yields the same term back
(`ProgramSyntaxTest.lean` checks this by printing, re-parsing and re-elaborating).  Hence
the two places where the printed form deviates from what one would write by hand:

* a `seq` in the left position of a `seq` is printed as a block `{ … }`, since re-parsing
  a flat sequence would re-associate it;
* a hole call prints as `call A (…)` only inside the `proc` that declares `A` in its `uses`
  clause (which is where the macro turns `call` back into a hole call), and as the internal
  `holecall n (…)` anywhere else;
* `let`/`have` statements print with their type ascribed (`let x : T := v;`), and `letI`/
  `haveI` do not print at all — they *inline* their value during elaboration, so no binder
  of theirs survives in the term to be printed.  What is printed is then the inlined term,
  which is what re-parsing gives back, so the round trip still holds.

Whenever a term does not fit the surface syntax — a `Getter` that is not of the shape
`GaudiExpr[ ]` builds, an l-value that is not a lifted lens, `let`s that `proc` would not
have generated — the delaborators fail and Lean falls back to its default output.  They also
step aside under `pp.explicit` and `set_option pp.notation false`, and under the dedicated
`set_option pp.gaudisCrypt false`, which switches *only* them off and leaves the rest of
Lean's notation alone — the way to look at the underlying term.

`pp.gaudisCrypt` reaches the delaborators above but not the `app_unexpander`s further up this
file (`proctype`/`procsig`, `Procedure`): `UnexpandM` is `ReaderT Syntax (EStateM Unit Unit)`
and carries no `Options`, so an unexpander cannot consult one.  Those still print the *type*
as `proctype (…) -> R` under `pp.gaudisCrypt false`; `pp.notation false` turns them off. -/

section Printing
open Lean PrettyPrinter Delaborator SubExpr

/-- Name given to the state binder of a `GaudiExpr[ ]` getter while delaborating it. -/
private def stateBinderName : Name := `st

private partial def syntaxHasIdent (n : Name) : Syntax → Bool
  | .ident _ _ v _ => v.eraseMacroScopes == n
  | .node _ _ args => args.any (syntaxHasIdent n)
  | _ => false

register_option pp.gaudisCrypt : Bool := {
  defValue := true
  descr := "(pretty printer) print GaudisCrypt statements and procedures in their surface \
syntax (`GaudiProg[ … ]`, `proc … { … }`).  Turn off to see the underlying term while \
keeping the rest of Lean's notation."
}

private def getPPGaudisCrypt (o : Options) : Bool :=
  o.get pp.gaudisCrypt.name pp.gaudisCrypt.defValue

/-- Surface syntax is printed only when Lean is printing readably, and only while
`pp.gaudisCrypt` is on. -/
private def guardSurfaceSyntax : DelabM Unit := do
  guard (← getPPOption getPPGaudisCrypt)
  guard (← getPPOption getPPNotation)
  guard <| !(← getPPOption getPPExplicit)

/-- The elements of a literal list `[a, b, c]` at the current position. -/
private partial def delabListElems : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, args) => do
      guard (args.size == 3)
      let hd ← withNaryArg 1 delab
      let tl ← withNaryArg 2 delabListElems
      return #[hd] ++ tl
  | _ => failure

/-- `⟨T, inst⟩ : Σ t, Inhabited t` ↦ `T`. -/
private def delabLocalType : DelabM Term := do
  guard ((← getExpr).isAppOfArity ``Sigma.mk 4)
  withNaryArg 2 delab

/-- The declared types of a `locals` list. -/
private partial def delabLocalTypes : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, args) => do
      guard (args.size == 3)
      let hd ← withNaryArg 1 delabLocalType
      let tl ← withNaryArg 2 delabLocalTypes
      return #[hd] ++ tl
  | _ => failure

/-- `ProcedureSignature.mk [T₁, …] R` ↦ its parameter types and its return type. -/
private def delabSigParts : DelabM (Array Term × Term) := do
  guard ((← getExpr).isAppOfArity ``ProcedureSignature.mk 2)
  return (← withNaryArg 0 delabListElems, ← withNaryArg 1 delab)

/-- `HoleSigs.empty.append s₁ … .append sₙ` ↦ the `sᵢ`, in declaration order. -/
private partial def delabHoleSigs : DelabM (Array (Array Term × Term)) := do
  match (← getExpr).getAppFnArgs with
  | (``HoleSigs.empty, _) => return #[]
  | (``HoleSigs.append, args) => do
      guard (args.size == 2)
      let init ← withNaryArg 0 delabHoleSigs
      let sig ← withNaryArg 1 delabSigParts
      return init.push sig
  | _ => failure

/-- `Getter.mk fun st => e` — what `GaudiExpr[ e ]` builds — ↦ `e`.  Fails when the state
binder really occurs in `e`, since then `e` is not expressible in the surface syntax. -/
private def delabGaudiExpr : DelabM Term := do
  guard ((← getExpr).isAppOfArity ``Getter.mk 3)
  withNaryArg 2 do
    guard (← getExpr).isLambda
    withBindingBody stateBinderName do
      let stx ← delab
      guard <| !syntaxHasIdent stateBinderName stx
      return stx

/-- One component of an l-value: a nested `Lens.pair` prints as the tuple `(a, b)`. -/
private partial def delabLValueComponent : DelabM Term := do
  match (← getExpr).getAppFnArgs with
  | (``Lens.pair, args) => do
      guard (args.size == 6)
      let x ← withNaryArg 3 delabLValueComponent
      let y ← withNaryArg 4 delabLValueComponent
      `(($x, $y))
  | _ => delab

/-- The top-level comma list of an l-value lens (its right `Lens.pair` spine). -/
private partial def delabLValueList : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``Lens.pair, args) => do
      guard (args.size == 6)
      let x ← withNaryArg 3 delabLValueComponent
      let ys ← withNaryArg 4 delabLValueList
      return #[x] ++ ys
  | _ => return #[← delab]

/-- The l-value of an assignment/sample/call: `liftLens x` ↦ the components of `x`,
`Setter.throwaway` ↦ `_`. -/
private def delabLValue : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``Setter.throwaway, _) => return #[← `(_)]
  | (``liftLens, args) => do
      guard (args.size == 6)
      withNaryArg 5 delabLValueList
  | _ => failure

/-- Is the current sub-expression the throwaway l-value (a `call` with no result)? -/
private def isThrowaway : DelabM Bool := return (← getExpr).isAppOf ``Setter.throwaway

/-- The elements of the comma list inside a printed tuple.  The tuple parser keeps the tail
of the list in a further `null` node (`(a, b, c)` is `a , ‹b , ‹c››`), so flatten those. -/
private partial def tupleElems (s : Syntax) : Array Term :=
  s.getSepArgs.flatMap fun e => if e.isOfKind nullKind then tupleElems e else #[⟨e⟩]

/-- Split a printed argument tuple back into an argument list.  Any split is sound: the
`call` macro re-tuples the list with `mkArgTuple`, which is exactly how tuples print. -/
private def splitArgTuple (stx : Term) : Array Term :=
  if stx.raw.isOfKind ``Lean.Parser.Term.tuple then tupleElems (stx.raw.getArg 1) else #[stx]

/-- Peel `n` `let`/`have` binders whose values satisfy `isOk`, then run `k` on the binder
names, inside the local context they introduce. -/
private partial def withPeeledLets {α} [Inhabited α] (n : Nat) (isOk : Lean.Expr → Bool)
    (acc : Array Name) (k : Array Name → DelabM α) : DelabM α := do
  if n == 0 then k acc
  else
    match (← getExpr) with
    | .letE nm _ v _ _ => do
        guard (isOk v)
        guard <| !nm.hasMacroScopes
        withLetBody (withPeeledLets (n - 1) isOk (acc.push nm) k)
    | _ => failure

private def isHoleIndex (v : Lean.Expr) : Bool :=
  v.isAppOf ``HoleIndex.zero || v.isAppOf ``HoleIndex.succ

/-- The `letDecl` node for `x : T := v`.  `letDecl` is a parser, not a syntax category, so
there is no `` `(letDecl| …) `` quotation for it; we quote a whole `let` term instead and
pick the declaration out of it. -/
private def mkLetDecl (x : Ident) (t v : Term) :
    DelabM (TSyntax ``Lean.Parser.Term.letDecl) := do
  let stx ← `(let $x : $t := $v; ())
  let some d := stx.raw.find? (·.isOfKind ``Lean.Parser.Term.letDecl) | failure
  return ⟨d⟩

mutual

/-- A statement sequence: the right `seq` spine, flattened.  A Lean binder wrapping the rest
of the sequence (what a `let`/`have` statement elaborates to) becomes one statement carrying
that rest; `have` is the nondependent `let`, which is the only thing that tells the two apart
in the term. -/
private partial def delabGaudiStmts (holeNames : Array Name) :
    DelabM (Array (TSyntax `gaudi_stmt)) := do
  if let .letE nm _ _ _ nonDep := (← getExpr) then
    guard <| !nm.hasMacroScopes
    let ty ← withLetVarType delab
    let val ← withLetValue delab
    let decl ← mkLetDecl (mkIdent nm) ty val
    let body ← withLetBody (delabGaudiStmts holeNames)
    return #[← if nonDep then `(gaudi_stmt| have $decl:letDecl; $body:gaudi_stmt*)
               else `(gaudi_stmt| let $decl:letDecl; $body:gaudi_stmt*)]
  match (← getExpr).getAppFnArgs with
  | (``StmtWithHoles.seq, args) => do
      guard (args.size == 5)
      let hd ← withNaryArg 3 (delabGaudiStmtNested holeNames)
      let tl ← withNaryArg 4 (delabGaudiStmts holeNames)
      return #[hd] ++ tl
  | _ => return #[← delabGaudiStmt holeNames]

/-- A statement in the *left* position of a `seq`.  A `seq` there is printed as a block
`{ … }`, or re-parsing would re-associate it; so is a Lean binder, whose carried statement
list would otherwise be re-parsed greedily and swallow the rest of the enclosing sequence. -/
private partial def delabGaudiStmtNested (holeNames : Array Name) :
    DelabM (TSyntax `gaudi_stmt) := do
  if (← getExpr).isAppOf ``StmtWithHoles.seq || (← getExpr).isLet then
    let ss ← delabGaudiStmts holeNames
    `(gaudi_stmt| { $ss:gaudi_stmt* })
  else
    delabGaudiStmt holeNames

private partial def delabGaudiStmt (holeNames : Array Name) :
    DelabM (TSyntax `gaudi_stmt) := do
  match (← getExpr).getAppFnArgs with
  | (``StmtWithHoles.skip, _) => `(gaudi_stmt| skip;)
  | (``StmtWithHoles.assign, args) => do
      guard (args.size == 6)
      let lv ← withNaryArg 4 delabLValue
      let e ← withNaryArg 5 delabGaudiExpr
      `(gaudi_stmt| $lv:term,* <- $e;)
  | (``StmtWithHoles.sample, args) => do
      guard (args.size == 6)
      let lv ← withNaryArg 4 delabLValue
      let e ← withNaryArg 5 delabGaudiExpr
      `(gaudi_stmt| $lv:term,* <$ $e;)
  | (``StmtWithHoles.call, args) => do
      guard (args.size == 7)
      let void ← withNaryArg 4 isThrowaway
      let lv ← withNaryArg 4 delabLValue
      let p ← withNaryArg 5 delab
      let as := splitArgTuple (← withNaryArg 6 delabGaudiExpr)
      if void then `(gaudi_stmt| call $p ( $as:term,* );)
      else `(gaudi_stmt| $lv:term,* <- call $p ( $as:term,* );)
  | (``StmtWithHoles.hole, args) => do
      guard (args.size == 7)
      let idx ← withNaryArg 4 delab
      let void ← withNaryArg 5 isThrowaway
      let lv ← withNaryArg 5 delabLValue
      let as := splitArgTuple (← withNaryArg 6 delabGaudiExpr)
      -- inside its `proc`, a hole is called with `call` (that is what the macro rewrites);
      -- anywhere else the internal `holecall` form is the only faithful spelling.
      if idx.raw.isIdent && holeNames.contains idx.raw.getId then
        if void then `(gaudi_stmt| call $idx ( $as:term,* );)
        else `(gaudi_stmt| $lv:term,* <- call $idx ( $as:term,* );)
      else
        if void then `(gaudi_stmt| holecall $idx ( $as:term,* );)
        else `(gaudi_stmt| $lv:term,* <- holecall $idx ( $as:term,* );)
  | (``StmtWithHoles.ifThenElse, args) => do
      guard (args.size == 6)
      let c ← withNaryArg 3 delabGaudiExpr
      let t ← withNaryArg 4 (delabGaudiStmts holeNames)
      -- `if (c) { … }` elaborates with `skip` as its else branch, so print the short form
      let noElse ← withNaryArg 5 (return (← getExpr).isAppOf ``StmtWithHoles.skip)
      if noElse then `(gaudi_stmt| if ($c) { $t:gaudi_stmt* })
      else
        let f ← withNaryArg 5 (delabGaudiStmts holeNames)
        `(gaudi_stmt| if ($c) { $t:gaudi_stmt* } else { $f:gaudi_stmt* })
  | (``StmtWithHoles.while, args) => do
      guard (args.size == 5)
      let c ← withNaryArg 3 delabGaudiExpr
      let body ← withNaryArg 4 (delabGaudiStmts holeNames)
      `(gaudi_stmt| while ($c) { $body:gaudi_stmt* })
  | _ => failure

end

/-- Print a `StmtWithHoles` as `GaudiProg[ … ]`. -/
@[delab app.GaudisCrypt.StmtWithHoles.skip, delab app.GaudisCrypt.StmtWithHoles.assign,
  delab app.GaudisCrypt.StmtWithHoles.sample, delab app.GaudisCrypt.StmtWithHoles.call,
  delab app.GaudisCrypt.StmtWithHoles.hole, delab app.GaudisCrypt.StmtWithHoles.seq,
  delab app.GaudisCrypt.StmtWithHoles.ifThenElse, delab app.GaudisCrypt.StmtWithHoles.while]
private def delabGaudiProg : Delab := do
  guardSurfaceSyntax
  let stmts ← delabGaudiStmts #[]
  `(GaudiProg[ $stmts:gaudi_stmt* ])

/-- The names bound by the `let`/`have` statements on the spine of a printed statement
sequence, outermost first — exactly the binders `wrapSpineBinders` repeats around the return
value.  (`letI`/`haveI` inline during elaboration, so no binder of theirs is in either term.) -/
private partial def spineLetNames (ss : Array (TSyntax `gaudi_stmt)) : Array Name := Id.run do
  for s in ss do
    match s with
    | `(gaudi_stmt| let $d:letDecl; $rest:gaudi_stmt*)
    | `(gaudi_stmt| have $d:letDecl; $rest:gaudi_stmt*) =>
        let n := match d.raw.find? (·.isIdent) with
          | some i => i.getId
          | none => Name.anonymous
        return #[n] ++ spineLetNames rest
    | _ => pure ()
  return #[]

/-- Print a procedure built by `proc` as `proc (…) uses (…) : R { … }`. -/
@[delab app.GaudisCrypt.ProcedureWithHoles.mk]
private def delabProc : Delab := do
  guardSurfaceSyntax
  guard ((← getExpr).getAppNumArgs == 6)
  let (paramTys, retTy) ← withNaryArg 2 delabSigParts
  let holeSigs ← withNaryArg 1 delabHoleSigs
  let localTys ← withNaryArg 3 delabLocalTypes
  -- the body: the parameter, local-variable and hole `let`s, then the statements
  let (paramNames, localNames, holeNames, stmts) ← withNaryArg 4 <|
    withPeeledLets paramTys.size (·.isAppOf ``Lens.intoParams) #[] fun ps =>
      withPeeledLets localTys.size (·.isAppOf ``Lens.intoVars) #[] fun ls =>
        withPeeledLets holeSigs.size isHoleIndex #[] fun hs => do
          return (ps, ls, hs, ← delabGaudiStmts hs)
  -- the return value repeats the parameter and local-variable `let`s (but not the holes), and
  -- then the binders on the body's spine, which scope over it too
  let spineNames := spineLetNames stmts
  let (retParams, retLocals, retSpine, ret) ← withNaryArg 5 <|
    withPeeledLets paramTys.size (·.isAppOf ``Lens.intoParams) #[] fun ps =>
      withPeeledLets localTys.size (·.isAppOf ``Lens.intoVars) #[] fun ls =>
        withPeeledLets spineNames.size (fun _ => true) #[] fun bs => do
          return (ps, ls, bs, ← delabGaudiExpr)
  guard (retParams == paramNames && retLocals == localNames && retSpine == spineNames)
  let params ← (paramNames.zip paramTys).mapM fun (n, t) =>
    `(proc_binder| $(mkIdent n):ident : $t)
  let locals ← (localNames.zip localTys).mapM fun (n, t) =>
    `(proc_binder| $(mkIdent n):ident : $t)
  let holes ← (holeNames.zip holeSigs).mapM fun (n, (ps, r)) =>
    `(hole_binder| $(mkIdent n):ident : ( $ps:term,* ) → $r)
  let varLines : Array (Syntax.TSepArray `proc_binder ",") :=
    if locals.isEmpty then #[] else #[locals]
  if holes.isEmpty then
    `(proc ( $params:proc_binder,* ) : $retTy {
        $[var $varLines:proc_binder,* ;]*
        $stmts:gaudi_stmt*
        return $ret })
  else
    `(proc ( $params:proc_binder,* ) uses ( $holes:hole_binder,* ) : $retTy {
        $[var $varLines:proc_binder,* ;]*
        $stmts:gaudi_stmt*
        return $ret })

end Printing

end GaudisCrypt

-- TODO: A `Getter` on its own still prints as `{ get := fun st => … }`, not as
--   `GaudiExpr[ … ]` (statements and procedures do print in surface syntax).
-- TODO: Allow _ inside a *tuple* lvalue too (a bare `_` already becomes Setter.throwaway)

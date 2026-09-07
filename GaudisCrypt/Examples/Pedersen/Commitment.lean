import GaudisCrypt.Syntax.Syntax

/-!
# Generic commitment schemes

A transliteration of EasyCrypt's `theories/crypto/Commitment.ec` (theory
`CommitmentProtocol`) into the Gaudí module/procedure syntax.

* EC's abstract theory types `value`, `message`, `commitment`, `openingkey` become the
  type class `CommitmentTypes` (instance-implicit section parameters, so the
  `moduletype`-generated definitions elaborate — the same pattern as `[ProgramSpec]`).
* EC `module type`s become `moduletype`s.
* EC's parameterized modules (`Correctness(S)`, `HidingExperiment(S,U)`,
  `BindingExperiment(S,B)`) become `module X (P : T) { … }` declarations: the calls are written
  against the parameters' own fields and the holes are inferred from them.
-/

namespace GaudisCrypt.Examples.Pedersen

/-
Still open:
- Maybe also support `let A := module ...` or `def A := module ...`
- `DoesNotUse A X.op` (in a proof, do induction, derive ⊥ from a use of `X.op`) — nothing of
  the sort exists yet.
-/

open GaudisCrypt


/-- The abstract types of EC's `theory CommitmentProtocol`: the public value (key), the
    message space, commitments, and opening keys.  `Inhabited` is needed for program
    local variables of these types — that one is real content (a default value has to *exist*).

    There is deliberately **no** `DecidableEq` here.  It was a field (`message_deceq`), justified
    by EC's binding experiment comparing `m ≠ m'`, but decidability is never needed for *proofs* —
    only to form a `Bool`-valued program expression via `BEq` — and no program in this development
    compares messages, so nothing consumed it.  (`Commitment` never had one either, and that has
    never been missed.)  When `BindingExperiment` does need `m ≠ m'`, note that these programs are
    never executed — the semantics is a measure and every `proc` is `noncomputable` — so
    `Classical.decEq` at the point of use is enough; a class field buys nothing.  See
    `Lib/RO/CollisionResistance.lean`, which does exactly that. -/
class CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  -- Local variables need a default: `localDefaults` (Language/Programs.lean) takes
  -- `List (Σ t : Type, Inhabited t)` and projects `.default`, so `Inhabited`-as-data is what the
  -- *language* demands, not a choice made here.
  --
  -- TODO "change to Nonempty": tried 2026-08-07 — it does work (carry `Nonempty`, derive
  -- `Inhabited` via `Classical.inhabited_of_nonempty`; whole build passes).  Reverted, because:
  --  (1) it removes nothing — the DSL still needs the data, so it only relabels who supplies the
  --      witness: same field count, plus four indirections;
  --  (2) unlike `Decidable`, `Inhabited` is *not* a subsingleton, so the classical default is not
  --      a different-but-equal witness, it is potentially a different *element*, with no
  --      `Subsingleton.elim` to bridge it — harmless only while every local is written before
  --      it is read, which the types do not enforce.
  -- If it is worth doing, the place is `localDefaults` itself: have locals require `Nonempty` and
  -- take the default classically *once*, so every downstream class benefits and `PedersenGroup`
  -- does not end up inconsistent with this one.
  value_inhabited : Inhabited Value
  message_inhabited : Inhabited Message
  commitment_inhabited : Inhabited Commitment
  openingKey_inhabited : Inhabited OpeningKey



-- TODO Make CommitmentTypes into a structure
-- variable (types : CommitmentTypes) in the section
--
-- Investigated 2026-08-07.  NOT fundamentally blocked — it is a fixable limitation of the
-- `moduletype` command, in two specific places.  What actually fails:
--
--  (1) The command emits a chain of definitions in which the later ones reference the earlier
--      ones *by bare name*:
--          def X.typeRep : ModuleTypeRep := …
--          def X := Module X.typeRep                    -- ← bare `X.typeRep`
--          instance : IsModule X where moduleTypeRep := X.typeRep
--      With a *class* section variable this works by luck: `X.typeRep` picks up an
--      instance-implicit parameter and each bare reference re-resolves it by instance synthesis.
--      With an explicit `(types : CTypes)` the auto-bound variable makes it
--      `X.typeRep : CTypes → ModuleTypeRep`, and the bare reference is then a *function* where a
--      `ModuleTypeRep` is wanted:
--          "Application type mismatch: X.typeRep has type CTypes → ModuleTypeRep but is
--           expected to have type ModuleTypeRep"
--      Fix: thread the explicit section variables through the command's own cross-references.
--
--  (2) The generated accessors are plain `def`s.  Lean infers `noncomputable` for them by itself
--      in the class form (checked: `CommitmentScheme.gen` is noncomputable today), but in the
--      structure form it demands the keyword.  Fix: emit `noncomputable def` — harmless either
--      way, since they are noncomputable regardless.
--
-- Everything else is fine.  The `Inhabited` facts stay reachable (`instance : Inhabited
-- types.Value := types.value_inhabited` works — the goal determines `types` by inverting the
-- projection), and hand-writing what `moduletype` *would* emit, with `types` threaded through,
-- elaborates completely, accessors and `mk`/round-trip lemma included.
--
-- So the earlier note here ("the class form is forced") was right about the *mechanism* but
-- wrong to call it inherent.  Cost of doing it: the two command fixes above, plus writing
-- `types.Value` instead of `Value` everywhere (the `open CommitmentTypes (Value …)` shorthand
-- goes away).  That is a `Language/Syntax2.lean` change, i.e. Dominique's call.

/- DON'T DO:

class NonEmptyCommitmentTypes (types : CommitmentTypes) where
  nonempty_value : Nonempty types.Value
  nonempty_message : Nonempty types.Message
  nonempty_commitment : Nonempty types.Commitment
  nonempty_openingKey : Nonempty types.OpeningKey

  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Value := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Message := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.Commitment := sorry
  instance (t : CommitmentTypes) [NonEmptyCommitmentTypes t] : Nonempty t.OpeningKey := sorry

instance (t : CommitmentTypes) [Nonempty t.Value] [Nonempty t.Message] [Nonempty t.Commitment]
[Nonempty t.OpeningKey] : NonEmptyCommitmentTypes t :=
sorry

  variable (types : CommitmentTypes)
  variable [NonEmptyCommitmentTypes types]
-/


/-

module type T {t} (x:Nat) ...

module T {t} (x) using (B:Module) : ... {...}

module  {t} (x): T (B:Module) : ... {...}

module Correctness using (S:CommitmentScheme) : @T Nat 17 {...}

module Correctness (S:CommitmentScheme) : @T Nat 17 {...}

module A [{t} (x:Nat) (C:Module)] (B:Module ...) : @T Nat 17 {...}

module {params : X} A (C : Module ...) : @T Nat 17 {...}

module A (C : Module ...) using (params : ZZ) : @T Nat 17 {...}

module A (params : ZZ) [C : Module ...]  : @T Nat 17 {...}

module A params (moduleparameters)

Rules:
- if nothing behind A: clear.
- if something behind A, last thing in parens with commans (tuple) -> last is module params
- if something behind A, last thing not in parents -> no module params
- if word `using` in between -> module params are after `using`
- something behind A, last thing in parens -> heuristic:
  - if argument has IsModule instance, module param
  - else not

Alternative:
- module A (moduleparamsters)
- module A params using (moduleparameters)
- module A
- module A params using

Alternative:
- module A params using (moduleparameters)
- module A using (moduleparameters)
- module A
- module A params
  - if last param is (...), and tuple (has comma) -> syntax error but with hint: "maybe you meant to use `using`"
  - if last param is (x:T) and `IsModule T` -> warning: "maybe you meant to use `using`"
    can be disabled by linter exception options

-/

def f (x y : Nat) : Nat := x + y

instance [CommitmentTypes] : Inhabited CommitmentTypes.Value :=
  CommitmentTypes.value_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Message :=
  CommitmentTypes.message_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.Commitment :=
  CommitmentTypes.commitment_inhabited
instance [CommitmentTypes] : Inhabited CommitmentTypes.OpeningKey :=
  CommitmentTypes.openingKey_inhabited

/-! ### Disjointness of tuple-projection lenses

The `proc` macro binds each local variable to a `Lens.id.ofst/.osnd` projection chain into
the local-state tuple; tuple *assignment* (`c, d <- …`) pairs those lenses via `Lens.pair`,
which needs them `disjoint`.  Distinct projection paths are always disjoint, and the instances
deriving that (`Lens.disjoint_ofst_osnd`, `Lens.disjoint_chain`, …) now live in
`Language/Lens.lean` — the "move them to the proper place" TODO that used to sit here is done,
and they are no longer declared in this file.

They do fire by themselves, including for *locals*, and `Correctness` below writes
`c,d <- call S.commit (…)` with nothing supplied by hand.  That took two `@[reducible]`s in
`Language/Programs.lean`, both there for this reason and worth not undoing:

* `paramListToTuple`, so a concrete type list shows unification the `_ × _` the
  `o`-instances are stated for (it is also what lets a numeral argument of a `call` go
  through without an ascription);
* `localTypes`, which replaced `locals.map (·.fst)` in `LocalVariableState.vars`.  `List.map`
  is *not* reducible, so with it the argument of `paramListToTuple` stayed stuck at
  `reducible` transparency, `paramListToTuple` could not match on it, and the tuple never
  opened up.  `Lens.intoVars` inherited that and could not be stated around it, since its
  argument type *is* that tuple — which is why every locals lens went through `List.map` by
  construction, while parameters (a literal list) escaped.

Before that, the assignment failed as
```
c, d   <- call S.commit (…);   -- failed to synthesize instance of type class  disjoint c d
(c, d) <- call S.commit (…);   -- same; `[lvalRaw|]` sends the tuple to `Lens.pair` either way
```
and had to be preceded by an explicit `haveI : disjoint c d := Lens.disjoint_chain …`, peeling
the `chain` prefix the two lenses share down to the slot where they differ.  Two things that
look like causes here are not: that the macro binds locals as `let`-variables (4.31 instance
search does unfold local `let`s — a plain `def` is what is opaque at `reducible`), and
`Lens.intoVars` itself (`Programs.disjoint_intoVars` peels it fine once the slots are
disjoint).

`HidingExperiment` and `BindingExperiment` used to work around it with pair-typed locals read
through `$`-projections (`var cd : Commitment × OpeningKey`, then `($cd).1`/`($cd).2`); they
are now written as one `var` per component, `BindingExperiment` taking a five-wide tuple
apart in a single assignment. -/

-- TODO: changes to named variable if CommitmentTypes becomes a structure (but see the
-- ⚠ above: that may be blocked)
variable [ProgramSpec] [CommitmentTypes]

-- With structure, replace by `local(?) abbrev Value := CommitmentTypes.Value types` etc.
-- and remove the `open` below
open CommitmentTypes (Value Message Commitment OpeningKey)

/-! ## Module types

```
module type CommitmentScheme = {
  proc gen() : value
  proc commit(x: value, m: message) : commitment * openingkey
  proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
}.
``` -/

moduletype CommitmentScheme {
  proc gen () -> Value;
  proc commit (Value, Message) -> Commitment × OpeningKey;
  proc verify (Value, Message, Commitment, OpeningKey) -> Bool;
}

-- EC's `Unhider`: the hiding-game adversary.
moduletype Unhider {
  proc choose (Value) -> Message × Message;
  proc guess (Commitment) -> Bool;
}

-- EC's `Binder`: the binding-game adversary.
moduletype Binder {
  proc bind (Value) -> Commitment × Message × OpeningKey × Message × OpeningKey;
}


example : CommitmentScheme = Module CommitmentScheme.typeRep := rfl


-- TODO: Dominique: move somewhere probably
/-- `params` and `vars` are distinct fields of `LocalVariableState`, so writes through
    projections of the two commute — no hypothesis on `x`, `y` needed. -/
instance LocalVariableState.disjoint_varsL_paramsL {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple (localTypes locals))}
    {y : Lens b (paramListToTuple paramTypes)} :
    disjoint (LocalVariableState.varsL.chain x) (LocalVariableState.paramsL.chain y) :=
  ⟨fun _ _ _ => rfl⟩

-- TODO: Dominique: move somewhere probably
/-- The mirror image of `LocalVariableState.disjoint_varsL_paramsL`; `disjoint.symm` is a
    theorem, not an instance, so search needs both orientations spelled out. -/
instance LocalVariableState.disjoint_paramsL_varsL {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple paramTypes)}
    {y : Lens b (paramListToTuple (localTypes locals))} :
    disjoint (LocalVariableState.paramsL.chain x) (LocalVariableState.varsL.chain y) :=
  ⟨fun _ _ _ => rfl⟩

-- TODO: Dominique: move somewhere probably
/-- Parameter-slot counterpart of `Programs.disjoint_intoVars`: distinct parameter slots stay
    disjoint after `intoParams` (two `chain` layers). -/
instance Programs.disjoint_intoParams {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple paramTypes)}
    {y : Lens b (paramListToTuple paramTypes)} [disjoint x y] :
    disjoint (Lens.intoParams (locals := locals) x) y.intoParams :=
  Lens.disjoint_chain ProcedureState.localL _ _

instance Programs.disjoint_intoVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple (localTypes locals))}
    {y : Lens b (paramListToTuple (localTypes locals))} [disjoint x y] :
    disjoint (Lens.intoVars (paramTypes := paramTypes) x) y.intoVars :=
  Lens.disjoint_chain ProcedureState.localL _ _

-- TODO: Dominique: move somewhere probably
/-- A local variable is disjoint from *any* parameter: they live in different fields of the
    scope record, so no `disjoint x y` hypothesis is required. -/
instance Programs.disjoint_intoVars_intoParams {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple (localTypes locals))}
    {y : Lens b (paramListToTuple paramTypes)} :
    disjoint (Lens.intoVars (paramTypes := paramTypes) x) (Lens.intoParams (locals := locals) y) :=
  Lens.disjoint_chain ProcedureState.localL _ _

-- TODO: Dominique: move somewhere probably
/-- The other orientation of `Programs.disjoint_intoVars_intoParams`. -/
instance Programs.disjoint_intoParams_intoVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple paramTypes)}
    {y : Lens b (paramListToTuple (localTypes locals))} :
    disjoint (Lens.intoParams (locals := locals) x) (Lens.intoVars (paramTypes := paramTypes) y) :=
  Lens.disjoint_chain ProcedureState.localL _ _



/- EC's `module Correctness (S : CommitmentScheme) = { proc main(m) = { … } }` — the module
command takes the parameter directly, so the calls are written against `S`'s own fields and the
holes are inferred from them.

(A `/-- … -/` docstring cannot be attached: the `module` command does not accept one, same gap
as `moduletype`.)

That replaces the hand-written functor this used to be: a `proc … uses (gen, commit, verify)`
body plus an explicit `ModuleExpression.abs` wrapping a `.pair`/`.fst`/`.snd` adapter that
repackaged the scheme record into the holes tuple.  The command derives exactly that adapter —
`(.var 0).snd.snd` for `verify`, `.snd.fst` for `commit`, `.fst` for `gen`, right-nested and
reversed — from the call sites, so the two really are the same term; it just is not written out
by hand any more (which is what Dominique's TODO at the bottom of `Syntax2.lean` was asking for).

It declares `Correctness.main.procedure` (the body, with its holes), `Correctness.main` (that
procedure as a functor of `S`), `Correctness` itself, and `Correctness.apply_simp`. -/
module Correctness (S : CommitmentScheme) {
  proc main(m : Message) : Bool {
    var x : Value;
    var c : Commitment;
    var d : OpeningKey;
    var b : Bool;
    x <- call S.gen ();
    c,d <- call S.commit ($x, $m);
    b <- call S.verify ($x, $m, $c, $d);
    return $b
  };
}

#check Correctness.main.procedure
#print Correctness.main.procedure
#check Correctness.main
#print Correctness.main
#print Correctness


/-- `Correctness(S)` elaborates: the functor applies to any `S : CommitmentScheme`. -/
noncomputable example (S : CommitmentScheme) : procmod (Message) -> Bool :=
  Module.app Correctness S

/- EC's
```
module HidingExperiment (S:CommitmentScheme, U:Unhider) = {
  proc main() : bool = {
    x        <@ S.gen();
    (m0, m1) <@ U.choose(x);
    b        <$ {0,1};
    (c, d)   <@ S.commit(x, b ? m1 : m0);
    b'       <@ U.guess(c);
    return (b = b');
  }
}.
```
Two module parameters, so `HidingExperiment` is a functor of the *pair* and each field is a
functor of the parameters it uses (both, here).  `{0,1}` is `SubProbability.uniform` at `Bool`.

`(m0, m1)` and `(c, d)` are tuple assignments, one local per component, as in EC. -/
module HidingExperiment (S : CommitmentScheme, U : Unhider) {
  proc main() : Bool {
    var x : Value;
    var m0 : Message;
    var m1 : Message;
    var b : Bool;
    var c : Commitment;
    var d : OpeningKey;
    var bg : Bool;
    x <- call S.gen ();
    m0,m1 <- call U.choose ($x);
    b <$ SubProbability.uniform;
    c,d <- call S.commit ($x, if $b then $m1 else $m0);
    bg <- call U.guess ($c);
    return $b == $bg
  };
}

/-- `HidingExperiment(S, U)` elaborates, for any scheme and any adversary. -/
noncomputable example (S : CommitmentScheme) (U : Unhider) :
    procmod () -> Bool :=
  Module.app (Module.app HidingExperiment.main S) U

/- `BindingExperiment` is the one place a *message comparison* is needed (`m <> m'`).  Rather than
a `DecidableEq` field on `CommitmentTypes` — see the note there — it is supplied classically right
where it is used: the program is never executed, so the comparison only has to denote a `Bool`.
`local`, so it does not leak to importers. -/
noncomputable local instance : DecidableEq Message := Classical.decEq _

/- EC's
```
module BindingExperiment (S:CommitmentScheme, B:Binder) = {
  proc main() : bool = {
    x                 <@ S.gen();
    (c, m, d, m', d') <@ B.bind(x);
    v                 <@ S.verify(x, m , c, d );
    v'                <@ S.verify(x, m', c, d');
    return v /\ v' /\ (m <> m');
  }
}.
```
`Binder.bind` returns `commitment * message * openingkey * message * openingkey`, taken apart
by a five-wide tuple assignment — note `verify` takes the components in the order
`(x, m, c, d)`, not the order they arrive in. -/
module BindingExperiment (S : CommitmentScheme, B : Binder) {
  proc main() : Bool {
    var x : Value;
    var c : Commitment;
    var m : Message;
    var d : OpeningKey;
    var m' : Message;
    var d' : OpeningKey;
    var v : Bool;
    var v' : Bool;
    x <- call S.gen ();
    c,m,d,m',d' <- call B.bind ($x);
    v <- call S.verify ($x, $m, $c, $d);
    v' <- call S.verify ($x, $m', $c, $d');
    return $v && $v' && !($m == $m')
  };
}

/-- `BindingExperiment(S, B)` elaborates, for any scheme and any binder. -/
noncomputable example (S : CommitmentScheme) (B : Binder) :
    procmod () -> Bool :=
  Module.app (Module.app BindingExperiment.main S) B


end GaudisCrypt.Examples.Pedersen

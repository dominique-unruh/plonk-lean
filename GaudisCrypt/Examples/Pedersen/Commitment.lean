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

class CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
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
-- TODO remove
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
    -- TODO: Make this work (needs have's to also surround the return statement in parsing)
    have _: DecidableEq Message := Classical.decEq _; -- Could be global, but we want to demo ths feature
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

import GaudisCrypt.Syntax.Syntax

/-!
# Generic commitment schemes

A transliteration of EasyCrypt's `theories/crypto/Commitment.ec` (theory
`CommitmentProtocol`) into the Gaudí module/procedure syntax.

* EC's abstract theory types `value`, `message`, `commitment`, `openingkey` become the fields of
  the structure `CommitmentTypes`, passed as an explicit Lean parameter `(types : CommitmentTypes)`
  to every `moduletype` and `module` that mentions one of them.
* EC `module type`s become `moduletype`s.
* EC's parameterized modules (`Correctness(S)`, `HidingExperiment(S,U)`,
  `BindingExperiment(S,B)`) become `module X … using (P : T) { … }` declarations: the calls are
  written against the parameters' own fields and the holes are inferred from them.
-/

namespace GaudisCrypt.Examples.Pedersen

/-
Still open:
- Maybe also support `let A := module ...` or `def A := module ...`
- `DoesNotUse A X.op` (in a proof, do induction, derive ⊥ from a use of `X.op`) — nothing of
  the sort exists yet.
-/

open GaudisCrypt

structure CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  -- TODO mark this as instances, e.g. [value_inhabited : Inhabited Value], then see whether we can omit some explicit instances belowwww
  value_inhabited : Inhabited Value
  message_inhabited : Inhabited Message
  commitment_inhabited : Inhabited Commitment
  openingKey_inhabited : Inhabited OpeningKey

-- The `Inhabited` facts stay reachable: the goal determines `types` by inverting the projection.
instance (types : CommitmentTypes) : Inhabited types.Value := types.value_inhabited
instance (types : CommitmentTypes) : Inhabited types.Message := types.message_inhabited
instance (types : CommitmentTypes) : Inhabited types.Commitment := types.commitment_inhabited
instance (types : CommitmentTypes) : Inhabited types.OpeningKey := types.openingKey_inhabited

variable [ProgramSpec]

/-! ## Module types

```
module type CommitmentScheme = {
  proc gen() : value
  proc commit(x: value, m: message) : commitment * openingkey
  proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
}.
``` -/

moduletype CommitmentScheme (types : CommitmentTypes) {
  proc gen () -> (types.Value);
  proc commit (types.Value, types.Message) -> types.Commitment × types.OpeningKey;
  proc verify (types.Value, types.Message, types.Commitment, types.OpeningKey) -> Bool;
}

-- EC's `Unhider`: the hiding-game adversary.
moduletype Unhider (types : CommitmentTypes) {
  proc choose (types.Value) -> types.Message × types.Message;
  proc guess (types.Commitment) -> Bool;
}

-- EC's `Binder`: the binding-game adversary.
moduletype Binder (types : CommitmentTypes) {
  proc bind (types.Value) ->
    types.Commitment × types.Message × types.OpeningKey × types.Message × types.OpeningKey;
}

module Correctness (types : CommitmentTypes) using (S : CommitmentScheme types) {
  proc main(m : types.Message) : Bool {
    var x : types.Value;
    var c : types.Commitment;
    var d : types.OpeningKey;
    var b : Bool;
    x <- call S.gen ();
    c,d <- call S.commit ($x, $m);
    b <- call S.verify ($x, $m, $c, $d);
    return $b
  };
}

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
module HidingExperiment (types : CommitmentTypes)
    using (S : CommitmentScheme types, U : Unhider types) {
  proc main() : Bool {
    var x : types.Value;
    var m0 : types.Message;
    var m1 : types.Message;
    var b : Bool;
    var c : types.Commitment;
    var d : types.OpeningKey;
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
noncomputable example (types : CommitmentTypes) (S : CommitmentScheme types) (U : Unhider types) :
    procmod () -> Bool :=
  Module.app (Module.app (HidingExperiment.main types) S) U

/- `BindingExperiment` is the one place a *message comparison* is needed (`m <> m'`).  Rather than
a `DecidableEq` field on `CommitmentTypes` — see the note there — it is supplied classically right
where it is used: the program is never executed, so the comparison only has to denote a `Bool`.
`local`, so it does not leak to importers. -/
-- TODO remove
noncomputable local instance (types : CommitmentTypes) : DecidableEq types.Message :=
  Classical.decEq _

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
module BindingExperiment (types : CommitmentTypes)
    using (S : CommitmentScheme types, B : Binder types) {
  proc main() : Bool {
    var x : types.Value, c : types.Commitment;
    -- TODO: syntax to allow to write `var m m' : types.Message` instead:
    var m : types.Message, m' : types.Message;
    var d : types.OpeningKey, d' : types.OpeningKey;
    var v : Bool, v' : Bool;
    -- TODO: Make this work (needs have's to also surround the return statement in parsing)
    have _: DecidableEq types.Message := Classical.decEq _; -- Could be global, but we want to demo ths feature
    x <- call S.gen ();
    c,m,d,m',d' <- call B.bind ($x);
    v <- call S.verify ($x, $m, $c, $d);
    v' <- call S.verify ($x, $m', $c, $d');
    return $v && $v' && !($m == $m')
  };
}

end GaudisCrypt.Examples.Pedersen

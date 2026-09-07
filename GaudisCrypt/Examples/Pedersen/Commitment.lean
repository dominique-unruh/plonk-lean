import GaudisCrypt.Syntax.Syntax

/-!
# Generic commitment schemes

A transliteration of EasyCrypt's `theories/crypto/Commitment.ec` (theory
`CommitmentProtocol`) into the Gaudí module/procedure syntax.

* EC's abstract theory types `value`, `message`, `commitment`, `openingkey` become the fields of
  the structure `CommitmentTypes`, declared here as a section `variable (types : CommitmentTypes)`
  and hence a Lean parameter of every `moduletype` and `module` below that mentions one of them.
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
  the sort exists yet.  --> Need clarification: is this something Denis wanted?
-/

open GaudisCrypt

structure CommitmentTypes where
  Value : Type
  Message : Type
  Commitment : Type
  OpeningKey : Type
  [value_inhabited : Inhabited Value]
  [message_inhabited : Inhabited Message]
  [commitment_inhabited : Inhabited Commitment]
  [openingKey_inhabited : Inhabited OpeningKey]

@[reducible] instance (types : CommitmentTypes) : Inhabited types.Value := types.value_inhabited
@[reducible] instance (types : CommitmentTypes) : Inhabited types.Message := types.message_inhabited
@[reducible] instance (types : CommitmentTypes) : Inhabited types.Commitment := types.commitment_inhabited
@[reducible] instance (types : CommitmentTypes) : Inhabited types.OpeningKey := types.openingKey_inhabited

variable [ProgramSpec]

variable (types : CommitmentTypes)

/-! ## Module types

```
module type CommitmentScheme = {
  proc gen() : value
  proc commit(x: value, m: message) : commitment * openingkey
  proc verify(x: value, m: message, c: commitment, d: openingkey) : bool
}.
``` -/

moduletype CommitmentScheme {
  proc gen () -> (types.Value);
  proc commit (types.Value, types.Message) -> types.Commitment × types.OpeningKey;
  proc verify (types.Value, types.Message, types.Commitment, types.OpeningKey) -> Bool;
}

-- EC's `Unhider`: the hiding-game adversary.
moduletype Unhider {
  proc choose (types.Value) -> types.Message × types.Message;
  proc guess (types.Commitment) -> Bool;
}

-- EC's `Binder`: the binding-game adversary.
moduletype Binder {
  proc bind (types.Value) ->
    types.Commitment × types.Message × types.OpeningKey × types.Message × types.OpeningKey;
}

module Correctness using (S : CommitmentScheme types) {
  proc main(m : types.Message) : Bool {
    var x : types.Value;
    var c : types.Commitment, d : types.OpeningKey;
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
module HidingExperiment using (S : CommitmentScheme types, U : Unhider types) {
  proc main() : Bool {
    var x : types.Value;
    var m0 m1 : types.Message;
    var b b' : Bool;
    var c : types.Commitment, d : types.OpeningKey;
    x <- call S.gen ();
    m0,m1 <- call U.choose ($x);
    b <$ SubProbability.uniform;
    c,d <- call S.commit ($x, if $b then $m1 else $m0);
    b' <- call U.guess ($c);
    return $b == $b'
  };
}

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
`(x, m, c, d)`, not the order they arrive in.

This is also the one place a *message comparison* is needed (`m <> m'`).  Rather than a
`DecidableEq` field on `CommitmentTypes`, it is supplied classically right where it is used, by
a `have` in the body: the program is never executed, so the comparison only has to denote a
`Bool`.  The `have` scopes over the `return` too, which is where the comparison sits. -/
module BindingExperiment using (S : CommitmentScheme types, B : Binder types) {
  proc main() : Bool {
    var x : types.Value, c : types.Commitment;
    var m m' : types.Message;
    var d d' : types.OpeningKey;
    var v v' : Bool;
    -- Could be a global instance, but this demonstrates a local `have` inside a procedure body:
    have _ : DecidableEq types.Message := Classical.decEq _;
    x <- call S.gen ();
    c,m,d,m',d' <- call B.bind ($x);
    v <- call S.verify ($x, $m, $c, $d);
    v' <- call S.verify ($x, $m', $c, $d');
    return $v && $v' && !($m == $m')
  };
}

#print BindingExperiment.main.procedure

end GaudisCrypt.Examples.Pedersen

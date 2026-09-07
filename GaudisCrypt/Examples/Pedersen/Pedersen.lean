import GaudisCrypt.Examples.Pedersen.Commitment
import GaudisCrypt.WeakestPreconditions

/-!
# The Pedersen commitment scheme

A transliteration of EasyCrypt's `examples/Pedersen.ec`:

* EC's `clone DLog` (cyclic group `group` with generator `g`, prime exponent field `exp`)
  becomes the class `PedersenGroup`: the operations the programs mention, plus the laws the
  proofs turned out to need (`f_commring`, `gpow_add`, `gpow_mul` — the last two are EC's
  `expD`/`expM`).
* EC's `PedersenTypes` + the `Commitment` clone become the `CommitmentTypes` record
  `pedersenTypes` (value/commitment = group, message/openingkey = exponent), which every
  `CommitmentScheme`-shaped name here is applied to.
* `module Pedersen : CommitmentScheme` becomes a
  `module Pedersen : (CommitmentScheme pedersenTypes) { … }` declaration — EC's own syntax, near
  enough, now that the `module` command exists.
* Correctness is stated as EC states it (`hoare[Correctness(Pedersen).main : true ==> res]`):
  the output distribution puts no mass on `res = false`.  Proven (`pedersen_correctness`), on
  standard axioms only, entirely on the `module` command's generated lemmas — this file declares
  nothing of its own for it beyond the per-procedure `wp_*` lemmas.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt

-- the scheme is deliberately named like the enclosing example namespace (EC: `module Pedersen`)
set_option linter.dupNamespace false

/-! ## The group setup (EC's `DLog` clone) -/

/-- A cyclic group `G` with generator `g` and exponent type `F` (EC's `group`/`exp`).
    Multiplication and exponentiation, what the programs genuinely need of the types — a default
    element (`Inhabited`, so local variables can be declared) and `Fintype F` (real content:
    `SubProbability.uniform` samples it, and the wp lemmas sum over it) — and the algebraic laws
    the proofs need, which are the three fields documented individually below.  Correctness needs
    none of the laws; they are all for `Hiding.lean`.

    Decidable equality is *not* a field.  `verify` does compare (`$c == $c'`), and `==` is `BEq`
    derived from `DecidableEq` — but these programs are never executed: every `proc` is
    `noncomputable` and the semantics is a measure, so the comparison only ever has to *denote* a
    `Bool`, not compute one.  `Classical.decEq` supplies that for free, which is why the instances
    below are classical and the class is two fields shorter.  Nothing in the proofs cares: they
    reason about `=`, and `beq_self_eq_true` and friends hold for any `DecidableEq` witness. -/
class PedersenGroup where
  G : Type
  F : Type
  g : G
  gmul : G → G → G
  gpow : G → F → G
  g_inhabited : Inhabited G
  f_inhabited : Inhabited F
  f_fintype : Fintype F
  /-- EC's exponent type is the prime field `DL.GP.ZModE`; the hiding proof forms `d + x * m`
      and its inverse `d - x * m`, so the additive group and the multiplication are both needed.
      (Only the ring structure is required — nothing here uses inverses.) -/
  f_commring : CommRing F
  /-- EC's `expD`: exponentiation turns addition into multiplication. -/
  gpow_add : ∀ (h : G) (a b : F), gpow h (a + b) = gmul (gpow h a) (gpow h b)
  /-- EC's `expM`: iterated exponentiation multiplies the exponents. -/
  gpow_mul : ∀ (h : G) (a b : F), gpow (gpow h a) b = gpow h (a * b)

namespace PedersenGroup
variable [PedersenGroup]
instance : Inhabited G := g_inhabited
noncomputable instance : DecidableEq G := Classical.decEq G
instance : Inhabited F := f_inhabited
instance : CommRing F := f_commring
noncomputable instance : DecidableEq F := Classical.decEq F
instance : Fintype F := f_fintype
instance : Mul G := ⟨gmul⟩
instance : Pow G F := ⟨gpow⟩

/-- `gpow_add` at the `^`/`*` notation.  The class fields have to be stated with the raw
    `gmul`/`gpow` (the instances below them do not exist yet), but every use site sees the
    notation, and `rw` matches on the notation's head — not the raw field. -/
theorem pow_add (h : G) (a b : F) : h ^ (a + b) = h ^ a * h ^ b := gpow_add h a b

/-- `gpow_mul` at the `^` notation. -/
theorem pow_mul (h : G) (a b : F) : (h ^ a) ^ b = h ^ (a * b) := gpow_mul h a b

end PedersenGroup

open PedersenGroup (G F g)

/-- EC's `PedersenTypes` + `clone Commitment with …`: value/commitment are group elements,
    message/openingkey are exponents. -/
/- Reducible on purpose.  It used to be an `instance`, which carries `@[reducible]` implicitly, and
the `wp_*` proofs below rely on it: they are stated at `pedersenTypes.Commitment` and worked on at
`G`, and every `simp` that has to see through that spelling needs the record to unfold at
`reducible` transparency.  A plain `def` leaves `programDenotation` stuck on the `.seq` of the
procedure's body. -/
@[reducible] def pedersenTypes [PedersenGroup] : CommitmentTypes where
  Value := G
  Message := F
  Commitment := G
  OpeningKey := F
  value_inhabited := inferInstance
  message_inhabited := inferInstance
  commitment_inhabited := inferInstance
  openingKey_inhabited := inferInstance

variable [ProgramSpec] [PedersenGroup]

/-! ## The scheme

EC's
```
module Pedersen : CommitmentScheme = {
  proc gen() : value                = { x <$ dt; h <- g ^ x; return h; }
  proc commit(h, m)                 = { d <$ dt; c <- (g ^ d) * (h ^ m); return (c, d); }
  proc verify(h, m, c, d)           = { c' <- (g ^ d) * (h ^ m); return (c = c'); }
}.
```
transcribes directly with the `module` command.  It declares, per procedure `f`, both the body
`Pedersen.f.procedure` and the module `Pedersen.f : Module.Proc …`, and assembles them into
`Pedersen : CommitmentScheme` with `CommitmentScheme.mk` (the field names match the moduletype's,
so the record constructor is used rather than a nest of `Module.pair`s).  `Pedersen` has no
module parameters, so it *is* the scheme — there is nothing to apply it to, and hence no
`Pedersen.apply_simp`. -/

module Pedersen : (CommitmentScheme pedersenTypes) {
  /- Sample a secret exponent, publish `h = g ^ x`. -/
  proc gen() : G {
    var x : F;
    var h : G;
    x <$ SubProbability.uniform;
    h <- g ^ $x;
    return $h
  };
  /- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
  proc commit(h : G, m : F) : (G × F) {
    var c : G;
    var d : F;
    d <$ SubProbability.uniform;
    c <- g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  /- Recompute the commitment and compare. -/
  proc verify(h : G, m : F, c : G, d : F) : Bool {
    var c' : G;
    c' <- g ^ $d * $h ^ $m;
    return $c == $c'
  };
}

/-! ## Correctness

To *run* an applied functor module we extract its procedure: a normal closed module
expression of procedure type is a `.proc` node (`proc_type_is_proc` / `Module.procedure`,
now in `Language/Modules.lean`).

`Correctness Pedersen` β/δ-normalizes to `Correctness.main` with Pedersen's procedures in the
holes.  That reduction used to be done by hand here, by a `functorApp_procedure` bridge lemma, a
`functor_procedure` tactic, a `Pedersen_expression` record equation and a `pedersenInst` naming
the hole filling.  None of it is needed any more, and all of it is gone (see the history of this
file if you want it back): the `module`/`moduletype` commands emit `@[simp]` `apply_simp` lemmas
and tag their accessors `@[module_accessor]`, and those do the whole reduction inline in
`pedersen_correctness`. -/

/-! ### Per-procedure wp lemmas (EC's `inline`+`auto` steps, done once per procedure)

All three are stated at the `pedersenTypes`-spelled signature the instantiated game carries,
not at `G`/`F`.  The two are definitionally equal, but `Eq` carries its type as an index, so the
spelling is what makes them the same proposition as the goal — see the ⚠ below. -/

theorem wp_gen (f : ProgramDenotation.Post State pedersenTypes.Value) :
    (procedureDenotation (sig := procsig () -> pedersenTypes.Value)
        Pedersen.gen.procedure ()).wp f
      = fun st => ∑ x : F, f (g ^ x, st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, LocalVariableState.varsL]

theorem wp_commit (args : G × F)
    (f : ProgramDenotation.Post State
      (pedersenTypes.Commitment × pedersenTypes.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (pedersenTypes.Value, pedersenTypes.Message) ->
          (pedersenTypes.Commitment × pedersenTypes.OpeningKey))
        Pedersen.commit.procedure args).wp f
      = fun st => ∑ x : F, f ((g ^ x * args.1 ^ args.2, x), st) / Fintype.card F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [pedersenTypes,
    Pedersen.commit.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL,
    LocalVariableState.paramsL, LocalVariableState.varsL]

theorem wp_verify (args : G × F × G × F) (f : ProgramDenotation.Post State Bool) :
    (procedureDenotation
        (sig := procsig (pedersenTypes.Value, pedersenTypes.Message,
          pedersenTypes.Commitment, pedersenTypes.OpeningKey) -> Bool)
        Pedersen.verify.procedure args).wp f
      = fun st => f (args.2.2.1 == g ^ args.2.2.2 * args.1 ^ args.2.1, st) := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [pedersenTypes,
    Pedersen.verify.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL,
    LocalVariableState.paramsL, LocalVariableState.varsL]

/-! ### Reducing the applied functor

`Correctness.main.procedure.apply_simp` fills `Correctness.main`'s holes with the callees they
were made from — which, since `Correctness`'s body calls `S.gen`, are the moduletype *accessors*
`CommitmentScheme.gen Pedersen` and friends.  The `wp_*` lemmas above are stated at
`Pedersen.gen.procedure`, a separate definition the `module` command emits.  Adding
`module_accessor` (the simp set the accessors are tagged with), `Pedersen`, and the
`Module.proc`/`Module.procedure_proc` round-trip to the main `simp` call is all it takes to close
that gap.  So the whole reduction is the commands' own lemmas plus one `simp` set: no bridge
lemma, no hand-written hole instantiation, nothing declared for the purpose.

(`Module.procedure_proc` has to be paired with unfolding `Module.proc`: the library states the
round-trip with `Module.proc` already unfolded, as `(ModuleExpression.proc p).toModule (.proc p)`,
so on its own it never fires against the folded `Module.proc` that `X.<f>.apply_simp` emits.)

⚠ One thing to know before touching this: `CommitmentScheme.gen Pedersen` and `Pedersen.gen`
**both print as `Pedersen.gen`** (dot-notation collision) and are *not* defeq — the accessor is a
chain of `Module.fst'`/`Module.snd'` through `Pedersen`'s expression.  So a lemma or rewrite
aimed at the wrong one of the two fails with the two sides displaying identically, or with "did
not find an occurrence of the pattern" against a goal in which the pattern is apparently right
there.  `set_option pp.explicit true` is what tells them apart.  A second, similar trap: signature
spellings must be `pedersenTypes.*`, not `G`/`F` — those are defeq, but `Eq` carries its type
as an index, so the two are *different propositions* and `exact` rejects the mismatch, again
printing identically (`convert … using 2` exposes that one).  The `wp_*` lemmas above are spelled
`pedersenTypes.*` for exactly this reason.

A third, from `pedersenTypes` being `@[reducible]`: `simp` files a lemma under the discrimination
key of its *statement*, and indexes the goal with `pedersenTypes.Message` already reduced to `F`,
so a lemma stated over an abstract `types` — every `apply_simp` the `module` command emits — is
looked up under a key the goal no longer has, and silently does not fire ("This simp argument is
unused").  `rw` unifies rather than looking up and is unaffected; that is why the first step of
`pedersen_correctness` is a `rw`. -/

set_option linter.flexible false in
/-- **Correctness of Pedersen** — EC's
    `hoare[Correctness(Pedersen).main : true ==> res]`: from any initial state, the
    correctness game never returns `false`. -/
theorem pedersen_correctness (m : F) (σ : State) :
    (procedureDenotation (Module.app (Correctness pedersenTypes) Pedersen).procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  -- reduce `ofEvent` to a `wp` with the indicator postcondition.  Done *before* the module
  -- reduction, so nothing here ever has to name the reduced procedure.
  suffices h : (procedureDenotation
      (Module.app (Correctness pedersenTypes) Pedersen).procedure m).wp
      (({r : Bool × State | r.1 = false}).indicator fun _ => 1) σ = 0 by
    have hi := expectation_indicator
      (procedureDenotation (Module.app (Correctness pedersenTypes) Pedersen).procedure m σ)
      {r : Bool × State | r.1 = false} 1
    rw [one_mul] at hi
    exact_mod_cast hi.symm.trans h
  -- β/δ-reduce the applied functor down to `Correctness.main`'s body with Pedersen's three
  -- procedures in the holes — the `module` command's own `@[simp]` lemmas do all of it.
  -- `rw`, not `simp`, for the outermost step: `pedersenTypes` is reducible (it has to be, for the
  -- `wp_*` lemmas below to see `G`/`F` through the `pedersenTypes.*` spelling), and simp's
  -- discrimination tree therefore indexes the goal with `types.Message` already reduced to `F`,
  -- which is not the key `Correctness.apply_simp` was filed under.  `rw` unifies instead of
  -- looking up, so it is unaffected.
  rw [Correctness.apply_simp, Correctness.main.apply_simp,
    Correctness.main.procedure.apply_simp]
  simp only [Module.proc, Module.procedure_proc]
  -- unfold the game and push `wp` through.  Kept as `rw`, not folded into the `simp only` above:
  -- as simp lemmas these two also fire on the *callees*, and `wp_gen` then no longer matches.
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  simp [module_accessor, Pedersen, Module.proc, Module.procedure_proc, programDenotation,
    StmtWithHoles.call, wp_bind, wp_get_g, wp_set_g, wp_zoom,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.paramsL, LocalVariableState.varsL,
    Set.indicator, Set.mem_setOf_eq]
  -- descend through the two samplings with `rw` (full-defeq unification), summand by summand
  rw [wp_gen]
  refine Finset.sum_eq_zero fun x _ => ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_commit]
  refine Finset.sum_eq_zero fun d _ => ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
  rw [wp_verify]
  -- `Lens.pair`: the game stores `commit`'s result through the tuple l-value `c, d <- …`, so
  -- the final read has to compute back through that pair lens.
  simp [Lens.pair]

end GaudisCrypt.Examples.Pedersen

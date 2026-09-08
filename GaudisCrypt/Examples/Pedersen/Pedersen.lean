import GaudisCrypt.Examples.Pedersen.Commitment
import GaudisCrypt.WeakestPreconditions

/-!
# The Pedersen commitment scheme

A transliteration of EasyCrypt's `examples/Pedersen.ec`:

* EC's `clone DLog` (cyclic group `group` with generator `g`, prime exponent field `exp`)
  becomes the structure `PedersenGroup`: the operations the programs mention, plus the laws the
  proofs turned out to need (`f_commring`, `gpow_add`, `gpow_mul` — the last two are EC's
  `expD`/`expM`).  It is a section `variable (group : PedersenGroup)`, and hence a Lean parameter
  of everything below that mentions it.
* EC's `PedersenTypes` + the `Commitment` clone become the `CommitmentTypes` record
  `group.types` (value/commitment = group, message/openingkey = exponent), which every
  `CommitmentScheme`-shaped name here is applied to.
* `module Pedersen : CommitmentScheme` becomes a
  `module Pedersen : (CommitmentScheme group.types) { … }` declaration — EC's own syntax, near
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
structure PedersenGroup where
  G : Type
  F : Type
  g : G
  -- TODO: Change to `[Mul G]`
  gmul : G → G → G
  -- TODO: Change to `[Pow G F]`
  gpow : G → F → G
  [g_inhabited : Inhabited G]
  -- TODO: Remove. Implied by CommRing F.
  [f_inhabited : Inhabited F]
  [f_fintype : Fintype F]
  /-- EC's exponent type is the prime field `DL.GP.ZModE`; the hiding proof forms `d + x * m`
      and its inverse `d - x * m`, so the additive group and the multiplication are both needed.
      (Only the ring structure is required — nothing here uses inverses.) -/
  [f_commring : CommRing F]
  /-- EC's `expD`: exponentiation turns addition into multiplication. -/
  gpow_add : ∀ (h : G) (a b : F), gpow h (a + b) = gmul (gpow h a) (gpow h b)
  /-- EC's `expM`: iterated exponentiation multiplies the exponents. -/
  gpow_mul : ∀ (h : G) (a b : F), gpow (gpow h a) b = gpow h (a * b)

-- namespace PedersenGroup

variable (group : PedersenGroup)

@[reducible] instance : Inhabited group.G := group.g_inhabited
@[reducible] noncomputable instance : DecidableEq group.G := Classical.decEq _
@[reducible] instance : Inhabited group.F := group.f_inhabited
@[reducible] instance : CommRing group.F := group.f_commring
@[reducible] noncomputable instance : DecidableEq group.F := Classical.decEq _
@[reducible] instance : Fintype group.F := group.f_fintype
@[reducible] instance : Mul group.G := ⟨group.gmul⟩
@[reducible] instance : Pow group.G group.F := ⟨group.gpow⟩

/-- `gpow_add` at the `^`/`*` notation.  The class fields have to be stated with the raw
    `gmul`/`gpow` (the instances below them do not exist yet), but every use site sees the
    notation, and `rw` matches on the notation's head — not the raw field. -/
theorem pow_add (h : group.G) (a b : group.F) : h ^ (a + b) = h ^ a * h ^ b := group.gpow_add h a b

/-- `gpow_mul` at the `^` notation. -/
theorem pow_mul (h : group.G) (a b : group.F) : (h ^ a) ^ b = h ^ (a * b) := group.gpow_mul h a b

-- end PedersenGroup

-- open PedersenGroup (G F g)


/-- EC's `PedersenTypes` + `clone Commitment with …`: value/commitment are group elements,
    message/openingkey are exponents. -/
/- Reducible on purpose.  It used to be an `instance`, which carries `@[reducible]` implicitly, and
the `wp_*` proofs below rely on it: they are stated at `group.types.Commitment` and worked on at
`group.G`, and every `simp` that has to see through that spelling needs the record to unfold at
`reducible` transparency.  A plain `def` leaves `programDenotation` stuck on the `.seq` of the
procedure's body. -/
@[reducible] def PedersenGroup.types : CommitmentTypes where
  Value := group.G
  Message := group.F
  Commitment := group.G
  OpeningKey := group.F
  value_inhabited := inferInstance
  message_inhabited := inferInstance
  commitment_inhabited := inferInstance
  openingKey_inhabited := inferInstance

variable [ProgramSpec]

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

module Pedersen : (CommitmentScheme group.types) {
  /- Sample a secret exponent, publish `h = g ^ x`. -/
  proc gen() : group.G {
    var x : group.F;
    var h : group.G;
    x <$ SubProbability.uniform;
    h <- group.g ^ $x;
    return $h
  };
  /- Commit to `m` under `h`: sample the opening key `d`, output `g ^ d * h ^ m`. -/
  proc commit(h : group.G, m : group.F) : (group.G × group.F) {
    var c : group.G;
    var d : group.F;
    d <$ SubProbability.uniform;
    c <- group.g ^ $d * $h ^ $m;
    return ($c, $d)
  };
  /- Recompute the commitment and compare. -/
  proc verify(h : group.G, m : group.F, c : group.G, d : group.F) : Bool {
    var c' : group.G;
    c' <- group.g ^ $d * $h ^ $m;
    return $c == $c'
  };
}

/-! ## Correctness

To *run* an applied functor module we extract its procedure: a normal closed module
expression of procedure type is a `.proc` node (`proc_type_is_proc` / `Module.procedure`,
now in `Language/Modules.lean`).

`Correctness group.types (Pedersen group)` β/δ-normalizes to `Correctness.main` with Pedersen's
procedures in the holes.  That reduction used to be done by hand here, by a `functorApp_procedure`
bridge lemma, a `functor_procedure` tactic, a `Pedersen_expression` record equation and a
`pedersenInst` naming the hole filling.  None of it is needed any more, and all of it is gone (see
the history of this file if you want it back): the `module`/`moduletype` commands emit `@[simp]`
`apply_simp` lemmas
and tag their accessors `@[module_accessor]`, and those do the whole reduction inline in
`pedersen_correctness`. -/

/-! ### Per-procedure wp lemmas (EC's `inline`+`auto` steps, done once per procedure)

All three are stated at the `group.types`-spelled signature the instantiated game carries,
not at `group.G`/`group.F`.  The two are definitionally equal, but `Eq` carries its type as an
index, so the spelling is what makes them the same proposition as the goal — see the ⚠ below. -/

theorem wp_gen (f : ProgramDenotation.Post State group.types.Value) :
    (procedureDenotation (sig := procsig () -> group.types.Value)
        (Pedersen.gen.procedure group) ()).wp f
      = fun st => ∑ x : group.F, f (group.g ^ x, st) / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [Pedersen.gen.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, LocalVariableState.varsL]

theorem wp_commit (args : group.G × group.F)
    (f : ProgramDenotation.Post State
      (group.types.Commitment × group.types.OpeningKey)) :
    (procedureDenotation
        (sig := procsig (group.types.Value, group.types.Message) ->
          (group.types.Commitment × group.types.OpeningKey))
        (Pedersen.commit.procedure group) args).wp f
      = fun st => ∑ x : group.F, f ((group.g ^ x * args.1 ^ args.2, x), st)
          / Fintype.card group.F := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [PedersenGroup.types,
    Pedersen.commit.procedure, programDenotation, StmtWithHoles.assign, wp_bind, wp_get_g,
    wp_set_g,
    wp_lift, uniform_expected, expected_pure, ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoParams, Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL,
    LocalVariableState.paramsL, LocalVariableState.varsL]

theorem wp_verify (args : group.G × group.F × group.G × group.F)
    (f : ProgramDenotation.Post State Bool) :
    (procedureDenotation
        (sig := procsig (group.types.Value, group.types.Message,
          group.types.Commitment, group.types.OpeningKey) -> Bool)
        (Pedersen.verify.procedure group) args).wp f
      = fun st => f (args.2.2.1 == group.g ^ args.2.2.2 * args.1 ^ args.2.1, st) := by
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  funext st
  simp [PedersenGroup.types,
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
spellings must be `group.types.*`, not `group.G`/`group.F` — those are defeq, but `Eq` carries its
type as an index, so the two are *different propositions* and `exact` rejects the mismatch, again
printing identically (`convert … using 2` exposes that one).  The `wp_*` lemmas above are spelled
`group.types.*` for exactly this reason.

A third, from `PedersenGroup.types` being `@[reducible]`: `simp` files a lemma under the
discrimination key of its *statement*, and indexes the goal with `group.types.Message` already
reduced to `group.F`, so a lemma stated over an abstract `types` — every `apply_simp` the `module`
command emits — used to be looked up under a key the goal no longer had, and silently did not fire
("This simp argument is unused").  The commands now keep those positions out of the key with
`no_index` (see "Keeping the generated `@[simp]` lemmas findable" in `Syntax/ModuleSyntax.lean`), so
the lemmas are found at a reducible instantiation too: `pedersen_correctness2` below reduces the
whole applied functor with a single `simp`.

`pedersen_correctness` still reduces it by `rw`, for a different reason: reaching the goal through
the `suffices` leaves it type-incorrect at the `instances` transparency simp works at (`m :
group.F` where `(procsig (group.F) → Bool).ParamType` is expected), and simp then declines.  `rw`
unifies at default transparency and is unaffected. -/

set_option linter.flexible false in
/-- **Correctness of Pedersen** — EC's
    `hoare[Correctness(Pedersen).main : true ==> res]`: from any initial state, the
    correctness game never returns `false`. -/
theorem pedersen_correctness (m : group.F) (σ : State) :
    (procedureDenotation
        (Module.app (Correctness group.types) (Pedersen group)).main.procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  -- reduce `ofEvent` to a `wp` with the indicator postcondition.  Done *before* the module
  -- reduction, so nothing here ever has to name the reduced procedure.
  suffices h : (procedureDenotation
      (Module.app (Correctness group.types) (Pedersen group)).main.procedure m).wp
      (({r : Bool × State | r.1 = false}).indicator fun _ => 1) σ = 0 by
    have hi := expectation_indicator
      (procedureDenotation
        (Module.app (Correctness group.types) (Pedersen group)).main.procedure m σ)
      {r : Bool × State | r.1 = false} 1
    rw [one_mul] at hi
    exact_mod_cast hi.symm.trans h
  -- β/δ-reduce the applied functor down to `Correctness.main`'s body with Pedersen's three
  -- procedures in the holes — the `module`/`moduletype` commands' own `@[simp]` lemmas do all of
  -- it.  `rw` rather than `simp` here: the goal the `suffices` above leaves is not type-correct at
  -- the `instances` transparency simp works at, and simp declines to rewrite in it (see the ⚠
  -- above); `rw` unifies at default transparency instead.
  rw [Correctness.apply_simp]
  -- read `main` back off the record `Correctness.apply_simp` builds — the `moduletype` command's
  -- own `@[simp]` lemma for the accessor
  simp only [CorrectnessT.main.mk_simp]
  rw [Correctness.main.apply_simp, Correctness.main.procedure.apply_simp]
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

omit [ProgramSpec] in
/-- An event of null points is null.  No `[Countable α]`: `μ.2.2` is the discreteness invariant
    `μ A = ∑_{x ∈ A} μ {x}`, so the sum over `E` is a `tsum` of zeroes whatever the cardinality. -/
lemma _root_.GaudisCrypt.SubProbability.ofEvent0I {μ : SubProbability α} :
    (∀ x ∈ E, μ x = 0) → μ.ofEvent E = 0 := by
  intro h
  -- `ofEvent` is `toNNReal` of the measure, and the measure is finite (`≤ 1`), so the two
  -- vanish together
  have hzero : ∀ s : Set α, μ.ofEvent s = 0 ↔ μ.1 s = 0 := fun s => by
    rw [SubProbability.ofEvent, ENNReal.toNNReal_eq_zero_iff]
    exact or_iff_left
      (((MeasureTheory.measure_mono (Set.subset_univ s)).trans μ.2.1).trans_lt
        ENNReal.one_lt_top).ne
  rw [hzero, μ.2.2 E, ENNReal.tsum_eq_zero]
  exact fun x => (hzero {(x : α)}).mp (h x x.2)

section UnfinitedExperimentsByDominique

/-- A single point's mass as a `wp`: the postcondition that picks out `x` is the indicator of
    `{x}`, and `expectation_indicator` at `c = 1` identifies the two. -/
lemma tmp {sig m σ E} {p : Procedure sig} :
  (procedureDenotation p m).wp (Set.indicator E fun _ => 1) σ = 0 →
  (procedureDenotation p m σ).ofEvent E = 0
  := by
  intro h
  simp only [ProgramDenotation.wp, expectation_indicator, one_mul, ENNReal.coe_eq_zero] at h
  exact h

-- TODO: Can we make p.instantiate (h1,...,hn) work (instead of HoleInstantiation.push etc etc...)?
-- TODO: Concrete syntax for Module.app

theorem pedersen_correctness2 (m : group.F) (σ : State) :
    (procedureDenotation
        (Module.app (Correctness group.types) (Pedersen group)).main.procedure m σ).ofEvent
      {r : Bool × State | r.1 = false} = 0 := by
  apply tmp
  simp
  -- TODO: why does this not use proc syntax?
  simp only [Correctness.main.procedure.apply_simp]
  sorry

end UnfinitedExperimentsByDominique

end GaudisCrypt.Examples.Pedersen

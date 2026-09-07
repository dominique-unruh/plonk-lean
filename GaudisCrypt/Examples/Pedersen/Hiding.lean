import GaudisCrypt.Examples.Pedersen.Pedersen
import GaudisCrypt.Logic.PRHL2
import GaudisCrypt.FV

/-!
# Perfect hiding of the Pedersen commitment scheme

A transliteration of `section PedersenSecurity` in EasyCrypt's `examples/Pedersen.ec`, kept as
close to the original as the DSL allows.  EC, in full:

```
local module FakeCommit(U:Unhider) = {
  proc main() : bool = {
    var b, b', x, h, c, d;
    var m0, m1 : exp;
    (* Clearly, there are many useless lines, but their presence helps for the proofs *)
    x <$ dt;  h <- g^x;  (m0, m1) <@ U.choose(h);
    b <$ {0,1};  d <$ dt;  c <- g^d;  (* message independent - fake commitment *)
    b' <@ U.guess(c);
    return (b = b');
  }
}.

local lemma hi_ll (U<:Unhider):
  islossless U.choose => islossless U.guess => islossless FakeCommit(U).main.

local lemma fakecommit_half (U<:Unhider) &m:
  islossless U.choose => islossless U.guess =>
  Pr[FakeCommit(U).main() @ &m : res] = 1%r/2%r.

local lemma phi_hi (U<:Unhider) &m:
  Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = Pr[FakeCommit(U).main() @ &m : res].

lemma pedersen_perfect_hiding (U<:Unhider) &m:
  islossless U.choose => islossless U.guess =>
  Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = 1%r/2%r.
```

**Status.**  All four EC lemmas are proven, on standard axioms, *except* for one framework fact:
`hidingGame_self_glob`, the glob adversary rule.  Everything cryptographic is closed; see that
theorem for exactly what is missing and where it belongs.

The point of this rewrite is that the theorems are about `HidingExperiment` and `FakeCommit`
*as modules*, exactly as EC states them.  The previous version stated its results about
hand-inlined `ProgramDenotation`s (`realGame`/`fakeGame`), which left the final theorem saying
nothing about `HidingExperiment` at all — the inlining was never justified against the module.
That justification is now `hidingGame_inline`/`fakeGame_inline`.

One deviation from EC, forced and local: EC's `&m` (an initial memory) becomes an explicit
`σ : State`.

`={glob U}` is *not* a deviation: it is `GlobEq` below, which is exactly EC's notion — see the
comment there.
-/

namespace GaudisCrypt.Examples.Pedersen

open GaudisCrypt
open PedersenGroup (G F g)

variable [ProgramSpec] [PedersenGroup]

/-! ## EC vocabulary

Two abbreviations so the statements below read like the EC ones.  Both are pure notation: they
unfold to the spellings already used in `pedersen_correctness`. -/

/-- EC's `Pr[M.main() @ σ : res]` — the probability that a `Bool`-returning, argument-less
    module procedure returns `true`, started in `σ`. -/
noncomputable def Pr (M : procmod () -> Bool) (σ : State) : NNReal :=
  (procedureDenotation M.procedure () σ).ofEvent {r : Bool × State | r.1 = true}

/-- The event `res` as a `wp` postcondition. -/
noncomputable def resIndicator : Bool × State → ENNReal :=
  ({r : Bool × State | r.1 = true}).indicator fun _ => 1

omit [PedersenGroup] in
/-- `Pr` as a `wp` — the bridge EC's `byphoare`/`byequiv` cross implicitly.  `wp p F σ` is
    `(p σ).expected F` definitionally, so this is `expectation_indicator` at `c = 1`. -/
theorem Pr_eq_wp (M : procmod () -> Bool) (σ : State) :
    (Pr M σ : ENNReal) = (procedureDenotation M.procedure ()).wp resIndicator σ := by
  have hi := expectation_indicator (procedureDenotation M.procedure () σ)
    {r : Bool × State | r.1 = true} 1
  rw [one_mul] at hi
  exact hi.symm

/-- EC's `islossless P` — `P` terminates with probability 1, from any state, on any argument.
    Real content under a sub-probability semantics: a diverging adversary would make
    `fakecommit_half` an inequality. -/
def IsLossless {sig : ProcedureSignature} (p : Procedure sig) : Prop :=
  ∀ (args : sig.ParamType) (σ : State),
    (procedureDenotation p args).wp (fun _ => (1 : ENNReal)) σ = 1

/-- **EC's `glob A`**, for a whole module `A` — the getter reading everything `A` may touch.

    `FVP.fvP A : Footprint State` is the computed footprint of the module (`FV.lean`; it
    decomposes over a `moduletype`'s fields by `FVP.fvP_pair`), and `Footprint.touched_getter`
    quotients the state by the *complement* footprint, so two states read equal exactly when they
    differ only outside `A` — see `Footprint.touched_getter` in `Language/Footprint.lean`, whose
    docstring names this as EC's `glob`. -/
noncomputable def glob {M : Type _} [IsModule M] (A : M) :
    Getter (Quotient ((FVP.fvP A)ᶜ.orbit_setoid)) State :=
  (FVP.fvP A).touched_getter

/-- **EC's `={glob A}`**.  That this is the right notion is not a definition but a theorem:
    `Footprint.indistinguishable_of_touched_getter_eq` says glob-equal states are separated by no
    `A`-test, and `Footprint.touched_getter_get_eq_of_mem` says writes outside `A` preserve it. -/
noncomputable def GlobEq {M : Type _} [IsModule M] (A : M) (σ₁ σ₂ : State) : Prop :=
  (glob A).get σ₁ = (glob A).get σ₂

omit [PedersenGroup] in
theorem GlobEq.refl {M : Type _} [IsModule M] (A : M) (σ : State) : GlobEq A σ σ := rfl

/-! ## The two games

`HidingExperiment` is declared in `Commitment.lean` (it is generic in the scheme, as in EC);
`FakeCommit` is EC's local module, transcribed line for line — including the "useless" `h <- g^x`
and `c <- g^d`, which EC keeps deliberately so that the two games line up statement by statement
for the relational proof. -/

/- EC's
```
local module FakeCommit(U:Unhider) = {
  proc main() : bool = {
    x <$ dt;  h <- g^x;  (m0, m1) <@ U.choose(h);
    b <$ {0,1};  d <$ dt;  c <- g^d;
    b' <@ U.guess(c);
    return (b = b');
  }
}.
``` -/
module FakeCommit using (U : Unhider pedersenTypes) {
  proc main() : Bool {
    var x : F;
    var h : G;
    var m0 : pedersenTypes.Message;
    var m1 : pedersenTypes.Message;
    var b : Bool;
    var d : F;
    var c : G;
    var bg : Bool;
    x <$ SubProbability.uniform;
    h <- g ^ $x;
    m0,m1 <- call U.choose ($h);
    b <$ SubProbability.uniform;
    d <$ SubProbability.uniform;
    c <- g ^ $d;
    bg <- call U.guess ($c);
    return $b == $bg
  };
}

/-- `HidingExperiment(Pedersen, U).main` — the real game, as a module. -/
noncomputable abbrev hidingGame (U : Unhider pedersenTypes) : procmod () -> Bool :=
  Module.app (Module.app (HidingExperiment.main pedersenTypes) Pedersen) U

/-- `FakeCommit(U).main` — the fake game, as a module. -/
noncomputable abbrev fakeGame (U : Unhider pedersenTypes) : procmod () -> Bool :=
  Module.app FakeCommit U

/-! ## Inlining (EC's `inline*`)

The `prhl2` rules consume `>>=`-chains, but a module procedure is a `procWrap` over a
`programDenotation` on its own local-state type — and the two games do not even have the same
locals (seven against eight, differently typed).  These two lemmas are EC's `inline*`: each
game *as a module* equals
a bind chain on `State`, with the adversary calls left as opaque denotations.  Proven by
`SubProbability.ext_of_expected`, i.e. by checking the `wp` at an arbitrary postcondition, which
is the same reduction `fakecommit_half` runs. -/

set_option linter.flexible false in
/-- `FakeCommit(U).main`, inlined. -/
theorem fakeGame_inline (U : Unhider pedersenTypes) :
    procedureDenotation (fakeGame U).procedure ()
      = (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
        procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x) >>= fun _mm =>
        (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d) >>= fun bg =>
        pure (b == bg) := by
  funext σ
  refine SubProbability.ext_of_expected fun post => ?_
  change (procedureDenotation (fakeGame U).procedure ()).wp post σ = _
  simp only [fakeGame, FakeCommit.apply_simp, FakeCommit.main.apply_simp,
    FakeCommit.main.procedure.apply_simp, Module.proc, Module.procedure_proc]
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  change _ = ((ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
        procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x) >>= fun _mm =>
        (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d) >>= fun bg =>
        pure (b == bg)).wp post σ
  simp [programDenotation,
    StmtWithHoles.call, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g, wp_zoom, wp_lift,
    wp_uniform, wp_pure, uniform_expected, expected_pure,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    -- `Lens.pair`: `m0,m1 <- call U.choose (…)` stores through a tuple l-value
    Lens.pair,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.varsL]

set_option linter.flexible false in
/-- `HidingExperiment(Pedersen, U).main`, inlined.  Pedersen's own `gen`/`commit` are inlined too
    (their internal samplings become the `x` and `d` draws), via `wp_gen`/`wp_commit`. -/
theorem hidingGame_inline (U : Unhider pedersenTypes) :
    procedureDenotation (hidingGame U).procedure ()
      = (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
        procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x) >>= fun mm =>
        (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess pedersenTypes U).procedure
            (g ^ d * (g ^ x) ^ (if b then mm.2 else mm.1 : F)) >>= fun bg =>
        pure (b == bg) := by
  funext σ
  refine SubProbability.ext_of_expected fun post => ?_
  change (procedureDenotation (hidingGame U).procedure ()).wp post σ = _
  simp only [hidingGame, HidingExperiment.main.apply_simp,
    HidingExperiment.main.procedure.apply_simp, Module.proc, Module.procedure_proc]
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  change _ = ((ProgramDenotation.uniform : ProgramDenotation State F) >>= fun x =>
        procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x) >>= fun mm =>
        (ProgramDenotation.uniform : ProgramDenotation State Bool) >>= fun b =>
        (ProgramDenotation.uniform : ProgramDenotation State F) >>= fun d =>
        procedureDenotation (Unhider.guess pedersenTypes U).procedure
            (g ^ d * (g ^ x) ^ (if b then mm.2 else mm.1 : F)) >>= fun bg =>
        pure (b == bg)).wp post σ
  simp [module_accessor, Pedersen, Module.proc, Module.procedure_proc, programDenotation,
    StmtWithHoles.call, wp_bind, wp_get_g, wp_set_g, wp_zoom, wp_lift,
    wp_uniform, wp_pure, uniform_expected,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    -- `Lens.pair`: `m0,m1 <- …` and `c,d <- …` store through tuple l-values
    Lens.pair,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.varsL]
  -- now inline Pedersen's own `gen`/`commit` (their internal samplings are the `x` and `d` draws).
  -- `wp_gen` is at the top so `rw` reaches it; `wp_commit` sits under two binders, and `simp only`
  -- will not match it in its `= fun st => …` form — the pointwise `congrFun` version does.
  rw [wp_gen]
  have hcommit : ∀ (hh : G) (mm : F)
      (f : ProgramDenotation.Post State
        (pedersenTypes.Commitment × pedersenTypes.OpeningKey)) (st : State),
      (procedureDenotation Pedersen.commit.procedure (hh, mm)).wp f st
        = ∑ d : F, f ((g ^ d * hh ^ mm, d), st) / (Fintype.card F : ENNReal) :=
    fun hh mm f st => congrFun (wp_commit (hh, mm) f) st
  simp only [hcommit]

omit [ProgramSpec] in
/-- The algebraic heart of the coupling — EC's closing `algebra`: the real commitment at opening
    key `d` is the fake one at `d + x * m`.  `g^d * (g^x)^m = g^d * g^(x*m) = g^(d + x*m)`. -/
theorem commit_shift (x m d : F) : g ^ d * (g ^ x) ^ m = g ^ (d + x * m) := by
  rw [PedersenGroup.pow_mul, ← PedersenGroup.pow_add]

/-- **EC's coupling argument**, at *equal* initial states — the content of EC's
```
proc; inline*.  call (_:true); wp;
rnd (fun d, (d + x * (b?m1:m0)){2}) (fun d, (d - x * (b?m1:m0)){2});
by wp; rnd; call (_: true); auto => />; progress; algebra.
```
Read bottom-up: couple the `x` draws by the identity, run `U.choose` on both sides (same program,
same argument — `prhl2.refl`), couple the coins by the identity, then **couple the two `d` draws
by the translation `d ↦ d + x * (b ? m1 : m0)`**, under which `commit_shift` makes the real and
fake commitments coincide, and finally run `U.guess` on what is by then literally the same
argument.

The `rcases eq_or_ne` steps are bookkeeping EC does not need: a mid-condition of the form
`x₀ = x₁ ∧ τ₁ = τ₂` has to be turned into an actual substitution before the two sides are
syntactically the same program. -/
theorem phi_hi_equiv_eq (U : Unhider pedersenTypes) :
    ProgramDenotation.prhl2 (Eq : State → State → Prop)
      (procedureDenotation (hidingGame U).procedure ())
      (procedureDenotation (fakeGame U).procedure ())
      (fun u v : Bool × State => u = v) := by
  rw [hidingGame_inline, fakeGame_inline]
  -- `x <$ dt` — identity coupling
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform_id fun _ _ _ h => ⟨rfl, h⟩) ?_
  rintro x₀ x₁
  rcases eq_or_ne x₀ x₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- `(m0,m1) <@ U.choose(h)` — same program, same argument
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    ((ProgramDenotation.prhl2.refl _).conseq (fun _ _ h => h)
      (fun _ _ h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)) ?_
  rintro mm₀ mm₁
  rcases eq_or_ne mm₀ mm₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- `b <$ {0,1}` — identity coupling
  refine ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform_id fun _ _ _ h => ⟨rfl, h⟩) ?_
  rintro b₀ b₁
  rcases eq_or_ne b₀ b₁ with rfl | hne
  case inr => intro _ _ h; exact absurd h.1 hne
  refine ProgramDenotation.prhl2.conseq (A := (Eq : State → State → Prop))
    ?_ (fun _ _ h => h.2) (fun _ _ h => h)
  -- **the hop**: `d` on the left is `d + x * m` on the right, so the commitments agree
  refine ProgramDenotation.prhl2.bind
    (M := fun u v =>
      g ^ u.1 * (g ^ x₀) ^ (if b₀ then mm₀.2 else mm₀.1 : F) = g ^ v.1 ∧ u.2 = v.2)
    (ProgramDenotation.prhl2.uniform
      (Equiv.addRight (x₀ * (if b₀ then mm₀.2 else mm₀.1 : F)))
      (fun d _ _ h => ⟨commit_shift _ _ d, h⟩)) ?_
  rintro d₀ d₁ τ₁ τ₂ ⟨hcomm, rfl⟩
  -- the two `U.guess` calls now have literally the same argument
  rw [hcomm]
  exact (ProgramDenotation.prhl2.bind
    (M := fun u v => u.1 = v.1 ∧ u.2 = v.2)
    ((ProgramDenotation.prhl2.refl _).conseq (fun _ _ h => h)
      (fun _ _ h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩))
    (fun _ _ => ProgramDenotation.prhl2.pure_pure
      (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; rfl))) τ₁ τ₁ rfl

/-! ## The statements

EC's four lemmas, in EC's order. -/

set_option linter.flexible false in
/-- EC's
```
local lemma hi_ll (U<:Unhider):
  islossless U.choose => islossless U.guess => islossless FakeCommit(U).main.
```
EC discharges this with `islossless; (apply dt_ll || apply DBool.dbool_ll)` — the game is a
straight-line composition of two lossless samplings and two lossless adversary calls. -/
theorem hi_ll (U : Unhider pedersenTypes)
    (uc_ll : IsLossless (Unhider.choose pedersenTypes U).procedure)
    (ug_ll : IsLossless (Unhider.guess pedersenTypes U).procedure) :
    IsLossless (fakeGame U).procedure := by
  intro args τ
  simp only [fakeGame, FakeCommit.apply_simp, FakeCommit.main.apply_simp,
    FakeCommit.main.procedure.apply_simp, Module.proc, Module.procedure_proc]
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  simp [programDenotation,
    StmtWithHoles.call, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g, wp_zoom, wp_lift,
    uniform_expected, expected_pure,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.varsL]
  have hcard : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hcard' : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  have hsum : (Fintype.card F : ENNReal) * (1 / (Fintype.card F : ENNReal)) = 1 :=
    ENNReal.mul_div_cancel' (fun h => absurd h hcard) (fun h => absurd h hcard')
  -- innermost: `U.guess` is lossless, so the `d`-average is `1`, and `2 * (1/2) = 1`.
  -- (The losslessness hypotheses have to be *specialized* before `simp only` will use them —
  -- `simp only [ug_ll]` on the general `∀ args σ` form fails on the `Module.Proc` transparency
  -- trap documented in `Pedersen.lean`.)
  have hinner : ∀ τ' : State,
      (2 : ENNReal) * ((∑ d : F, (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
          (fun _ => (1 : ENNReal)) τ' / (Fintype.card F : ENNReal)) / 2) = 1 := by
    intro τ'
    have hone : ∀ d : F, (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
        (fun _ => (1 : ENNReal)) τ' = 1 := fun d => ug_ll (g ^ d) τ'
    simp only [hone]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum, one_div]
    exact ENNReal.mul_inv_cancel two_ne_zero (by simp)
  simp only [hinner]
  -- `U.choose` likewise contributes only its mass
  have hchoose : ∀ x : F, (procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x)).wp
      (fun _ => (1 : ENNReal)) τ = 1 := fun x => uc_ll (g ^ x) τ
  simp only [hchoose]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum]

set_option linter.flexible false in
/-- EC's
```
local lemma fakecommit_half (U<:Unhider) &m:
  islossless U.choose => islossless U.guess =>
  Pr[FakeCommit(U).main() @ &m : res] = 1%r/2%r.
```
EC: `byphoare; proc; wp; swap 4 3; rnd (pred1 b'); call ug_ll; wp; rnd; call uc_ll; auto`.
The `swap 4 3` moves the coin `b` past `d` and `c` so that it is drawn *after* `U.guess` has
fixed `b'`; a fresh fair coin then matches `b'` with probability exactly `1/2`. -/
theorem fakecommit_half (U : Unhider pedersenTypes) (σ : State)
    (uc_ll : IsLossless (Unhider.choose pedersenTypes U).procedure)
    (ug_ll : IsLossless (Unhider.guess pedersenTypes U).procedure) :
    Pr (fakeGame U) σ = 1 / 2 := by
  refine ENNReal.coe_inj.mp ?_
  rw [Pr_eq_wp]
  have hhalf : ((1 / 2 : NNReal) : ENNReal) = (1 / 2 : ENNReal) := by norm_num
  rw [hhalf]
  simp only [fakeGame, FakeCommit.apply_simp, FakeCommit.main.apply_simp,
    FakeCommit.main.procedure.apply_simp, Module.proc, Module.procedure_proc]
  rw [procedureDenotation_eq_procWrap, wp_procWrap]
  simp [programDenotation,
    StmtWithHoles.call, StmtWithHoles.assign, wp_bind, wp_get_g, wp_set_g, wp_zoom, wp_lift,
    uniform_expected, expected_pure,
    ProcedureSignature.localVariableInit,
    AsGetter.toG, AsSetter.toS, liftLens, LiftLens.lift,
    Lens.intoVars, Lens.chain, Lens.ofst, Lens.osnd,
    Lens.fst, Lens.snd, Lens.id, ProcedureState.localL, ProcedureState.globalL,
    LocalVariableState.varsL,
    resIndicator, Set.indicator, Set.mem_setOf_eq]
  have hcard : (Fintype.card F : ENNReal) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hcard' : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  -- EC's `rnd (pred1 b')`: for a *fixed* `b'`, the fair coin matches it with probability `1/2`.
  -- Here `b` was drawn first, so instead: the two coin branches partition, `⟦res⟧ + ⟦¬res⟧ = 1`
  -- pointwise, and `U.guess` is lossless — so the two branch weights sum to `1` at every state.
  have guessSum : ∀ (d : F) (τ : State),
      (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
            (fun r : Bool × State => if r.1 = true then 1 else 0) τ
          + (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
            (fun r : Bool × State => if r.1 = false then 1 else 0) τ = 1 := by
    intro d τ
    rw [← ProgramDenotation.wp_add]
    have hone : (fun r : Bool × State =>
        (if r.1 = true then (1 : ENNReal) else 0) + (if r.1 = false then 1 else 0))
        = fun _ => 1 := by
      funext r; cases hr : r.1 <;> simp
    rw [hone]
    exact ug_ll _ τ
  -- hence the whole `b`/`d`/`U.guess` block is `1/2` from any state
  have inner : ∀ τ : State,
      (∑ d : F, (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
            (fun r : Bool × State => if r.1 = true then 1 else 0) τ
              / (Fintype.card F : ENNReal)) / 2
        + (∑ d : F, (procedureDenotation (Unhider.guess pedersenTypes U).procedure (g ^ d)).wp
            (fun r : Bool × State => if r.1 = false then 1 else 0) τ
              / (Fintype.card F : ENNReal)) / 2 = 2⁻¹ := by
    intro τ
    rw [← ENNReal.add_div, ← Finset.sum_add_distrib]
    simp only [← ENNReal.add_div]
    rw [Finset.sum_congr rfl (fun d _ => by rw [guessSum d τ])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_div_cancel' (fun h => absurd h hcard) (fun h => absurd h hcard')]
    simp
  -- `U.choose` cannot change that: its result is never looked at, so only its mass matters,
  -- and that is `1` by losslessness (EC's `call uc_ll`)
  simp only [inner]
  have hconst : ∀ x : F,
      (procedureDenotation (Unhider.choose pedersenTypes U).procedure (g ^ x)).wp
          (fun _ => (2⁻¹ : ENNReal)) σ = 2⁻¹ := by
    intro x
    have hmul : (fun _ : (pedersenTypes.Message × pedersenTypes.Message) × State =>
        (2⁻¹ : ENNReal)) = fun _ => (2⁻¹ : ENNReal) * 1 := by
      funext p; rw [mul_one]
    rw [hmul, ProgramDenotation.wp_const_mul, uc_ll, mul_one]
  simp only [hconst]
  -- and the outer `x <$ dt` averages a constant
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.mul_div_cancel' (fun h => absurd h hcard) (fun h => absurd h hcard')]

/-- **The one open proof: the glob adversary rule**, at the whole game — two runs of the *same*
    game from `={glob U}` states agree on the result and stay `={glob U}`.

    This is the only place `={glob U}` (rather than plain equality) is doing work, and it is a
    framework fact, not a Pedersen one.  The rule that discharges it is `prhl2_self_of_orbit`
    (`Lib/RO/GlobTransfer.lean` — generic, despite the file): a program confined to `F`
    self-couples across any zig-zag of `Fᶜ`-updates, and its orbit precondition is literally what
    `GlobEq` unfolds to under `Quotient.exact`.

    What is missing to feed it is `(procedureDenotation A args).inFootprint (FVP.fvP_proc A)`,
    which is not stated anywhere: the ingredients exist (`procedureDenotation_inFootprint_reduce`,
    `fvP_stmt_le_FVP`, `inFootprint_selfRange`, and `FVP.fvP_proc` being exactly that
    `globalL`-reduction) but are only ever assembled into the RO-specific
    `fvP_proc_le_roLift_compl`.  That lemma belongs next to `FVP.fvP_proc` in `FV.lean`. -/
theorem hidingGame_self_glob (U : Unhider pedersenTypes) :
    ProgramDenotation.prhl2 (GlobEq U)
      (procedureDenotation (hidingGame U).procedure ())
      (procedureDenotation (hidingGame U).procedure ())
      (fun u v : Bool × State => u.1 = v.1 ∧ GlobEq U u.2 v.2) :=
  sorry

/-- The relational judgment behind EC's `phi_hi` — what `byequiv` reduces that lemma to:
```
equiv[ HidingExperiment(Pedersen,U).main ~ FakeCommit(U).main : ={glob U} ==> ={res} ]
```
Assembled the way `Lib/RO/GlobTransfer.lean` assembles its endpoint: relax the precondition from
`Eq` to `={glob U}` by composing the same-program glob rule with the coupling proper,

    real σ₁  ~[glob rule]~  real σ₂  ~[EC's coupling]~  fake σ₂

so that all the *cryptographic* content lives in `phi_hi_equiv_eq` and all the *framework*
content in `hidingGame_self_glob`. -/
theorem phi_hi_equiv (U : Unhider pedersenTypes) :
    ProgramDenotation.prhl2 (GlobEq U)
      (procedureDenotation (hidingGame U).procedure ())
      (procedureDenotation (fakeGame U).procedure ())
      (fun u v : Bool × State => u.1 = v.1 ∧ GlobEq U u.2 v.2) :=
  ((hidingGame_self_glob U).trans (phi_hi_equiv_eq U)).conseq
    (fun _ σ₃ h => ⟨σ₃, h, rfl⟩)
    (fun _ _ h => by obtain ⟨_, ⟨h1, h2⟩, rfl⟩ := h; exact ⟨h1, h2⟩)

/-- EC's
```
local lemma phi_hi (U<:Unhider) &m:
  Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = Pr[FakeCommit(U).main() @ &m : res].
```
i.e. `byequiv` applied to `phi_hi_equiv`.  `relE.wp_eq` is the `byequiv` bridge; the observable
`resIndicator` depends only on the result, so `={res}` alone transfers it, and `GlobEq.refl`
supplies the precondition at the single memory `σ` (EC's `&m` against itself). -/
theorem phi_hi (U : Unhider pedersenTypes) (σ : State) :
    Pr (hidingGame U) σ = Pr (fakeGame U) σ := by
  refine ENNReal.coe_inj.mp ?_
  rw [Pr_eq_wp, Pr_eq_wp]
  refine ProgramDenotation.relE.wp_eq (phi_hi_equiv U).to_relE ?_ (GlobEq.refl U σ)
  rintro u v ⟨hres, -⟩
  simp only [resIndicator, Set.indicator, Set.mem_setOf_eq, hres]

/-- **Perfect hiding.**  EC's
```
lemma pedersen_perfect_hiding (U<:Unhider) &m:
  islossless U.choose => islossless U.guess =>
  Pr[HidingExperiment(Pedersen,U).main() @ &m : res] = 1%r/2%r.
proof. by move => uc_ll ug_ll; rewrite (phi_hi U &m) (fakecommit_half U &m). qed.
``` -/
theorem pedersen_perfect_hiding (U : Unhider pedersenTypes) (σ : State)
    (uc_ll : IsLossless (Unhider.choose pedersenTypes U).procedure)
    (ug_ll : IsLossless (Unhider.guess pedersenTypes U).procedure) :
    Pr (hidingGame U) σ = 1 / 2 := by
  rw [phi_hi U σ]
  exact fakecommit_half U σ uc_ll ug_ll

end GaudisCrypt.Examples.Pedersen

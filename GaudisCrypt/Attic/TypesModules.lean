import Mathlib.Data.List.AList
import Mathlib.Logic.Equiv.Defs
import GaudisCrypt.Language.Programs
import Metatheory.STLCext.Normalization
import Metatheory.STLCext.Confluence

-- CLAUDE-TODO: Rename this file to TypedModules.lean
namespace GaudisCrypt.TypedModules

open GaudisCrypt

variable [ProgramSpec]

/- # Definition of the module calculus -/

/-- Possible types of modules -/
inductive ModuleTypeRep where
  | proc : ProcedureSignature → ModuleTypeRep
  | prod : ModuleTypeRep → ModuleTypeRep → ModuleTypeRep
  | arr  : ModuleTypeRep → ModuleTypeRep → ModuleTypeRep
  | unit : ModuleTypeRep

/-- Module context typing:
    Types of a given module contexts; just a list of module types -/
inductive ModuleContext where
  | empty  : ModuleContext
  | append : ModuleContext → ModuleTypeRep → ModuleContext

/-- Pointer into a module context; type safe for a given module context typing -/
inductive ModuleContextIdx : ModuleContext → ModuleTypeRep → Type _ where
  | zero {a} {Γ : ModuleContext} : ModuleContextIdx (Γ.append a) a
  | succ {a b} : ModuleContextIdx Γ a → ModuleContextIdx (Γ.append b) a

def ModuleContextIdx.toNat : ModuleContextIdx Γ T → Nat
| .zero => 0
| .succ n => Nat.succ (n.toNat)

/-- Note: lives in `GaudisCrypt.TypedModules`, not in `GaudisCrypt.HoleSigs`, so that it does not
    clash with `GaudisCrypt.HoleSigs.toModuleTypeRepTuple` from `Language/ModuleExpressions.lean`
    (same name, different `ModuleTypeRep`). Dot notation on a `HoleSigs` therefore does not find
    it; write `HoleSigs.toModuleTypeRepTuple holes`. -/
def HoleSigs.toModuleTypeRepTuple : HoleSigs → ModuleTypeRep
| .empty => .unit
| .append holes sig => .prod (.proc sig) (HoleSigs.toModuleTypeRepTuple holes)

omit [ProgramSpec] in
lemma ModuleContextIdx.toNat_inj' {Γ : ModuleContext} :
  ∀ {T1 T2 : ModuleTypeRep} (r1 : ModuleContextIdx Γ T1) (r2 : ModuleContextIdx Γ T2),
    r1.toNat = r2.toNat → T1 = T2 ∧ HEq r1 r2
  | _, _, .zero,    .zero,    _ => ⟨rfl, HEq.rfl⟩
  | _, _, .zero,    .succ _,  h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ _,  .zero,    h => by simp [ModuleContextIdx.toNat] at h
  | _, _, .succ r1', .succ r2', h => by
      simp only [ModuleContextIdx.toNat, Nat.succ_eq_add_one, Nat.add_right_cancel_iff] at h
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' r1' r2' h
      subst hT
      exact ⟨rfl, heq_of_eq (congrArg ModuleContextIdx.succ (eq_of_heq hr))⟩

/-- `ModuleExpression Γ T` is the type of all module expressions that are well-typed in
    module contexts of type `Γ` and have type `T`. -/
inductive ModuleExpression : ModuleContext → ModuleTypeRep → Type _ where
  | proc {sig} : Procedure sig → ModuleExpression Δ (.proc sig)
  | procHoles {holes} {sig} : holes.NonEmpty → ProcedureWithHoles holes sig →
        ModuleExpression Δ (.arr (HoleSigs.toModuleTypeRepTuple holes) (.proc sig))
  | var  : ModuleContextIdx Δ M → ModuleExpression Δ M
  | app  : ModuleExpression Δ (.arr A B) → ModuleExpression Δ A → ModuleExpression Δ B
  | fst : ModuleExpression Δ (.prod A B) → ModuleExpression Δ A
  | snd : ModuleExpression Δ (.prod A B) → ModuleExpression Δ B
  | abs : ModuleExpression (Δ.append A) B → ModuleExpression Δ (ModuleTypeRep.arr A B)
  | pair : ModuleExpression Δ A → ModuleExpression Δ B → ModuleExpression Δ (ModuleTypeRep.prod A B)
  | unit : ModuleExpression Δ .unit

/- # Helper functions -/

def IsPair (m : ModuleExpression Δ (.prod T U)) : Prop :=
  match m with | .pair _ _ => true | _ => false

instance (m : ModuleExpression Δ (.prod T U)) : Decidable (IsPair m) :=
  match m with
  | .pair _ _ => isTrue rfl
  | .var _ | .app _ _ | .fst _ | .snd _ => isFalse Bool.false_ne_true

def IsPair.split [ProgramSpec] {m : ModuleExpression Δ (.prod T U)} (_ : IsPair m) :
    (ModuleExpression Δ T × ModuleExpression Δ U) :=
  match m with
   | .pair m1 m2 => (m1,m2)
   | .fst _ => False.elim (by simp [IsPair] at *)
   | .snd _ => False.elim (by simp [IsPair] at *)
   | .app _ _ => False.elim (by simp [IsPair] at *)
   | .var _ => False.elim (by simp [IsPair] at *)

def IsPair.fst {m : ModuleExpression Δ (.prod T U)} (h : IsPair m) : ModuleExpression Δ T :=
  h.split.1

def IsPair.snd {m : ModuleExpression Δ (.prod T U)} (h : IsPair m) : ModuleExpression Δ U :=
  h.split.2


def IsAbs (m : ModuleExpression Δ T) : Prop :=
  match m with | .abs _ => true | _ => false

instance : Decidable (IsAbs m) :=
  match m with
  | .abs _ => isTrue rfl
  | .unit | .var _ | .pair _ _ | .fst _ | .snd _ | .app _ _ | .proc _ | .procHoles _ _ =>
       isFalse Bool.false_ne_true

def IsAbs.body {m : ModuleExpression Δ (.arr T U)} (_ : IsAbs m) :
    ModuleExpression (Δ.append T) U :=
  match m with
   | .abs body => body
   | .fst _ | .snd _ | .var _ | .app _ _ => False.elim (by simp [IsAbs] at *)


def IsProcHoles : ModuleExpression Δ T → Prop
| .procHoles _ _ => True
| _ => False

instance : Decidable (IsProcHoles m) :=
  match m with
  | .procHoles _ _ => isTrue trivial
  | .unit | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .proc _ => isFalse not_false

/-- `IsProcTuple m` holds when `m` is a right-nested tuple of hole-free procedures:
    either `.proc _`, or `.pair (.proc _) rest` with `IsProcTuple rest`.  These are exactly
    the ground arguments a procedure-with-holes can be instantiated with (the module-level
    analogue of STLC `BasicTerm`s). -/
def IsProcTuple : ModuleExpression Δ T → Prop
  | .unit => True
  | .pair (.proc _) rest => IsProcTuple rest
  | _ => False

instance instDecidableIsProcTuple (m : ModuleExpression Δ T) : Decidable (IsProcTuple m) :=
  match m with
  | .unit => isTrue trivial
  | .pair a rest =>
      match a with
      | .proc _ =>
          match instDecidableIsProcTuple rest with
          | isTrue h  => isTrue h
          | isFalse h => isFalse h
      | .unit | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .pair _ _ | .procHoles _ _ =>
          isFalse (by simp [IsProcTuple])
  | .proc _ | .var _ | .app _ _ | .fst _ | .snd _ | .abs _ | .procHoles _ _ => isFalse not_false


/-- A type that can be the argument type of a procedure-with-holes: a right-nested tuple of
    procedure types. -/
def IsProcArgType : ModuleTypeRep → Prop
  | .unit => True
  | .prod (.proc _) rest => IsProcArgType rest
  | _ => False

lemma IsProcHoles.isProcArgType {Δ : ModuleContext} {A B : ModuleTypeRep}
    {f : ModuleExpression Δ (.arr A B)} (h : IsProcHoles f) : IsProcArgType A := by
  cases f with
  | procHoles _ _ => rename_i holes _ _ _; exact holes.rec trivial (fun _ _ ih => ih)
  | abs _ => exact absurd h (by simp [IsProcHoles])
  | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcHoles])

def IsProcHoles.destruct {m : ModuleExpression Γ T} (h : IsProcHoles m) :
    Σ holes : HoleSigs, Σ sig : ProcedureSignature,
    { proc : ProcedureWithHoles holes sig //
      T = (.arr (HoleSigs.toModuleTypeRepTuple holes) (.proc sig))}
:= match m with
| @ModuleExpression.procHoles _ _ holes sigs _ p => ⟨holes, sigs, p, rfl⟩


/- # Normal forms -/

mutual

  /-- Beta-normal form: no beta-redex anywhere in the term. -/
  inductive Normal : ModuleExpression Δ T → Prop where
    | neutral : Neutral e → Normal e
    | abs {body : ModuleExpression (ModuleContext.append Δ A) B} : Normal body → Normal (.abs body)
    | pair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
             Normal a → Normal b → Normal (.pair a b)
    | proc : Normal (.proc p)
    | procHoles {holes sig} {ne : holes.NonEmpty} {p : ProcedureWithHoles holes sig} :
        Normal (.procHoles ne p)
    | unit : Normal .unit

  /-- Neutral form: no outermost redex.  Either the head is a variable, or it is a
      procedure-with-holes applied to a normal argument that is not a proc-tuple (so the
      δ-rule cannot fire) — both are stuck.
      `Neutral f` in `app` rules out `app (abs ..) ..`.
      `Neutral e` in `fst`/`snd` rules out `fst (pair ..)` / `snd (pair ..)`. -/
  inductive Neutral : ModuleExpression Δ T → Prop where
    | var : Neutral (.var r)
    | app {f : ModuleExpression Δ (.arr A B)} {arg : ModuleExpression Δ A} :
        Neutral f → Normal arg → Neutral (.app f arg)
    | appProcHoles {f : ModuleExpression Δ (.arr A B)} {arg : ModuleExpression Δ A} :
        IsProcHoles f → Normal arg → ¬ IsProcTuple arg → Neutral (.app f arg)
    | fst : Neutral e → Neutral (.fst e)
    | snd : Neutral e → Neutral (.snd e)
end

private def decidableNormalNeutral (m : ModuleExpression Δ t) :
    Decidable (Normal m) × Decidable (Neutral m) :=
  match m with
  | .unit => ⟨.isTrue .unit, .isFalse fun h => nomatch h⟩
  | .var _  => ⟨.isTrue (.neutral .var), .isTrue .var⟩
  | .proc _ => ⟨.isTrue .proc, .isFalse fun h => nomatch h⟩
  | .procHoles _ _ => ⟨.isTrue .procHoles, .isFalse fun h => nomatch h⟩
  | .abs body =>
      match (decidableNormalNeutral body).1 with
      | .isTrue hn   => ⟨.isTrue (.abs hn), .isFalse fun h => nomatch h⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .abs hb => hb | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .pair a b =>
      match (decidableNormalNeutral a).1, (decidableNormalNeutral b).1 with
      | .isTrue ha, .isTrue hb =>
          ⟨.isTrue (.pair ha hb), .isFalse fun h => nomatch h⟩
      | .isFalse ha, _ =>
          ⟨.isFalse fun h => ha (match h with | .pair hp _ => hp | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
      | .isTrue _, .isFalse hb =>
          ⟨.isFalse fun h => hb (match h with | .pair _ hq => hq | .neutral ne => nomatch ne),
           .isFalse fun h => nomatch h⟩
  | .app f arg => by
      -- An application is Normal iff it is Neutral (applications are never canonical values).
      -- It is Neutral either via `.app` (neutral head) or `.appProcHoles`
      -- (procedure-with-holes applied to a normal, non-proc-tuple argument).
      have df := decidableNormalNeutral f
      have da := decidableNormalNeutral arg
      have dN : Decidable (Neutral (.app f arg)) := by
        match df.2, da.1 with
        | .isTrue nf, .isTrue na => exact .isTrue (.app nf na)
        | _, .isFalse na =>
            exact .isFalse fun h => by
              cases h with
              | app _ na' => exact na na'
              | appProcHoles _ na' _ => exact na na'
        | .isFalse nf, .isTrue na =>
            if hph : IsProcHoles f then
              match instDecidableIsProcTuple arg with
              | .isFalse hpt => exact .isTrue (.appProcHoles hph na hpt)
              | .isTrue hpt =>
                  exact .isFalse fun h => by
                    cases h with
                    | app nf' _ => exact nf nf'
                    | appProcHoles _ _ hpt' => exact hpt' hpt
            else
              exact .isFalse fun h => by
                cases h with
                | app nf' _ => exact nf nf'
                | appProcHoles hph' _ _ => exact hph hph'
      exact ⟨(match dN with
              | .isTrue h => .isTrue (.neutral h)
              | .isFalse h => .isFalse fun hn => by cases hn with | neutral hne => exact h hne), dN⟩
  | .fst e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.fst hn)), .isTrue (.fst hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.fst he) => he),
           .isFalse fun h => hnn (match h with | .fst he => he)⟩
  | .snd e =>
      match (decidableNormalNeutral e).2 with
      | .isTrue hn   => ⟨.isTrue (.neutral (.snd hn)), .isTrue (.snd hn)⟩
      | .isFalse hnn =>
          ⟨.isFalse fun h => hnn (match h with | .neutral (.snd he) => he),
           .isFalse fun h => hnn (match h with | .snd he => he)⟩

instance (m : ModuleExpression Γ A) : Decidable (Normal m) := (decidableNormalNeutral m).1
instance (m : ModuleExpression Γ A) : Decidable (Neutral m) := (decidableNormalNeutral m).2

/-- Beta-normal form for closed terms (empty context).
    Neutral terms cannot occur (they would require a variable in the empty context),
    so this has fewer cases than `Normal`. The `abs` body is in a one-variable context
    and therefore still uses the general `Normal`. -/
inductive NormalClosed : ModuleExpression .empty T → Prop where
  | proc : NormalClosed (.proc p)
  | procHoles : NormalClosed (.procHoles n p)
  | abs {body : ModuleExpression (ModuleContext.append .empty A) B} :
                Normal body → NormalClosed (.abs body)
  | pair {a : ModuleExpression .empty A} {b : ModuleExpression .empty B} :
      NormalClosed a → NormalClosed b → NormalClosed (.pair a b)
  | unit : NormalClosed .unit

/-- Progress for the closed fragment, packaged so the two facts share one structural
    recursion on the term: a closed term is never neutral, and a closed `Normal` term of a
    procedure-argument type is a proc-tuple. -/
private lemma closed_progress : {T : ModuleTypeRep} → (m : ModuleExpression .empty T) →
    (¬ Neutral m) ∧ (IsProcArgType T → Normal m → IsProcTuple m)
  | _, .unit => ⟨fun hne => (nomatch hne), fun _ _ => trivial⟩
  | _, .proc _ => ⟨fun hne => (nomatch hne), fun ht _ => absurd ht (by simp [IsProcArgType])⟩
  | _, .procHoles _ _ => ⟨fun hne => (nomatch hne), fun ht _ => ht.elim⟩
  | _, .var r => nomatch r
  | _, .app f arg =>
      have ihf := closed_progress f
      have iharg := closed_progress arg
      have h1 : ¬ Neutral (.app f arg) := by
        intro hne
        cases hne with
        | app nf _ => exact ihf.1 nf
        | appProcHoles hph ha hpt => exact hpt (iharg.2 hph.isProcArgType ha)
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .fst e =>
      have ih := closed_progress e
      have h1 : ¬ Neutral (.fst e) := by intro hne; cases hne with | fst ne => exact ih.1 ne
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .snd e =>
      have ih := closed_progress e
      have h1 : ¬ Neutral (.snd e) := by intro hne; cases hne with | snd ne => exact ih.1 ne
      ⟨h1, fun _ hn => by cases hn with | neutral hne => exact absurd hne h1⟩
  | _, .abs _ => ⟨fun hne => (nomatch hne), fun ht _ => ht.elim⟩
  | _, .pair a b =>
      have iha := closed_progress a
      have ihb := closed_progress b
      ⟨fun hne => (nomatch hne), fun ht hn => by
        cases hn with
        | neutral hne => exact nomatch hne
        | pair ha hb =>
            cases a with
            | unit => exact absurd ht (by simp [IsProcArgType])
            | proc p => exact ihb.2 ht hb
            | var r => exact nomatch r
            | app _ _ => cases ha with | neutral hne => exact absurd hne iha.1
            | fst _ => cases ha with | neutral hne => exact absurd hne iha.1
            | snd _ => cases ha with | neutral hne => exact absurd hne iha.1
            | abs _ => exact ht.elim
            | procHoles _ _ => exact ht.elim
            | pair _ _ => exact ht.elim⟩

lemma empty_context_not_neutral {T : ModuleTypeRep} {m : ModuleExpression .empty T} : ¬ Neutral m :=
  (closed_progress m).1

lemma Normal.normalClosed {T : ModuleTypeRep} {m : ModuleExpression .empty T} :
    Normal m → NormalClosed m
  | .neutral h  => absurd h empty_context_not_neutral
  | .proc       => .proc
  | .procHoles  => .procHoles
  | .abs hb     => .abs hb
  | .pair ha hb => .pair ha.normalClosed hb.normalClosed
  | .unit       => .unit

lemma NormalClosed.normal {T : ModuleTypeRep} {m : ModuleExpression .empty T} :
    NormalClosed m → Normal m
  | .proc       => .proc
  | .procHoles  => .procHoles
  | .abs hb     => .abs hb
  | .pair ha hb => .pair ha.normal hb.normal
  | .unit       => .unit


/- # Reduction step -/


/-- Extends a renaming `ρ : ModuleContextIdx Δ → ModuleContextIdx Γ` to work under one
    binder of type `A`.
    The bound variable `.zero` maps to itself; outer variables `.succ r` are renamed by `ρ`
    and re-wrapped with `.succ`.  This is the typed analogue of incrementing the cutoff `c`
    in Pierce's shift operation. -/
def liftRenaming {Δ Γ : ModuleContext} {A : ModuleTypeRep}
    (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T) {T} :
    ModuleContextIdx (ModuleContext.append Δ A) T → ModuleContextIdx (ModuleContext.append Γ A) T
  | .zero   => .zero
  | .succ r => .succ (ρ r)

/-- Applies a renaming `ρ : ModuleContextIdx Δ → ModuleContextIdx Γ` to every variable in a term,
    producing a term over context `Γ`.
    Goes under binders by lifting `ρ` with `liftRename`.
    This is the typed analogue of Pierce's shift `↑_c^d`, where `ρ` encodes both the
    cutoff `c` and the displacement `d`. -/
def ModuleExpression.rename
    (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T) :
  ModuleExpression Δ T → ModuleExpression Γ T
| .unit => .unit
| .proc p  => .proc p
| .procHoles ne p => .procHoles ne p
| .var r    => .var (ρ r)
| .app f a  => .app (f.rename ρ) (a.rename ρ)
| .fst e    => .fst (e.rename ρ)
| .snd e    => .snd (e.rename ρ)
| .abs body => .abs (body.rename (liftRenaming ρ))
| .pair a b => .pair (a.rename ρ) (b.rename ρ)

/-- Extends a simultaneous substitution `σ : ModuleContextIdx Δ → ModuleExpression Γ`
    to work under one binder of type `A`,
    yielding a substitution `ModuleContextIdx (Δ,A) → ModuleExpression (Γ,A)`.
    The bound variable `.zero` maps to the fresh variable `.var .zero`;
    outer variables `.succ r` are substituted by `σ r` and then weakened into the
    extended context `Γ,A` by renaming with `.succ`. -/
def liftSubstitution {Δ Γ : ModuleContext} {A : ModuleTypeRep}
    (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T) {T} :
    ModuleContextIdx (ModuleContext.append Δ A) T → ModuleExpression (ModuleContext.append Γ A) T
  | .zero   => .var .zero
  | .succ r => (σ r).rename (fun {_} r => .succ r)

/-- Applies a simultaneous substitution `σ : ModuleContextIdx Δ → ModuleExpression Γ`
    to every variable in a term, producing a term over context `Γ`.
    Goes under binders by lifting `σ` with `liftSubst`. -/
def substituteSimultaneously (σ : ∀ {T}, ModuleContextIdx Δ T → ModuleExpression Γ T) :
   ModuleExpression Δ T → ModuleExpression Γ T
  | .unit => .unit
  | .proc p  => .proc p
  | .procHoles ne p => .procHoles ne p
  | .var r    => σ r
  | .app f a  => .app (substituteSimultaneously σ f) (substituteSimultaneously σ a)
  | .fst e    => .fst (substituteSimultaneously σ e)
  | .snd e    => .snd (substituteSimultaneously σ e)
  | .abs body => .abs (substituteSimultaneously (liftSubstitution σ) body)
  | .pair a b => .pair (substituteSimultaneously σ a) (substituteSimultaneously σ b)

/-- The single-variable substitution map used as the `σ` argument to `substSimultaneous`:
    de Bruijn index 0 (the outermost bound variable) maps to `arg`;
    any other index `k+1` maps back to the variable at index `k`. -/
def variableSubstitution {Δ : ModuleContext} {u : ModuleTypeRep} (arg : ModuleExpression Δ u) {T} :
    ModuleContextIdx (ModuleContext.append Δ u) T → ModuleExpression Δ T
  | .zero   => arg
  | .succ r => .var r

/-- Single-variable de Bruijn substitution: replaces de Bruijn index 0 in `body` with `arg`.
    Implemented via `substSimultaneous` with the point substitution `substVar arg`. -/
def substitute (body : ModuleExpression (Δ.append u) t) (arg : ModuleExpression Δ u) :
  ModuleExpression Δ t :=
  substituteSimultaneously (variableSubstitution arg) body

/-- Convert a `HoleSigs.Instantiation` into the corresponding module-expression tuple.

    Like `HoleSigs.toModuleTypeRepTuple`, this lives in `GaudisCrypt.TypedModules` rather than in
    `GaudisCrypt.HoleSigs`, so dot notation on an `Instantiation` does not find it. -/
def HoleSigs.Instantiation.toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → holes.Instantiation →
      ModuleExpression Δ (HoleSigs.toModuleTypeRepTuple holes)
  | .empty,       _    => .unit
  | .append _ _, inst =>
      .pair (.proc (inst .zero))
            (HoleSigs.Instantiation.toModuleTuple
              (fun idx => inst (.succ idx)))

/-- Non-deterministic single-step reduction: all possible one-step reductions. -/
inductive ReductionStep : ModuleExpression Δ T → ModuleExpression Δ T → Prop where
  | beta    {body : ModuleExpression (ModuleContext.append Δ A) T} {arg : ModuleExpression Δ A} :
      ReductionStep (.app (.abs body) arg) (substitute body arg)
  | appL    {f f' : ModuleExpression Δ (.arr A T)} {arg : ModuleExpression Δ A} :
      ReductionStep f f' → ReductionStep (.app f arg) (.app f' arg)
  | appR    {f : ModuleExpression Δ (.arr A T)} {arg arg' : ModuleExpression Δ A} :
      ReductionStep arg arg' → ReductionStep (.app f arg) (.app f arg')
  | lam     {body body' : ModuleExpression (ModuleContext.append Δ A) B} :
      ReductionStep body body' → ReductionStep (.abs body) (.abs body')
  | pairL   {a a' : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep a a' → ReductionStep (.pair a b) (.pair a' b)
  | pairR   {a : ModuleExpression Δ A} {b b' : ModuleExpression Δ B} :
      ReductionStep b b' → ReductionStep (.pair a b) (.pair a b')
  | fstPair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep (.fst (.pair a b)) a
  | fst     {e e' : ModuleExpression Δ (.prod A T)} :
      ReductionStep e e' → ReductionStep (.fst e) (.fst e')
  | sndPair {a : ModuleExpression Δ A} {b : ModuleExpression Δ B} :
      ReductionStep (.snd (.pair a b)) b
  | snd     {e e' : ModuleExpression Δ (.prod A T)} :
      ReductionStep e e' → ReductionStep (.snd e) (.snd e')
  /-- δ-reduction: a procedure-with-holes applied to a ground proc-tuple argument is
      instantiated, producing the closed procedure `substituteProcedure proc args`. -/
  | delta   {holes : HoleSigs} {sigs : ProcedureSignature} {ne : holes.NonEmpty}
            {proc : ProcedureWithHoles holes sigs}
            (instantiation : holes.Instantiation) :
      ReductionStep
        (.app (.procHoles ne proc) (HoleSigs.Instantiation.toModuleTuple instantiation))
        (.proc (proc.instantiate instantiation))

def MultiStepReduction : ModuleExpression Γ T → ModuleExpression Γ T → Prop :=
  Rewriting.Star ReductionStep

theorem multiStepReduction_app
    {m1 m1' : ModuleExpression Γ (.arr T U)} {m2 m2' : ModuleExpression Γ T}
    (h1 : MultiStepReduction m1 m1') (h2 : MultiStepReduction m2 m2') :
    MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2') := by
  have left : MultiStepReduction (ModuleExpression.app m1 m2) (ModuleExpression.app m1' m2) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appL hbc)
  have right : MultiStepReduction (ModuleExpression.app m1' m2) (ModuleExpression.app m1' m2') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.appR hbc)
  exact Rewriting.Star.trans left right



theorem multiStepReduction_fst
    {e e' : ModuleExpression Γ (.prod A B)} (h : MultiStepReduction e e') :
    MultiStepReduction (ModuleExpression.fst e) (ModuleExpression.fst e') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (.fst hbc)

theorem multiStepReduction_pair
    {a a' : ModuleExpression Γ A} {b b' : ModuleExpression Γ B}
    (h1 : MultiStepReduction a a') (h2 : MultiStepReduction b b') :
    MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b') := by
  have left : MultiStepReduction (ModuleExpression.pair a b) (ModuleExpression.pair a' b) := by
    induction h1 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairL hbc)
  have right : MultiStepReduction (ModuleExpression.pair a' b) (ModuleExpression.pair a' b') := by
    induction h2 with
    | refl => exact Rewriting.Star.refl _
    | tail _ hbc ih => exact Rewriting.Star.tail ih (.pairR hbc)
  exact Rewriting.Star.trans left right



/- # Call-by-value reduction step -/

/-- Inverse of `HoleSigs.Instantiation.toModuleTuple`: extract a `Procedure` for each hole index
    from a `ModuleExpression` that is a right-nested tuple of procedures (`IsProcTuple`). -/
def procTupleLookup {Δ : ModuleContext} :
    {holes : HoleSigs} → (m : ModuleExpression Δ (HoleSigs.toModuleTypeRepTuple holes)) →
    IsProcTuple m → holes.Instantiation
  | .empty, _, _ => fun n => nomatch n
  | .append _ _, m, h => fun n => by
      cases m with
      | pair a rest =>
          cases a with
          | proc p =>
              cases n with
              | zero => exact p
              | succ n' => exact procTupleLookup rest h n'
          | var _ | app _ _ | fst _ | snd _ => simp [IsProcTuple] at h
      | var _ | app _ _ | fst _ | snd _ => simp [IsProcTuple] at h

/-- Round-trip: converting a proc-tuple back to an instantiation and then to a tuple recovers
    the original expression. -/
lemma procTupleLookup_toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → (m : ModuleExpression Δ (HoleSigs.toModuleTypeRepTuple holes)) →
    (h : IsProcTuple m) →
    HoleSigs.Instantiation.toModuleTuple (Δ := Δ) (procTupleLookup m h) = m
  | .empty, m, h => by
      cases m with
      | unit => rfl
      | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcTuple])
  | .append _ _, m, h => by
      cases m with
      | pair a rest =>
          cases a with
          | proc p =>
              have ih := procTupleLookup_toModuleTuple (Δ := Δ) rest h
              exact congrArg (ModuleExpression.pair (.proc p)) ih
          | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcTuple])
      | var _ | app _ _ | fst _ | snd _ => exact absurd h (by simp [IsProcTuple])

def cbvReductionStep (m : ModuleExpression Δ t) (nn : ¬ Normal m) :
    ModuleExpression Δ t :=
  match m with
  | @ModuleExpression.app _ _  A B hd arg =>
      if abs : IsAbs hd then
        substitute abs.body arg
      else if h : IsProcHoles hd ∧ IsProcTuple arg then
        let ⟨holes, sigs, proc, tconv⟩ := h.1.destruct
        have a : A = (HoleSigs.toModuleTypeRepTuple holes) := by grind
        have b : B = ModuleTypeRep.proc sigs := by grind
        let ipt : IsProcTuple (a ▸ arg) := by grind
        let instantiation : holes.Instantiation := procTupleLookup (a ▸ arg) ipt
        let result := ModuleExpression.proc (proc.instantiate instantiation)
        b ▸ result
      else
        if nn_hd : ¬ Normal hd then
          .app (cbvReductionStep hd nn_hd) arg
        else
          have nn_arg : ¬ Normal arg := fun ha => by
            by_cases hph : IsProcHoles hd
            · exact nn (.neutral (.appProcHoles hph ha (fun hpt => h ⟨hph, hpt⟩)))
            · have hne : Neutral hd := by
                cases not_not.mp nn_hd with
                | neutral ne => exact ne
                | abs _ => exact absurd rfl abs
                | procHoles => exact absurd trivial hph
              exact nn (.neutral (.app hne ha))
          .app hd (cbvReductionStep arg nn_arg)
  | .proc p => absurd .proc nn
  | .procHoles _ p => absurd .procHoles nn
  | .abs body =>
      have nn' : ¬ Normal body := fun hb => nn (.abs hb)
      .abs (cbvReductionStep body nn')
  | .pair m1 m2 =>
      if nn1: ¬ Normal m1 then
        .pair (cbvReductionStep m1 nn1) m2
      else
        have nn2 : ¬ Normal m2 := fun h2 => nn (.pair (not_not.mp nn1) h2)
        .pair m1 (cbvReductionStep m2 nn2)
  | .fst m' =>
      if pair: IsPair m' then
        pair.fst
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.fst ne))
          | .pair _ _ => False.elim (by simp [IsPair] at *)
        .fst (cbvReductionStep m' nn')
  | .snd m' =>
      if pair: IsPair m' then
        pair.snd
      else
        have nn' : ¬ Normal m' := fun hn => match hn with
          | .neutral ne => nn (.neutral (.snd ne))
          | .pair _ _ => False.elim (by simp [IsPair] at *)
        .snd (cbvReductionStep m' nn')
  | .var n => absurd (.neutral .var) nn
  | .unit => absurd .unit nn


theorem cbvReductionStep_is_reductionStep (m : ModuleExpression Γ T) (nn : ¬ Normal m) :
    ReductionStep m (cbvReductionStep m nn) := by
  induction m with
  | proc p =>
      exact absurd .proc nn
  | procHoles ne p =>
      exact absurd .procHoles nn
  | var r =>
      exact absurd (.neutral .var) nn
  | unit =>
      exact absurd .unit nn
  | abs body ih =>
      exact .lam (ih (fun hb => nn (.abs hb)))
  | pair a b iha ihb =>
      simp only [cbvReductionStep]
      by_cases nn1 : ¬ Normal a
      · simp only [dif_pos nn1]; exact .pairL (iha nn1)
      · simp only [dif_neg nn1]
        exact .pairR (ihb (fun h2 => nn (.pair (not_not.mp nn1) h2)))
  | fst e ih =>
      simp only [cbvReductionStep]
      by_cases hp : IsPair e
      · simp only [dif_pos hp]
        cases e with
        | pair a b => exact .fstPair
        | var _ | app _ _ | fst _ | snd _ => exact absurd hp (by simp [IsPair])
      · simp only [dif_neg hp]
        exact .fst (ih (fun hn => by
          cases hn with
          | neutral ne => exact nn (.neutral (.fst ne))
          | pair _ _ => exact absurd rfl hp))
  | snd e ih =>
      simp only [cbvReductionStep]
      by_cases hp : IsPair e
      · simp only [dif_pos hp]
        cases e with
        | pair a b => exact .sndPair
        | var _ | app _ _ | fst _ | snd _ => exact absurd hp (by simp [IsPair])
      · simp only [dif_neg hp]
        exact .snd (ih (fun hn => by
          cases hn with
          | neutral ne => exact nn (.neutral (.snd ne))
          | pair _ _ => exact absurd rfl hp))
  | app f arg ihf iharg =>
      simp only [cbvReductionStep]
      by_cases hab : IsAbs f
      · -- beta: f = .abs body, result = substitute body arg
        simp only [dif_pos hab]
        cases f with
        | abs body => exact .beta
        | var _ | app _ _ | fst _ | snd _ | procHoles _ _ => exact absurd hab (by simp [IsAbs])
      · simp only [dif_neg hab]
        by_cases hph : IsProcHoles f ∧ IsProcTuple arg
        · -- delta: f = .procHoles ne proc, arg = instantiation.toModuleTuple
          simp only [dif_pos hph]
          cases f with
          | procHoles ne proc =>
              nth_rw 1 [← procTupleLookup_toModuleTuple arg hph.2]
              exact .delta _
          | abs _ | var _ | app _ _ | fst _ | snd _ => exact absurd hph.1 (by simp [IsProcHoles])
        · simp only [dif_neg hph]
          by_cases nn_f : ¬ Normal f
          · -- appL: f is not normal
            simp only [dif_pos nn_f]
            exact .appL (ihf nn_f)
          · -- appR: f is normal, arg is not normal
            simp only [dif_neg nn_f]
            refine .appR (iharg ?_)
            intro ha
            by_cases hph' : IsProcHoles f
            · exact nn (.neutral (.appProcHoles hph' ha (fun hpt => hph ⟨hph', hpt⟩)))
            · have hne : Neutral f := by
                cases not_not.mp nn_f with
                | neutral ne => exact ne
                | abs _ => simp [IsAbs] at hab
                | procHoles => simp [IsProcHoles] at hph'
              exact nn (.neutral (.app hne ha))


/- # Type erasure in module expressions -/

def ModuleExpression.erasedEqual
  (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') : Prop := match m, m' with
  | @ModuleExpression.proc _ _ sig p, @ModuleExpression.proc _ _ sig' p' => sig = sig' ∧ p ≍ p'
  | @ModuleExpression.procHoles _ _ holes sig _ p,
    @ModuleExpression.procHoles _ _ holes' sig' _ p' => holes = holes' ∧ sig = sig' ∧ p ≍ p'
  | .var r, .var r' => r.toNat = r'.toNat
  | .app f a, .app f' a' => ModuleExpression.erasedEqual f f' ∧ ModuleExpression.erasedEqual a a'
  | .fst e, .fst e' => ModuleExpression.erasedEqual e e'
  | .snd e, .snd e' => ModuleExpression.erasedEqual e e'
  | .pair a b, .pair a' b' => ModuleExpression.erasedEqual a a' ∧ ModuleExpression.erasedEqual b b'
  | .abs body, .abs body' => ModuleExpression.erasedEqual body body'
  | .unit, .unit => True
  | _, _ => False

theorem ModuleExpression.erasedEqual_refl (m : ModuleExpression Γ T) :
  ModuleExpression.erasedEqual m m := by
  induction m with
  | unit => trivial
  | proc => exact ⟨rfl, HEq.refl _⟩
  | procHoles => exact ⟨rfl, rfl, HEq.refl _⟩
  | var r => simp [ModuleExpression.erasedEqual]
  | app f a ihf iha => exact ⟨ihf, iha⟩
  | fst e ih => exact ih
  | snd e ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | abs body ih => exact ih


theorem ModuleExpression.erasedEqual_pair_right (a : ModuleExpression Γ T)
  {b : ModuleExpression Γ U} {b' : ModuleExpression Γ U'} (h : ModuleExpression.erasedEqual b b') :
  ModuleExpression.erasedEqual (.pair a b) (.pair a b') :=
  ⟨ModuleExpression.erasedEqual_refl a, h⟩

theorem ModuleExpression.erasedEqual_pair_left
    {a : ModuleExpression Γ T} {a' : ModuleExpression Γ T'}
    (b : ModuleExpression Γ U) (h : ModuleExpression.erasedEqual a a') :
    ModuleExpression.erasedEqual (.pair a b) (.pair a' b) :=
  ⟨h, ModuleExpression.erasedEqual_refl b⟩


theorem ModuleExpression.erasedEqual_normal_neutral_eq
    {Γ : ModuleContext} {T1 T2 : ModuleTypeRep}
    (m : ModuleExpression Γ T1) (m' : ModuleExpression Γ T2)
    (h : ModuleExpression.erasedEqual m m') :
    (Normal m → T1 = T2 → HEq m m') ∧ (Neutral m → T1 = T2 ∧ HEq m m') := by
  induction m generalizing T2 with
  | unit =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    rfl
  | proc p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case proc p' =>
      obtain ⟨hsig, hp⟩ := h
      subst hsig
      exact heq_of_eq (congrArg ModuleExpression.proc (eq_of_heq hp))
  | procHoles ne p =>
    refine ⟨fun _ _ => ?_, fun hne => by cases hne⟩
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case procHoles ne' p' =>
      obtain ⟨hholes, hsig, hp⟩ := h
      subst hholes; subst hsig
      obtain rfl := eq_of_heq hp
      rfl
  | var r =>
    cases m' <;> simp only [ModuleExpression.erasedEqual] at h
    case var r' =>
      obtain ⟨hT, hr⟩ := ModuleContextIdx.toNat_inj' _ _ h
      subst hT
      have heq : HEq (ModuleExpression.var r) (ModuleExpression.var r') :=
        heq_of_eq (congrArg ModuleExpression.var (eq_of_heq hr))
      exact ⟨fun _ _ => heq, fun _ => ⟨rfl, heq⟩⟩
  | app f arg ihf iharg =>
    cases m' with
    | app f' arg' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨hf_eq, harg_eq⟩ := h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf ha =>
            obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
            obtain ⟨hA, hB⟩ := ModuleTypeRep.arr.inj hTf
            subst hA hB
            exact (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                cases f' with
                | procHoles ne' p' =>
                    simp only [ModuleExpression.erasedEqual] at hf_eq
                    obtain ⟨hh, hs, hp⟩ := hf_eq
                    subst hh; subst hs; obtain rfl := eq_of_heq hp
                    obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                    rfl
                | var _ | app _ _ | fst _ | snd _ | abs _ =>
                    simp [ModuleExpression.erasedEqual] at hf_eq
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf ha =>
          obtain ⟨hTf, hf_heq⟩ := (ihf f' hf_eq).2 hf
          obtain ⟨hA, hB⟩ := ModuleTypeRep.arr.inj hTf
          subst hA hB
          exact ⟨rfl, (eq_of_heq hf_heq) ▸ (eq_of_heq ((iharg arg' harg_eq).1 ha rfl)) ▸ HEq.rfl⟩
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              cases f' with
              | procHoles ne' p' =>
                  simp only [ModuleExpression.erasedEqual] at hf_eq
                  obtain ⟨hh, hs, hp⟩ := hf_eq
                  subst hh; subst hs; obtain rfl := eq_of_heq hp
                  obtain rfl := eq_of_heq ((iharg arg' harg_eq).1 ha rfl)
                  exact ⟨rfl, HEq.rfl⟩
              | var _ | app _ _ | fst _ | snd _ | abs _ =>
                  simp [ModuleExpression.erasedEqual] at hf_eq
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | _ => simp [ModuleExpression.erasedEqual] at h
  | fst e ihe =>
    cases m' with
    | fst e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | fst hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleTypeRep.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | fst hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleTypeRep.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.fst (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | snd e ihe =>
    cases m' with
    | snd e' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn _
        cases hn with
        | neutral hne =>
          cases hne with
          | snd hne' =>
            obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
            obtain ⟨hA, hB⟩ := ModuleTypeRep.prod.inj hTe
            subst hA hB
            exact heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))
      · intro hne
        cases hne with
        | snd hne' =>
          obtain ⟨hTe, he_heq⟩ := (ihe e' h).2 hne'
          obtain ⟨hA, hB⟩ := ModuleTypeRep.prod.inj hTe
          subst hA hB
          exact ⟨rfl, heq_of_eq (congrArg ModuleExpression.snd (eq_of_heq he_heq))⟩
    | _ => simp [ModuleExpression.erasedEqual] at h
  | abs body ihbody =>
    cases m' with
    | abs body' =>
      simp only [ModuleExpression.erasedEqual] at h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | abs hb =>
          obtain ⟨hA, hB⟩ := ModuleTypeRep.arr.inj hT
          subst hA hB
          have hbody' := eq_of_heq ((ihbody body' h).1 hb rfl)
          subst hbody'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h
  | pair a b iha ihb =>
    cases m' with
    | pair a' b' =>
      simp only [ModuleExpression.erasedEqual] at h
      obtain ⟨ha_eq, hb_eq⟩ := h
      constructor
      · intro hn hT
        cases hn with
        | neutral hne => cases hne
        | pair ha hb =>
          obtain ⟨hA, hB⟩ := ModuleTypeRep.prod.inj hT
          subst hA hB
          have ha' := eq_of_heq ((iha a' ha_eq).1 ha rfl)
          have hb' := eq_of_heq ((ihb b' hb_eq).1 hb rfl)
          subst ha' hb'
          exact HEq.rfl
      · intro hne
        cases hne
    | _ => simp [ModuleExpression.erasedEqual] at h

theorem ModuleExpression.erasedEqual_normal_eq {Γ : ModuleContext} {T : ModuleTypeRep}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : ModuleExpression.erasedEqual n1 n2) : n1 = n2 :=
  eq_of_heq ((ModuleExpression.erasedEqual_normal_neutral_eq n1 n2 h).1 hn1 rfl)

theorem ModuleExpression.erasedEqual_neutral_eq {Γ : ModuleContext} {T1 T2 : ModuleTypeRep}
    {e1 : ModuleExpression Γ T1} {e2 : ModuleExpression Γ T2}
    (hne1 : Neutral e1)
    (h : ModuleExpression.erasedEqual e1 e2) : T1 = T2 ∧ HEq e1 e2 :=
  (ModuleExpression.erasedEqual_normal_neutral_eq e1 e2 h).2 hne1


/- # Mapping to Metatheory.STLCext -/

private scoped instance instModuleExpressionSTLCspec : Metatheory.STLCext.STLCspec where
  baseTypes := ProcedureSignature
  baseTypeValue := Procedure
  funcData := Σ holes : HoleSigs, Σ sig : ProcedureSignature, ProcedureWithHoles holes sig

private def ModuleTypeRep.toSTLC : ModuleTypeRep → Metatheory.STLCext.Ty
| .prod A B => .prod A.toSTLC B.toSTLC
| .arr A B => .arr A.toSTLC B.toSTLC
| .proc sig => .base sig
| .unit => .unit

private lemma toModuleTypeRepTuple_isArrowFree (holes : HoleSigs) :
    (HoleSigs.toModuleTypeRepTuple holes).toSTLC.isArrowFree := by
  induction holes with
  | empty => simp [HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
  | append _ _ ih =>
      simp [HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree, ih]

open Metatheory.STLCext in
private def basicTermHoleLookup : (holes : HoleSigs) →
    BasicTerm ((HoleSigs.toModuleTypeRepTuple holes).toSTLC) →
    holes.Instantiation
  | .empty, _ => fun n => nomatch n
  | .append Γ _, .pair (.value v) rest => fun n =>
      match n with
      | .zero   => v
      | .succ m => basicTermHoleLookup Γ rest m

open Metatheory.STLCext in
private noncomputable def ProcedureWithHoles.toSTLC {holes sig}
  (proc : ProcedureWithHoles holes sig) : Term :=
    let inputType := (HoleSigs.toModuleTypeRepTuple holes).toSTLC
    let outputType := (ModuleTypeRep.proc sig).toSTLC
    let inputArrowFree : inputType.isArrowFree := toModuleTypeRepTuple_isArrowFree holes
    let outputArrowFree : outputType.isArrowFree := by
      simp [outputType, ModuleTypeRep.toSTLC, Metatheory.STLCext.Ty.isArrowFree]
    let substitution : BasicTerm inputType → BasicTerm outputType :=
      fun basicTerm =>
        .value (proc.instantiate (basicTermHoleLookup holes basicTerm))
    .func (t := inputType) (u := outputType)
      (ht := inputArrowFree) (hu := outputArrowFree) ⟨holes, sig, proc⟩ substitution


private noncomputable def ModuleExpression.toSTLC :
    ModuleExpression Γ T → Metatheory.STLCext.Term
  | .unit => .unit
  | .proc p => .value p
  | .procHoles _ p => ProcedureWithHoles.toSTLC p
  | .var n => .var n.toNat
  | .app M N => .app M.toSTLC N.toSTLC
  | .fst M => .fst M.toSTLC
  | .snd M => .snd M.toSTLC
  | .abs M => .lam M.toSTLC
  | .pair M N => .pair M.toSTLC N.toSTLC

private def ModuleContext.toSTLC : ModuleContext → Metatheory.STLCext.Context
| .empty => []
| .append Γ T => T.toSTLC :: Γ.toSTLC

private lemma ModuleExpression.toSTLC_rename_shift (d : Nat)
    {Δ : ModuleContext} {T : ModuleTypeRep} (m : ModuleExpression Δ T) :
    ∀ (c : Nat) {Γ : ModuleContext}
      (ρ : ∀ {T}, ModuleContextIdx Δ T → ModuleContextIdx Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat < c → (ρ r).toNat = r.toNat)
      (_ : ∀ {T} (r : ModuleContextIdx Δ T), r.toNat ≥ c → (ρ r).toNat = r.toNat + d),
      ModuleExpression.toSTLC (m.rename ρ) =
      Metatheory.STLCext.Term.shift d c (ModuleExpression.toSTLC m) := by
  induction m with
  | unit => intros; simp [ModuleExpression.rename, ModuleExpression.toSTLC,
                          Metatheory.STLCext.Term.shift]
  | proc p => intros; simp [ModuleExpression.rename, ModuleExpression.toSTLC,
                            Metatheory.STLCext.Term.shift]
  | procHoles ne p =>
    intros
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC,
          Metatheory.STLCext.Term.shift]
  | var r =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift]
    by_cases h : r.toNat < c
    · simp only [h, ite_true]; congr 1; exact hlo _ h
    · simp only [h, ite_false]; congr 1
      have h' : r.toNat ≥ c := Nat.le_of_not_lt h
      have heq := hhi _ h'; omega
  | app f a ihf iha =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift,
          ihf c ρ hlo hhi, iha c ρ hlo hhi]
  | fst e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | snd e ih =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC,
          Metatheory.STLCext.Term.shift, ih c ρ hlo hhi]
  | pair a b iha ihb =>
    intro c Γ ρ hlo hhi
    simp [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift,
          iha c ρ hlo hhi, ihb c ρ hlo hhi]
  | abs body ih =>
    intro c Γ ρ hlo hhi
    simp only [ModuleExpression.rename, ModuleExpression.toSTLC, Metatheory.STLCext.Term.shift]
    congr 1
    apply ih (c + 1) (liftRenaming ρ)
    · intro T r hr
      cases r with
      | zero => simp [liftRenaming, ModuleContextIdx.toNat]
      | succ r' =>
        simp only [liftRenaming, ModuleContextIdx.toNat] at *
        have := hlo r' (by omega); omega
    · intro T r hr
      cases r with
      | zero => simp [ModuleContextIdx.toNat] at hr
      | succ r' =>
        simp only [liftRenaming, ModuleContextIdx.toNat] at *
        have := hhi r' (by omega); omega

private lemma ModuleExpression.toSTLC_substAll_level
    (N_stlc : Metatheory.STLCext.Term)
    {Δ' : ModuleContext} {T : ModuleTypeRep} (m : ModuleExpression Δ' T) :
    ∀ (k : Nat) {Γ : ModuleContext}
      (σ : ∀ {T}, ModuleContextIdx Δ' T → ModuleExpression Γ T)
      (_ : ∀ {T} (r : ModuleContextIdx Δ' T),
        ModuleExpression.toSTLC (σ r) =
        Metatheory.STLCext.Term.subst k
          (Metatheory.STLCext.Term.shift k 0 N_stlc)
          (Metatheory.STLCext.Term.var r.toNat)),
      ModuleExpression.toSTLC (substituteSimultaneously σ m) =
      Metatheory.STLCext.Term.subst k
        (Metatheory.STLCext.Term.shift k 0 N_stlc)
        (ModuleExpression.toSTLC m) := by
  induction m with
  | unit => intros; simp [substituteSimultaneously, ModuleExpression.toSTLC,
                          Metatheory.STLCext.Term.subst]
  | proc p => intros
              simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst]
  | procHoles ne p =>
    intros
    simp [substituteSimultaneously, ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC,
          Metatheory.STLCext.Term.subst]
  | var r =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, hσ]
  | app f a ihf iha =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst,
          ihf k σ hσ, iha k σ hσ]
  | fst e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | snd e ih =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst, ih k σ hσ]
  | pair a b iha ihb =>
    intro k Γ σ hσ
    simp [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst,
          iha k σ hσ, ihb k σ hσ]
  | abs body ih =>
    intro k Γ σ hσ
    simp only [substituteSimultaneously, ModuleExpression.toSTLC, Metatheory.STLCext.Term.subst]
    congr 1
    have hshift : (Metatheory.STLCext.Term.shift k 0 N_stlc).shift1 =
        Metatheory.STLCext.Term.shift (k + 1) 0 N_stlc := by
      simp only [Metatheory.STLCext.Term.shift1]
      rw [show (1 : Int) = ((1 : Nat) : Int) from by norm_num,
          Metatheory.STLCext.Term.shift_shift]
      congr 1; omega
    rw [hshift]
    apply ih (k + 1) (liftSubstitution σ)
    intro T r
    cases r with
    | zero =>
      simp only [liftSubstitution, ModuleExpression.toSTLC, ModuleContextIdx.toNat,
                 Metatheory.STLCext.Term.subst]
      simp [show ¬ (0 : Nat) > k + 1 from Nat.not_lt.mpr (Nat.zero_le _)]
    | succ r' =>
      simp only [liftSubstitution, ModuleContextIdx.toNat]
      rw [ModuleExpression.toSTLC_rename_shift 1 (σ r') 0 (fun {_} r => .succ r)
        (fun {_} r hr => absurd hr (Nat.not_lt.mpr (Nat.zero_le _)))
        (fun {_} r _ => by simp [ModuleContextIdx.toNat])]
      rw [hσ r']
      have key := Metatheory.STLCext.Term.shift1_subst
          (Metatheory.STLCext.Term.var r'.toNat)
          (Metatheory.STLCext.Term.shift (↑k) 0 N_stlc) k
      simp only [Metatheory.STLCext.Term.shift1] at key hshift
      rw [show (↑(1 : Nat) : Int) = (1 : Int) from by norm_cast, key, hshift]
      simp only [Metatheory.STLCext.Term.shift,
                 show ¬ (r'.toNat < (0 : Nat)) from Nat.not_lt.mpr (Nat.zero_le _), ite_false]
      norm_cast

private lemma ModuleExpression.toSTLC_subst
    {Δ : ModuleContext} {u T : ModuleTypeRep}
    (body : ModuleExpression (Δ.append u) T) (arg : ModuleExpression Δ u) :
    ModuleExpression.toSTLC (substitute body arg) =
    Metatheory.STLCext.Term.subst0 (ModuleExpression.toSTLC arg) (ModuleExpression.toSTLC body) := by
  simp only [substitute]
  rw [ModuleExpression.toSTLC_substAll_level (ModuleExpression.toSTLC arg) body 0 (variableSubstitution arg)]
  · simp [Metatheory.STLCext.Term.shift_zero]
  · intro T r
    cases r with
    | zero =>
      simp only [variableSubstitution, ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [Metatheory.STLCext.Term.shift_zero]
    | succ r' =>
      simp only [variableSubstitution, ModuleExpression.toSTLC,
                 ModuleContextIdx.toNat, Metatheory.STLCext.Term.subst]
      simp [show r'.toNat + 1 > 0 from Nat.succ_pos _]

/-- `toModuleTuple inst` erases to a basic STLC term. Defined in term mode so it is
    definitionally transparent (enabling `rfl` in the roundtrip below).
    Note: use `HoleSigs.Instantiation.toModuleTuple inst` explicitly; dot notation fails because
    `HoleSigs.Instantiation` is an `abbrev` that unfolds to a plain function type. -/
private def isBasicType_toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
    Metatheory.STLCext.Term.isBasicType (HoleSigs.toModuleTypeRepTuple holes).toSTLC
        (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) inst).toSTLC
  | .empty,    _    => trivial
  | .append _ _, inst =>
      -- isBasicType (.base sig) (.value (inst .zero)) reduces to (sig = sig) = rfl, not True
      ⟨rfl, isBasicType_toModuleTuple (fun idx => inst (.succ idx))⟩

/-- Reading the procedures back from the STLC encoding of `toModuleTuple inst` recovers `inst`.
    Term-mode so `isBasicType_toModuleTuple` unfolds and `rfl`/direct recursion closes goals. -/
private def basicTermHoleLookup_toModuleTuple {Δ : ModuleContext} :
    {holes : HoleSigs} → (inst : holes.Instantiation) →
    {sig : ProcedureSignature} → (n : HoleIndex holes sig) →
    basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple (Δ := Δ) inst)) n = inst n
  | .empty,    _,    _, n => nomatch n
  | .append _ _, _, _, .zero   => rfl
  | .append _ _, inst, _, .succ m =>
      basicTermHoleLookup_toModuleTuple (fun idx => inst (.succ idx)) m


-- Two instantiations that agree on every hole index produce the same statement.
-- Generic in the local-state `l` (a variable here), so `induction` is well-formed —
-- unlike inducting on a procedure body, whose `l` is a fixed `sig.LocalVariableState …`.
private lemma StmtWithHoles.instantiate_congr_of_agree {holes : HoleSigs} {l : Type}
    (s : StmtWithHoles holes l) {f g : holes.Instantiation}
    (h : ∀ {sig} (n : HoleIndex holes sig), f n = g n) :
    s.instantiate f = s.instantiate g := by
  induction s with
  | hole n _ _ => simp only [StmtWithHoles.instantiate]; rw [h n]
  | seq _ _ ih1 ih2 => simp only [StmtWithHoles.instantiate]; rw [ih1 h, ih2 h]
  | ifThenElse _ _ _ iht ihe => simp only [StmtWithHoles.instantiate]; rw [iht h, ihe h]
  | «while» _ _ ihb => simp only [StmtWithHoles.instantiate]; rw [ihb h]
  | _ => rfl

-- `funext` cannot introduce the implicit `{sig}` binder in `holes.Instantiation`.
-- Instead prove the needed instantiate equality via the agreement lemma above.
private lemma instantiate_congr {Δ : ModuleContext} {holes : HoleSigs} (args : holes.Instantiation)
    {sig : ProcedureSignature} (proc : ProcedureWithHoles holes sig) :
    proc.instantiate (basicTermHoleLookup holes
      (Metatheory.STLCext.Term.toBasicTerm _ _ (isBasicType_toModuleTuple (Δ := Δ) args)))
    = proc.instantiate args := by
  obtain ⟨_, body, _⟩ := proc
  simp only [ProcedureWithHoles.instantiate]
  congr 1
  exact StmtWithHoles.instantiate_congr_of_agree body
    (fun n => basicTermHoleLookup_toModuleTuple (Δ := Δ) args n)

/-- `toModuleTuple inst` always satisfies `IsProcTuple`. -/
lemma toModuleTuple_isProcTuple {Δ : ModuleContext} {holes : HoleSigs}
    (inst : holes.Instantiation) :
    IsProcTuple (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) inst) := by
  induction holes with
  | empty => simp [HoleSigs.Instantiation.toModuleTuple, IsProcTuple]
  | append holeTail sig ih =>
      simp only [HoleSigs.Instantiation.toModuleTuple]
      exact ih (fun idx => inst (.succ idx))

/-- Round-trip from the STLC side: if `arg.toSTLC` is a basic term of the hole-tuple type,
    then recovering the instantiation from that basic term and converting back gives `arg`. -/
private lemma toModuleTuple_of_basicType {Δ : ModuleContext} :
    {holes : HoleSigs} → (arg : ModuleExpression Δ (HoleSigs.toModuleTypeRepTuple holes)) →
    (h : Metatheory.STLCext.Term.isBasicType
          (HoleSigs.toModuleTypeRepTuple holes).toSTLC arg.toSTLC) →
    HoleSigs.Instantiation.toModuleTuple (Δ := Δ)
      (basicTermHoleLookup holes (Metatheory.STLCext.Term.toBasicTerm _ _ h)) = arg
  | .empty, arg, h => by
      cases arg with
      | unit => rfl
      | var _ | app _ _ | fst _ | snd _ =>
          simp [ModuleExpression.toSTLC, HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC,
                Metatheory.STLCext.Term.isBasicType] at h
  | .append holeTail sig, arg, h => by
      cases arg with
      | pair a rest =>
          cases a with
          | proc p =>
              obtain ⟨h1, h2⟩ := h
              simp only [HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC, ModuleExpression.toSTLC,
                         Metatheory.STLCext.Term.toBasicTerm,
                         HoleSigs.Instantiation.toModuleTuple]
              exact congrArg (ModuleExpression.pair (.proc p))
                (toModuleTuple_of_basicType (Δ := Δ) rest h2)
          | var _ | app _ _ | fst _ | snd _ =>
              simp [ModuleExpression.toSTLC, HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC,
                    Metatheory.STLCext.Term.isBasicType] at h
      | var _ | app _ _ | fst _ | snd _ =>
          simp [ModuleExpression.toSTLC, HoleSigs.toModuleTypeRepTuple, ModuleTypeRep.toSTLC,
                Metatheory.STLCext.Term.isBasicType] at h

private theorem reductionStep_stlc_compat (m m' : ModuleExpression Γ T) :
    ReductionStep m m' →
    Metatheory.STLCext.Step (ModuleExpression.toSTLC m) (ModuleExpression.toSTLC m') := by
  intro h
  induction h with
  | beta =>
      simp only [ModuleExpression.toSTLC]
      rw [ModuleExpression.toSTLC_subst]
      exact .beta _ _
  | appL _ ih => simp only [ModuleExpression.toSTLC]; exact .appL ih
  | appR _ ih => simp only [ModuleExpression.toSTLC]; exact .appR ih
  | lam _ ih  => simp only [ModuleExpression.toSTLC]; exact .lam ih
  | pairL _ ih => simp only [ModuleExpression.toSTLC]; exact .pairL ih
  | pairR _ ih => simp only [ModuleExpression.toSTLC]; exact .pairR ih
  | fstPair => simp only [ModuleExpression.toSTLC]; exact .fstPair _ _
  | fst _ ih  => simp only [ModuleExpression.toSTLC]; exact .fst ih
  | sndPair => simp only [ModuleExpression.toSTLC]; exact .sndPair _ _
  | snd _ ih  => simp only [ModuleExpression.toSTLC]; exact .snd ih
  | delta args =>
      rename_i Δ holes sigs ne proc
      simp only [ModuleExpression.toSTLC]
      rw [show Metatheory.STLCext.Term.value (proc.instantiate args)
            = Metatheory.STLCext.BasicTerm.toTerm
                ((fun bt => Metatheory.STLCext.BasicTerm.value
                    (proc.instantiate (basicTermHoleLookup holes bt)))
                  (Metatheory.STLCext.Term.toBasicTerm _
                    (ModuleExpression.toSTLC (HoleSigs.Instantiation.toModuleTuple (Δ := Δ) args))
                    (isBasicType_toModuleTuple (Δ := Δ) args)))
            from by
              simp only [Metatheory.STLCext.BasicTerm.toTerm]
              exact congrArg Metatheory.STLCext.Term.value (instantiate_congr (Δ := Δ) args proc).symm]
      exact Metatheory.STLCext.Step.funcApp _ _ _ _

private theorem ModuleExpression.toSTLC_hasType (m : ModuleExpression Γ T) :
  Metatheory.STLCext.HasType (ModuleContext.toSTLC Γ) m.toSTLC T.toSTLC
   := by induction m with
  | proc c =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    exact Metatheory.STLCext.HasType.value c
  | procHoles _ _ =>
    exact Metatheory.STLCext.HasType.func _ _
  | abs M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC, ModuleContext.toSTLC] at *
    exact Metatheory.STLCext.HasType.lam ihM
  | pair M N ihM ihN =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    exact Metatheory.STLCext.HasType.pair ihM ihN
  | app M N ihM ihN =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    exact Metatheory.STLCext.HasType.app ihM ihN
  | fst M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    exact Metatheory.STLCext.HasType.fst ihM
  | snd M ihM =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    exact Metatheory.STLCext.HasType.snd ihM
  | unit => exact Metatheory.STLCext.HasType.unit
  | var n =>
    simp only [ModuleExpression.toSTLC, ModuleTypeRep.toSTLC]
    apply Metatheory.STLCext.HasType.var
    induction n with
    | zero =>
      simp [ModuleContextIdx.toNat, ModuleContext.toSTLC]
    | succ n ih =>
      simp [ModuleContextIdx.toNat, ModuleContext.toSTLC, ih]

private theorem reductionStep_stlc_complete
  (m : ModuleExpression Γ T) (M' : Metatheory.STLCext.Term)
  (h : Metatheory.STLCext.Step (ModuleExpression.toSTLC m) M') :
    ∃ m', ReductionStep m m' ∧ ModuleExpression.toSTLC m' = M' := by
  induction m generalizing M' with
  | unit | proc _ | procHoles _ _ | var _ => simp only [ModuleExpression.toSTLC] at h; cases h
  | app f arg ihf iharg =>
      -- case-split on f first so ModuleExpression.toSTLC f is a literal constructor
      -- after simp, enabling cases h without dependent-elim failures
      cases f with
      | abs body =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | beta => exact ⟨substitute body arg, .beta, ModuleExpression.toSTLC_subst body arg⟩
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.abs body) arg', .appR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | procHoles ne proc =>
          simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
          cases h with
          | appL step => nomatch step
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app (.procHoles ne proc) arg', .appR hnd,
                by simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC, heq]⟩
          | funcApp d g N hbasic =>
              refine ⟨.proc (proc.instantiate (basicTermHoleLookup _
                  (Metatheory.STLCext.Term.toBasicTerm _ _ hbasic))), ?_, ?_⟩
              · exact Eq.subst
                    (motive := fun x => ReductionStep (.app (.procHoles ne proc) x)
                      (.proc (proc.instantiate (basicTermHoleLookup _
                        (Metatheory.STLCext.Term.toBasicTerm _ _ hbasic)))))
                    (toModuleTuple_of_basicType arg hbasic)
                    (ReductionStep.delta _)
              · rfl
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | appL step =>
              obtain ⟨f', hnd, heq⟩ := ihf _ step
              exact ⟨.app f' arg, .appL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
          | appR step =>
              obtain ⟨arg', hnd, heq⟩ := iharg _ step
              exact ⟨.app _ arg', .appR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | abs body ih =>
      simp only [ModuleExpression.toSTLC] at h
      cases h with
      | lam step =>
          obtain ⟨body', hnd, heq⟩ := ih _ step
          exact ⟨.abs body', .lam hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | pair a b iha ihb =>
      simp only [ModuleExpression.toSTLC] at h
      cases h with
      | pairL step =>
          obtain ⟨a', hnd, heq⟩ := iha _ step
          exact ⟨.pair a' b, .pairL hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | pairR step =>
          obtain ⟨b', hnd, heq⟩ := ihb _ step
          exact ⟨.pair a b', .pairR hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | fst e ih =>
      -- case-split on e first for the same reason
      cases e with
      | pair e1 e2 =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | fstPair => exact ⟨e1, .fstPair, rfl⟩
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | fst step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.fst e', .fst hnd, by simp [ModuleExpression.toSTLC, heq]⟩
  | snd e ih =>
      cases e with
      | pair e1 e2 =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | sndPair => exact ⟨e2, .sndPair, rfl⟩
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [ModuleExpression.toSTLC, heq]⟩
      | var _ | app _ _ | fst _ | snd _ =>
          simp only [ModuleExpression.toSTLC] at h
          cases h with
          | snd step =>
              obtain ⟨e', hnd, heq⟩ := ih _ step
              exact ⟨.snd e', .snd hnd, by simp [ModuleExpression.toSTLC, heq]⟩

private theorem multiStepReduction_to_stlc_star {m m' : ModuleExpression Γ T}
    (h : MultiStepReduction m m') :
    Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m) (ModuleExpression.toSTLC m')
    := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail hab hbc ih => exact Rewriting.Star.tail ih (reductionStep_stlc_compat _ _ hbc)

private theorem ModuleExpression.toSTLC_Normal_iff {m : ModuleExpression Γ T} :
    Normal m ↔ Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m) := by
  constructor
  · intro hm
    suffices key : ∀ {Γ' : ModuleContext} {T' : ModuleTypeRep} (m' : ModuleExpression Γ' T'),
        (Normal m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m')) ∧
        (Neutral m' → Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC m') ∧
                     (∀ body, ModuleExpression.toSTLC m' ≠ Metatheory.STLCext.Term.lam body) ∧
                     (∀ P Q, ModuleExpression.toSTLC m' ≠ Metatheory.STLCext.Term.pair P Q)) from
      (key m).1 hm
    intro Γ' T' m'
    induction m' with
    | unit =>
      constructor
      · intro _ N h; simp only [ModuleExpression.toSTLC] at h; cases h
      · intro hne; nomatch hne
    | var n =>
      constructor
      · intro _ N h; simp only [ModuleExpression.toSTLC] at h; cases h
      · intro _; refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
        · simp only [ModuleExpression.toSTLC] at h; cases h
        · intro h; cases h
        · intro h; cases h
    | proc _ | procHoles _ _ =>
      constructor
      · intro _ N h; simp only [ModuleExpression.toSTLC] at h; cases h
      · intro h; cases h
    | abs body ih =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | abs hb => cases h with | lam step => exact (ih.1 hb) _ step
      · intro h; exact nomatch h
    | pair a b iha ihb =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne => exact nomatch hne
        | pair ha hb =>
          cases h with
          | pairL step => exact (iha.1 ha) _ step
          | pairR step => exact (ihb.1 hb) _ step
      · intro h; exact nomatch h
    | app f arg ihf iharg =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with
        | neutral hne =>
          cases hne with
          | app hf_n harg_n =>
            obtain ⟨ihf_step, ihf_lam, _⟩ := ihf.2 hf_n
            generalize hF : ModuleExpression.toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [ModuleExpression.toSTLC] at hF
          | appProcHoles hph ha hpt =>
            cases f with
            | procHoles ne p =>
                simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic =>
                    exact absurd
                      (toModuleTuple_of_basicType arg hbasic ▸
                        toModuleTuple_isProcTuple _)
                      hpt
            | abs _ => exact absurd hph (by simp [IsProcHoles])
            | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
      · intro hne
        cases hne with
        | app hf_n harg_n =>
          obtain ⟨ihf_step, ihf_lam, ihf_pair⟩ := ihf.2 hf_n
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hF : ModuleExpression.toSTLC f = F at h
            cases h with
            | beta M0 N0 => exact absurd hF (ihf_lam M0)
            | appL step => rw [← hF] at step; exact ihf_step _ step
            | appR step => exact (iharg.1 harg_n) _ step
            | funcApp => cases hf_n <;> simp [ModuleExpression.toSTLC] at hF
          · intro h; cases h
          · intro h; cases h
        | appProcHoles hph ha hpt =>
          cases f with
          | procHoles ne p =>
              refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
              · simp only [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
                cases h with
                | appL step => nomatch step
                | appR step => exact (iharg.1 ha) _ step
                | funcApp d g N' hbasic =>
                    exact absurd
                      (toModuleTuple_of_basicType arg hbasic ▸
                        toModuleTuple_isProcTuple _)
                      hpt
              · intro h; cases h
              · intro h; cases h
          | abs _ => exact absurd hph (by simp [IsProcHoles])
          | var _ | app _ _ | fst _ | snd _ => exact absurd hph (by simp [IsProcHoles])
    | fst e ihe =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with | neutral hne => cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : ModuleExpression.toSTLC e = E at h
          cases h with
          | fstPair => exact absurd hE (ihe_pair _ _)
          | fst step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | fst hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hE : ModuleExpression.toSTLC e = E at h
            cases h with
            | fstPair => exact absurd hE (ihe_pair _ _)
            | fst step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
    | snd e ihe =>
      constructor
      · intro hn N h
        simp only [ModuleExpression.toSTLC] at h
        cases hn with | neutral hne => cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          generalize hE : ModuleExpression.toSTLC e = E at h
          cases h with
          | sndPair => exact absurd hE (ihe_pair _ _)
          | snd step => rw [← hE] at step; exact ihe_step _ step
      · intro hne; cases hne with | snd hne_e =>
          obtain ⟨ihe_step, _, ihe_pair⟩ := ihe.2 hne_e
          refine ⟨fun N h => ?_, fun _ => ?_, fun _ _ => ?_⟩
          · simp only [ModuleExpression.toSTLC] at h
            generalize hE : ModuleExpression.toSTLC e = E at h
            cases h with
            | sndPair => exact absurd hE (ihe_pair _ _)
            | snd step => rw [← hE] at step; exact ihe_step _ step
          · intro h; cases h
          · intro h; cases h
  · intro h
    by_contra hnn
    exact h _ (reductionStep_stlc_compat m _ (cbvReductionStep_is_reductionStep m hnn))

/-- The STLC translation of a procedure-with-holes determines the procedure (and its
    hole/return signatures). -/
private theorem ProcedureWithHoles.toSTLC_inj {holes holes' : HoleSigs}
    {sig sig' : ProcedureSignature}
    {p : ProcedureWithHoles holes sig} {p' : ProcedureWithHoles holes' sig'} :
    ProcedureWithHoles.toSTLC p = ProcedureWithHoles.toSTLC p' → holes = holes' ∧ sig = sig' ∧ p ≍ p' := by
  intro h
  simp only [ProcedureWithHoles.toSTLC] at h
  rw [Metatheory.STLCext.Term.func.injEq] at h
  obtain ⟨-, -, hdata, -⟩ := h
  -- hdata : (⟨holes, sig, p⟩ : FuncData) = ⟨holes', sig', p'⟩
  injection hdata with h1 h2
  subst h1
  injection (eq_of_heq h2) with h3 h4
  subst h3
  exact ⟨rfl, rfl, h4⟩

private theorem ModuleExpression.toSTLC_injective {Γ Γ' : ModuleContext} {T T' : ModuleTypeRep}
    (m : ModuleExpression Γ T) (m' : ModuleExpression Γ' T') :
    ModuleExpression.toSTLC m = ModuleExpression.toSTLC m' → ModuleExpression.erasedEqual m m' := by
  revert Γ' T' m'
  induction m with
  | unit =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | proc p =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | procHoles ne p =>
    intro Γ' T' m' h
    cases m' with
    | unit => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
    | procHoles ne' p' =>
        simp only [ModuleExpression.toSTLC] at h
        exact ProcedureWithHoles.toSTLC_inj h
    | proc _ | var _ | app _ _ | fst _ | snd _ | abs _ | pair _ _ =>
        simp_all [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC]
  | var r =>
    intro Γ' T' m' h
    cases m' <;> simp_all [ModuleExpression.toSTLC, ModuleExpression.erasedEqual, ProcedureWithHoles.toSTLC]
  | app f a ihf iha =>
    intro Γ' T' m' h
    cases m' with
    | app f' a' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.app.injEq] at h
      exact ⟨ihf f' h.1, iha a' h.2⟩
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | fst e ih =>
    intro Γ' T' m' h
    cases m' with
    | fst e' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.fst.injEq] at h
      exact ih e' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | snd e ih =>
    intro Γ' T' m' h
    cases m' with
    | snd e' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.snd.injEq] at h
      exact ih e' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | pair a b iha ihb =>
    intro Γ' T' m' h
    cases m' with
    | pair a' b' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.pair.injEq] at h
      exact ⟨iha a' h.1, ihb b' h.2⟩
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h
  | abs body ih =>
    intro Γ' T' m' h
    cases m' with
    | abs body' =>
      simp only [ModuleExpression.toSTLC, Metatheory.STLCext.Term.lam.injEq] at h
      exact ih body' h
    | _ => simp [ModuleExpression.toSTLC, ProcedureWithHoles.toSTLC] at h

private theorem ModuleExpression.toSTLC_injective_normal {Γ : ModuleContext} {T : ModuleTypeRep}
    {n1 n2 : ModuleExpression Γ T} (hn1 : Normal n1)
    (h : ModuleExpression.toSTLC n1 = ModuleExpression.toSTLC n2) : n1 = n2 :=
  ModuleExpression.erasedEqual_normal_eq hn1 (ModuleExpression.toSTLC_injective n1 n2 h)


/- # Strong normalization -/

private theorem reduce_acc {Γ : ModuleContext} {T : ModuleTypeRep} (m : ModuleExpression Γ T) :
    Acc (fun p q : ModuleExpression Γ T =>
      Metatheory.STLCext.Step (ModuleExpression.toSTLC q) (ModuleExpression.toSTLC p)) m := by
  suffices h : ∀ M : Metatheory.STLCext.Term, Metatheory.STLCext.SN M →
      ∀ (n : ModuleExpression Γ T), ModuleExpression.toSTLC n = M → Acc (fun p q =>
          Metatheory.STLCext.Step (ModuleExpression.toSTLC q) (ModuleExpression.toSTLC p)) n from
    h _ (Metatheory.STLCext.strong_normalization (ModuleExpression.toSTLC_hasType m)) m rfl
  intro M sn
  induction sn with
  | intro _ h_acc ih =>
    intro n heq
    apply Acc.intro
    intro q step
    rw [heq] at step
    exact ih _ step q rfl

private scoped instance (priority := 1001)
    instWellFoundedRelationModuleExpressionReduction {Γ : ModuleContext} {T : ModuleTypeRep} :
    WellFoundedRelation (ModuleExpression Γ T) :=
  ⟨fun p q => ReductionStep q p,
   ⟨fun m => by
     have lift : ∀ (n : ModuleExpression Γ T),
         Acc (fun p q =>
               Metatheory.STLCext.Step q.toSTLC p.toSTLC) n →
         Acc (fun p q => ReductionStep q p) n := by
       intro n h
       induction h with
       | intro x _ ih => exact Acc.intro x (fun y step => ih y (reductionStep_stlc_compat x y step))
     exact lift m (reduce_acc m)⟩⟩

/- # Full reduction -/

def reduce (m : ModuleExpression Γ T) : ModuleExpression Γ T :=
    if h : Normal m then m
    else
      reduce (cbvReductionStep m h)
termination_by m
decreasing_by
  exact cbvReductionStep_is_reductionStep m h

theorem multiStepReduction_reduce {m : ModuleExpression Γ T} :
    MultiStepReduction m (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => MultiStepReduction m (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact Rewriting.Star.refl _
  · apply Rewriting.Star.head (cbvReductionStep_is_reductionStep n h)
    exact ih (cbvReductionStep n h) (cbvReductionStep_is_reductionStep n h)

theorem reduce_normal (m : ModuleExpression Δ t) : Normal (reduce m) := by
  apply WellFoundedRelation.wf.induction (C := fun m => Normal (reduce m)) m
  intro n ih
  unfold reduce
  split_ifs with h
  · exact h
  · exact ih (cbvReductionStep n h) (cbvReductionStep_is_reductionStep n h)

theorem reduce_normalClosed (m : ModuleExpression .empty t) : NormalClosed (reduce m) :=
  (reduce_normal m).normalClosed

@[simp]
theorem reduce_fst_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (.fst (.pair m1 m2)) = reduce m1 := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_fst (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.fst (ModuleExpression.pair m m')) = reduce m := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | fst ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_snd (m : ModuleExpression Γ T) (m' : ModuleExpression Γ T') :
  reduce (ModuleExpression.snd (ModuleExpression.pair m m')) = reduce m' := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with | snd ne' => exact nomatch ne'
  · rfl

@[simp]
theorem reduce_idempotent (m : ModuleExpression Γ T) :
  reduce (reduce m) = reduce m := by
  conv_lhs => unfold reduce
  simp [reduce_normal m]


@[simp]
theorem reduce_beta
  (body : ModuleExpression (Γ.append T) U) (arg : ModuleExpression Γ T) :
  reduce (ModuleExpression.app (ModuleExpression.abs body) arg) = reduce (substitute body arg) := by
  conv_lhs => unfold reduce
  split_ifs with h
  · cases h with | neutral ne => cases ne with
      | app ne' _ => exact nomatch ne'
      | appProcHoles hph _ _ => exact absurd hph (by simp [IsProcHoles])
  · rfl


/- # Confluence -/

theorem confluence {m m1 m2 : ModuleExpression Γ T}
   (h1 : MultiStepReduction m m1) (h2 : MultiStepReduction m m2) :
   reduce m1 = reduce m2 := by
  have star1 : Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m)
                                                      (ModuleExpression.toSTLC (reduce m1)) :=
    Rewriting.Star.trans (multiStepReduction_to_stlc_star h1)
                         (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have star2 : Rewriting.Star Metatheory.STLCext.Step (ModuleExpression.toSTLC m)
                                                      (ModuleExpression.toSTLC (reduce m2)) :=
    Rewriting.Star.trans
      (multiStepReduction_to_stlc_star h2)
      (multiStepReduction_to_stlc_star multiStepReduction_reduce)
  have nf1 : Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC (reduce m1)) :=
    ModuleExpression.toSTLC_Normal_iff.mp (reduce_normal m1)
  have nf2 : Rewriting.IsNormalForm Metatheory.STLCext.Step (ModuleExpression.toSTLC (reduce m2)) :=
    ModuleExpression.toSTLC_Normal_iff.mp (reduce_normal m2)
  exact ModuleExpression.toSTLC_injective_normal (reduce_normal m1)
    (Rewriting.normalForm_unique Metatheory.STLCext.step_confluent star1 star2 nf1 nf2)


theorem reduce_app (m : ModuleExpression Γ (.arr T U)) (m' : ModuleExpression Γ T) :
  reduce (ModuleExpression.app m m') = reduce (ModuleExpression.app (reduce m) (reduce m')) :=
  (reduce_idempotent _).symm.trans
    (confluence multiStepReduction_reduce
      (multiStepReduction_app multiStepReduction_reduce multiStepReduction_reduce))

theorem reduce_fst_cong (m m' : ModuleExpression Γ (.prod T U)) :
    reduce m = reduce m' → reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst m') := by
  intro h
  have eq1 : reduce (ModuleExpression.fst m) = reduce (ModuleExpression.fst (reduce m)) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  have eq2 : reduce (ModuleExpression.fst m') = reduce (ModuleExpression.fst (reduce m')) :=
    (reduce_idempotent _).symm.trans
      (confluence multiStepReduction_reduce (multiStepReduction_fst multiStepReduction_reduce))
  rw [eq1, eq2, h]


theorem reduce_pair {T U} (m1 : ModuleExpression Γ T) (m2 : ModuleExpression Γ U) :
    reduce (ModuleExpression.pair m1 m2) = ModuleExpression.pair (reduce m1) (reduce m2) := by
  have h2 : MultiStepReduction (ModuleExpression.pair m1 m2)
            (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    multiStepReduction_pair multiStepReduction_reduce multiStepReduction_reduce
  have key : reduce (ModuleExpression.pair m1 m2) =
             reduce (ModuleExpression.pair (reduce m1) (reduce m2)) :=
    (reduce_idempotent _).symm.trans (confluence multiStepReduction_reduce h2)
  rw [key]; conv_lhs => unfold reduce
  rw [dif_pos (Normal.pair (reduce_normal m1) (reduce_normal m2))]

theorem pair_type_is_pair {m : ModuleExpression _ (.prod t1 t2)} (_ : NormalClosed m) :
  ∃ m1 m2, m = .pair m1 m2 := by
  rename_i h
  cases h
  exact ⟨_, _, rfl⟩

/- # Modules -/

structure Module (T : ModuleTypeRep) where
  expression : ModuleExpression .empty T
  normal : NormalClosed expression

def ModuleExpression.toModule {T : ModuleTypeRep}
  (m : ModuleExpression .empty T) : Module T :=
  ⟨reduce m, reduce_normalClosed m⟩

instance : CoeFun (Module (.arr T U)) (fun _ ↦ Module T → Module U) where
  coe f x := ModuleExpression.toModule (ModuleExpression.app f.expression x.expression)

def Module.fst' {T U} (m : Module (.prod T U)) : Module T :=
  m.expression.fst.toModule

def Module.snd' {T U} (m : Module (.prod T U)) : Module U :=
  m.expression.snd.toModule

def Module.pair' {T U} (m1 : Module T) (m2 : Module U) : Module (.prod T U) :=
  (m1.expression.pair m2.expression).toModule

@[ext]
theorem Module.ext {T} {m1 m2 : Module T} (h : m1.expression = m2.expression) :
  m1 = m2 := by
  obtain ⟨e1, n1⟩ := m1; obtain ⟨e2, n2⟩ := m2
  simp only at h; subst h; rfl

@[simp]
theorem Module.expression_fst' {T U} (m : Module (.prod T U)) :
    m.fst'.expression = reduce m.expression.fst := rfl

@[simp]
theorem Module.expression_snd' {T U} (m : Module (.prod T U)) :
    m.snd'.expression = reduce m.expression.snd := rfl


@[simp]
theorem Module.toModule_expression {T} (m : ModuleExpression .empty T) :
    (ModuleExpression.toModule m).expression = reduce m := rfl

@[simp]
theorem Module.reduce_expression {T} (m : Module T) : reduce m.expression = m.expression := by
  obtain ⟨expression, normal⟩ := m
  simp only
  unfold reduce
  exact dif_pos normal.normal

@[simp]
theorem Module.fst_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).fst' = m1 := by
  ext
  simp [Module.fst', Module.pair', reduce_pair]


@[simp]
theorem Module.snd_pair' {T U} (m1 : Module T) (m2 : Module U) :
    (m1.pair' m2).snd' = m2 := by
  ext
  simp [Module.snd', Module.pair', reduce_pair]


theorem Module.pair_fst_snd' : (Module.fst' m).pair' (Module.snd' m) = m := by
  ext
  -- a closed normal term of product type is a pair `a, b` with `a`, `b` normal
  obtain ⟨a, b, he⟩ := pair_type_is_pair m.normal
  have hn := m.normal
  rw [he] at hn
  cases hn with
  | pair hna hnb =>
      have ha : reduce a = a := Module.reduce_expression ⟨a, hna⟩
      have hb : reduce b = b := Module.reduce_expression ⟨b, hnb⟩
      simp only [Module.fst', Module.snd', Module.pair', Module.toModule_expression, he,
        reduce_fst, reduce_snd, reduce_pair, ha, hb]


abbrev Module.Unit := Module .unit
def Module.unit : Module .unit := ModuleExpression.unit.toModule

class IsModule (T : Type _) where
  moduleTypeRep : ModuleTypeRep
  isModule : T = Module moduleTypeRep := by rfl

@[reducible]
instance : IsModule (Module t) where
  moduleTypeRep := t
  isModule := rfl

def Module.moduleTypeRep (T : Type _) [inst : IsModule T] := inst.moduleTypeRep

def Module.cast (T : Type _) [inst : IsModule T] (m : T) : Module (Module.moduleTypeRep T) :=
  inst.isModule ▸ m

def Module.cast' (T : Type _) [inst : IsModule T] (m : Module (Module.moduleTypeRep T)) : T :=
  inst.isModule.symm ▸ m

def Module.Arr (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Arr M N) where
  moduleTypeRep := ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

def Module.Proc (sig : ProcedureSignature) : Type _ :=
  Module (ModuleTypeRep.proc sig)

instance {sig} : IsModule (Module.Proc sig) where
  moduleTypeRep := ModuleTypeRep.proc sig

def Module.app' (m : Module (.arr A B)) (m' : Module A) :=
  (m.expression.app m'.expression).toModule

def Module.app {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N] (m : Module.Arr M N) (m' : M) : N :=
  have hMN : Module.Arr M N = Module (ModuleTypeRep.arr (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Arr]
  iN.isModule.symm ▸ Module.app' (hMN ▸ m) (iM.isModule ▸ m')

theorem Module.cast_app [IsModule M] [IsModule N] (a : Module.Arr M N) (b : M) :
    Module.cast _ (Module.app a b)
      = Module.app' (Module.cast (Module.Arr M N) a) (Module.cast M b) := by
  unfold Module.cast Module.app
  simp only [eqRec_eq_cast, cast_cast, cast_eq]
  rfl

def Module.Prod (M : Type _) (N : Type _) [IsModule M] [IsModule N] : Type _ :=
  Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N))

instance (M : Type _) (N : Type _) [IsModule M] [IsModule N] : IsModule (Module.Prod M N) where
  moduleTypeRep := ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)
  isModule := rfl

def Module.fst {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N] (m : Module.Prod M N) : M :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iM.isModule.symm ▸ Module.fst' (hMN ▸ m)

def Module.snd {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N] (m : Module.Prod M N) : N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  iN.isModule.symm ▸ Module.snd' (hMN ▸ m)

def Module.pair {M N : Type max 1 u} [iM : IsModule M] [iN : IsModule N] (m1 : M) (m2 : N) :
    Module.Prod M N :=
  have hMN : Module.Prod M N
      = Module (ModuleTypeRep.prod (Module.moduleTypeRep M) (Module.moduleTypeRep N)) := by
    simp [Module.Prod]
  hMN ▸ Module.pair' (iM.isModule ▸ m1) (iN.isModule ▸ m2)

@[simp]
theorem Module.fst_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.fst (Module.pair m1 m2) = m1 := by
  simp only [Module.fst, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.fst_pair']

@[simp]
theorem Module.snd_pair {M N : Type max 1 u} [IsModule M] [IsModule N] (m1 : M) (m2 : N) :
    Module.snd (Module.pair m1 m2) = m2 := by
  simp only [Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast, cast_eq,
    Module.snd_pair']

theorem Module.pair_fst_snd {M N : Type max 1 u} [IsModule M] [IsModule N] (m : Module.Prod M N) :
    Module.pair (Module.fst m) (Module.snd m) = m := by
  simp only [Module.fst, Module.snd, Module.pair, Module.moduleTypeRep, eqRec_eq_cast, cast_cast,
    cast_eq, Module.pair_fst_snd']

/- # Demo -/



section Demo

axiom sig : ProcedureSignature
def TestModule := Module (ModuleTypeRep.prod (ModuleTypeRep.proc sig) (ModuleTypeRep.proc sig))

noncomputable
def TestModule.main (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.fst'
noncomputable
def TestModule.aux (m : TestModule) : Module (ModuleTypeRep.proc sig) := m.snd'

structure TestModuleStruct where
  main : Module (ModuleTypeRep.proc sig)
  aux : Module (ModuleTypeRep.proc sig)

noncomputable
def TestModuleStruct.destruct (str : TestModuleStruct) : TestModule :=
  str.main.pair' str.aux

noncomputable
def TestModule.mk (str : TestModuleStruct) : TestModule := str.main.pair' str.aux

axiom testMain : Module (ModuleTypeRep.proc sig)
axiom testAux : Module (ModuleTypeRep.proc sig)

noncomputable
def myMod := TestModule.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModule.main, myMod, TestModule.mk]


end Demo

end GaudisCrypt.TypedModules

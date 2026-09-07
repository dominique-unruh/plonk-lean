import Lean
import Lean.Elab.Term
import Mathlib.Data.Fintype.Basic
import GaudisCrypt.Language.Semantics
import GaudisCrypt.Language.Footprint

namespace GaudisCrypt

open GaudisCrypt
open GaudisCrypt

class ProgramSpec : Type _ where
  state : Type u

def State [spec : ProgramSpec] := spec.state


variable [ProgramSpec]

/-- The state a statement runs in: the `global` program state together with the
`local` state `l` (procedure parameters + local variables).  Replaces the former
`State × l` product so that the two halves are named. -/
structure ProcedureState (l : Type) where
  global : State
  -- Rename → scoped
  locals : l

/-- Lens onto the global part of a `ProcedureState`. -/
def ProcedureState.globalL {l : Type} : Lens State (ProcedureState l) where
  get s := s.global
  set v s := { s with global := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local part of a `ProcedureState`. -/
-- TODO: rename to .scopedL
def ProcedureState.localL {l : Type} : Lens l (ProcedureState l) where
  get s := s.locals
  set v s := { s with locals := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

def VariableName := String

structure ProcedureSignature where
  params : List Type
  ret : Type

-- TODO is this used?
class LocalState : Type _ where
  params : List Type
  locals : List Type

-- TODO: rename -> typeListToTuple
/-- Reducible on purpose: at a concrete parameter list the tuple type has to be visible to
unification at `reducible` transparency, or everything stated about `_ × _` gets stuck on it —
typeclass resolution (`OfNat (paramListToTuple [Nat]) 5` for a numeral argument of a `call`,
`disjoint` of two projection lenses) is where it shows. -/
@[reducible] def paramListToTuple : List Type → Type
  | []      => Unit
  | [x]     => x
  | x :: xs => x × paramListToTuple xs

/-- The local state of a procedure: parameter values (`params`) and local-variable
values (`vars`).  Indexed by the parameter *types* and the local declarations only
(not the return type), so it can be formed before the return type is known — this is
what lets a `proc` with an omitted return type elaborate. -/
-- TODO: Rename LocalVariableState to ProcedureScope
structure LocalVariableState (paramTypes : List Type)
    (locals : List (Σ t : Type, Inhabited t)) where
  params : paramListToTuple paramTypes
  -- TODO: rename vars to localVars
  vars : paramListToTuple (locals.map (·.fst))

/-- The local state for a full signature (delegates to `LocalVariableState`; reducible
so `sig.LocalVariableState locals` is defeq to `LocalVariableState sig.params locals`). -/
@[reducible] def ProcedureSignature.LocalVariableState (sig : ProcedureSignature)
    (locals : List (Σ t : Type, Inhabited t)) : Type :=
  _root_.GaudisCrypt.LocalVariableState sig.params locals

/-- Lens onto the parameter tuple of a `LocalVariableState`. -/
def LocalVariableState.paramsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (paramListToTuple paramTypes) (LocalVariableState paramTypes locals) where
  get s := s.params
  set v s := { s with params := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lens onto the local-variable tuple of a `LocalVariableState`. -/
-- TODO Rename to .localVarsL
def LocalVariableState.varsL {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} :
    Lens (paramListToTuple (locals.map (·.fst))) (LocalVariableState paramTypes locals) where
  get s := s.vars
  set v s := { s with vars := v }
  set_get _ _ := rfl
  set_set _ _ _ := rfl
  get_set _ := rfl

/-- Lift a lens into the parameter tuple to a lens into the full procedure state
(`localL ∘ paramsL`).  Analogous to `Lens.ofst`.  (Defined in the `Lens` namespace via
`_root_` so dot notation `lens.intoParams` resolves.) -/
def Lens.intoParams {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)} (lens : Lens a (paramListToTuple paramTypes)) :
    Lens a (ProcedureState (LocalVariableState paramTypes locals)) :=
  ProcedureState.localL.chain (LocalVariableState.paramsL.chain lens)

/-- Lift a lens into the local-variable tuple to a lens into the full procedure state
(`localL ∘ varsL`).  Analogous to `Lens.ofst`. -/
-- TODO: rename → intoLocalVars
def Lens.intoVars {a : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    (lens : Lens a (paramListToTuple (locals.map (·.fst)))) :
    Lens a (ProcedureState (LocalVariableState paramTypes locals)) :=
  ProcedureState.localL.chain (LocalVariableState.varsL.chain lens)

/-- Local program variables are `Lens.intoVars` of their slot projections; distinct slots
    are disjoint, and `intoVars` (two `chain` layers) preserves that. -/
instance Programs.disjoint_intoVars {a b : Type} {paramTypes : List Type}
    {locals : List (Σ t : Type, Inhabited t)}
    {x : Lens a (paramListToTuple (locals.map (·.fst)))}
    {y : Lens b (paramListToTuple (locals.map (·.fst)))} [disjoint x y] :
    disjoint (Lens.intoVars (paramTypes := paramTypes) x) y.intoVars :=
  Lens.disjoint_chain ProcedureState.localL _ _

def ProcedureSignature.ParamType (sig : ProcedureSignature) := paramListToTuple sig.params

private def localDefaults : (ls : List (Σ t : Type, Inhabited t)) → paramListToTuple (ls.map (·.fst))
  | [] => ()
  | [⟨_, inst⟩] => inst.default
  | ⟨_, inst⟩ :: h :: t => (inst.default, localDefaults (h :: t))

def ProcedureSignature.localVariableInit
    (sig : ProcedureSignature) (locals : List (Σ t : Type, Inhabited t))
    (params : paramListToTuple sig.params) : sig.LocalVariableState locals :=
  ⟨params, localDefaults locals⟩

/-- A sequences of procedure signatures, intended to be used to describe the type
    of holes in a program -/
inductive HoleSigs where
  | empty  : HoleSigs
  | append : HoleSigs → ProcedureSignature → HoleSigs

def HoleSigs.length : HoleSigs → Nat
  | .empty => 0
  | .append h _ => h.length.succ

def HoleSigs.NonEmpty : HoleSigs → Prop
| .empty => False
| _ => True

def HoleSigs.toList : HoleSigs → List ProcedureSignature
  | .empty => []
  | .append h sig => HoleSigs.toList h ++ [sig]

inductive HoleIndex : HoleSigs → ProcedureSignature → Type _ where
  | zero {a} {Γ : HoleSigs} : HoleIndex (Γ.append a) a
  | succ {a b} : HoleIndex Γ a → HoleIndex (Γ.append b) a
  deriving DecidableEq

def HoleIndex.toFin {holes sig} : HoleIndex holes sig → Fin holes.length
  | .zero =>
      ⟨0, by simp [HoleSigs.length]⟩
  | .succ i =>
      let j : Fin _ := HoleIndex.toFin (holes := _) (sig := _) i
      ⟨j.val.succ, Nat.succ_lt_succ j.isLt⟩

theorem HoleIndex.toFin_inj {holes sig} :
    ∀ (i1 i2 : HoleIndex holes sig), i1.toFin = i2.toFin → i1 = i2
  | .zero,    .zero,    _ => rfl
  | .zero,    .succ i2, h => by
      have : (0 : Nat) = Nat.succ (i2.toFin.val) := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      exact (Nat.succ_ne_zero _ this.symm).elim
  | .succ i1, .zero,    h => by
      have : Nat.succ (i1.toFin.val) = 0 := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      exact (Nat.succ_ne_zero _ this).elim
  | .succ i1, .succ i2, h => by
      have hv : Nat.succ (i1.toFin.val) = Nat.succ (i2.toFin.val) := by
        simpa [HoleIndex.toFin] using congrArg Fin.val h
      have hv' : i1.toFin.val = i2.toFin.val := Nat.succ.inj hv
      have ht : i1.toFin = i2.toFin := Fin.ext hv'
      exact congrArg HoleIndex.succ (HoleIndex.toFin_inj i1 i2 ht)

noncomputable instance {holes sig} : Fintype (HoleIndex holes sig) := by
  refine Fintype.ofInjective (HoleIndex.toFin (holes := holes) (sig := sig))
    (by
      intro i1 i2 h
      exact HoleIndex.toFin_inj (holes := holes) (sig := sig) i1 i2 h)

abbrev Var [ProgramSpec] a := Lens a State
abbrev Expr [ProgramSpec] a := Getter a State

/-- Syntactic program (with arbitrary Lean terms as expressions) -/
inductive StmtWithHoles [ProgramSpec]: HoleSigs → Type → Type _ where
  | skip : StmtWithHoles h l
  -- | assign {a : Type} : Lens a (ProcedureState l) → Getter a (ProcedureState l) → StmtWithHoles h l
  | sample {a : Type} : Setter a (ProcedureState l) → Getter (SubProbability a) (ProcedureState l) → StmtWithHoles h l
  | call' {sig : ProcedureSignature} :
      -- We have to spell out all parts of the procedure, unfortunately
      -- (Lean forbids the mutual induction with `Procedure`)
      Setter sig.ret (ProcedureState l) → (locals : List (Σ t : Type, Inhabited t))
        → StmtWithHoles .empty (sig.LocalVariableState locals)
        → Getter sig.ret (ProcedureState (sig.LocalVariableState locals))
        → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | hole {sig} (n: HoleIndex h sig) : Setter sig.ret (ProcedureState l) → Getter sig.ParamType (ProcedureState l) → StmtWithHoles h l
  | seq : StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l                   -- c1; c2
  | ifThenElse : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l → StmtWithHoles h l
  | while : Getter Bool (ProcedureState l) → StmtWithHoles h l → StmtWithHoles h l          -- while b do c

def Stmt [ProgramSpec] := StmtWithHoles .empty

structure ProcedureWithHoles [ProgramSpec] (holeSigs : HoleSigs) (sig : ProcedureSignature) where
  locals : List (Σ t : Type, Inhabited t)
  body : StmtWithHoles holeSigs (sig.LocalVariableState locals)
  return_val : Getter sig.ret (ProcedureState (sig.LocalVariableState locals))

def Procedure [ProgramSpec] sig := ProcedureWithHoles .empty sig

/-- The signature of a procedure-with-holes as a *term* — `sig` is otherwise only reachable as
an implicit argument of the type, which makes it awkward to name in generated code. -/
abbrev ProcedureWithHoles.signature [ProgramSpec] {holes sig}
    (_p : ProcedureWithHoles holes sig) : ProcedureSignature := sig

@[match_pattern]
def StmtWithHoles.call [ProgramSpec] {sig} (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
      (params : Getter sig.ParamType (ProcedureState l)) : StmtWithHoles h l :=
  StmtWithHoles.call' x proc.locals proc.body proc.return_val params

noncomputable
def StmtWithHoles.assign [ProgramSpec]
  (x : Setter a (ProcedureState l)) (e : Getter a (ProcedureState l)) : StmtWithHoles h l :=
  StmtWithHoles.sample x ⟨fun st => pure (e.get st)⟩

def Stmt.call [ProgramSpec] {sig} (x : Setter sig.ret (ProcedureState l)) (proc : Procedure sig)
      (params : Getter sig.ParamType (ProcedureState l)) : Stmt l
     := StmtWithHoles.call x proc params

def HoleSigs.Instantiation (holes : HoleSigs) := ∀ {sig}, HoleIndex holes sig → Procedure sig

/-- The only instantiation of no holes at all. -/
def HoleSigs.Instantiation.nil : HoleSigs.empty.Instantiation := fun {_} idx => nomatch idx

/-- Extend an instantiation by one more procedure, for one more (last-appended) hole.  Written in
the order the holes were appended, `nil.push p₀ |>.push p₁ …`, this is how an instantiation is
built up from concrete procedures — note `HoleIndex.zero` is the *last* one pushed. -/
def HoleSigs.Instantiation.push {holes : HoleSigs} {sig : ProcedureSignature}
    (inst : holes.Instantiation) (p : Procedure sig) : (holes.append sig).Instantiation :=
  fun {_} idx => match idx with
    | .zero => p
    | .succ i => inst i

/-- Looking up the hole a `push` was made for. -/
@[simp] theorem HoleSigs.Instantiation.push_zero {holes : HoleSigs} {sig : ProcedureSignature}
    (inst : holes.Instantiation) (p : Procedure sig) :
    HoleSigs.Instantiation.push inst p HoleIndex.zero = p := rfl

/-- Looking up any other hole of a `push` falls through to the instantiation it extends. -/
@[simp] theorem HoleSigs.Instantiation.push_succ {holes : HoleSigs} {sig sig' : ProcedureSignature}
    (inst : holes.Instantiation) (p : Procedure sig) (i : HoleIndex holes sig') :
    HoleSigs.Instantiation.push inst p (HoleIndex.succ i) = inst i := rfl

/-- Convert an instantiation into a plain list of procedures (tagged by their signature),
in the same right-nested order as `HoleSigs.Instantiation.toModuleTuple`.

The head of the list corresponds to the most-recently appended hole signature. -/
def HoleSigs.Instantiation.toList : {holes : HoleSigs} → holes.Instantiation → List (Σ sig, Procedure sig)
  | .empty,       _    => []
  | .append _ sig, inst =>
      ⟨sig, inst .zero⟩ ::
        HoleSigs.Instantiation.toList (holes := _)
          (fun {sig'} idx => inst (.succ idx))

/-- Instantiate all holes in a statement using `resolve`, turning each `.hole` into a
    `.call'` of the resolved procedure.  Hole-free constructors are simply re-typed. -/
def StmtWithHoles.instantiate {holes : HoleSigs} {l : Type}
    (stmt : StmtWithHoles holes l)
    (instantiation : holes.Instantiation) :
    Stmt l := match stmt with
  | .skip            => .skip
  -- | .assign x e      => .assign x e
  | .sample x e      => .sample x e
  | .call' x ls b r p => .call' x ls b r p
  | .hole n x p      => StmtWithHoles.call x (instantiation n) p
  | .seq s1 s2       =>
      .seq (s1.instantiate instantiation) (s2.instantiate instantiation)
  | .ifThenElse c t e =>
      .ifThenElse c (StmtWithHoles.instantiate t instantiation)
                    (StmtWithHoles.instantiate e instantiation)
  | .while c t       => .while c (StmtWithHoles.instantiate t instantiation)

def ProcedureWithHoles.instantiate {holes : HoleSigs} {sig}
    (proc : ProcedureWithHoles holes sig)
    (instantiation : holes.Instantiation)
     : Procedure sig :=
  ⟨proc.locals, StmtWithHoles.instantiate proc.body instantiation, proc.return_val⟩


/-- A structural size measure used to justify termination of `programDenotation`.
    The auto-generated `sizeOf` for `StmtWithHoles` is trivially `0` (the inductive
    lives in a higher universe because its constructors quantify over `a : Type`), so
    we define our own. -/
def StmtWithHoles.depth {h l} : StmtWithHoles h l → Nat
  | .skip           => 0
  | .sample _ _     => 0
  | .hole _ _ _     => 0
  | .call' _ _ body _ _ => body.depth + 1
  | .seq p q        => max p.depth q.depth + 1
  | .ifThenElse _ p q => max p.depth q.depth + 1
  | .while _ p      => p.depth + 1

/-- A hole-free statement has nothing to instantiate: every constructor is re-typed as itself, and
the `.hole` case cannot occur (`HoleIndex .empty _` is empty).  Recursion is on `depth` — the
statement's own index `HoleSigs.empty` is not a variable, so the equation compiler cannot recurse
on it structurally. -/
theorem StmtWithHoles.instantiate_empty {l : Type} (inst : HoleSigs.empty.Instantiation) :
    ∀ s : Stmt l, s.instantiate inst = s
  | .skip => rfl
  | .sample _ _ => rfl
  | .call' _ _ _ _ _ => rfl
  | .seq s1 s2 => by
      simp only [StmtWithHoles.instantiate, instantiate_empty inst s1, instantiate_empty inst s2]
  | .ifThenElse _ s1 s2 => by
      simp only [StmtWithHoles.instantiate, instantiate_empty inst s1, instantiate_empty inst s2]
  | .while _ s => by simp only [StmtWithHoles.instantiate, instantiate_empty inst s]
termination_by s => s.depth
decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-- Instantiating a procedure that has no holes leaves it alone. -/
@[simp] theorem ProcedureWithHoles.instantiate_empty {sig} (p : ProcedureWithHoles .empty sig)
    (inst : HoleSigs.empty.Instantiation) : p.instantiate inst = p := by
  obtain ⟨locals, body, ret⟩ := p
  simp only [ProcedureWithHoles.instantiate, StmtWithHoles.instantiate_empty]

mutual
noncomputable
def programDenotation : Stmt l → ProgramDenotation (ProcedureState l) Unit
| .skip => ProgramDenotation.skip
-- | .assign x e => do let v <- ProgramDenotation.get e; ProgramDenotation.set x v
| .sample x e => do let μ : SubProbability _ <- ProgramDenotation.get e; let v <-
    μ.toProgramDenotation; ProgramDenotation.set x v
| .seq p q => do let _ <- programDenotation p; programDenotation q
| .ifThenElse c p q => do if ← ProgramDenotation.get c then programDenotation p else
    programDenotation q
| .while c p => while_loop (ProgramDenotation.get c) (programDenotation p)
| .call' (sig:=sig) (x : Setter sig.ret _) locals body ret args => do
    let proc : Procedure sig := ⟨locals, body, ret⟩
    let argValues <- ProgramDenotation.get args
    let retVal <- ProgramDenotation.zoom ProcedureState.globalL (procedureDenotation proc argValues)
    ProgramDenotation.set x retVal
termination_by stmt => (stmt.depth, 0)
decreasing_by all_goals simp [StmtWithHoles.depth, Prod.lex_def]

noncomputable
def procedureDenotation {sig} (proc : Procedure sig) (args : sig.ParamType) :
   ProgramDenotation State sig.ret := fun st => do
    let procLocalSt := sig.localVariableInit proc.locals args
    let (_, procFinalSt) <-
      programDenotation (l := sig.LocalVariableState proc.locals) proc.body ⟨st, procLocalSt⟩
    let retVal := proc.return_val.get procFinalSt
    return (retVal, procFinalSt.global)
termination_by (proc.body.depth, 1)
decreasing_by simp [Prod.lex_def]

end
/-- The procedure denotation as an explicit wrapper: initialise locals, run the
    body, extract `(return_val, global)`. -/
noncomputable def procWrap {sig : ProcedureSignature} {L : Type}
    (rv : Getter sig.ret (ProcedureState L)) (initL : L)
    (B : ProgramDenotation (ProcedureState L) Unit) : ProgramDenotation State sig.ret :=
  fun st => B ⟨st, initL⟩ >>= fun p => pure (rv.get p.2, p.2.global)

/-- `procedureDenotation` of an instantiated procedure is `procWrap` of its body
    (generic over the holes and their instantiation). -/
theorem procedureDenotation_eq_procWrap_gen {holes : HoleSigs} {sig : ProcedureSignature}
    (A : ProcedureWithHoles holes sig) (args : sig.ParamType) (inst : holes.Instantiation) :
    procedureDenotation (A.instantiate inst) args
      = procWrap A.return_val (sig.localVariableInit A.locals args)
          (programDenotation (A.body.instantiate inst)) := by
  funext st; simp only [procedureDenotation, ProcedureWithHoles.instantiate, procWrap]


end GaudisCrypt

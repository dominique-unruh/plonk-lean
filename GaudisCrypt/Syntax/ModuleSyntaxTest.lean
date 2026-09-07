import GaudisCrypt.Syntax.ModuleSyntax

/-! # Tests for `ModuleSyntax` -/

open GaudisCrypt

namespace Experiment
variable [ProgramSpec]

/-

Define a toplevel command `moduletype` that would transform something like the following
to the sequence of commands given below between START and END. Of course, this should not be restricted to allowing only two fields (main, aux)
but an arbitrary number.


moduletype TestModuleTypeRep {
  main : Module (ModuleTypeRep.proc (procsig (String,Nat) -> Bool));
  module aux : Module (ModuleTypeRep.proc (procsig (Nat) -> String)) (ModuleTypeRep.unit));
}

-/

moduletype TestModule {
  -- module main : ModuleTypeRep.proc (procsig (String, Nat) -> Bool);
  proc main (String, Nat) -> Bool;
  module aux : .arr (.proc (procsig (Nat) -> String)) .unit;
}
#check TestModule.mk

/- With a *single* field the accessor is the identity and its `accessorModule` is `.abs (.var 0)` —
the one case where `accessor_apply` has nothing left to normalise after the first `simp only`, which
is why its trailing steps are `try`s. -/
moduletype OneField {
  proc only (Nat) -> Bool;
}
#check OneField.only.utilities.apply_simp
#check OneField.only.utilities.expression_eq

/- ### `ModuleTypeRep` concrete syntax (`.proc`, `.arr`, `.prod`, `.unit`)

`ModuleTypeRep`'s constructors are written by dot notation wherever the expected type says so.
`procmod (…) -> R` is *not* one of them — it is the module **type** `Module.Proc (procsig (…) -> R)`
(see below), as `→ₘ`/`×ₘ` are `Module.Arr`/`Module.Prod` rather than `.arr`/`.prod`. -/

example : (.proc (procsig (Nat) -> String) : ModuleTypeRep)
    = ModuleTypeRep.proc (ProcedureSignature.mk [Nat] String) := rfl

example : (.arr (.proc (procsig (Nat) -> String)) .unit : ModuleTypeRep)
    = ModuleTypeRep.arr (ModuleTypeRep.proc (procsig (Nat) -> String)) ModuleTypeRep.unit := rfl

example : (.prod (.proc (procsig () -> Bool)) .unit : ModuleTypeRep)
    = ModuleTypeRep.prod (ModuleTypeRep.proc (procsig () -> Bool)) ModuleTypeRep.unit := rfl

-- `procsig` and the `moduletype` proc-field accept the `→` arrow spelling too
example : (procsig (Nat) → String) = procsig (Nat) -> String := rfl

moduletype UnicodeArrowField {
  proc f (Nat) → Bool;
  module g : .arr (.proc (procsig (Bool) → Nat)) .unit;
}

-- prints back in the concrete form
#check (.arr (.proc (procsig (Nat) -> String)) .unit : ModuleTypeRep)
#check (.arr (.prod .unit .unit) .unit : ModuleTypeRep)

/- ### Module-type concrete syntax (`→ₘ` = `Module.Arr`, `×ₘ` = `Module.Prod`) -/

example : (TestModule →ₘ TestModule ×ₘ TestModule) = Module.Arr TestModule
    (Module.Prod TestModule TestModule) := rfl

-- `×ₘ` binds tighter than `→ₘ`, and `→ₘ` is right-associative
example : (TestModule ×ₘ TestModule →ₘ TestModule →ₘ TestModule)
    = Module.Arr (Module.Prod TestModule TestModule) (Module.Arr TestModule TestModule) := rfl

-- `procmod (…) -> R` is the module type of a procedure, i.e. `Module.Proc (procsig (…) -> R)` —
-- so it composes with `→ₘ`/`×ₘ` (its return type binds tighter than a trailing operator)
example : (procmod (Nat) -> String) = Module.Proc (procsig (Nat) -> String) := rfl
example : (procmod (Nat) → String) = procmod (Nat) -> String := rfl
example : (TestModule →ₘ procmod (Nat) -> String)
    = Module.Arr TestModule (Module.Proc (procsig (Nat) -> String)) := rfl

axiom testMain : procmod (String, Nat) -> Bool
axiom testAux : Module (.arr (.proc (procsig (Nat) -> String)) .unit)

noncomputable
def myMod := TestModule.mk {main := testMain, aux := testAux}

theorem test : myMod.main = testMain := by
  simp [TestModule.main, myMod]

moduletype M2 {
  proc g() -> Unit;
  proc h() -> Unit;
}


/- ### `module` declarations -/

module X using (A : Module.Arr TestModule (procmod () → Unit), B : TestModule) : M2 {
  proc g() : Unit {
    _ <- call (Module.app A myMod) ();
    _ <- call (Module.app A myMod) ();   -- same callee ⇒ same hole
    _ <- call (myMod.main)  ("hello", 5);
    return ();
  };
  proc h() : Unit {
    return ();
  };
}

-- `g` calls the parameter `A` (⇒ one hole) and the closed module `myMod.main` (⇒ a plain call)
#check (X.g.procedure : proctype () -> Unit uses (() → Unit))
#check (X.h.procedure : proctype () -> Unit)
#print X.g.procedure
#print X
#print X.g

-- `g` uses `A` but not `B`, so `X.g` abstracts over `A` alone; `h` uses no parameter at all
#check (X.g : Module.Arr (Module.Arr TestModule (procmod () → Unit))
                (Module.Proc (procsig () -> Unit)))
#check (X.h : Module.Proc (procsig () -> Unit))
#print X.g
#print X

-- two parameters, two holes; `B.main` reaches the parameter through a `moduletype` accessor
module Y using (A : Module.Arr TestModule (procmod () → Unit), B : TestModule) : M2 {
  proc g() : Unit {
    _ <- call (B.main) ("hi", (3 : Nat));
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Unit { return (); };
}
#check (Y.g.procedure : proctype () -> Unit uses ((String, Nat) → Bool, () → Unit))
#check (Y.g : Module.Arr (Module.Arr TestModule (procmod () → Unit))
                (Module.Arr TestModule (Module.Proc (procsig () -> Unit))))
-- and it applies to modules of those types, in that order
#check fun (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) =>
  (Module.app (Module.app Y.g a) b : Module.Proc (procsig () -> Unit))

-- `X` itself takes *all* the parameters — `B` too, which only `Y` uses — as one tuple
#check (X : Module.Arr (Module.Prod (Module.Arr TestModule (procmod () → Unit)) TestModule)
             M2)
#check (Y : Module.Arr (Module.Prod (Module.Arr TestModule (procmod () → Unit)) TestModule)
             M2)
#print X
-- it applies to a tuple of them, and the fields are then projected out with the `M2` accessors
#check fun (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) =>
  (M2.g (Module.app X (Module.pair a b)) : Module.Proc (procsig () -> Unit))

-- `X.apply_simp` does that application: each field gets the parameters *it* uses (`g` gets `A`
-- alone, `h` none), so a projection out of an applied module reduces to an applied procedure
#print X.apply_simp
#print Y.apply_simp
example (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) :
    M2.g (Module.app X (Module.pair a b))
      = (Module.app X.g a : Module.Proc (procsig () -> Unit)) := by
  simp only [M2.g, M2.mk, X.apply_simp, Module.fst_pair']
example (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) :
    M2.h (Module.app X (Module.pair a b)) = (X.h : Module.Proc (procsig () -> Unit)) := by
  simp [M2.h, M2.mk]

-- `X.g.apply_simp` carries the application on down to a procedure: `X.g` applied to `A` is
-- `X.g.procedure` with its one hole filled by the callee that hole was made from
#check (X.g.apply_simp :
  ∀ (A : Module.Arr TestModule (procmod () → Unit)),
    Module.app X.g A
      = Module.proc (X.g.procedure.instantiate
          (HoleSigs.Instantiation.push HoleSigs.Instantiation.nil
            (Module.Proc.procedure (Module.app A myMod)))))

-- `h` has no hole to fill — and hence no parameter to take: it *is* its procedure
#check (X.h.apply_simp : X.h = Module.proc X.h.procedure)

-- two holes, pushed in declaration order: the last-declared one is the outermost push, which is
-- what `HoleIndex.zero` picks out
#check (Y.g.apply_simp :
  ∀ (A : Module.Arr TestModule (procmod () → Unit)) (B : TestModule),
    Module.app (Module.app Y.g A) B
      = Module.proc (Y.g.procedure.instantiate
          (HoleSigs.Instantiation.push
            (HoleSigs.Instantiation.push HoleSigs.Instantiation.nil (Module.Proc.procedure B.main))
            (Module.Proc.procedure (Module.app A myMod)))))

-- the two lemmas chain: projecting a field out of an applied `X` gets all the way to the procedure
example (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) :
    M2.g (Module.app X (Module.pair a b))
      = Module.proc (X.g.procedure.instantiate
          (HoleSigs.Instantiation.push HoleSigs.Instantiation.nil
            (Module.Proc.procedure (Module.app a myMod)))) := by
  simp [M2.g, M2.mk]

-- `X.g.procedure.apply_simp` takes the last step, from the `instantiate` to a hole-free procedure:
-- the body as declared, with the hole calls turned back into ordinary calls of `args <index>`
#check (X.g.procedure.apply_simp :
  ∀ (args : (HoleSigs.empty.append (procsig () → Unit)).Instantiation),
    X.g.procedure.instantiate args
      = proc () : Unit {
          _ <- call (args HoleIndex.zero) ();
          _ <- call (args HoleIndex.zero) ();
          _ <- call (myMod.main.procedure) ("hello", (5 : Nat));
          return ();
        })

-- two holes: the *first*-declared one is the outermost `.succ` (`.zero` is the last)
#check (Y.g.procedure.apply_simp :
  ∀ (args : ((HoleSigs.empty.append (procsig (String, Nat) → Bool)).append
        (procsig () → Unit)).Instantiation),
    Y.g.procedure.instantiate args
      = proc () : Unit {
          _ <- call (args HoleIndex.zero.succ) ("hi", (3 : Nat));
          _ <- call (args HoleIndex.zero) ();
          return ();
        })

-- nothing to fill: the lemma of a hole-free procedure is that procedure, unchanged
#check (X.h.procedure.apply_simp :
  ∀ (args : HoleSigs.empty.Instantiation),
    X.h.procedure.instantiate args = proc () : Unit { return (); })

-- and now all three families chain: a field of an applied `X` all the way to a plain `Procedure`.
-- (`Module.Proc.procedure (Module.app …)` rather than `(Module.app …).procedure`: written prefix,
-- the expected type `Module (.proc _)` reaches `Module.app`'s result type before `a`'s type does,
-- which is how the generated lemmas spell it — the two are defeq but not syntactically equal.)
example (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) :
    M2.g (Module.app X (Module.pair a b))
      = Module.proc (proc () : Unit {
          _ <- call (Module.Proc.procedure (Module.app a myMod)) ();
          _ <- call (Module.Proc.procedure (Module.app a myMod)) ();
          _ <- call (Module.Proc.procedure myMod.main) ("hello", (5 : Nat));
          return ();
        }) := by
  simp [M2.g, M2.mk]

-- TODO: Something like that should be autogenerated by moduletype command!
lemma M2.mk_g : M2.g (M2.mk s) = s.g := by simp [M2.mk, M2.g]
example (a : Module.Arr TestModule (procmod () → Unit)) (b : TestModule) :
    M2.g (Module.app Y (Module.pair a b))
      = (Module.app (Module.app Y.g a) b : Module.Proc (procsig () -> Unit)) := by
      simp only [Y.apply_simp, M2.mk_g]


def M3 := M2

-- the parameter list is optional; without it `X` is the module type itself …
module NoParams : M2 {
  proc g() : Unit { return (); };
  proc h() : Unit { return (); };
}
#check (NoParams.g.procedure : proctype () -> Unit)
#check (NoParams.g : Module.Proc (procsig () -> Unit))
#check (NoParams : M2)
-- (no `NoParams.apply_simp`: with no parameter list there is nothing to apply `NoParams` to)
#check X.apply_simp

-- … whereas an empty one still makes it a function, of the empty tuple
module EmptyParams using () : M2 {
  proc g() : Unit { return (); };
  proc h() : Unit { return (); };
}
#check EmptyParams.apply_simp
#check (EmptyParams : Module.Arr Module.Unit M2)

-- the module type is optional too; without it `X` gets the anonymous record of its procedures
module NoType using (A : Module.Arr TestModule (procmod () → Unit)) {
  proc g() : Unit {
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Bool { return true; };
}
#check (NoType : Module.Arr (Module.Arr TestModule (procmod () → Unit))
                   (Module.Prod (Module.Proc (procsig () -> Unit))
                                (Module.Proc (procsig () -> Bool))))
-- and `apply_simp` then builds that record with `Module.pair`, there being no `N.mk` to build it
#print NoType.apply_simp
example (a : Module.Arr TestModule (procmod () → Unit)) :
    Module.fst (Module.app NoType a) = (Module.app NoType.g a : Module.Proc (procsig () -> Unit)) :=
  by simp

-- three parameters, so `apply_simp`'s proof has to get through the deeper projections
-- `fst (snd t)` and `snd (snd t)` — and `g` takes two of them, in declaration order
module Deep using (A : Module.Arr TestModule (procmod () → Unit), B : TestModule,
                   C : Module.Arr TestModule (procmod () → Unit)) : M2 {
  proc g() : Unit {
    _ <- call (Module.app C myMod) ();
    _ <- call (Module.app A myMod) ();
    return ();
  };
  proc h() : Unit {
    _ <- call (B.main) ("hi", (3 : Nat));
    return ();
  };
}
#check (Deep.apply_simp :
  ∀ (A : Module.Arr TestModule (procmod () → Unit)) (B : TestModule)
    (C : Module.Arr TestModule (procmod () → Unit)),
  Module.app Deep (Module.pair A (Module.pair B C))
    = M2.mk { g := Module.app (Module.app Deep.g A) C, h := Module.app Deep.h B })

-- `g` takes two of the three parameters, so its `apply_simp` binds those two — and has to β-reduce
-- twice, with the argument of the first β sitting under the second binder in between
#check (Deep.g.apply_simp :
  ∀ (A : Module.Arr TestModule (procmod () → Unit))
    (C : Module.Arr TestModule (procmod () → Unit)),
    Module.app (Module.app Deep.g A) C
      = Module.proc (Deep.g.procedure.instantiate
          (HoleSigs.Instantiation.push
            (HoleSigs.Instantiation.push HoleSigs.Instantiation.nil
              (Module.Proc.procedure (Module.app C myMod)))
            (Module.Proc.procedure (Module.app A myMod)))))

-- one `using` binder may name several parameters of the same module type, exactly as writing
-- them out one by one does
module SharedType using (A B : TestModule) : M2 {
  proc g() : Unit {
    _ <- call (A.main) ("hi", (3 : Nat));
    _ <- call (B.main) ("ho", (4 : Nat));
    return ();
  };
  proc h() : Unit { return (); };
}
#check (SharedType : Module.Arr (Module.Prod TestModule TestModule) M2)
#check (SharedType.g :
  Module.Arr TestModule (Module.Arr TestModule (Module.Proc (procsig () -> Unit))))

module NoTypeNoParams {
  proc g() : Unit { return (); };
}
-- a one-procedure record is that procedure (`moduletype` nests its fields the same way)
#check (NoTypeNoParams : Module.Proc (procsig () -> Unit))


/- ### Lean parameters

Both commands take ordinary Lean binders between the name and the rest of the header.  Every
generated declaration is abstracted over them, and refers to its siblings with them applied. -/

moduletype Sized (n : Nat) {
  proc gen () -> (Fin (n+1));
  proc use (Fin (n+1)) -> Bool;
}

-- `n` reaches the field types, and the generated declarations pass it to one another
#check (Sized.gen : (n : Nat) → Sized n → Module.Proc (procsig () -> (Fin (n+1))))
#check (Sized.mk_destruct :
  ∀ (n : Nat) (s : Sized.Structure n), Sized.structure n (Sized.mk n s) = s)

-- implicit and instance parameters too; `Poly.typeRep` needs `α` passed to it *by name*, since
-- `@` would also expose the auto-included section variable `[ProgramSpec]`
moduletype Poly {α : Type} [Inhabited α] {
  proc gen () -> α;
  proc use (α) -> Bool;
}
#check (Poly.typeRep : {α : Type} → [Inhabited α] → ModuleTypeRep)

-- Lean parameters and module parameters at once: `n` before `using`, `S` after it
module Twice (n : Nat) using (S : Sized n) {
  proc main() : Bool {
    var x : Fin (n+1);
    var b : Bool;
    x <- call S.gen ();
    b <- call S.use ($x);
    return $b
  };
}
#check (Twice : (n : Nat) → Module.Arr (Sized n) (Module.Proc (procsig () -> Bool)))
#check (Twice.main.apply_simp : ∀ (n : Nat) (S : Sized n),
  Module.app (Twice.main n) S = Module.proc ((Twice.main.procedure n).instantiate
    (HoleSigs.Instantiation.push
      (HoleSigs.Instantiation.push HoleSigs.Instantiation.nil
        (Module.Proc.procedure (Sized.gen n S)))
      (Module.Proc.procedure (Sized.use n S)))))

-- Lean parameters with no `using`: the module is a function, but not a module function
module Fixed (k : Nat) {
  proc main(y : Fin (k+1)) : (Fin (k+1)) { return $y };
}
#check (Fixed : (k : Nat) → Module.Proc (procsig (Fin (k+1)) -> (Fin (k+1))))

/- A Lean parameter may be named after one of the binders the commands invent for themselves —
the module an accessor takes, the record `mk` takes, the expression a `proj` takes, a hole
instantiation, the empty parameter tuple.  Those are hygienic, so it cannot capture them; before
they were, a `moduletype Foo (m : Nat)` produced `def Foo.gen (m : Nat) (m : Foo (m := m)) : …`,
whose field type read the module where it wanted the number, and the whole batch failed. -/
moduletype AllTheNames (m : Nat) (s : Nat) (e : Nat) (args : Nat) (t : Nat) {
  proc gen () -> (Fin (m + s + e + args + t + 1));
  proc use (Fin (m + s + e + args + t + 1)) -> Bool;
}
#check (AllTheNames.gen : (m s e args t : Nat) → AllTheNames m s e args t →
  Module.Proc (procsig () -> (Fin (m + s + e + args + t + 1))))

module UsesThemToo (args : Nat) using (S : OneField) {
  proc main() : Bool {
    var b : Bool;
    b <- call S.only (args);
    return $b
  };
}
#check (UsesThemToo : (args : Nat) → Module.Arr OneField (Module.Proc (procsig () -> Bool)))

/- ### Section variables

A Lean parameter may come from a section `variable`, and is then not written on the declaration at
all: one a declaration mentions anywhere — a field type, a procedure body, the type of a module
parameter — becomes a parameter of it, in front of the ones it does write, together with the
instance variables that are about it.  A variable it does not mention stays out, and so does one
whose name it binds itself. -/
section
variable {α : Type} [Inhabited α] (k : Nat) (untouched : Bool)

moduletype Boxed {
  proc gen () -> α;
  proc use (α) -> (Fin (k+1));
}
-- `α` and `k` are mentioned, `[Inhabited α]` comes along with `α`, `untouched` stays out
#check (Boxed.typeRep : {α : Type} → [Inhabited α] → (k : Nat) → ModuleTypeRep)

module Unbox using (S : Boxed (α := α) k) {
  proc main() : (Fin (k+1)) {
    var x : α;
    var i : Fin (k+1);
    x <- call S.gen ();
    i <- call S.use ($x);
    return $i
  };
}
#check (Unbox : {α : Type} → [Inhabited α] → (k : Nat) →
  Module.Arr (Boxed (α := α) k) (Module.Proc (procsig () -> (Fin (k+1)))))

-- a written binder wins over the section variable of the same name: one `k`, not two
moduletype Shadow (k : Nat) {
  proc gen () -> (Fin (k+1));
  proc use (Fin (k+1)) -> Bool;
}
#check (Shadow.typeRep : (k : Nat) → ModuleTypeRep)

end

/- ### A parameterised `moduletype` as a declared type

`module X … : T` builds the record of its procedures with `T.mk { f₁ := …, … }` when `T` is a
`moduletype` with exactly these fields, and with an anonymous nest of `Module.pair`s otherwise
(`moduletypeMk?`).  A parameterised `T` is written applied — `: (Sized n)` — and its constructor
takes the same arguments, `Sized.mk n`, the command having given `T` and `T.mk` the same binders. -/

module MkSized (n : Nat) : (Sized n) {
  proc gen() : (Fin (n+1)) { return 0 };
  proc use(_x : Fin (n+1)) : Bool { return true };
}
-- the named form is what makes this reduce: a `Module.pair` record has no `Sized.gen` to project
example (n : Nat) : Sized.gen n (MkSized n) = MkSized.gen n := by
  simp only [MkSized, Sized.gen, Sized.mk, Module.fst_pair']

-- all-implicit parameters have to be passed by name, which reaches the constructor unchanged
module MkPoly {α : Type} [Inhabited α] : (Poly (α := α)) {
  proc gen() : α { return (default : α) };
  proc use(_x : α) : Bool { return true };
}
example {α : Type} [Inhabited α] : Poly.use (MkPoly (α := α)) = MkPoly.use (α := α) := by
  simp only [MkPoly, Poly.use, Poly.mk, Module.snd_pair']

-- and with module parameters as well, so that `apply_simp`'s right-hand side is the record too
module WrapSized (n : Nat) using (S : Sized n) : (Sized n) {
  proc gen() : (Fin (n+1)) { var r : Fin (n+1); r <- call S.gen (); return $r };
  proc use(x : Fin (n+1)) : Bool { var b : Bool; b <- call S.use ($x); return $b };
}
#check (WrapSized.apply_simp : ∀ (n : Nat) (S : Sized n),
  Module.app (WrapSized n) S
    = Sized.mk n { gen := Module.app (WrapSized.gen n) S,
                   use := Module.app (WrapSized.use n) S })

/- A comma-separated group is what the module parameters used to look like, and is not a Lean
binder list; it is rejected by name rather than by the parser complaining about the comma. -/
/--
error: module: a comma-separated group is not a Lean parameter list.  If these are the module parameters, write them after `using`.
-/
#guard_msgs(error, drop info) in
module Grouped (A : TestModule, B : TestModule) {
  proc g() : Unit { return (); };
}

/- A single module-typed Lean parameter *is* a Lean binder list, so it elaborates — with a
warning, since it is much more likely to be a module parameter written without `using`. -/
/--
warning: module: the Lean parameter `A` has a module type (TestModule).  If it is meant to be a module parameter, write it after `using`.

Disable this warning with `set_option linter.gaudisCrypt.using false`.
-/
#guard_msgs(warning, drop info) in
module Warned (A : TestModule) {
  proc g() : Unit { return (); };
}

-- and the option turns it off (no expected message: any warning here would fail the check)
#guard_msgs(drop info) in
set_option linter.gaudisCrypt.using false in
module Quiet (A : TestModule) {
  proc g() : Unit { return (); };
}


/- ### Hole names

A hole is named after the callee it was made from — `S.gen` gives the hole `S_gen` — so that a
printed procedure says which call each of its holes stands for.  A callee with no name to take
(an applied one, as in `X` and `Deep` above) falls back to `_holeᵢ`, and a name already in use —
by a parameter, a local, or an earlier hole — gets a `2`, `3`, … appended. -/
module HoleNames using (S : TestModule, T : TestModule) : M2 {
  proc g() : Unit {
    var S_main : Bool;
    S_main <- call (S.main) ("hi", (3 : Nat));
    _ <- call (T.main) ("ho", (4 : Nat));
    return ();
  };
  proc h() : Unit { return (); };
}

/--
info: def Experiment.HoleNames.g.procedure : [inst : ProgramSpec] →
  proctype () → Unit uses ((String, ℕ) → Bool, (String, ℕ) → Bool) :=
fun [ProgramSpec] ↦
  proc () uses (S_main2 : (String, ℕ) → Bool, T_main : (String, ℕ) → Bool) : Unit {
      var S_main : Bool;
      S_main <- call S_main2 ("hi", 3);
      call T_main ("ho", 4);
      return ()
}
-/
#guard_msgs in
#print HoleNames.g.procedure


end Experiment

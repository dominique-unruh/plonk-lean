import GaudisCrypt.Syntax.ProgramSyntax

/-! # Tests for `ProgramSyntax` -/

/-! ## Experiments for programs -/

namespace GaudisCrypt.ProgTest

open GaudisCrypt

variable [ProgramSpec]

axiom a : Lens Nat State
axiom b : Lens Nat State
axiom c : Lens Bool State
axiom d : Lens Nat State

-- `Lens.pair` needs disjointness of the paired lenses (resolved at the concrete lenses).
-- For nested tuples `(a, b), d` the `disjoint3'` instance derives `disjoint (a.pair b) d`
-- from the pairwise ones.
axiom a_b_disjoint : disjoint a b
axiom a_d_disjoint : disjoint a d
axiom b_d_disjoint : disjoint b d
attribute [instance] a_b_disjoint a_d_disjoint b_d_disjoint

noncomputable def prog_assign : Stmt Unit := GaudiProg[
  a <- $a + 1;
  b <- $a + $b;
]

noncomputable def prog_if : Stmt Unit := GaudiProg[
  if ($a == $b) {
    a <- 0;
  } else {
    a <- $b;
  }
]

noncomputable def prog_while : Stmt Unit := GaudiProg[
  while ($a == 0) {
    a <- $a + 1;
  }
]

noncomputable def prog_sample : Stmt Unit := GaudiProg[
  c <$ GaudisCrypt.SubProbability.uniform;
]

noncomputable def split : Stmt Unit := GaudiProg[
  (a,b) <- (1,2);
]

noncomputable def split2 : Stmt Unit := GaudiProg[
  a,b <- (1,2);
]

noncomputable def split3 : Stmt Unit := GaudiProg[
  (a,b),d <- ((1,3),2);
]


#check @prog_assign
#print prog_if

/- ### Procedures -/

-- one param, no locals, return type inferred
noncomputable def proc_inc := proc (x : Nat) {
  return $x + 1
}
#check @proc_inc

-- params + a local + body + explicit return type
noncomputable def proc_sum := proc (x : Nat, y : Nat) : Nat {
  var u : Nat;
  u <- $x + $y;
  return $u
}
#print proc_sum

-- no params, a local, control flow, writes to a global
noncomputable def proc_loop := proc () {
  var i : Nat;
  i <- 0;
  while ($i == 0) {
    i <- $i + 1;
    a <- $a + $i;
  }
  return $i
}
#check @proc_loop

/- ### Procedure calls -/

-- store the result of a one-argument call
noncomputable def prog_call : Stmt Unit := GaudiProg[
  a <- call proc_inc ($a);
]
#print prog_call

-- a two-argument call (the argument tuple matches the callee's `ParamType`)
noncomputable def prog_call2 : Stmt Unit := GaudiProg[
  a <- call proc_sum ($a, $b);
]

-- discard the result (uses `Lens.throwaway`); `()` still required
noncomputable def prog_call_void : Stmt Unit := GaudiProg[
  call proc_inc ($a);
]
#check @prog_call_void

/- ### Holes (adversary placeholders) -/

-- A `uses` clause declares holes; `call A (…)` on a hole name becomes `StmtWithHoles.hole`.
noncomputable def proc_with_hole := proc (x : Nat) uses (A : (Nat) → Nat) : Nat {
  var y : Nat;
  y <- call A ($x);          -- hole call (A is a HoleIndex)
  return $y
}
#print proc_with_hole

-- two holes + a concrete procedure call, mixed in one body
noncomputable def proc_two_holes := proc (x : Nat) uses (A : (Nat) → Bool, B : (Bool) → Nat) {
  var u : Bool;
  var v : Nat;
  u <- call A ($x);          -- hole A
  v <- call B ($u);          -- hole B
  v <- call proc_inc ($v);   -- concrete procedure (still `call`)
  call A ($v);               -- discarded hole result
  return $v
}
#check @proc_two_holes
#print proc_two_holes

/- ### Procedure *type* syntax -/

-- `proctype (…) -> W` is `Procedure { params := […], ret := W }`
example : (proctype (Nat, Bool) -> Nat) = Procedure { params := [Nat, Bool], ret := Nat } := rfl
#check (proc_inc : proctype (Nat) -> Nat)
#check (proc_sum : proctype (Nat, Nat) -> Nat)

-- `proctype (…) -> W uses (…)` is the corresponding `ProcedureWithHoles`
#check (proc_two_holes : proctype (Nat) -> Nat uses ((Nat) → Bool, (Bool) → Nat))
#check (proc_with_hole : proctype (Nat) -> Nat uses ((Nat) → Nat))

-- the types also print back as `proctype …` (unexpanders)
#check proctype (Nat) -> Nat
#check proctype (Nat, Bool) -> Nat uses ((Nat) → Bool, (Bool) → Nat)

-- `procsig (…) -> W` is the bare signature; `Procedure (procsig …) = proctype …`
example : (procsig (Nat, Bool) -> Nat) = ({ params := [Nat, Bool], ret := Nat } : ProcedureSignature) :=
  rfl
example : Procedure (procsig (Nat) -> Nat) = proctype (Nat) -> Nat := rfl
#check procsig (Nat, Bool) -> Nat
#check ProcedureSignature.mk [String,String] Nat
#check Procedure (ProcedureSignature.mk [String,String] Nat)
#check ProcedureWithHoles (.append .empty (procsig () -> Unit)) (ProcedureSignature.mk [String,String] Nat)
-- TODO: Can we make test cases that trigger if the terms above don't print the way we want?

-- both arrow spellings accepted: `->` and `→`
example : (procsig (Nat) → Bool) = (procsig (Nat) -> Bool) := rfl
example : (proctype (Nat) → Bool) = (proctype (Nat) -> Bool) := rfl
#check (proc_two_holes : proctype (Nat) → Nat uses ((Nat) → Bool, (Bool) → Nat))

/-! ### Printing and round-tripping

`#roundtrip t` prints `t` with the delaborators of `ProgramSyntax.lean`, parses the printed
text again and checks that what comes back is definitionally equal to `t`.  The printed text
is logged and pinned by the `#guard_msgs` docstrings — a delaborator that quietly gave up
(so that Lean printed the raw constructor term) would still round-trip, but would not print
the surface syntax, and the docstring catches that. -/

open Lean Elab Command Term PrettyPrinter in
/-- `#roundtrip t`: print `t`, parse the printed text, elaborate it, and check the result is
defeq to `t`.  Logs the printed text. -/
elab "#roundtrip " t:term : command => Command.runTermElabM fun _ => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let ty ← Meta.inferType e
  let text := (← ppExpr e).pretty
  let stx ← match Parser.runParserCategory (← getEnv) `term text "<roundtrip>" with
    | .ok stx => pure stx
    | .error msg => throwError "printed term does not parse:{indentD text}\n{msg}"
  let e' ← Term.elabTerm (TSyntax.mk stx : Term) (some ty)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e' ← instantiateMVars e'
  unless ← Meta.isDefEq e e' do
    throwError "round-trip changed the term:{indentD text}\nelaborated back to\
      {indentD (← Meta.ppExpr e')}"
  logInfo text

/--
info: GaudiProg[
    a <- §a + 1;
    b <- §a + §b;
]
-/
#guard_msgs in
#roundtrip GaudiProg[ a <- $a + 1; b <- $a + $b; ]

-- tuple l-values, a nested tuple, and the throwaway `_`
/--
info: GaudiProg[
    a, b <- (1, 2);
    (a, b), d <- ((1, 2), 3);
    _ <- 4;
]
-/
#guard_msgs in
#roundtrip GaudiProg[ a, b <- (1, 2); (a, b), d <- ((1, 2), 3); _ <- 4; ]

-- control flow; `if` without an `else` prints in its short form again
/--
info: GaudiProg[
    if (§a == 0) {
      a <- 1;
    } else {
      a <- 2;
    }
    if (§a == 0) {
      a <- 1;
    }
    while (§a == 0) {
      a <- §a + 1;
    }
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  if ($a == 0) { a <- 1; } else { a <- 2; }
  if ($a == 0) { a <- 1; }
  while ($a == 0) { a <- $a + 1; }
]

-- a `seq` in the left position of a `seq` has to print as a block, or re-parsing would
-- re-associate it
/--
info: GaudiProg[
    {
      a <- 1;
      b <- 2;
    }
    a <- 3;
]
-/
#guard_msgs in
#roundtrip GaudiProg[ { a <- 1; b <- 2; } a <- 3; ]

-- Lean binders in statement position.  A binder at the very top of a program wraps the whole
-- `StmtWithHoles`, so the term's head is a `let`, not a `StmtWithHoles` constructor, and it is
-- Lean's own `let` delaborator that prints it — outside the `GaudiProg[ ]` brackets.  That
-- re-parses to the same term, so the round trip holds either way.
/--
info: let n := 1;
have m := n + 1;
GaudiProg[
    a <- n;
    b <- m;
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  let n := 1;
  have m : Nat := n + 1;
  a <- n;
  b <- m;
]

-- `letI`/`haveI` inline their value during elaboration, so no binder of theirs is left in the
-- term: what prints is the inlined program
/--
info: GaudiProg[
    a <- 1;
    b <- 2;
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  letI n : Nat := 1;
  haveI m : Nat := 2;
  a <- n;
  b <- m;
]

-- a binder carries the statements it scopes over, so in the *left* position of a `seq` it has
-- to print as a block — re-parsing it flat would let it swallow the statements that follow
/--
info: GaudiProg[
    {
      let n : ℕ := 1;
      a <- n;
    }
    b <- 2;
]
-/
#guard_msgs in
#roundtrip GaudiProg[ { let n := 1; a <- n; } b <- 2; ]

-- a binder inside a branch scopes over the rest of that branch only
/--
info: GaudiProg[
    if (§a == 0) {
      let n : ℕ := 1;
      a <- n;
    }
    b <- 2;
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  if ($a == 0) {
    let n := 1;
    a <- n;
  }
  b <- 2;
]

-- in a `proc`: the parameter and local-variable lenses are in scope in the binder's value
/--
info: proc (x : ℕ) : ℕ {
    var u : ℕ;
    let k : ℕ := 7;
    u <- §x + k;
    return §u
}
-/
#guard_msgs in
#roundtrip proc (x : Nat) : Nat {
  var u : Nat;
  let k := 7;
  u <- $x + k;
  return $u
}

-- a binder on the body's spine scopes over the `return` expression as well: the macro repeats
-- it around the return value, which is a field of its own
/--
info: proc (x : ℕ) : ℕ {
    var u : ℕ;
    let k : ℕ := 7;
    u <- §x;
    return §u + k
}
-/
#guard_msgs in
#roundtrip proc (x : Nat) : Nat {
  var u : Nat;
  let k := 7;
  u <- $x;
  return $u + k
}

-- an instance bound by `have` is likewise available to the `return` expression (the linter is
-- off because a binder used only by instance resolution counts as unreferenced)
/--
info: proc () : ℕ {
    have inst : Inhabited ℕ := { default := 3 };
    skip;
    return default
}
-/
#guard_msgs in
set_option linter.unusedVariables false in
#roundtrip proc () : Nat {
  have inst : Inhabited Nat := ⟨3⟩;
  return default
}

/- An *anonymous* binder, `have _ : T := v;` — the usual spelling for one bound only to be found
by instance resolution — prints as the `_` it was written as.  Lean gives it an inaccessible name
(`x✝`), which is not a name one could write back, so it is the one binder whose printed name is
not its name in the term. -/
/--
info: proc () : Bool {
    have _ : Inhabited ℕ := { default := 3 };
    skip;
    return true
}
-/
#guard_msgs in
#roundtrip proc () : Bool {
  have _ : Inhabited Nat := ⟨3⟩;
  return true
}

-- one binder may name several variables of one type, in the parameter list and in a `var` line
-- alike; it stands for the same list as writing them out, which is how it prints back
/--
info: proc (x : ℕ, y : ℕ) : ℕ {
    var u : ℕ, w : ℕ;
    u <- §x;
    w <- §y;
    return §u + §w
}
-/
#guard_msgs in
#roundtrip proc (x y : Nat) : Nat {
  var u w : Nat;
  u <- $x;
  w <- $y;
  return $u + $w
}

-- sampling and calls: no arguments, one argument, two arguments, result discarded
/--
info: GaudiProg[
    c <$ SubProbability.uniform;
    a <- call proc_loop ();
    a <- call proc_inc (§a);
    a <- call proc_sum (§a, §b);
    call proc_inc (§a);
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  c <$ GaudisCrypt.SubProbability.uniform;
  a <- call proc_loop ();
  a <- call proc_inc ($a);
  a <- call proc_sum ($a, $b);
  call proc_inc ($a);
]

-- outside of a `proc` there is no name for a hole, so the internal `holecall` is printed
/--
info: GaudiProg[
    a <- holecall HoleIndex.zero (§a);
]
-/
#guard_msgs in
#roundtrip GaudiProg[
  a <- holecall (HoleIndex.zero (Γ := .empty) (a := procsig (Nat) -> Nat)) ($a);
]

-- procedures: parameters, locals, an explicit return type (always printed)
/--
info: proc (x : ℕ, y : ℕ) : ℕ {
    var u : ℕ;
    u <- §x + §y;
    return §u
}
-/
#guard_msgs in
#roundtrip proc (x : Nat, y : Nat) : Nat {
  var u : Nat;
  u <- $x + $y;
  return $u
}

-- no parameters, no locals, empty body (the body is `skip`)
/--
info: proc () : ℕ {
    skip;
    return 0
}
-/
#guard_msgs in
#roundtrip proc () { return 0 }

-- holes print as `call A (…)` inside the `proc` that declares `A`
/--
info: proc (x : ℕ) uses (A : (ℕ) → Bool, B : (Bool) → ℕ) : ℕ {
    var u : Bool, v : ℕ;
    u <- call A (§x);
    v <- call B (§u);
    call A (§x);
    return §v
}
-/
#guard_msgs in
#roundtrip proc (x : Nat) uses (A : (Nat) → Bool, B : (Bool) → Nat) : Nat {
  var u : Bool;
  var v : Nat;
  u <- call A ($x);
  v <- call B ($u);
  call A ($x);
  return $v
}

-- a procedure literal in callee position prints (and re-parses) as one
/--
info: GaudiProg[
    a <- call
    (proc (x : ℕ) : ℕ {
        skip;
        return §x + 1
  }) (§a);
]
-/
#guard_msgs in
#roundtrip GaudiProg[ a <- call (proc (x : Nat) : Nat { return $x + 1 }) ($a); ]

-- the surface syntax steps aside when Lean is told to print the term as it is
/-- info: StmtWithHoles.assign (liftLens a) { get := fun st ↦ 1 } : StmtWithHoles HoleSigs.empty Unit -/
#guard_msgs in
set_option pp.notation false in
#check (GaudiProg[ a <- 1; ] : Stmt Unit)

/-- info: @StmtWithHoles.skip inst✝ HoleSigs.empty Unit : @StmtWithHoles inst✝ HoleSigs.empty Unit -/
#guard_msgs in
set_option pp.explicit true in
#check (GaudiProg[ skip; ] : Stmt Unit)

-- `pp.gaudisCrypt false` steps aside too, but only these delaborators: Lean's own notation
-- is untouched, so the `locals` list still prints as `[…]` and not as `List.cons … List.nil`.
/--
info: { locals := [⟨ℕ, inferInstance⟩],
  body :=
    let x := Lens.id.intoParams;
    let u := Lens.id.intoVars;
    StmtWithHoles.assign (liftLens u) { get := fun st ↦ §x },
  return_val :=
    let x := Lens.id.intoParams;
    let u := Lens.id.intoVars;
    { get := fun st ↦ §u } } : proctype (ℕ) -> ℕ
-/
#guard_msgs in
set_option pp.gaudisCrypt false in
#check (proc (x : Nat) : Nat { var u : Nat; u <- $x; return $u })

end GaudisCrypt.ProgTest

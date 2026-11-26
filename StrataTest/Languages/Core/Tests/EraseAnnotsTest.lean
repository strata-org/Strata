/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.Verifier

/-! # Tests for `Program.eraseAnnots`

Programs built as ASTs. Each test prints the erased program, and whether it equals
the erasure of a second program that differs only in its annotations (types of
binders, variables, declarations and signatures, type arguments of calls, and
names of type parameters). A pair that differs outside the annotations does not
have equal erasures.
-/

namespace Core.EraseAnnotsTest
open Lambda

private def x : CoreIdent := ⟨"x", ()⟩
private def y : CoreIdent := ⟨"y", ()⟩
private def p : CoreIdent := ⟨"p", ()⟩
private def one : Expression.Expr := .const coreLoc (.intConst 1)
private def tt : Expression.Expr := .const coreLoc (.boolConst true)

/-- Prints the erasure of `annotated` and whether `plain` has the same erasure. -/
private def report (annotated plain : Program) : IO Unit := do
  IO.println (Std.format annotated.eraseAnnots)
  IO.println s!"same erasure: {annotated.eraseAnnots == plain.eraseAnnots}"

/-- The expression `x == 1`, with `x` annotated by `ty`. -/
private def eqOne (ty : Option LMonoTy) : Expression.Expr :=
  .eq coreLoc (.fvar coreLoc x ty) one

/-- A lambda `λ (b : ty). b` applied to `1`. -/
private def lam (ty : Option LMonoTy) : Expression.Expr :=
  .app coreLoc (.abs coreLoc "b" ty (.bvar coreLoc 0)) one

/-- A procedure with type parameter `a`, whose input, spec and body mention `a`
(or the annotation `ty` for the spec and guard). -/
private def proc (a : String) (declTy : LMonoTy) (ty : Option LMonoTy) : Procedure :=
  { header := { name := p, typeArgs := [a], inputs := [(x, .ftvar a)], outputs := [] },
    spec := { preconditions := [("pre", { expr := eqOne ty })], postconditions := [] },
    body := .structured
      [Statement.init y (.forAll [] declTy) (.det (lam ty)) #[],
       Imperative.Stmt.ite (.det (eqOne ty)) [] [] #[]] false }

private def prog (a : String) (declTy : LMonoTy) (ty : Option LMonoTy) : Program :=
  { decls := [.proc (proc a declTy ty) #[]] }

/-! ## Procedures -/

-- The guard, spec, binder and `init` types differ; the type parameter is renamed.
/--
info: program Core;

procedure p<||> (x : ||)
spec {
  requires [pre]: x == 1;
  } {
  var y : || := (fun b : $__unknown_type => b)(1);
  if (x == 1) {
    
  }
};

same erasure: true
-/
#guard_msgs in
#eval report (prog "a" (.ftvar "a") (some .int)) (prog "b" .int none)

-- A difference outside the annotations (the list of declarations) is kept.
/--
info: program Core;

procedure p<||> (x : ||)
spec {
  requires [pre]: x == 1;
  } {
  var y : || := (fun b : $__unknown_type => b)(1);
  if (x == 1) {
    
  }
};

same erasure: false
-/
#guard_msgs in
#eval report (prog "a" .int none) { prog "a" .int none with decls := [] }

/-- A procedure whose only statement asserts that `x` equals the constant `n`. -/
private def constProg (n : Int) : Program :=
  { decls :=
    [ .proc { header := { name := p, typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured
                [Statement.assert "a" (.eq coreLoc (.fvar coreLoc x none)
                  (.const coreLoc (.intConst n))) #[]] false } #[] ] }

-- A change to a constant is not an annotation change.
/--
info: program Core;

procedure p ()
{
  assert [a]: x == 1;
};

same erasure: false
-/
#guard_msgs in
#eval report (constProg 1) (constProg 2)

/-- A callee with type parameter `a`, and a caller whose call has type arguments `tyArgs`. -/
private def callProg (tyArgs : Option (List LTy)) : Program :=
  { decls :=
    [ .proc { header := { name := p, typeArgs := ["a"], inputs := [(x, .ftvar "a")],
                          outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [] false } #[],
      .proc { header := { name := ⟨"q", ()⟩, typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured [.cmd (.call "p" tyArgs [.inArg one] #[])] false } #[] ] }

-- The type arguments of a call are reset to `none`.
/--
info: program Core;

procedure p<||> (x : ||)
{
  
};
procedure q ()
{
  call p(1);
};

same erasure: true
-/
#guard_msgs in
#eval report (callProg (some [.forAll [] .int])) (callProg none)

/-- A procedure with a loop, whose measure, invariant and guard carry the annotation `ty`. -/
private def loopProg (ty : Option LMonoTy) : Program :=
  { decls :=
    [ .proc { header := { name := p, typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .structured
                [Imperative.Stmt.loop (.det (eqOne ty)) (some (lam ty)) [("inv", eqOne ty)]
                  [] #[]] false } #[] ] }

-- The guard, measure and invariants of a loop are erased.
/--
info: program Core;

procedure p ()
{
  while (x == 1)
  decreases (fun b : $__unknown_type => b)(1)
  invariant [inv]: x == 1
  {
    
  }
};

same erasure: true
-/
#guard_msgs in
#eval report (loopProg (some .int)) (loopProg none)

/-- A procedure with a control flow graph body. -/
private def cfgProg (declTy : LMonoTy) (ty : Option LMonoTy) : Program :=
  { decls :=
    [ .proc { header := { name := p, typeArgs := [], inputs := [], outputs := [] },
              spec := { preconditions := [], postconditions := [] },
              body := .cfg
                { entry := "l0",
                  blocks :=
                    [("l0", ⟨[.cmd (.init y (.forAll [] declTy) (.det (lam ty)) #[])],
                        .condGoto (eqOne ty) "l1" "l1" #[], #[]⟩),
                     ("l1", ⟨[], .finish #[], #[]⟩)] } false } #[] ] }

-- The commands and branch guards of a control flow graph are erased.
/--
info: program Core;

procedure p ()
cfg l0 {
  l0: {
    var y : || := (fun b : $__unknown_type => b)(1);
    branch (x == 1) goto l1 else goto l1;
  }
  l1: {
    return;
  }
};

same erasure: true
-/
#guard_msgs in
#eval report (cfgProg (.ftvar "a") (some .int)) (cfgProg .int none)

/-! ## Functions -/

/-- A function with type parameter `a`, signature types `inTy` and `outTy`, and a body,
precondition, axiom and measure annotated by `ty`. -/
private def func (a : String) (inTy outTy : LMonoTy) (ty : Option LMonoTy) : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [a], inputs := [(x, inTy)], output := outTy,
    body := some (lam ty), preconditions := [{ expr := eqOne ty, md := coreLoc }],
    axioms := [eqOne ty], measure := some (lam ty) }

-- The signature types, type parameter and every expression of a function are erased.
/--
info: program Core;

function f<||> (x : ||) : || requires x == 1;
   {
  (fun b : $__unknown_type => b)(1)
}

same erasure: true
-/
#guard_msgs in
#eval report { decls := [.func (func "a" (.ftvar "a") (.ftvar "a") (some .int)) #[]] }
  { decls := [.func (func "b" .int .int none) #[]] }

-- A function in a recursive block is erased in the same way.
/--
info: program Core;

rec function f<||> (x : ||) : || requires x == 1;
  
decreases (fun b : $__unknown_type => b)(1)
  {
  (fun b : $__unknown_type => b)(1)
};

same erasure: true
-/
#guard_msgs in
#eval report
  { decls := [.recFuncBlock [{ func "a" (.ftvar "a") (.ftvar "a") (some .int) with
      isRecursive := true }] #[]] }
  { decls := [.recFuncBlock [{ func "b" .int .int none with isRecursive := true }] #[]] }

/-! ## Axioms, lemmas and distinct declarations -/

/-- A universally quantified formula whose binders, including a nested lambda binder,
have type `ty`. -/
private def quantified (ty : Option LMonoTy) : Expression.Expr :=
  .quant coreLoc .all "i" ty tt
    (.eq coreLoc (.app coreLoc (.abs coreLoc "a" ty (.abs coreLoc "b" ty (.bvar coreLoc 0))) one)
      (.bvar coreLoc 0))

-- The binder types of a quantifier and of nested lambdas are erased.
/--
info: program Core;

axiom [q]: forall i : $__unknown_type ::  { true }
  (fun a : $__unknown_type => fun b : $__unknown_type => b)(1) == i;

same erasure: true
-/
#guard_msgs in
#eval report { decls := [.ax { name := "q", e := quantified (some .int) } #[]] }
  { decls := [.ax { name := "q", e := quantified none } #[]] }

-- The type parameters of a lemma become placeholders and its expression is erased.
/--
info: program Core;

lemma [l] <||>: x == 1;

same erasure: true
-/
#guard_msgs in
#eval report { decls := [.lemma { name := "l", typeArgs := ["a"], e := eqOne (some .int) } #[]] }
  { decls := [.lemma { name := "l", typeArgs := ["b"], e := eqOne none } #[]] }

-- The expressions of a `distinct` declaration are erased.
/--
info: program Core;

distinct [d]: [x == 1, x == 1];

same erasure: true
-/
#guard_msgs in
#eval report { decls := [.distinct ⟨"d", ()⟩ [eqOne (some .int), eqOne none] #[]] }
  { decls := [.distinct ⟨"d", ()⟩ [eqOne none, eqOne none] #[]] }

/-! ## Types -/

/-- A datatype with type parameter `a` whose constructor has a field of type `field`. -/
private def box (field : LMonoTy) : Program :=
  { decls :=
    [ .type (.data
        [{ name := "Box", typeArgs := ["a"],
           constrs := [{ name := ⟨"Mk", ()⟩, args := [(⟨"v", ()⟩, field)] }],
           constrs_ne := rfl }]) #[] ] }

-- The field types of a datatype constructor are erased and the type parameters are kept.
/--
info: program Core;

datatype Box (a : Type) {
  Mk(v : ||)
};

same erasure: true
-/
#guard_msgs in
#eval report (box (.ftvar "a")) (box .int)

-- A synonym's body is erased and its type parameters are kept.
/--
info: program Core;

type S (a : Type) := ||;

same erasure: true
-/
#guard_msgs in
#eval report { decls := [.type (.syn { name := "S", typeArgs := ["a"], type := .int }) #[]] }
  { decls := [.type (.syn { name := "S", typeArgs := ["a"], type := .bool }) #[]] }

/-! ## Expressions and statements -/

-- A lambda binder type is erased.
/--
info: (fun b : $__unknown_type => b)(1)
-/
#guard_msgs in
#eval Std.format (lam (some .int)).eraseTypes

-- A declared `init` type becomes the placeholder.
/--
info: var x : || := x == 1;
-/
#guard_msgs in
#eval Std.format
  (Statement.eraseAnnots (Statement.init x (.forAll [] .int) (.det (eqOne none)) #[]))

end Core.EraseAnnotsTest

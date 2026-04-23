/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for the StaticFieldParameterization pass, which eliminates static fields
by converting them to explicit in/out parameters on procedures.

Covers: no-op, single read, single write, multiple globals, transitive
propagation, aliasing (two globals written by one procedure), mixed read/write,
existing parameters/outputs, call-in-value-position, conditional write,
loop body write, and staticFields clearing.
-/

import Strata.Languages.Laurel.StaticFieldParameterization
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

open Strata.Laurel

namespace Strata.Laurel.StaticFieldParameterizationTest

/-! ## Helpers -/

private def intTy : HighTypeMd := ⟨.TInt, none, .empty⟩
private def mkE (e : StmtExpr) : StmtExprMd := ⟨e, none, .empty⟩
private def mkVar (n : String) : StmtExprMd := mkE (.Identifier (mkId n))
private def mkSF (n : String) : StmtExprMd := mkE (.Identifier (mkId s!"$sf_{n}"))
private def mkAssign (targets : List StmtExprMd) (v : StmtExprMd) : StmtExprMd :=
  mkE (.Assign targets v)
private def mkCall (name : String) (args : List StmtExprMd := []) : StmtExprMd :=
  mkE (.StaticCall (mkId name) args)
private def mkBlock (stmts : List StmtExprMd) : StmtExprMd :=
  mkE (.Block stmts none)
private def mkLocalVar (n : String) (init : Option StmtExprMd := none) : StmtExprMd :=
  mkE (.LocalVariable (mkId n) intTy init)
private def mkSFLocalVar (n : String) : StmtExprMd :=
  mkE (.LocalVariable (mkId s!"$sf_{n}") intTy (some (mkE .Hole)))
private def mkIntLit (n : Int) : StmtExprMd := mkE (.LiteralInt n)

private def mkField (n : String) : Field :=
  { name := mkId n, isMutable := true, type := intTy }

private def mkProc (name : String) (body : StmtExprMd)
    (inputs : List Parameter := []) (outputs : List Parameter := []) : Procedure :=
  { name := mkId name, inputs, outputs, preconditions := [],
    decreases := none, isFunctional := false,
    body := .Transparent body }

private def mkMainProc (body : StmtExprMd) : Procedure :=
  mkProc "__main__" body

private def runPass (p : Program) : Program := staticFieldParameterization p

private def printProcs (p : Program) : IO Unit := do
  for proc in p.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))

/-! ## Test: No static fields → pass is a no-op -/

/--
info: procedure noop()
1;
-/
#guard_msgs in
#eval! do
  let prog : Program := {
    staticProcedures := [mkProc "noop" (mkIntLit 1)]
    staticFields := []
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Single global write — writer gets in/out params, __main__ keeps locals -/

/--
info: procedure writer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 42 } };
procedure __main__()
{ var $sf_x: int := <?>; $sf_x := writer($sf_x) };
-/
#guard_msgs in
#eval! do
  let writerBody := mkBlock [
    mkSFLocalVar "x",
    mkAssign [mkSF "x"] (mkIntLit 42)
  ]
  let mainBody := mkBlock [
    mkSFLocalVar "x",
    mkCall "writer"
  ]
  let prog : Program := {
    staticProcedures := [mkProc "writer" writerBody, mkMainProc mainBody]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Read-only access → input parameter only, no output -/

/--
info: procedure reader($sf_in_x: int)
{ $sf_x := $sf_in_x; { $sf_x } };
procedure __main__()
{ var $sf_x: int := <?>; reader($sf_x) };
-/
#guard_msgs in
#eval! do
  let readerBody := mkBlock [
    mkSFLocalVar "x",
    mkSF "x"
  ]
  let mainBody := mkBlock [
    mkSFLocalVar "x",
    mkCall "reader"
  ]
  let prog : Program := {
    staticProcedures := [mkProc "reader" readerBody, mkMainProc mainBody]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Multiple globals, procedure uses only a subset -/

/--
info: procedure usesX($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 1 } };
procedure __main__()
{ var $sf_x: int := <?>; var $sf_y: int := <?>; $sf_x := usesX($sf_x) };
-/
#guard_msgs in
#eval! do
  let usesXBody := mkBlock [
    mkSFLocalVar "x",
    mkAssign [mkSF "x"] (mkIntLit 1)
  ]
  let mainBody := mkBlock [
    mkSFLocalVar "x",
    mkSFLocalVar "y",
    mkCall "usesX"
  ]
  let prog : Program := {
    staticProcedures := [mkProc "usesX" usesXBody, mkMainProc mainBody]
    staticFields := [mkField "x", mkField "y"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Transitive propagation — caller inherits callee's field usage -/

/--
info: procedure inner($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 99 } };
procedure outer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := inner($sf_x) } };
procedure __main__()
{ var $sf_x: int := <?>; $sf_x := outer($sf_x) };
-/
#guard_msgs in
#eval! do
  let innerBody := mkBlock [
    mkSFLocalVar "x",
    mkAssign [mkSF "x"] (mkIntLit 99)
  ]
  let outerBody := mkBlock [
    mkSFLocalVar "x",
    mkCall "inner"
  ]
  let mainBody := mkBlock [
    mkSFLocalVar "x",
    mkCall "outer"
  ]
  let prog : Program := {
    staticProcedures := [
      mkProc "inner" innerBody,
      mkProc "outer" outerBody,
      mkMainProc mainBody
    ]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Two globals aliased — both written by same procedure -/

/--
info: procedure writesBoth($sf_in_a: int, $sf_in_b: int)
  returns ($sf_a: int, $sf_b: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_a := 1; $sf_b := 2 } };
procedure __main__()
{ var $sf_a: int := <?>; var $sf_b: int := <?>; $sf_a := writesBoth($sf_a, $sf_b) };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "a",
    mkSFLocalVar "b",
    mkAssign [mkSF "a"] (mkIntLit 1),
    mkAssign [mkSF "b"] (mkIntLit 2)
  ]
  let mainBody := mkBlock [
    mkSFLocalVar "a",
    mkSFLocalVar "b",
    mkCall "writesBoth"
  ]
  let prog : Program := {
    staticProcedures := [mkProc "writesBoth" body, mkMainProc mainBody]
    staticFields := [mkField "a", mkField "b"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Procedure with existing parameters — SF params prepended -/

/--
info: procedure addToGlobal($sf_in_x: int, n: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := $sf_x + n } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "x",
    mkAssign [mkSF "x"] (mkE (.PrimitiveOp .Add [mkSF "x", mkVar "n"]))
  ]
  let proc := mkProc "addToGlobal" body
    (inputs := [{ name := mkId "n", type := intTy }])
  let prog : Program := {
    staticProcedures := [proc]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Procedure with existing outputs — SF outputs prepended -/

/--
info: procedure getAndBump($sf_in_x: int)
  returns ($sf_x: int, $result: int)
{ $sf_x := $sf_in_x; { var old: int := $sf_x; $sf_x := $sf_x + 1; old } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "x",
    mkLocalVar "old" (some (mkSF "x")),
    mkAssign [mkSF "x"] (mkE (.PrimitiveOp .Add [mkSF "x", mkIntLit 1])),
    mkVar "old"
  ]
  let proc := mkProc "getAndBump" body
    (outputs := [{ name := mkId "$result", type := intTy }])
  let prog : Program := {
    staticProcedures := [proc]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Write one, read another — mixed in/out parameters -/

/--
info: procedure copyAtoB($sf_in_a: int, $sf_in_b: int)
  returns ($sf_b: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_b := $sf_a } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "a",
    mkSFLocalVar "b",
    mkAssign [mkSF "b"] (mkSF "a")
  ]
  let prog : Program := {
    staticProcedures := [mkProc "copyAtoB" body]
    staticFields := [mkField "a", mkField "b"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: staticFields is cleared after the pass -/

/--
info: true
-/
#guard_msgs in
#eval! do
  let body := mkBlock [mkSFLocalVar "x", mkAssign [mkSF "x"] (mkIntLit 1)]
  let prog : Program := {
    staticProcedures := [mkProc "f" body, mkMainProc (mkBlock [mkSFLocalVar "x", mkCall "f"])]
    staticFields := [mkField "x"]
    types := []
  }
  IO.println (toString (runPass prog).staticFields.isEmpty)

/-! ## Test: Call to non-SF procedure is unchanged -/

/--
info: procedure helper()
42;
procedure writer($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := helper() } };
-/
#guard_msgs in
#eval! do
  let helperBody := mkIntLit 42
  let writerBody := mkBlock [
    mkSFLocalVar "x",
    mkAssign [mkSF "x"] (mkCall "helper")
  ]
  let prog : Program := {
    staticProcedures := [mkProc "helper" helperBody, mkProc "writer" writerBody]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Call in value position to writer wraps in block with temp var -/

/--
info: procedure writer($sf_in_g: int)
  returns ($sf_g: int, $result: int)
{ $sf_g := $sf_in_g; { $sf_g := 10; 5 } };
procedure caller($sf_in_g: int)
  returns ($sf_g: int)
{ $sf_g := $sf_in_g; { var y: int := { var $sftmp0: Unknown; $sf_g := writer($sf_g); $sftmp0 } } };
-/
#guard_msgs in
#eval! do
  let writerBody := mkBlock [
    mkSFLocalVar "g",
    mkAssign [mkSF "g"] (mkIntLit 10),
    mkIntLit 5
  ]
  let callerBody := mkBlock [
    mkSFLocalVar "g",
    mkLocalVar "y" (some (mkCall "writer"))
  ]
  let prog : Program := {
    staticProcedures := [
      mkProc "writer" writerBody (outputs := [{ name := mkId "$result", type := intTy }]),
      mkProc "caller" callerBody
    ]
    staticFields := [mkField "g"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Conditional write — if branch writes global -/

/--
info: procedure condWriter($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { if true then $sf_x := 1 else $sf_x := 2 } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "x",
    mkE (.IfThenElse
      (mkE (.LiteralBool true))
      (mkAssign [mkSF "x"] (mkIntLit 1))
      (some (mkAssign [mkSF "x"] (mkIntLit 2))))
  ]
  let prog : Program := {
    staticProcedures := [mkProc "condWriter" body]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Global in while loop body -/

/--
info: procedure looper($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { while(true) { $sf_x := $sf_x + 1 } } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "x",
    mkE (.While
      (mkE (.LiteralBool true))
      []
      none
      (mkBlock [mkAssign [mkSF "x"] (mkE (.PrimitiveOp .Add [mkSF "x", mkIntLit 1]))]))
  ]
  let prog : Program := {
    staticProcedures := [mkProc "looper" body]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Aliasing — two procedures write the same global, caller calls both -/

/--
info: procedure setA($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 1 } };
procedure setB($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := 2 } };
procedure callBoth($sf_in_x: int)
  returns ($sf_x: int)
{ $sf_x := $sf_in_x; { $sf_x := setA($sf_x); $sf_x := setB($sf_x) } };
-/
#guard_msgs in
#eval! do
  let setABody := mkBlock [mkSFLocalVar "x", mkAssign [mkSF "x"] (mkIntLit 1)]
  let setBBody := mkBlock [mkSFLocalVar "x", mkAssign [mkSF "x"] (mkIntLit 2)]
  let callBothBody := mkBlock [mkSFLocalVar "x", mkCall "setA", mkCall "setB"]
  let prog : Program := {
    staticProcedures := [
      mkProc "setA" setABody,
      mkProc "setB" setBBody,
      mkProc "callBoth" callBothBody
    ]
    staticFields := [mkField "x"]
    types := []
  }
  printProcs (runPass prog)

/-! ## Test: Aliasing — procedure writes global a, reads global b, where a and b
    are distinct fields. Verifies correct parameter separation. -/

/--
info: procedure swapper($sf_in_a: int, $sf_in_b: int)
  returns ($sf_a: int)
{ $sf_a := $sf_in_a; $sf_b := $sf_in_b; { $sf_a := $sf_b } };
-/
#guard_msgs in
#eval! do
  let body := mkBlock [
    mkSFLocalVar "a",
    mkSFLocalVar "b",
    mkAssign [mkSF "a"] (mkSF "b")
  ]
  let prog : Program := {
    staticProcedures := [mkProc "swapper" body]
    staticFields := [mkField "a", mkField "b"]
    types := []
  }
  printProcs (runPass prog)

end Strata.Laurel.StaticFieldParameterizationTest

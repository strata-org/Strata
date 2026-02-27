/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Backends.CBMC.GOTO.LambdaToCProverGOTO
import Strata.DL.Imperative.ToCProverGOTO
import Strata.Backends.CBMC.GOTO.InstToJson

-------------------------------------------------------------------------------

/- PoC of mapping Imperative parameterized by an expression language into GOTO
instructions -/

section
open Std (ToFormat Format format)

private abbrev TestParams : Lambda.LExprParams := ⟨Unit, Unit⟩

private abbrev LExprTP : Imperative.PureExpr :=
   { Ident := TestParams.Identifier,
     Expr := Lambda.LExprT TestParams.mono,
     Ty := Lambda.LMonoTy,
     ExprMetadata := TestParams.Metadata,
     TyEnv := @Lambda.TEnv TestParams.IDMeta,
     TyContext := @Lambda.LContext TestParams,
     EvalEnv := Lambda.LState TestParams
     EqIdent := inferInstanceAs (DecidableEq TestParams.Identifier) }

/--
Commands, parameterized by type-annotated Lambda expressions.

We assume in this test that the Lambda expressions are well-typed. In practice,
these should after Lambda's type inference pass.
-/
private abbrev Cmd := Imperative.Cmd LExprTP

private def lookupType (T : LExprTP.TyEnv) (i : LExprTP.Ident) : Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => .error f!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else .error f!"Poly-type unexpected in the context for {i}: {ty}"

private def updateType (T : LExprTP.TyEnv) (i : LExprTP.Ident) (ty : LExprTP.Ty) : LExprTP.TyEnv :=
  T.addInNewestContext [(i, (.forAll [] ty))]

instance : Imperative.ToGoto LExprTP where
  lookupType := lookupType
  updateType := updateType
  identToString := (fun i => i.name)
  toGotoType := Lambda.LMonoTy.toGotoType
  toGotoExpr := Lambda.LExprT.toGotoExpr

-------------------------------------------------------------------------------

open Lambda.LTy.Syntax

def ExampleProgram1 : Imperative.Cmds LExprTP :=
  [.init (Lambda.Identifier.mk "s" ()) mty[bv32]
    (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)))
    .empty,
   .set (Lambda.Identifier.mk "s" ())
    (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100))
    .empty]

/--
info: ok: #[DECL (decl (s : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (100 : unsignedbv[32]))]
-/
#guard_msgs in
#eval do let ans ← Imperative.Cmds.toGotoTransform Lambda.TEnv.default "one" ExampleProgram1
          return format ans.instructions

-------------------------------------------------------------------------------


/- (100 : bv32) + (200 : bv32) -/
private def addBV32LExpr (op1 op2 : Lambda.LExprT TestParams.mono) : Lambda.LExprT TestParams.mono :=
  (Lambda.LExpr.app { underlying := (), type := mty[bv32] }
    (Lambda.LExpr.app { underlying := (), type := mty[bv32 → bv32] }
      (.op { underlying := (), type := mty[bv32 → bv32 → bv32] } (Lambda.Identifier.mk "Bv32.Add" ()) (some mty[bv32 → bv32 → bv32])) op1)
    op2)

def ExampleProgram2 : Imperative.Cmds LExprTP :=
  [.init (Lambda.Identifier.mk "s" ()) mty[bv32]
    (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)))
    .empty,
   .set (Lambda.Identifier.mk "s" ())
    (addBV32LExpr (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100))
    (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 200)))
    .empty]

/--
info: ok: #[DECL (decl (s : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (((100 : unsignedbv[32]) + (200 : unsignedbv[32])) : unsignedbv[32]))]
-/
#guard_msgs in
#eval do let ans ← Imperative.Cmds.toGotoTransform Lambda.TEnv.default "two" ExampleProgram2
          return format ans.instructions

-------------------------------------------------------------------------------

-- (FIXME) Is this the right way to deal with non-det. expressions?

def ExampleProgram3 : Imperative.Cmds LExprTP :=
  [.init (Lambda.Identifier.mk "x" ()) mty[bv32]
    (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)))
    .empty,
   .init (Lambda.Identifier.mk "y" ()) mty[bv32]
    (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)))
    .empty,
   .havoc (Lambda.Identifier.mk "x" ()) .empty,
   .havoc (Lambda.Identifier.mk "y" ()) .empty,
   .init (Lambda.Identifier.mk "z" ()) mty[bv32]
    (some (addBV32LExpr (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "x" ()) (some mty[bv32])) (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "y" ()) (some mty[bv32]))))
    .empty]

/--
info: ok: #[DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 DECL (decl (y : unsignedbv[32])),
 ASSIGN (assign (y : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (nondet : unsignedbv[32])),
 ASSIGN (assign (y : unsignedbv[32]) (nondet : unsignedbv[32])),
 DECL (decl (z : unsignedbv[32])),
 ASSIGN (assign (z : unsignedbv[32]) (((x : unsignedbv[32]) + (y : unsignedbv[32])) : unsignedbv[32]))]
-/
#guard_msgs in
#eval do let ans ← Imperative.Cmds.toGotoTransform Lambda.TEnv.default "three" ExampleProgram3
          return format ans.instructions

-------------------------------------------------------------------------------

/-! ## Tests for Statement Transformation -/

/-- Test block statement transformation -/
def ExampleStmt1 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.block "test_block"
    [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10))) {}),
     .cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 20)) {})]
    {}]

/--
info: ok: #[LOCATION skip,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (20 : unsignedbv[32])),
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test1" ExampleStmt1
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test if-then-else (ite) statement transformation -/
def ExampleStmt2 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .cmd (.init (Lambda.Identifier.mk "y" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .ite
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     [.cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10)) {})]
     [.cmd (.set (Lambda.Identifier.mk "y" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 20)) {})]
     {}]

/--
info: ok: #[DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 DECL (decl (y : unsignedbv[32])),
 ASSIGN (assign (y : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO skip [((not(true : bool)) : bool)],
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 GOTO skip,
 LOCATION skip,
 ASSIGN (assign (y : unsignedbv[32]) (20 : unsignedbv[32])),
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test2" ExampleStmt2
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test loop statement transformation -/
def ExampleStmt3 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "i" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .loop
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     none
     []
     [.cmd (.set (Lambda.Identifier.mk "i" ()) (addBV32LExpr
       (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "i" ()) (some mty[bv32]))
       (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 1))) {})]
     {}]

/--
info: ok: #[DECL (decl (i : unsignedbv[32])),
 ASSIGN (assign (i : unsignedbv[32]) (0 : unsignedbv[32])),
 LOCATION skip,
 GOTO skip [((not(true : bool)) : bool)],
 ASSIGN (assign (i : unsignedbv[32]) (((i : unsignedbv[32]) + (1 : unsignedbv[32])) : unsignedbv[32])),
 GOTO skip,
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test3" ExampleStmt3
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test nested control flow: if inside block -/
def ExampleStmt4 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.block "outer"
    [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
     .ite
       (.const { underlying := (), type := mty[bool] } (.boolConst true))
       [.cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100)) {})]
       []
       {}]
    {}]

/--
info: ok: #[LOCATION skip,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO skip [((not(true : bool)) : bool)],
 ASSIGN (assign (x : unsignedbv[32]) (100 : unsignedbv[32])),
 GOTO skip,
 LOCATION skip,
 LOCATION skip,
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test4" ExampleStmt4
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test exit statement transformation -/
def ExampleStmt5 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .exit (some "target_label") {},
   .cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10)) {}),
   .block "target_label"
     [.cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 20)) {})]
     {}]

/--
info: ok: #[DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO skip,
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 LOCATION skip,
 ASSIGN (assign (x : unsignedbv[32]) (20 : unsignedbv[32])),
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test5" ExampleStmt5
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test complex nested control flow: loop with if inside -/
def ExampleStmt6 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "i" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .cmd (.init (Lambda.Identifier.mk "sum" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .loop
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     none
     []
     [.ite
       (.const { underlying := (), type := mty[bool] } (.boolConst true))
       [.cmd (.set (Lambda.Identifier.mk "sum" ()) (addBV32LExpr
         (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "sum" ()) (some mty[bv32]))
         (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "i" ()) (some mty[bv32]))) {})]
       []
       {},
      .cmd (.set (Lambda.Identifier.mk "i" ()) (addBV32LExpr
        (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "i" ()) (some mty[bv32]))
        (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 1))) {})]
     {}]

/--
info: ok: #[DECL (decl (i : unsignedbv[32])),
 ASSIGN (assign (i : unsignedbv[32]) (0 : unsignedbv[32])),
 DECL (decl (sum : unsignedbv[32])),
 ASSIGN (assign (sum : unsignedbv[32]) (0 : unsignedbv[32])),
 LOCATION skip,
 GOTO skip [((not(true : bool)) : bool)],
 GOTO skip [((not(true : bool)) : bool)],
 ASSIGN (assign (sum : unsignedbv[32]) (((sum : unsignedbv[32]) + (i : unsignedbv[32])) : unsignedbv[32])),
 GOTO skip,
 LOCATION skip,
 LOCATION skip,
 ASSIGN (assign (i : unsignedbv[32]) (((i : unsignedbv[32]) + (1 : unsignedbv[32])) : unsignedbv[32])),
 GOTO skip,
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test6" ExampleStmt6
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test multiple blocks in sequence -/
def ExampleStmt7 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.block "block1"
     [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10))) {})]
     {},
   .block "block2"
     [.cmd (.init (Lambda.Identifier.mk "y" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 20))) {})]
     {},
   .block "block3"
     [.cmd (.set (Lambda.Identifier.mk "x" ())
       (addBV32LExpr
         (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "x" ()) (some mty[bv32]))
         (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "y" ()) (some mty[bv32]))) {})]
     {}]

/--
info: ok: #[LOCATION skip,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 LOCATION skip,
 LOCATION skip,
 DECL (decl (y : unsignedbv[32])),
 ASSIGN (assign (y : unsignedbv[32]) (20 : unsignedbv[32])),
 LOCATION skip,
 LOCATION skip,
 ASSIGN (assign (x : unsignedbv[32]) (((x : unsignedbv[32]) + (y : unsignedbv[32])) : unsignedbv[32])),
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test7" ExampleStmt7
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test empty branches in if-then-else -/
def ExampleStmt8 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .ite
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     []
     [.cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100)) {})]
     {}]

/--
info: ok: #[DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO skip [((not(true : bool)) : bool)],
 GOTO skip,
 LOCATION skip,
 ASSIGN (assign (x : unsignedbv[32]) (100 : unsignedbv[32])),
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test8" ExampleStmt8
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test loop with empty body -/
def ExampleStmt9 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.loop
     (.const { underlying := (), type := mty[bool] } (.boolConst false))
     none
     []
     []
     {}]

/--
info: ok: #[LOCATION skip, GOTO skip [((not(false : bool)) : bool)], GOTO skip, LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test9" ExampleStmt9
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test assertions and assumptions within control flow -/
def ExampleStmt10 : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 5))) {}),
   .ite
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     [.cmd (.assume "precond" (.const { underlying := (), type := mty[bool] } (.boolConst true)) {}),
      .cmd (.set (Lambda.Identifier.mk "x" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10)) {}),
      .cmd (.assert "postcond" (.const { underlying := (), type := mty[bool] } (.boolConst true)) {})]
     []
     {}]

/--
info: ok: #[DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (5 : unsignedbv[32])),
 GOTO skip [((not(true : bool)) : bool)],
 ASSUME skip,
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 ASSERT skip,
 GOTO skip,
 LOCATION skip,
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "test10" ExampleStmt10
          return format ans.instructions

-------------------------------------------------------------------------------

/-- Test cover command translates to ASSERT -/
def ExampleCover : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.cover "reachable" (.const { underlying := (), type := mty[bool] } (.boolConst true)) {})]

/--
info: ok: #[ASSERT skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "testCover" ExampleCover
          return format ans.instructions

-------------------------------------------------------------------------------

-- Test that contracts are included in the function symbol's code type
#eval do
  let reqExpr := CProverGOTO.exprToJson
    (CProverGOTO.Expr.gt (.symbol "x" .Integer) (.constant "0" .Integer))
  let contracts := [("#spec_requires",
    Lean.Json.mkObj [("id", ""), ("sub", Lean.Json.arr #[reqExpr])])]
  let (_, sym) := CProverGOTO.createFunctionSymbol "test_fn" [("x", .Integer)] .Empty contracts
  let namedSub := sym.type.getObjValD "namedSub"
  let specReq := namedSub.getObjValD "#spec_requires"
  assert! specReq != Lean.Json.null
  match specReq.getObjValD "sub" with
  | .arr a => assert! a.size == 1
  | _ => assert! false

-------------------------------------------------------------------------------

-- Test loop with invariant attaches #spec_loop_invariant to backward GOTO
def ExampleLoopInvariant : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "i" ()) mty[bv32] (some (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .loop
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     none
     [(.const { underlying := (), type := mty[bool] } (.boolConst true))]  -- invariant: true
     [.cmd (.set (Lambda.Identifier.mk "i" ()) (addBV32LExpr
       (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "i" ()) (some mty[bv32]))
       (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 1))) {})]
     {}]

/--
info: ok: #[DECL (decl (i : unsignedbv[32])),
 ASSIGN (assign (i : unsignedbv[32]) (0 : unsignedbv[32])),
 LOCATION skip,
 GOTO skip [((not(true : bool)) : bool)],
 ASSIGN (assign (i : unsignedbv[32]) (((i : unsignedbv[32]) + (1 : unsignedbv[32])) : unsignedbv[32])),
 GOTO skip,
 LOCATION skip]
-/
#guard_msgs in
#eval do let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "testInv" ExampleLoopInvariant
          return format ans.instructions

-- The backward GOTO (location 5, targeting location 2) should have the invariant
#eval do
  let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "testInv" ExampleLoopInvariant
  let backGotos := ans.instructions.toList.filter (fun (i : CProverGOTO.Instruction) =>
    i.type == CProverGOTO.InstructionType.GOTO && i.target == some 2)
  assert! backGotos.length == 1
  let inv := backGotos[0]!.guard.getNamedField "#spec_loop_invariant"
  assert! inv.isSome

-------------------------------------------------------------------------------

-- Test: loop with measure emits #spec_decreases on backward GOTO
private def ExampleLoopMeasure : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  open Lambda.LTy.Syntax Lambda.LExpr.Syntax in
  [.cmd (.init (Lambda.Identifier.mk "i" ()) mty[int]
     (some (.const { underlying := (), type := mty[int] } (.intConst 10))) {}),
   .loop
     -- guard: true
     (.const { underlying := (), type := mty[bool] } (.boolConst true))
     -- measure: i
     (some (.fvar { underlying := (), type := mty[int] } (Lambda.Identifier.mk "i" ()) (some mty[int])))
     -- invariants: [true]
     [(.const { underlying := (), type := mty[bool] } (.boolConst true))]
     -- body: empty
     []
     {}]

#eval do
  let ans ← Imperative.Stmts.toGotoTransform Lambda.TEnv.default "testMeas" ExampleLoopMeasure
  let backGotos := ans.instructions.toList.filter (fun (i : CProverGOTO.Instruction) =>
    i.type == CProverGOTO.InstructionType.GOTO && i.target == some 2)
  assert! backGotos.length == 1
  let inv := backGotos[0]!.guard.getNamedField "#spec_loop_invariant"
  assert! inv.isSome
  let dec := backGotos[0]!.guard.getNamedField "#spec_decreases"
  assert! dec.isSome

-------------------------------------------------------------------------------

end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CFGToCProverGOTO
import Strata.DL.Lambda.LState
import Strata.Transform.StructuredToUnstructured
import StrataTest.Backends.CBMC.GOTO.LambdaToCProverGOTO

/-! ## Tests for CFG-to-CProverGOTO translation

These tests verify that `detCFGToGotoTransform` correctly translates
deterministic CFGs into CProverGOTO instruction arrays.
-/

section
open Std (ToFormat Format format)
open Lambda.LTy.Syntax

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

instance : Imperative.HasBool LExprTP where
  tt := .const { underlying := (), type := mty[bool] } (.boolConst true)
  ff := .const { underlying := (), type := mty[bool] } (.boolConst false)
  tt_is_not_ff := by simp
  boolTy := .tcons "bool" []

instance : Imperative.HasIdent LExprTP where
  ident s := ⟨s, ()⟩

private abbrev md : Lambda.Typed Unit := { underlying := (), type := mty[bool] }

instance : Imperative.HasFvar LExprTP where
  mkFvar := (.fvar md · none)
  getFvar
  | .fvar _ v _ => some v
  | _ => none

instance : Imperative.HasIntOrder LExprTP where
  eq    e1 e2 := .eq md e1 e2
  lt    e1 e2 := .app md (.app md (.op md ⟨"Int.Lt", ()⟩ none) e1) e2
  zero        := .intConst md 0
  intTy       := .tcons "int" []

instance : Imperative.HasNot LExprTP where
  not e := .app md (.op md ⟨"Bool.Not", ()⟩ none) e

-------------------------------------------------------------------------------

/-! ### Test: simple sequential commands -/

private def seqCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32]
    (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .cmd (.set (Lambda.Identifier.mk "x" ())
    (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 42))) {})]

/--
info: ok: #[LOCATION 0,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (42 : unsignedbv[32])),
 GOTO 6 [((not(true : bool)) : bool)],
 GOTO 6,
 LOCATION 6]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG seqCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-------------------------------------------------------------------------------

/-! ### Test: if-then-else -/

private def iteCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32]
    (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .ite (.det
     (.const { underlying := (), type := mty[bool] } (.boolConst true)))
     [.cmd (.set (Lambda.Identifier.mk "x" ())
       (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 10))) {})]
     [.cmd (.set (Lambda.Identifier.mk "x" ())
       (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 20))) {})]
     {}]

/--
info: ok: #[LOCATION 0,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO 9 [((not(true : bool)) : bool)],
 GOTO 5,
 LOCATION 5,
 ASSIGN (assign (x : unsignedbv[32]) (10 : unsignedbv[32])),
 GOTO 13 [((not(true : bool)) : bool)],
 GOTO 13,
 LOCATION 9,
 ASSIGN (assign (x : unsignedbv[32]) (20 : unsignedbv[32])),
 GOTO 13 [((not(true : bool)) : bool)],
 GOTO 13,
 LOCATION 13]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG iteCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-- Verify all emitted GOTOs have resolved targets
/--
info: ok: ()
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG iteCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  let gotos := ans.instructions.toList.filter (fun (i : CProverGOTO.Instruction) =>
    i.type == CProverGOTO.InstructionType.GOTO)
  assert! gotos.all (fun (i : CProverGOTO.Instruction) => i.target.isSome)

-------------------------------------------------------------------------------

/-! ### Test: loop -/

private def addBV32 (op1 op2 : Lambda.LExprT TestParams.mono) : Lambda.LExprT TestParams.mono :=
  (Lambda.LExpr.app { underlying := (), type := mty[bv32] }
    (Lambda.LExpr.app { underlying := (), type := mty[bv32 → bv32] }
      (.op { underlying := (), type := mty[bv32 → bv32 → bv32] }
        (Lambda.Identifier.mk "Bv32.Add" ()) (some mty[bv32 → bv32 → bv32])) op1)
    op2)

private def loopCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "i" ()) mty[bv32]
    (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .loop (.det
     (.const { underlying := (), type := mty[bool] } (.boolConst true)))
     none
     []
     [.cmd (.set (Lambda.Identifier.mk "i" ()) (.det (addBV32
       (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "i" ()) (some mty[bv32]))
       (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 1)))) {})]
     {}]

/--
info: ok: #[LOCATION 0,
 DECL (decl (i : unsignedbv[32])),
 ASSIGN (assign (i : unsignedbv[32]) (0 : unsignedbv[32])),
 GOTO 5 [((not(true : bool)) : bool)],
 GOTO 5,
 LOCATION 5,
 GOTO 12 [((not(true : bool)) : bool)],
 GOTO 8,
 LOCATION 8,
 ASSIGN (assign (i : unsignedbv[32]) (((i : unsignedbv[32]) + (1 : unsignedbv[32])) : unsignedbv[32])),
 GOTO 5 [((not(true : bool)) : bool)],
 GOTO 5,
 LOCATION 12]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG loopCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-- Verify the loop back-edge: there should be a GOTO targeting the loop entry
/--
info: ok: ()
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG loopCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  let gotos := ans.instructions.toList.filter (fun (i : CProverGOTO.Instruction) =>
    i.type == CProverGOTO.InstructionType.GOTO && i.target.isSome)
  -- At least one GOTO should jump backwards (target < its own locationNum)
  assert! gotos.any (fun (i : CProverGOTO.Instruction) =>
    i.target.any (· < i.locationNum))

-------------------------------------------------------------------------------

/-! ### Test: empty CFG (single finish block) -/

private def emptyCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) := []

/--
info: ok: #[LOCATION 0]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG emptyCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-------------------------------------------------------------------------------

/-! ### Test: assert and assume commands -/

private def assertAssumeCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.assume "pre" (.const { underlying := (), type := mty[bool] } (.boolConst true)) {}),
   .cmd (.assert "post" (.const { underlying := (), type := mty[bool] } (.boolConst true)) {})]

/--
info: ok: #[LOCATION 0, ASSUME, ASSERT, GOTO 5 [((not(true : bool)) : bool)], GOTO 5, LOCATION 5]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG assertAssumeCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-------------------------------------------------------------------------------

/-! ### Test: havoc command -/

private def havocCmds : List (Imperative.Stmt LExprTP (Imperative.Cmd LExprTP)) :=
  [.cmd (.init (Lambda.Identifier.mk "x" ()) mty[bv32]
    (.det (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0))) {}),
   .cmd (.set (Lambda.Identifier.mk "x" ()) .nondet {})]

/--
info: ok: #[LOCATION 0,
 DECL (decl (x : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (x : unsignedbv[32]) (nondet : unsignedbv[32])),
 GOTO 6 [((not(true : bool)) : bool)],
 GOTO 6,
 LOCATION 6]
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG havocCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  return format ans.instructions

-------------------------------------------------------------------------------

/-! ### Test: entry block must be listed first -/

#eval do
  -- Construct a CFG where entry label doesn't match the first block
  let cfg : Imperative.CFG String (Imperative.DetBlock String (Imperative.Cmd LExprTP) LExprTP) :=
    { entry := "second",
      blocks := [("first", { cmds := [], transfer := .finish }),
                 ("second", { cmds := [], transfer := .finish })] }
  match Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg with
  | .error e => assert! (s!"{e}".splitOn "Entry label").length > 1
  | .ok _ => assert! false

-------------------------------------------------------------------------------

/-! ### Test: all GOTOs have resolved targets (sequential) -/

/--
info: ok: ()
-/
#guard_msgs in
#eval do
  let cfg := Imperative.stmtsToCFG seqCmds
  let ans ← Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg
  let gotos := ans.instructions.toList.filter (fun (i : CProverGOTO.Instruction) =>
    i.type == CProverGOTO.InstructionType.GOTO)
  assert! gotos.all (fun (i : CProverGOTO.Instruction) => i.target.isSome)

-------------------------------------------------------------------------------

/-! ### Test: unresolved label produces an error -/

#eval do
  let trueExpr : LExprTP.Expr :=
    .const { underlying := (), type := mty[bool] } (.boolConst true)
  let blk : Imperative.DetBlock String (Imperative.Cmd LExprTP) LExprTP :=
    { cmds := [], transfer := .condGoto trueExpr "missing_label" "also_missing" }
  let cfg : Imperative.CFG String (Imperative.DetBlock String (Imperative.Cmd LExprTP) LExprTP) :=
    { entry := "entry", blocks := [("entry", blk)] }
  match Imperative.detCFGToGotoTransform Lambda.TEnv.default "test" cfg with
  | .error e => assert! (s!"{e}".splitOn "Unresolved label").length > 1
  | .ok _ => assert! false

-------------------------------------------------------------------------------

end

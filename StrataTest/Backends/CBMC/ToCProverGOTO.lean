/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.ToCProverGOTO
import Strata.DL.Imperative.ToCProverGOTO

-------------------------------------------------------------------------------

/- PoC of mapping Imperative parameterized by an expression language into GOTO
instructions -/

section
open Std (ToFormat Format format)

abbrev LExprTP : Imperative.PureExpr :=
   { Ident := String,
     Expr := Lambda.LExprT String,
     Ty := Lambda.LMonoTy,
     TyEnv := @Lambda.TEnv String,
     EvalEnv := Lambda.LState String
     EqIdent := instDecidableEqString }

/--
Commands, parameterized by type-annotated Lambda expressions.

We assume in this test that the Lambda expressions are well-typed.
-/
abbrev Cmd := Imperative.Cmd LExprTP

private def lookupType (T : LExprTP.TyEnv) (i : LExprTP.Ident) : Except Format CProverGOTO.Ty :=
  match T.context.types.find? i with
  | none => .error s!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else .error f!"Poly-type unexpected in the context for {i}: {ty}"

private def updateType (T : LExprTP.TyEnv) (i : LExprTP.Ident) (ty : LExprTP.Ty) : LExprTP.TyEnv :=
  T.insertInContext i (.forAll [] ty)

instance : Imperative.ToGoto LExprTP where
  lookupType := lookupType
  updateType := updateType
  identToString := (fun i => i)
  toGotoType := Lambda.LMonoTy.toGotoType
  toGotoExpr := Lambda.LExprT.toGotoExpr

-------------------------------------------------------------------------------

open Lambda.LTy.Syntax

def ExampleProgram1 : Imperative.Cmds LExprTP :=
  [.init "s" mty[bv32] (.const "0" mty[bv32]),
   .set "s" (.const "100" mty[bv32])]

/--
info: ok: #[DECL (decl (s : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (100 : unsignedbv[32]))]
-/
#guard_msgs in
#eval do let ans ← Imperative.Cmds.toGotoTransform Lambda.TEnv.default ExampleProgram1
          return format ans.instructions

/- (100 : bv32) + (200 : bv32) -/
private def addNumsLExpr :=
  (Lambda.LExprT.app
    (.app (.op "bv32AddOp" mty[bv32 → bv32 → bv32]) (.const "100" mty[bv32]) mty[bv32 → bv32])
    (.const "200" mty[bv32])
       mty[bv32])

def ExampleProgram2 : Imperative.Cmds LExprTP :=
  [.init "s" mty[bv32] (.const "0" mty[bv32]),
   .set "s" addNumsLExpr]

/--
info: ok: #[DECL (decl (s : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (0 : unsignedbv[32])),
 ASSIGN (assign (s : unsignedbv[32]) (((100 : unsignedbv[32]) + (200 : unsignedbv[32])) : unsignedbv[32]))]
-/
#guard_msgs in
#eval do let ans ← Imperative.Cmds.toGotoTransform Lambda.TEnv.default ExampleProgram2
          return format ans.instructions

-------------------------------------------------------------------------------

end

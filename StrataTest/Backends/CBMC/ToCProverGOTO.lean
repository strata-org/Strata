/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Backends.CBMC.LambdaToCProverGOTO
import Strata.DL.Imperative.ToCProverGOTO

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
  [.init (Lambda.Identifier.mk "s" ()) mty[bv32] (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)),
   .set (Lambda.Identifier.mk "s" ()) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100))]

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
  [.init (Lambda.Identifier.mk "s" ()) mty[bv32] (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)),
   .set (Lambda.Identifier.mk "s" ()) (addBV32LExpr (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 100)) (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 200)))]

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
  [.init (Lambda.Identifier.mk "x" ()) mty[bv32] (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)),
   .init (Lambda.Identifier.mk "y" ()) mty[bv32] (.const { underlying := (), type := mty[bv32] } (.bitvecConst 32 0)),
   .havoc (Lambda.Identifier.mk "x" ()),
   .havoc (Lambda.Identifier.mk "y" ()),
   .init (Lambda.Identifier.mk "z" ()) mty[bv32] (addBV32LExpr (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "x" ()) (some mty[bv32])) (.fvar { underlying := (), type := mty[bv32] } (Lambda.Identifier.mk "y" ()) (some mty[bv32])))]

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

end

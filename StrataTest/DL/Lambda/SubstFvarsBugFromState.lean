/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory

/-! # Iterated substFvar bug in substFvarsFromState (LState) -/

namespace Lambda

open LExpr LTy.Syntax LExpr.SyntaxMono
open Std (ToFormat Format format)

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

private def mkId (s : String) : Identifier Unit := ⟨s, ()⟩
private def mkFv (s : String) : LExpr TP.mono := .fvar () (mkId s) (some mty[int])
private def mkInt (n : Int) : LExpr TP.mono := .intConst () n
private def addOp : LExpr TP.mono := .op () (mkId "Int.Add") (some (LMonoTy.arrow mty[int] (LMonoTy.arrow mty[int] mty[int])))
private def mkAdd (a b : LExpr TP.mono) : LExpr TP.mono := .app () (.app () addOp a) b

-- State: x → y + 1, y → 0
private def testState : LState TP :=
  let σ : LState TP := LState.init
  let σ := { σ with state := σ.state.push [(mkId "x", (some mty[int], mkAdd (mkFv "y") (mkInt 1))),
                                            (mkId "y", (some mty[int], mkInt 0))] }
  σ

-- Expression: x + y
private def expr : LExpr TP.mono := mkAdd (mkFv "x") (mkFv "y")

private def result := LExpr.substFvarsFromState testState expr

-- Iterated [x→(y+1)][y→0] would produce `(0+1) + 0`. Simultaneous correctly gives `(y+1) + 0`.
/-- info: ((~Int.Add : (arrow int (arrow int int))) ((~Int.Add : (arrow int (arrow int int))) (y : int) #1) #0) -/
#guard_msgs in
#eval format result

end Lambda

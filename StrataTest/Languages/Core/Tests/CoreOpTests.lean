/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreOp

/-! ## Tests for CoreOp structured operator types -/

namespace Core

/-! ### Round-trip tests: toString ∘ ofString = id for all known operators -/

section RoundTrip

private def checkRoundTrip (name : String) : Bool :=
  CoreOp.toString (CoreOp.ofString name) == name

-- BV ops (representative sizes)
#guard checkRoundTrip "Bv8.Add"
#guard checkRoundTrip "Bv16.Sub"
#guard checkRoundTrip "Bv32.SDiv"
#guard checkRoundTrip "Bv64.ULt"
#guard checkRoundTrip "Bv1.Neg"
#guard checkRoundTrip "Bv32.Concat"
#guard checkRoundTrip "Bv32.Shl"
#guard checkRoundTrip "Bv8.SShr"
#guard checkRoundTrip "Bv2.Add"
#guard checkRoundTrip "Bv128.Mul"

-- BV Extract
#guard checkRoundTrip "Bv32.Extract_7_0"
#guard checkRoundTrip "Bv16.Extract_15_15"
#guard checkRoundTrip "Bv64.Extract_31_0"

-- Numeric ops
#guard checkRoundTrip "Int.Add"
#guard checkRoundTrip "Int.SafeDiv"
#guard checkRoundTrip "Int.ModT"
#guard checkRoundTrip "Int.Neg"
#guard checkRoundTrip "Int.Lt"
#guard checkRoundTrip "Real.Add"
#guard checkRoundTrip "Real.Div"
#guard checkRoundTrip "Real.Ge"

-- Bool ops
#guard checkRoundTrip "Bool.And"
#guard checkRoundTrip "Bool.Or"
#guard checkRoundTrip "Bool.Not"
#guard checkRoundTrip "Bool.Implies"
#guard checkRoundTrip "Bool.Equiv"

-- String ops
#guard checkRoundTrip "Str.Length"
#guard checkRoundTrip "Str.Concat"
#guard checkRoundTrip "Str.Substr"

-- Regex ops
#guard checkRoundTrip "Re.All"
#guard checkRoundTrip "Re.Star"
#guard checkRoundTrip "Re.None"

-- Map ops
#guard checkRoundTrip "const"
#guard checkRoundTrip "select"
#guard checkRoundTrip "update"

-- Sequence ops
#guard checkRoundTrip "Sequence.length"
#guard checkRoundTrip "Sequence.empty"
#guard checkRoundTrip "Sequence.append"

-- Trigger ops
#guard checkRoundTrip "Triggers.empty"
#guard checkRoundTrip "Triggers.addGroup"
#guard checkRoundTrip "TriggerGroup.empty"
#guard checkRoundTrip "TriggerGroup.addTrigger"

end RoundTrip

/-! ### Unknown ops fall through to .other -/

#guard CoreOp.ofString "myCustomFunc" == .other "myCustomFunc"
#guard CoreOp.ofString? "myCustomFunc" == none
#guard CoreOp.ofString? "Int.Add" == some (.numeric ⟨.int, .Add⟩)

/-! ### Predicate tests -/

#guard BvOpKind.isSigned .SDiv == true
#guard BvOpKind.isSigned .SMod == true
#guard BvOpKind.isSigned .SLt == true
#guard BvOpKind.isSigned .SShr == true
#guard BvOpKind.isSigned .Add == false
#guard BvOpKind.isSigned .ULt == false

#guard BvOpKind.isPredicate .ULt == true
#guard BvOpKind.isPredicate .SGe == true
#guard BvOpKind.isPredicate .Add == false

#guard NumericOpKind.hasPrecondition .SafeDiv == true
#guard NumericOpKind.hasPrecondition .SafeModT == true
#guard NumericOpKind.hasPrecondition .Add == false
#guard NumericOpKind.hasPrecondition .Div == false

/-! ### Structural pattern matching -/

#guard match CoreOp.ofString "Bv32.Add" with
  | .bv ⟨32, .Add⟩ => true | _ => false

#guard match CoreOp.ofString "Int.SafeDiv" with
  | .numeric ⟨.int, .SafeDiv⟩ => true | _ => false

#guard match CoreOp.ofString "Bool.Not" with
  | .bool .Not => true | _ => false

#guard match CoreOp.ofString "Bv16.Extract_15_15" with
  | .bvExtract 16 15 15 => true | _ => false

end Core

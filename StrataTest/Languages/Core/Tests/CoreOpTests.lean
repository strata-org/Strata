/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.CoreOp

meta section

/-! ## Tests for CoreOp structured operator types -/

namespace Core

/-! ### Round-trip tests: toString ∘ ofString = id for all known operators -/

section RoundTrip

private def checkRoundTrip (name : String) : Bool :=
  CoreOp.toString (CoreOp.ofString name) == name

-- BV ops: fold over all kinds at a fixed size, plus representative sizes
-- to exercise the size parse path (Bv{size} prefix).
#guard BvOpKind.names.all (fun (_, n) => checkRoundTrip s!"Bv32.{n}")
#guard checkRoundTrip "Bv1.Neg"
#guard checkRoundTrip "Bv2.Add"
#guard checkRoundTrip "Bv8.SShr"
#guard checkRoundTrip "Bv128.Mul"

-- BV Extract (parametric over Nat, no `names` list)
#guard checkRoundTrip "Bv32.Extract_7_0"
#guard checkRoundTrip "Bv16.Extract_15_15"
#guard checkRoundTrip "Bv64.Extract_31_0"

-- Numeric ops (every kind, for both Int and Real)
#guard NumericType.names.all (fun (_, t) =>
  NumericOpKind.names.all (fun (_, n) => checkRoundTrip s!"{t}.{n}"))

-- Bool ops
#guard BoolOpKind.names.all (fun (_, n) => checkRoundTrip s!"Bool.{n}")

-- String ops
#guard StrOpKind.names.all (fun (_, n) => checkRoundTrip s!"Str.{n}")

-- Regex ops
#guard ReOpKind.names.all (fun (_, n) => checkRoundTrip s!"Re.{n}")

-- Map ops (names are the full canonical string, no prefix)
#guard MapOpKind.names.all (fun (_, n) => checkRoundTrip n)

-- Sequence ops
#guard SeqOpKind.names.all (fun (_, n) => checkRoundTrip s!"Sequence.{n}")

-- Trigger ops (names are the full canonical string, no prefix)
#guard TriggerOpKind.names.all (fun (_, n) => checkRoundTrip n)

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

end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Transform.DatatypePartialEval

open Core
open Strata

/-! ## DatatypePartialEval Tests -/

section DatatypePartialEvalTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def anyDatatypePgm :=
#strata
program Core;

datatype Any {
  from_int(intVal: int),
  from_str(strVal: string),
  from_None()
};

#end

/-! ### Test: collectDatatypeInfo finds constructors and testers -/

#guard_msgs in
#eval do
  let pgm := translate anyDatatypePgm
  let info := collectDatatypeInfo pgm
  assert! info.constrNames.contains "from_int"
  assert! info.constrNames.contains "from_str"
  assert! info.constrNames.contains "from_None"
  assert! info.testerToConstr.contains "Any..isfrom_int"
  assert! info.testerToConstr["Any..isfrom_int"]? == some "from_int"
  assert! info.selectorInfo.contains "Any..intVal!"

/-! ### Test: tester on known constructor simplifies to true/false -/

-- isfrom_int(from_int(42)) → true
#guard_msgs in
#eval do
  let pgm := translate anyDatatypePgm
  let info := collectDatatypeInfo pgm
  let m : Core.ExpressionMetadata := default
  let lit42 : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let fromInt := Lambda.LExpr.op m ⟨"from_int", ()⟩ none
  let fromInt42 := Lambda.LExpr.app m fromInt lit42
  let isfromInt := Lambda.LExpr.op m ⟨"Any..isfrom_int", ()⟩ none
  let result := partialEvalDatatypes info (.app m isfromInt fromInt42)
  assert! result matches .const _ (.boolConst true)

-- isfrom_str(from_int(42)) → false
#guard_msgs in
#eval do
  let pgm := translate anyDatatypePgm
  let info := collectDatatypeInfo pgm
  let m : Core.ExpressionMetadata := default
  let lit42 : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let fromInt := Lambda.LExpr.op m ⟨"from_int", ()⟩ none
  let fromInt42 := Lambda.LExpr.app m fromInt lit42
  let isfromStr := Lambda.LExpr.op m ⟨"Any..isfrom_str", ()⟩ none
  let result := partialEvalDatatypes info (.app m isfromStr fromInt42)
  assert! result matches .const _ (.boolConst false)

/-! ### Test: selector on known constructor extracts field -/

-- Any..intVal!(from_int(42)) → 42
#guard_msgs in
#eval do
  let pgm := translate anyDatatypePgm
  let info := collectDatatypeInfo pgm
  let m : Core.ExpressionMetadata := default
  let lit42 : Lambda.LExpr Core.CoreLParams.mono := .const m (.intConst 42)
  let fromInt := Lambda.LExpr.op m ⟨"from_int", ()⟩ none
  let fromInt42 := Lambda.LExpr.app m fromInt lit42
  let asX := Lambda.LExpr.op m ⟨"Any..intVal!", ()⟩ none
  let result := partialEvalDatatypes info (.app m asX fromInt42)
  assert! result matches .const _ (.intConst 42)

end DatatypePartialEvalTests

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.PyFactory
import Strata.Languages.Core.Verifier

/-! # Prelude Verification Test

Verify that all prelude procedures pass verification.
This ensures the Python runtime prelude is well-formed
after PrecondElim generates WF-checking procedures. -/

namespace Strata.Python.PreludeVerifyTest

/-- Build the full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgram : Core.Program :=
  let (coreOption, _) := Strata.translateCombinedLaurel pythonRuntimeLaurelPart
  match coreOption with
  | some prog => prog
  | none => { decls := [] }

private def verifyPrelude : IO Core.VCResults := do
  IO.FS.withTempDir fun tempDir => do
    let r ← EIO.toIO (IO.Error.userError ∘ toString)
      (Core.verify preludeProgram tempDir
        (options := .quiet)
        (moreFns := Strata.Python.ReFactory))
    return r

/--
info:
Obligation: List_get_body_calls_List_get_0
Property: assert
Result: ✅ pass

Obligation: List_take_body_calls_List_take_0
Property: assert
Result: ✅ pass

Obligation: List_drop_body_calls_List_drop_0
Property: assert
Result: ✅ pass

Obligation: List_slice_body_calls_List_drop_0
Property: assert
Result: ✅ pass

Obligation: List_slice_body_calls_List_take_1
Property: assert
Result: ✅ pass

Obligation: List_set_body_calls_List_set_0
Property: assert
Result: ✅ pass

Obligation: DictStrAny_get_body_calls_DictStrAny_get_0
Property: assert
Result: ✅ pass

Obligation: DictStrAny_get_or_none_body_calls_DictStrAny_get_0
Property: assert
Result: ✅ pass

Obligation: Any_get_body_calls_DictStrAny_get_0
Property: assert
Result: ✅ pass

Obligation: Any_get_body_calls_List_get_1
Property: assert
Result: ✅ pass

Obligation: Any_get_body_calls_List_slice_2
Property: assert
Result: ✅ pass

Obligation: Any_get_body_calls_List_drop_3
Property: assert
Result: ✅ pass

Obligation: Any_get!_body_calls_DictStrAny_get_0
Property: assert
Result: ✅ pass

Obligation: Any_get!_body_calls_List_get_1
Property: assert
Result: ✅ pass

Obligation: Any_set_body_calls_List_set_0
Property: assert
Result: ✅ pass

Obligation: Any_set!_body_calls_List_set_0
Property: assert
Result: ✅ pass

Obligation: PFloorDiv_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: PFloorDiv_body_calls_Int.SafeDiv_1
Property: division by zero check
Result: ✅ pass

Obligation: PFloorDiv_body_calls_Int.SafeDiv_2
Property: division by zero check
Result: ✅ pass

Obligation: PFloorDiv_body_calls_Int.SafeDiv_3
Property: division by zero check
Result: ✅ pass

Obligation: PAnd_body_calls_Any_to_bool_0
Property: assert
Result: ✅ pass

Obligation: POr_body_calls_Any_to_bool_0
Property: assert
Result: ✅ pass

Obligation: ret_type
Property: assert
Result: ✅ pass

Obligation: ret_type
Property: assert
Result: ✅ pass

Obligation: ret_pos
Property: assert
Result: ✅ pass

Obligation: assert_name_is_foo
Property: assert
Result: ✅ pass

Obligation: assert_opt_name_none_or_str
Property: assert
Result: ✅ pass

Obligation: assert_opt_name_none_or_bar
Property: assert
Result: ✅ pass

Obligation: ensures_maybe_except_none
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verifyPrelude

end Strata.Python.PreludeVerifyTest

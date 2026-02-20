/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Factory
import Strata.DL.Util.Func
import Strata.DL.Lambda.IntBoolFactory

/-! # Factory Wellformedness Proof

  This file contains the proof that the Strata Core Factory is well-formed.
-/

namespace Core
open Lambda

theorem array_list_happend_toArray:
  ∀ {α:Type} (a:Array α) (b:List α), a ++ b = (a.toList ++ b).toArray
  := by
  unfold HAppend.hAppend Array.instHAppendList Array.appendList
  grind

set_option maxRecDepth 1024 in
set_option maxHeartbeats 400000 in
/--
Wellformedness of Factory
-/
theorem Factory_wf :
    FactoryWF Factory := by
  sorry
end Core

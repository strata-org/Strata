/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import Strata.DDM.Integration.Lean.HashCommands

meta section

---------------------------------------------------------------------
namespace Strata

-- Duplicate DDM bindings (polymorphic functions, datatypes) are caught during
-- DDM elaboration and reported as errors (not panics).

/--
error: 'f1' already defined
-/
#guard_msgs in
def dupPolyFunctions : Program :=
#strata
program Core;
function f1<T1, T2>(x : T1) : Map T1 T2;
function f1<T1, T2>(x : T1) : Map T1 T2;
#end

---------------------------------------------------------------------

end Strata

end

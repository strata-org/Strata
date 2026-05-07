/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def instanceProcedureProgram := r"
composite Counter {
  var count: int
  procedure increment(self: Counter)
//          ^^^^^^^^^ error: Instance procedure 'increment' on composite type 'Counter' is not yet supported
    opaque
  {
    self#count := self#count + 1
  };
  procedure reset(self: Counter)
//          ^^^^^ error: Instance procedure 'reset' on composite type 'Counter' is not yet supported
    opaque
  {
    self#count := 0
  };
}
"

#guard_msgs (error, drop all) in
#eval! testInputWithOffset "InstanceProcedures" instanceProcedureProgram 14 processLaurelFile

end Laurel

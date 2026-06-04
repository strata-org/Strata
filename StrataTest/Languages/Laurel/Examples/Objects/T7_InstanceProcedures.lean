/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util
open Strata

namespace Strata.Laurel

def instanceProcedureProgram := r"
composite Counter {
  var count: int
  procedure self_increment(self: Counter)
//          ^^^^^^^^^^^^^^ error: Instance procedure 'self_increment' on composite type 'Counter' is not yet supported
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

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 4:12-26  not-yet-implemented: Instance procedure 'self_increment' on composite type 'Counter' is not yet supported
9:12-17  not-yet-implemented: Instance procedure 'reset' on composite type 'Counter' is not yet supported -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
composite Counter {
  var count: int
  procedure self_increment(self: Counter)
    opaque
  {
    self#count := self#count + 1
  };
  procedure reset(self: Counter)
    opaque
  {
    self#count := 0
  };
}
#end

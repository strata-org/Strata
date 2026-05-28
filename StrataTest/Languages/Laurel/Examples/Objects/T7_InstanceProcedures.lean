/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExpect <|
#strata
program Laurel;
composite Counter {
  var count: int
  procedure self_increment(self: Counter)
//          ^^^^^^^^^^^^^^ not-yet-implemented: Instance procedure 'self_increment' on composite type 'Counter' is not yet supported
    opaque
  {
    self#count := self#count + 1
  };
  procedure reset(self: Counter)
//          ^^^^^ not-yet-implemented: Instance procedure 'reset' on composite type 'Counter' is not yet supported
    opaque
  {
    self#count := 0
  };
}
#end

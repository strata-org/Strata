/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Escape enforcement for *instance methods*. The escape analysis runs from
`resolve`, on the initial resolution — so method bodies are still inside their
composites and are walked there, and a method that calls another throwing method
resolves that callee's `throws` (the model records an instance procedure just as
it does a static one). Diagnostics name the method with a dot
(`Composite.method`), supplied by the walk since the method has not been lifted.
-/

-- A method that throws without declaring `throws` is rejected (the hole that
-- existed while the check only scanned top-level procedures).
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite Account {
  var balance: int
  procedure risky(self: Account)
    opaque
  {
    var e: Exception := new Exception;
    throw e
//  ^^^^^^^ error: procedure 'Account.risky' may let an exception of type 'Exception' escape; catch it with a `try`/`catch` or declare a `throws` clause
  };
}
procedure useIt() opaque {
  var a: Account := new Account;
  a#risky()
};
#end

-- A method that declares `throws` and throws it: allowed (verifies).
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite Account2 {
  var balance: int
  procedure risky(self: Account2)
    throws (e: Exception)
    opaque
  {
    var e: Exception := new Exception;
    throw e
  };
}
#end

-- method -> method propagation: `caller` invokes a throwing method without
-- catching it and without declaring `throws`. This is caught only because the
-- check runs after lifting, when `self#risky()`'s callee `throws` resolves.
#eval testLaurel <|
#strata
program Laurel;
composite Exception {}
composite Account3 {
  var balance: int
  procedure risky(self: Account3)
    throws (e: Exception)
    opaque
  {
    var e: Exception := new Exception;
    throw e
  };
  procedure caller(self: Account3)
    opaque
  {
    self#risky()
//  ^^^^^^^^^^^^ error: procedure 'Account3.caller' may let an exception of type 'Exception' escape; catch it with a `try`/`catch` or declare a `throws` clause
  };
}
#end

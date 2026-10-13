/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Escapes from *instance methods*. The static `throws` upper-bound check runs from
`resolve`, on the initial resolution — so method bodies are still inside their
composites and are walked there, and a method that calls another throwing method
resolves that callee's `throws` (the model records an instance procedure just as
it does a static one).

A method that declares no `throws` gets the same verification obligations as a
static procedure (see `Execution/Exceptions/UncaughtExceptions.lean`): they are
emitted after the method is lifted, so they apply to methods too.
-/

-- A method that throws without declaring `throws`: the reachable `throw` is reported.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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
//  ^^^^^^^ error: uncaught exception 'Exception' is not thrown does not hold
  };
}
procedure useIt() opaque {
  var a: Account := new Account;
  a#risky()
};
#end

-- A method that declares `throws` and throws it: allowed (verifies).
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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
-- catching it and without declaring `throws`, so the call is asserted not to throw
-- (and fails: `risky` always throws).
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
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
//  ^^^^^^^^^^^^ error: call does not throw an uncaught 'Exception' could not be proved
  };
}
#end

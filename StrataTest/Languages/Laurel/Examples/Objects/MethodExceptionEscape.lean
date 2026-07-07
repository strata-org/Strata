/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
E4 escape enforcement for *instance methods*. The escape analysis runs as the
`ExceptionEscapeCheck` pipeline pass, after `LiftInstanceProcedures` — so method
bodies are checked as ordinary (lifted) procedures, and a method that calls
another throwing method resolves that callee's `throws`. Diagnostics name the
lifted method with a dot (`Composite.method`).
-/

-- A method that throws without declaring `throws` is rejected (the hole that
-- existed while the check only scanned top-level procedures).
#eval testLaurel <|
#strata
program Laurel;
composite Account {
  var balance: int
  procedure risky(self: Account)
    opaque
  {
    var e: BaseException := new BaseException;
    throw e
//  ^^^^^^^ error: procedure 'Account.risky' may let an exception of type 'BaseException' escape; catch it with a `try`/`catch` or declare a `throws` clause
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
composite Account2 {
  var balance: int
  procedure risky(self: Account2)
    throws BaseException
    opaque
  {
    var e: BaseException := new BaseException;
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
composite Account3 {
  var balance: int
  procedure risky(self: Account3)
    throws BaseException
    opaque
  {
    var e: BaseException := new BaseException;
    throw e
  };
  procedure caller(self: Account3)
    opaque
  {
    self#risky()
//  ^^^^^^^^^^^^ error: procedure 'Account3.caller' may let an exception of type 'BaseException' escape; catch it with a `try`/`catch` or declare a `throws` clause
  };
}
#end

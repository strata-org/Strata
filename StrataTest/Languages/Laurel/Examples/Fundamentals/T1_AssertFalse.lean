/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
procedure foo() {
    assert true;
    assert false;
//  ^^^^^^^^^^^^^ error: assertion can be false
    assert false;
//  ^^^^^^^^^^^^^ error: assertion can be false
}

procedure bar() {
    assume false;
    assert false;
}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "AssertFalse" program 14 processLaurelFile

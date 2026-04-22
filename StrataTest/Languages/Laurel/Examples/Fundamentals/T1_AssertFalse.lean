/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
meta import StrataTest.Util.TestDiagnostics
meta import StrataTest.Languages.Laurel.TestExamples


meta section

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
procedure foo() {
    assert true;
    assert false;
//  ^^^^^^^^^^^^ error: assertion does not hold
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};

procedure bar() {
    assume false;
    assert false
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "AssertFalse" program 14 processLaurelFile

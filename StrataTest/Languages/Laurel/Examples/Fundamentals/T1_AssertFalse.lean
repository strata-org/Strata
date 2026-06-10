/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.Util.TestDiagnostics
meta import all StrataTest.Languages.Laurel.TestExamples

meta section

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
procedure foo()
  opaque
{
    assert true;
    assert false;
//  ^^^^^^^^^^^^ error: assertion does not hold
    assert false
//  ^^^^^^^^^^^^ error: assertion does not hold
};

procedure bar()
  opaque
{
    assume false;
    assert false
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "AssertFalse" program 17 processLaurelFile

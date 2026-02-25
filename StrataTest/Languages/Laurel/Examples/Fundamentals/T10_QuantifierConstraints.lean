/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples
open StrataTest.Util
namespace Strata.Laurel

def quantifierConstraintsProgram := r"
constrained nat = x: int where x >= 0 witness 0
constrained int32 = x: int where x >= -2147483648 && x <= 2147483647 witness 0

// Forall over unconstrained int — no constraint injection
procedure forallPlainInt()
  ensures forall(x: int) => x + 0 == x
{}

// Exists over constrained type — uses && not ==>
procedure existsConstrained()
  ensures exists(n: nat) => n == 0
{}

// Nested quantifiers with mixed constrained types
procedure nestedMixed()
  ensures forall(i: int32) => forall(j: nat) => j >= 0
{}

// Forall with constrained type in both quantifier and procedure param
procedure constrainedParam(n: nat)
  ensures forall(m: nat) => m <= n ==> m + 1 > 0
{}

// Exists nested inside forall, both constrained
procedure existsInForall()
  ensures forall(i: nat) => exists(j: nat) => j == i
{}
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "QuantifierConstraints" quantifierConstraintsProgram 5 processLaurelFile

end Strata.Laurel

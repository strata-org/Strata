/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def bvProgram := r"
// Bitvector types in procedure signatures and variable declarations.

// Parameters and return types
procedure identity32(x: bv 32) returns (r: bv 32) {
  r := x
};

procedure identity8(x: bv 8) returns (r: bv 8) {
  r := x
};

// Local variable with bv type
procedure localBv() returns (r: bv 16) {
  var x: bv 16 := r;
  r := x
};

// Opaque procedure returning bv64 — caller gets typed result
procedure opaqueBv64() returns (r: bv 64);
procedure callOpaque() returns (r: bv 64) {
  r := opaqueBv64()
};

// Mixed bv and int parameters
procedure mixedTypes(a: bv 32, b: int) returns (r: int) {
  r := b
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "BitvectorTypes" bvProgram 14 processLaurelFile

end Laurel
end Strata

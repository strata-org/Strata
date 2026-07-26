/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple
#strata
program Laurel;
// Bitvector types in procedure signatures and variable declarations.

// Parameters and return types
procedure identity32(x: bv 32) returns (r: bv 32)
  opaque
{
  r := x
};

procedure identity8(x: bv 8) returns (r: bv 8)
  opaque
{
  r := x
};

// Local variable with bv type
procedure localBv() returns (r: bv 16)
  opaque
{
  var x: bv 16 := r;
  r := x
};

// Opaque procedure returning bv64 — caller gets typed result
procedure opaqueBv64() returns (r: bv 64);
procedure callOpaque() returns (r: bv 64)
  opaque
{
  r := opaqueBv64()
};

// Mixed bv and int parameters
procedure mixedTypes(a: bv 32, b: int) returns (r: int)
  opaque
{
  r := b
};

// A parameterless `entry` so the concrete interpreter exercises bitvector
// values end-to-end. It uses only local bv literals (the procedures above are
// `opaque`, so a caller can't observe their results), keeping the assertions
// provable by the verifier and reproducible under concrete execution.
procedure runBitvectorLocals()
  entry
  opaque
{
  var x: bv 16 := 100 bv 16;
  assert x == 100 bv 16;
  var y: bv 8 := 3 bv 8;
  assert y == 3 bv 8
};
#end

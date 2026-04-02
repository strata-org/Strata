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
// Constrained integer types modelling bounded ranges over mathematical int.
// These exercise range constraints without wrapping semantics.

constrained i8     = x: int where x >= -128      && x <= 127       witness 0
constrained i16    = x: int where x >= -32768     && x <= 32767     witness 0
constrained u16    = x: int where x >= 0          && x <= 65535     witness 0
constrained i32    = x: int where x >= -2147483648 && x <= 2147483647 witness 0
constrained i64    = x: int where x >= -9223372036854775808 && x <= 9223372036854775807 witness 0

// --- Basic range checks ---

// Input constraints: callee can rely on range
procedure i8InRange(b: i8) {
  assert b >= -128;
  assert b <= 127
};

procedure i32InRange(n: i32) {
  assert n >= -2147483648;
  assert n <= 2147483647
};

procedure u16IsUnsigned(c: u16) {
  assert c >= 0;
  assert c <= 65535
};

// Output constraints: valid returns pass
procedure returnValidI8(): i8 { return 42 };
procedure returnValidI32(): i32 { return 1000000 };
procedure returnValidU16(): u16 { return 65 };

// Output constraints: out-of-range returns fail
procedure returnOverflowI8(): i8 {
//                            ^^ error: assertion does not hold
  return 128
};

procedure returnUnderflowI32(): i32 {
//                              ^^^ error: assertion does not hold
  return -2147483649
};

procedure returnNegativeU16(): u16 {
//                             ^^^ error: assertion does not hold
  return -1
};

// --- Arithmetic within range ---

// Addition that stays in range
procedure safeI8Add(a: i8, b: i8) returns (r: i32) {
  // i8 + i8 always fits in i32
  r := a + b;
  assert r >= -256;
  assert r <= 254
};

// Multiplication that stays in range
procedure safeI32Mul() returns (r: i32) {
  var a: i32 := 1000;
  var b: i32 := 1000;
  r := a * b;
  assert r == 1000000
};

// --- Cross-type widening ---

// i8 widens to i32 (always safe)
procedure i8ToI32(b: i8) returns (r: i32) {
  r := b
};

// u16 widens to i32 (always safe)
procedure u16ToI32(c: u16) returns (r: i32) {
  r := c
};

// i32 does NOT fit in i8 (requires check)
procedure i32ToI8(n: i32) returns (r: i8) {
//                                   ^^ error: assertion does not hold
  r := n
};

// --- Opaque procedure contracts ---

// Opaque procedure returning i32 — caller gets range guarantee
procedure opaqueI32(): i32;
procedure callerUsesRange() {
  var x: int := opaqueI32();
  assert x >= -2147483648;
  assert x <= 2147483647
};

// --- Quantifiers with constrained types ---

// All i8 values are valid i32 values
procedure allI8AreI32() {
  var b: bool := forall(b: i8) => b >= -2147483648 && b <= 2147483647;
  assert b
};

// There exists a u16 that is also a valid i8
procedure someU16IsI8() {
  var b: bool := exists(c: u16) => c <= 127;
  assert b
};
"

/-- error: Test failed -/
#guard_msgs(drop info, error) in
#eval testInputWithOffset "ConstrainedIntegerTypes" program 14 processLaurelFile

end Laurel
end Strata

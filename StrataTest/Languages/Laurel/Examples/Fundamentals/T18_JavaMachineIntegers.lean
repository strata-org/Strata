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
// Java machine integer types as constrained types over mathematical int.
// These model the range constraints without wrapping semantics.

constrained jbyte  = x: int where x >= -128      && x <= 127       witness 0
constrained jshort = x: int where x >= -32768     && x <= 32767     witness 0
constrained jchar  = x: int where x >= 0          && x <= 65535     witness 0
constrained jint   = x: int where x >= -2147483648 && x <= 2147483647 witness 0
constrained jlong  = x: int where x >= -9223372036854775808 && x <= 9223372036854775807 witness 0

// --- Basic range checks ---

// Input constraints: callee can rely on range
procedure byteInRange(b: jbyte) {
  assert b >= -128;
  assert b <= 127
};

procedure intInRange(n: jint) {
  assert n >= -2147483648;
  assert n <= 2147483647
};

procedure charIsUnsigned(c: jchar) {
  assert c >= 0
};

// Output constraints: valid returns pass
procedure returnValidByte(): jbyte { return 42 };
procedure returnValidInt(): jint { return 1000000 };
procedure returnValidChar(): jchar { return 65 };

// Output constraints: out-of-range returns fail
procedure returnOverflowByte(): jbyte {
//                               ^^^^^ error: assertion does not hold
  return 128
};

procedure returnUnderflowInt(): jint {
//                              ^^^^ error: assertion does not hold
  return -2147483649
};

procedure returnNegativeChar(): jchar {
//                              ^^^^^ error: assertion does not hold
  return -1
};

// --- Arithmetic within range ---

// Addition that stays in range
procedure safeByteAdd(a: jbyte, b: jbyte) returns (r: jint) {
  // byte + byte always fits in int
  r := a + b;
  assert r >= -256;
  assert r <= 254
};

// Multiplication that stays in range
procedure safeIntMul() returns (r: jint) {
  var a: jint := 1000;
  var b: jint := 1000;
  r := a * b;
  assert r == 1000000
};

// --- Cross-type widening ---

// byte widens to int (always safe)
procedure byteToInt(b: jbyte) returns (r: jint) {
  r := b
};

// char widens to int (always safe)
procedure charToInt(c: jchar) returns (r: jint) {
  r := c
};

// int does NOT fit in byte (requires check)
procedure intToByte(n: jint) returns (r: jbyte) {
//                                      ^^^^^ error: assertion does not hold
  r := n
};

// --- Opaque procedure contracts ---

// Opaque procedure returning jint — caller gets range guarantee
procedure opaqueJint(): jint;
procedure callerUsesRange() {
  var x: int := opaqueJint();
  assert x >= -2147483648;
  assert x <= 2147483647
};

// --- Quantifiers with constrained types ---

// All bytes are valid ints
procedure allBytesAreInts() {
  var b: bool := forall(b: jbyte) => b >= -2147483648 && b <= 2147483647;
  assert b
};

// There exists a char that is also a valid byte
procedure someCharIsByte() {
  var b: bool := exists(c: jchar) => c <= 127;
  assert b
};
"

/-- error: Test failed -/
#guard_msgs(drop info, error) in
#eval testInputWithOffset "JavaMachineIntegers" program 14 processLaurelFile

end Laurel
end Strata

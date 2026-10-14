/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testStringKO()
  returns (result: string)
  entry
  opaque
{
  var message: string := "Hello";
  assert(message == "Hell");
//^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold

  return message
};

procedure testStringOK()
returns (result: string)
  entry
  opaque
{
  var message: string := "Hello";
  assert(message == "Hello");

  return message
};

procedure testStringLiteralConcatOK()
  entry
  opaque
{
  var result: string := "a" ^ "b";
  assert(result == "ab")
};

procedure testStringLiteralConcatKO()
  entry
  opaque
{
  var result: string := "a" ^ "b";
  assert(result == "cd")
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testStringVarConcatOK()
  entry
  opaque
{
  var x: string := "Hello";
  var result: string := x ^ " World";
  assert(result == "Hello World")
};

procedure testStringVarConcatKO()
  entry
  opaque
{
  var x: string := "Hello";
  var result: string := x ^ " World";
  assert(result == "Goodbye")
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## Ordering (`<`, `<=`, `>`, `>=`) under concrete execution.

The prelude's `string` comparison overloads lower to Core's `Str.Lt`/`Str.Le`
(`CoreDefinitionsForLaurel.lean`). Those two carry a concrete evaluator, so the
INTERPRETER can reduce them. These blocks guard that evaluator and check the same
comparisons with the verifier, so the two have to agree.

The evaluator is the lexicographic order over CODE POINTS, matching the SMT
`str.<` the verifier uses. The non-ASCII pair that would distinguish a code-point
order from a byte order is pinned on the INTERPRETER ONLY, at the end of this
file: a non-ASCII literal cannot reach the solver at all today (it is emitted raw
and the solver rejects it as a non-printable character in a string literal), which
is a pre-existing limitation of the SMT string-literal emitter and not of these
operators.

These blocks run on the verifier and on both interpreters; the standalone Laurel
interpreter compares strings by code point too. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure testStringOrderingOK()
  entry
  opaque
{
  var a: string := "apple";
  var b: string := "banana";
  assert(a < b);
  assert(a <= b);
  assert(b > a);
  assert(b >= a);
  assert(a <= a);
  assert(a >= a)
};

procedure testStringOrderingPrefixOK()
  entry
  opaque
{
  var a: string := "ab";
  var b: string := "abc";
  assert(a < b);
  assert(!(b < a))
};

procedure testStringOrderingCaseOK()
  entry
  opaque
{
  var a: string := "Zebra";
  var b: string := "apple";
  assert(a < b)
};

procedure testStringOrderingKO()
  entry
  opaque
{
  var a: string := "apple";
  var b: string := "banana";
  assert(b < a)
//^^^^^^^^^^^^^ error: assertion does not hold
};

procedure testStringOrderingStrictKO()
  entry
  opaque
{
  var a: string := "apple";
  assert(a < a)
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### Non-ASCII ordering — INTERPRETER ONLY.

`skipVerification := true` is required because the two literals below are not
ASCII, and the SMT emitter writes them raw, so the solver rejects the query
outright (`Non-printable character in string literal`) — a pre-existing emitter
limitation, reproducible on a plain `assert a != "héllo"` with a symbolic `a` and
unrelated to ordering. Dropping the skip turns these into `strata-bug` diagnostics
rather than verdicts.

What this block buys that no ASCII pair can: `"hello" < "héllo"` holds under the
CODE-POINT order the evaluator implements. `é` is U+00E9, which is above `e`
(U+0065) as a code point and whose UTF-8 encoding also begins `0xC3`, so the two
orders agree here; what the block excludes is a *case-* or *locale-folding*
comparison, under which the pair would compare on `hello`/`hllo` and flip. -/

#eval testLaurelExecution { skipVerification := true } <|
#strata
program Laurel;
procedure testStringOrderingNonAsciiInterpretOnly()
  entry
  opaque
{
  var a: string := "hello";
  var b: string := "héllo";
  assert(a < b);
  assert(b > a);
  assert(!(b < a))
};
#end

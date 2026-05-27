/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

/-! Documents the current behaviour of the arithmetic typing rules.

    Two rules apply:

    - [⇐] Op-Arith — the *check* path. When the surrounding context
      provides an expected type (e.g. an annotated `var` declaration,
      a procedure parameter, an assignment target), the arithmetic
      expression is checked at that type, and the type is pushed into
      every operand. The error surfaces as "expected '<T>', got
      '<U>'" at the offending operand.

    - [⇒] Op-Arith — the *synth* path. Each operand is synthesized,
      required to be `Numeric` (`TInt` / `TReal` / `TFloat64` /
      `Unknown`), and the result type is the consistency LUB of the
      operand types: `Unknown ⊔ T = T`, `T ⊔ T = T`, anything else
      is rejected. Same shape as `Op-Eq` but extended to n operands
      and returning the LUB rather than `TBool`.

    Homogeneous numeric operands type-check via either path.
    Heterogeneous numeric operands (e.g. `int + real`) are rejected
    by both paths. The gradual `Unknown` wildcard flows freely. -/

def arithTypingProgram := r"
procedure homogeneousInt()
  opaque
{
  var x: int := 1 + 2;
  assert x == 3
};

procedure homogeneousReal()
  opaque
{
  var x: real := 1.5 + 2.5;
  assert x == 4.0
};

// [⇐] Op-Arith path: the outer 'real' expectation is pushed into both
// operands. Operand '1' synthesizes 'int' and fails the check.
procedure heterogeneousCheckPath()
  opaque
{
  var x: real := 1 + 2.0
//               ^ error: expected 'real', got 'int'
};

// [⇒] Op-Arith path: '<' synthesizes its operands, so '1 + 2.0' is
// resolved in synth position. The arithmetic synth rule synthesizes
// the operands ('int' and 'real') and folds them under
// consistencyLub. 'int' and 'real' are mutually inconsistent, so
// the fold fails: a single error fires at the operator's source
// position listing the operand types.
procedure heterogeneousSynthPath()
  opaque
{
  assert (1 + 2.0) < 5
//        ^^^^^^^ error: incompatible types
};

procedure unaryNegHomogeneous()
  opaque
{
  var a: int := 5;
  var b: int := -a;
  var c: real := 1.5;
  var d: real := -c;
  assert b == 0 - 5;
  assert d == 0.0 - 1.5
};

// Unknown (here from the unresolved name 'mystery') promotes to its
// neighbour under consistencyLub: 'Unknown + TInt' folds to TInt.
// The 'mystery is not defined' diagnostic is the *only* error.
procedure unknownFlowsFreely()
  opaque
{
  assert (mystery + 1) == 1
//        ^^^^^^^ error: 'mystery' is not defined
};
"

#guard_msgs(drop info, error) in
#eval testInputWithOffset "ArithTyping" arithTypingProgram 14 processLaurelFile

end Laurel

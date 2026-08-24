/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A hole must not hide a sibling operand's type error

Overload selection runs on argument types, and `Unknown` (an untyped hole `<?>`, an
undefined identifier, …) is a consistent subtype of *every* parameter type. So an
`Unknown` argument can never rule an overload out, and it matches all of them —
which is why `Synth.staticCall` suppresses its "no overload matches" / "ambiguous
call" diagnostics when a hole is involved: the report would either be spurious or
pile on top of an error the argument already reported for itself.

The suppression has to ask whether the hole is *why* selection failed, not merely
whether one is present. A concrete argument that no candidate accepts rules out
every overload on its own, whether or not a hole sits beside it — so `culpritArg`
checks for exactly that, and only a blameless hole silences the report.

`$eq`/`$neq` need matching care in `InferHoleTypes`. `CoreDefinitionsForLaurel`
declares them `procedure $eq<T>(x: T, y: T) : bool external`, so both slots are the
same uninstantiated `T` and neither can type a hole. Their operands must agree,
though, which makes the first non-hole sibling a sound guess — so `calleeParamTypes`
declines for these two names and `unresolvedOperatorArgType` supplies it, letting
`<?> == "hello"` infer `string`. Typing the hole from `T` would leave it with
nothing and report "could not infer type"; the general rule for a generic callee
blanks only the slots whose declared type mentions a type variable (`mentionsTVar`),
which is right where the slots differ, as in `select<K,V>(map: Map K V, key: K)`.
-/

-- Baseline, no hole: the operator reports.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure baseline() opaque {
  var y: int := 1 + "hello"
//              ^^^^^^^^^^^ error: no overload of '$add' matches the argument types
};
#end

-- With a hole beside the offending operand, the operator still reports: `"hello"`
-- is rejected by every overload of `$add` on its own, so the hole is not to blame.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeBesideWrongOperand() opaque {
  var y: int := <?> + "hello"
//              ^^^^^^^^^^^^^ error: no overload of '$add' matches the argument types
};
#end

-- A hole beside a *compatible* operand must stay silent and still select the `int`
-- overload, so `InferHoleTypes` can read its parameter types and type the hole.
-- This is what the suppression exists to protect.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeBesideCompatibleOperand() opaque {
  var y: int := 1 + <?>;
  assert y == y
};
#end

-- A hole compared against a string takes the sibling's type, so this is an
-- unknown *string* rather than an `int`/`string` mismatch reported as a bug.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeComparedToString(s: string) opaque {
  assume <?> == s;
  assert true
};
#end

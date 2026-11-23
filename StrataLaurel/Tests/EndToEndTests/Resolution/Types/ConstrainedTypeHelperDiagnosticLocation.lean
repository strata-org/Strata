/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A diagnostic about a constrained type's generated helper points at the type

Constrained-type elimination lowers each constrained type into a constraint function and a
witness procedure of its own. Core reports a type error in such a helper at the helper's
declaration unless the error carries a range of its own. The helpers carry the source of the
type declaration, so the error lands on the type the user wrote.

The constraint and the witness below call an `external` procedure, which Laurel resolution
accepts and Core's type checker rejects, as it cannot type the call. Only the stable headline
of the message is matched. -/

/-! The error in the constraint function has no range of its own, so it is placed at the
function's declaration: the name of the constrained type. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure isGood(x: int): bool external;
constrained good = x: int where isGood(x) witness 0
//          ^^^^ error: ❌ Type checking error.
#end

/-! The error in the witness procedure is placed at the statement that initializes the
witness, which carries the witness expression's source. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure pick(x: int): int external;
constrained picked = x: int where x >= 0 witness pick(0)
//                                               ^^^^^^^ error: ❌ Type checking error.
#end

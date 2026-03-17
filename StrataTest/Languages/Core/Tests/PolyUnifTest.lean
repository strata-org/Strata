/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Polymorphic Unification Test

Regression test for issue #460: type variables are correctly handled during
unification, allowing polymorphic function return types to pass through to
type inference.
-/

namespace Strata.PolyUnifTest

def polyUnifPgm : Program :=
#strata
program Core;

datatype Option (a: Type) {Some (unwrap: a), None ()};

function somefunc (s: string) : int ;

function OptString_len (o: Option(string)) : int {
  somefunc(Option..unwrap(o))
}

#end

/-- info: ok: datatype Option (a : Type) {(
  (Some(unwrap : a))),
  (None())
};
function somefunc (s : string) : int;
function OptString_len (o : (Option string)) : int {
  somefunc(Option..unwrap(o))
}-/
#guard_msgs in
#eval Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram polyUnifPgm)).fst

---------------------------------------------------------------------
-- Test 2: Incorrect polymorphic instantiation caught by type checking
---------------------------------------------------------------------

def polyUnifBadPgm : Program :=
#strata
program Core;

datatype Option (a: Type) {Some (unwrap: a), None ()};

function somefunc (s: string) : int ;

function BadFunc (o: Option(int)) : int {
  somefunc(Option..unwrap(o))
}

#end

/--
info: error: (1277-1350) Impossible to unify (arrow string int) with (arrow int $__ty4).
First mismatch: string with int.
-/
#guard_msgs in
#eval Core.typeCheck .quiet (TransM.run Inhabited.default (translateProgram polyUnifBadPgm)).fst

end Strata.PolyUnifTest

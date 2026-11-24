/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- The last block of `PolyProcedure.lean` under `--vcgen wp`. Each obligation's query defines
-- only the definitions it reads: the false assertion does not read `m`, so its query has neither
-- `m`'s definition nor the quantified axiom of `mapConst` that `m`'s right-hand side drains, and
-- the solver finds the counterexample, as in the default mode.
#eval testLaurelVerification
    (options := { verifyOptions :=
      { Core.VerifyOptions.quiet with solver := "z3", vcgen := .wp } }) <|
#strata
program Laurel;
datatype Tree<T> { Leaf(), Node(l: Tree<T>, v: T) }
procedure f<T>(x: T) returns (r: T) opaque ensures r == x { r := x };
procedure w<U, V>(u: U, v: V) opaque {
  var m := mapSet(mapEmpty(), 3, f(u));
  var t := Node(Leaf(), u);
  var s := Node(Leaf(), v);
  assert mapGet(m, 3) == u && Tree..v!(t) == u && Tree..v!(s) == v;
  assert Tree..v!(t) != u
//^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

procedure calleeTypeVariableInASlot()
  entry
  opaque
{
  w(1, true)
};
#end

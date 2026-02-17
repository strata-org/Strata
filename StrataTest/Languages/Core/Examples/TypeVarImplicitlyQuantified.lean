/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Fix for https://github.com/strata-org/Strata/issues/105.

import Strata.Languages.Core.Verifier

namespace Strata

private def pgm :=
#strata
program Core;

type set := Map int bool;

function diff(a : set, b : set) : set;
function lambda_0(l_0 : bool, l_1 : int, l_2 : int) : Map int int;

axiom [a1]: (forall a: set, b: set ::
  { diff(a, b) }
  diff(a, b) == diff(b, a)
);

axiom [a2]: (forall l_0: bool, l_1: int, l_2: int, y: int ::
  { lambda_0(l_0, l_1, l_2)[y] }
  (lambda_0(l_0, l_1, l_2)[y]) == (lambda_0(l_0, l_2, l_1)[y])
);
#end

def core_pgm := TransM.run Inhabited.default (translateProgram pgm)

/-- info: true -/
#guard_msgs in
#eval core_pgm.snd.isEmpty

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: type set := Map int bool;
function diff (a : (Map int bool), b : (Map int bool)) : Map int bool;
function lambda_0 (l_0 : bool, l_1 : int, l_2 : int) : Map int int;
axiom [a1]: forall x0 : (Map int bool) :: forall x1 : (Map int bool) ::  { diff(x0, x1) }
  diff(x0, x1) == diff(x1, x0);
axiom [a2]: forall x0 : bool :: forall x1 : int :: forall x2 : int :: forall x3 : int ::  { (lambda_0(x0, x1, x2))[x3] }
  (lambda_0(x0, x1, x2))[x3] == (lambda_0(x0, x2, x1))[x3];
-/
#guard_msgs in
#eval Core.typeCheck Options.default core_pgm.fst

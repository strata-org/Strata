/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
open Strata
open StrataDDM (Program)

/-!
# `have` type-check failure test

A `have x : T = v in body` binding must type check `v` against the binder
annotation `T`. A mismatch (here `have x : int = true`) is rejected by the
type checker rather than silently accepted.
-/

private def haveBadPgm : Program :=
#strata
program Core;

procedure TestHaveBad()
spec {
  ensures true;
}
{
  assert [bad]: have x : int = true in x == x;
};
#end

/--
info: error: (642-686) Impossible to unify (arrow int bool) with (arrow bool $__ty0).
First mismatch: int with bool.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram haveBadPgm) |>.fst).stripMetaData

end

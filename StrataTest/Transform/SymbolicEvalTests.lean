/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

/-! ## Symbolic evaluation phase tests -/

namespace Core.SymbolicEval.Tests

open Strata

private def translateCore (p : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-! The symbolic evaluation phase converts a program's procedures into
    obligation trees (assume/assert blocks combined with if *). -/

private def simpleProg :=
#strata
program Core;
procedure test(x : int) returns ()
spec { requires [pre]: x >= 0; }
{
  assert [a]: x >= 0;
};
#end

/--
info: program Core;

procedure obligations () returns ()
{
  assume [pre]: $__x0 >= 0;
  assert [a]: $__x0 >= 0;
  };
-/
#guard_msgs in
#eval do
  match typeCheckAndEval .quiet (translateCore simpleProg) with
  | .ok (oblProg, _) => IO.println (toString oblProg)
  | .error e => IO.println s!"Error: {e}"

end Core.SymbolicEval.Tests

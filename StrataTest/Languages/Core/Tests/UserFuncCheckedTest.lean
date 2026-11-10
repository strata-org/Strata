/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.InterpreterEvalSound
import StrataDDM.Integration.Lean.HashCommands

/-! # `userFuncChecked` on the factory of a type-checked program

The factory `Core.Program.run` builds for a type-checked program extends `Core.Factory` with the
program's functions. `Core.userFuncChecked` accepts every monomorphic function of this program
(constants, inlined and non-inlined functions with bodies, a quantified body, calls between
them) and rejects the
polymorphic `polyId`, which `Core.UserFuncWF` covers only through its `Prop` conditions. -/

open StrataDDM (Program)

namespace Strata

private def userFuncPgm : Program :=
#strata
program Core;
const fooConst : int;
inline function fooTest() : int { fooConst }

function barTest1(x : int) : int { int.add(x, 1) }
inline function barTest2(y : int) : bool { int.gt(y, 0) }
function allPositive(x : int) : bool { forall y : int :: int.gt(y, 0) ==> int.gt(int.add(y, x), 0) }

function barTest3(y : int) : int { if barTest2(y) then barTest1(y) else 0 }
function polyId<a>(y : a) : a { y }

procedure fooProc(a : int) {
  assert [barEq]: int.ge(barTest3(a), 0);
};
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: "[(fooConst, true), (fooTest, true), (barTest1, true), (barTest2, true), (allPositive, true), (barTest3, true), (polyId, false)]"
-/
#guard_msgs in
#eval do
  let (program, _) := Core.getProgram userFuncPgm
  match Core.typeCheck default program with
  | .error e => return s!"type error {e}"
  | .ok p =>
    match Core.Program.run p with
    | .error e => return s!"run error {e}"
    | .ok E =>
      let F := E.exprEnv.config.factory
      let users := F.toArray.toList.filter fun (fn : Lambda.LFunc Core.CoreLParams) =>
        (Core.Factory[fn.name.name]?).isNone
      return toString (users.map fun (fn : Lambda.LFunc Core.CoreLParams) =>
        (fn.name.name, Core.userFuncChecked F fn))

end Strata

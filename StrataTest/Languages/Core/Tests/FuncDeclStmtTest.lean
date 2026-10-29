/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
import StrataDDM.Integration.Lean.HashCommands

meta section
open Core
open Strata

private def translateResult (t : StrataDDM.Program) : Core.Program × Array String :=
  TransM.run Inhabited.default (translateProgram t)

def translate (t : StrataDDM.Program) : Core.Program :=
  (translateResult t).fst

private def transErrors (t : StrataDDM.Program) : Array String :=
  (translateResult t).snd

def simpleFuncDeclPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 1;
  function addX(y : int) : int
  { int.add(y, x) }
  var z : int := addX(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure test ()
{
  var x : int := 1;
  var addX : int -> int := fun y : int => int.add(y, x);
  var z : int := addX(5);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate simpleFuncDeclPgm).stripMetaData)))

-- Regression test for issue #1226: local function with ≥3 distinct-type args
-- Previously built wrong arrow type (int → real → bool → int instead of int → bool → real → int)
def localFuncDistinctTypesPgm :=
#strata
program Core;

procedure test()
{
  function f(x : int, b : bool, r : real) : int
  { x }
  var z : int := f(1, true, 0.0);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

procedure test ()
{
  var f : int -> bool -> real -> int := fun x : int => fun b : bool => fun r : real => x;
  var z : int := f(1, true, 0.0);
};
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck .default (translate localFuncDistinctTypesPgm).stripMetaData)))

-- Contract: mkArrow' followed by destructArrow preserves input order
#guard (Lambda.LMonoTy.mkArrow' .int [.int, .bool, .real]).destructArrow
    == [.int, .bool, .real, .int]

private def localFuncTypeParamsPgm :=
#strata
program Core;

procedure test()
{
  function id<T>(x : T) : T { x }
};

#end

/-- info: true -/
#guard_msgs in
#eval (transErrors localFuncTypeParamsPgm).any
  (· == "local function 'id': polymorphism in local functions is not supported")

private def localFuncPreconditionPgm :=
#strata
program Core;

procedure test()
{
  function positive(x : int) : int
    requires int.ge(x, 0);
  { x }
};

#end

/-- info: true -/
#guard_msgs in
#eval (transErrors localFuncPreconditionPgm).any
  (· == "local function 'positive': preconditions are not supported")

end

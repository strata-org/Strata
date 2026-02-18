/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate

open Core
open Strata

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

def simpleFuncDeclPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 1;
  function addX(y : int) : int
  { y + x }
  var z : int := addX(5);
};

#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: procedure test () returns ()
{
  var x : int := 1;
  function addX (y : int) : int { fvar!1 }
  var z : int := fvar!0(5);
  };


-- Errors encountered during conversion:
Unsupported construct in funcDeclToStatement: funcDecl without body not supported in statements: addX
Context: Global scope:
Scope 1:
Scope 2:
  boundVars: [x]
Scope 3:
  boundVars: [y]
-/
#guard_msgs in
#eval (Std.format ((Core.typeCheck Options.default (translate simpleFuncDeclPgm).stripMetaData)))

import Strata.Languages.Boole.Verify

open Strata

def local_func_decl_program :=
#strata
program Boole;

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
  function addX (y : int) : int { y + x }
  var z : int := addX(5);
  };
-/
#guard_msgs in
#eval Strata.Boole.typeCheck local_func_decl_program

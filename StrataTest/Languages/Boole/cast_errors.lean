/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Error cases for cast operators:
  1. `e as_sint` where `e : int`  → rejected (not a bitvector)
  2. `e as_int`  where `e` is a Map → rejected (not a bitvector or int)
  3. `e as_sint` where `e` is a Map → rejected (not a bitvector)
-/

private def helper (p : Strata.Program) : Except String Unit := do
  let prog ← (Boole.getProgram p).mapError toString
  let _ ← (Boole.toCoreProgram prog p.globalContext).mapError
    fun e => toString (e.format none)
  return ()

private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

-- (1) `as_sint` on an `int` — identity no-op (int is already signed), consistent with `as_int`
private def sintOnInt :=
#strata
program Boole;
procedure ok_sint(n: int) returns ()
spec {
  ensures n as_sint == n;
} {
  exit ok_sint;
};
#end

#guard (helper sintOnInt).isOk

-- (1b) `as_int` on an `int` — also identity no-op, locking in symmetric behaviour
private def asIntOnInt :=
#strata
program Boole;
procedure ok_as_int(n: int) returns ()
spec {
  ensures n as_int == n;
} {
  exit ok_as_int;
};
#end

#guard (helper asIntOnInt).isOk

-- (2) `as_int` on a `Map int bv8` — must be rejected
private def asIntOnMap :=
#strata
program Boole;
procedure bad_as_int(m: Map int bv8) returns ()
spec {
  ensures m as_int >= 0;
} {
  exit bad_as_int;
};
#end

#guard match helper asIntOnMap with
  | .error e => containsSubstr e "'as int' requires a bitvector source type"
  | .ok _ => false

-- (3) `as_sint` on a `Map int bv8` — must be rejected
private def sintOnMap :=
#strata
program Boole;
procedure bad_sint_map(m: Map int bv8) returns ()
spec {
  ensures m as_sint >= 0;
} {
  exit bad_sint_map;
};
#end

#guard match helper sintOnMap with
  | .error e => containsSubstr e "'as sint' requires a bitvector source type"
  | .ok _ => false

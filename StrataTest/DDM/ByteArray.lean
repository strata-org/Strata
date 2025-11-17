/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Integration.Lean

-- Minimal dialect to test dialects can be declared.
#guard_msgs in
#dialect
dialect Test;
op eval (b : ByteArray) : Command => "eval " b ";";
#end

/--
info: program Test;
eval b"ab\x12\r\\";
-/
#guard_msgs in
#eval IO.print #strata
program Test;
eval b"ab\x12\r\\";
#end

/--
error: expected Invalid hex escape sequence
-/
#guard_msgs in
#eval IO.print #strata
program Test;
eval b"\xgg";
#end

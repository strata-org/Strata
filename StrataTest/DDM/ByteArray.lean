/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

-- Minimal dialect to test dialects can be declared.
#guard_msgs in
#dialect
dialect Test;
op eval (b : ByteArray) : Command => "eval " b ";";
#end

#strata_gen Test

def bvExample := #strata
program Test;
eval b"ab\x12\r\\";
#end

/--
info: program Test;
eval b"ab\x12\r\\";
-/
#guard_msgs in
#eval IO.print bvExample

#guard
  match Command.ofAst bvExample.commands[0]! with
  | .ok (Command.eval _ bv) => bv.val == .mk ("ab\x12\r\\".toList.toArray.map Char.toUInt8)
  | _ => false

/--
error: expected Invalid hex escape sequence
-/
#guard_msgs in
#eval IO.print #strata
program Test;
eval b"\xgg";
#end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests direct emission of Core-implicit heap commands: a Laurel program with
field reads, field writes, allocation, and an embedded read is run through
`liftHeapExpressions` and then `translateLaurelToCoreImplicit`, and the
resulting `heapRead`/`heapWrite`/`heapAlloc` commands are checked. The output
must contain no explicit-encoding artifacts (`$heap`, `readField`,
`updateField`, `Box`).
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Strata.Languages.Laurel.LiftHeapExpressions
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

private def runImplicit (program : StrataDDM.Program)
    : IO (Option Core.Implicit.Program × List DiagnosticModel) := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  -- Lift heap reads/allocations into canonical position, then group/order
  -- declarations the same way the explicit pipeline does before translation.
  let lifted := liftHeapExpressions result.model result.program
  let unordered := transparencyPass lifted
  let compositeTypes := lifted.types.filter (fun t => match t with | .Composite _ => true | _ => false)
  let (unordered, model) := resolveUnorderedCore unordered (existingModel := some result.model) (additionalTypes := compositeTypes)
  let ordered := orderFunctionsAndProcedures unordered
  let initState : TranslateState := { model := model }
  let (prog?, st) := runTranslateM initState (translateLaurelToCoreImplicit {} ordered)
  return (prog?, st.coreDiagnostics)

private def printImplicit (program : StrataDDM.Program) : IO Unit := do
  let (prog?, _) ← runImplicit program
  match prog? with
  | some prog => IO.println (toString (Std.Format.pretty (Std.ToFormat.format prog)))
  | none => throw (IO.userError "implicit translation produced no program")

/-- Print the core diagnostics emitted during implicit translation (one per
line), for tests that assert a construct is rejected. -/
private def printImplicitDiagnostics (program : StrataDDM.Program) : IO Unit := do
  let (_, diags) ← runImplicit program
  for d in diags do
    IO.println d.message

/--
info: program CoreImplicit;


procedure manipulate [heap: none]
block $body {
  heapWrite(a, Account.balance, 1)
  var x : int;
  x := heapRead(a, Account.balance)
  var $h_0 : int;
  $h_0 := heapRead(a, Account.balance)
  var y : int := $h_0 + x;
  var b : Composite;
  b := heapAlloc(Account)
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
}
procedure manipulate(a: Account)
opaque {
  a#balance := 1;
  var x: int := a#balance;
  var y: int := a#balance + x;
  var b: Account := new Account
};
#end

-- Nested field read `(a#next)#balance` (inner-first lifting), a read in an
-- if-guard, a field write whose object is itself a read, and a field-write RHS
-- that reads a field. Confirms lifted temps are correctly typed even when the
-- read target is itself a field access.
/--
info: program CoreImplicit;


procedure nested [heap: none]
block $body {
  var $h_0 : Composite;
  $h_0 := heapRead(a, Node.next)
  var x : int;
  x := heapRead($h_0, Node.balance)
  var $h_1 : int;
  $h_1 := heapRead(a, Node.balance)
  if $h_1 > 0 {
    var $h_2 : Composite;
    $h_2 := heapRead(a, Node.next)
    var $h_3 : int;
    $h_3 := heapRead($h_2, Node.balance)
    heapWrite(a, Node.balance, $h_3)
  } else {
    ⏎
  }
  var $h_4 : Composite;
  $h_4 := heapRead(a, Node.next)
  var $h_5 : int;
  $h_5 := heapRead(a, Node.balance)
  heapWrite($h_4, Node.balance, $h_5 + 1)
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Node {
  var balance: int
  var next: Node
}
procedure nested(a: Node)
opaque {
  var x: int := (a#next)#balance;
  if a#balance > 0 then {
    a#balance := (a#next)#balance
  };
  (a#next)#balance := a#balance + 1
};
#end

-- A while-guard reading a field exercises guard duplication: the read is lifted
-- before the loop and refreshed on the back-edge (end of body).
/--
info: program CoreImplicit;


procedure consume [heap: none]
block $body {
  var $h_0 : int;
  $h_0 := heapRead(self, Account.balance)
  while $h_0 > 0 {
    var $h_1 : int;
    $h_1 := heapRead(self, Account.balance)
    heapWrite(self, Account.balance, $h_1 - 1)
    $h_0 := heapRead(self, Account.balance)
  }
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
}
procedure consume(self: Account)
opaque {
  while (self#balance > 0) {
    self#balance := self#balance - 1
  }
};
#end

-- Short-circuit `&&` whose RHS reads a field: DesugarShortCircuit converts it
-- to an if-then-else first, then both operand reads are lifted. The RHS read is
-- lifted unconditionally (eager) — sound for total heap reads.
/--
info: program CoreImplicit;


procedure shortCircuit [heap: none]
block $body {
  var $h_0 : bool;
  $h_0 := heapRead(self, Account.ok)
  var $h_1 : int;
  $h_1 := heapRead(self, Account.balance)
  var z : bool := if $h_0 then $h_1 > 0 else false;
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
  var ok: bool
}
procedure shortCircuit(self: Account)
opaque {
  var z: bool := self#ok && (self#balance > 0)
};
#end

-- Compound while-guard with two reads: both are duplicated on the back-edge.
/--
info: program CoreImplicit;


procedure compoundGuard [heap: none]
block $body {
  var $h_0 : int;
  $h_0 := heapRead(self, Account.balance)
  var $h_1 : int;
  $h_1 := heapRead(self, Account.limit)
  while $h_0 > $h_1 {
    var $h_2 : int;
    $h_2 := heapRead(self, Account.balance)
    heapWrite(self, Account.balance, $h_2 - 1)
    $h_0 := heapRead(self, Account.balance)
    $h_1 := heapRead(self, Account.limit)
  }
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
  var limit: int
}
procedure compoundGuard(self: Account)
opaque {
  while (self#balance > self#limit) {
    self#balance := self#balance - 1
  }
};
#end

-- A read assigned to an output parameter.
/--
info: program CoreImplicit;


procedure retRead [heap: none]
ensures r == retRead$asFunction(self)
block $body {
  r := heapRead(self, Account.balance)
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
}
procedure retRead(self: Account) returns (r: int)
opaque {
  r := self#balance
};
#end

-- Three-deep nested read `((a#next)#next)#value` lifts inner-to-outer.
/--
info: program CoreImplicit;


procedure deep [heap: none]
ensures r == deep$asFunction(a)
block $body {
  var $h_0 : Composite;
  $h_0 := heapRead(a, Node.next)
  var $h_1 : Composite;
  $h_1 := heapRead($h_0, Node.next)
  r := heapRead($h_1, Node.value)
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Node {
  var value: int
  var next: Node
}
procedure deep(a: Node) returns (r: int)
opaque {
  r := ((a#next)#next)#value
};
#end

-- `new Account` as a call argument lifts to a temp, then the call uses it.
/--
info: program CoreImplicit;




procedure takesAccount [heap: none]
block $body {
  var b : bool := true;
}

procedure makesAndPasses [heap: none]
block $body {
  var $h_0 : Composite;
  $h_0 := heapAlloc(Account)
  call takesAccount($h_0);
}
-/
#guard_msgs in
#eval printImplicit
#strata
program Laurel;
composite Account {
  var balance: int
}
procedure takesAccount(x: Account)
opaque {
  var b: bool := true
};
procedure makesAndPasses()
opaque {
  takesAccount(new Account)
};
#end

-- A field read in a specification (here a postcondition) is rejected: implicit
-- mode has no expression-level heap-read form, and specs have no statement slot
-- for a heapRead. See the design's spec discussion.
/--
info: field reads in specifications are not yet supported in implicit heap mode
-/
#guard_msgs in
#eval printImplicitDiagnostics
#strata
program Laurel;
composite Account {
  var balance: int
}
procedure withSpec(self: Account) returns (r: int)
opaque
  ensures r == self#balance
{
  r := self#balance
};
#end

end Laurel

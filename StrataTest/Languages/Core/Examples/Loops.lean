/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Transform.StructuredToUnstructured

---------------------------------------------------------------------
namespace Strata

def gaussPgm :=
#strata
program Core;

procedure sum(n : int) returns (s : int)
spec {
  requires (n >= 0);
  ensures (s == ((n * (n + 1)) div 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant s == (i * (i + 1)) div 2
  {
    i := (i + 1);
    s := (s + i);
  }
};
#end

def singleCFG (p : Program) : Imperative.CFG String (Imperative.DetBlock String Core.Command Core.Expression) :=
  let corePgm : Core.Program := TransM.run Inhabited.default (translateProgram p) |>.fst
  let proc := match corePgm.decls.filter (λ d => d.kind = .proc) with | (.proc p _) :: _ => p | _ => panic!"No procedure!"
  Imperative.stmtsToCFG proc.body

/--
info: Entry: l_3

[l_3:
   [init (i : int), i := #0, s := #0]
   cgoto #true loop_entry_1 loop_entry_1,
 loop_entry_1:
   [assert [inv] ((~Int.Le : (arrow int (arrow int bool))) #0 (i : int)),
 assert [inv] ((~Int.Le : (arrow int (arrow int bool))) (i : int) (n : int)),
 assert [inv] ((s : int) == ((~Int.Div : (arrow int (arrow int int)))
   ((~Int.Mul : (arrow int (arrow int int))) (i : int) ((~Int.Add : (arrow int (arrow int int))) (i : int) #1))
   #2))]
   cgoto ((~Int.Lt : (arrow int (arrow int bool))) (i : int) (n : int)) l_2 end_0,
 l_2:
   [i := ((~Int.Add : (arrow int (arrow int int))) (i : int) #1),
 s := ((~Int.Add : (arrow int (arrow int int))) (s : int) (i : int))]
   cgoto #true loop_entry_1 loop_entry_1,
 end_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG gaussPgm))

/--
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: sum_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify gaussPgm (options := Options.quiet)

def nestedPgm :=
#strata
program Core;

const top : int;
axiom [top100]: top == 100;

procedure nested(n : int) returns (s : int)
spec {
  requires [n_pos]: n > 0;
  requires [n_lt_top]: n < top;
} {
  var x: int;
  var y: int;
  x := 0;
  while (x < n)
    invariant x >= 0 && x <= n && n < top
  {
    y := 0;
    while (y < x)
      invariant y >= 0 && y <= x
    {
      y := y + 1;
    }
    x := x + 1;
  }
};
#end

/--
info: Entry: l_6

[l_6:
   [init (x : int), init (y : int), x := #0]
   cgoto #true loop_entry_1 loop_entry_1,
 loop_entry_1:
   [assert [inv] ((~Bool.And : (arrow bool (arrow bool bool)))
  ((~Bool.And : (arrow bool (arrow bool bool)))
   ((~Int.Ge : (arrow int (arrow int bool))) (x : int) #0)
   ((~Int.Le : (arrow int (arrow int bool))) (x : int) (n : int)))
  ((~Int.Lt : (arrow int (arrow int bool))) (n : int) (~top : int)))]
   cgoto ((~Int.Lt : (arrow int (arrow int bool))) (x : int) (n : int)) l_5 end_0,
 l_5:
   [y := #0]
   cgoto #true loop_entry_3 loop_entry_3,
 loop_entry_3:
   [assert [inv] ((~Bool.And : (arrow bool (arrow bool bool)))
  ((~Int.Ge : (arrow int (arrow int bool))) (y : int) #0)
  ((~Int.Le : (arrow int (arrow int bool))) (y : int) (x : int)))]
   cgoto ((~Int.Lt : (arrow int (arrow int bool))) (y : int) (x : int)) l_4 l_2,
 l_4:
   [y := ((~Int.Add : (arrow int (arrow int int))) (y : int) #1)]
   cgoto #true loop_entry_3 loop_entry_3,
 l_2:
   [x := ((~Int.Add : (arrow int (arrow int int))) (x : int) #1)]
   cgoto #true loop_entry_1 loop_entry_1,
 end_0:
   []
   finish]
-/
#guard_msgs in
#eval (Std.format (singleCFG nestedPgm))

/--
info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify nestedPgm (options := Options.quiet)

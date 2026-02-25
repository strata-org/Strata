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
info: Entry: l_6

[l_6:
   [init (i : int), i := #0, s := #0]
   cgoto #true loop_entry_1 loop_entry_1,
 loop_entry_1:
   [assert [inv] ((~Bool.And : (arrow bool (arrow bool bool)))
  ((~Bool.And : (arrow bool (arrow bool bool)))
   ((~Int.Le : (arrow int (arrow int bool))) #0 (i : int))
   ((~Int.Le : (arrow int (arrow int bool))) (i : int) (n : int)))
  ((s : int) == ((~Int.Div : (arrow int (arrow int int)))
    ((~Int.Mul : (arrow int (arrow int int))) (i : int) ((~Int.Add : (arrow int (arrow int int))) (i : int) #1))
    #2)))]
   cgoto ((~Int.Lt : (arrow int (arrow int bool))) (i : int) (n : int)) l_3 end_0,
 l_3:
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
info: [Strata.Core] Type checking succeeded.


VCs:
Label: entry_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
sum_requires_0: $__n0 >= 0
Obligation:
true && 0 <= $__n0 && true

Label: arbitrary_iter_maintain_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n0
assume_guard_0: $__i3 < $__n0
assume_invariant_0: 0 <= $__i3 && $__i3 <= $__n0 && $__s4 == $__i3 * ($__i3 + 1) div 2
sum_requires_0: $__n0 >= 0
Obligation:
0 <= $__i3 + 1 && $__i3 + 1 <= $__n0 && $__s4 + ($__i3 + 1) == ($__i3 + 1) * ($__i3 + 1 + 1) div 2

Label: sum_ensures_1
Property: assert
Assumptions:
sum_requires_0: $__n0 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n0 then (0 < $__n0) else true
assume_guard_0: if 0 < $__n0 then ($__i3 < $__n0) else true
assume_invariant_0: if 0 < $__n0 then (0 <= $__i3 && $__i3 <= $__n0 && $__s4 == $__i3 * ($__i3 + 1) div 2) else true
not_guard_0: if 0 < $__n0 then !($__i5 < $__n0) else true
invariant_0: if 0 < $__n0 then (0 <= $__i5 && $__i5 <= $__n0 && $__s6 == $__i5 * ($__i5 + 1) div 2) else true
<label_ite_cond_false: !(~Int.Lt i n)>: if if 0 < $__n0 then false else true then if 0 < $__n0 then false else true else true
Obligation:
if 0 < $__n0 then $__s6 else 0 == $__n0 * ($__n0 + 1) div 2

---
info:
Obligation: entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass

Obligation: sum_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify gaussPgm

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
info: Entry: l_8

[l_8:
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
Obligation: entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify nestedPgm (options := Options.quiet)

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

/-!
`const x : T := v` declares a constant together with its value. The value is
recorded on the declaration, so no SMT-level axiom relating `x` to `v` is
needed.

Constants take the same defaults as functions: as for a function definition,
marking the declaration `inline` additionally substitutes the value at each use
during symbolic evaluation, which is what folds the obligations below to `true`.
Without the marker the value still reaches the solver, as the final test shows.
-/

def constValuePgm :=
#strata
program Core;

inline const x : int := 5;
inline const y : int := int.add(x, 2);
inline const b : bool := true;

procedure P() {
  assert [x_value]: x == 5;
  assert [y_value]: y == 7;
  assert [b_value]: b;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: x_value
Property: assert
Obligation:
true

Label: y_value
Property: assert
Obligation:
true

Label: b_value
Property: assert
Obligation:
true

---
info:
Obligation: x_value
Property: assert
Result: ✅ pass

Obligation: y_value
Property: assert
Result: ✅ pass

Obligation: b_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify constValuePgm

---------------------------------------------------------------------

/-- The value of a constant is usable by the type checker, which rejects a
right-hand side whose type differs from the declared one. -/
def constValueIllTypedPgm :=
#strata
program Core;

const x : int := true;
#end

/--
error: ❌ Type checking error.
Impossible to unify int with bool.
-/
#guard_msgs in
#eval Core.verify constValueIllTypedPgm

---------------------------------------------------------------------

/-- Constants with values interact with other declarations: here the value of
`limit` is inlined into a procedure's specification. -/
def constValueSpecPgm :=
#strata
program Core;

inline const limit : int := 10;

procedure bounded(n : int, out r : int)
  spec {
    requires [n_pos]: int.ge(n, 0);
    ensures [r_bounded]: int.le(r, 10);
  }
{
  if (int.le(n, limit)) {
    r := n;
  } else {
    r := limit;
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: r_bounded
Property: assert
Assumptions:
n_pos: int.ge(n@1, 0)
<label_ite_cond_true: int.le(n, limit)>: if int.le(n@1, 10) then int.le(n@1, 10) else true
<label_ite_cond_false: !(int.le(n, limit))>: if if int.le(n@1, 10) then false else true then if int.le(n@1, 10) then false else true else true
Obligation:
int.le(if int.le(n@1, 10) then n@1 else 10, 10)

---
info:
Obligation: r_bounded
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify constValueSpecPgm

---------------------------------------------------------------------

/-- Without the `inline` marker the value is not substituted into uses, so the
obligation still mentions `x`. The declaration itself carries the value, so the
solver discharges the obligation with no axiom relating `x` to `5`. -/
def constValueNoInlinePgm :=
#strata
program Core;

const x : int := 5;

procedure P() {
  assert [x_value]: x == 5;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: x_value
Property: assert
Obligation:
x == 5

---
info:
Obligation: x_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify constValueNoInlinePgm

end Strata

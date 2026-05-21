/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end coverage of user-written `old(...)` in Laurel postconditions.

`old(e)` parses to `StmtExpr.Old e`, is pushed inward by `PushOldInward`
until each `Old` immediately wraps a variable reference, then translated
to Core's two-state semantics via `LaurelToCoreTranslator`. Together with
the inout-`$heap` parameter introduced by `HeapParameterization`, this
lets postconditions relate the pre- and post-state of the heap.

The procedures below exercise:
- `old` of a heap field read (basic two-state).
- `old` over a non-trivial sub-expression (PushOldInward distribution).
- `old` of a comparison and a nested arithmetic expression.
- `old` inside a universally quantified frame condition.
- `old` inside an `if-then-else` postcondition.
- `old(old(...))` idempotence.
- Multiple modifies / multiple `old`-using ensures clauses.
- Negative cases: wrong body, wrong `old` reference.
- A caller asserting the post-state via the implicit pre-state snapshot.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util

namespace Strata
namespace Laurel

def program := r"
composite Cell {
  var value: int
  var flag: bool
}

// ----- 1. Basic two-state postcondition -----

procedure bumpCell(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies c
{
  c#value := c#value + 1
};

procedure bumpCellWrong(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  modifies c
{
  c#value := c#value + 2
};

procedure bumpCellCaller()
  opaque
{
  var c: Cell := new Cell;
  var pre: int := c#value;
  bumpCell(c);
  assert c#value == pre + 1
};

// ----- 2. `old` distributing through sub-expressions -----

// PushOldInward must push the outer `old` past `+`, so the translator
// only sees `old` wrapping a variable.
procedure addTwoSubexpr(c: Cell)
  opaque
  ensures c#value == old(c#value + 1) + 1
  modifies c
{
  c#value := c#value + 2
};

// Nested arithmetic: `old(2 * c#value + 3)` distributes through both
// `*` and `+`, leaving `2 * old(c#value) + 3` after lowering.
procedure linearTransform(c: Cell)
  opaque
  ensures c#value == 2 * old(c#value) + 3
  modifies c
{
  c#value := 2 * c#value + 3
};

// ----- 3. `old` of a comparison / boolean field -----

procedure flipFlag(c: Cell)
  opaque
  ensures c#flag == !old(c#flag)
  modifies c
{
  c#flag := !c#flag
};

procedure compareOldAndNew(c: Cell)
  opaque
  ensures old(c#value) < c#value
  modifies c
{
  c#value := c#value + 5
};

// ----- 4. `old(old(e)) == old(e)` idempotence -----

procedure doubleOldIsOld(c: Cell)
  opaque
  ensures c#value == old(old(c#value)) + 1
  modifies c
{
  c#value := c#value + 1
};

// ----- 5. Quantified frame: every other cell is unchanged -----

// The postcondition frames every Cell besides `c` to its pre-state.
// This is the user-written analogue of the synthetic frame condition
// emitted by ModifiesClauses.
procedure framedBump(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  ensures forall(other: Cell) => other != c ==> other#value == old(other#value)
  modifies c
{
  c#value := c#value + 1
};

procedure framedBumpCaller()
  opaque
{
  var c: Cell := new Cell;
  var d: Cell := new Cell;
  var preD: int := d#value;
  framedBump(c);
  assert d#value == preD
};

// ----- 6. `if-then-else` in postcondition with `old` -----

procedure conditionalUpdate(c: Cell)
  opaque
  ensures c#value == if old(c#flag) then old(c#value) + 1 else old(c#value)
  modifies c
{
  if c#flag then { c#value := c#value + 1 }
};

// ----- 7. Multiple modifies + multiple old-using ensures -----

procedure bumpBoth(c: Cell, d: Cell)
  requires c != d
  opaque
  ensures c#value == old(c#value) + 1
  ensures d#value == old(d#value) + 2
  ensures c#flag == old(c#flag)
  modifies c
  modifies d
{
  c#value := c#value + 1;
  d#value := d#value + 2
};

procedure bumpBothCaller()
  opaque
{
  var c: Cell := new Cell;
  var d: Cell := new Cell;
  var preC: int := c#value;
  var preD: int := d#value;
  // c != d holds because both come from `new Cell`.
  bumpBoth(c, d);
  assert c#value == preC + 1;
  assert d#value == preD + 2
};

// ----- 8. Negative: ensures asserts the wrong `old` relation -----

procedure wrongOldRelation(c: Cell)
  opaque
  ensures c#value == old(c#value) - 1
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  modifies c
{
  c#value := c#value + 1
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "OldHeapTwoState" program 32 processLaurelFile

end Laurel
end Strata

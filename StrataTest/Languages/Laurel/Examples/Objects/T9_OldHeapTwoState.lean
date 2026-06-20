/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end coverage of user-written `old(...)` in Laurel postconditions.

`old(e)` parses to `StmtExpr.Old e`, is pushed inward by `PushOldInward`
until each `Old` immediately wraps a variable reference, then translated
to Core's two-state semantics via `LaurelToCoreTranslator`. Combined with
the inout-`$heap` parameter introduced by `HeapParameterization`, this
lets postconditions relate the pre- and post-state of the heap.

The procedures below exercise:
- `old` of a heap field read (basic two-state).
- `old` of a non-trivial arithmetic sub-expression (PushOldInward
  distributes through `+` and `*`).
- `old` of a unary `!` and of a `<` comparison.
- `old(old(...))` of a sub-expression (collapse + distribution).
- `old` inside a universal quantifier body.
- `old` inside an `if-then-else` postcondition.
- Multiple `modifies` / multiple `old`-using ensures clauses.
- Modifies-wildcard combined with `old`.
- Wrong-body and wrong-`old`-relation negative cases.
- Warning when `old(...)` mentions no inout (no-op `old`).
- A caller asserting the post-state via the implicit pre-state snapshot.

Each positive postcondition is engineered so that, were `old(...)` to
be silently dropped, the postcondition would reduce to a post-state
equation that the body falsifies — the procedure would fail to verify.
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Util.LaurelDebugPipeline

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

// ----- 2. `old` distributing through arithmetic sub-expressions -----

// PushOldInward must push the outer `old` past `+`, leaving
// `old(c#value) + 1` for the translator to handle.
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

// ----- 3. `old` of a boolean: unary `!` and comparison -----

procedure flipFlag(c: Cell)
  opaque
  ensures c#flag == !old(c#flag)
  modifies c
{
  c#flag := !c#flag
};

// `old(c#value < d#value)` distributes through `<`, leaving
// `old(c#value) < old(d#value)`. The body inverts the ordering, so this
// postcondition can only hold when `old` actually refers to the
// pre-state: without two-state semantics the postcondition reduces to
// the (now false) post-state comparison.
procedure recallPreOrdering(c: Cell, d: Cell)
  requires c != d
  requires c#value < d#value
  opaque
  ensures old(c#value < d#value)
  modifies c
  modifies d
{
  c#value := 100;
  d#value := -100
};

// ----- 4. Nested `old(old(e))`: inner `old` is a no-op, warning emitted -----

// PushOldInward warns about the redundant inner `old` and drops it; the
// outer `old` then distributes past `+`, leaving `2 * old(c#value) + 1`,
// which the body satisfies.
procedure nestedOldWarns(c: Cell)
  opaque
  ensures c#value == old(old(c#value + c#value)) + 1
//                       ^^^^^^^^^^^^^^^^^^^^^^ warning: nested `old(...)` has no effect
  modifies c
{
  c#value := 2 * c#value + 1
};

// ----- 5. `old` inside a universal quantifier body -----

// The postcondition uses `old` inside `forall`: for the modified cell
// `c`, post > pre strictly. This would be unprovable without `old`
// (it'd reduce to `c#value > c#value`). The synthetic frame for every
// other cell does not entail this strict inequality, so the verifier
// must use the explicit `c#value > old(c#value)` claim.
procedure strictBumpInForall(c: Cell)
  opaque
  ensures forall(other: Cell) => other == c ==> other#value > old(other#value)
  modifies c
{
  c#value := c#value + 1
};

// ----- 6. `if-then-else` in postcondition with `old` on both branches -----

// The body conditionally bumps `c#value`. The postcondition relates
// post- to pre-state through an `if` whose condition is itself an
// `old(...)` field read.
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

// ----- 8. `modifies *` with an `old`-using ensures -----

// Wildcard modifies takes a different path through ModifiesClauses;
// `old(c#value)` should still resolve to the pre-state.
procedure bumpUnderWildcard(c: Cell)
  opaque
  ensures c#value == old(c#value) + 1
  modifies *
{
  c#value := c#value + 1
};

// ----- 9. Negative: ensures asserts the wrong `old` relation -----

procedure wrongOldRelation(c: Cell)
  opaque
  ensures c#value == old(c#value) - 1
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  modifies c
{
  c#value := c#value + 1
};

// ----- 10. `old(...)` over an expression with no inout: warning, no effect -----

procedure noEffectOld(c: Cell)
  opaque
  ensures old(42) == 42
//        ^^^^^^^ warning: `old(...)` has no effect
  modifies c
{
  c#value := c#value + 1
};
"

#guard_msgs (drop info, error) in
#eval testInputWithOffset "OldHeapTwoState" program 32 processLaurelFile

end Laurel
end Strata

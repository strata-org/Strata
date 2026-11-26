/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # End-to-end `--vcgen uwp/usp` test for a guarded Core program

Verifies a structured Core procedure through the unstructured passification VC
generator (`--vcgen uwp` and `--vcgen usp`), exercising the full
`Strata.Core.verifyProgram` pipeline (`Core.passiveVCGenPhases`): call
elimination, CFG loop elimination, precondition checks, type checking, then the
passive VC phase (structured-to-unstructured lowering with guard
materialization, then `Imperative.PassiveVCGen`), whose obligation program the
standard back end discharges with cvc5.

The program contains an `if (x > 0) { assert x >= 0 }`. Soundness hinges on
guard materialization: the `assert x >= 0` is reachable only on the `x > 0`
branch, so the VC is `x > 0 ⇒ x ≥ 0`, which is valid. Were the guard dropped
during Det→Nondet lowering, the assertion would be checked unconditionally
(`x ≥ 0` for arbitrary `x`), which is not valid, so a passing result here is
evidence the guard was materialized as an `assume` on the branch edge.

Both `uwp` (weakest precondition) and `usp` (strongest postcondition) report
one obligation per source assertion, labelled with the assertion's label (a
postcondition with its own), as symbolic evaluation labels them; `#guard_msgs` pins
that cvc5 reports each valid. Each assertion is checked on its own, as under
`--vcgen symbolic`.
-/

namespace Strata

def guardedPgm :=
#strata
program Core;
procedure Test(x : int)
{
  if (int.gt(x, 0)) {
    assert [guarded_nonneg]: (int.ge(x, 0));
  }
};
#end

-- The per-assertion `uwp` obligation, discharged by cvc5 as valid.
/--
info:
Obligation: guarded_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardedPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

-- The per-assertion `usp` obligation, discharged by cvc5 as valid.
/--
info:
Obligation: guarded_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardedPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Negative control: without the guard, the same assertion is *not* valid.

Dropping the guard during Det→Nondet lowering would check `x ≥ 0` for arbitrary
`x`, which is false (e.g. `x = -1`). This unguarded program therefore fails
under `uwp`, confirming that the guarded program above passes *because* the
guard was materialized as an `assume` — not because the assertion is trivially
valid. -/

def unguardedPgm :=
#strata
program Core;
procedure Test(x : int)
{
  assert [unguarded_nonneg]: (int.ge(x, 0));
};
#end

/--
info:
Obligation: unguarded_nonneg
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify unguardedPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Multiple assertions: per-obligation reporting is independent per assert.

Two assertions in one procedure, one valid (`x ≥ x`) and one not (`x > 0`, false
for `x = 0`). Each is its own obligation, discharged separately: the first
passes, the second fails, and neither assumes the other. -/

def twoAssertPgm :=
#strata
program Core;
procedure Test(x : int)
{
  assert [trivially_true]: (int.ge(x, x));
  assert [bogus_nonzero]: (int.gt(x, 0));
};
#end

/--
info:
Obligation: trivially_true
Property: assert
Result: ✅ pass

Obligation: bogus_nonzero
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify twoAssertPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Nested branches: the guard of each arm must reach its assertion.

`if (x > 0) { if (y > 0) { assert x + y > 0 } }` — the inner assertion holds
only under both guards. Materializing both guards yields `x>0 ⇒ y>0 ⇒ x+y>0`,
valid; dropping either would make it unprovable. -/

def nestedPgm :=
#strata
program Core;
procedure Test(x : int, y : int)
{
  if (int.gt(x, 0)) {
    if (int.gt(y, 0)) {
      assert [both_pos_sum_pos]: (int.gt(int.add(x, y), 0));
    }
  }
};
#end

/--
info:
Obligation: both_pos_sum_pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify nestedPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## An assumption narrows the state before an assertion.

`assume x > 5; assert x > 0` — the assertion follows from the assumption, so the
obligation `x>5 ⇒ x>0` is valid under both calculi. -/

def assumeThenAssertPgm :=
#strata
program Core;
procedure Test(x : int)
{
  assume [x_big]: (int.gt(x, 5));
  assert [x_pos]: (int.gt(x, 0));
};
#end

/--
info:
Obligation: x_pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify assumeThenAssertPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: x_pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify assumeThenAssertPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Unstructured LoopSimple (loop already cut to an acyclic body).

`--vcgen uwp/usp` assumes an acyclic CFG, so a `while` must already be cut by
the loop-invariant + loop-elimination passes (as the symbolic evaluation pipeline does at
evaluation time). This is a hand-written, self-contained transcription of the
loop-cut shape of `Examples/LoopSimple.core.st` — invariant established on
entry, an arbitrary iteration modelled by havocking the loop variables and
assuming the invariant + guard, the body run once, and the invariant's
maintenance asserted — plus the post-loop assertion that the invariant and the
negated guard give the postcondition.

Simplified invariant `0 ≤ i ≤ n` (the arithmetic sum invariant of the original
needs nonlinear reasoning; this keeps the shape while staying decidable):

* `maintain_inv` — one arbitrary iteration preserves `0 ≤ i ≤ n`: from
  `0 ≤ i ≤ n ∧ i < n`, after `i := i+1`, `0 ≤ i ≤ n`. Valid.
* `exit_i_le_n` — on loop exit `i ≤ n` holds (from the invariant). Valid. -/

def loopSimpleCutPgm :=
#strata
program Core;
procedure loopSimple (n : int)
spec {
  requires [nonneg_n]: (int.ge(n, 0));
}
{
  var i : int;
  i := 0;
  // establish invariant 0 <= i <= n on entry
  assert [entry_inv_lo]: (int.ge(i, 0));
  assert [entry_inv_hi]: (int.le(i, n));
  // arbitrary iteration: havoc i, assume invariant and guard, run body once
  havoc i;
  assume [iter_inv_lo]: (int.ge(i, 0));
  assume [iter_inv_hi]: (int.le(i, n));
  assume [iter_guard]: (int.lt(i, n));
  i := int.add(i, 1);
  // the iteration must preserve the invariant
  assert [maintain_inv_lo]: (int.ge(i, 0));
  assert [maintain_inv_hi]: (int.le(i, n));
};
#end

/--
info:
Obligation: entry_inv_lo
Property: assert
Result: ✅ pass

Obligation: entry_inv_hi
Property: assert
Result: ✅ pass

Obligation: maintain_inv_lo
Property: assert
Result: ✅ pass

Obligation: maintain_inv_hi
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify loopSimpleCutPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: entry_inv_lo
Property: assert
Result: ✅ pass

Obligation: entry_inv_hi
Property: assert
Result: ✅ pass

Obligation: maintain_inv_lo
Property: assert
Result: ✅ pass

Obligation: maintain_inv_hi
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify loopSimpleCutPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Specifications are threaded: `requires` assumed, `ensures` checked.

`requires x > 0`, body `y := x + 1`, `ensures y > 1`. The postcondition is
discharged only because the precondition is assumed: `x>0 ⇒ (y=x+1) ⇒ y>1`.
The obligation is reported under the synthesized `ensures_<label>` label. -/

def specPgm :=
#strata
program Core;
procedure Test(x : int, out y : int)
spec {
  requires [x_pos]: (int.gt(x, 0));
  ensures [y_big]: (int.gt(y, 1));
}
{
  y := int.add(x, 1);
};
#end

/--
info:
Obligation: y_big
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify specPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## A `bool` parameter is declared to the solver at its real type.

`procedure Test(b : bool)` with `assume b; assert b`. `b` is read at version 0,
so it has no `Cmd.init` from the body: its type comes solely from the header
(`headerTypeDecls`). Defaulting it to `int` would be a type mismatch for a
boolean; it is declared `bool`, and the obligation `b ⇒ b` discharges cleanly.
Exercises both calculi. -/

def boolParamPgm :=
#strata
program Core;
procedure Test(b : bool)
{
  assume [assume_b]: (b);
  assert [assert_b]: (b);
};
#end

/--
info:
Obligation: assert_b
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boolParamPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: assert_b
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boolParamPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## A structured `while` loop is eliminated before the lowering.

`uwp`/`usp` need an acyclic CFG. A structured `while` is eliminated first, by the
phases of the symbolic evaluation pipeline (`insertLoopInvariantAsserts`, `loopElim`), so the
loop is checked from its invariant: its entry and maintenance, and the assertion
after it, which holds by the invariant and the negated guard. A loop with no
invariant is cut with `true`: after it only the negated guard is known. The loop is
entered only when `0 < n`, so `i ≥ 0` holds after it, and `i > 5` is `unknown`, as its
counterexample rests on the arbitrary iteration. -/

def whileLoopPgm :=
#strata
program Core;
procedure Counted(n : int)
{
  var i : int := 0;
  while (int.lt(i, n)) invariant (int.ge(i, 0)) {
    i := int.add(i, 1);
  }
  assert [done]: (int.ge(i, 0));
};
procedure NoInvariant(n : int)
{
  var i : int := 0;
  while (int.lt(i, n)) {
    i := int.add(i, 1);
  }
  assert [after]: (int.ge(i, 0));
  assert [after_bad]: (int.gt(i, 5));
};
#end

/--
info:
Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: done
Property: assert
Result: ✅ pass

Obligation: after
Property: assert
Result: ✅ pass

Obligation: after_bad
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify whileLoopPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## `old(...)` in a postcondition refers to the pre-state.

At DDM translation `old(g)` becomes the free variable `old g`; this pass
snapshots each `inout` parameter's entry value into that variable
(`init (old g) := g` after the parameter declarations), so a postcondition
comparing the final state to `old` sees the pre-state. Core's type system
sanctions `old` only for `inout` parameters, so these use one.

`procedure Test(inout g : int)`, body `g := g + 1`, `ensures g > old g`: the
final `g` exceeds its entry value. -/

def oldPostPgm :=
#strata
program Core;
procedure Test(inout g : int)
spec {
  ensures [g_gt_old]: (int.gt(g, old g));
}
{
  g := int.add(g, 1);
};
#end

/--
info:
Obligation: g_gt_old
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldPostPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: g_gt_old
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify oldPostPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## A false `old` postcondition fails (guards against a vacuous snapshot).

Same program, but `ensures g < old g`. With `g := g + 1` this is `g+1 < g`,
false — so the obligation must *fail*. A passing result here would mean `old g`
had been dropped or bound to `g`'s final value rather than the pre-state. -/

def oldPostFailPgm :=
#strata
program Core;
procedure Test(inout g : int)
spec {
  ensures [g_lt_old]: (int.lt(g, old g));
}
{
  g := int.add(g, 1);
};
#end

/--
info:
Obligation: g_lt_old
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify oldPostFailPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## `old` of an input-only parameter is a type error (not silently accepted).

Core's type system binds `old` only for `inout` parameters. A postcondition
`ensures y > old x` where `x` is input-only names an unbound `old x`; with type
checking in the pipeline this surfaces as a clean type error rather than a
downstream SMT solver crash. -/

def oldInputOnlyPgm :=
#strata
program Core;
procedure Test(x : int, out y : int)
spec {
  ensures [y_gt_old_x]: (int.gt(y, old x));
}
{
  y := int.add(x, 1);
};
#end

/--
info: type error: old x is unbound
-/
#guard_msgs in
#eval do
  try
    let _ ← Core.verify oldInputOnlyPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })
    IO.println "unexpected: verification produced a result"
  catch e =>
    let msg := toString e
    if (msg.splitOn "Type checking error").length > 1 &&
        (msg.splitOn "Free Variables: [old x]").length > 1 then
      IO.println "type error: old x is unbound"
    else
      IO.println s!"unexpected error: {msg}"

/-! ## `inout` parameter: `old` captures the entry value while the param mutates.

`procedure Test(inout g : int)`, body `g := g + 1`. An `inout` parameter is in
both the inputs and the outputs, so `g` is re-incarnated by the body write while
`old g` (snapshotted at entry) keeps the pre-state. `ensures g == old g + 1`
must pass; the vacuous `ensures g == old g` must fail. This exercises the
input-type-declaration + `old`-snapshot + output-re-incarnation interaction. -/

def inoutPgm :=
#strata
program Core;
procedure Test(inout g : int)
spec {
  ensures [g_inc]: (g == int.add(old g, 1));
}
{
  g := int.add(g, 1);
};
#end

/--
info:
Obligation: g_inc
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify inoutPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

def inoutFailPgm :=
#strata
program Core;
procedure Test(inout g : int)
spec {
  ensures [g_unchanged]: (g == old g);
}
{
  g := int.add(g, 1);
};
#end

/--
info:
Obligation: g_unchanged
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify inoutFailPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Postconditions are checked on an early-`exit` path.

A structured `exit` breaks to an enclosing block's continuation; every path
still reaches the single procedure `finish`. Because this pass appends the
`ensures` to the `finish` block (not as trailing source statements), a
postcondition is checked no matter which `exit` path reaches the exit.

`procedure Test(x, out y)` sets `y := 1` then `exit`s the block, skipping a
`y := 0` that would violate the postcondition; `ensures y > 0` must still be
checked and hold (proving the `ensures` reached the exit), and it would be
*unprovable* if the skipped `y := 0` were on the checked path. -/

def earlyExitPgm :=
#strata
program Core;
procedure Test(x : int, out y : int)
spec {
  ensures [y_pos]: (int.gt(y, 0));
}
{
  l1: {
    y := 1;
    exit l1;
    y := 0; // skipped by the exit
  }
};
#end

/--
info:
Obligation: y_pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify earlyExitPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## A polymorphic procedure is monomorphized before verification.

`uwp`/`usp` run procedure/function monomorphization (after call
elimination). A polymorphic `procedure id<T>` has its type variable replaced by
a fresh opaque type, so its spec `y == x` — and the parameter types threaded by
`headerTypeDecls` — reach the solver over a concrete (uninterpreted) sort rather
than an un-instantiated type variable. Body `y := x` gives `y == x`. -/

def polyPgm :=
#strata
program Core;
procedure id<T>(x : T, out y : T)
spec {
  ensures [y_eq_x]: (y == x);
}
{
  y := x;
};
#end

/--
info:
Obligation: y_eq_x
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polyPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Two procedures sharing a parameter name stay independent.

Obligations are generated per procedure and qualified by procedure name, and
passification renames incarnations per body, so a parameter `x` in `A` and an
`x` in `B` do not interfere. `A` proves `x ≥ 0` from `x > 0`; `B` proves
`x ≤ 0` from `x < 0`. Both pass and are reported under distinct labels. -/

def multiProcPgm :=
#strata
program Core;
procedure A(x : int)
{
  assume [a_pos]: (int.gt(x, 0));
  assert [a_nonneg]: (int.ge(x, 0));
};
procedure B(x : int)
{
  assume [b_neg]: (int.lt(x, 0));
  assert [b_nonpos]: (int.le(x, 0));
};
#end

/--
info:
Obligation: a_nonneg
Property: assert
Result: ✅ pass

Obligation: b_nonpos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiProcPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## `free` clauses: a free `requires` is assumed; a free `ensures` is not checked.

`free requires g == 15` is assumed like any precondition, so the dependent
`assert g > 10` holds. `free ensures g < 100` is taken for granted rather than
proved, so it produces no obligation, even though the body leaves `g` far from
constrained. Only the checked assert is reported. -/

def freeClausePgm :=
#strata
program Core;
procedure Test(inout g : int)
spec {
  free requires [g_is_15]: (g == 15);
  free ensures [g_small]: (int.lt(g, 100));
}
{
  assert [g_gt_10]: (int.gt(g, 10));
};
#end

/--
info:
Obligation: g_gt_10
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify freeClausePgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Multiple `inout` parameters with cross-assignment `old`.

The shape of `OldExpressions.T1`: two `inout` params, the body copies `old g`
into `g2`, and `g` itself is untouched. `ensures g2 == old g` holds (that is what
the body did) and `ensures g == old g` holds (`g` unchanged). Exercises several
independent `old` snapshots at once. -/

def multiInoutPgm :=
#strata
program Core;
procedure Test(inout g : int, inout g2 : int)
spec {
  ensures [g2_eq_old_g]: (g2 == old g);
  ensures [g_unchanged]: (g == old g);
}
{
  g2 := old g;
};
#end

/--
info:
Obligation: g2_eq_old_g
Property: assert
Result: ✅ pass

Obligation: g_unchanged
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify multiInoutPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Calls inside CFG bodies

Call elimination rewrites calls in CFG blocks as well as in structured bodies, so a
`cfg` procedure may call other procedures. Each call becomes an `assert` of the
callee's precondition (labelled `callElimAssert_…`), a `havoc` of its outputs, and
an `assume` of its postcondition, in place in its block. `CfgCaller` calls `Inc`
once on one branch and twice on the other; its preconditions and postcondition
hold. `CfgBadCaller` has no precondition, so `Inc`'s `x ≥ 0` cannot be shown. -/

def cfgCallPgm :=
#strata
program Core;
procedure Inc(x : int, out r : int)
spec {
  requires [inc_nonneg]: (int.ge(x, 0));
  ensures [inc_post]: (r == int.add(x, 1));
}
{ r := int.add(x, 1); };
procedure CfgCaller(a : int, out m : int)
spec {
  requires [a_nonneg]: (int.ge(a, 0));
  ensures [m_gt_a]: (int.gt(m, a));
}
cfg entry {
  entry: {
    branch (int.ge(a, 10)) goto big else goto small;
  }
  big: {
    call Inc(a, out m);
    goto done;
  }
  small: {
    call Inc(a, out m);
    call Inc(m, out m);
    assert [small_m]: (m == int.add(a, 2));
    goto done;
  }
  done: {
    return;
  }
};
procedure CfgBadCaller(a : int, out m : int)
cfg entry {
  entry: {
    call Inc(a, out m);
    goto done;
  }
  done: {
    return;
  }
};
#end

/--
info:
Obligation: inc_post
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_2
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_6
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_10
Property: assert
Result: ✅ pass

Obligation: small_m
Property: assert
Result: ✅ pass

Obligation: m_gt_a
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_14
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cfgCallPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: inc_post
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_2
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_6
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_10
Property: assert
Result: ✅ pass

Obligation: small_m
Property: assert
Result: ✅ pass

Obligation: m_gt_a
Property: assert
Result: ✅ pass

Obligation: callElimAssert_inc_nonneg_14
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cfgCallPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })


/-! ## `cover` statements

A `cover e` is met when some execution reaches it with `e` true. Its obligation
is `αₙ ∧ e`, with `αₙ` the strongest postcondition reaching it, checked for
satisfiability (the same in both calculi). Results follow the assertions'. The
verdicts match symbolic evaluation's: `reach_pos` is reachable with `x > 5`, `unreach` needs
`x < 0` under `x > 0`. -/

def coverPgm :=
#strata
program Core;
procedure S(x : int)
{
  if (int.gt(x, 0)) {
    cover [reach_pos]: (int.gt(x, 5));
    cover [unreach]: (int.lt(x, 0));
  }
  assert [triv]: (x == x);
};
#end

/--
info:
Obligation: reach_pos
Property: cover
Result: ✅ pass

Obligation: unreach
Property: cover
Result: ❌ fail

Obligation: triv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify coverPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: reach_pos
Property: cover
Result: ✅ pass

Obligation: unreach
Property: cover
Result: ❌ fail

Obligation: triv
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify coverPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! Covers in a CFG body: `n_small` contradicts the precondition, `dead` follows
`assume false`. `mid_loop` (inside the cut loop) and `at_n` (after it) are
satisfiable in the loop's abstraction, an arbitrary iteration satisfying the
invariant, which may reach states the loop does not; a result that rests on the
cut's assumptions is reported `unknown`, as under `--vcgen symbolic`. -/

def cfgCoverPgm :=
#strata
program Core;
procedure C(n : int, out y : int)
spec { requires [n_pos]: (int.gt(n, 2)); }
cfg entry {
  entry: {
    y := 0;
    cover [n_small]: (int.lt(n, 2));
    goto loop;
  }
  @[loopInvariant = (int.le(y, n))]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    cover [mid_loop]: (y == int.sub(n, 1));
    y := int.add(y, 1);
    goto loop;
  }
  done: {
    cover [at_n]: (y == n);
    assume [stop]: (false);
    cover [dead]: (true);
    return;
  }
};
#end

/--
info: Obligation: n_small
Property: cover
Result: ❌ fail

Obligation: mid_loop
Property: cover
Result: ❓ unknown

Obligation: at_n
Property: cover
Result: ❓ unknown

Obligation: dead
Property: cover
Result: ❌ fail

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cfgCoverPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Function preconditions

Precondition elimination runs on structured and CFG bodies alike, after CFG loop
elimination, so a partial call is checked wherever it occurs: in a contract (a
well-formedness lemma, `Div_post_…`, checked under the `requires`), in a command,
in a branch guard (`branch_cond_…`), and in a loop invariant, both where it is
asserted and where it is assumed. In `LoopDiv` the invariant divides by `i`,
which after the cut's havoc may be `0`, so its check where it is assumed is not
proved (the invariant needs `i > 0` first), and with it the invariant is too
weak to be maintained. Both counterexamples rest on the cut's arbitrary
iteration, so they are reported `unknown` rather than as definite failures. -/

def precondPgm :=
#strata
program Core;
procedure Div(x : int, y : int, out r : int)
spec {
  requires [y_nz]: (y != 0);
  ensures [r_def]: (r == int.safeDiv(x, y));
}
{
  r := int.safeDiv(x, y);
};
procedure CfgDiv(x : int, y : int, out r : int)
cfg entry {
  entry: {
    branch (int.gt(int.safeDiv(x, y), 0)) goto pos else goto done;
  }
  pos: {
    r := int.safeDiv(x, int.sub(y, 1));
    goto done;
  }
  done: {
    return;
  }
};
procedure LoopDiv(n : int, out i : int)
spec { requires (int.gt(n, 0)); }
cfg entry {
  entry: { i := 1; goto loop; }
  @[loopInvariant = (int.ge(int.safeDiv(n, i), 0))]
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { i := int.add(i, 1); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: Div_post_r_def_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: set_r_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: r_def
Property: assert
Result: ✅ pass

Obligation: branch_cond_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: set_r_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail

Obligation: assert_cfgLoopElimAssert_entry_loop_0_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: assume_$__cfgLoopElimAssume_invariant_loop_0_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❓ unknown

Obligation: assert_cfgLoopElimAssert_maintain_loop_body_0_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify precondPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Program-level declarations

The back end encodes the program's functions and axioms, and a lemma is checked as
an obligation unit, as under `--vcgen symbolic`. -/

def funcPgm :=
#strata
program Core;
function inc(x : int) : int { int.add(x, 1) }
procedure P(x : int) { assert [inc_gt]: (int.gt(inc(x), x)); };
#end

/--
info:
Obligation: inc_gt
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify funcPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

def axiomPgm :=
#strata
program Core;
function g(x : int) : int;
axiom [g_pos]: (forall x : int :: int.gt(g(x), 0));
procedure P(x : int) { assert [g_gt]: (int.gt(g(x), 0)); };
#end

/--
info:
Obligation: g_gt
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify axiomPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

-- A false lemma fails.
def lemmaPgm :=
#strata
program Core;
lemma [bad]: (forall x : int :: int.gt(x, 0));
procedure P(x : int) { assert [t]: (true); };
#end

/--
info:
Obligation: bad
Property: assert
Result: ❌ fail

Obligation: t
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify lemmaPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## Size of the VC

The block predicates of the passive VC are named definitions, so the VC stays
linear in the CFG: forty sequential branches, each a join, verify in both
calculi. (Inlined, the formula would grow about threefold per branch.) -/

def manyBranchesPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  y := 0;
  if (int.gt(x, 1)) { y := int.add(y, 1); }
  if (int.gt(x, 2)) { y := int.add(y, 1); }
  if (int.gt(x, 3)) { y := int.add(y, 1); }
  if (int.gt(x, 4)) { y := int.add(y, 1); }
  if (int.gt(x, 5)) { y := int.add(y, 1); }
  if (int.gt(x, 6)) { y := int.add(y, 1); }
  if (int.gt(x, 7)) { y := int.add(y, 1); }
  if (int.gt(x, 8)) { y := int.add(y, 1); }
  if (int.gt(x, 9)) { y := int.add(y, 1); }
  if (int.gt(x, 10)) { y := int.add(y, 1); }
  if (int.gt(x, 11)) { y := int.add(y, 1); }
  if (int.gt(x, 12)) { y := int.add(y, 1); }
  if (int.gt(x, 13)) { y := int.add(y, 1); }
  if (int.gt(x, 14)) { y := int.add(y, 1); }
  if (int.gt(x, 15)) { y := int.add(y, 1); }
  if (int.gt(x, 16)) { y := int.add(y, 1); }
  if (int.gt(x, 17)) { y := int.add(y, 1); }
  if (int.gt(x, 18)) { y := int.add(y, 1); }
  if (int.gt(x, 19)) { y := int.add(y, 1); }
  if (int.gt(x, 20)) { y := int.add(y, 1); }
  if (int.gt(x, 21)) { y := int.add(y, 1); }
  if (int.gt(x, 22)) { y := int.add(y, 1); }
  if (int.gt(x, 23)) { y := int.add(y, 1); }
  if (int.gt(x, 24)) { y := int.add(y, 1); }
  if (int.gt(x, 25)) { y := int.add(y, 1); }
  if (int.gt(x, 26)) { y := int.add(y, 1); }
  if (int.gt(x, 27)) { y := int.add(y, 1); }
  if (int.gt(x, 28)) { y := int.add(y, 1); }
  if (int.gt(x, 29)) { y := int.add(y, 1); }
  if (int.gt(x, 30)) { y := int.add(y, 1); }
  if (int.gt(x, 31)) { y := int.add(y, 1); }
  if (int.gt(x, 32)) { y := int.add(y, 1); }
  if (int.gt(x, 33)) { y := int.add(y, 1); }
  if (int.gt(x, 34)) { y := int.add(y, 1); }
  if (int.gt(x, 35)) { y := int.add(y, 1); }
  if (int.gt(x, 36)) { y := int.add(y, 1); }
  if (int.gt(x, 37)) { y := int.add(y, 1); }
  if (int.gt(x, 38)) { y := int.add(y, 1); }
  if (int.gt(x, 39)) { y := int.add(y, 1); }
  if (int.gt(x, 40)) { y := int.add(y, 1); }
  assert [done]: (int.ge(y, 0));
};
#end

/--
info:
Obligation: done
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify manyBranchesPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/--
info:
Obligation: done
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify manyBranchesPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## Reachability, check modes and counterexamples

Each obligation's precondition (the strongest postcondition reaching its
command) is its path condition, so `--check-level full` tells an unreachable
command from a reachable one as `--vcgen symbolic` does: `dead_assert`/`dead_cover` are dead
because of an `assume` on their own path, and `join_dead`/`join_dead_cover`
only because no path through the join satisfies `y == 3`. Each assertion is
checked on its own, as under `--vcgen symbolic`: in `Indep` every assertion can fail, though
`is_two` and `not_seven` would hold if the ones before them were assumed. -/

def reachPgm :=
#strata
program Core;
procedure Reach(x : int, out y : int)
{
  if (int.gt(x, 0)) {
    assume [never]: (int.lt(x, 0));
    assert [dead_assert]: (x == 5);
    cover [dead_cover]: (x == 5);
  } else {
    y := int.sub(0, x);
    assert [live_maybe]: (y == 3);
  }
};
procedure JoinDead(x : int, out y : int)
{
  if (int.gt(x, 0)) { y := 1; } else { y := 2; }
  assume [three]: (y == 3);
  assert [join_dead]: (x == 7);
  cover [join_dead_cover]: (x == 7);
};
procedure Indep(x : int)
spec { requires (x != 0); }
{
  assert [is_one]: (x == 1);
  assert [is_two]: (x == 2);
  assert [not_seven]: (x != 7);
};
#end

/--
info:
Obligation: dead_assert
Property: assert
Result: ✅ pass (❗unreachable in this context)

Obligation: dead_cover
Property: cover
Result: ❌ fail (❗unreachable in this context)

Obligation: live_maybe
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: join_dead
Property: assert
Result: ✅ pass (❗unreachable in this context)

Obligation: join_dead_cover
Property: cover
Result: ❌ fail (❗unreachable in this context)

Obligation: is_one
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: is_two
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: not_seven
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify reachPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp, checkLevel := .full })

-- `bugFinding` makes dead code an error, as under `--vcgen symbolic`.
/--
info:
Obligation: dead_assert
Property: assert
Result: ❌ fail (❗unreachable in this context)

Obligation: dead_cover
Property: cover
Result: ❌ fail (❗unreachable in this context)

Obligation: live_maybe
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: join_dead
Property: assert
Result: ❌ fail (❗unreachable in this context)

Obligation: join_dead_cover
Property: cover
Result: ❌ fail (❗unreachable in this context)

Obligation: is_one
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: is_two
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: not_seven
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify reachPgm (options := { Core.VerifyOptions.quiet with vcgen := .usp, checkMode := .bugFinding, checkLevel := .full })

-- Counterexamples are given over the passive variables (`x@1` is `x` on entry).
/--
info: Obligation: dead_assert
Property: assert
Result: ✅ pass

Obligation: dead_cover
Property: cover
Result: ❌ fail

Obligation: live_maybe
Property: assert
Result: ❌ fail
Model:
(x, 0) (y, 0) 

Obligation: join_dead
Property: assert
Result: ✅ pass

Obligation: join_dead_cover
Property: cover
Result: ❌ fail

Obligation: is_one
Property: assert
Result: ❌ fail
Model:
(x, int.neg(1))

Obligation: is_two
Property: assert
Result: ❌ fail
Model:
(x, int.neg(1))

Obligation: not_seven
Property: assert
Result: ❌ fail
Model:
(x, 7)
-/
#guard_msgs in
#eval Core.verify reachPgm (options := { Core.VerifyOptions.models with vcgen := .usp })

end Strata

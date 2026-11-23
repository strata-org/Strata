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

/-! # `--vcgen uwp` on CFG bodies over various types

CFG procedure bodies over bitvectors (a counting loop), maps (filled in a loop,
with a quantified invariant), datatypes (constructors, testers and a partial
selector, whose precondition is checked in the contract), reals, strings, and a
polymorphic procedure (whose type parameter becomes an opaque type in every
block). Each is lowered, cut where it loops, passified and discharged by the
standard back end.

Known incompleteness: maintaining `MapFill`'s quantified invariant is valid, and
cvc5 proves its query with the option `full-saturate-quant`, but with the default options
it returns `unknown` (symbolic evaluation proves the same loop written as a
structured `while`). Instantiating the invariant at the goal's witness depends on
the solver's trigger heuristics. The expected output pins this `unknown`; a solver
that proves it makes the test fail, and the expectation is then updated to a pass. -/

namespace Strata.PassiveVCGenTypesTest

def typesPgm :=
#strata
program Core;
datatype List () { Nil(), Cons(head: int, tail: List) };

procedure BvCount(out i : bv W32)
spec { ensures [i_ten]: (i == bv{32}(10)); }
cfg entry {
  entry: { i := bv{32}(0); goto loop; }
  @[loopInvariant = (bv32.uLe(i, bv{32}(10)))]
  loop: { branch (bv32.uLt(i, bv{32}(10))) goto body else goto done; }
  body: { i := bv32.add(i, bv{32}(1)); goto loop; }
  done: { return; }
};

procedure MapFill(n : int, out m : Map int int)
spec {
  requires (int.gt(n, 0));
  ensures [m0]: (m[0] == 0);
}
cfg entry {
  entry: { var i : int := 0; goto loop; }
  @[loopInvariant = (int.ge(i, 0)),
    loopInvariant = (forall j : int :: (int.ge(j, 0) && int.lt(j, i)) ==> m[j] == j),
    loopInvariant = (int.gt(i, 0) || int.gt(n, 0))]
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { m := m[i := i]; i := int.add(i, 1); goto loop; }
  done: { assert [i_ge_1]: (int.ge(i, 1)); return; }
};

procedure Lists(x : int, out l : List)
spec { ensures [nonempty]: List..isCons(l); ensures [hd]: (List..head(l) == x); }
cfg entry {
  entry: { l := Nil(); branch (int.gt(x, 0)) goto pos else goto neg; }
  pos: { l := Cons(x, l); goto done; }
  neg: { l := Cons(x, Cons(0, l)); goto done; }
  done: { return; }
};

procedure Reals(x : real, out y : real)
spec { requires (real.ge(x, 1.0)); ensures [y_ge]: (real.ge(y, 2.0)); }
cfg entry {
  entry: { branch (real.gt(x, 3.0)) goto big else goto small; }
  big: { y := x; goto done; }
  small: { y := real.add(x, 1.0); goto done; }
  done: { return; }
};

procedure Strings(s : string, out t : string)
spec { ensures [len]: (str.len(t) == int.add(str.len(s), 3)); }
cfg entry {
  entry: { t := str.concat(s, "abc"); goto done; }
  done: { return; }
};

procedure Id<a>(x : a, out y : a)
spec { ensures [same]: (y == x); }
cfg entry {
  entry: { y := x; goto done; }
  done: { return; }
};
#end

/--
info: Obligation: i_ten
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: i_ge_1
Property: assert
Result: ✅ pass

Obligation: m0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_1
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_2
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_1
Property: assert
Result: ❓ unknown

Obligation: cfgLoopElimAssert_maintain_loop_body_2
Property: assert
Result: ✅ pass

Obligation: Lists_post_hd_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: nonempty
Property: assert
Result: ✅ pass

Obligation: hd
Property: assert
Result: ✅ pass

Obligation: y_ge
Property: assert
Result: ✅ pass

Obligation: len
Property: assert
Result: ✅ pass

Obligation: same
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify typesPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })

/-! ## The `unknown` of `MapFill` is the solver's

A result resting on the loop cut is shown as `unknown` whether the solver found a
counterexample (which the cut's assumptions may have made spurious) or gave up.
The solver log keeps the raw answer: for the quantified invariant it is
`unknown`, not `sat`, so no counterexample was found. -/

/-- info: [(cfgLoopElimAssert_maintain_loop_body_1, [unknown])] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Core.verify typesPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })
  let rawAnswers := r.toList.filterMap fun r =>
    if r.obligation.label != "cfgLoopElimAssert_maintain_loop_body_1" then none else
    match r.outcome with
    | .ok o => some (r.obligation.label,
        -- The solver's own entries; the phases' decisions are logged after them, apart.
        ((o.solverLog.toList.filter fun (path : Array Core.SolverPhaseLog) =>
            path.any (·.phase.startsWith "solver.")).map fun path => match path[0]? with
          | some entry => match entry.result with
            | .sat _ => "sat"
            | .unsat => "unsat"
            | .unknown _ => "unknown"
            | .err _ => "err"
          | none => "none"))
    | .error _ => none
  IO.println rawAnswers

/-! The phases' decisions on that result are logged too, as an entry after the solver's: each
phase that read the model, with what it made of it. -/

/-- info: [(cfgLoopElimAssert_maintain_loop_body_1, true)] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Core.verify typesPgm (options := { Core.VerifyOptions.quiet with vcgen := .uwp })
  let phaseLogged := r.toList.filterMap fun r =>
    if r.obligation.label != "cfgLoopElimAssert_maintain_loop_body_1" then none else
    match r.outcome with
    | .ok o => some (r.obligation.label,
        o.solverLog.toList.any fun (path : Array Core.SolverPhaseLog) =>
          !path.isEmpty && path.all fun e => !e.phase.startsWith "solver.")
    | .error _ => none
  IO.println phaseLogged

end Strata.PassiveVCGenTypesTest

end

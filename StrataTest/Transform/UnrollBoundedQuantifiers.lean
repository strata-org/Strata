/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Transform.UnrollBoundedQuantifiers
import StrataDDM.Integration.Lean
import StrataDDM.Integration.Lean.HashCommands

meta section
namespace Strata

/-- Options with the phase off. CSE is off so `unrolled` prints the program the
    solver is given, inlining on so a goal over the program's own functions arrives
    as their bodies. -/
private def noUnrolling : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with functionInlining := true, disableCSE := true }

/-- `noUnrolling` with the phase on, differing in that flag alone. -/
private def unrolling : Core.VerifyOptions :=
  { noUnrolling with unrollBoundedQuantifiers := true }

private def toCore (pgm : StrataDDM.Program) : Core.Program :=
  TransM.run Inhabited.default (translateProgram pgm) |>.fst

/-- This pass's counters; one absent from the output stands at zero. -/
private def counters (st : Core.Transform.CoreTransformState) : String :=
  ({ data := st.statistics.data.filter fun k _ =>
       k.startsWith "UnrollBoundedQuantifiers." } : Statistics).format

/-- The phases through the unrolling one, so `unrolled` prints this pass's output. -/
private def upToUnrolling (phases : List Core.PipelinePhase) : List Core.PipelinePhase :=
  let name := Core.unrollBoundedQuantifiersPipelinePhase.phase.name
  phases.take (phases.findIdx (fun p => p.phase.name == name) + 1)

/-- The factory `Core.verify` starts from: the per-instance reduction needs the
    builtins' concrete evaluation to fold arithmetic and booleans. -/
private def initState : Core.Transform.CoreTransformState :=
  { Core.Transform.CoreTransformState.emp with factory := Core.Factory }

/-- The counters the pass recorded, then the program it produced. -/
private def unrolled (pgm : StrataDDM.Program) : IO Unit := do
  match Core.coreValidatedPipeline (options := unrolling) with
  | .error e => IO.println s!"pipeline assembly failed: {e}"
  | .ok vp =>
    match ← (Core.runTransforms (toCore pgm) (upToUnrolling vp.phases)
               (initState := initState)).toBaseIO with
    | .error e => IO.println s!"{e}"
    | .ok (p, st) =>
      IO.println (counters st)
      IO.println (Std.format p.stripMetaData)

/-! ## `unrollBoundedQuantifiers` tests

Each program is run with the phase off and on: unrolling must never turn a provable
obligation into a failing one. -/

/-! ### A pinned length and concrete elements -/

def concretePgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assume [e1]:  Sequence.select!(s, 1) == 5;
  assume [e2]:  Sequence.select!(s, 2) == 5;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]: Sequence.select!(s, 0) == 5;
  assume [e1]: Sequence.select!(s, 1) == 5;
  assume [e2]: Sequence.select!(s, 2) == 5;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled concretePgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify concretePgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify concretePgm (options := unrolling)

/-! ### A pinned length with symbolic elements -/

def symbolicPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled symbolicPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify symbolicPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify symbolicPgm (options := unrolling)

/-! ### One element pinned, the rest symbolic -/

def mixedElementsPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]: Sequence.select!(s, 0) == 5;
  assert [a]: (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1))) && (int.lt(2, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 2)));
};
-/
#guard_msgs in
#eval unrolled mixedElementsPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify mixedElementsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify mixedElementsPgm (options := unrolling)

/-! ### An unpinned length leaves the quantifier standing -/

def unpinnedPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unresolved: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, i));
};
-/
#guard_msgs in
#eval unrolled unpinnedPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify unpinnedPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify unpinnedPgm (options := unrolling)

/-! ### An existential unrolls to a disjunction -/

def existentialPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assert [a]: exists i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) && int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]: Sequence.select!(s, 0) == 5;
  assert [a]: int.lt(0, Sequence.length(s)) || int.lt(1, Sequence.length(s)) && int.le(0, Sequence.select!(s, 1));
};
-/
#guard_msgs in
#eval unrolled existentialPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify existentialPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify existentialPgm (options := unrolling)

/-! ### The length stated by a top-level axiom -/

def axiomFactPgm :=
#strata
program Core;

const s : Sequence int;

axiom [len]: Sequence.length(s) == 2;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled axiomFactPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify axiomFactPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify axiomFactPgm (options := unrolling)

/-! ### The length stated by the path condition reaching the goal -/

def pathConditionPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  if (Sequence.length(s) == 2) {
    assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
  }
  else {
  }
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [|<label_ite_cond_true: Sequence.length(s) == 2>|]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled pathConditionPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify pathConditionPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify pathConditionPgm (options := unrolling)

/-! ### A length stated in one branch is out of scope after it -/

def factUnderIfPgm :=
#strata
program Core;

const s : Sequence int;
const b : bool;

procedure P()
{
  if (b) {
    assume [len]: Sequence.length(s) == 2;
  }
  else {
  }
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unresolved: 1
program Core;

function s () : Sequence int;
function b () : bool;
procedure P ()
{
  assume [|<label_ite_cond_true: b>|]: if b then b else true;
  assume [len]: if b then Sequence.length(s) == 2 else true;
  assume [|<label_ite_cond_false: !(b)>|]: if if b then false else true then if b then false else true else true;
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, i));
};
-/
#guard_msgs in
#eval unrolled factUnderIfPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify factUnderIfPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify factUnderIfPgm (options := unrolling)

/-! ### One procedure's assumptions are out of scope in another's goal

Symbolic evaluation merges the two procedures into sibling branches of one body, and
no fact crosses from one arm to the other. -/

def twoProceduresPgm :=
#strata
program Core;

const n : int;
const m : int;

procedure P()
{
  assume [ln]: n == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 2);
};

procedure Q()
{
  assume [lm]: m == 2;
  assert [b]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 2);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unresolved: 1
[statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
function m () : int;
procedure P ()
{
  if * {
    assume [ln]: n == 2;
    assert [a]: true;
  } else {
    assume [lm]: m == 2;
    assert [b]: forall i : int :: int.le(0, i) && int.lt(i, n) ==> int.lt(i, 2);
  }
};
-/
#guard_msgs in
#eval unrolled twoProceduresPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify twoProceduresPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify twoProceduresPgm (options := unrolling)

/-! ### Two goals of one procedure are each folded in the scope reaching them -/

def twoObligationsPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assume [e1]:  Sequence.select!(s, 1) == 5;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
  assert [b]: forall j : int :: (int.le(0, j) && int.lt(j, Sequence.length(s))) ==> int.lt(Sequence.select!(s, j), 6);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 2
program Core;

function s () : Sequence int;
procedure P ()
{
  if * {
    assume [len]: Sequence.length(s) == 2;
    assume [e0]: Sequence.select!(s, 0) == 5;
    assume [e1]: Sequence.select!(s, 1) == 5;
    assert [a]: true;
  } else {
    assume [len]: Sequence.length(s) == 2;
    assume [e0]: Sequence.select!(s, 0) == 5;
    assume [e1]: Sequence.select!(s, 1) == 5;
    assert [b]: true;
  }
};
-/
#guard_msgs in
#eval unrolled twoObligationsPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify twoObligationsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify twoObligationsPgm (options := unrolling)

/-! ### A fact stated between two goals reaches only the later one -/

def factBetweenGoalsPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
  assume [len]: Sequence.length(s) == 2;
  assert [b]: forall j : int :: (int.le(0, j) && int.lt(j, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, j));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unresolved: 1
[statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  if * {
    assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, i));
  } else {
    assume [len]: Sequence.length(s) == 2;
    assert [b]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
  }
};
-/
#guard_msgs in
#eval unrolled factBetweenGoalsPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown

Obligation: b
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify factBetweenGoalsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown

Obligation: b
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify factBetweenGoalsPgm (options := unrolling)

/-! ### An axiom for the length and an assume for an element -/

def mixedLocationsPgm :=
#strata
program Core;

const s : Sequence int;

axiom [len]: Sequence.length(s) == 2;

procedure P()
{
  assume [e0]: Sequence.select!(s, 0) == 5;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]: Sequence.select!(s, 0) == 5;
  assert [a]: int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1));
};
-/
#guard_msgs in
#eval unrolled mixedLocationsPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify mixedLocationsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify mixedLocationsPgm (options := unrolling)

/-! ### The length stated by a procedure precondition -/

def preconditionPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
spec {
  requires Sequence.length(s) == 2;
}
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [P_requires_0]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled preconditionPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify preconditionPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify preconditionPgm (options := unrolling)

/-! ### A goal whose body comes from two inlined functions -/

def inlinedFunctionsPgm :=
#strata
program Core;

const s : Sequence int;

inline function nonNeg(x : int) : bool { int.le(0, x) }

inline function elemOk(t : Sequence int, i : int) : bool { nonNeg(Sequence.select!(t, i)) }

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> elemOk(s, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
inline function nonNeg (x : int) : bool {
  int.le(0, x)
}
inline function elemOk (t : Sequence int, i : int) : bool {
  nonNeg(Sequence.select!(t, i))
}
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled inlinedFunctionsPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify inlinedFunctionsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify inlinedFunctionsPgm (options := unrolling)

/-! ### A polymorphic function applied to each element -/

def polymorphicPgm :=
#strata
program Core;

const s : Sequence int;

function same<T>(x : T) : T;

axiom [sameInt]: forall x : int :: same(x) == x;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> same(Sequence.select!(s, i)) == Sequence.select!(s, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
function |$__mono#same#int| (x : int) : int;
procedure P ()
{
  assume [sameInt]: forall x : int :: |$__mono#same#int|(x) == x;
  assume [len]: Sequence.length(s) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> |$__mono#same#int|(Sequence.select!(s, 0)) == Sequence.select!(s, 0)) && (int.lt(1, Sequence.length(s)) ==> |$__mono#same#int|(Sequence.select!(s, 1)) == Sequence.select!(s, 1));
};
-/
#guard_msgs in
#eval unrolled polymorphicPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polymorphicPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify polymorphicPgm (options := unrolling)

/-! ### A nested quantifier whose own length is pinned unrolls in turn -/

def nestedBothPinnedPgm :=
#strata
program Core;

const s : Sequence int;
const t : Sequence int;

procedure P()
{
  assume [ls]: Sequence.length(s) == 2;
  assume [lt]: Sequence.length(t) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> (forall j : int :: (int.le(0, j) && int.lt(j, Sequence.length(t))) ==> int.le(Sequence.select!(s, i), Sequence.select!(t, j)));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 3
program Core;

function s () : Sequence int;
function t () : Sequence int;
procedure P ()
{
  assume [ls]: Sequence.length(s) == 2;
  assume [lt]: Sequence.length(t) == 2;
  assert [a]: (int.lt(0, Sequence.length(s)) ==> (int.lt(0, Sequence.length(t)) ==> int.le(Sequence.select!(s, 0), Sequence.select!(t, 0))) && (int.lt(1, Sequence.length(t)) ==> int.le(Sequence.select!(s, 0), Sequence.select!(t, 1)))) && (int.lt(1, Sequence.length(s)) ==> (int.lt(0, Sequence.length(t)) ==> int.le(Sequence.select!(s, 1), Sequence.select!(t, 0))) && (int.lt(1, Sequence.length(t)) ==> int.le(Sequence.select!(s, 1), Sequence.select!(t, 1))));
};
-/
#guard_msgs (whitespace := lax) in
#eval unrolled nestedBothPinnedPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify nestedBothPinnedPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify nestedBothPinnedPgm (options := unrolling)

/-! ### A surviving inner quantifier restores the whole obligation -/

def nestedInnerUnpinnedPgm :=
#strata
program Core;

const s : Sequence int;
const t : Sequence int;

procedure P()
{
  assume [ls]: Sequence.length(s) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> (forall j : int :: (int.le(0, j) && int.lt(j, Sequence.length(t))) ==> int.le(Sequence.select!(s, i), Sequence.select!(t, j)));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.reverted: 1
[statistics] UnrollBoundedQuantifiers.unresolved: 2
program Core;

function s () : Sequence int;
function t () : Sequence int;
procedure P ()
{
  assume [ls]: Sequence.length(s) == 2;
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> forall j : int :: int.le(0, j) && int.lt(j, Sequence.length(t)) ==> int.le(Sequence.select!(s, i), Sequence.select!(t, j));
};
-/
#guard_msgs in
#eval unrolled nestedInnerUnpinnedPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify nestedInnerUnpinnedPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify nestedInnerUnpinnedPgm (options := unrolling)

/-! ### Unrolling beneath a kept outer quantifier -/

def underOuterQuantifierPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: exists m : int :: (forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(m, Sequence.select!(s, i)));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.int: 1
[statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assert [a]: exists m : int :: (int.lt(0, Sequence.length(s)) ==> int.le(m, Sequence.select!(s, 0))) && (int.lt(1, Sequence.length(s)) ==> int.le(m, Sequence.select!(s, 1)));
};
-/
#guard_msgs in
#eval unrolled underOuterQuantifierPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify underOuterQuantifierPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify underOuterQuantifierPgm (options := unrolling)

/-! ### Instances that refer to the kept outer binder

`Box..v(m)` is a partial destructor, so each occurrence raises its own obligation
that `m` was built by `MkBox`, and the fold rewrites those goals too. -/

def keptBinderInstancesPgm :=
#strata
program Core;

datatype Box { MkBox(v : int), NoBox() };

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assume [e1]:  Sequence.select!(s, 1) == 7;
  assert [a]: exists m : Box :: Box..isMkBox(m) &&
    (forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(Box..v(m), int.add(Box..v(m), Sequence.select!(s, i))));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.other: 3
[statistics] UnrollBoundedQuantifiers.unrolled: 3
program Core;

datatype Box {
  MkBox(v : int),
  NoBox()
};
function s () : Sequence int;
procedure P ()
{
  if * {
    if * {
      assume [len]: Sequence.length(s) == 2;
      assume [e0]: Sequence.select!(s, 0) == 5;
      assume [e1]: Sequence.select!(s, 1) == 7;
      assert [assert_a_calls_Box..v_0]: forall m : Box :: (int.lt(0, Sequence.length(s)) ==> Box..isMkBox(m) ==> Box..isMkBox(m)) && (int.lt(1, Sequence.length(s)) ==> Box..isMkBox(m) ==> Box..isMkBox(m));
    } else {
      assume [len]: Sequence.length(s) == 2;
      assume [e0]: Sequence.select!(s, 0) == 5;
      assume [e1]: Sequence.select!(s, 1) == 7;
      assert [assert_a_calls_Box..v_1]: forall m : Box :: (int.lt(0, Sequence.length(s)) ==> Box..isMkBox(m) ==> Box..isMkBox(m)) && (int.lt(1, Sequence.length(s)) ==> Box..isMkBox(m) ==> Box..isMkBox(m));
    }
  } else {
    assume [len]: Sequence.length(s) == 2;
    assume [e0]: Sequence.select!(s, 0) == 5;
    assume [e1]: Sequence.select!(s, 1) == 7;
    assert [a]: exists m : Box :: Box..isMkBox(m) && ((int.lt(0, Sequence.length(s)) ==> int.le(Box..v(m), int.add(Box..v(m), 5))) && (int.lt(1, Sequence.length(s)) ==> int.le(Box..v(m), int.add(Box..v(m), 7))));
  }
};
-/
#guard_msgs in
#eval unrolled keptBinderInstancesPgm

/--
info:
Obligation: assert_a_calls_Box..v_0
Property: assert
Result: ✅ pass

Obligation: assert_a_calls_Box..v_1
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify keptBinderInstancesPgm (options := noUnrolling)

/--
info:
Obligation: assert_a_calls_Box..v_0
Property: assert
Result: ✅ pass

Obligation: assert_a_calls_Box..v_1
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify keptBinderInstancesPgm (options := unrolling)

/-! ### A negative lower bound states no range the pass accepts

The claim fails only at `-1`, so the fail verdict is what shows the guard was read
as written rather than as `[0, n)`. -/

def negativeLowerBoundPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.le(int.neg(1), i) && int.lt(i, n)) ==> int.le(0, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.int: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: int.le(int.neg(1), i) && int.lt(i, n) ==> int.le(0, i);
};
-/
#guard_msgs in
#eval unrolled negativeLowerBoundPgm

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify negativeLowerBoundPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify negativeLowerBoundPgm (options := unrolling)

/-! ### A disjunctive guard states no range the pass accepts -/

def disjunctiveGuardPgm :=
#strata
program Core;

const n : int;
const b : bool;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.le(0, i) && (int.lt(i, n) || b)) ==> int.lt(i, n);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.int: 1
program Core;

function n () : int;
function b () : bool;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: int.le(0, i) && (int.lt(i, n) || b) ==> int.lt(i, n);
};
-/
#guard_msgs in
#eval unrolled disjunctiveGuardPgm

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify disjunctiveGuardPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify disjunctiveGuardPgm (options := unrolling)

/-! ### A count past the per-quantifier cap leaves the quantifier standing -/

def binderCapPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 100;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.capped: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 100;
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> int.le(0, Sequence.select!(s, i));
};
-/
#guard_msgs in
#eval unrolled binderCapPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify binderCapPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify binderCapPgm (options := unrolling)

/-! ### Nested counts whose product passes the cap leave the quantifiers standing -/

def productCapPgm :=
#strata
program Core;

const s : Sequence int;
const t : Sequence int;
const u : Sequence int;

procedure P()
{
  assume [ls]: Sequence.length(s) == 42;
  assume [lt]: Sequence.length(t) == 42;
  assume [lu]: Sequence.length(u) == 42;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> (forall j : int :: (int.le(0, j) && int.lt(j, Sequence.length(t))) ==> (forall k : int :: (int.le(0, k) && int.lt(k, Sequence.length(u))) ==> int.le(Sequence.select!(s, i), int.add(Sequence.select!(t, j), Sequence.select!(u, k)))));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.capped: 1764
[statistics] UnrollBoundedQuantifiers.reverted: 43
program Core;

function s () : Sequence int;
function t () : Sequence int;
function u () : Sequence int;
procedure P ()
{
  assume [ls]: Sequence.length(s) == 42;
  assume [lt]: Sequence.length(t) == 42;
  assume [lu]: Sequence.length(u) == 42;
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, Sequence.length(s)) ==> forall j : int :: int.le(0, j) && int.lt(j, Sequence.length(t)) ==> forall k : int :: int.le(0, k) && int.lt(k, Sequence.length(u)) ==> int.le(Sequence.select!(s, i), int.add(Sequence.select!(t, j), Sequence.select!(u, k)));
};
-/
#guard_msgs in
#eval unrolled productCapPgm

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify productCapPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify productCapPgm (options := unrolling)

/-! ## Decidable goals

These carry no sequence, so the solver decides them outright: a fold that emitted one
instance too few would leave a valid formula and the verdict would move. -/

/-! ### A refuted goal over a scalar bound -/

def scalarRefutedPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 2);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [r]: int.lt(2, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled scalarRefutedPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify scalarRefutedPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify scalarRefutedPgm (options := unrolling)

/-! ### A refuted goal over sequence elements

The verdict is unknown rather than a counterexample either way, since the sequence
axioms leave the query quantified whichever way the goal is stated. -/

def refutedElementsPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]:  Sequence.select!(s, 0) == 5;
  assume [e1]:  Sequence.select!(s, 1) == 5;
  assume [e2]:  Sequence.select!(s, 2) == int.neg(1);
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 3;
  assume [e0]: Sequence.select!(s, 0) == 5;
  assume [e1]: Sequence.select!(s, 1) == 5;
  assume [e2]: Sequence.select!(s, 2) == int.neg(1);
  assert [r]: int.lt(2, Sequence.length(s)) ==> false;
};
-/
#guard_msgs in
#eval unrolled refutedElementsPgm

/--
info:
Obligation: r
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify refutedElementsPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify refutedElementsPgm (options := unrolling)

/-! ### A non-strict upper bound includes its endpoint -/

def leUpperBoundPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 2;
  assert [r]: forall i : int :: (int.le(0, i) && int.le(i, n)) ==> int.lt(i, 2);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assert [r]: int.le(2, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled leUpperBoundPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify leUpperBoundPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify leUpperBoundPgm (options := unrolling)

/-! ### A count of one -/

def countOnePgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 1;
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 0);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 1;
  assert [r]: int.lt(0, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled countOnePgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify countOnePgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify countOnePgm (options := unrolling)

/-! ### An empty range leaves the unit of the connective -/

def emptyRangePgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 0;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 0);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 0;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled emptyRangePgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify emptyRangePgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify emptyRangePgm (options := unrolling)

/-! ### A strict lower bound, written either way round -/

def strictLowerBoundPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.lt(0, i) && int.lt(i, n)) ==> int.le(1, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled strictLowerBoundPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify strictLowerBoundPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify strictLowerBoundPgm (options := unrolling)

/-! ### A strict lower bound with the binder on the left -/

def strictLowerBoundGtPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.gt(i, 0) && int.lt(i, n)) ==> int.le(1, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled strictLowerBoundGtPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify strictLowerBoundGtPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify strictLowerBoundGtPgm (options := unrolling)

/-! ### An element fact with the selector on the right -/

def selectOnRightPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]:  5 == Sequence.select!(s, 0);
  assume [e1]:  7 == Sequence.select!(s, 1);
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
procedure P ()
{
  assume [len]: Sequence.length(s) == 2;
  assume [e0]: 5 == Sequence.select!(s, 0);
  assume [e1]: 7 == Sequence.select!(s, 1);
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled selectOnRightPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify selectOnRightPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify selectOnRightPgm (options := unrolling)

/-! ### A guard behind a redex states no range the matchers can read -/

def guardBehindRedexPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int ::
    (have ok : bool = (int.le(0, i) && int.lt(i, n)) in (ok ==> int.le(0, i)));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled guardBehindRedexPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardBehindRedexPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify guardBehindRedexPgm (options := unrolling)

/-! ### A strict bound at `-1` admits exactly the indices the fold covers -/

def negativeOneStrictPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.lt(int.neg(1), i) && int.lt(i, n)) ==> int.le(0, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled negativeOneStrictPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify negativeOneStrictPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify negativeOneStrictPgm (options := unrolling)

/-! ### A strict bound below `-1` admits indices the fold would miss -/

def negativeTwoStrictPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: (int.lt(int.neg(2), i) && int.lt(i, n)) ==> int.le(0, i);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.int: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 3;
  assert [a]: forall i : int :: int.lt(int.neg(2), i) && int.lt(i, n) ==> int.le(0, i);
};
-/
#guard_msgs in
#eval unrolled negativeTwoStrictPgm

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify negativeTwoStrictPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify negativeTwoStrictPgm (options := unrolling)

/-! ### A fact pinning a negative value is not recorded -/

def negativeFactPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == int.neg(1);
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 0);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unresolved: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == int.neg(1);
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, n) ==> int.lt(i, 0);
};
-/
#guard_msgs in
#eval unrolled negativeFactPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify negativeFactPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify negativeFactPgm (options := unrolling)

/-! ### A literal bound needs no fact -/

def literalBoundPgm :=
#strata
program Core;

procedure P()
{
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, 3)) ==> int.lt(i, 2);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

procedure P ()
{
  assert [r]: false;
};
-/
#guard_msgs in
#eval unrolled literalBoundPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify literalBoundPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify literalBoundPgm (options := unrolling)

/-! ### A lower bound written the other way round -/

def geLowerBoundPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 2;
  assert [r]: forall i : int :: (int.ge(i, 0) && int.lt(i, n)) ==> int.lt(i, 1);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assert [r]: int.lt(1, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled geLowerBoundPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify geLowerBoundPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify geLowerBoundPgm (options := unrolling)

/-! ### A fact with the literal on the left -/

def literalOnLeftPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: 2 == n;
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 1);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: 2 == n;
  assert [r]: int.lt(1, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled literalOnLeftPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify literalOnLeftPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify literalOnLeftPgm (options := unrolling)

/-! ### A fact stated in a nested block -/

def nestedBlockPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  b: {
    assume [ln]: n == 2;
  }
  assert [r]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 1);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assert [r]: int.lt(1, n) ==> false;
};
-/
#guard_msgs in
#eval unrolled nestedBlockPgm

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify nestedBlockPgm (options := noUnrolling)

/--
info:
Obligation: r
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify nestedBlockPgm (options := unrolling)

/-! ## Facts, guards and commands the pass reads -/

/-! ### Two facts disagreeing about one term: the later one gives the count -/

def disagreeingFactsPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [l1]: n == 2;
  assume [l2]: n == 3;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, 1);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [l1]: n == 2;
  assume [l2]: n == 3;
  assert [a]: (int.lt(1, n) ==> false) && (int.lt(2, n) ==> false);
};
-/
#guard_msgs in
#eval unrolled disagreeingFactsPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify disagreeingFactsPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify disagreeingFactsPgm (options := unrolling)

/-! ### A binder that is not an integer is passed over -/

def boolBinderPgm :=
#strata
program Core;

procedure P()
{
  assert [a]: forall b : bool :: b || !b;
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.ineligible.bool: 1
program Core;

procedure P ()
{
  assert [a]: forall b : bool :: b || !b;
};
-/
#guard_msgs in
#eval unrolled boolBinderPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boolBinderPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify boolBinderPgm (options := unrolling)

/-! ### Two resolvable quantifiers in one goal are both folded -/

def twoResolvableQuantifiersPgm :=
#strata
program Core;

const n : int;
const m : int;

procedure P()
{
  assume [ln]: n == 2;
  assume [lm]: m == 2;
  assert [a]: (forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, n)) && (forall j : int :: (int.le(0, j) && int.lt(j, m)) ==> int.lt(j, m));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 2
program Core;

function n () : int;
function m () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assume [lm]: m == 2;
  assert [a]: (int.lt(0, n) ==> int.lt(0, n)) && (int.lt(1, n) ==> int.lt(1, n)) && ((int.lt(0, m) ==> int.lt(0, m)) && (int.lt(1, m) ==> int.lt(1, m)));
};
-/
#guard_msgs in
#eval unrolled twoResolvableQuantifiersPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify twoResolvableQuantifiersPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify twoResolvableQuantifiersPgm (options := unrolling)

/-! ### One unresolvable sibling reverts the obligation both quantifiers sit in -/

def siblingQuantifiersPgm :=
#strata
program Core;

const n : int;
const m : int;

procedure P()
{
  assume [ln]: n == 2;
  assert [a]: (forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.le(0, i)) && (forall j : int :: (int.le(0, j) && int.lt(j, m)) ==> int.le(0, j));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.reverted: 1
[statistics] UnrollBoundedQuantifiers.unresolved: 1
program Core;

function n () : int;
function m () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, n) ==> int.le(0, i) && forall j : int :: int.le(0, j) && int.lt(j, m) ==> int.le(0, j);
};
-/
#guard_msgs in
#eval unrolled siblingQuantifiersPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify siblingQuantifiersPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify siblingQuantifiersPgm (options := unrolling)

/-! ### A cover unrolls to a disjunction -/

def coverPgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 2;
  cover [c]: exists i : int :: (int.le(0, i) && int.lt(i, n)) && int.lt(i, 1);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 2;
  cover [c]: int.lt(0, n);
};
-/
#guard_msgs in
#eval unrolled coverPgm

/--
info:
Obligation: c
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify coverPgm (options := noUnrolling)

/--
info:
Obligation: c
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify coverPgm (options := unrolling)

/-! ### A quantifier in an assume is left alone -/

def quantifierInAssumePgm :=
#strata
program Core;

const n : int;

procedure P()
{
  assume [ln]: n == 2;
  assume [q]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, n);
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, n)) ==> int.lt(i, n);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function n () : int;
procedure P ()
{
  assume [ln]: n == 2;
  assume [q]: forall i : int :: int.le(0, i) && int.lt(i, n) ==> int.lt(i, n);
  assert [a]: (int.lt(0, n) ==> int.lt(0, n)) && (int.lt(1, n) ==> int.lt(1, n));
};
-/
#guard_msgs in
#eval unrolled quantifierInAssumePgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify quantifierInAssumePgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify quantifierInAssumePgm (options := unrolling)

/-! ### An element fact stated with the checked selector

`Sequence.select` carries an in-bounds precondition, so each occurrence raises an
out-of-bounds obligation of its own. -/

def selectNoBangPgm :=
#strata
program Core;

const s : Sequence int;

procedure P()
{
  assume [ls]: Sequence.length(s) == 2;
  assume [e0]: Sequence.select(s, 0) == 5;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(s))) ==> int.le(0, Sequence.select(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 2
program Core;

function s () : Sequence int;
procedure P ()
{
  if * {
    if * {
      assume [ls]: Sequence.length(s) == 2;
      assert [assume_e0_calls_Sequence.select_0]: true && int.lt(0, Sequence.length(s));
    } else {
      assume [ls]: Sequence.length(s) == 2;
      assume [e0]: Sequence.select(s, 0) == 5;
      assert [assert_a_calls_Sequence.select_0]: (int.lt(0, Sequence.length(s)) ==> int.lt(0, Sequence.length(s))) && (int.lt(1, Sequence.length(s)) ==> int.lt(1, Sequence.length(s)));
    }
  } else {
    assume [ls]: Sequence.length(s) == 2;
    assume [e0]: Sequence.select(s, 0) == 5;
    assert [a]: int.lt(1, Sequence.length(s)) ==> int.le(0, Sequence.select(s, 1));
  }
};
-/
#guard_msgs in
#eval unrolled selectNoBangPgm

/--
info:
Obligation: assume_e0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_a_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify selectNoBangPgm (options := noUnrolling)

/--
info:
Obligation: assume_e0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assert_a_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify selectNoBangPgm (options := unrolling)

/-! ### A bound that names its value only after normalization

The fact uses the checked selector and the bound the unchecked one, so no fact names
the bound as written and its value is reached by substituting the element into it. -/

def normalizedBoundPgm :=
#strata
program Core;

const s : Sequence int;
const idx : Sequence int;

procedure P()
{
  assume [li]: Sequence.length(idx) == 1;
  assume [i0]: Sequence.select(idx, 0) == 2;
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.select!(idx, 0))) ==> int.le(0, Sequence.select!(s, i));
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

function s () : Sequence int;
function idx () : Sequence int;
procedure P ()
{
  if * {
    assume [li]: Sequence.length(idx) == 1;
    assert [assume_i0_calls_Sequence.select_0]: true && int.lt(0, Sequence.length(idx));
  } else {
    assume [li]: Sequence.length(idx) == 1;
    assume [i0]: Sequence.select(idx, 0) == 2;
    assert [a]: int.le(0, Sequence.select!(s, 0)) && int.le(0, Sequence.select!(s, 1));
  }
};
-/
#guard_msgs in
#eval unrolled normalizedBoundPgm

/--
info:
Obligation: assume_i0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify normalizedBoundPgm (options := noUnrolling)

/--
info:
Obligation: assume_i0_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: a
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify normalizedBoundPgm (options := unrolling)

/-! ### A length reached through a sequence constructor

The count comes from the builtin axiom `length(empty()) == 0`, which monomorphization
instantiates at the program's element type so that it names the same term as the bound. -/

def emptySeqLengthPgm :=
#strata
program Core;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, Sequence.length(Sequence.empty<int>()))) ==> int.lt(i, 0);
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

procedure P ()
{
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled emptySeqLengthPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify emptySeqLengthPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify emptySeqLengthPgm (options := unrolling)

/-! ### A count equal to `unrollBinderCap` still unrolls

Only the counters separate this pair from the one below: the fold and the quantifier
it came from are equally provable. -/

def binderCapExactPgm :=
#strata
program Core;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, 64)) ==> i == i;
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.unrolled: 1
program Core;

procedure P ()
{
  assert [a]: true;
};
-/
#guard_msgs in
#eval unrolled binderCapExactPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify binderCapExactPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify binderCapExactPgm (options := unrolling)

/-! ### One instance past the per-quantifier cap -/

def binderCapBoundaryPgm :=
#strata
program Core;

procedure P()
{
  assert [a]: forall i : int :: (int.le(0, i) && int.lt(i, 65)) ==> i == i;
};
#end

/--
info: [statistics] UnrollBoundedQuantifiers.capped: 1
program Core;

procedure P ()
{
  assert [a]: forall i : int :: int.le(0, i) && int.lt(i, 65) ==> i == i;
};
-/
#guard_msgs in
#eval unrolled binderCapBoundaryPgm

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify binderCapBoundaryPgm (options := noUnrolling)

/--
info:
Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify binderCapBoundaryPgm (options := unrolling)

end Strata

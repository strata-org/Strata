/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
meta import Strata.Transform.CFGLoopElim
meta import Strata.Transform.PrecondElim
meta import StrataTest.Languages.Core.Tests.ReparseTestUtils
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # CFG loop elimination

`CFGLoopElim` cuts the loops of a `cfg` body at their headers, using the
`@[loopInvariant = (e)]` annotations on the header blocks (none means `true`).
Each header gets a pre-header that asserts the invariant on entry, havocs the
loop's modified variables and assumes the invariant; each back edge goes to a
block that asserts the invariant (maintenance) and ends the path. The verification
tests run `--vcgen symexec` (the path explorer), which runs it before call
elimination, so CFG bodies with loops are verified.

A counterexample that rests on the cut is a state of an arbitrary iteration, not
necessarily one the program reaches, so such a failure is reported `unknown`. That
covers every check after the havoc: a maintenance check, and a check after the loop
even when the failing run skips the loop. Only the entry check fails definitely.
Under merge mode `merged`, a path that never enters the loop can also carry the cut's
label after a join, so its failure is `unknown` too. -/

namespace Strata.Test.CFGLoopElim

open Strata
open Strata.CoreDDM

private def translate (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Run CFG loop elimination and print the result, with its `loopInvariant`
    annotations (none remain on a cut header). -/
private def printCut (p : StrataDDM.Program) : IO Unit :=
  match Core.Transform.run (translate p) Core.CFGLoopElim.cfgLoopElim with
  | .ok (_, p') => IO.println (Core.formatProgram p'
      (annFilter := .only (Std.HashSet.ofList [Imperative.MetaData.loopInvariantKey]))).pretty
  | .error e => IO.println s!"error: {e}"

/-- Verify with `--vcgen symexec` (the path explorer) under merge mode `merge`, printing a
    pipeline failure as a message. -/
private def run (p : StrataDDM.SourcedProgram) (merge : Core.MergeMode := .always) :
    IO Unit := do
  try
    IO.println (← Strata.Core.verify p
      (options := { Core.VerifyOptions.quiet with symExec := some merge }))
  catch e => IO.println s!"error: {e}"

/-- The labels of the commands the cut generates, in order. -/
private def generatedLabels (p : StrataDDM.Program) : List String :=
  match Core.Transform.run (translate p) Core.CFGLoopElim.cfgLoopElim with
  | .ok (_, p') => p'.decls.flatMap fun d => match d with
    | .proc q _ => match q.body with
      | .cfg g _ => g.blocks.flatMap fun (_, b) => b.cmds.filterMap fun c => match c with
        | .cmd (.assert l _ _) => some l
        | .cmd (.assume l _ _) => some l
        | _ => none
      | _ => []
    | _ => []
  | .error _ => []

/-! ## A counting loop -/

private def countUp :=
#strata
program Core;
procedure CountUp(n : int, out y : int)
spec {
  requires [n_nonneg]: (int.ge(n, 0));
  ensures [y_eq_n]: (y == n);
}
cfg entry {
  entry: {
    y := 0;
    goto loop;
  }
  @[loopInvariant = (int.le(y, n)), loopInvariant = (int.ge(y, 0))]
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto loop;
  }
  done: {
    return;
  }
};
#end

/--
info: program Core;

procedure CountUp (n : int, out y : int)
spec {
  requires [n_nonneg]: int.ge(n, 0);
  ensures [y_eq_n]: y == n;
  } cfg entry {
  entry: {
    y := 0;
    goto loopElim_pre_loop;
  }
  loop: {
    branch (int.lt(y, n)) goto body else goto done;
  }
  body: {
    y := int.add(y, 1);
    goto loopElim_back_body_loop;
  }
  done: {
    return;
  }
  loopElim_pre_loop: {
    assert [cfgLoopElimAssert_entry_loop_0]: int.le(y, n);
    assert [cfgLoopElimAssert_entry_loop_1]: int.ge(y, 0);
    assume [$__cfgLoopElimAssume_havoc_loop]: true;
    havoc y;
    assume [$__cfgLoopElimAssume_invariant_loop_0]: int.le(y, n);
    assume [$__cfgLoopElimAssume_invariant_loop_1]: int.ge(y, 0);
    goto loop;
  }
  loopElim_back_body_loop: {
    assert [cfgLoopElimAssert_maintain_loop_body_0]: int.le(y, n);
    assert [cfgLoopElimAssert_maintain_loop_body_1]: int.ge(y, 0);
    assume [$__cfgLoopElimAssume_cut_loop_body]: false;
    return;
  }
};
-/
#guard_msgs in
#eval printCut countUp.program

-- The back-edge block is not an exit, so `y_eq_n` is checked once, at `done`.
/--
info:
Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_1
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_1
Property: assert
Result: ✅ pass

Obligation: y_eq_n
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run countUp


/-! ## No invariant

A header with no invariant is cut with `true`: no invariant is asserted, and the
havoc forgets everything about `y` except the exit guard, so the postcondition
cannot be shown. The counterexample is a state of the cut (an arbitrary
iteration), which a labelled `assume true` before the havoc marks, so it is
reported `unknown` rather than as a definite failure, as with an invariant. -/

private def noInvPgm :=
#strata
program Core;
procedure P(n : int, out y : int)
spec { requires (int.ge(n, 0)); ensures [y_eq_n]: (y == n); }
cfg entry {
  entry: { y := 0; goto loop; }
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: y_eq_n
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run noInvPgm

-- The same under merge mode `never` (one path per way through the body).
/--
info:
Obligation: y_eq_n
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run noInvPgm .never

/-! ## The cut's marker reaches every later obligation

The labelled `assume true` before the havoc is a marker (`Core.isAbstractionMarker`), so the
path explorer keeps it in the path condition. After the loop, call elimination rewrites a call
and precondition elimination checks a partial function's precondition; each line is a check and
whether its obligation carries the cut's marker, through the whole `--vcgen symexec` pipeline. -/

private def markerAfterLoop :=
#strata
program Core;
function safeMod(x : int, y : int) : int
  requires y != 0;
{ int.safeMod(x, y) }
procedure Q(x : int, out r : int)
spec { ensures [q_post]: (r == x); }
{ r := x; };
procedure P(x : int, out y : int)
spec { ensures [post]: (y == x); }
cfg entry {
  entry: { y := 0; goto h; }
  h: { goto body, after; }
  body: { goto h; }
  after: { call Q(x, out y); var m : int := safeMod(x, 1); assert [chk]: (y == x); return; }
};
#end

/-- For each result of verifying `p` under merge mode `merge`, its label and whether its
    assumptions carry the cut's marker. -/
private def carriesMarker (p : StrataDDM.Program) (merge : Core.MergeMode) : IO Unit := do
  let options := { Core.VerifyOptions.quiet with symExec := some merge }
  match ← (Strata.Core.verifyProgram (Strata.Core.getProgram p).1 options).toBaseIO with
  | .ok rs =>
    for r in rs do
      IO.println s!"{r.obligation.label}: \
        {Core.obligationHasLabelPrefix r.obligation Core.CFGLoopElim.cfgLoopElimAssumePrefix}"
  | .error e => IO.println s!"error: {e}"

/--
info: safeMod_body_calls_Int.SafeMod_0: false
q_post: false
init_calls_safeMod_0: true
chk: true
post: true
-/
#guard_msgs in
#eval carriesMarker markerAfterLoop.program .always

/--
info: safeMod_body_calls_Int.SafeMod_0: false
q_post: false
init_calls_safeMod_0: true
chk: true
post: true
-/
#guard_msgs in
#eval carriesMarker markerAfterLoop.program .never

/-! ## A label with the marker prefix is refused

The cut reserves its marker prefix, so a written assumption cannot pass for one of its markers. -/

private def writtenMarker :=
#strata
program Core;
procedure P(out y : int)
cfg entry {
  entry: { assume [$__cfgLoopElimAssume_mine]: true; y := 0; return; }
};
#end

/--
info: error: ❌ The label "$__cfgLoopElimAssume_mine" starts with "$__cfgLoopElimAssume_", which
  CFG loop elimination reserves for its markers.
-/
#guard_msgs (whitespace := lax) in
#eval run writtenMarker

/-! ## An invariant that holds on entry but is not maintained

The maintenance check's counterexample is a state of the loop's abstraction (an
arbitrary iteration satisfying the invariant), so it is
reported `unknown` rather than as a definite failure. -/

private def notMaintainedPgm :=
#strata
program Core;
procedure P(n : int, out y : int)
spec { requires (int.ge(n, 0)); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (y == 0)]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run notMaintainedPgm

-- The same under merge mode `never` (one path per way through the body).
/--
info:
Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run notMaintainedPgm .never

/-! ## The entry block as header

The entry is a loop header (the back edge comes from `dec`), so the pre-header
becomes the entry. -/

private def entryHeader :=
#strata
program Core;
procedure P(inout x : int)
spec { requires (int.ge(x, 0)); ensures [x_zero]: (x == 0); }
cfg entry {
  @[loopInvariant = (int.ge(x, 0))]
  entry: {
    branch (int.gt(x, 0)) goto dec else goto done;
  }
  dec: { x := int.sub(x, 1); goto entry; }
  done: { return; }
};
#end

/--
info: program Core;

procedure P (inout x : int)
spec {
  requires [P_requires_0]: int.ge(x, 0);
  ensures [x_zero]: x == 0;
  } cfg loopElim_pre_entry {
  entry: {
    branch (int.gt(x, 0)) goto dec else goto done;
  }
  dec: {
    x := int.sub(x, 1);
    goto loopElim_back_dec_entry;
  }
  done: {
    return;
  }
  loopElim_pre_entry: {
    assert [cfgLoopElimAssert_entry_entry_0]: int.ge(x, 0);
    assume [$__cfgLoopElimAssume_havoc_entry]: true;
    havoc x;
    assume [$__cfgLoopElimAssume_invariant_entry_0]: int.ge(x, 0);
    goto entry;
  }
  loopElim_back_dec_entry: {
    assert [cfgLoopElimAssert_maintain_entry_dec_0]: int.ge(x, 0);
    assume [$__cfgLoopElimAssume_cut_entry_dec]: false;
    return;
  }
};
-/
#guard_msgs in
#eval printCut entryHeader.program

/--
info:
Obligation: cfgLoopElimAssert_entry_entry_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_entry_dec_0
Property: assert
Result: ✅ pass

Obligation: x_zero
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run entryHeader

/-! ## A local declared inside a loop

A declaration in a loop would run again on every iteration, which `init` cannot,
so the cut rejects it. -/

private def loopLocalPgm :=
#strata
program Core;
procedure P(inout x : int)
cfg entry {
  entry: { goto loop; }
  loop: {
    var t : int := x;
    x := t;
    branch (int.gt(x, 0)) goto loop else goto done;
  }
  done: { return; }
};
#end

/--
info: error: procedure 'P': block 'loop' declares 't' inside the loop at 'loop'; a local must be
  declared before the loop
-/
#guard_msgs (whitespace := lax) in
#eval printCut loopLocalPgm.program

/-! ## A header with two back edges

`mid` returns to the header early, as a `continue` would, and `tail` at the end of
the body: each back edge gets its own back-edge block, with its own maintenance
check (`…maintain_loop_mid_0` and `…maintain_loop_tail_0`), and both hold. -/

private def twoBackEdges :=
#strata
program Core;
procedure P(n : int, c : bool, out x : int)
spec { ensures [x_nonneg]: (int.ge(x, 0)); }
cfg entry {
  entry: { x := 0; goto loop; }
  @[loopInvariant = (int.ge(x, 0))]
  loop: { branch (int.lt(x, n)) goto body else goto done; }
  body: { x := int.add(x, 1); branch (c) goto mid else goto tail; }
  mid: { goto loop; }
  tail: { x := int.add(x, 1); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_mid_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_tail_0
Property: assert
Result: ✅ pass

Obligation: x_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run twoBackEdges

/-! ## Where a failed invariant check points

An entry check points at its invariant, and a maintenance check at its back edge's source
(here `mid` and `tail`); the description gives the invariant's index. -/

/-- The cut's invariant checks of `p`, each with what its location is: an invariant of the
    header (by index) or a block's transfer (by label). -/
private def checkLocations (p : StrataDDM.Program) : List String :=
  let q := translate p
  let rangeOf (md : Imperative.MetaData Core.Expression) :=
    (Imperative.getFileRange md).map (·.range)
  let blocks := q.decls.flatMap fun d => match d with
    | .proc pr _ => match pr.body with | .cfg g _ => g.blocks | _ => []
    | _ => []
  let invRanges := blocks.flatMap fun (_, b) =>
    (b.md.loopInvariantValues.filterMap fun v => match v with
      | .expr e => some e.metadata.range | _ => none).zipIdx
  let name (md : Imperative.MetaData Core.Expression) : String :=
    match rangeOf md with
    | none => "no location"
    | some r =>
      match invRanges.find? (·.1 == r) with
      | some (_, i) => s!"invariant {i}"
      | none => match blocks.find? (fun (_, b) => rangeOf b.transfer.md == some r) with
        | some (l, _) => s!"the transfer of {l}"
        | none => "elsewhere"
  match Core.Transform.run q Core.CFGLoopElim.cfgLoopElim with
  | .ok (_, p') => p'.decls.flatMap fun d => match d with
    | .proc pr _ => match pr.body with
      | .cfg g _ => g.blocks.flatMap fun (_, b) => b.cmds.filterMap fun c => match c with
        | .cmd (.assert l _ md) =>
          if l.startsWith Core.CFGLoopElim.cfgLoopElimAssertPrefix then some s!"{l}: {name md}"
          else none
        | _ => none
      | _ => []
    | _ => []
  | .error e => [s!"error: {e}"]

/--
info: cfgLoopElimAssert_entry_loop_0: invariant 0
cfgLoopElimAssert_maintain_loop_mid_0: the transfer of mid
cfgLoopElimAssert_maintain_loop_tail_0: the transfer of tail
-/
#guard_msgs (whitespace := lax) in
#eval (checkLocations twoBackEdges.program).forM IO.println

#guard Core.cfgLoopElimPipelinePhase.phase.getAssertDescription
  "cfgLoopElimAssert_maintain_loop_mid_1" == some "loop invariant 1 maintained"
#guard Core.cfgLoopElimPipelinePhase.phase.getAssertDescription
  "cfgLoopElimAssert_entry_loop_0" == some "loop invariant 0 on entry"

/-! ## A nondeterministic `goto` inside a loop

The translator declares the choice of `goto body, done` (`$__nondet_0`) in the
header, which is on the cycle. `hoistNondetChoices`, which runs before type checking,
declares it once, at the entry, and havocs it in the header, so the loop is cut like any
other, and `y` is still known to stay non-negative. `bad`, which needs the loop to run,
fails: its counterexample rests on the cut, but replaying it through the program before the
cut (`CFGLoopElim.replayValidates`) gives a run that skips the loop and ends with `y = 0`. -/

private def nondetInLoop :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [pos]: (int.ge(y, 0)); ensures [bad]: (int.gt(y, 0)); }
cfg entry {
  entry: { y := 0; goto h; }
  @[loopInvariant = (int.ge(y, 0))]
  h: { goto body, done; }
  body: { y := int.add(y, 1); goto h; }
  done: { return; }
};
#end

/--
info: Obligation: cfgLoopElimAssert_entry_h_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_h_body_0
Property: assert
Result: ✅ pass

Obligation: pos
Property: assert
Result: ✅ pass

Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval run nondetInLoop

-- The same under merge mode `never` (one path per way through the body).
/--
info: Obligation: cfgLoopElimAssert_entry_h_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_h_body_0
Property: assert
Result: ✅ pass

Obligation: pos
Property: assert
Result: ✅ pass

Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval run nondetInLoop .never

/-! ## Declarations at the entry when the entry is not listed first

In the concrete syntax a declaration is in scope only in the blocks listed after it, so the
block that receives the hoisted declarations goes first, and the printed output parses back.
Here the loop is listed before `entry`. -/

private def entryListedLast :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [pos]: (int.ge(y, 0)); }
cfg entry {
  @[loopInvariant = (int.ge(y, 0))]
  h: { goto body, done; }
  body: { y := int.add(y, 1); goto h; }
  done: { return; }
  entry: { y := 0; goto h; }
};
#end

/-- `phases`, run in order on `p`. -/
private def afterPhases (phases : List (Core.Program → Core.Transform.CoreTransformM
    (Bool × Core.Program))) (p : StrataDDM.Program) : Except String Core.Program :=
  Core.Transform.run (translate p) (phases.foldlM (fun q f => do
    let (_, q') ← f q
    pure q') ·) |>.mapError toString

/-- The block labels of each CFG body of `p`, in the order they are listed. -/
private def blockLabels (p : Core.Program) : List String :=
  p.decls.flatMap fun d => match d with
    | .proc q _ => match q.body with
      | .cfg g _ => g.blocks.map (·.1)
      | _ => []
    | _ => []

/-- The block labels after `phases`, and whether the printed output parses back. -/
private def printReparse (phases : List (Core.Program → Core.Transform.CoreTransformM
    (Bool × Core.Program))) (p : StrataDDM.Program) : IO Unit :=
  match afterPhases phases p with
  | .ok q => do
    let back ← Strata.Test.CoreReparse.parseAndTranslate (Core.formatProgram q).pretty
    IO.println s!"{blockLabels q}, re-parses: {back.isOk}"
  | .error e => IO.println s!"error: {e}"

/-- info: [entry, h, body, done], re-parses: true -/
#guard_msgs in
#eval printReparse [Core.CFGLoopElim.hoistNondetChoicesInLoops] entryListedLast.program

/-- info: [entry, h, body, done, loopElim_pre_h, loopElim_back_body_h], re-parses: true -/
#guard_msgs in
#eval printReparse [Core.CFGLoopElim.hoistNondetChoicesInLoops, Core.CFGLoopElim.cfgLoopElim]
  entryListedLast.program

/-- The variables block `lbl` of each CFG body of `p` declares nondeterministically (`init x
    := *`) and havocs (`x := *`), in command order. -/
private def nondetOf (p : Core.Program) (lbl : String) : List String × List String :=
  p.decls.foldl (fun acc d => match d with
    | .proc q _ => match q.body with
      | .cfg g _ => match g.blocks.lookup lbl with
        | some b =>
          (acc.1 ++ b.cmds.filterMap (fun | .cmd (.init x _ .nondet _) => some x.name | _ => none),
           acc.2 ++ b.cmds.filterMap (fun | .cmd (.set x .nondet _) => some x.name | _ => none))
        | none => acc
      | _ => acc
    | _ => acc) ([], [])

-- After the hoist and the cut, `nondetInLoop`'s choice is declared once at the entry, the
-- header still chooses it afresh (`$__nondet_0 := *`), and the pre-header havocs it with the
-- loop's other writes.
/--
info: entry: ([$__nondet_0], []), h: ([], [$__nondet_0]), loopElim_pre_h: ([], [$__nondet_0, y])
-/
#guard_msgs (whitespace := lax) in
#eval match afterPhases [Core.CFGLoopElim.hoistNondetChoicesInLoops, Core.CFGLoopElim.cfgLoopElim]
    nondetInLoop.program with
  | .ok q => IO.println (", ".intercalate (["entry", "h", "loopElim_pre_h"].map
      fun l => s!"{l}: {nondetOf q l}"))
  | .error e => IO.println s!"error: {e}"

/-! The cut lists its pre-headers after the input's blocks, since a pre-header havocs
variables declared there: here `x` is declared in `d`, listed after the header `h`. -/

private def declListedAfterHeader :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [pos]: (int.ge(y, 0)); }
cfg entry {
  entry: { y := 0; goto d; }
  h: { goto body, done; }
  d: { var x : int := 0; goto h; }
  body: { x := int.add(x, 1); y := x; goto h; }
  done: { return; }
};
#end

/-- info: [entry, h, d, body, done, loopElim_pre_h, loopElim_back_body_h], re-parses: true -/
#guard_msgs in
#eval printReparse [Core.CFGLoopElim.hoistNondetChoicesInLoops, Core.CFGLoopElim.cfgLoopElim]
  declListedAfterHeader.program


/-! ## Nested loops

The inner loop's blocks are part of the outer loop, so the outer loop havocs
`s`, `j` and `i`; the inner loop havocs `s` and `j`. The locals `i` and `j` are
declared before the loops that modify them. -/

private def nestedPgm :=
#strata
program Core;
procedure P(n : int, out s : int)
spec { requires (int.ge(n, 0)); ensures [s_nonneg]: (int.ge(s, 0)); }
cfg entry {
  entry: { var i : int := 0; var j : int := 0; s := 0; goto outer; }
  @[loopInvariant = (int.ge(s, 0)), loopInvariant = (int.le(i, n))]
  outer: { branch (int.lt(i, n)) goto obody else goto done; }
  obody: { j := 0; goto inner; }
  @[loopInvariant = (int.ge(s, 0)), loopInvariant = (int.lt(i, n))]
  inner: { branch (int.lt(j, i)) goto ibody else goto onext; }
  ibody: { s := int.add(s, 1); j := int.add(j, 1); goto inner; }
  onext: { i := int.add(i, 1); goto outer; }
  done: { return; }
};
#end

-- The cut: each pre-header havocs exactly the variables its loop writes.
/--
info: program Core;

procedure P (n : int, out s : int)
spec {
  requires [P_requires_0]: int.ge(n, 0);
  ensures [s_nonneg]: int.ge(s, 0);
  } cfg entry {
  entry: {
    var i : int := 0;
    var j : int := 0;
    s := 0;
    goto loopElim_pre_outer;
  }
  outer: {
    branch (int.lt(i, n)) goto obody else goto done;
  }
  obody: {
    j := 0;
    goto loopElim_pre_inner;
  }
  inner: {
    branch (int.lt(j, i)) goto ibody else goto onext;
  }
  ibody: {
    s := int.add(s, 1);
    j := int.add(j, 1);
    goto loopElim_back_ibody_inner;
  }
  onext: {
    i := int.add(i, 1);
    goto loopElim_back_onext_outer;
  }
  done: {
    return;
  }
  loopElim_pre_outer: {
    assert [cfgLoopElimAssert_entry_outer_0]: int.ge(s, 0);
    assert [cfgLoopElimAssert_entry_outer_1]: int.le(i, n);
    assume [$__cfgLoopElimAssume_havoc_outer]: true;
    havoc j;
    havoc s;
    havoc i;
    assume [$__cfgLoopElimAssume_invariant_outer_0]: int.ge(s, 0);
    assume [$__cfgLoopElimAssume_invariant_outer_1]: int.le(i, n);
    goto outer;
  }
  loopElim_pre_inner: {
    assert [cfgLoopElimAssert_entry_inner_0]: int.ge(s, 0);
    assert [cfgLoopElimAssert_entry_inner_1]: int.lt(i, n);
    assume [$__cfgLoopElimAssume_havoc_inner]: true;
    havoc s;
    havoc j;
    assume [$__cfgLoopElimAssume_invariant_inner_0]: int.ge(s, 0);
    assume [$__cfgLoopElimAssume_invariant_inner_1]: int.lt(i, n);
    goto inner;
  }
  loopElim_back_ibody_inner: {
    assert [cfgLoopElimAssert_maintain_inner_ibody_0]: int.ge(s, 0);
    assert [cfgLoopElimAssert_maintain_inner_ibody_1]: int.lt(i, n);
    assume [$__cfgLoopElimAssume_cut_inner_ibody]: false;
    return;
  }
  loopElim_back_onext_outer: {
    assert [cfgLoopElimAssert_maintain_outer_onext_0]: int.ge(s, 0);
    assert [cfgLoopElimAssert_maintain_outer_onext_1]: int.le(i, n);
    assume [$__cfgLoopElimAssume_cut_outer_onext]: false;
    return;
  }
};
-/
#guard_msgs in
#eval printCut nestedPgm.program

/--
info:
Obligation: cfgLoopElimAssert_entry_outer_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_outer_1
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_inner_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_inner_1
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_inner_ibody_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_inner_ibody_1
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_outer_onext_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_outer_onext_1
Property: assert
Result: ✅ pass

Obligation: s_nonneg
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run nestedPgm

/-! ## Rejections -/

-- Irreducible control flow: neither `a` nor `b` dominates the other.
private def irreduciblePgm :=
#strata
program Core;
procedure P(c : bool, out y : int)
cfg entry {
  entry: { y := 0; branch (c) goto a else goto b; }
  a: { y := int.add(y, 1); goto b; }
  b: { y := int.add(y, 2); goto a; }
};
#end

/--
info: error: procedure 'P': irreducible control flow: the cycle through [a, b] has no loop header
  that dominates it, so its loops cannot be cut
-/
#guard_msgs (whitespace := lax) in
#eval run irreduciblePgm

-- An invariant must be an expression.
private def nonExprInvPgm :=
#strata
program Core;
procedure P(out y : int)
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = "y >= 0"]
  loop: { goto loop; }
};
#end

/--
info: error: procedure 'P': the `loopInvariant` metadata of block 'loop' must be an expression,
  `@[loopInvariant = (e)]`
-/
#guard_msgs (whitespace := lax) in
#eval run nonExprInvPgm

-- On an unreachable block, where placement is not checked, such an annotation is dropped.
private def nonExprInvDeadPgm :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [y0]: (y == 0); }
cfg entry {
  entry: { y := 0; goto done; }
  @[loopInvariant = "y >= 0"]
  dead: { goto done; }
  done: { return; }
};
#end

/--
info:
Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run nonExprInvDeadPgm

-- An invariant must be boolean: it becomes an `assert`, which the type checker
-- requires to be boolean.
private def intInvPgm :=
#strata
program Core;
procedure P(out y : int)
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.add(y, 1))]
  loop: { y := int.add(y, 1); goto loop; }
};
#end

/--
info: error: Procedure 'P': Assertion cfgLoopElimAssert_entry_loop_0 expected to be of type boolean,
  but inferred type is int.
-/
#guard_msgs (whitespace := lax) in
#eval
  -- The generated assert points at the invariant; its source offsets are dropped from the
  -- message (the text up to the first `) `).
  let p := (translate intInvPgm.program).stripMetaData
  match Core.Transform.run p Core.CFGLoopElim.cfgLoopElim with
  | .ok (_, p') =>
    let msg := toString (Std.format (Core.typeCheck .default p'))
    IO.println (match msg.splitOn ") " with
      | pre :: rest@(_ :: _) => (pre.takeWhile (· != '(')).toString ++ ") ".intercalate rest
      | _ => msg)
  | .error e => IO.println s!"error: {e}"

-- In the pipeline, the type check before the cut already rejects it.
/--
info: error: ❌ Type checking error.
Procedure 'P': [P]: in metadata `loopInvariant` of block "loop": the invariant is not of type bool,
  got int
-/
#guard_msgs (whitespace := lax) in
#eval run intInvPgm

/-! ## A call inside a loop

The cut runs before call elimination, so the call's temporaries are declared in an
acyclic body. -/

private def callInLoop :=
#strata
program Core;
procedure Inc(x : int, out r : int)
spec { ensures [inc_post]: (r == int.add(x, 1)); }
{ r := int.add(x, 1); };
procedure P(n : int, out y : int)
spec { requires (int.ge(n, 0)); ensures [y_eq_n]: (y == n); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.le(y, n))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { call Inc(y, out y); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: inc_post
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: y_eq_n
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run callInLoop

-- With call elimination before the cut, the call's temporaries are declared inside the loop,
-- and the cut refuses them with a hint.
/--
info: error: procedure 'P': block 'body' declares 'tmp_arg_0' inside the loop at 'loop'; a local
  must be declared before the loop; if it is a call elimination temporary, run call elimination
  after cfgLoopElim
-/
#guard_msgs (whitespace := lax) in
#eval show IO Unit from do
  match ← (Strata.Core.runTransforms (translate callInLoop.program)
      [Strata.Core.passTypeCheck Core.VerifyOptions.quiet, Strata.Core.passCallElim,
       Strata.Core.passCFGLoopElim]).toBaseIO with
  | .ok _ => IO.println "ok"
  | .error e => IO.println s!"error: {e}"

-- The same program under merge mode `never` (one path per way through the body).
/--
info:
Obligation: inc_post
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: y_eq_n
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run callInLoop .never

/-! ## A precondition in an invariant

A call of a function with a precondition in an invariant gets that precondition
checked. -/

private def divInvPgm :=
#strata
program Core;
function safeMod(x : int, y : int) : int
  requires y != 0;
{ int.safeMod(x, y) }
procedure P(n : int, out y : int)
spec { requires (int.gt(n, 0)); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.ge(safeMod(y, n), 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: safeMod_body_calls_Int.SafeMod_0
Property: division by zero check
Result: ✅ pass

Obligation: assert_cfgLoopElimAssert_entry_loop_0_calls_safeMod_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: assume_$__cfgLoopElimAssume_invariant_loop_0_calls_safeMod_0
Property: assert
Result: ✅ pass

Obligation: assert_cfgLoopElimAssert_maintain_loop_body_0_calls_safeMod_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run divInvPgm

-- Precondition elimination runs after the cut: it refuses a block that still carries a
-- `loopInvariant`.
/--
info: error: procedure 'P': block 'loop' has a `loopInvariant`; run `cfgLoopElim` before
  precondition elimination
-/
#guard_msgs (whitespace := lax) in
#eval
  match Core.Transform.run (translate divInvPgm.program) _root_.Core.PrecondElim.precondElim
      { _root_.Core.Transform.CoreTransformState.emp with factory := _root_.Core.Factory } with
  | .ok _ => IO.println "ok"
  | .error e => IO.println s!"error: {e}"

/-! ## Unreachable annotated blocks

The type checker checks the placement of a `loopInvariant` only on reachable blocks, so an
unreachable block may carry one. The cut drops it, as it does from the headers it cuts, so
its output has no `loopInvariant` on any block, and precondition elimination, which refuses
a block that still has one, accepts it. -/

private def deadAnnotated :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [y0]: (y == 0); }
cfg entry {
  entry: { y := 0; goto done; }
  @[loopInvariant = (int.ge(y, 0))]
  dead: { goto done; }
  done: { return; }
};
#end

private def deadLoop :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [y0]: (y == 0); }
cfg entry {
  entry: { y := 0; goto done; }
  @[loopInvariant = (int.ge(y, 0))]
  dh: { branch (int.lt(y, 10)) goto db else goto done; }
  db: { y := int.add(y, 1); goto dh; }
  done: { return; }
};
#end

private def liveLoopAndDead :=
#strata
program Core;
procedure P(out y : int)
spec { ensures [pos]: (int.ge(y, 0)); }
cfg entry {
  entry: { y := 0; goto h; }
  @[loopInvariant = (int.ge(y, 0))]
  h: { branch (int.lt(y, 10)) goto body else goto done; }
  body: { y := int.add(y, 1); goto h; }
  @[loopInvariant = (int.ge(y, 0))]
  dead: { goto done; }
  done: { return; }
};
#end

/-- The labels of the blocks of `p` that carry a `loopInvariant`. -/
private def annotatedBlocks (p : Core.Program) : List String :=
  p.decls.flatMap fun d => match d with
    | .proc q _ => match q.body with
      | .cfg g _ => g.blocks.filterMap fun (l, b) =>
        if b.md.loopInvariantValues.isEmpty then none else some l
      | _ => []
    | _ => []

#guard annotatedBlocks (translate deadAnnotated.program) == ["dead"]
#guard annotatedBlocks (translate deadLoop.program) == ["dh"]
#guard annotatedBlocks (translate liveLoopAndDead.program) == ["h", "dead"]
#guard [deadAnnotated, deadLoop, liveLoopAndDead].all fun p =>
  match afterPhases [Core.CFGLoopElim.cfgLoopElim] p.program with
  | .ok q => annotatedBlocks q == []
  | .error _ => false

/--
info:
Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run deadAnnotated

/--
info:
Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run deadAnnotated .never

/--
info:
Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run deadLoop

/--
info:
Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run deadLoop .never

/--
info:
Obligation: cfgLoopElimAssert_entry_h_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_h_body_0
Property: assert
Result: ✅ pass

Obligation: pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run liveLoopAndDead

/--
info:
Obligation: cfgLoopElimAssert_entry_h_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_h_body_0
Property: assert
Result: ✅ pass

Obligation: pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval run liveLoopAndDead .never

/-! ## The registered pass

The pass is named `cfgLoopElim` (as in `strata transform --pass cfgLoopElim`),
and `--vcgen symexec` runs it after the procedure filter and before call elimination. -/

#guard Strata.Core.passCFGLoopElim.phase.name == "cfgLoopElim"
#guard ((Core.transformPipelinePhases
    { Core.VerifyOptions.default with symExec := some .always }).map (·.phase.name)).take 4 ==
  ["hoistNondetChoices", "typeCheck", "cfgLoopElim", "callElim"]
#guard !((Core.transformPipelinePhases).any (·.phase.name == "cfgLoopElim"))

-- `strata transform --pass cfgLoopElim` hoists the choices of nondeterministic `goto`s before
-- type checking, as `--vcgen symexec` does; other passes are type-checked only.
#guard (Strata.Core.transformPrefix ["cfgLoopElim"]).map (·.phase.name) ==
  ["hoistNondetChoices", "typeCheck"]
#guard (Strata.Core.transformPrefix ["callElim"]).map (·.phase.name) == ["typeCheck"]
-- With that prefix, a nondeterministic `goto` in a loop is cut; with type checking alone, the
-- choice declared in the loop is rejected.
/-- Whether running `phases` on `p` succeeds. -/
private def phasesSucceed (phases : List Core.PipelinePhase) (p : StrataDDM.Program) :
    IO Bool := do
  return (← (Strata.Core.runTransforms (translate p) phases).toBaseIO).toBool

/-- info: (true, false) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  let withPrefix ← phasesSucceed
    (Strata.Core.transformPrefix ["cfgLoopElim"] ++ [Strata.Core.passCFGLoopElim])
    nondetInLoop.program
  let typeCheckOnly ← phasesSucceed
    [Strata.Core.passTypeCheck Core.VerifyOptions.quiet, Strata.Core.passCFGLoopElim]
    nondetInLoop.program
  return (withPrefix, typeCheckOnly)

/-! ## Generated labels stay distinct

The labels of a back edge's checks are built from the header and the source
block. Header `a` with source `b_c`, and header `a_b` with source `c`, make the
same text, so the second gets a numeric suffix. -/

private def collidingPgm :=
#strata
program Core;
procedure P(p : bool, q : bool)
cfg entry {
  entry: { goto a; }
  @[loopInvariant = (p == p)]
  a: { branch (p) goto b_c else goto a_b; }
  b_c: { goto a; }
  @[loopInvariant = (q == q)]
  a_b: { branch (q) goto c else goto done; }
  c: { goto a_b; }
  done: { return; }
};
#end


/-- info: true -/
#guard_msgs in
#eval
  let ls := generatedLabels collidingPgm.program
  ls.length == ls.eraseDups.length && ls.contains "cfgLoopElimAssert_maintain_a_b_c_0" &&
    ls.contains "cfgLoopElimAssert_maintain_a_b_c_1_0"

/-! ## The havoc covers every write in the loop

Each program below would pass if the cut did not havoc the variable it names, though it
fails on a run that goes around the loop. -/

-- `y` is written only by the call's output (call elimination runs after the cut).
private def callOutHavocPgm :=
#strata
program Core;
procedure Inc(x : int, out r : int)
spec { ensures [inc_post]: (r == int.add(x, 1)); }
{ r := int.add(x, 1); };
procedure P(n : int, out y : int)
spec { requires (int.ge(n, 0)); ensures [y_zero]: (y == 0); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.ge(y, 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { call Inc(y, out y); goto loop; }
  done: { return; }
};
#end

/--
info:
Obligation: inc_post
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_body_0
Property: assert
Result: ✅ pass

Obligation: y_zero
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run callOutHavocPgm

-- `x` is written only in the inner loop, so the outer cut havocs it too.
private def innerWriteHavocPgm :=
#strata
program Core;
procedure P(n : int, out x : int, out z : int)
spec { requires (int.ge(n, 0)); ensures [x_zero]: (x == 0); }
cfg entry {
  entry: { x := 0; z := 0; goto outer; }
  @[loopInvariant = (int.ge(z, 0))]
  outer: { branch (int.lt(z, n)) goto ihead else goto done; }
  ihead: { branch (int.lt(x, 1)) goto ibody else goto onext; }
  ibody: { x := int.add(x, 1); goto ihead; }
  onext: { z := int.add(z, 1); goto outer; }
  done: { return; }
};
#end

/--
info:
Obligation: cfgLoopElimAssert_entry_outer_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_outer_onext_0
Property: assert
Result: ✅ pass

Obligation: x_zero
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval run innerWriteHavocPgm

/-! ## Without the cut

The path explorer requires `noCFGCycles`, so a CFG body with a loop is refused when
`cfgLoopElim` has not run. -/

/-- info: ["noCFGCycles"] -/
#guard_msgs in
#eval ((Core.SymExec.failedRequires (translate countUp.program)).map (·.name))

/-! ## The claimed fact holds on the output

`cfgLoopElim` claims `noCFGCycles` without a proof of it for the whole phase
(`CFGLoopElimProps.cutLoops_acyclic` covers one body), so it is checked on the output
for every program above that the cut accepts, alone and after `hoistNondetChoices`. -/

/-- Whether `phases`, run in order on `p`, succeed with an output with no CFG cycle. -/
private def acyclicAfter (phases : List (Core.Program → Core.Transform.CoreTransformM
    (Bool × Core.Program))) (p : StrataDDM.Program) : Bool :=
  match afterPhases phases p with
  | .ok q => Core.Program.noCFGCycles q
  | .error _ => false

/-- The programs above that the cut accepts on its own: none declares a choice on a cycle. -/
private def cutAlonePrograms : List StrataDDM.Program :=
  [countUp.program, noInvPgm.program, notMaintainedPgm.program, entryHeader.program,
   twoBackEdges.program, nestedPgm.program, callInLoop.program, divInvPgm.program,
   collidingPgm.program, callOutHavocPgm.program, innerWriteHavocPgm.program]

private def cutPrograms : List StrataDDM.Program :=
  cutAlonePrograms ++
    [nondetInLoop.program, entryListedLast.program, declListedAfterHeader.program]

-- Each program has a CFG cycle before the cut, so the check is not vacuous.
#guard cutPrograms.all fun p => !Core.Program.noCFGCycles (translate p)
#guard cutAlonePrograms.all (acyclicAfter [Core.CFGLoopElim.cfgLoopElim])
-- Without `hoistNondetChoices`, the choice declared on the cycle makes the cut refuse.
#guard !acyclicAfter [Core.CFGLoopElim.cfgLoopElim] nondetInLoop.program
#guard cutPrograms.all
  (acyclicAfter [Core.CFGLoopElim.hoistNondetChoicesInLoops, Core.CFGLoopElim.cfgLoopElim])
-- No block of the output carries a `loopInvariant`.
#guard cutPrograms.all fun p =>
  match afterPhases
      [Core.CFGLoopElim.hoistNondetChoicesInLoops, Core.CFGLoopElim.cfgLoopElim] p with
  | .ok q => annotatedBlocks q == []
  | .error _ => false

/-! ## Long chains

Dominators are only computed for a body with a cycle, so an acyclic body with no annotated
unreachable block is passed through unchanged; a body with a cycle gains a pre-header and
one block per back edge. Each line is whether the body changed and its number of blocks. -/

/-- A chain of `n` blocks, with a back edge from the last to the second when `loop`. -/
private def chainCfg (n : Nat) (loop : Bool) : Imperative.DetCFG Core.Expression Core.Command :=
  { entry := "b0",
    blocks := (List.range n).map fun i =>
      (s!"b{i}", ({ cmds := [], transfer :=
        if i + 1 < n then .goto s!"b{i+1}"
        else if loop then .goto "b1" else .finish .empty } :
        Imperative.DetBlock String Core.Command Core.Expression)) }

/--
info: false 8000
true 1002
-/
#guard_msgs (whitespace := lax) in
#eval for (n, loop) in [(8000, false), (1000, true)] do
  match Core.CFGLoopElim.cutLoops "P" (chainCfg n loop) with
  | .ok (changed, g) => IO.println s!"{changed} {g.blocks.length}"
  | .error e => IO.println s!"error: {e}"

/-! ## Under the passive generators

The same cut under `--vcgen usp` and `uwp`: each program's verdicts, by label. A result
that rests on the cut is `unknown` unless replay confirms it (`nondetInLoop`'s `bad`, on
the run that skips the loop). -/

private def passiveVerdicts (p : StrataDDM.SourcedProgram) (m : Core.VCGenMode) :
    IO (List (String × String)) := do
  let r ← Strata.Core.verify p (options := { Core.VerifyOptions.quiet with vcgen := m })
  pure (r.toList.map fun r => (r.obligation.label,
    if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/--
info: [(y_eq_n, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_entry_loop_1, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass), (cfgLoopElimAssert_maintain_loop_body_1, pass)]
[(y_eq_n, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_entry_loop_1, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass), (cfgLoopElimAssert_maintain_loop_body_1, pass)]
[(y_eq_n, other)]
[(y_eq_n, other)]
[(cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, other)]
[(cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, other)]
[(x_zero, pass), (cfgLoopElimAssert_entry_entry_0, pass), (cfgLoopElimAssert_maintain_entry_dec_0, pass)]
[(x_zero, pass), (cfgLoopElimAssert_entry_entry_0, pass), (cfgLoopElimAssert_maintain_entry_dec_0, pass)]
[(x_nonneg, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_mid_0, pass), (cfgLoopElimAssert_maintain_loop_tail_0, pass)]
[(x_nonneg, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_mid_0, pass), (cfgLoopElimAssert_maintain_loop_tail_0, pass)]
[(pos, pass), (bad, fail), (cfgLoopElimAssert_entry_h_0, pass), (cfgLoopElimAssert_maintain_h_body_0, pass)]
[(pos, pass), (bad, fail), (cfgLoopElimAssert_entry_h_0, pass), (cfgLoopElimAssert_maintain_h_body_0, pass)]
[(s_nonneg, pass), (cfgLoopElimAssert_entry_outer_0, pass), (cfgLoopElimAssert_entry_outer_1, pass), (cfgLoopElimAssert_entry_inner_0, pass), (cfgLoopElimAssert_entry_inner_1, pass), (cfgLoopElimAssert_maintain_inner_ibody_0, pass), (cfgLoopElimAssert_maintain_inner_ibody_1, pass), (cfgLoopElimAssert_maintain_outer_onext_0, pass), (cfgLoopElimAssert_maintain_outer_onext_1, pass)]
[(s_nonneg, pass), (cfgLoopElimAssert_entry_outer_0, pass), (cfgLoopElimAssert_entry_outer_1, pass), (cfgLoopElimAssert_entry_inner_0, pass), (cfgLoopElimAssert_entry_inner_1, pass), (cfgLoopElimAssert_maintain_inner_ibody_0, pass), (cfgLoopElimAssert_maintain_inner_ibody_1, pass), (cfgLoopElimAssert_maintain_outer_onext_0, pass), (cfgLoopElimAssert_maintain_outer_onext_1, pass)]
[(inc_post, pass), (y_eq_n, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass)]
[(inc_post, pass), (y_eq_n, pass), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass)]
-/
#guard_msgs in
#eval show IO Unit from do
  for p in [countUp, noInvPgm, notMaintainedPgm, entryHeader, twoBackEdges, nondetInLoop,
            nestedPgm, callInLoop] do
    for m in [Core.VCGenMode.usp, .uwp] do
      IO.println (← passiveVerdicts p m)

end Strata.Test.CFGLoopElim

end

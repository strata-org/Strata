/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import Strata.Languages.Core.Options
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Transform.CallElim
meta import Strata.DL.Imperative.StructuredToPassiveCFG
meta import Strata.Transform.MonomorphizeFunctions
meta import Strata.Transform.PrecondElim
meta import Strata.Transform.PassiveVCGenCoreProgram
meta import Strata.Transform.CFGLoopElimReplay
meta import Strata.Transform.CFGLoopElim
meta import Strata.Languages.Core.DDMTransform.ASTtoCST
meta import StrataTest.Languages.Core.Tests.CoreTextTestUtils
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Passive VC generation: regression tests

Each section pins one behavior of `--vcgen uwp/usp` that a change could break:
a verdict, a rejection, or the shape of a pipeline. -/

namespace Strata.Test.PassiveVCGenRegression

open Strata

private def verify (p : StrataDDM.SourcedProgram) (mode : Core.VCGenMode := .usp)
    (procs : Option (List String) := none) : IO Unit := do
  try
    IO.println (← Strata.Core.verify p (options :=
      { Core.VerifyOptions.quiet with vcgen := mode, proceduresToVerify := procs }))
  catch e => IO.println s!"error: {e}"

/-! ## A user annotation does not mark a block as a back-edge block

Only a returning block containing `assume false` gets no postcondition. A block
annotated `@[loopCutBlock]` (a key with no meaning to the pipeline) is an ordinary
exit, and `post` is checked there. -/

def userAnnotation :=
#strata
program Core;
procedure P(x : int, out y : int)
spec { ensures [post]: (y == 1); }
cfg entry {
  entry: { y := x; goto done; }
  @[loopCutBlock] done: { return; }
};
#end

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify userAnnotation

/-! ## A cover in an unreachable block fails

`dead` is not reachable from the entry, so no execution meets its cover. -/

def unreachableCover :=
#strata
program Core;
procedure P(x : int)
cfg entry {
  entry: {
    assert [live]: (x == x);
    return;
  }
  dead: {
    cover [dead_cover]: (x == x);
    assert [dead_assert]: (x == 0);
    return;
  }
};
#end

/--
info:
Obligation: live
Property: assert
Result: ✅ pass

Obligation: dead_cover
Property: cover
Result: ❌ fail

Obligation: dead_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify unreachableCover

/--
info:
Obligation: live
Property: assert
Result: ✅ pass

Obligation: dead_cover
Property: cover
Result: ❌ fail

Obligation: dead_assert
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify unreachableCover (mode := .uwp)

/-! ## A callee's contract reaches a counterexample through many joins

The call is preceded by twelve diamonds. The counterexample to `tgt` rests on
the callee's contract (`r` may be `0`), so it is reported `unknown`, not `fail`,
whichever branch makes the call. -/

def diamondsThenCall :=
#strata
program Core;
procedure F(a : int, out r : int) spec { ensures [fe]: (int.ge(r, 0)); } { r := 0; };
procedure T(x : int, c : bool, d : bool, out r : int) {
  var z : int := 0;
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (c) { z := 1; } else { z := 2; }
  if (d) { r := 1; } else { call F(x, out r); }
  assert [tgt]: (int.gt(r, 0));
};
#end

/--
info:
Obligation: fe
Property: assert
Result: ✅ pass

Obligation: tgt
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval verify diamondsThenCall

/-! ## Same-named locals of different types in sibling scopes

The two `t`s are renamed apart before lowering, which gives each variable one
type. -/

def siblings :=
#strata
program Core;
procedure Test(y : int)
{
  if (int.gt(y, 0)) {
    var t : int := 1;
    assert [a]: (t == 1);
  } else {
    var t : bool := true;
    assert [b]: (t == true);
  }
  assert [c]: (y == y);
};
#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ✅ pass

Obligation: c
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify siblings

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ✅ pass

Obligation: c
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify siblings (mode := .uwp)

/-! ## A call inside a CFG loop

Call elimination declares the temporaries of a call at the start of the entry
block and assigns them at the call, so the loop does not declare a variable on
every iteration, and the body type-checks. -/

def loopCall :=
#strata
program Core;
procedure f(x : int, out y : int)
spec {
  requires (int.ge(x, 0));
  ensures (int.gt(y, x));
}
{ y := int.add(x, 1); };
procedure h(a : int, out r : int)
spec { ensures [pos]: (int.gt(r, 0)); }
cfg entry {
  entry: {
    r := 0;
    goto loop;
  }
  @[loopInvariant = (int.ge(r, 0))]
  loop: {
    call f(r, out r);
    branch (int.lt(r, a)) goto loop else goto done;
  }
  done: {
    return;
  }
};
#end

/--
info: Obligation: f_ensures_1
Property: assert
Result: ✅ pass

Obligation: callElimAssert_f_requires_0_2
Property: assert
Result: ✅ pass

Obligation: pos
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_loop_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify loopCall

/-! ## `--vcgen symbolic` refuses only the CFG bodies of the procedures verified

With `--procedures S`, the CFG body of `Q` is not verified, so `S`'s structured loop is
verified by symbolic evaluation. Verifying `Q` is refused, with the advice to pass
`--vcgen symexec` or `--vcgen usp`: the default generator does not fall back to another
generator. -/

def mixed :=
#strata
program Core;
procedure S(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n)) invariant (int.ge(i, 0)) {
    i := int.add(i, 1);
  }
  assert [s_ok]: (int.ge(i, 0));
};
procedure Q(x : int, out y : int)
spec { ensures [q_ok]: (y == x); }
cfg entry {
  entry: { y := x; return; }
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

Obligation: s_ok
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify mixed (mode := .symbolic) (procs := some ["S"])

/--
info: error: ❌ Expected every procedure body to be structured, but found procedure Q with a CFG body. To verify it, pass --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp).
-/
#guard_msgs in
#eval verify mixed (mode := .symbolic) (procs := some ["Q"])

/-! ## `goto` is one edge

`goto l` is a branch with both targets `l`. It becomes a single edge, with no
guard, so `post` is checked once along it. -/

def gotoPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
spec { ensures [post]: (y == int.add(x, 1)); }
cfg entry {
  entry: { y := int.add(x, 1); goto done; }
  done: { return; }
};
#end

/-- The passification CFG of `P`: its blocks' labels and successors. -/
private def gotoEdges : List (String × List String) :=
  let p := (TransM.run Inhabited.default (translateProgram gotoPgm.program)).fst
  match p.decls.findSome? fun d => match d with
      | .proc proc _ => match proc.body with
        | .cfg g _ => some g
        | _ => none
      | _ => none with
  | some g => match Imperative.StructuredToPassiveCFG.convert (P := Core.Expression) g with
    | .ok pcfg => pcfg.blocks.map fun (l, b) => (l, b.succs)
    | .error _ => []
  | none => []

/-- info: [("entry", ["done"]), ("done", [])] -/
#guard_msgs in
#eval gotoEdges

/-! ## An explicit pipeline is run as given

Under `--vcgen symbolic`, the default order refuses a CFG body. An explicit pipeline
(here, the order of `usp`) is run as given, whatever `--vcgen` says. -/

/-- info: [(post, true)] -/
#guard_msgs in
#eval show IO Unit from do
  let phases := Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }
  let vp ← match Strata.Core.validatePipeline phases with
    | .ok vp => pure vp
    | .error e => throw (IO.userError e)
  let p := (TransM.run Inhabited.default (translateProgram gotoPgm.program)).fst
  match ← (Strata.Core.verifyProgram p Core.VerifyOptions.quiet (pipeline := some vp)).toBaseIO with
  | .ok results => IO.println (results.toList.map fun r => (r.obligation.label, r.isSuccess))
  | .error e => IO.println s!"error: {e}"

/-! ## Under `uwp`, an obligation's query holds only its own goal

`lam` compares two functions, which the SMT encoder cannot express (and the
simplifier cannot decide, as they differ). Its
weakest-precondition definitions are local to its own obligation, so `ok` is
unaffected. -/

def lambdaGoal :=
#strata
program Core;
procedure P(p : bool, q : bool)
{
  assert [lam]: (fun y : int => p) == (fun y : int => q);
  assert [ok]: (p == p);
};
#end

/-- info: [(lam, false), (ok, true)] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify lambdaGoal
    (options := { Core.VerifyOptions.quiet with vcgen := .uwp })
  IO.println (r.toList.map fun r => (r.obligation.label, r.isSuccess))

/-! ## A free postcondition is not assumed

The body does not establish `fe`, so it must not help prove `post`. -/

def freeEnsures :=
#strata
program Core;
procedure P(x : int, out y : int)
spec { free ensures [fe]: (y == 0); ensures [post]: (y == 0); }
{ y := 1; };
#end

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify freeEnsures

/--
info:
Obligation: post
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify freeEnsures (mode := .uwp)

/-! ## A check after a loop cut's havoc is validated

The invariant divides by `y`. Its check where the cut assumes it rests on the
havoc, an arbitrary iteration, so a counterexample is `unknown`, not `fail`. -/

def havocCheck :=
#strata
program Core;
procedure P(n : int, out y : int)
cfg entry {
  entry: { y := 1; goto loop; }
  @[loopInvariant = (int.ge(int.safeDiv(10, y), 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := 1; goto loop; }
  done: { return; }
};
#end

/-- info: [(assume_$__cfgLoopElimAssume_invariant_loop_0_calls_Int.SafeDiv_0, unknown)] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify havocCheck
    (options := { Core.VerifyOptions.quiet with vcgen := .usp })
  IO.println (r.toList.filterMap fun r =>
    if r.obligation.label.startsWith "assume_" then
      some (r.obligation.label, if r.isSuccess then "pass" else if r.isFailure then "fail" else "unknown")
    else none)

/-! ## A local declared inside a CFG loop is rejected

The CFG type checker, which runs first, rejects it; loop elimination would too,
before removing the cycle (`CFGLoopElimTest`). -/

def loopLocal :=
#strata
program Core;
procedure P(n : int)
cfg entry {
  entry: { goto loop; }
  loop: { var t : int := 1; assert [t1]: (t == 1); goto loop, done; }
  done: { return; }
};
#end

/--
info: error: ❌ Type checking error.
Procedure 'P': [P]: a CFG-local is declared in a block that lies on a cycle; a loop-carried declaration would be re-initialized on re-entry.
-/
#guard_msgs in
#eval verify loopLocal

/-! ## Precondition checks of invariants are not skipped

`f` needs a positive argument, and the invariant calls it with `y`, which is `0`
on entry. Precondition elimination runs after CFG loop elimination, so it checks the
call in the cut's `assert` of the invariant on entry, in the entry state. -/

def partialInvariant :=
#strata
program Core;
function f(x : int) : int
  requires (int.gt(x, 0));
{ x }
procedure P(n : int, out y : int)
spec { requires (int.ge(n, 0)); }
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.ge(f(y), 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/-- Verify `partialInvariant` with `phases`; print whether some check of `f`'s
    precondition fails definitely (as it does in the entry state). -/
private def precondChecked (phases : List Core.PipelinePhase) : IO Unit := do
  let vp ← match Strata.Core.validatePipeline phases with
    | .ok vp => pure vp
    | .error e => IO.println s!"refused: {e}"; return
  let p := (TransM.run Inhabited.default (translateProgram partialInvariant.program)).fst
  match ← (Strata.Core.verifyProgram p { Core.VerifyOptions.quiet with vcgen := .usp }
      (pipeline := some vp)).toBaseIO with
  | .ok results =>
    IO.println (results.toList.any fun r =>
      (r.obligation.label.splitOn "_calls_f_").length > 1 && r.isFailure)
  | .error e => IO.println s!"error: {e}"

/-- info: true -/
#guard_msgs in
#eval precondChecked (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp })

/-! ## A call in an unreachable CFG block

Its temporaries stay declared in its own block: the type checker checks an
unreachable block without the entry's declarations. -/

def deadCall :=
#strata
program Core;
procedure g(a : int, out r : int) spec { ensures [g_post]: (r == a); } { r := a; };
procedure P(out y : int)
spec { ensures [y0]: (y == 0); }
cfg entry {
  entry: { y := 0; return; }
  dead: { call g(1, out y); return; }
};
#end

/--
info:
Obligation: g_post
Property: assert
Result: ✅ pass

Obligation: y0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify deadCall

/-! ## Each obligation marks each label prefix once

Each of the 20 calls to `Q`, which has a body and is not opaque, adds labelled
assumptions; the obligation after the last one carries one `callElimAssume_` mark, not
one per assumption, since call elimination's prefix is a known one. -/

def manyCalls :=
#strata
program Core;
procedure Q(out y : int) spec { ensures [q_post]: (int.ge(y, 0)); } { y := 1; };
procedure P(out y : int)
cfg entry {
  entry: {
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    call Q(out y);
    assert [last]: (int.ge(y, 0));
    return;
  }
};
#end

/-- info: [(last, 1)] -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram manyCalls.program)).fst
  let p := match _root_.Core.Transform.run p _root_.Core.CallElim.callElim' with
    | .ok (_, p') => p'
    | .error _ => p
  -- The known prefixes, as the pipeline passes them (`passiveVCPipelinePhase`).
  match _root_.Core.PassiveVC.passiveVCProgram .sp p [_root_.Core.CallElim.callElimAssumePrefix] with
  | .ok out =>
    let counts := out.decls.flatMap fun d => match d with
      | .proc q _ => if q.header.name.name != "P" then [] else match q.body with
        | .structured ss _ => ss.filterMap fun s => match s with
          | .ite _ arm _ _ =>
            let label := arm.findSome? fun s => match s with
              | .cmd (.cmd (.assert l _ _)) => some l
              | _ => none
            some (label.getD "", (arm.filter fun s => match s with
              | .cmd (.cmd (.assume l _ _)) => l.startsWith _root_.Core.CallElim.callElimAssumePrefix
              | _ => false).length)
          | _ => none
        | .cfg _ _ | .abstract => []
      | _ => []
    IO.println counts
  | .error e => IO.println s!"error: {e}"

/-! ## Every phase is nameable under every mode -/

/-- info: [] -/
#guard_msgs in
#eval
  let names := fun (o : Core.VerifyOptions) => (Strata.Core.nameablePhases o).map (·.phase.name)
  let modes : List Core.VerifyOptions :=
    [Core.VerifyOptions.quiet, { Core.VerifyOptions.quiet with vcgen := .wp },
     { Core.VerifyOptions.quiet with vcgen := .uwp },
     { Core.VerifyOptions.quiet with vcgen := .usp },
     { Core.VerifyOptions.quiet with symExec := some .default }]
  let all := (modes.flatMap names).eraseDups
  modes.filterMap fun o =>
    let ns := names o
    let missing := all.filter (!ns.contains ·)
    let twice := ns.filter fun n => ns.count n > 1
    if missing.isEmpty && twice.isEmpty then none else some (missing, twice)

/-! ## Monomorphization rewrites block metadata

An invariant calling a polymorphic function is specialized like any other
expression, so a pipeline that monomorphizes before cutting loops copies the
specialized call into the cut's commands. -/

def polyInvariant :=
#strata
program Core;
function id<a>(x : a) : a { x }
procedure P(n : int, out y : int)
cfg entry {
  entry: { y := 0; goto loop; }
  @[loopInvariant = (int.ge(id(y), 0))]
  loop: { branch (int.lt(y, n)) goto body else goto done; }
  body: { y := int.add(y, 1); goto loop; }
  done: { return; }
};
#end

/-- info: @[loopInvariant = ((int.ge(|$__mono#id#int|(y), 0)))] loop: { -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram polyInvariant.program)).fst
  let p ← IO.ofExcept ((Core.typeCheck Core.VerifyOptions.quiet p).mapError (·.message))
  match _root_.Core.Transform.run p _root_.Core.monomorphizeFunctions with
  | .ok (_, p') =>
    let text := (Core.formatProgram p' (annFilter := .all)).pretty
    for line in text.splitOn "\n" do
      if line.trimAscii.toString.startsWith "@[loopInvariant" then IO.println line.trimAscii
  | .error e => IO.println s!"error: {e}"

/-! ## Local functions

A local function's value is substituted into its uses: an SMT solver cannot
compare lambdas. It captures the value `b` has where it is declared, and
sibling scopes may declare functions of one name at different types. -/

def localFunctions :=
#strata
program Core;
procedure P(a : int, c : bool) {
  var b : int := 1;
  function addb(v : int) : int { int.add(v, b) }
  b := 5;
  assert [cap]: (addb(0) == 1);
  assert [plain]: (a == a);
  if (c) {
    function sq(v : int) : int { int.mul(v, v) }
    assert [s1]: (int.ge(sq(a), 0));
  } else {
    function sq(v : bool) : bool { v }
    assert [s2]: (sq(true));
  }
};
#end

/-- info: [(cap, true), (plain, true), (s1, true), (s2, true)] -/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify localFunctions
      (options := { Core.VerifyOptions.quiet with vcgen := m })
    if m == .usp then IO.println (r.toList.map fun r => (r.obligation.label, r.isSuccess))
    else if !(r.toList.all (·.isSuccess)) then IO.println "uwp differs"

/-! ## Block labels are renamed apart

Sibling blocks may share a label, and a label may end in `_<digits>`; each
`exit` leaves the nearest block of its label. -/

def blockLabels :=
#strata
program Core;
procedure P(x : int, out y : int)
spec { ensures [y_pos]: (int.gt(y, 0)); }
{
  y := 1;
  l: { if (int.gt(x, 0)) { exit l; } y := 2; }
  l: { step_1: { exit l; } y := 0; }
};
#end

/--
info:
Obligation: y_pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify blockLabels

/-! ## Other block metadata is inert

Only a `loopInvariant` gets precondition checks: a `note` that divides by zero
gives no obligation. -/

def inertNote :=
#strata
program Core;
procedure P(n : int)
cfg entry {
  @[note = (int.safeDiv(n, 0) == 1)]
  entry: { return; }
};
#end

/-- info: 0 -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify inertNote (options := { Core.VerifyOptions.quiet with vcgen := .usp })
  IO.println r.size

/-! ## Label keys

A label with a known prefix is keyed by the prefix; any other label is kept whole,
so a phase that is not among the known ones (an external phase, say, whose prefix
has an `_` inside it) still finds its labels by its own prefix, except the labels
of the source's own assumptions, which get none. -/

/-- info: [$__loopElimAssume_, callElimAssume_, $__extAssume_k_3, x, ] -/
#guard_msgs in
#eval IO.println (["$__loopElimAssume_guard_1", "callElimAssume_f_2", "$__extAssume_k_3", "x", ""].map
  (_root_.Core.PassiveVC.labelKey ["$__loopElimAssume_", "callElimAssume_"]))

-- The source's own assumptions get no mark: the translator's `assume_<N>` and the
-- procedure's `requires` labels (here `pre`), which no phase validates by.
/-- info: [callElimAssume_, , , assume_x, x] -/
#guard_msgs in
#eval IO.println (["callElimAssume_f_2", "assume_7", "pre", "assume_x", "x"].map
  (_root_.Core.PassiveVC.labelKey ["callElimAssume_"]
    (fun l => _root_.Core.PassiveVC.isAutoAssumeLabel l || l == "pre")))

/-! ## A lambda-valued variable at a join

A function-typed variable that is written a lambda is inlined, so its value on
each path is that lambda. At a join of different lambdas the variable is
unconstrained: it does not take the value it had on entry, nor the assumptions
made about it after an earlier join. In `joinReset`, `f(0) == 1` when `c` is
false and `d` is true, so `bad` does not hold; the result rests on the reset, so
it is `unknown`, never `pass`. `joinResetCfg` has the same shape with a nested
join. -/

def joinReset :=
#strata
program Core;
procedure P(c : bool, d : bool) {
  var f : int -> int := fun y : int => y;
  if (c) { f := fun y : int => 7; }
  assume (f(0) == 0);
  if (d) { f := fun y : int => 1; }
  assert [bad]: (f(0) == 0);
};
#end

def joinResetCfg :=
#strata
program Core;
procedure P(c : bool, d : bool)
cfg entry {
  entry: { var f : int -> int := fun y : int => 0; branch (c) goto a else goto b; }
  a: { branch (d) goto a1 else goto a2; }
  a1: { f := fun y : int => 1; goto a3; }
  a2: { goto a3; }
  a3: { assume (true); goto j; }
  b: { goto j; }
  j: { assert [bad]: (f(0) == 0); return; }
};
#end

/-- info: [(bad, other)] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify joinReset (options := { Core.VerifyOptions.quiet with vcgen := .usp })
  IO.println (r.toList.map fun r => (r.obligation.label, if r.isSuccess then "pass" else "other"))

/-- info: [(bad, other)] -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify joinResetCfg (options := { Core.VerifyOptions.quiet with vcgen := .uwp })
  IO.println (r.toList.map fun r => (r.obligation.label, if r.isSuccess then "pass" else "other"))

/-! ## Lambdas at a join: equal ones are kept, different ones are validated

If every path writes the same lambda, the variable keeps its value across the
join, so a cover that needs another value is unreachable, as under `--vcgen symbolic`. If the
paths write different lambdas, the variable is unconstrained after the join. A
result that rests on that (a cover met, an assertion failed) is `unknown`, since
the program may not allow it. -/

def sameLambdas :=
#strata
program Core;
procedure P(c : bool) {
  var f : int -> int := fun y : int => 0;
  if (c) { f := fun y : int => 0; }
  cover [cvBad]: (f(0) == 5);
  assert [aOk]: (f(0) == 0);
};
#end

def differentLambdas :=
#strata
program Core;
procedure P(c : bool) {
  var f : int -> int := fun y : int => 0;
  if (c) { f := fun y : int => 1; }
  cover [cvDiv]: (f(0) == 5);
  assert [aDiv]: (f(0) == 0);
};
#end

/-- The verdict of each result: pass, fail (a cover that is not met also fails), or unknown. -/
private def verdicts (p : StrataDDM.SourcedProgram) (m : Core.VCGenMode) : IO Unit := do
  let r ← Strata.Core.verify p (options := { Core.VerifyOptions.quiet with vcgen := m })
  IO.println (r.toList.map fun r =>
    (r.obligation.label, if r.isFailure then "fail" else if r.isSuccess then "pass" else "other"))

/-- info: [(cvBad, fail), (aOk, pass)] -/
#guard_msgs in
#eval verdicts sameLambdas .usp

/-- info: [(cvBad, fail), (aOk, pass)] -/
#guard_msgs in
#eval verdicts sameLambdas .uwp

/-- info: [(cvDiv, other), (aDiv, other)] -/
#guard_msgs in
#eval verdicts differentLambdas .usp

/-- info: [(cvDiv, other), (aDiv, other)] -/
#guard_msgs in
#eval verdicts differentLambdas .uwp

/-! ## An order without CFG loop elimination is refused

Passive VC generation needs every CFG body acyclic (`noCFGCycles`), which only
`cfgLoopElim` establishes: an order without it is refused when the pipeline is
assembled, not when a looping body reaches `passiveVC`. -/

/-- info: "refused" -/
#guard_msgs in
#eval
  let phases := (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }).filter
    (·.phase.name != "cfgLoopElim")
  match Strata.Core.validatePipeline phases with
  | .ok _ => "accepted"
  | .error _ => "refused"

/-! ## A program with a structured loop and a CFG loop

Both are verified in one run: the structured loop by loop elimination, the CFG
loop by CFG loop elimination, under `usp`, which handles both. -/

def mixedLoops :=
#strata
program Core;
procedure S(n : int)
{
  var i : int;
  i := 0;
  while (int.lt(i, n)) invariant (int.ge(i, 0)) {
    i := int.add(i, 1);
  }
  assert [s_ok]: (int.ge(i, 0));
};
procedure Q(a : int, out r : int)
spec { ensures [q_ok]: (int.ge(r, 0)); }
cfg entry {
  entry: { r := 0; goto loop; }
  @[loopInvariant = (int.ge(r, 0))]
  loop: { r := int.add(r, 1); branch (int.lt(r, a)) goto loop else goto done; }
  done: { return; }
};
#end

/--
info: Obligation: insertLoopInvAssert_entry_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: insertLoopInvAssert_arbitrary_iter_maintain_invariant_loop_0_0
Property: assert
Result: ✅ pass

Obligation: s_ok
Property: assert
Result: ✅ pass

Obligation: q_ok
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_entry_loop_0
Property: assert
Result: ✅ pass

Obligation: cfgLoopElimAssert_maintain_loop_loop_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify mixedLoops

/-! ## The default generators refuse a CFG body

`--vcgen symbolic` and `--vcgen wp` do not fall back to another generator on a CFG
body: they report it, with the advice to pass `--vcgen symexec` or `--vcgen usp`. -/

/--
info: error: ❌ Expected every procedure body to be structured, but found procedure P with a CFG body. To verify it, pass --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp).
-/
#guard_msgs in
#eval verify gotoPgm (mode := .symbolic)

/--
info: error: ❌ Expected every procedure body to be structured, but found procedure P with a CFG body. To verify it, pass --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp).
-/
#guard_msgs in
#eval verify gotoPgm (mode := .wp)

/-! ## `cfgLoopElim` establishes `noCFGCycles`, and the phases after it keep it

On programs with looping CFG bodies of several shapes, the fact is false before
`cfgLoopElim`, true after it, and still true after every later phase up to
`passiveVC`, which requires it (each claims to preserve it). A phase that fails is
reported, rather than skipped. -/

private def loopCallProgram : Core.Program :=
  (TransM.run Inhabited.default (translateProgram loopCall.program)).fst

/-- Nested loops, an entry that is a loop header, a header with two back edges,
    labels whose back-edge keys collide (`a` with `b_c`, and `a_b` with `c`), and a
    cycle that the entry does not reach. -/
def cycleShapes :=
#strata
program Core;
procedure Nested(n : int, out s : int)
cfg entry {
  entry: { var i : int := 0; var j : int := 0; s := 0; goto outer; }
  @[loopInvariant = (int.ge(s, 0))]
  outer: { branch (int.lt(i, n)) goto obody else goto done; }
  obody: { j := 0; goto inner; }
  @[loopInvariant = (int.ge(s, 0))]
  inner: { branch (int.lt(j, i)) goto ibody else goto onext; }
  ibody: { s := int.add(s, 1); j := int.add(j, 1); goto inner; }
  onext: { i := int.add(i, 1); goto outer; }
  done: { return; }
};
procedure EntryHeader(n : int, out x : int)
cfg loop {
  @[loopInvariant = (int.le(0, 1))]
  loop: { branch (int.lt(x, n)) goto body else goto done; }
  body: { x := int.add(x, 1); goto loop; }
  done: { return; }
};
procedure TwoBack(n : int, c : bool, out x : int)
cfg entry {
  entry: { x := 0; goto loop; }
  @[loopInvariant = (int.ge(x, 0))]
  loop: { branch (int.lt(x, n)) goto body else goto done; }
  body: { x := int.add(x, 1); branch (c) goto mid else goto loop; }
  mid: { goto loop; }
  done: { return; }
};
procedure Colliding(p : bool, q : bool)
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
procedure Unreached(out x : int)
cfg entry {
  entry: { x := 0; return; }
  a: { goto b; }
  b: { goto a; }
};
#end

/-- For each phase from `cfgLoopElim` to `passiveVC`, whether `noCFGCycles` holds after
    it, or the phase's error; the fact's value before is first. -/
private def cycleTrace (p : Core.Program) : String := Id.run do
  let phases := Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }
  let names := phases.map (·.phase.name)
  let i := names.idxOf "cfgLoopElim"
  let k := names.idxOf "passiveVC"
  let mut prog := p
  -- The phases before the cut, run for their effect only.
  for ph in phases.take i do
    match Core.Transform.run prog ph.transform with
    | .ok (_, q) => prog := q
    | .error e => return s!"{ph.phase.name} failed: {e}"
  let mut out := s!"before: {prog.noCFGCycles}"
  for ph in (phases.drop i).take (k - i) do
    match Core.Transform.run prog ph.transform with
    | .ok (_, q) =>
      prog := q
      out := out ++ s!", {ph.phase.name}: {q.noCFGCycles}"
    | .error e => return out ++ s!", {ph.phase.name} failed: {e}"
  return out

/--
info: before: false, cfgLoopElim: true, callElim: true, termCheck: true, precondElim: true, seqTotalize: true, insertLoopInvariantAsserts: true, loopElim: true, genOpaqueTypeParams: true, monomorphizeFunctions: true, simplify: true, declObligations: true
-/
#guard_msgs in
#eval IO.println (cycleTrace loopCallProgram)

/--
info: before: false, cfgLoopElim: true, callElim: true, termCheck: true, precondElim: true, seqTotalize: true, insertLoopInvariantAsserts: true, loopElim: true, genOpaqueTypeParams: true, monomorphizeFunctions: true, simplify: true, declObligations: true
-/
#guard_msgs in
#eval IO.println (cycleTrace (TransM.run Inhabited.default (translateProgram cycleShapes.program)).fst)

/-! `cfgLoopElim` also keeps every expression annotated (`typeAnnotated`), which
`termCheck`, right after it, requires: on the same programs, the fact holds before
the cut (after `typeCheck`) and after it. -/

/-- Whether every expression is annotated before and after `cfgLoopElim`. -/
private def annotatedAcrossCut (p : Core.Program) : String := Id.run do
  let phases := Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }
  let i := (phases.map (·.phase.name)).idxOf "cfgLoopElim"
  let mut prog := p
  let mut out := ""
  for ph in phases.take (i + 1) do
    if ph.phase.name == "cfgLoopElim" then
      out := s!"before: {Core.Program.allExprs Lambda.LExpr.fullyAnnotated prog}"
    match Core.Transform.run prog ph.transform with
    | .ok (_, q) => prog := q
    | .error e => return s!"{ph.phase.name} failed: {e}"
  return out ++ s!", after: {Core.Program.allExprs Lambda.LExpr.fullyAnnotated prog}"

/-- info: before: true, after: true
before: true, after: true -/
#guard_msgs in
#eval do
  IO.println (annotatedAcrossCut loopCallProgram)
  IO.println (annotatedAcrossCut (TransM.run Inhabited.default (translateProgram cycleShapes.program)).fst)

/-- info: true -/
#guard_msgs in
#eval
  let phases := (Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }).filter
    (·.phase.name != "cfgLoopElim")
  match Strata.Core.validatePipeline phases with
  | .ok _ => false
  | .error e => ((toString e).splitOn "requires `noCFGCycles`").length > 1

/-! ## A phase that rewrites only expressions may sit between loop elimination and `passiveVC`

Beta reduction does not change a body's blocks or edges, so it preserves
`noCFGCycles`; right after `cfgLoopElim` and `callElim` the order is accepted. (Right
after `cfgLoopElim` it is not: it does not keep `wellFormedCalls`, which `callElim`
needs. The other expression and axiom phases preserve `noCFGCycles` too, but each
needs facts this position does not yet have, and is refused for those.) -/

/-- info: true -/
#guard_msgs in
#eval
  let phases := Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }
  let i := (phases.map (·.phase.name)).idxOf "callElim"
  match Strata.Core.validatePipeline
      (phases.take (i + 1) ++ [Core.passBetaReduce] ++ phases.drop (i + 1)) with
  | .ok _ => true
  | .error _ => false

/-! ## Copies of function-typed variables

A write to a variable of function type is inlined whatever its right-hand side: a
copy of another function variable, or a conditional of two. A copy's definition is
the other variable's, and no obligation sees an equality between functions. -/

def functionCopies :=
#strata
program Core;
procedure P(c : bool, x : int) {
  var f : int -> int := fun y : int => y;
  var h : int -> int := fun y : int => 0;
  var g : int -> int := f;
  assert [copy_ok]: (g(1) == 1);
  assert [copy_bad]: (g(1) == 2);
  var k : int -> int := if c then f else h;
  assert [plain]: (x == x);
};
#end

/-- info: [(copy_ok, pass), (copy_bad, fail), (plain, pass)] -/
#guard_msgs in
#eval verdicts functionCopies .usp

/-- info: [(copy_ok, pass), (copy_bad, fail), (plain, pass)] -/
#guard_msgs in
#eval verdicts functionCopies .uwp


/-! ## A function-typed variable declared in one branch only

`g` is declared in the `then` branch alone, so nothing after the join reads it and
the join needs no reset. A failing assertion after the join is therefore reported
as a failure, as under `--vcgen symbolic`, not as `unknown` for want of validation of a join
reset. -/

def branchLocalFn :=
#strata
program Core;
procedure R(c : bool) {
  var f : int -> int := fun y : int => int.add(y, 1);
  if (c) { var g : int -> int := fun y : int => y; assert [r0]: (g(1) == 1); }
  assert [r1]: (f(1) == 2);
  assert [r2]: (f(1) == 3);
};
#end

/--
info:
Obligation: r0
Property: assert
Result: ✅ pass

Obligation: r1
Property: assert
Result: ✅ pass

Obligation: r2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify branchLocalFn (mode := .symbolic)

/--
info:
Obligation: r0
Property: assert
Result: ✅ pass

Obligation: r1
Property: assert
Result: ✅ pass

Obligation: r2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify branchLocalFn (mode := .usp)

/--
info:
Obligation: r0
Property: assert
Result: ✅ pass

Obligation: r1
Property: assert
Result: ✅ pass

Obligation: r2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify branchLocalFn (mode := .uwp)

/-! ## Each shared definition comes before the first obligation that reads it

The obligation procedure declares a shared definition (`$__vc…`) in front of the
first arm that reads it, so the paths of an obligation carry the definitions up to
the ones it needs and none after. The statements of the procedure of `P`, in
order: `v` a variable declaration, `d` a shared definition, `a` an arm. The first
arm is preceded by one definition, the second by all eleven. -/

def twoAsserts :=
#strata
program Core;
procedure P(x : int, c : bool) {
  assert [a1]: (int.ge(x, x));
  if (c) { assume (int.gt(x, 0)); }
  assert [a2]: (int.ge(x, 0));
};
#end

/-- The kinds of the statements of the first procedure of the program after
    `passiveVCProgram`. -/
private def defPlacement : String :=
  let p := (TransM.run Inhabited.default (translateProgram twoAsserts.program)).fst
  match Core.PassiveVC.passiveVCProgram .sp p with
  | .error e => s!"error: {e}"
  | .ok q =>
    match q.decls.findSome? fun d => match d with
        | .proc proc _ => some proc
        | _ => none with
    | none => "no procedure"
    | some proc =>
      match proc.body with
      | .structured ss _ =>
        let kinds := ss.map fun s => match s with
          | .cmd (.cmd (.init x _ _ _)) => if x.name.startsWith "$__vc" then "d" else "v"
          | .ite .. => "a"
          | _ => "?"
        String.join kinds
      | .cfg _ _ | .abstract => "cfg"

/-- info: "vvdadddddddddda" -/
#guard_msgs in
#eval defPlacement


/-! ## A function-typed local declared on both sides of a CFG join

`A` and `B` each declare `f`, as different lambdas; neither declaration dominates `J`,
so nothing after the join can read `f`, and the join needs no reset of it. The failing
assertion at `J` is then a failure, as under `--vcgen symbolic`, not `unknown` for want of
validating a reset. -/

def bothSidesDeclare :=
#strata
program Core;
procedure P(c : bool, x : int)
cfg entry {
  entry: { branch (c) goto a else goto b; }
  a: { var f : int -> int := fun y : int => int.add(y, 1); assert [fa]: (f(0) == 1); goto j; }
  b: { var f : int -> int := fun y : int => int.add(y, 2); assert [fb]: (f(0) == 2); goto j; }
  j: { assert [after]: (int.gt(x, x)); return; }
};
#end

/-- info: [(fa, pass), (fb, pass), (after, fail)] -/
#guard_msgs in
#eval verdicts bothSidesDeclare .usp

/-- info: [(fa, pass), (fb, pass), (after, fail)] -/
#guard_msgs in
#eval verdicts bothSidesDeclare .uwp

/-! ## Several returning blocks give one obligation per postcondition

The returning blocks of a CFG body go to one exit block that holds the `ensures`, so
`post` is one obligation, whichever path fails it, as for a structured body. -/

def twoReturns :=
#strata
program Core;
procedure Q(x : int, out y : int)
spec { ensures [post]: (int.gt(y, 0)); }
cfg entry {
  entry: { branch (int.gt(x, 0)) goto a else goto b; }
  a: { y := x; return; }
  b: { y := x; return; }
};
#end

/-- The number of checks of `post` in the obligation program of `twoReturns`. -/
private def postChecks : Nat :=
  let p := (TransM.run Inhabited.default (translateProgram twoReturns.program)).fst
  match _root_.Core.PassiveVC.passiveVCProgram .sp p with
  | .error _ => 0
  | .ok q => q.decls.foldl (fun n d => match d with
    | .proc r _ => match r.body with
      | .structured ss _ => n + (ss.filter fun s => match s with
        | .ite _ arm _ _ => arm.any fun t => match t with
          | .cmd (.cmd (.assert l _ _)) => l == "post"
          | _ => false
        | _ => false).length
      | .cfg _ _ | .abstract => n
    | _ => n) 0

/-- info: 1 -/
#guard_msgs in
#eval postChecks

/-- info: [(post, fail)] -/
#guard_msgs in
#eval verdicts twoReturns .usp

/-! ## Verifying a structured procedure that calls a CFG one

With `--procedures S`, the CFG body of `S`'s callee `Q` is kept (a callee's contract
is needed for call elimination), so `--vcgen symbolic` refuses it, and `usp` verifies
`S`. -/

def callsCfg :=
#strata
program Core;
procedure Q(x : int, out y : int)
spec { ensures [q_post]: (int.ge(y, x)); }
cfg entry {
  entry: { y := x; return; }
};
procedure S(a : int, out b : int)
spec { ensures [s_post]: (int.ge(b, a)); }
{
  call Q(a, out b);
};
#end

/--
info: error: ❌ Expected every procedure body to be structured, but found procedure Q with a CFG body. To verify it, pass --vcgen symexec (for an acyclic one) or --vcgen usp (or uwp).
-/
#guard_msgs in
#eval verify callsCfg (mode := .symbolic) (procs := some ["S"])

/--
info: Obligation: s_post
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify callsCfg (procs := some ["S"])

/-! ## A CFG body that is not dominance-scoped is refused

`t` is declared on one arm and read at the join, which the CFG type checker
rejects. Passification relies on that scoping, so handed such a body directly, the
passive VC phase reports it rather than give a result. -/

def unscopedRead :=
#strata
program Core;
procedure P(c : bool)
cfg entry {
  entry: { branch (c) goto a else goto j; }
  a: { var t : int := 1; goto j; }
  j: { assert [t_pos]: (int.gt(t, 0)); return; }
};
#end

/-- info: procedure 'P': a CFG-local is read where no declaration of it dominates, or declared twice on one path (the CFG type checker rejects such a body) -/
#guard_msgs in
#eval
  let p := (TransM.run Inhabited.default (translateProgram unscopedRead.program)).fst
  match _root_.Core.PassiveVC.passiveVCProgram .sp p with
  | .error e => IO.println e
  | .ok _ => IO.println "accepted"

/-! ## Each phase's declared validation prefix is the one it validates by

The passive VC phase keeps on an obligation's paths the labels of the phases before
it, by the prefixes they declare (`AbstractedPhase.validationPrefixes`). For every
nameable phase, an obligation carrying an assumption with each prefix it declares is
one it validates, and the phases that declare prefixes are the ones listed. -/

/-- info: [(callElim, true), (insertLoopInvariantAsserts, true), (loopElim, true), (cfgLoopElim, true), (passiveVC, true)] -/
#guard_msgs in
#eval
  let obligationWith (l : String) : Imperative.ProofObligation _root_.Core.Expression :=
    { label := "t", property := .assert,
      assumptions := [[.assumption l (Lambda.LExpr.boolConst default true)]],
      obligation := Lambda.LExpr.boolConst default true, metadata := {} }
  let validates (ph : _root_.Core.PipelinePhase) (l : String) : Bool :=
    match ph.phase.getValidation (obligationWith l) with
    | .modelToValidate _ | .markersOnPath _ => true
    | .modelPreserving => false
  IO.println ((Strata.Core.nameablePhases).filterMap fun ph =>
    if ph.phase.validationPrefixes.isEmpty then none
    else some (ph.phase.name,
      ph.phase.validationPrefixes.all fun pfx => validates ph s!"{pfx}0"))

/-! ## Introduced names avoid the program's names

The obligations declare each incarnation and each definition as a variable, which an
SMT encoding gives the same symbol as a function of that name. A program declaring a
function named like an incarnation (`c@1`) or a definition (`$__vcA_0`) must not
constrain them: the generator lengthens its separator and prefix until no name of the
program contains them (`PassiveVCGen.Naming.avoiding`). -/

def incarnationName :=
#strata
program Core;
function |c@1|() : int;
axiom [ax]: |c@1|() == 5;
procedure P(c : int)
cfg entry {
  entry: { assert [a]: (c == 5); return; }
};
#end

/--
info: Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify incarnationName

/--
info: Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify incarnationName (mode := .uwp)

def definitionName :=
#strata
program Core;
function |$__vcA_0|() : bool;
axiom [ax]: !(|$__vcA_0|());
procedure P(x : int) {
  assert [a]: (x == 5);
};
#end

/--
info: Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify definitionName (mode := .symbolic)

/--
info: Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify definitionName

/--
info: Obligation: a
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify definitionName (mode := .uwp)

/--
info: { sep := "@@@", defPrefix := "$$$__vc" }
-/
#guard_msgs in
#eval IO.println (repr (Imperative.PassiveVCGen.Naming.avoiding ["c@1", "$__vcA_0", "a@@b", "$$__vc"]))

/-! ## A failing goal that rests on a loop cut is validated by replay

A model of a goal whose paths cross a loop cut is replayed through the procedure as it
was before the cut (`CFGLoopElim.replayValidates`), from the model's parameter values.
A run that fails the goal makes the result `fail`; otherwise it stays `unknown`.

* `Untouched`: the loop never writes `s`, so `s_pos` fails on every run.
* `Iterates`: `r == 0` fails on every run, after `n > 0` iterations.
* `Holds`: without an invariant, the cut loses that the loop ends with `r == n`, so
  the model is spurious: the run from it ends with `r == n`, and `eq` stays `unknown`. -/

def replayed :=
#strata
program Core;
procedure Untouched(n : int, out r : int, out s : int)
spec { ensures [s_pos]: int.gt(s, 0); }
cfg entry {
  entry: { s := 0; r := 0; goto loop; }
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
procedure Iterates(n : int, out r : int)
spec { requires [pos]: int.gt(n, 0); ensures [zero]: (r == 0); }
cfg entry {
  entry: { r := 0; goto loop; }
  @[loopInvariant = (int.ge(r, 0))]
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
procedure Holds(n : int, out r : int)
spec { requires [nneg]: int.ge(n, 0); ensures [eq]: (r == n); }
cfg entry {
  entry: { r := 0; goto loop; }
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
#end

/--
info: [(s_pos, fail), (zero, fail), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass), (eq, other)]
[(s_pos, fail), (zero, fail), (cfgLoopElimAssert_entry_loop_0, pass), (cfgLoopElimAssert_maintain_loop_body_0, pass), (eq, other)]
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify replayed (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println (r.toList.map fun r =>
      (r.obligation.label, if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! At `--check-level full` both queries run, and a model of each is replayed for the
value its query gives the check. `s_pos` and `zero` fail on every run: always false and
reachable. For `eq`, a model of the satisfiability query replays to a run where it
holds, and the model of the validity query stays unconfirmed: it can be true, and is
not known to always be. -/

/--
info: s_pos: always false and is reachable from declaration entry
zero: always false and is reachable from declaration entry
cfgLoopElimAssert_entry_loop_0: always true and is reachable from declaration entry
cfgLoopElimAssert_maintain_loop_body_0: always true if reached
eq: can be true and is reachable from declaration entry
-/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify replayed (options := { Core.VerifyOptions.quiet with
    vcgen := .usp, checkLevel := .full })
  for v in r do
    match v.outcome with
    | .ok o => IO.println s!"{v.obligation.label}: {o.label v.obligation.property .full .deductive}"
    | .error e => IO.println s!"{v.obligation.label}: error {e}"

/-! ## A counterexample is given in the program's variables

The passive VC phase records, at each check, the incarnation each variable is at
(`PassiveVCGen.varAtPrefix`), and a counterexample gives each variable the value of
that incarnation: the variables' values at the failing check, not the incarnations.
Here, at `r_small`, after the loop ran `n` times. -/

def namedCex :=
#strata
program Core;
procedure R(n : int, out r : int, out s : int)
spec { requires [three]: (n == 3); ensures [r_small]: int.lt(r, 2); }
cfg entry {
  entry: { s := 0; r := 0; goto loop; }
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
#end

/--
info: r_small: fail (n, 3) (r, 3) (s, 0) 
r_small: fail (n, 3) (r, 3) (s, 0)
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify namedCex (options := { Core.VerifyOptions.quiet with vcgen := m })
    for v in r do
      IO.println s!"{v.obligation.label}: {if v.isFailure then "fail" else "other"} \
        {Std.format v.lexprModel}"

-- A partial counterexample's missing variables are named as its model is: by the program's
-- variable whose incarnation at the check is missing (`x@3` is `x`'s; `z` is no variable's).
/-- info: [x] -/
#guard_msgs in
#eval
  let pfx := Imperative.PassiveVCGen.varAtPrefix
  let md : Imperative.MetaData _root_.Core.Expression :=
    #[⟨.label s!"{pfx}x", .msg "x@3"⟩, ⟨.label s!"{pfx}y", .msg "y@1"⟩]
  IO.println (_root_.Core.LExprModel.missingAtCheck md ["x@3", "z"])

/-! ## Replay runs a callee's body, not its contract

`f`'s contract (`y >= 0`) is weaker than its body (`y := 1`), and `g` has no contract
at all. A cut loop that calls one of them is replayed through the program before call
elimination, so the run executes the callee: `s` is `1` after the loop whether or not
it ran, so `p_post` (`s == 1`) cannot fail and stays `unknown`; the contract's
`s == 0` is not a run of the program. `bad` (`s == 2`) fails on every run. -/

def callInLoop :=
#strata
program Core;
procedure f(out y : int) spec { ensures [f_post]: (int.ge(y, 0)); } { y := 1; };
procedure g(out y : int) { y := 1; };
procedure P(n : int, out s : int)
spec { requires (int.ge(n, 1)); ensures [p_post]: (s == 1); ensures [bad]: (s == 2); }
cfg entry {
  entry: { var i : int := 0; s := 1; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call f(out s); i := int.add(i, 1); goto loop; }
  done: { return; }
};
procedure Q(n : int, out s : int)
spec { requires (int.ge(n, 1)); ensures [q_post]: (s == 1); ensures [q_bad]: (s == 2); }
cfg entry {
  entry: { var i : int := 0; s := 1; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call g(out s); i := int.add(i, 1); goto loop; }
  done: { return; }
};
#end

/--
info: [(p_post, other), (bad, fail), (q_post, other), (q_bad, fail)]
[(p_post, other), (bad, fail), (q_post, other), (q_bad, fail)]
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify callInLoop (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println ((r.toList.filter fun r => r.obligation.label ∈ ["p_post", "bad", "q_post", "q_bad"]).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A `loopInvariant` on a block that is not a loop header is rejected in every mode

`mid` is on no cycle, so its invariant (a false one) means nothing. The CFG type
checker, which every mode's order runs first, reports it, so the default (symbolic
execution, for this CFG body) and `usp` agree. -/

def notHeader :=
#strata
program Core;
procedure S(out x : int) { x := 1; };
procedure C(out y : int)
cfg entry {
  entry: { y := 1; goto mid; }
  @[loopInvariant = (int.lt(y, 0))]
  mid: { return; }
};
#end

/--
info: error: ❌ Type checking error.
Procedure 'C': [C]: block "mid" has a `loopInvariant` but is not a loop header (the target of an edge from a block it dominates).
error: ❌ Type checking error.
Procedure 'C': [C]: block "mid" has a `loopInvariant` but is not a loop header (the target of an edge from a block it dominates).
-/
#guard_msgs in
#eval do
  verify notHeader (mode := .symbolic)
  verify notHeader

/-! ## Replay confirms a model only through the check's own procedure

`Q` and `P` both have a postcondition labelled `post`. With the postconditions'
source ranges cleared, as a front end that builds a program without locations has
them, label and range no longer tell the two apart. The check records the procedure
it comes from (`PassiveVC.sourceProcKey`), so only `P` is replayed: `P`'s loop has no
invariant, so its `post` stays `unknown`, rather than being confirmed by `Q`'s
failing run. `Q`'s `post` fails. -/

def samePostLabel :=
#strata
program Core;
procedure Q(n : int, out r : int)
spec { ensures [post]: (r == 1); }
cfg entry { entry: { r := 0; return; } };
procedure P(n : int, out r : int)
spec { requires (int.ge(n, 0)); ensures [post]: (r == n); }
cfg entry {
  entry: { r := 0; goto loop; }
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
#end

/-- The procedure a result's check comes from, as the passive VC phase records it. -/
private def sourceOf (r : Core.VCResult) : String :=
  (_root_.Core.PassiveVC.sourceProcOf r.obligation.metadata).getD "?"

/--
info: [(Q, fail), (P, other)]
[(Q, fail), (P, other)]
-/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram samePostLabel.program)).fst
  let p : Core.Program := { decls := p.decls.map fun d => match d with
    | .proc q md => .proc { q with spec := { q.spec with
        postconditions := q.spec.postconditions.map fun (l, c) => (l, { c with md := #[] }) } } md
    | d => d }
  for m in [Core.VCGenMode.usp, .uwp] do
    match ← (Strata.Core.verifyProgram p { Core.VerifyOptions.quiet with vcgen := m }).toBaseIO with
    | .ok r => IO.println (r.toList.filter (·.obligation.label == "post") |>.map fun r =>
        (sourceOf r, if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))
    | .error e => IO.println s!"error: {e}"

/-! Without the check's source procedure, a target must be unique across all the
procedures: `Q` and `P` both have an unranged `post`, so a model of an obligation that
does not name its procedure is not confirmed, though `Q`'s run fails its `post`. With
the source named, `Q`'s model is confirmed. -/

/-- info: (false, true) -/
#guard_msgs in
#eval
  let p := (TransM.run Inhabited.default (translateProgram samePostLabel.program)).fst
  let p : Core.Program := { decls := p.decls.map fun d => match d with
    | .proc q md => .proc { q with spec := { q.spec with
        postconditions := q.spec.postconditions.map fun (l, c) => (l, { c with md := #[] }) } } md
    | d => d }
  let ob (md : Imperative.MetaData _root_.Core.Expression) :
      Imperative.ProofObligation _root_.Core.Expression :=
    { label := "post", property := .assert, assumptions := [],
      obligation := Lambda.LExpr.boolConst default true, metadata := md }
  let named : Imperative.MetaData _root_.Core.Expression :=
    Imperative.MetaData.empty.pushElem (.label _root_.Core.PassiveVC.sourceProcKey) (.msg "Q")
  let model : Imperative.SMT.Model _root_.Core.Expression.Ident :=
    [(⟨"n@1", ()⟩, .prim (.int 0))]
  ((_root_.Core.CFGLoopElim.replayValidates (fun _ => false) p (ob #[]) false model).isSome,
   (_root_.Core.CFGLoopElim.replayValidates (fun _ => false) p (ob named) false model).isSome)

/-! ## Replay through a callee: no false reachability

`f`'s body keeps `s == 1`, so `bad` is never reached. A replayed run executes `f`'s
body, so neither query's model is confirmed through `f`'s weaker contract: at
`--check-level full`, `unreach` is not reported reachable, and `reached` (`s == 0`)
is not reported true. -/

def unreachedThroughCall :=
#strata
program Core;
procedure f(out y : int) spec { ensures [f_post]: (int.ge(y, 0)); } { y := 1; };
procedure P(n : int, out s : int)
spec { requires (int.ge(n, 1)); }
cfg entry {
  entry: { var i : int := 0; s := 1; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call f(out s); i := int.add(i, 1); goto loop; }
  done: { branch (s == 0) goto bad else goto ok; }
  bad: { assert [unreach]: (false); assert [reached]: (s == 0); return; }
  ok: { return; }
};
#end

/--
info: unreach: always false if reached
reached: always true if reached
-/
#guard_msgs in
#eval show IO Unit from do
  let r ← Strata.Core.verify unreachedThroughCall (options := { Core.VerifyOptions.quiet with
    vcgen := .usp, checkLevel := .full })
  for v in r do
    if v.obligation.label ∈ ["unreach", "reached"] then
      match v.outcome with
      | .ok o => IO.println s!"{v.obligation.label}: {o.label v.obligation.property .full .deductive}"
      | .error e => IO.println s!"{v.obligation.label}: error {e}"

/-! ## A counterexample confirmed by replay shows the run's values

`tp` fails on every run, after the loop has run `n == 3` times and made `t == 6`. The
cut leaves `t` unconstrained after the loop, so the solver's model may give it any
value; the replay that confirms the failure runs the loop, and the counterexample
shows its values at the check. -/

def runValues :=
#strata
program Core;
procedure R(n : int, out r : int, out t : int)
spec { requires (n == 3); ensures [tp]: (int.lt(t, 0)); }
cfg entry {
  entry: { r := 0; t := 0; goto loop; }
  loop: { branch (int.lt(r, n)) goto body else goto done; }
  body: { r := int.add(r, 1); t := int.add(t, 2); goto loop; }
  done: { return; }
};
#end

/--
info: tp: fail (n, 3) (r, 3) (t, 6) 
tp: fail (n, 3) (r, 3) (t, 6)
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify runValues (options := { Core.VerifyOptions.quiet with vcgen := m })
    for v in r do
      if v.obligation.label == "tp" then
        IO.println s!"tp: {if v.isFailure then "fail" else "other"} {Std.format v.lexprModel}"

/-! Under `--incremental` the same: a goal alone in its session is sent the per-obligation way,
whose reading of the counterexample the replay's refined model is read with again. -/

/--
info: tp: fail (n, 3) (r, 3) (t, 6) 
tp: fail (n, 3) (r, 3) (t, 6)
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify runValues
      (options := { Core.VerifyOptions.quiet with vcgen := m, incremental := true })
    for v in r do
      if v.obligation.label == "tp" then
        IO.println s!"tp: {if v.isFailure then "fail" else "other"} {Std.format v.lexprModel}"

/-! ## Replay with datatype values

Each postcondition fails on every run after its loop. Replay evaluates the datatypes'
functions (the runtime factory, with their constructors and selectors), reads a
model's datatype value back as a constructor annotated with its type, and gives an
output its type's default on entry, so each failure is confirmed: through a selector
(`s_pos3`), with a datatype output (`s_v`), and with a datatype input (`x_int`). -/

def datatypeReplay :=
#strata
program Core;
datatype Val { VInt(n : int), VNone() };
procedure R3(k : int, out r : int, out s : int)
spec { ensures [s_pos3]: (int.gt(s, 0)); }
cfg entry {
  entry: { var v : Val := VInt(0); s := Val..n(v); r := 0; goto loop; }
  loop: { branch (int.lt(r, k)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
procedure R4(k : int, out r : int, out s : Val)
spec { ensures [s_v]: (s == VInt(1)); }
cfg entry {
  entry: { s := VNone(); r := 0; goto loop; }
  loop: { branch (int.lt(r, k)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
procedure R5(x : Val, k : int, out r : int)
spec { ensures [x_int]: (Val..isVInt(x)); }
cfg entry {
  entry: { r := 0; goto loop; }
  loop: { branch (int.lt(r, k)) goto body else goto done; }
  body: { r := int.add(r, 1); goto loop; }
  done: { return; }
};
#end

/--
info: [(s_pos3, fail), (s_v, fail), (x_int, fail)]
[(s_pos3, fail), (s_v, fail), (x_int, fail)]
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify datatypeReplay (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println ((r.toList.filter fun r => r.obligation.label ∈ ["s_pos3", "s_v", "x_int"]).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A call's temporaries do not take a name the procedure declares

Call elimination names a call's temporaries `tmp_arg_N`, `tmp_<out>_N`, … with `N`
past every number the program's names end in, so none is a name the program uses.
`C` declares `tmp_arg_0` itself, and `D` has a parameter of that name, so the
program's variable keeps its value across the call. `c_bad` and `d_bad` do not pass,
under symbolic execution or under `usp`; they are `unknown` rather than `fail`, as is
any result whose path runs through a callee's contract. `E` is correct and is not
refused: `e_ok` holds. -/

def tempClash :=
#strata
program Core;
procedure g(x : int, out y : int) spec { ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure C(n : int, out r : int)
cfg entry {
  entry: { var tmp_arg_0 : int := 5; call g(7, out r); assert [c_bad]: (tmp_arg_0 == 7); return; }
};
procedure D(tmp_arg_0 : int, out r : int)
spec { requires (tmp_arg_0 == 5); }
cfg entry {
  entry: { call g(7, out r); assert [d_bad]: (tmp_arg_0 == 7); return; }
};
procedure E(n : int, out r : int)
cfg entry {
  entry: { var tmp_arg_0 : int := 5; call g(7, out r); assert [e_ok]: (tmp_arg_0 == 5); return; }
};
#end

/--
info: [(c_bad, other), (d_bad, other), (e_ok, pass)]
[(c_bad, other), (d_bad, other), (e_ok, pass)]
-/
#guard_msgs in
#eval show IO Unit from do
  let modes : List Core.VerifyOptions :=
    [{ Core.VerifyOptions.quiet with symExec := some .default },
     { Core.VerifyOptions.quiet with vcgen := .usp }]
  for o in modes do
    let r ← Strata.Core.verify tempClash (options := o)
    IO.println ((r.toList.filter fun r => r.obligation.label ∈ ["c_bad", "d_bad", "e_ok"]).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A structured body's locals named like temporaries keep their values

The structured twins of `C`: `SI` declares `tmp_s_1` and `old_s_2` next to a call with
an `inout` argument, whose temporaries are named `tmp_s_<n>` and `old_s_<n>` (here
they would be `tmp_s_1` and `old_s_2`), and `SC` declares `tmp_arg_0`. None of these is a temporary's name, so `sc_bad` and
`si_bad` do not pass, under symbolic execution or `usp`/`uwp`. -/

def structuredTempClash :=
#strata
program Core;
procedure h(inout s : int) spec { ensures (s == int.add(old s, 1)); } { s := int.add(s, 1); };
procedure SI(n : int, out r : int)
{ var s : int := 0; var tmp_s_1 : int := 5; var old_s_2 : int := 5; call h(inout s);
  assert [si_bad]: (int.add(tmp_s_1, old_s_2) == 0); };
#end

def structuredTempClashArg :=
#strata
program Core;
procedure g(x : int, out y : int) spec { ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure SC(n : int, out r : int)
{ var tmp_arg_0 : int := 5; call g(7, out r); assert [sc_bad]: (tmp_arg_0 == 7); };
#end

/--
info: [(si_bad, other), (sc_bad, other)]
[(si_bad, other), (sc_bad, other)]
[(si_bad, other), (sc_bad, other)]
-/
#guard_msgs in
#eval show IO Unit from do
  let modes : List Core.VerifyOptions :=
    [{ Core.VerifyOptions.quiet with symExec := some .default },
     { Core.VerifyOptions.quiet with vcgen := .usp },
     { Core.VerifyOptions.quiet with vcgen := .uwp }]
  for o in modes do
    let r ← Strata.Core.verify structuredTempClash (options := o)
    let r' ← Strata.Core.verify structuredTempClashArg (options := o)
    IO.println ((r.toList ++ r'.toList |>.filter fun r => r.obligation.label ∈ ["sc_bad", "si_bad"]).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A call's output named like a temporary is the call's output

`F` and `SF` (CFG and structured) pass `tmp_arg_0` as the call's output, and `G` and
`SG` call into it and then assert `false`. The output is `8`, so `f_bad`/`sf_bad`
(`tmp_arg_0 == 100`) and `g_bad`/`sg_bad` do not pass, under symbolic execution or
`usp`/`uwp`: the call's
temporaries are not `tmp_arg_0`, so the output is not overwritten by (or merged with)
a temporary the call assigns. `H` and `SH` pass `tmp_arg_0` (`5`) as the input of
`g2`, which requires it to be `5`: the precondition and `h_ok`/`sh_ok` (`r == 6`)
hold, as the argument's temporary is not the program's variable. -/

def outClash :=
#strata
program Core;
procedure g(x : int, out y : int) spec { ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure g2(x : int, out y : int) spec { requires [g2_pre]: (x == 5); ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure H(n : int, out r : int)
cfg entry {
  entry: { var tmp_arg_0 : int := 5; call g2(tmp_arg_0, out r); assert [h_ok]: (r == 6); return; }
};
procedure SH(n : int, out r : int)
{ var tmp_arg_0 : int := 5; call g2(tmp_arg_0, out r); assert [sh_ok]: (r == 6); };
procedure F(n : int, out r : int)
cfg entry {
  entry: { var tmp_arg_0 : int := 0; call g(7, out tmp_arg_0); assert [f_bad]: (tmp_arg_0 == 100); return; }
};
procedure G(n : int, out r : int)
cfg entry {
  entry: { var tmp_arg_0 : int := 0; call g(7, out tmp_arg_0); assert [g_bad]: false; return; }
};
procedure SF(n : int, out r : int)
{ var tmp_arg_0 : int := 0; call g(7, out tmp_arg_0); assert [sf_bad]: (tmp_arg_0 == 100); };
procedure SG(n : int, out r : int)
{ var tmp_arg_0 : int := 0; call g(7, out tmp_arg_0); assert [sg_bad]: false; };
#end

/--
info: [(callElimAssert_g2_pre_3, pass), (h_ok, pass), (callElimAssert_g2_pre_7, pass), (sh_ok, pass), (f_bad, other), (g_bad, other), (sf_bad, other), (sg_bad, other)]
[(callElimAssert_g2_pre_3, pass), (h_ok, pass), (callElimAssert_g2_pre_7, pass), (sh_ok, pass), (f_bad, other), (g_bad, other), (sf_bad, other), (sg_bad, other)]
[(callElimAssert_g2_pre_3, pass), (h_ok, pass), (callElimAssert_g2_pre_7, pass), (sh_ok, pass), (f_bad, other), (g_bad, other), (sf_bad, other), (sg_bad, other)]
-/
#guard_msgs in
#eval show IO Unit from do
  let modes : List Core.VerifyOptions :=
    [{ Core.VerifyOptions.quiet with symExec := some .default },
     { Core.VerifyOptions.quiet with vcgen := .usp },
     { Core.VerifyOptions.quiet with vcgen := .uwp }]
  for o in modes do
    let r ← Strata.Core.verify outClash (options := o)
    IO.println ((r.toList.filter fun r => r.obligation.label ∈ ["f_bad", "g_bad", "sf_bad", "sg_bad", "h_ok", "sh_ok"]
        || (r.obligation.label.splitOn "g2_pre").length > 1).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## Replay does not run a callee that has no body

`Q` has no body, so a call to it returns any `s` its postcondition (`s > 5`) allows.
Running its empty body would leave `r` at `0`, which no call returns, and `p_post`
would seem to fail on that run; replay does not run such a callee, so `p_post` stays
`unknown`. `P2` calls `Q2`, which has a body (`s := 6`): the run gives `r = 6`,
`p2_post` holds on it, and it stays `unknown` too. In `P3`, `bad` is reached only if
`r == 0` after the loop, which no call to `Q` allows: `unreach` (`false`) is `unknown`,
not a failure on a run through `Q`'s empty body. -/

def contractOnlyCallee :=
#strata
program Core;
procedure Q(out s : int) spec { ensures [q_post]: (int.gt(s, 5)); };
procedure P(n : int, out r : int)
spec { requires (int.ge(n, 1)); ensures [p_post]: (int.gt(r, 5)); }
cfg entry {
  entry: { var i : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call Q(out r); i := int.add(i, 1); goto loop; }
  done: { return; }
};
procedure Q2(out s : int) spec { ensures [q2_post]: (int.gt(s, 5)); } { s := 6; };
procedure P2(n : int, out r : int)
spec { requires (int.ge(n, 1)); ensures [p2_post]: (int.gt(r, 5)); }
cfg entry {
  entry: { var i : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call Q2(out r); i := int.add(i, 1); goto loop; }
  done: { return; }
};
procedure P3(n : int, out r : int)
spec { requires (int.ge(n, 1)); }
cfg entry {
  entry: { var i : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { call Q(out r); i := int.add(i, 1); goto loop; }
  done: { branch (r == 0) goto bad else goto ok; }
  bad: { assert [unreach]: (false); return; }
  ok: { return; }
};
#end

/--
info: [(p_post, other), (p2_post, other), (unreach, other)]
[(p_post, other), (p2_post, other), (unreach, other)]
-/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify contractOnlyCallee (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println ((r.toList.filter fun r => r.obligation.label ∈ ["p_post", "p2_post", "unreach"]).map
      fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A call's temporaries do not take a function's name

The function `tmp_arg_0` is named like a call's temporary, and the temporaries avoid
it too: none of the variables call elimination declares in `K` is named `tmp_arg_0`. -/

def funClash :=
#strata
program Core;
function tmp_arg_0(x : int) : int { 100 }
procedure g(x : int, out y : int) spec { ensures (y == int.add(x, 1)); } { y := int.add(x, 1); };
procedure K(n : int, out r : int)
cfg entry {
  entry: { call g(7, out r); assert [k_ok]: (tmp_arg_0(r) == 100); return; }
};
#end

/-- info: [tmp_arg_1, tmp_r_2] -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram funClash.program)).fst
  let .ok (_, p) := _root_.Core.Transform.run p _root_.Core.CallElim.callElim'
    | IO.println "callElim failed"
  IO.println (p.decls.flatMap fun d => match d with
    | .proc q _ => if q.header.name.name != "K" then [] else match q.body with
      | .cfg g _ => g.blocks.flatMap fun (_, b) => b.cmds.filterMap fun c => match c with
        | .cmd (.init x _ _ _) => some x.name
        | _ => none
      | _ => []
    | _ => [])

/-! ## A numbered name that no temporary can take leaves the labels alone

`P` and `P'` differ only in a parameter's name, `a` and `a_2024`. Only a name shaped
like a temporary (`tmp_…_n`, `old_…_n`) moves the counter call elimination numbers
its temporaries and labels from, so the precondition's label is the same in both. -/

def numberedParam :=
#strata
program Core;
procedure f(x : int, out y : int) spec { requires [f_pre]: (int.ge(x, 0)); } { y := x; };
procedure P(a : int, out r : int) spec { requires (int.ge(a, 0)); } { call f(a, out r); };
#end

def numberedParam' :=
#strata
program Core;
procedure f(x : int, out y : int) spec { requires [f_pre]: (int.ge(x, 0)); } { y := x; };
procedure P(a_2024 : int, out r : int) spec { requires (int.ge(a_2024, 0)); } { call f(a_2024, out r); };
#end

/-- info: true -/
#guard_msgs in
#eval show IO Unit from do
  let labels (p : StrataDDM.Program) : IO (List String) := do
    let r ← Strata.Core.verify p (options := Core.VerifyOptions.quiet)
    pure (r.toList.map (·.obligation.label))
  IO.println ((← labels numberedParam) == (← labels numberedParam'))

/-! ## Replay is not used after call elimination

Call elimination leaves a call to a callee without postconditions as a bare `havoc`,
with no labelled assumption that replay could stop at. In an order that cuts the CFG
loops after it (`cfgLoopElim` moved after `callElim`), replay would run that `havoc`
at its default value: `Q` returns `1`, so `p_post` holds on every run, but the run
with `y = 0` would fail it. Replay is not used there, so `p_post` is `unknown`, as in
the default order. (A call inside the loop would be refused in that order: call
elimination declares its temporaries at the call, which the cut rejects in a loop.) -/

def replayNoLoopQ :=
#strata
program Core;
procedure Q(out r : int) { r := 1; };
procedure P(out y : int)
spec { ensures [p_post]: (y == 1); }
cfg entry {
  entry: { var k : int := 0; y := 7; call Q(out y); goto loop; }
  @[loopInvariant = (true)]
  loop: { branch (int.lt(k, 1)) goto body else goto done; }
  body: { k := int.add(k, 1); goto loop; }
  done: { return; }
};
#end

/-- info: [(p_post, other)]
[(p_post, other)] -/
#guard_msgs in
#eval show IO Unit from do
  let phases := Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .usp }
  let isCut := fun (pp : Core.PipelinePhase) => pp.phase.name == "cfgLoopElim"
  let rest := phases.filter (! isCut ·)
  let reordered := match phases.find? isCut, rest.findIdx? (·.phase.name == "callElim") with
    | some cut, some i => rest.take (i + 1) ++ [cut] ++ rest.drop (i + 1)
    | _, _ => phases
  let p := (TransM.run Inhabited.default (translateProgram replayNoLoopQ.program)).fst
  for ps in [phases, reordered] do
    let vp ← match Strata.Core.validatePipeline ps with
      | .ok vp => pure vp
      | .error e => throw (IO.userError e)
    match ← (Strata.Core.verifyProgram p Core.VerifyOptions.quiet (pipeline := some vp)).toBaseIO with
    | .ok results => IO.println ((results.toList.filter (·.obligation.label == "p_post")).map
        fun r => (r.obligation.label,
          if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))
    | .error e => IO.println s!"error: {e}"

/-! ## Declarations added at the entry print as a program that parses back

`h` lists its entry after a block that calls `f` (whose precondition reads the
argument's temporary), and `n` lists its entry after a loop
whose `goto` is nondeterministic. In `m`, the loop header is listed before the
block declaring `x`, which the loop writes: the cut's pre-header, which havocs `x`, is
listed after the input's blocks. The temporaries of call elimination and the choice
that `cfgLoopElim` declares at the entry are declared before the blocks that use them
in the printed program, which parses back. -/

def entryNotFirst :=
#strata
program Core;
procedure f(x : int, out y : int) spec { requires (int.ge(x, 0)); } { y := x; };
procedure h(a : int, out r : int)
cfg entry {
  once: { call f(a, out r); goto done; }
  entry: { goto once; }
  done: { return; }
};
procedure n(out r : int)
cfg entry {
  body: { r := 1; goto body, done; }
  entry: { r := 0; goto body; }
  done: { return; }
};
procedure m(k : int, out r : int)
cfg entry {
  @[loopInvariant = (true)]
  loop: { branch (int.lt(r, k)) goto body else goto done; }
  entry: { var x : int := 0; r := 0; goto loop; }
  body: { x := int.add(x, 1); r := int.add(r, 1); goto loop; }
  done: { return; }
};
#end

/-- info: callElim: parses back
cfgLoopElim: parses back -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram entryNotFirst.program)).fst
  let passes : List (String × _root_.Core.Transform.CoreTransformM (Bool × _root_.Core.Program)) :=
    [("callElim", _root_.Core.CallElim.callElim' p),
     ("cfgLoopElim", do
        let (_, p) ← _root_.Core.CFGLoopElim.hoistNondetChoicesInLoops p
        _root_.Core.CFGLoopElim.cfgLoopElim p)]
  for (name, pass) in passes do
    match _root_.Core.Transform.run p (fun _ => pass) with
    | .ok (_, p') =>
      let text := (Core.formatProgram p').pretty
      try
        let _ ← Strata.Core.TestUtils.parseCoreText name text.toUTF8
        IO.println s!"{name}: parses back"
      catch e => IO.println s!"{name}: {e}"
    | .error e => IO.println s!"{name}: error {e}"

/-! ## Introduced names avoid the extra factory functions

`|y@1|` and `|y@2|` are given to the verifier as extra functions (`moreFns`), outside
the program, with axioms making both `5`. They are named like `y`'s incarnations, which
the SMT encoding would name the same, so if the passive VC phase introduced them,
`bad` (`y == 4` after `y := 3`) would pass. The phase avoids their names too, so `bad`
fails under `usp` and `uwp`. -/

def moreFnsClash :=
#strata
program Core;
function |y@1|() : int;
function |y@2|() : int;
axiom [ax1]: (|y@1|() == 5);
axiom [ax2]: (|y@2|() == 5);
procedure P(out y : int) { y := 3; assert [bad]: (y == 4); };
#end

/-- info: [(bad, fail)]
[(bad, fail)] -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram moreFnsClash.program)).fst
  let fns := p.decls.filterMap fun d => match d with
    | .func f _ => some f.toLFunc
    | _ => none
  let p : _root_.Core.Program := { decls := p.decls.filter fun d => match d with
    | .func .. => false
    | _ => true }
  let moreFns : Lambda.Factory _root_.Core.CoreLParams := fns.foldl (·.pushIfNew ·) Lambda.Factory.default
  for m in [Core.VCGenMode.usp, .uwp] do
    match ← (Strata.Core.verifyProgram p { Core.VerifyOptions.quiet with vcgen := m }
        (moreFns := moreFns)).toBaseIO with
    | .ok results => IO.println ((results.toList.filter (·.obligation.label == "bad")).map
        fun r => (r.obligation.label,
          if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))
    | .error e => IO.println s!"error: {e}"

/-! ## Replay stops at a check that fails before the target

`P` calls itself with `0`, outside its precondition `n == 1`. In that call the loop
does not run, so `a` (`k >= 1`) fails there; in `P`'s own run, with `n == 1`, it holds.
A run that passes a failed precondition of a callee is not one `a`'s verdict is about,
so replay stops at it, and `a` (resting on the cut, which has no invariant) is
`unknown`, not a failure. With an invariant that keeps `k == j`, `a` passes. -/

def nestedActivation :=
#strata
program Core;
procedure P(n : int, out r : int) spec { requires (n == 1); }
cfg entry {
  entry: { var j : int := 0; var k : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(j, n)) goto body else goto done; }
  body: { j := int.add(j, 1); k := int.add(k, 1); goto loop; }
  done: { branch (n == 1) goto recb else goto chk; }
  recb: { call P(0, out r); goto chk; }
  chk: { assert [a]: (int.ge(k, 1)); return; }
};
#end

/-- info: [(a, other)]
[(a, other)] -/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify nestedActivation (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println ((r.toList.filter (·.obligation.label == "a")).map fun r => (r.obligation.label,
      if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## CFG loop elimination's marker prefix is reserved

A written assumption labelled with `cfgLoopElim`'s marker prefix would turn a real
failure after it into `unknown`, so the phase rejects the program. -/

def forgedCutMarker :=
#strata
program Core;
procedure P(out r : int)
cfg entry {
  entry: { r := 0; assume [$__cfgLoopElimAssume_x]: (true); assert [bad]: (r == 1); return; }
};
#end

/-- info: rejected: true -/
#guard_msgs in
#eval show IO Unit from do
  try
    let _ ← Strata.Core.verify forgedCutMarker (options := { Core.VerifyOptions.quiet with vcgen := .usp })
    IO.println "rejected: false"
  catch e =>
    let reserved := decide (((toString e).splitOn "reserves for its markers").length > 1)
    IO.println s!"rejected: {reserved}"

/-! ## A passive VC phase built by hand still avoids the `moreFns` names

The passive VC phase reads the names it must avoid from the transform state's factory,
which `verifyPipeline` seeds with `moreFns`, so a pipeline whose passive VC phase is
built by hand, without them, still gives `moreFnsClash`'s `bad` a failure. -/

/-- info: [(bad, fail)]
[(bad, fail)] -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram moreFnsClash.program)).fst
  let fns := p.decls.filterMap fun d => match d with
    | .func f _ => some f.toLFunc
    | _ => none
  let p : _root_.Core.Program := { decls := p.decls.filter fun d => match d with
    | .func .. => false
    | _ => true }
  let moreFns : Lambda.Factory _root_.Core.CoreLParams := fns.foldl (·.pushIfNew ·) Lambda.Factory.default
  for m in [Core.VCGenMode.usp, .uwp] do
    let options := { Core.VerifyOptions.quiet with vcgen := m }
    -- `passiveVCGenPhases` with its passive VC phase rebuilt by hand, which takes no
    -- `moreFns`.
    let phases := Core.passiveVCGenPhases options moreFns
    let phases := phases.zipIdx.map fun (ph, i) =>
      if ph.phase.name == "passiveVC" then
        Core.passiveVCPipelinePhase options.vcgen
          ((phases.take i).flatMap (·.phase.validationPrefixes))
      else ph
    let .ok vp := Core.ValidatedPipeline.ofListDelivering "the verification back end"
        Core.backEndRequiredFacts phases
      | IO.println "error: pipeline"
    let r ← IO.FS.withTempDir fun dir =>
      (Core.verifyPipeline p dir options (moreFns := moreFns) (pipeline := some vp)).toBaseIO
    match r with
    | .ok results => IO.println ((results.toList.filter (·.obligation.label == "bad")).map
        fun r => (r.obligation.label,
          if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))
    | .error e => IO.println s!"error: {e}"

/-! ## Replay checks every precondition of a callee at its entry

As in `nestedActivation`, `P` calls itself with `0` outside its precondition, and `a`
fails only in that call. Here the interpreter emits no assertion of the precondition:
it is free in `freeRequiresActivation`, and in `undecidedRequiresActivation` it does
not evaluate for `n == 0` (a quantifier the bounded evaluator does not decide). Replay
assumes every precondition, free ones included, at a callee's entry, and an assumption
that is false or does not evaluate stops the run, so `a` is `unknown` in both. -/

def freeRequiresActivation :=
#strata
program Core;
procedure P(n : int, out r : int) spec { free requires (n == 1); }
cfg entry {
  entry: { var j : int := 0; var k : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(j, n)) goto body else goto done; }
  body: { j := int.add(j, 1); k := int.add(k, 1); goto loop; }
  done: { branch (n == 1) goto recb else goto chk; }
  recb: { call P(0, out r); goto chk; }
  chk: { assert [a]: (int.ge(k, 1)); return; }
};
#end

def undecidedRequiresActivation :=
#strata
program Core;
procedure P(n : int, out r : int)
spec { requires (if (n == 1) then true else (forall x : int :: !(x == x))); }
cfg entry {
  entry: { var j : int := 0; var k : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(j, n)) goto body else goto done; }
  body: { j := int.add(j, 1); k := int.add(k, 1); goto loop; }
  done: { branch (n == 1) goto recb else goto chk; }
  recb: { call P(0, out r); goto chk; }
  chk: { assert [a]: (int.ge(k, 1)); return; }
};
#end

/-- info: [(a, other)]
[(a, other)]
[(a, other)]
[(a, other)] -/
#guard_msgs in
#eval show IO Unit from do
  for prog in [freeRequiresActivation, undecidedRequiresActivation] do
    for m in [Core.VCGenMode.usp, .uwp] do
      let r ← Strata.Core.verify prog (options := { Core.VerifyOptions.quiet with vcgen := m })
      IO.println ((r.toList.filter (·.obligation.label == "a")).map fun r => (r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## A callee's check does not confirm the caller's check of the same label

`P` is correct: its loop leaves `r == n >= 0`. `Q`'s `post` fails in every run, and has
the label of `P`'s `post`. With the postconditions' source ranges dropped, as in a Core
program built in Lean, the two checks have the same label and metadata. Replay marks
the target in its own procedure only, so the failure of `Q`'s `post` in the call does
not confirm `P`'s, which is `unknown` (it rests on the cut, which has no invariant). -/

def calleeSameLabel :=
#strata
program Core;
procedure Q(n : int, out r : int)
spec { ensures [post]: (r == 1); }
cfg entry { entry: { r := 0; return; } };
procedure P(n : int, out r : int)
spec { requires (int.ge(n, 0)); ensures [post]: (int.ge(r, 0)); }
cfg entry {
  entry: { var i : int := 0; var t : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { i := int.add(i, 1); r := int.add(r, 1); goto loop; }
  done: { call Q(n, out t); return; }
};
#end

/-- info: [(P, other), (Q, fail)]
[(P, other), (Q, fail)] -/
#guard_msgs in
#eval show IO Unit from do
  let p := (TransM.run Inhabited.default (translateProgram calleeSameLabel.program)).fst
  let p : _root_.Core.Program := { decls := p.decls.map fun d => match d with
    | .proc q md =>
      let posts := q.spec.postconditions.toList.map fun (l, c) =>
        (l, { c with md := c.md.eraseElem Imperative.MetaData.provenanceField })
      .proc { q with spec := { q.spec with postconditions := ListMap.ofList posts } } md
    | d => d }
  for m in [Core.VCGenMode.usp, .uwp] do
    match ← (Strata.Core.verifyProgram p { Core.VerifyOptions.quiet with vcgen := m }).toBaseIO with
    | .ok results =>
      let post := results.toList.filter (·.obligation.label == "post")
      IO.println ((post.map fun r =>
        ((Core.PassiveVC.sourceProcOf r.obligation.metadata).getD "?",
          if r.isSuccess then "pass" else if r.isFailure then "fail" else "other")).mergeSort
        (fun a b => decide (a.1 ≤ b.1)))
    | .error e => IO.println s!"error: {e}"

/-! ## Replay confirms a callee's failing precondition after a loop

Every run of `P` calls `f(0)`, outside `f`'s precondition `x > 0`. Call elimination
turns the precondition into an assertion of `P`, `callElimAssert_f_pre_…`, which rests
on the cut of the loop. Replay finds the call it comes from, and the run's call of `f`
fails the precondition, so the assertion fails. `p_post` comes after the failed check,
and stays `unknown`. -/

def preAfterLoop :=
#strata
program Core;
procedure f(x : int) spec { requires [f_pre]: (int.gt(x, 0)); } { };
procedure P(n : int, out r : int)
spec { ensures [p_post]: (int.lt(r, 0)); }
cfg entry {
  entry: { var i : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { i := int.add(i, 1); goto loop; }
  done: { call f(0); return; }
};
#end

/-- info: [(f_pre, fail), (p_post, other)]
[(f_pre, fail), (p_post, other)] -/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify preAfterLoop (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println (r.toList.map fun r =>
      (if r.obligation.label.startsWith "callElimAssert_f_pre" then "f_pre" else r.obligation.label,
        if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

/-! ## Replay runs an abstract callee without outputs

`log` and `g` are abstract and have no outputs, so a call changes no variable, and replay
runs it exactly: it assumes the callee's postconditions and goes on. So the call of `f(0)`
after them is reached, and its precondition, which fails on every run, is confirmed, as in
`preAfterLoop`. -/

def abstractNoOutputs :=
#strata
program Core;
procedure log(x : int) { };
procedure g(x : int) spec { requires [g_pre]: (int.gt(x, 0)); ensures [g_post]: (true); } { };
procedure f(x : int) spec { requires [a]: (int.gt(x, 0)); } { };
procedure P(n : int, out r : int)
cfg entry {
  entry: { var i : int := 0; r := 0; goto loop; }
  loop: { branch (int.lt(i, n)) goto body else goto done; }
  body: { i := int.add(i, 1); goto loop; }
  done: { call log(i); call g(7); call f(0); return; }
};
#end

/-- info: [(a, fail)]
[(a, fail)] -/
#guard_msgs in
#eval show IO Unit from do
  for m in [Core.VCGenMode.usp, .uwp] do
    let r ← Strata.Core.verify abstractNoOutputs
      (options := { Core.VerifyOptions.quiet with vcgen := m })
    IO.println ((r.toList.filter (·.obligation.label.startsWith "callElimAssert_a")).map
      fun r => ("a", if r.isSuccess then "pass" else if r.isFailure then "fail" else "other"))

end Strata.Test.PassiveVCGenRegression

end

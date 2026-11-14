/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.InterpreterCFG
meta import Strata.Languages.Core.InterpreterKleene
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.InterpreterTestUtils

/-! # Control flow of the Kleene and CFG drivers under `ReplayM`

Kleene programs run by `runCoreInterpKleene` at `ReplayM` with an explicit oracle:
- `loop { { var t : int := int.add(x, 1); x := t; } }`, whose body is a block that `init`s the
  local `t`: with the oracle `[tt, tt, ff]` the loop runs its body twice, so `x` goes from `0` to
  `2`, and `t` is undefined after the loop because each iteration's block drops it on exit; with
  `[ff]` the body never runs; with `[tt, tt]` the oracle runs out at the third decision;
- the same loop without the explicit block: each iteration still runs in the loop's own block,
  so `t` is dropped after every iteration, while two `init t` in sequence outside a block fail;
- `choice { x := 1 } { x := 2 }` with the oracles `[tt]` (left arm) and `[ff]` (right arm), and
  a `.seq` of two choices with the oracle `[ff, tt]`.

CFG programs run by `runCoreInterpCFG` at `ReplayM`:
- `counted(out x)`, a counted loop whose back-edge `c1 → c0` runs while `x < 3`: from `x ↦ 0`
  it halts at `x ↦ 3`;
- `call withLocal(out x)` from `x ↦ 7`, where `withLocal(out r)` has a CFG body that declares
  the local `t := 5` and sets `r := t`: the caller ends at `x ↦ 5` with `t` undefined, and the
  callee body runner `Calls.runCallee` returns the callee's halting store projected through its
  entry frame (`RStore.project`): `r ↦ 5`, `t` undefined. -/

meta section

namespace InterpreterKleeneControlTest

open Core Lambda Imperative

/-- The procedures whose bodies the programs below are built from. -/
private def program :=
#strata
program Core;
procedure loopBody(out x : int)
{
  var t : int := int.add(x, 1);
  x := t;
};
procedure arms(out x : int)
{
  x := 1;
  x := 2;
};
procedure counted(out x : int)
cfg c0 {
  c0: {
    branch (int.lt(x, 3)) goto c1 else goto c2;
  }
  c1: {
    x := int.add(x, 1);
    goto c0;
  }
  c2: {
    return;
  }
};
procedure withLocal(out r : int)
cfg e0 {
  e0: {
    var t : int := 5;
    r := t;
    return;
  }
};
procedure caller(out x : int)
cfg k0 {
  k0: {
    call withLocal(out x);
    return;
  }
};
#end

-- The translation of `program` reports no errors.
#guard Strata.InterpreterTestUtils.translationOk program

/-- The procedure table of `program`. -/
private def π : String → Option Procedure := Strata.InterpreterTestUtils.procTable program

/-- The commands of the structured body of the procedure `n`, `[]` if it has none. -/
private def bodyCmds (n : String) : List Command :=
  match (π n).map Procedure.body with
  | some (.structured ss) => ss.filterMap fun | .cmd c => some c | _ => none
  | _ => []

/-- The CFG body of the procedure `n`, the empty CFG if it has none. -/
private def cfgBody (n : String) : DetCFG Expression Command :=
  match (π n).map Procedure.body with
  | some (.cfg g) => g
  | _ => { entry := "", blocks := [] }

/-- The Core identifier `name`. -/
private def id (name : String) : CoreIdent := ⟨name, ()⟩
/-- The integer literal `n`. -/
private def int (n : Int) : Expression.Expr := .intConst default n

/-- The environment with the single binding `x ↦ v`, at `Core.Factory`. -/
private def envX (v : Int) : IEnv Expression :=
  { store := .ofStore fun n => if n == id "x" then some (int v) else none,
    factory := Core.Factory }

/-- The `i`-th command of the structured body of `n`, as a Kleene command. -/
private def kcmd (n : String) (i : Nat) : KleeneStmt Expression Command :=
  .cmd ((bodyCmds n)[i]?.getD (.call "" [] #[]))

/-- The values of `x` and `t` in the terminal store of a Kleene replay run, and the oracle
    values the run consumed; `none` for a run that does not reach `.terminal`. -/
private def kleeneRun (s : KleeneStmt Expression Command) (oracle : List Expression.Expr) :
    Option (Option Expression.Expr × Option Expression.Expr × Nat) :=
  match replayRun (runCoreInterpKleene (m := ReplayM Expression) π 100 (.stmt s (envX 0))) {}
      { remaining := oracle } with
  | (.ok (.terminal ρ), st) => some (ρ.store.get (id "x"), ρ.store.get (id "t"), st.usedRev.length)
  | _ => none

/-- The error a Kleene replay run stops with; `none` for a run that succeeds. -/
private def kleeneError (s : KleeneStmt Expression Command) (oracle : List Expression.Expr) :
    Option StopReason :=
  match replayRun (runCoreInterpKleene (m := ReplayM Expression) π 100 (.stmt s (envX 0))) {}
      { remaining := oracle } with
  | (.error r, _) => some r
  | _ => none

/-! ## Kleene loops whose body is a block declaring a local -/

/-- `loop { { var t : int := int.add(x, 1); x := t; } }`. -/
private def blockLoop : KleeneStmt Expression Command :=
  .loop (.block (.seq (kcmd "loopBody" 0) (kcmd "loopBody" 1)))

-- Two iterations: `x` is `2`, the local `t` is gone, three oracle values were consumed.
#guard kleeneRun blockLoop [HasBool.tt, HasBool.tt, HasBool.ff] =ₘ some (some (int 2), none, 3)
-- No iteration.
#guard kleeneRun blockLoop [HasBool.ff] =ₘ some (some (int 0), none, 1)
-- The oracle runs out at the third decision.
#guard kleeneError blockLoop [HasBool.tt, HasBool.tt] == some .oracleExhausted

/-- The same loop without the explicit block. -/
private def flatLoop : KleeneStmt Expression Command :=
  .loop (.seq (kcmd "loopBody" 0) (kcmd "loopBody" 1))

-- Each iteration runs in the loop's own iteration block, which drops `t` on exit, so the second
-- iteration's `init t` succeeds and `t` is gone after the loop.
#guard kleeneRun flatLoop [HasBool.tt, HasBool.tt, HasBool.ff] =ₘ some (some (int 2), none, 3)
-- Outside a block, `t` survives its `init` ...
#guard kleeneRun (.seq (kcmd "loopBody" 0) (kcmd "loopBody" 1)) [] =ₘ
  some (some (int 1), some (int 1), 0)
-- ... and a second `init t` fails.
#guard kleeneError (.seq (kcmd "loopBody" 0) (kcmd "loopBody" 0)) [] ==
  some .programInitTargetAlreadyDefined

/-! ## Kleene choices and sequences -/

/-- `choice { x := 1 } { x := 2 }`. -/
private def arms : KleeneStmt Expression Command := .choice (kcmd "arms" 0) (kcmd "arms" 1)

#guard kleeneRun arms [HasBool.tt] =ₘ some (some (int 1), none, 1)
#guard kleeneRun arms [HasBool.ff] =ₘ some (some (int 2), none, 1)
-- A sequence of two choices consumes two oracle values; the second choice decides `x`.
#guard kleeneRun (.seq arms arms) [HasBool.ff, HasBool.tt] =ₘ some (some (int 1), none, 2)
#guard kleeneRun (.seq arms arms) [HasBool.tt, HasBool.ff] =ₘ some (some (int 2), none, 2)

-- `=ₘ` ignores metadata but never a value: two results that differ only in a value
-- (here `int 1` vs `int 2`, both at the default location) compare `false`.
#guard !((some (some (int 1), none, 3) : Option (Option Expression.Expr × Option Expression.Expr × Nat))
          =ₘ some (some (int 2), none, 3))

-- Location coverage (metadata-sensitive, exact `==`): a read variable carries the
-- reference's location at the evaluator's output, not the stored value's. Removing the
-- fvar read re-tag in `LExpr.evalCore` would make this fail.
#guard
  (let refLoc : ExprSourceLoc := .synthesized "ref"
   let env : Lambda.Env CoreLParams :=
     fun y => if y == id "x" then some (.intConst (.synthesized "val") 7) else none
   ((LExpr.evalCore 1 Core.Factory env (.fvar refLoc (id "x") (some .int))).fst).metadata == refLoc)

/-! ## A CFG back-edge -/

/-- The value of `x` in the terminal store of a CFG replay run of the body of `n` from `env`. -/
private def cfgX (n : String) (env : IEnv Expression) : Option Expression.Expr :=
  match replayRun (runCoreInterpCFG (m := ReplayM Expression) π 100
      (.atBlock (cfgBody n) (cfgBody n).entry env)) {} { remaining := [] } with
  | (.ok (.terminal ρ), _) => ρ.store.get (id "x")
  | _ => none

-- The back-edge runs three times from `x ↦ 0`, and the loop exits at `x ↦ 3`.
#guard cfgX "counted" (envX 0) =ₘ some (int 3)
-- From `x ↦ 5` the guard is false at once.
#guard cfgX "counted" (envX 5) =ₘ some (int 5)

/-! ## A CFG callee that declares a local -/

-- The caller ends at `x ↦ 5`.
#guard cfgX "caller" (envX 7) =ₘ some (int 5)

-- The callee's local `t` does not reach the caller's store.
#guard match replayRun (runCoreInterpCFG (m := ReplayM Expression) π 100
    (.atBlock (cfgBody "caller") "k0" (envX 7))) {} { remaining := [] } with
  | (.ok (.terminal ρ), _) => (ρ.store.get (id "t")).isNone
  | _ => false

/-- The store `Calls.runCallee` returns for the CFG body of `withLocal` from the entry frame
    `r ↦ 0`: the callee's halting store projected through the entry frame. -/
private def calleeExit : Option (RStore Expression) :=
  match replayRun (Calls.runCallee (m := ReplayM Expression)
      (fun fuel env c => Calls.stepCmd π 10 fuel env c) "withLocal" (.cfg (cfgBody "withLocal"))
      Core.Factory 100 (fun n => if n == id "r" then some (int 0) else none)) {}
      { remaining := [] } with
  | (.ok σ, _) => some σ
  | _ => none

-- `r` holds the callee's result, and the callee's local `t` is projected away.
#guard (calleeExit.bind (· (id "r"))) =ₘ some (int 5)
#guard (calleeExit.map fun σ => (σ (id "t")).isNone) == some true


end InterpreterKleeneControlTest

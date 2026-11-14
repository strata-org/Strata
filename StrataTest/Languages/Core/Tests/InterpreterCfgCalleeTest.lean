/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.DDMTransform.Translate
meta import Strata.Languages.Core.InterpreterCFG
meta import Strata.Languages.Core.InterpreterKleene
meta import Strata.Languages.Core.InterpreterEval
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.InterpreterTestUtils

/-! # Executed calls to a procedure with a CFG body

The procedures are written in Core's DDM syntax (`program`) and run after DDM
translation.  The callee `pick(a : int, out r : int)` has a CFG body: block `b0`
branches on `0 < a` to `pos`, which calls `one(out r)`, or to `neg`, which sets `r := 0`.
The nested callee `one(out z : int)` has the structured body `z := 1`.  Each caller runs
`call pick(a, out x)` from the store `x ↦ 7` under the `EvalM` instance: a structured caller
(the call-aware statement engine `Calls.runCallInterp` and Core's `runCoreInterp`), a CFG
caller (the CFG driver over `Calls.cfgStepCmd` and Core's `runCoreInterpCFG`) and a Kleene
caller (`Calls.runCallInterpKleene` and Core's `runCoreInterpKleene`).  The callers named
`…Pos` pass `a = 5`: the callee takes the `pos` branch and the nested call, and the caller
ends at `x ↦ 1`.  The callers named `…Neg` pass `a = -3`: the callee takes `neg` and the
caller ends at `x ↦ 0`.  The Kleene caller runs the call command of the structured
caller. -/

meta section

namespace InterpreterCfgCalleeTest

open Core Lambda Imperative

/-- The callees `one` and `pick`, and the structured and CFG callers for `a = 5` and
    `a = -3`. -/
private def program :=
#strata
program Core;
procedure one(out z : int)
{
  z := 1;
};
procedure pick(a : int, out r : int)
cfg b0 {
  b0: {
    branch (int.lt(0, a)) goto pos else goto neg;
  }
  pos: {
    call one(out r);
    return;
  }
  neg: {
    r := 0;
    return;
  }
};
procedure structuredCallerPos(out x : int)
{
  call pick(5, out x);
};
procedure structuredCallerNeg(out x : int)
{
  call pick(int.neg(3), out x);
};
procedure cfgCallerPos(out x : int)
cfg c0 {
  c0: {
    call pick(5, out x);
    return;
  }
};
procedure cfgCallerNeg(out x : int)
cfg c0 {
  c0: {
    call pick(int.neg(3), out x);
    return;
  }
};
#end

-- The translation of `program` reports no errors.
#guard Strata.InterpreterTestUtils.translationOk program

/-- The procedure table of `program`. -/
private def π : String → Option Procedure := Strata.InterpreterTestUtils.procTable program

/-- The call command of the structured caller `n`, whose body is one call. -/
private def callerCmd (n : String) : Command :=
  match (π n).map Procedure.body with
  | some (.structured [.cmd c]) => c
  | _ => .call "" [] #[]

/-- The CFG body of the procedure `n`, the empty CFG if it has none. -/
private def cfgBody (n : String) : DetCFG Expression Command :=
  match (π n).map Procedure.body with
  | some (.cfg g) => g
  | _ => { entry := "", blocks := [] }

/-- The Core identifier `name`. -/
private def id (name : String) : CoreIdent := ⟨name, ()⟩
/-- The integer literal `n`. -/
private def int (n : Int) : Expression.Expr := .intConst default n

/-- The caller store `x ↦ 7`. -/
private def σ0 : RStore Expression := fun n => if n == id "x" then some (int 7) else none

/-- The caller environment: store `σ0` at `Core.Factory`. -/
private def env0 : IEnv Expression := { store := .ofStore σ0, factory := Core.Factory }

/-- The `EvalM` options of every run. -/
private def opts : EvalOpts := EvalOpts.legacy 100

/-- `x` in the terminal store of a structured run, `none` for every other outcome. -/
private def xOfCfg :
    Except EvalHalt (IConfig Expression Command) × EvalState → Option Expression.Expr
  | (.ok (.terminal ρ), _) => ρ.store.get (id "x")
  | _ => none

/-- `x` in the terminal store of a CFG run, `none` for every other outcome. -/
private def xOfCFG :
    Except EvalHalt (ICFGConfig String Command Expression) × EvalState → Option Expression.Expr
  | (.ok (.terminal ρ), _) => ρ.store.get (id "x")
  | _ => none

/-- `x` in the terminal store of a Kleene run, `none` for every other outcome. -/
private def xOfKleene :
    Except EvalHalt (IKleeneConfig Expression Command) × EvalState → Option Expression.Expr
  | (.ok (.terminal ρ), _) => ρ.store.get (id "x")
  | _ => none

/-! ## A structured caller -/

/-- `x` after the generic statement engine runs the structured caller `n`. -/
private def structGeneric (n : String) : Option Expression.Expr :=
  xOfCfg ((((Calls.runCallInterp (m := EvalM) π 100 (.stmt (.cmd (callerCmd n)) env0)).run
    opts).run).run {})

/-- `x` after Core's statement engine runs the structured caller `n`. -/
private def structCore (n : String) : Option Expression.Expr :=
  xOfCfg (runCoreEvalWith π opts 100 (.stmt (.cmd (callerCmd n)) env0))

#guard structGeneric "structuredCallerPos" =ₘ some (int 1)
#guard structGeneric "structuredCallerNeg" =ₘ some (int 0)
#guard structCore "structuredCallerPos" =ₘ some (int 1)
#guard structCore "structuredCallerNeg" =ₘ some (int 0)

/-! ## A CFG caller -/

/-- `x` after the CFG driver over `Calls.cfgStepCmd` (at the default call-depth limit) runs the
    body of the CFG caller `n`. -/
private def cfgGeneric (n : String) : Option Expression.Expr :=
  xOfCFG ((((runInterpCFG (Calls.cfgStepCmd (m := EvalM) π defaultMaxCallDepth) 100
    (.atBlock (cfgBody n) "c0" env0)).run opts).run).run {})

/-- `x` after Core's CFG driver runs the body of the CFG caller `n`. -/
private def cfgCore (n : String) : Option Expression.Expr :=
  xOfCFG ((((runCoreInterpCFG (m := EvalM) π 100
    (.atBlock (cfgBody n) "c0" env0)).run opts).run).run {})

#guard cfgGeneric "cfgCallerPos" =ₘ some (int 1)
#guard cfgGeneric "cfgCallerNeg" =ₘ some (int 0)
#guard cfgCore "cfgCallerPos" =ₘ some (int 1)
#guard cfgCore "cfgCallerNeg" =ₘ some (int 0)

/-! ## A Kleene caller -/

/-- `x` after the generic Kleene driver runs the call of the structured caller `n`. -/
private def kleeneGeneric (n : String) : Option Expression.Expr :=
  xOfKleene ((((Calls.runCallInterpKleene (m := EvalM) π 100
    (.stmt (.cmd (callerCmd n)) env0)).run opts).run).run {})

/-- `x` after Core's Kleene driver runs the call of the structured caller `n`. -/
private def kleeneCore (n : String) : Option Expression.Expr :=
  xOfKleene ((((runCoreInterpKleene (m := EvalM) π 100
    (.stmt (.cmd (callerCmd n)) env0)).run opts).run).run {})

#guard kleeneGeneric "structuredCallerPos" =ₘ some (int 1)
#guard kleeneGeneric "structuredCallerNeg" =ₘ some (int 0)
#guard kleeneCore "structuredCallerPos" =ₘ some (int 1)
#guard kleeneCore "structuredCallerNeg" =ₘ some (int 0)

end InterpreterCfgCalleeTest

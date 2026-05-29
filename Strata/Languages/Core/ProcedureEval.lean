/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementEval
public import Strata.Languages.Core.StatementSemantics
public section

---------------------------------------------------------------------

namespace Core

namespace Procedure
open Std

open Statement Lambda LExpr

def fixupError (E : Env) : Env :=
  -- Clearing `error` and popping frames must be unconditional: a leftover
  -- error short-circuits the next procedure's evaluation in `StatementEval`.
  -- Clean-path obligations in `E.deferred` survive — each carries its own
  -- assumptions and is independently provable.
  { E with error := none,
           exprEnv.state := E.exprEnv.state.pop,
           pathConditions := E.pathConditions.pop }

/--
Merge multiple procedure evaluation results into one.

After `fixupError`, all paths through a procedure have identical variable state
and path conditions — the procedure scope and its path-condition scope have been
popped, leaving only the outer (global) scope, which is the same on every path.
This holds for both clean and errored paths: `fixupError` pops frames and
clears `Env.error` unconditionally, so an errored procedure does not
contaminate the env handed to the next procedure.
The differences across paths are:

- `deferred`: path-specific proof obligations (each already carries its own
  assumptions), which we union. No duplicates arise: `processIteBranches`
  clears `deferred` on the false branch, so pre-split obligations appear only
  in the first (true) path; post-split obligations appear in each path under
  distinct path conditions.
- `exprEnv.config.usedNames`: may diverge when branches generate different
  variables. We union the sets to prevent fresh-variable name collisions in
  subsequent evaluation.

The `fallback` Env is returned when `results` is empty (which should not occur
in practice, since `Statement.eval` always produces at least one result).
-/
private def mergeResults (fallback : Env) (results : List Env) : Env :=
  match results with
  | [] => fallback
  | [E] => E
  | E :: rest =>
    let allDeferred := rest.foldl (fun acc e => acc ++ e.deferred) E.deferred
    let mergedNames := rest.foldl (fun acc e =>
      acc.union e.exprEnv.config.usedNames) E.exprEnv.config.usedNames
    { E with
      deferred := allDeferred,
      exprEnv  := { E.exprEnv with config := { E.exprEnv.config with usedNames := mergedNames } } }

private def evalBlockCmds (E : Env) (old_var_subst : SubstMap)
    (cmds : List Command) : Env :=
  cmds.foldl (fun env cmd =>
    if env.error.isSome then env
    else (Statement.Command.eval env old_var_subst cmd).snd) E

private def evalCFGStep (cfg : DetCFG) (old_var_subst : SubstMap)
    (active : List (String × Env)) :
    List (String × Env) × List Env × Statistics :=
  active.foldl (fun (newActive, finished, stats) (label, env) =>
    if env.error.isSome then
      (newActive, env :: finished, stats)
    else
      match cfg.blocks.lookup label with
      | none =>
        let env' := { env with error := some (.Misc
            s!"evalCFG: block '{label}' not found in CFG") }
        (newActive, env' :: finished, stats)
      | some blk =>
        let env' := evalBlockCmds env old_var_subst blk.cmds
        if env'.error.isSome then
          (newActive, env' :: finished, stats)
        else
          let stats := stats.increment s!"{Evaluator.Stats.simulatedStmts}"
          match blk.transfer with
          | .finish _ =>
            (newActive, env' :: finished, stats)
          | .condGoto cond lt lf _ =>
            let cond' := env'.exprEval cond
            match cond' with
            | .true _ => ((lt, env') :: newActive, finished, stats)
            | .false _ => ((lf, env') :: newActive, finished, stats)
            | _ =>
              let condErased := cond.eraseTypes
              let label_t := toString (f!"<cfgBranch_true: {condErased}>")
              let label_f := toString (f!"<cfgBranch_false: !({condErased})>")
              let env_t := { env' with pathConditions :=
                (env'.pathConditions.addInNewest
                  [.assumption label_t cond']) }
              let env_f := { env' with pathConditions :=
                (env'.pathConditions.addInNewest
                  [.assumption label_f
                    (Lambda.LExpr.ite () cond' (LExpr.false ()) (LExpr.true ()))]) }
              ((lt, env_t) :: (lf, env_f) :: newActive, finished, stats))
    ([], [], {})

private partial def evalCFGBlocks (cfg : DetCFG) (old_var_subst : SubstMap)
    (active : List (String × Env)) (finished : List Env)
    (stats : Statistics) : List Env × Statistics :=
  match active with
  | [] => (finished, stats)
  | (_, env) :: _ =>
    if env.fuel == 0 then
      let errorEnvs := active.map fun (_, e) =>
        { e with error := some .OutOfFuel }
      (errorEnvs ++ finished,
       stats.increment s!"{Evaluator.Stats.simulatingStmtHitOutOfFuel}" active.length)
    else
      let active := active.map fun (l, e) => (l, { e with fuel := e.fuel - 1 })
      let (newActive, newFinished, stepStats) :=
        evalCFGStep cfg old_var_subst active
      evalCFGBlocks cfg old_var_subst newActive
        (newFinished ++ finished) (stats.merge stepStats)

private def evalCFGBody (E : Env) (old_var_subst : SubstMap)
    (precond_assumes postcond_asserts : Statements)
    (cfg : DetCFG) : List Env × Statistics :=
  let (preEnvs, preStats) := Statement.eval E old_var_subst precond_assumes
  let emptyAcc : List Env × Statistics := ([], {})
  let (cfgResultsRev, cfgStats) :=
    preEnvs.foldl (fun acc preEnv =>
      let (accEnvs, accStats) := acc
      let (envs, stats) :=
        evalCFGBlocks cfg old_var_subst [(cfg.entry, preEnv)] [] {}
      (envs.reverse ++ accEnvs, accStats.merge stats)) emptyAcc
  let cfgResults := cfgResultsRev.reverse
  let (postResultsRev, postStats) :=
    cfgResults.foldl (fun acc cfgEnv =>
      let (accEnvs, accStats) := acc
      if cfgEnv.error.isSome then
        (cfgEnv :: accEnvs, accStats)
      else
        let (envs, stats) := Statement.eval cfgEnv old_var_subst postcond_asserts
        (envs.reverse ++ accEnvs, accStats.merge stats)) emptyAcc
  (postResultsRev.reverse, preStats.merge (cfgStats.merge postStats))

/--
Evaluate a single procedure: generate fresh variables for parameters,
execute the body, check postconditions, and collect proof obligations.

`fuel` is the evaluator work budget seeded into `E.fuel` before evaluation.
For CFG bodies, fuel is decremented once per active symbolic path per block
visit in `evalCFGBlocks` — so a program with `K` concurrent paths and `N`
block visits consumes `K × N` fuel. The default `100000` is generous enough
for typical SMACK-translated programs (shallow branching, <100 blocks);
tighter or looser budgets are exposed via a CLI flag in a later task.
-/

def eval (E : Env) (p : Procedure) (fuel : Nat := 100000) : Env × Statistics :=
  -- Create a new scope with the formals and return variables. We will pop this
  -- scope at the end of this procedure.
  -- Parameters go through genFVars for globally unique names.
  -- Mark original parameter names as used so that fvar names always differ
  -- from the scope keys. Without this, a bare fvar "x" would be captured
  -- by the scope entry for "x" after reassignment, causing old(x) to
  -- resolve to the post-assignment value instead of the initial value.
  let vars := p.header.inputs.keys ++ p.header.outputs.keys
  let E := vars.foldl (fun E (v : CoreIdent) =>
    { E with exprEnv.config.usedNames := E.exprEnv.config.usedNames.insert v.name }) E
  let var_tys := p.header.inputs.values ++ p.header.outputs.values
  let var_tys := var_tys.map (fun ty => some ty)
  let vars_typed := vars.zip var_tys
  let (vals, E) := E.genFVars vars_typed
  let pVarMap := List.zip vars (var_tys.zip vals)
  let E := E.pushScope pVarMap
  let E := { E with pathConditions := E.pathConditions.push [] }
  -- For input parameters that also appear as outputs, old(param) should use
  -- the input parameter's initial value.
  let outputNames := p.header.outputs.keys
  let inputParamSubst := E.exprEnv.state.newest.filterMap fun (id, _, e) =>
    if p.header.inputs.keys.contains id && outputNames.contains id
    then some (CoreIdent.mkOld id.name, e) else none
  let old_g_subst := inputParamSubst
  let postcond_asserts :=
    List.map (fun (label, check) =>
                match check.attr with
                | .Free =>
                    -- NOTE: A free postcondition is not checked.
                    -- We simply change a free-postcondition to "true", but
                    -- keep a record in the metadata field.
                    -- TODO: Perhaps introduce an "opaque" expression construct
                    -- that hides the expression from the evaluator, allowing us
                    -- to retain the postcondition body instead of replacing it
                    -- with "true".
                  (.assert label (.true ())
                                 ((Imperative.MetaData.pushElem
                                  #[]
                                  (.label label)
                                  (.expr check.expr)).pushElem
                                  (.label label)
                                  (.msg "FreePostCondition")))
                | _ => (.assert label check.expr check.md))
      p.spec.postconditions
  let precond_assumes :=
    List.map (fun (label, check) =>
      /- the assumptions from preconditions are set to have empty metadata  -/
      (.assume label check.expr check.md))
      p.spec.preconditions
  let E := { E with fuel := fuel }
  match p.body with
  | .cfg cfgBody =>
    let (ssEs, evalStats) :=
      evalCFGBody E old_g_subst precond_assumes postcond_asserts cfgBody
    (mergeResults E (ssEs.map (fun sE => fixupError sE)), evalStats)
  | .structured bodyStmts =>
    let (ssEs, evalStats) := Statement.eval E old_g_subst (precond_assumes ++ bodyStmts ++ postcond_asserts)
    (mergeResults E (ssEs.map (fun sE => fixupError sE)), evalStats)

---------------------------------------------------------------------

end Procedure
end Core

end -- public section

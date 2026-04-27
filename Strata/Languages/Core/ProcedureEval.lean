/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.Util.Statistics
import Strata.Languages.Core.StatementEval
public section

---------------------------------------------------------------------

namespace Core

namespace Procedure
open Std

open Statement Lambda LExpr

def fixupError (E : Env) : Env :=
  match E.error with
  | none => { E with exprEnv.state := E.exprEnv.state.pop,
                     pathConditions := E.pathConditions.pop }
  | some _ => E

/--
Merge multiple procedure evaluation results into one.

After `fixupError`, all paths through a procedure have identical variable state
and path conditions — the procedure scope and its path-condition scope have been
popped, leaving only the outer (global) scope which is the same on every path.
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

/--
Evaluate a single procedure: generate fresh variables for parameters,
execute the body, check postconditions, and collect proof obligations.
-/

def eval (E : Env) (p : Procedure) : Env × Statistics :=
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
  let (ssEs, evalStats) := Statement.eval E old_g_subst (precond_assumes ++ p.body ++ postcond_asserts)
  (mergeResults E (ssEs.map (fun sE => fixupError sE)), evalStats)

---------------------------------------------------------------------

end Procedure
end Core

end -- public section

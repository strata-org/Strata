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

After `fixupError`, all paths through a procedure that did not fail have
identical variable state and path conditions — the procedure scope and its
path-condition scope have been popped, leaving only the outer (global) scope
which is the same on every path. Every path also carries the same name supply, the one
statement evaluation threads through all paths.
The differences across paths are:

- `deferred`: path-specific proof obligations (each already carries its own
  assumptions), which we union. No duplicates arise: `processIteBranches`
  clears `deferred` on the false branch, so pre-split obligations appear only
  in the first (true) path; post-split obligations appear in each path under
  distinct path conditions.
- `error`: a path whose evaluation failed is not popped by `fixupError` and
  carries no obligations for the statements after the failure. The merged Env
  takes the first error of any path, so the caller reports the procedure as
  failed instead of dropping that path.

`Statement.eval` produces at least one result; if `results` is empty, the result is
`fallback` with an error.
-/
private def mergeResults (fallback : Env) (results : List Env) : Env :=
  match results with
  | [] => { fallback with error := some (.Misc "symbolic evaluation produced no paths") }
  | [E] => E
  | E :: rest =>
    let error := results.findSome? (·.error)
    -- The first path's obligations leave `E` before the others are appended, so they are
    -- appended in place.
    let first := E.deferred
    let E := { E with deferred := #[] }
    let allDeferred := rest.foldl (fun acc e => acc ++ e.deferred) first
    { E with error, deferred := allDeferred }

/--
Evaluate a single procedure: generate fresh variables for parameters,
execute the body, check postconditions, and collect proof obligations.
-/

def eval (E : Env) (p : Procedure) : Env × Statistics :=
  -- A new scope binds the parameters and the `old` values of the in-out parameters; it is
  -- popped at the end of the procedure.
  -- Each parameter's initial value is a fresh unknown (`genFVars`).
  -- An in-out parameter is one variable: it is bound once, as an input.
  let outputsOnly := p.header.outputs.filter fun (x, _) => !p.header.inputs.keys.contains x
  let vars := p.header.inputs.keys ++ outputsOnly.map (·.1)
  let var_tys := p.header.inputs.values ++ outputsOnly.map (·.2)
  let var_tys := var_tys.map (fun ty => some ty)
  let vars_typed := vars.zip var_tys
  let (vals, E) := E.genFVars vars_typed
  let pVarMap := List.zip vars (var_tys.zip vals)
  -- `old x`, for an in-out parameter `x`, is bound to `x`'s initial value.
  let inoutNames := p.header.getInoutParams.keys
  let oldVarMap := pVarMap.filterMap fun (x, tyv) =>
    if inoutNames.contains x then some (CoreIdent.mkOld x.name, tyv) else none
  let E := E.pushScope (pVarMap ++ oldVarMap)
  let E := { E with pathConditions := E.pathConditions.push [] }
  match p.body with
  | .structured bodyStmts =>
    -- `E` stays alive as the fallback without the name supply, so the supply has one
    -- reference during evaluation.
    let (names, E) := E.takeNames
    let (ssEs, evalStats) := Statement.eval (E.withNames names) (p.contractWrapped bodyStmts)
    (mergeResults E (ssEs.map (fun sE => fixupError sE)), evalStats)
  | .cfg _ =>
    -- CFG bodies are not supported here.
    -- The caller names the procedure, so this says only what went wrong.
    let errEnv := { E with error := some (.Misc "CFG bodies not supported yet") }
    (errEnv, {})

---------------------------------------------------------------------

end Procedure
end Core

end -- public section

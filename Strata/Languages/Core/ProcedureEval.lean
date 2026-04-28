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
- `exprEnv.config.gen`: may diverge when branches execute different numbers of
  `genFVar` calls (e.g. procedure calls only in one branch). We take the max to
  prevent fresh-variable name collisions in subsequent evaluation.

The `fallback` Env is returned when `results` is empty (which should not occur
in practice, since `Statement.eval` always produces at least one result).
-/
private def mergeResults (fallback : Env) (results : List Env) : Env :=
  match results with
  | [] => fallback
  | [E] => E
  | E :: rest =>
    let allDeferred := rest.foldl (fun acc e => acc ++ e.deferred) E.deferred
    let maxGen      := rest.foldl (fun acc e => max acc e.exprEnv.config.gen) E.exprEnv.config.gen
    { E with
      deferred := allDeferred,
      exprEnv  := { E.exprEnv with config := { E.exprEnv.config with gen := maxGen } } }

def eval (E : Env) (p : Procedure) : Env × Statistics :=
  -- Generate fresh variables for the globals in the modifies clause, and _update_
  -- the context. These reflect the pre-state values of the globals.
  let modifies_tys :=
    p.spec.modifies.map
    (fun l => (E.exprEnv.state.findD l (none, .fvar Strata.SourceRange.none l none)).fst)
  let modifies_typed := p.spec.modifies.zip modifies_tys
  let (globals_fvars, E) := E.genFVars modifies_typed
  let global_init_subst := List.zip modifies_typed globals_fvars
  let E := E.addToContext global_init_subst
  -- Create a new scope with the formals and return variables. We will pop this
  -- scope at the end of this procedure.
  let vars := p.header.inputs.keys ++ p.header.outputs.keys
  let var_tys := p.header.inputs.values ++ p.header.outputs.values
  let var_tys := var_tys.map (fun ty => some ty)
  let (vals, E) := E.genFVars (vars.zip var_tys)
  let pVarMap := List.zip vars (var_tys.zip vals)
  let E := E.pushScope pVarMap
  let E := { E with pathConditions := E.pathConditions.push [] }
  -- Note that the type checker has already done some transformations to ensure
  -- that we only have `old` expressions left for variables.
  -- With `old_var_subst`, we substitute `old <var>` expressions for globals
  -- with the current value of `<var>` in the post-conditions and body.
  -- `Statement.eval` will substitute `old <var>` where `<var>` is a local
  -- variable with the value of `<var>` at each given statement.
  let old_var_subst := E.exprEnv.state.oldest.map (fun (i, _, e) => (i, e))
  -- Build "old g" → pre-state value substitutions for all declared globals.
  -- These are passed as substMap so preprocess can substitute them in postcondition asserts.
  let globalNames : List String := E.program.decls.filterMap fun d =>
    match d with | .var name _ _ _ => some name.name | _ => none
  let old_g_subst := old_var_subst.filterMap fun (id, e) =>
    if globalNames.contains id.name then some (CoreIdent.mkOld id.name, e) else none
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
                  (.assert label (Core.true)
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

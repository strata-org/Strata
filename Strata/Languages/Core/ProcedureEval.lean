/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Statement
import Strata.Languages.Core.StatementEval
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.LoopElim

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

def eval (E : Env) (p : Procedure) : List (Procedure × Env) :=
  -- Generate fresh variables for the globals in the modifies clause, and _update_
  -- the context. These reflect the pre-state values of the globals.
  let modifies_tys :=
    p.spec.modifies.map
    (fun l => (E.exprEnv.state.findD l (none, .fvar () l none)).fst)
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
    List.map (fun (label, check) => (.assume label check.expr)) p.spec.preconditions
  let body' : List Statement := p.body.map Stmt.removeLoops
  let ssEs := Statement.eval E old_var_subst (precond_assumes ++ body' ++ postcond_asserts)
  ssEs.map (fun (ss, sE) => ({ p with body := ss }, fixupError sE))

---------------------------------------------------------------------

def evalOne (E : Env) (p : Procedure) : Procedure × Env :=
  match eval E p with
  | [(p', E')] => (p', E')
  | _ => (p, { E with error := some (.Misc "More than one result environment") })

---------------------------------------------------------------------

end Procedure
end Core

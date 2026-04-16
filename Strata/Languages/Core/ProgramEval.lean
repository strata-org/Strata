/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.ProcedureEval

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)

namespace Program
open Lambda.LTy Lambda.LExpr Statement Procedure Program

public section

def eval (E : Env) : Except String (List Env × Statistics) :=
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
  go E.program.decls E ({} : Statistics)
  where go (decls : Decls) (declsE : Env) (stats : Statistics)
      : Except String (List Env × Statistics) :=
  match decls with
  | [] => .ok ([declsE], stats)
  | decl :: rest =>
    match decl with

    | .var name ty init md =>
      let (ssEs, varStats) := Statement.eval declsE [] [(.init name ty init md)]
      let stats := stats.merge varStats
      ssEs.foldl (fun acc E => do
                      let (accEs, statsAcc) ← acc
                      let (results, s) ← go rest E statsAcc
                      .ok (accEs ++ results, s))
        (.ok ([], stats))

    | .type _ _ =>
      go rest declsE stats

    | .ax a _ =>
      -- All axioms go into the top-level path condition before anything is executed.
      -- There should be exactly one entry in the path condition stack at this point.
      if declsE.pathConditions.length != 1 then
        .error "Internal error: path condition stack misaligned when adding axiom"
      else
        let declsE := { declsE with pathConditions :=
                      declsE.pathConditions.insert (toString $ a.name) a.e }
        go rest declsE stats

    | .distinct _ es _ =>
        let declsE := { declsE with distinct := es :: declsE.distinct }
      go rest declsE stats

    | .proc proc _md =>
      let (E, procStats) := Procedure.eval declsE proc
      go rest E (stats.merge procStats)

    | .func func _ =>
      match declsE.addFactoryFunc func with
      | .error e => .ok ([{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}], stats)
      | .ok new_env =>
        let declsE := new_env
      go rest declsE stats

    | .recFuncBlock funcs _ =>
      match validateCasesTypes funcs declsE.datatypes with
      | .error e => .ok ([{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}], stats)
      | .ok () =>
      let result := funcs.foldlM (fun env func => env.addFactoryFunc func) declsE
      match result with
      | .error e => .ok ([{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}], stats)
      | .ok new_env =>
        let declsE := new_env
        go rest declsE stats


--------------------------------------------------------------------

end -- public section

end Program
end Core

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

def eval (E : Env) : Except Strata.DiagnosticModel (List Env × Statistics) :=
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
  go E.program.decls E ({} : Statistics)
  where go (decls : Decls) (declsE : Env) (stats : Statistics)
      : Except Strata.DiagnosticModel (List Env × Statistics) :=
  match decls with
  | [] => .ok ([declsE], stats)
  | decl :: rest =>
    match decl with

    | .type _ _ =>
      go rest declsE stats

    | .ax a _ =>
      -- All axioms go into the top-level path condition before anything is executed.
      -- There should be exactly one entry in the path condition stack at this point.
      if declsE.pathConditions.length != 1 then
        .error (Strata.DiagnosticModel.fromMessage
            "Internal error: path condition stack misaligned when adding axiom")
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

    | .func func _ => do
      let new_env ← declsE.addFactoryFunc func
      go rest new_env stats

    | .recFuncBlock funcs _ => do
      validateCasesTypes funcs declsE.datatypes
      let declsE ← funcs.foldlM (fun env func => env.addFactoryFunc func) declsE
      go rest declsE stats


--------------------------------------------------------------------

end -- public section

end Program
end Core

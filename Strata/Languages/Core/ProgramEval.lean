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

def eval (E : Env) : List Env :=
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
  let declsEnv := go E.program.decls E
  declsEnv
  where go (decls : Decls) (declsE : Env) : List Env :=
  match decls with
  | [] => [declsE]
  | decl :: rest =>
    match decl with

    | .var name ty init md =>
      (Statement.eval declsE [] [(.init name ty init md)]).flatMap (fun E => go rest E)

    | .type _ _ =>
      go rest declsE

    | .ax a _ =>
      -- All axioms go into the top-level path condition before anything is executed.
      -- There should be exactly one entry in the path condition stack at this point.
      if declsE.pathConditions.length != 1 then
        panic! "Internal error: path condition stack misaligned when adding axiom"
      else
        let declsE := { declsE with pathConditions :=
                      declsE.pathConditions.insert (toString $ a.name) a.e }
        go rest declsE

    | .distinct _ es _ =>
        let declsE := { declsE with distinct := es :: declsE.distinct }
      go rest declsE

    | .proc proc _md =>
      let E := Procedure.eval declsE proc
      go rest E

    | .func func _ =>
      match declsE.addFactoryFunc func with
      | .error e => [{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}]
      | .ok new_env =>
        let declsE := new_env
      go rest declsE

    | .recFuncBlock funcs _ =>
      match validateCasesTypes funcs declsE.datatypes with
      | .error e => [{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}]
      | .ok () =>
      let result := funcs.foldlM (fun env func => env.addFactoryFunc func) declsE
      match result with
      | .error e => [{ declsE with error := some (Imperative.EvalError.Misc f!"{e}")}]
      | .ok new_env =>
        let declsE := new_env
        go rest declsE


--------------------------------------------------------------------

end -- public section

end Program
end Core

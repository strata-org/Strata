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

/--
A new environment, with declarations obtained after the partial evaluation
transform.
-/
structure DeclsEnv where
  env : Env
  xdecls : Decls := []

def initStmtToGlobalVarDecl (s : Statement) : Decl :=
  match s with
  | .init x ty e md => (.var x ty e md)
  | _ => panic s!"Expected a variable initialization; found {format s} instead."

def eval (E : Env) : List (Program × Env) × Statistics :=
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
  let (declsEnv, stats) := go E.program.decls { env := E } ({} : Statistics)
  (declsEnv.map (fun (decls, E) => ({ decls }, E)), stats)
  where go (decls : Decls) (declsE : DeclsEnv) (stats : Statistics)
      : List (Decls × Env) × Statistics :=
  match decls with
  | [] => ([(declsE.xdecls, declsE.env)], stats)
  | decl :: rest =>
    match decl with

    | .var name ty init md =>
      let (ssEs, varStats) := Statement.eval declsE.env [] [(.init name ty init md)]
      let stats := stats.merge varStats
      ssEs.foldl (fun (acc, statsAcc) (ss, E) =>
                      let xdecls := ss.map initStmtToGlobalVarDecl
                      let declsE := { declsE with xdecls := declsE.xdecls ++ xdecls,
                                                  env := E }
                      let (results, s) := go rest declsE statsAcc
                      (acc ++ results, s))
        ([], stats)

    | .type _ _ =>
      go rest { declsE with xdecls := declsE.xdecls ++ [decl] } stats

    | .ax a _ =>
      -- All axioms go into the top-level path condition before anything is executed.
      -- There should be exactly one entry in the path condition stack at this point.
      if declsE.env.pathConditions.length != 1 then
        panic! "Internal error: path condition stack misaligned when adding axiom"
      else
        let declsE := {
          declsE with
            env := { declsE.env with pathConditions :=
                      declsE.env.pathConditions.insert (toString $ a.name) a.e },
                    xdecls := declsE.xdecls ++ [decl] }
        go rest declsE stats

    | .distinct _ es _ =>
        let declsE := {
          declsE with
            env := { declsE.env with distinct := es :: declsE.env.distinct },
            xdecls := declsE.xdecls ++ [decl] }
      go rest declsE stats

    | .proc proc md =>
      let ((p, E), procStats) := Procedure.eval declsE.env proc
      let declsE := { declsE with xdecls := declsE.xdecls ++ [.proc p md], env := E }
      go rest declsE (stats.merge procStats)

    | .func func _ =>
      match declsE.env.addFactoryFunc func with
      | .error e => ([(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})], stats)
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }
      go rest declsE stats

    | .recFuncBlock funcs _ =>
      match validateCasesTypes funcs declsE.env.datatypes with
      | .error e => ([(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})], stats)
      | .ok () =>
      let result := funcs.foldlM (fun env func => env.addFactoryFunc func) declsE.env
      match result with
      | .error e => ([(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})], stats)
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }
        go rest declsE stats


--------------------------------------------------------------------

end -- public section

end Program
end Core

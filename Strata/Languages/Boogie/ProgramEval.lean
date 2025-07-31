/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.ProcedureEval

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)

namespace Program
open Lambda.LTy Lambda.LExpr Statement Procedure Program

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

def eval (E : Env) : List (Program × Env) :=
  let declsEnv := go E.program.decls { env := E }
  declsEnv.map (fun (decls, E) => ({ decls }, E))
  where go (decls : Decls) (declsE : DeclsEnv) : List (Decls × Env) :=
  match decls with
  | [] => [(declsE.xdecls, declsE.env)]
  | decl :: rest =>
    match decl with

    | .var name ty init md =>
      let ssEs := Statement.eval declsE.env [] [(.init name ty init md)]
      ssEs.flatMap (fun (ss, E) =>
                      let xdecls := ss.map initStmtToGlobalVarDecl
                      let declsE := { declsE with xdecls := declsE.xdecls ++ xdecls,
                                                  env := E }
                      go rest declsE)

    | .type _ _ =>
      go rest { declsE with xdecls := declsE.xdecls ++ [decl] }

    | .ax a _ =>
       -- All axioms go into the list of assumptions before anything is executed.
       let declsE := { declsE with
                        env := { declsE.env with pathConditions :=
                                              declsE.env.pathConditions.push [(toString $ a.name, a.e)] },
                        xdecls := declsE.xdecls ++ [decl] }
       go rest declsE

    | .proc proc _ =>
      let pEs := Procedure.eval declsE.env proc
      pEs.flatMap (fun (p, E) =>
                      let declsE := { declsE with xdecls := declsE.xdecls ++ [.proc p],
                                                  env := E }
                      go rest declsE)

    | .func func _ =>
      match declsE.env.addFactoryFunc func with
      | .error e => [(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})]
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }

      go rest declsE


--------------------------------------------------------------------

end Program
end Boogie

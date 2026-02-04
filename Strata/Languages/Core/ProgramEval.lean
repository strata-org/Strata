/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Program
import Strata.Languages.Core.ProcedureEval
import Strata.DL.Lambda.Preconditions

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)

namespace Program
open Lambda.LTy Lambda.LExpr Statement Procedure Program

/--
Generate WF obligations for a function's preconditions and body.

For each precondition (in order):
- Collect WF obligations from the precondition expression
- Earlier preconditions are assumed when checking later ones

For the function body (if present):
- Collect WF obligations from the body expression
- All preconditions are assumed
-/
def generateFuncWFObligations (E : Env) (func : Lambda.LFunc CoreLParams)
    : Imperative.ProofObligations Expression :=
  let factory := E.factory
  let funcName := func.name.name
  -- Counter for unique labels
  let mkLabel (calledFunc : String) (idx : Nat) : String :=
    s!"{funcName}_calls_{calledFunc}_{idx}"
  -- Helper to convert WFObligation to ProofObligation with unique label
  let toProofObligation (ob : Lambda.WFObligation CoreLParams) (idx : Nat)
      (assumptions : Imperative.PathConditions Expression)
      : Imperative.ProofObligation Expression :=
    { label := mkLabel ob.funcName idx
      property := .assert
      assumptions := assumptions
      obligation := ob.obligation
      metadata := #[] }
  -- Process preconditions: each precondition is checked with earlier ones as assumptions
  let (precondObligations, finalAssumptions, counter) := func.preconditions.foldl
    (fun (acc, assumptions, idx) precond =>
      let wfObs := Lambda.collectWFObligations factory precond
      let (newObs, newIdx) := wfObs.foldl
        (fun (obs, i) ob => (obs.push (toProofObligation ob i assumptions), i + 1))
        (#[], idx)
      let newAssumptions := assumptions.addInNewest [(s!"precond_{funcName}", precond)]
      (acc ++ newObs, newAssumptions, newIdx))
    (#[], E.pathConditions, 0)
  -- Process body: all preconditions are assumed
  let bodyObligations := match func.body with
    | none => #[]
    | some body =>
      let wfObs := Lambda.collectWFObligations factory body
      let (obs, _) := wfObs.foldl
        (fun (obs, i) ob => (obs.push (toProofObligation ob i finalAssumptions), i + 1))
        (#[], counter)
      obs
  precondObligations ++ bodyObligations

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
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
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
        go rest declsE

    | .distinct _ es _ =>
        let declsE := {
          declsE with
            env := { declsE.env with distinct := es :: declsE.env.distinct },
            xdecls := declsE.xdecls ++ [decl] }
      go rest declsE

    | .proc proc _ =>
      let pEs := Procedure.eval declsE.env proc
      pEs.flatMap (fun (p, E) =>
                      let declsE := { declsE with xdecls := declsE.xdecls ++ [.proc p],
                                                  env := E }
                      go rest declsE)

    | .func func _ =>
      -- Generate WF obligations for function preconditions and body
      let wfObligations := generateFuncWFObligations declsE.env func
      let env_with_wf := { declsE.env with deferred := declsE.env.deferred ++ wfObligations }
      match env_with_wf.addFactoryFunc func with
      | .error e => [(declsE.xdecls, { env_with_wf with error := some (Imperative.EvalError.Misc f!"{e}")})]
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }

      go rest declsE


--------------------------------------------------------------------

end Program
end Core

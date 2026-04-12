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

    | .proc proc md =>
      let (p, E) := Procedure.eval declsE.env proc
      let declsE := { declsE with xdecls := declsE.xdecls ++ [.proc p md], env := E }
      go rest declsE

    | .func func _ =>
      match declsE.env.addFactoryFunc func with
      | .error e => [(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})]
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }
      go rest declsE

    | .recFuncBlock funcs _ =>
      match validateCasesTypes funcs declsE.env.datatypes with
      | .error e => [(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})]
      | .ok () =>
      let result := funcs.foldlM (fun env func => env.addFactoryFunc func) declsE.env
      match result with
      | .error e => [(declsE.xdecls, { declsE.env with error := some (Imperative.EvalError.Misc f!"{e}")})]
      | .ok new_env =>
        let declsE := { declsE with env := new_env,
                                    xdecls := declsE.xdecls ++ [decl] }
        go rest declsE


--------------------------------------------------------------------

end -- public section

end Program

/-! ## Concrete Interpretation Setup -/

public section

/-- Set up an environment for concrete interpretation of a type-checked program.
    Sets `evalMode := .concrete` and processes all declarations (globals,
    functions, axioms) without running procedure bodies. -/
def initConcreteEnv (prog : Program) (fuel : Nat := defaultFuel) :
    Except Strata.DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let datatypes := prog.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← Lambda.LState.init.addFactory factory
  let E := { Env.init with exprEnv := σ, program := prog, evalMode := .concrete }
  let E := { E with exprEnv := { E.exprEnv with config := { E.exprEnv.config with fuel := fuel } } }
  let E ← E.addDatatypes datatypes
  -- Process declarations: globals, functions, axioms (but not procedure bodies)
  let E := { E with pathConditions := E.pathConditions.push [] }
  let E := prog.decls.foldl (fun E decl =>
    match E.error with
    | some _ => E
    | none =>
    match decl with
    | .var name ty init _md =>
      let ssEs := Statement.eval E [] [(.init name ty init #[])]
      match ssEs with
      | (_, E') :: _ => E'
      | [] => E
    | .type _ _ => E
    | .ax a _ =>
      { E with pathConditions := E.pathConditions.insert (toString a.name) a.e }
    | .distinct _ es _ =>
      { E with distinct := es :: E.distinct }
    | .func f _md =>
      match E.addFactoryFunc f with
      | .ok E' => E'
      | .error _ => E
    | .recFuncBlock fs _md =>
      fs.foldl (fun E f =>
        match E.addFactoryFunc f with
        | .ok E' => E'
        | .error _ => E) E
    | .proc _ _ => E
  ) E
  return E

end -- public section

end Core

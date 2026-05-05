/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.ProcedureEval
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementEval
public import Strata.Languages.Core.StatementSemantics
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Imperative.StmtEval
public import Strata.DL.Imperative.CmdEval

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)

namespace Program
open Lambda LExpr
open Lambda.LTy Lambda.LExpr Statement Procedure Program
open Strata (DiagnosticModel DiagnosticType FileRange)

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
                      declsE.pathConditions.addEntry (.assumption (toString a.name) a.e) }
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

def Decl.run (d : Decl) (E : Env) : Except DiagnosticModel Env :=
  match d with
  | .type t _md =>
    match t with
    | .data d => E.addMutualDatatype d
    | _ => .ok E
  | .func f _md =>
    E.addFactoryFunc f
  | .recFuncBlock fs _md =>
    fs.foldlM (fun E f => E.addFactoryFunc f) E
  | .ax a _md =>
    -- Not strictly necessary for concrete execution
    .ok { E with pathConditions := E.pathConditions.addInNewest [.assumption (toString a.name) a.e] }
  | _ => .ok E

/--
Initialize an environment and evaluate all of the declarations
from a type-checked program.
-/
def run (prog : Program) : Except DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let σ ← Lambda.LState.init.addFactory factory
  let E: Env := { Env.init with exprEnv := σ, program := prog }
  prog.decls.foldlM (fun E d => Decl.run d E) E

end -- public section

end Program
end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env
public import Strata.Util.Statistics
import Strata.Languages.Core.ProcedureEval
import Strata.Languages.Core.StatementEval

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
      if declsE.pathConditions.scopes.length != 1 then
        .error (Strata.DiagnosticModel.fromMessage
            "Internal error: path condition stack misaligned when adding axiom")
      else
        let declsE := { declsE with pathConditions :=
                      declsE.pathConditions.prepend (.assumption (toString a.name) a.e) }
        go rest declsE stats

    | .distinct _ es _ =>
        let declsE := { declsE with distinct := es :: declsE.distinct }
      go rest declsE stats

    | .proc proc _md =>
      let (E, procStats) := Procedure.eval declsE proc
      -- Reset path conditions to the pre-procedure state so a procedure's
      -- assumptions don't leak into later ones. Likewise reset `Env.error`: it
      -- is a within-procedure short-circuit flag, and leaking it would make the
      -- next procedure no-op its body and silently drop its obligations (an
      -- unsound vacuous pass). Deferred obligations and fresh names carry forward.
      let E := { E with pathConditions := declsE.pathConditions,
                        error := declsE.error }
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

/--
Run a single procedure as an entry point in the concrete interpreter.

Generates fresh variables for the procedure's outputs, binds them, then invokes
the procedure with no arguments under the given `fuel` bound, returning the
resulting environment. Inspect `.error` on the result to detect a runtime
assertion failure (`AssertFail`), fuel exhaustion (`OutOfFuel`), or another
evaluation error (`Misc`).

`E` is expected to be a freshly-initialized environment, e.g. the result of
`Program.run` on the type-checked program containing `proc`.

Note: this is the *concrete interpreter's* entry-point runner, driven by the
producer-set `interpretEntry` marker. It is unrelated to `Core.EntryPoint`,
which is the verifier's target selector (`.main | .roots | .all`) used to
decide which procedures the SMT verifier targets.
-/
def runEntry (E : Env) (proc : Procedure) (fuel : Nat) : Env :=
  let outputNames := proc.header.outputs.keys.map (·.name)
  let (lhs, exprEnv) := Env.genVars outputNames E.exprEnv
  let E := { E with exprEnv }
  Statement.Command.runCall lhs proc.header.name.name [] fuel E

/--
All procedures the producer marked as concrete-interpretation entry points,
via the `interpretEntry` metadata on their declaration (see
`Imperative.MetaData.interpretEntry`). The marker is set on a Laurel procedure's
`entry` clause and carried into Core metadata by the Laurel→Core translator.

Distinct from `Core.EntryPoint` (verifier target selector); this returns the
procedures the *concrete interpreter* should enter.
-/
def entryProcedures (prog : Program) : List Procedure :=
  prog.decls.filterMap fun d =>
    match d.getProc? with
    | some p =>
      match d.metadata.findElem Imperative.MetaData.interpretEntry with
      | some { value := .switch true, .. } => some p
      | _ => none
    | none => none

end -- public section

end Program
end Core

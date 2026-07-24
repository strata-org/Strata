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
      let new_env ← declsE.addFactoryFunc func.toLFunc
      go rest new_env stats

    | .recFuncBlock funcs _ => do
      validateCasesTypes funcs declsE.datatypes
      let declsE ← funcs.foldlM (fun env func => env.addFactoryFunc func.toLFunc) declsE
      go rest declsE stats


--------------------------------------------------------------------

def Decl.run (d : Decl) (E : Env) : Except DiagnosticModel Env :=
  match d with
  | .type t _md =>
    match t with
    | .data d => E.addMutualDatatype d
    | _ => .ok E
  | .func f _md =>
    E.addFactoryFunc f.toLFunc
  | .recFuncBlock fs _md =>
    fs.foldlM (fun E f => E.addFactoryFunc f.toLFunc) E
  | .ax a _md =>
    -- Not strictly necessary for concrete execution
    .ok { E with pathConditions := E.pathConditions.addInNewest [.assumption (toString a.name) a.e] }
  | _ => .ok E

/--
Initialize an environment and evaluate all of the declarations
from a type-checked program.

`moreFns` are extra factory functions (beyond the Core built-ins)
that are used for both the type-checker and evaluator. Callers of
run can register language-specific functions this way and have them
type-checked and evaluated just like Core's own built-ins.
-/
def run (prog : Program) (moreFns : Lambda.Factory CoreLParams := Lambda.Factory.default)
    : Except DiagnosticModel Env := do
  let factory ← Core.Factory.addFactory Lambda.Factory.default
  let factory ← factory.addFactory moreFns
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

/-- Build a map from assert labels to their source `FileRange` and *property
    summary*. The summary (e.g. "precondition", "postcondition") is what the
    verifier prefixes onto its "… does not hold" diagnostic, so a caller mapping
    an interpreter `AssertFail` back to source can reproduce the verifier's exact
    wording. Absent a summary the label maps to the default "assertion". -/
def collectAssertInfo (prog : Program) : Std.HashMap String (Strata.FileRange × String) := Id.run do
  let mut m : Std.HashMap String (Strata.FileRange × String) := {}
  for decl in prog.decls do
    if let some proc := decl.getProc? then
      if let .ok ss := proc.body.getStructured then
        for (label, md) in Core.Statement.Statements.collectAsserts ss do
          if let some fr := Imperative.getFileRange md then
            m := m.insert label (fr, md.getPropertySummary.getD "assertion")
  return m

/-- Build a map from assert labels to their source `FileRange`. Projection of
    `collectAssertInfo` that discards the property summary. -/
def collectAssertRanges (prog : Program) : Std.HashMap String Strata.FileRange :=
  (collectAssertInfo prog).fold (init := {}) fun m k (fr, _) => m.insert k fr

/-- Mark every bodied, non-recursive function in the program with
    `inlineIfAllCanonical`, so the concrete interpreter unfolds it once all of
    its arguments are concrete values. Verification keeps these functions
    uninterpreted and discharges them via SMT, but concrete execution needs the
    body inlined to reduce e.g. `int32$constraint(5)` to a boolean. (Recursive
    functions are left alone to avoid non-termination; the fuel bound also
    protects against runaway unfolding.)

    Shared by the `laurelInterpret` CLI command and the Laurel E2E execute tests. -/
def inlineBodiedFunctions (prog : Program) : Program :=
  let addInline (f : Core.Function) : Core.Function :=
    if f.body.isSome && !f.isRecursive
        && !f.attr.contains .inlineIfAllCanonical && !f.attr.contains .inline
    then { f with attr := f.attr.push .inlineIfAllCanonical }
    else f
  { prog with decls := prog.decls.map fun d =>
      match d with
      | .func f md => .func (addInline f) md
      | .recFuncBlock fs md => .recFuncBlock (fs.map addInline) md
      | other => other }

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

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

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
open Strata (Message MessageKind FileRange)

public section


def eval (E : Env) : Except Strata.Message (List Env × Statistics) :=
  -- Push a path condition scope to store axioms
  let E := { E with pathConditions := E.pathConditions.push [] }
  go E.program.decls E ({} : Statistics)
  where go (decls : Decls) (declsE : Env) (stats : Statistics)
      : Except Strata.Message (List Env × Statistics) :=
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
        .error (Strata.Message.fromString
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
      if E.error.isSome && declsE.error.isNone then
        -- Resetting the error and carrying on would no-op the remaining
        -- procedures and drop their obligations, reporting success on a program
        -- that was never evaluated.
        .error (Strata.Message.fromFormat
          f!"procedure '{proc.header.name}': \
             {match E.error with | some e => Std.format e | none => ""}")
      else
      -- Reset path conditions to the pre-procedure state so a procedure's
      -- assumptions don't leak into later ones. Likewise reset `Env.error`: it
      -- is a within-procedure short-circuit flag when it was already set on
      -- entry. Deferred obligations and fresh names carry forward.
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

def Decl.run (d : Decl) (E : Env) : Except Message Env :=
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
    : Except Message Env := do
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

/--
Everything an entry-point interpretation run observed that a caller may want to
report. Split by how much the interpreter knows about each failure, because the
callers differ in how they surface them: the CLI prints all three and reserves
the exit code for `errors`, while the test harness turns `diagnostics` into
expected output and throws on the other two.
-/
structure InterpretOutcome where
  /-- Assertion failures that mapped back to a source range, deduplicated,
      in discovery order. -/
  diagnostics : Array Strata.Message
  /-- Assertion failures whose label carried no source range, as
      `(procedure name, assert label)`. -/
  unmapped : Array (String × String)
  /-- Non-assertion evaluation errors (out of fuel, `Misc`, …), paired with the
      entry procedure that raised them. -/
  errors : Array (String × Imperative.EvalError Core.Expression)

/--
Concretely interpret `entries` — the entry points of the type-checked program
`prog` — and collect every failure they produce.

This is the single implementation of the concrete-interpretation path, shared by
the `laurelInterpret` CLI command and the Laurel execute tests, so the two
cannot drift on the evaluator configuration below.

Two `Env` flags define what "interpret" means here:

* `collectAllAssertFailures` — an assertion failure records itself and execution
  continues, so one run reports every independent violation instead of halting
  on the first. Assertions don't mutate the store, so the rest of the procedure
  still executes faithfully.
* `ignoreAssumes` — `assume`s are no-ops, matching Laurel's language-level
  semantics: an assume constrains the verifier's symbolic state but has no
  runtime effect. Callers reach here having translated with
  `analysisMode := .Execute`, which leaves contract-inserted assumes (e.g. a
  callee's `requires`, assumed in its own body) in place; enforcing them would
  halt this assertion-oracle run on a spec the interpreter cannot decide
  concretely, rather than on the assertion under test.

Bodied functions are inlined first (see `inlineBodiedFunctions`) so concrete
execution can reduce them. Failures are mapped back to source through the
metadata each failure carries, reproducing the verifier's wording for the same
property.
-/
def interpretEntries (prog : Program) (entries : List Procedure) (fuel : Nat)
    : Except Message InterpretOutcome := do
  let prog := inlineBodiedFunctions prog
  let E ← prog.run
  let E := { E with collectAllAssertFailures := true, ignoreAssumes := true }
  let mut diagnostics : Array Strata.Message := #[]
  let mut seen : Std.HashSet Strata.Message := {}
  let mut unmapped : Array (String × String) := #[]
  let mut errors : Array (String × Imperative.EvalError Core.Expression) := #[]
  for p in entries do
    let procName := p.header.name.name
    -- Each entry runs from the same freshly-initialized environment, so entries
    -- neither observe nor clobber each other's state.
    let resultEnv := runEntry E p fuel
    for (label, _e, md) in resultEnv.assertFailures.reverse do
      match Imperative.getFileRange md with
      | some fr =>
        let summary := md.getPropertySummary.getD "assertion"
        let dm := Strata.Message.withRange fr s!"{summary} does not hold"
        unless seen.contains dm do
          diagnostics := diagnostics.push dm
          seen := seen.insert dm
      | none => unmapped := unmapped.push (procName, label)
    if let some e := resultEnv.error then
      errors := errors.push (procName, e)
  return { diagnostics, unmapped, errors }

end -- public section

end Program
end Core

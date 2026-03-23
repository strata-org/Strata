/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter

/-!
# Concrete Program Evaluator for Laurel

Bridges the gap between `interpStmt` (which operates on individual statements)
and `Laurel.Program` (which is the top-level program structure). Given a program,
builds the required environments and calls `interpStmt` on the `main` procedure's body.

See `LaurelSemantics.lean` for the module layering rationale.
-/

namespace Strata.Laurel

/-! ## ToString for LaurelValue -/

instance : ToString LaurelValue where
  toString
    | .vInt i => toString i
    | .vBool b => toString b
    | .vString s => s!"\"{s}\""
    | .vVoid => "void"
    | .vRef n => s!"ref({n})"

/-! ## Building ProcEnv -/

/-- Build a `ProcEnv` from a list of procedures. Earlier entries shadow later ones. -/
def listToProcEnv (procs : List Procedure) : ProcEnv :=
  fun name => procs.find? (fun p => p.name == name)

/-- Build a `ProcEnv` from a `Program`, including static procedures and
    instance procedures keyed as `"TypeName.methodName"`. -/
def buildProcEnv (prog : Program) : ProcEnv :=
  let statics := prog.staticProcedures
  let instanceProcs := prog.types.foldl (fun acc td =>
    match td with
    | .Composite ct =>
      ct.instanceProcedures.map (fun p =>
        { p with name := mkId (ct.name.text ++ "." ++ p.name.text) }) ++ acc
    | _ => acc) []
  listToProcEnv (instanceProcs ++ statics)

/-! ## Building Initial Store -/

/-- Build an initial store from static fields, all initialized to `vVoid`. -/
def buildInitialStore (prog : Program) : LaurelStore :=
  let fields := prog.staticFields
  fields.foldl (fun acc f => fun x => if x == f.name.text then some .vVoid else acc x)
    (fun _ => none)

/-! ## Default Expression Evaluator -/

/-- A `LaurelEval` that handles identifiers and literals.
    Specification constructs return `none`. -/
def defaultEval : LaurelEval := fun st expr =>
  match expr with
  | .Identifier name => st name.text
  | .LiteralInt i => some (.vInt i)
  | .LiteralBool b => some (.vBool b)
  | .LiteralString s => some (.vString s)
  | _ => none

/-! ## Core Evaluation -/

/-- Evaluate a `Program` by finding and running its `main` procedure.
    Returns `none` if there is no `main` or it has no body. -/
def evalProgram (prog : Program) (fuel : Nat := 10000)
    : Option (Outcome × LaurelStore × LaurelHeap) :=
  let procEnv := buildProcEnv prog
  match prog.staticProcedures.find? (fun p => p.name.text == "main") with
  | none => none
  | some mainProc =>
    match getBody mainProc with
    | none => none
    | some body =>
      let initStore := buildInitialStore prog
      let initHeap : LaurelHeap := fun _ => none
      interpStmt defaultEval procEnv fuel initHeap initStore body.val

/-! ## User-Friendly Result Type -/

inductive EvalResult where
  | success (value : LaurelValue) (store : LaurelStore) (heap : LaurelHeap)
  | returned (value : Option LaurelValue) (store : LaurelStore) (heap : LaurelHeap)
  | noMain
  | noBody
  | stuck (msg : String)
  | fuelExhausted
  deriving Inhabited

instance : ToString EvalResult where
  toString
    | .success v _ _ => s!"success: {v}"
    | .returned (some v) _ _ => s!"returned: {v}"
    | .returned none _ _ => "returned: void"
    | .noMain => "error: no 'main' procedure found"
    | .noBody => "error: 'main' has no body"
    | .stuck msg => s!"stuck: {msg}"
    | .fuelExhausted => "error: fuel exhausted"

/-- Run a program and classify the result. Delegates to `evalProgram` for
    the core evaluation, preserving the `noMain` / `noBody` distinction. -/
def runProgram (prog : Program) (fuel : Nat := 10000) : EvalResult :=
  match prog.staticProcedures.find? (fun p => p.name.text == "main") with
  | none => .noMain
  | some mainProc =>
    match getBody mainProc with
    | none => .noBody
    | some _ =>
      match evalProgram prog fuel with
      | some (.normal v, st, hp) => .success v st hp
      | some (.ret rv, st, hp) => .returned rv st hp
      | some (.exit label, _, _) => .stuck s!"uncaught exit '{label}'"
      | none => .fuelExhausted

end Strata.Laurel

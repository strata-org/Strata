/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Translate
import Strata.DL.SMT.Term
import Strata.DL.SMT.TermType
import Strata.Languages.Core.Options
import Std.Data.HashMap

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Solver.lean)
This file defines a simple interface to an SMT solver running in a separate
process.

## String formatting

All `Term → SMT-LIB string` conversion lives in this module. The Encoder layer
works purely with `Term` values and delegates string rendering to the Solver via
`termToSMTString`, `typeToSMTString`, and the typed command API.
-/

namespace Strata.SMT

inductive Decision where
  | sat
  | unsat
  | unknown
deriving DecidableEq, Repr

/--
 A Solver is an interpreter for SMTLib scripts, which are passed to the solver
 via its `smtLibInput` stream. Solvers optionally have an `smtLibOutput` stream
 to which they print the results of executing the commands received on the input
 stream. We assume that both the input and output streams conform to the SMTLib
 standard: the inputs are SMTLib script commands encoded as s-expressions, and
 the outputs are the s-expressions whose shape is determined by the standard for
 each command. We don't have an error stream here, since we configure solvers to
 run in quiet mode and not print anything to the error stream.
-/
structure Solver where
  smtLibInput : IO.FS.Stream
  smtLibOutput : Option IO.FS.Stream

/-- State tracked by `SolverM`: caches `Term → SMT-LIB string` and
    `TermType → SMT-LIB string` conversions so that the same term/type is
    never converted twice. -/
structure SolverState where
  /-- Caches `Term → full SMT-LIB string` via `SMTDDM.termToString`. -/
  termStrings : Std.HashMap Term String := {}
  /-- Caches `TermType → full SMT-LIB string` via `SMTDDM.termTypeToString`. -/
  typeStrings : Std.HashMap TermType String := {}

def SolverState.init : SolverState := {}

abbrev SolverM (α) := StateT SolverState (ReaderT Solver IO) α

def SolverM.run (solver : Solver) (x : SolverM α) (state : SolverState := SolverState.init) : IO (α × SolverState) :=
  ReaderT.run (StateT.run x state) solver

/-- A typed SMT-LIB datatype constructor: name + typed fields. -/
structure SMTConstructor where
  name : String
  args : List (String × TermType)
deriving Repr, Inhabited

namespace Solver

/--
  Returns a Solver for the given path and arguments. This function expects
  `path` to point to an SMT solver executable, and `args` to specify valid
  arguments to that solver.
-/
def spawn (path : String) (args : Array String) : IO Solver := do
  try
    let proc ← IO.Process.spawn {
      stdin  := .piped
      stdout := .piped
      stderr := .piped
      cmd    := path
      args   := args
    }
    return ⟨IO.FS.Stream.ofHandle proc.stdin, IO.FS.Stream.ofHandle proc.stdout⟩
  catch e =>
    let suggestion := if path == defaultSolver || path.endsWith defaultSolver then s!" Ensure {defaultSolver} is on your PATH or use --solver to specify another SMT solver." else ""
    throw (IO.userError s!"could not execute external process '{path}'.{suggestion} Original error: {e}")

/--
  Returns an instance of the solver that is backed by the executable
  specified in the environment variable "SOLVER".
-/
def solver : IO Solver := do
  match (← IO.getEnv "SOLVER") with
  | .some path => spawn path ["--quiet", "--lang", "smt"].toArray
  | .none      => throw (IO.userError "SOLVER environment variable not defined.")

/--
  Returns a solver that writes all issued commands to the given file handle `h`.
  Commands that produce output, such as `checkSat`, write the command to `h` and
  return values that are sound according to the SMTLIb spec (but generally not
  useful). For example, `Solver.checkSat` returns `Decision.unknown`. This
  function expects `h` to be write-enabled.
-/
def fileWriter (h : IO.FS.Handle) : IO Solver :=
  return ⟨IO.FS.Stream.ofHandle h, .none⟩

/--
  Returns a solver that writes all issued commands to the given buffer `b`.
  Commands that produce output, such as `checkSat`, write the command to `b` and
  return values that are sound according to the SMTLIb spec (but generally not
  useful). For example, `Solver.checkSat` returns `Decision.unknown`.
-/
def bufferWriter (b : IO.Ref IO.FS.Stream.Buffer) : IO Solver :=
  return ⟨IO.FS.Stream.ofBuffer b, .none⟩

/-! ## Internal helpers -/

private def emitln (str : String) : SolverM Unit := do
  let solver ← read
  solver.smtLibInput.putStr s!"{str}\n"
  solver.smtLibInput.flush

/-- Convert a `Term` to its SMT-LIB string, using the `SolverState` cache. -/
def termToSMTString (t : Term) : SolverM String := do
  if let (.some s) := (← get).termStrings.get? t then return s
  match Strata.SMTDDM.termToString t with
  | .ok s =>
    modify fun st => { st with termStrings := st.termStrings.insert t s }
    return s
  | .error msg => panic! s!"Solver.termToSMTString failed: {msg}"

/-- Convert a `TermType` to its SMT-LIB string, using the `SolverState` cache. -/
def typeToSMTString (ty : TermType) : SolverM String := do
  if let (.some s) := (← get).typeStrings.get? ty then return s
  match Strata.SMTDDM.termTypeToString ty with
  | .ok s =>
    modify fun st => { st with typeStrings := st.typeStrings.insert ty s }
    return s
  | .error msg => panic! s!"Solver.typeToSMTString failed: {msg}"

/-! ## String-based commands (less critical, kept as-is) -/

def setLogic (logic : String) : SolverM Unit :=
  emitln s!"(set-logic {logic})"

def setOption (name value : String) : SolverM Unit :=
  emitln s!"(set-option :{name} {value})"

def setInfo (name value : String) : SolverM Unit :=
  emitln s!"(set-info :{name} {value})"

def comment (comment : String) : SolverM Unit :=
  let inline := comment.replace "\n" " "
  emitln s!"; {inline}"

def getValue (ids : List String) : SolverM Unit :=
  let ids := Std.Format.joinSep ids " "
  emitln s!"(get-value ({ids}))"

def declareSort (id : String) (arity : Nat) : SolverM Unit :=
  emitln s!"(declare-sort {id} {arity})"

/-- Convert a single constructor to its SMT-LIB string representation. -/
private def constructorToSMTString (c : SMTConstructor) : SolverM String := do
  if c.args.isEmpty then return s!"({c.name})"
  else
    let fieldStrs ← c.args.mapM fun (name, ty) => do
      let tyStr ← typeToSMTString ty
      return s!"({name} {tyStr})"
    return s!"({c.name} {String.intercalate " " fieldStrs})"

def declareDatatype (id : String) (params : List String) (constructors : List SMTConstructor) : SolverM Unit := do
  let cStrs ← constructors.mapM constructorToSMTString
  let cInline := "\n  " ++ String.intercalate "\n  " cStrs
  let pInline := String.intercalate " " params
  if params.isEmpty
  then emitln s!"(declare-datatype {id} ({cInline}))"
  else emitln s!"(declare-datatype {id} (par ({pInline}) ({cInline})))"

/-- Declare multiple mutually recursive datatypes. Each element is (name, params, constructors). -/
def declareDatatypes (dts : List (String × List String × List SMTConstructor)) : SolverM Unit := do
  if dts.isEmpty then return
  let sortDecls := dts.map fun (name, params, _) => s!"({name} {params.length})"
  let sortDeclStr := String.intercalate " " sortDecls
  let bodies ← dts.mapM fun (_, params, constrs) => do
    let cStrs ← constrs.mapM constructorToSMTString
    let cInline := String.intercalate " " cStrs
    if params.isEmpty then return s!"({cInline})"
    else
      let pInline := String.intercalate " " params
      return s!"(par ({pInline}) ({cInline}))"
  let bodyStr := String.intercalate "\n  " bodies
  emitln s!"(declare-datatypes ({sortDeclStr})\n  ({bodyStr}))"

/-! ## Typed commands -/

/-- Assert a `Term` (must be Bool-typed). Converts via the cached `termToSMTString`. -/
def assert (t : Term) : SolverM Unit := do
  let s ← termToSMTString t
  emitln s!"(assert {s})"

/-- Assert a raw SMT-LIB identifier string (e.g. an abbreviated name like `"t0"`).
    Used by the Encoder after ANF decomposition, where the term has already been
    broken into `define-fun` definitions and only the short name needs asserting. -/
def assertId (id : String) : SolverM Unit :=
  emitln s!"(assert {id})"

/-- Declare a constant with a typed `TermType`. -/
def declareConst (id : String) (ty : TermType) : SolverM Unit := do
  let tyStr ← typeToSMTString ty
  emitln s!"(declare-const {id} {tyStr})"

/-- Declare a function with typed argument and return types. -/
def declareFun (id : String) (argTys : List TermType) (retTy : TermType) : SolverM Unit := do
  let retStr ← typeToSMTString retTy
  if argTys.isEmpty then
    emitln s!"(declare-const {id} {retStr})"
  else
    let argStrs ← argTys.mapM typeToSMTString
    let inline := String.intercalate " " argStrs
    emitln s!"(declare-fun {id} ({inline}) {retStr})"

/-- Define a function with typed return type and a raw SMT-LIB string body.
    This is an internal helper; prefer `defineFunTerm` for Term-based bodies. -/
def defineFun (id : String) (args : List (String × TermType)) (retTy : TermType)
    (body : String) : SolverM Unit := do
  let typedArgs ← args.mapM fun (name, ty) => do
    let tyStr ← typeToSMTString ty
    return s!"({name} {tyStr})"
  let inline := String.intercalate " " typedArgs
  let retStr ← typeToSMTString retTy
  emitln s!"(define-fun {id} ({inline}) {retStr} {body})"

/-- Define a function where the body is given as a `Term` (converted via cache). -/
def defineFunTerm (id : String) (args : List (String × TermType)) (retTy : TermType)
    (body : Term) : SolverM Unit := do
  let bodyStr ← termToSMTString body
  defineFun id args retTy bodyStr

/-! ## Solver control -/

private def readlnD (dflt : String) : SolverM String := do
  match (← read).smtLibOutput with
  | .some stdout => stdout.getLine
  | .none        => pure dflt

def checkSat (vars : List String) : SolverM Decision := do
  emitln "(check-sat)"
  let result := (← readlnD "unknown").trimAscii.toString
  match result with
  | "sat"     =>
    if !vars.isEmpty then
      getValue vars
    return Decision.sat
  | "unsat"   => return Decision.unsat
  | "unknown" =>
    if !vars.isEmpty then
      getValue vars
    return Decision.unknown
  | other     => throw (IO.userError s!"Unrecognized solver output: {other}")

def reset : SolverM Unit :=
  emitln "(reset)"

def exit : SolverM Unit :=
  emitln "(exit)"

end Solver

end Strata.SMT

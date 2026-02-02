/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-!
Based on Cedar's Term language.
(https://github.com/cedar-policy/cedar-spec/blob/main/cedar-lean/Cedar/SymCC/Solver.lean)
This file defines a simple interface to an SMT solver running in a separate
process. Callers communicate with the solver by issuing commands with
s-expressions encoded as strings. The interface is based on
[lean-smt](https://github.com/ufmg-smite/lean-smt/).
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

abbrev SolverM (α) := ReaderT Solver IO α

def SolverM.run (solver : Solver) (x : SolverM α) : IO α := ReaderT.run x solver

namespace Solver

/--
  Returns a Solver for the given path and arguments. This function expects
  `path` to point to an SMT solver executable, and `args` to specify valid
  arguments to that solver.
-/
def spawn (path : String) (args : Array String) : IO Solver := do
  let proc ← IO.Process.spawn {
    stdin  := .piped
    stdout := .piped
    stderr := .piped
    cmd    := path
    args   := args
  }
  return ⟨IO.FS.Stream.ofHandle proc.stdin, IO.FS.Stream.ofHandle proc.stdout⟩

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

private def emitln (str : String) : SolverM Unit := do
  -- dbg_trace "{str}" -- uncomment to see input sent to the solver
  let solver ← read
  solver.smtLibInput.putStr s!"{str}\n"
  solver.smtLibInput.flush

def setLogic (logic : String) : SolverM Unit :=
  emitln s!"(set-logic {logic})"

def setOption (name value : String) : SolverM Unit :=
  emitln s!"(set-option :{name} {value})"

def comment (comment : String) : SolverM Unit :=
  let inline := comment.replace "\n" " "
  emitln s!"; {inline}"

def assert (expr : String) : SolverM Unit :=
  emitln s!"(assert {expr})"

def getValue (ids : List String) : SolverM Unit :=
  let ids := Std.Format.joinSep ids " "
  emitln s!"(get-value ({ids}))"

def defineFun (id : String) (args : List (String × String)) (type expr : String) : SolverM Unit :=
  let inline := String.intercalate " " (args.map (λ ⟨pᵢ, pₜ⟩ => s!"({pᵢ} {pₜ})"))
  emitln s!"(define-fun {id} ({inline}) {type} {expr})"

def declareConst (id type : String) : SolverM Unit :=
  emitln s!"(declare-const {id} {type})"

def declareSort (id : String) (arity : Nat) : SolverM Unit :=
  emitln s!"(declare-sort {id} {arity})"

def declareFun (id : String) (args : List String) (type : String) : SolverM Unit :=
  if args.isEmpty then
    declareConst id type
  else
    let inline := String.intercalate " " args
    emitln s!"(declare-fun {id} ({inline}) {type})"

def declareDatatype (id : String) (params : List String) (constructors : List String) : SolverM Unit :=
  let cInline := "\n  " ++ String.intercalate "\n  " constructors
  let pInline := String.intercalate " " params
  if params.isEmpty
  then emitln s!"(declare-datatype {id} ({cInline}))"
  else emitln s!"(declare-datatype {id} (par ({pInline}) ({cInline})))"

/-- Declare multiple mutually recursive datatypes. Each element is (name, params, constructors). -/
def declareDatatypes (dts : List (String × List String × List String)) : SolverM Unit := do
  if dts.isEmpty then return
  let sortDecls := dts.map fun (name, params, _) => s!"({name} {params.length})"
  let sortDeclStr := String.intercalate " " sortDecls
  let bodies := dts.map fun (_, params, constrs) =>
    let cInline := String.intercalate " " constrs
    if params.isEmpty then s!"({cInline})"
    else
      let pInline := String.intercalate " " params
      s!"(par ({pInline}) ({cInline}))"
  let bodyStr := String.intercalate "\n  " bodies
  emitln s!"(declare-datatypes ({sortDeclStr})\n  ({bodyStr}))"

private def readlnD (dflt : String) : SolverM String := do
  match (← read).smtLibOutput with
  | .some stdout => stdout.getLine
  | .none        => pure dflt

def checkSat (vars : List String) : SolverM Decision := do
  emitln "(check-sat)"
  let result := (← readlnD "unknown").trim
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

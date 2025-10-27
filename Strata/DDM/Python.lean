import Strata.DDM.TaggedRegions
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.HasInputContext
import Strata.DDM.Integration.Lean.HashCommands
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.Integration.Lean.Gen

open Lean
open Lean (Expr)
open Lean.Elab (throwIllFormedSyntax throwUnsupportedSyntax)
open Elab.Command (CommandElab CommandElabM elabCommand)

open Lean.Elab.Term (TermElab TermElabM)

open Strata (dialectExt)
open Strata.Elab (elabProgram)
open Strata.Integration.Lean

open System (FilePath)

namespace Strata

namespace PythonSSA

#load_dialect "../../Tools/Python/test_results/dialects/PythonSSA.dialect.st.ion"

set_option trace.Strata.generator true

#strata_gen PythonSSA

#eval 1

#print Ann
#print Command

def ofProgram (p : Program) : Array (Command SourceRange) :=
  match p.commands.mapM Command.ofAst with
  | .error msg => panic! msg
  | .ok cmds => cmds

/--
Use mise to find which Python to run
-/
def misePythonPath : IO (Option String) := do
  let out ← IO.Process.output { cmd := "mise", args := #["which", "python"] }
  if out.exitCode != 0 then
    return none
  return some out.stdout.trim

def runPyToStrata (pythonPath : String) (dialect : String) (pyfile : String) (outfile : String) (cwd : Option FilePath) : IO Unit := do
  let args : IO.Process.SpawnArgs := {
      cmd := pythonPath
      args := #["-m", "strata.gen", "py_to_strata", dialect, pyfile, outfile ]
      cwd := cwd
      env := #[]
      inheritEnv := false
    }
  let res ← IO.Process.output args none
  if res.exitCode != 0 then
    throw <| IO.userError s!"py_to_strata failed:\n  {res.stderr}"

syntax (name := loadPythonSSACommand) "#load_PythonSSA" str : term

def readPythonSSA (loaded : Elab.LoadedDialects) (cwd : FilePath) (pythonPath : String) (programPath : String) : IO Program := do
  let name := "PythonSSA"
  let .isTrue mem := inferInstanceAs (Decidable (name ∈ loaded.dialects))
    | throw <| IO.userError s!"{name} unloaded."
  let bytes ← IO.FS.withTempFile fun h outpath => do
      runPyToStrata (cwd := some cwd) pythonPath name programPath outpath.toString
      h.readBinToEnd
  let dm := loaded.dialects.importedDialects name mem
  match Program.fromIon dm name bytes with
  | .error msg =>
    throw <| IO.userError msg
  | .ok p =>
    return p

@[term_elab loadPythonSSACommand]
def loadPythonSSAImpl: TermElab := fun (stx : Syntax) _ => do
  match stx with
  | `(#load_PythonSSA $pathStx) =>
    let programPath : String := pathStx.getString
    let cwd ← getLeanCwd
    let some pythonPath ← misePythonPath
      | throwError "Could not run mise to find python.  Check that it is installed."
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    match ← readPythonSSA loaded cwd pythonPath programPath |>.toBaseIO with
    | .error emsg => throwError emsg.toString
    | .ok p => return toExpr p
  | _ =>
    throwUnsupportedSyntax

def benchmark : Strata.Program := #load_PythonSSA "../../Tools/Python/benchmarks/ErgoPythonBenchmarks/botomoog-bm-simple/simple1_btg.py"

#eval IO.print benchmark

def gen_benchmark := ofProgram benchmark

#guard gen_benchmark.size == 1


end PythonSSA

end Strata

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

#load_dialect "../../../../Tools/Python/test_results/dialects/PythonSSA.dialect.st.ion"

set_option trace.Strata.generator true

#strata_gen PythonSSA

#print Command.ofAst

def ofProgram (p : Program) : Array (Command SourceRange) :=
  match p.commands.mapM Command.ofAst with
  | .error msg => panic! msg
  | .ok cmds => cmds

def runPyToStrata (pyfile : String) (outfile : String) (cwd : Option FilePath) : IO Unit := do
  let args : IO.Process.SpawnArgs := {
      cmd := "/Users/joehx/.local/share/mise/installs/python/latest/bin/python"
      args := #["-m", "strata.gen", "py_to_strata", "PythonSSA", pyfile, outfile ]
      cwd := cwd
      env := #[]
      inheritEnv := false
    }
  let res ← IO.Process.output args none
  if res.exitCode != 0 then
    throw <| IO.userError s!"py_to_strata failed:\n  {res.stderr}"

syntax (name := loadPythonSSACommand) "#load_PythonSSA" str : term

@[term_elab loadPythonSSACommand]
def loadPythonSSAImpl: TermElab := fun (stx : Syntax) _ => do
  match stx with
  | `(#load_PythonSSA $pathStx) =>
    let programPath : FilePath := pathStx.getString
    let cwd ← getLeanCwd
    let absPath := pathAbsoluteRelativeTo cwd programPath
    if !(←absPath.pathExists) then
      throwError "Could not find file {programPath}"
    let bytes ←
      IO.FS.withTempFile fun h outpath => do
        runPyToStrata (cwd := some cwd) absPath.toString outpath.toString
        h.readBinToEnd
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let name := "PythonSSA"
    let .isTrue mem := inferInstanceAs (Decidable (name ∈ loaded.dialects))
      | throwError s!"{name} unloaded."
    let dm := loaded.dialects.importedDialects name mem
    match Program.fromIon dm name bytes with
    | .error msg =>
      throwError msg
    | .ok p =>
      let e := toExpr p
      return e
  | _ =>
    throwUnsupportedSyntax

def foo := #load_PythonSSA "../../../../Tools/Python/benchmarks/ErgoPythonBenchmarks/botomoog-bm-simple/simple1_btg.py"

#print foo
def bar := ofProgram foo

#print Command.mk_function
--def match : Command


#eval IO.print foo
end PythonSSA

end Strata

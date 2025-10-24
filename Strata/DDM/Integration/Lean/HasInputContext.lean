import Lean.Elab.Command
import Lean.Elab.Term

open Lean.Parser (InputContext)
open System (FilePath)
open Lean.Core (CoreM)

open Lean.Elab.Command (CommandElab CommandElabM elabCommand)

namespace Strata.Integration.Lean

class HasInputContext (m : Type → Type _) [Functor m] where
  /-- Return the input context for the underlying `.lean` file being processed. -/
  getInputContext : m InputContext
  /-- Return the filename for the underlying `.lean` file. -/
  getFileName : m FilePath :=
    (fun ctx => FilePath.mk ctx.fileName) <$> getInputContext

export HasInputContext (getInputContext)

instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }
  getFileName := return (← read).fileName

instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }
  getFileName := return (← read).fileName

instance : HasInputContext Lean.Elab.TermElabM where
  getInputContext := (HasInputContext.getInputContext : CoreM _)
  getFileName := (HasInputContext.getFileName : CoreM _)

/--
Get the directory for the `.lean`file being processed.
-/
def getLeanCwd {m} [Monad m] [HasInputContext m] [Lean.MonadError m] : m FilePath := do
  let leanPath ← HasInputContext.getFileName
  let .some leanDir := leanPath.parent
    | throwError "Current file {leanPath} does not have a parent."
  return leanDir

def pathAbsoluteRelativeTo (cwd : FilePath) (path : FilePath) : FilePath :=
  if path.isAbsolute then
    path
  else
    cwd / path


def resolveLeanRelPath {m} [Monad m] [HasInputContext m] [Lean.MonadError m] (path : FilePath) : m FilePath := do
  return pathAbsoluteRelativeTo (← getLeanCwd) path

end Strata.Integration.Lean

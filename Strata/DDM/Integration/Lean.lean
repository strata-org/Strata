/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean.Gen
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions

open Lean
open Elab (throwIllFormedSyntax throwUnsupportedSyntax)
open Elab.Command (CommandElab CommandElabM elabCommand)
open Elab.Term (TermElab)
open Parser (InputContext TokenTable)
open System (FilePath)

namespace Strata

class HasInputContext (m : Type → Type _) [Functor m] where
  getInputContext : m InputContext
  getFileName : m FilePath :=
    (fun ctx => FilePath.mk ctx.fileName) <$> getInputContext

export HasInputContext (getInputContext)

instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      input    := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }
  getFileName := return (← read).fileName

instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      input    := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }
  getFileName := return (← read).fileName

declare_tagged_region command strataDialectCommand "#dialect" "#end"

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
  let scope ← getCurrNamespace
  let dialectRelName := Lean.Name.anonymous |>.str d.name
  let dialectFullName := scope ++ dialectRelName
  let env ← getEnv
  if env.contains dialectFullName then
    throwError "Cannot define {dialectRelName}: {dialectFullName} already exists."
  let dialectIdent := Lean.mkScopedIdent scope dialectRelName
  let cmd ← `(command| def $dialectIdent := $(quote d))
  tryCatch (elabCommand cmd) fun _ =>
    panic! "Elab command failed: {e}"
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d (isNew := true))

@[command_elab strataDialectCommand]
def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← getInputContext
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let (_, d, s) ← Strata.Elab.elabDialect {} loaded inputCtx p e
  if !s.errors.isEmpty then
    for e in s.errors do
      logMessage e
    return
  -- Add dialect to command environment
  declareDialect d

declare_tagged_region term strataProgram "#strata" "#end"

 @[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (getInputContext : CoreM _)
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram loaded leanEnv inputCtx p e with
  | .ok pgm =>
    return toExpr pgm
  | .error errors =>
    for e in errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Program) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

def resolveLeanRelPath {m} [Monad m] [HasInputContext m] [MonadError m] (path : FilePath) : m FilePath := do
  if path.isAbsolute then
    -- TODO: Add warning about absolute paths
    pure path
  else
    let leanPath ← HasInputContext.getFileName
    let .some leanDir := leanPath.parent
      | throwError "Current file {leanPath} does not have a parent."
    pure <| leanDir / path

@[command_elab loadDialectCommand]
def loadDialectImpl: CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (←absPath.pathExists) then
      throwError "Could not find file {dialectPath}"
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let (_, r) ← Elab.loadDialectFromPath {} loaded #[]
                        (path := dialectPath) (actualPath := absPath) (expected := .none)
    -- Add dialect to command environment
    match r with
    | .ok d =>
        declareDialect d
    | .error errorMessages =>
      assert! errorMessages.size > 0
      throwError (← Elab.mkErrorReport errorMessages)
  | _ =>
    throwUnsupportedSyntax

end Strata

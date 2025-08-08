/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.Gen
import Strata.DDM.Integration.Lean.Quote
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions
import Strata.DDM.Util.Lean

open Lean
open Elab.Command (CommandElab CommandElabM elabCommand)
open Elab.Term (TermElab)
open Parser (InputContext TokenTable)

namespace Strata

class HasInputContext (m : Type → Type _) where
  getInputContext : m InputContext

export HasInputContext (getInputContext)

instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      input    := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }

instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      input    := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap  := ctx.fileMap
    }

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let emptyLeanEnv ← mkEmptyEnvironment 0
  let inputCtx ← getInputContext
  let dialects := (dialectExt.getState (←Lean.getEnv)).loaded
  let loadFn (dialect : String) := pure (Except.error s!"Unknown dialect {dialect}.")
  let (d, s, _) ← Elab.elabDialect emptyLeanEnv loadFn dialects inputCtx p e
  if !s.errors.isEmpty then
    for (stx, e) in s.errors do
      logMessage e
    return
  -- Add dialect to command
  let cmd ← `(command| def $(Lean.mkLocalDeclId d.name) := $(quote d))
  tryCatch (elabCommand cmd) fun e =>
    panic! "Elab command failed: {e}"
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d (isNew := true))

declare_tagged_region term strataProgram "#strata" "#end"

 @[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (getInputContext : CoreM _)
  let loader := (dialectExt.getState (←Lean.getEnv)).loaded
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram loader leanEnv inputCtx p e with
  | .ok pgm =>
    return toExpr pgm
  | .error errors =>
    for (stx, e) in errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Program) (toExpr true)

end Strata

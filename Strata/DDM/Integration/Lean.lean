/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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

declare_tagged_region term strataProgram "#strata" "#end"

 @[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let emptyEnv ← mkEmptyEnvironment 0
  let inputCtx ← (getInputContext : CoreM _)
  let loader := (dialectExt.getState (←Lean.getEnv)).loader
  let ds := Elab.elabProgram emptyEnv loader inputCtx p e
  if ds.errors.isEmpty then
    return toExpr ds.mkEnv
  else
    for (stx, e) in ds.errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Strata.Environment) (toExpr true)

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let emptyLeanEnv ← mkEmptyEnvironment 0
  let inputCtx ← getInputContext
  let loader := (dialectExt.getState (←Lean.getEnv)).loader
  let (d, s) := Elab.elabDialect emptyLeanEnv loader inputCtx p e
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

end Strata

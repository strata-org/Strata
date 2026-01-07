/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Parser.Types

public import Lean.Elab.Command

public meta import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions

public meta import Strata.DDM.Integration.Lean.Env
public meta import Strata.DDM.Elab

meta import Strata.DDM.TaggedRegions

open Lean
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM liftCoreM)
open Lean.Elab.Term (TermElab)
open Lean.Parser (InputContext)
open System (FilePath)

namespace Strata

class HasInputContext (m : Type → Type _) [Functor m] where
  getInputContext : m InputContext
  getFileName : m FilePath :=
    (fun ctx => FilePath.mk ctx.fileName) <$> getInputContext

--export HasInputContext (getInputContext)

meta instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

meta instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

private meta def mkScopedName {m} [Monad m] [MonadError m] [MonadEnv m] [MonadResolveName m] (name : Name) : m Name := do
  let scope ← getCurrNamespace
  let fullName := scope ++ name
  let env ← getEnv
  if env.contains fullName then
    throwError s!"Cannot define {name}: {fullName} already exists."
  return fullName

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
private def mkAbsIdent (name : Lean.Name) : Ident :=
  let nameStr := toString name
  .mk (.ident .none nameStr.toSubstring name [.decl name []])

/--
Add a definition to environment and compile it.
-/
meta def addDefn (name : Lean.Name)
            (type : Lean.Expr)
            (value : Lean.Expr)
            (levelParams : List Name := [])
            (hints : ReducibilityHints := .abbrev)
            (safety : DefinitionSafety := .safe)
            (all : List Lean.Name := [name]) : CoreM Unit := do
  addAndCompile <| .defnDecl {
    name := name
    levelParams := levelParams
    type := type
    value := value
    hints := hints
    safety := safety
    all := all
  }

/--
Declare dialect and add to environment.
-/
meta def declareDialect (d : Dialect) : CommandElabM Unit := do
  -- Identifier for dialect
  let dialectName := Name.anonymous |>.str d.name
  let dialectAbsName ← mkScopedName dialectName
  -- Identifier for dialect map
  let mapAbsName ← mkScopedName (Name.anonymous |>.str s!"{d.name}_map")

  let dialectTypeExpr := mkConst ``Dialect
  liftCoreM <| addDefn dialectAbsName dialectTypeExpr (toExpr d)
  -- Add dialect to environment
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d dialectAbsName (isNew := true))
  -- Create term to represent minimal DialectMap with dialect.
  let s := (dialectExt.getState (←Lean.getEnv))
  let .isTrue mem := inferInstanceAs (Decidable (d.name ∈ s.loaded.dialects))
    | throwError "Internal error with unknown dialect"
  let openDialects := s.loaded.dialects.importedDialects d.name mem |>.toList
  let exprD (d : Dialect) : CommandElabM Lean.Expr := do
      let some name := s.nameMap[d.name]?
        | throwError s!"Unknown dialect {d.name}"
      return mkConst name
  let de ← openDialects.mapM exprD
  let mapValue := mkApp (mkConst ``DialectMap.ofList!)
                        (listToExpr .zero dialectTypeExpr de)
  liftCoreM <| addDefn mapAbsName (mkConst ``DialectMap) mapValue

declare_tagged_region command strataDialectCommand "#dialect" "#end"

@[command_elab strataDialectCommand]
public meta def strataDialectImpl: Lean.Elab.Command.CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← HasInputContext.getInputContext
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
public meta def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (HasInputContext.getInputContext : CoreM _)
  let s := (dialectExt.getState (←Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram s.loaded leanEnv inputCtx p e with
  | .ok pgm =>
    -- Get Lean name for dialect
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    let commandType := mkConst ``Operation
    let cmdToExpr (cmd : Strata.Operation) : CoreM Lean.Expr := do
          let n ← mkFreshUserName `command
          addDefn n commandType (toExpr cmd)
          pure <| mkConst n
    let commandExprs ← monadLift <| pgm.commands.mapM cmdToExpr
    return astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (arrayToExpr .zero commandType commandExprs)
  | .error errors =>
    for e in errors do
      logMessage e
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr Program) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

meta def resolveLeanRelPath {m} [Monad m] [HasInputContext m] [MonadError m] (path : FilePath) : m FilePath := do
  if path.isAbsolute then
    pure path
  else
    let leanPath ← HasInputContext.getFileName
    let .some leanDir := leanPath.parent
      | throwError "Current file {leanPath} does not have a parent."
    pure <| leanDir / path

@[command_elab loadDialectCommand]
public meta def loadDialectImpl: CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (← absPath.pathExists) then
      throwErrorAt pathStx "Could not find file {dialectPath}"
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

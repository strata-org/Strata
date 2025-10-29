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
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

declare_tagged_region command strataDialectCommand "#dialect" "#end"

private def mkScopedName {m} [Monad m] [MonadError m] [MonadEnv m] [MonadResolveName m] (name : Name) : m (Ident × Name) := do
  let scope ← getCurrNamespace
  let fullName := scope ++ name
  let env ← getEnv
  if env.contains fullName then
    throwError s!"Cannot define {name}: {fullName} already exists."
  return (Lean.mkScopedIdent scope name, fullName)

/--
Create a new definition equal to the given term.
-/
private def elabDef (ident : Ident) (type : Term) (qdef : Term) : CommandElabM Unit := do
  let cmd ← `(command| def $ident : $type := $qdef)
  tryCatch (elabCommand cmd) fun e =>
    throwError m!"Definition of {ident} failed: {e.toMessageData}"

private def quoteList : List Term → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[x, quoteList xs]

/--
Prepend the current namespace to the Lean name and convert to an identifier.
-/
private def mkAbsIdent (name : Lean.Name) : Ident :=
  let nameStr := toString name
  .mk (.ident .none nameStr.toSubstring name [.decl name []])

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
  -- Identifier for dialect
  let dialectName := Name.anonymous |>.str d.name
  let (dialectIdent, dialectAbsName) ← mkScopedName dialectName
  -- Identifier for dialect map
  let (mapIdent, _) ← mkScopedName (Name.anonymous |>.str s!"{d.name}_map")
  elabDef dialectIdent (mkAbsIdent ``Dialect) (quote d)
  -- Add dialect to environment
  modifyEnv fun env =>
    dialectExt.modifyState env (·.addDialect! d dialectAbsName (isNew := true))
  -- Create term to represent minimal DialectMap with dialect.
  let s := (dialectExt.getState (←Lean.getEnv))
  let openDialects := s.loaded.dialects.importedDialects! d.name |>.toList
  let quoteD (d : Dialect) : CommandElabM Term := do
      let some name := s.nameMap[d.name]?
        | throwError s!"Unknown dialect {d.name}"
      return mkAbsIdent name
  let ds ← openDialects.mapM quoteD
  let mapTerm : Term := Syntax.mkCApp ``DialectMap.ofList! #[quoteList ds]
  elabDef mapIdent (mkAbsIdent ``DialectMap) mapTerm

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

private def listToExpr (level : Level) (type : Lean.Expr) (es : List Lean.Expr) : Lean.Expr :=
  let nilFn  := mkApp (mkConst ``List.nil [level]) type
  let consFn := mkApp (mkConst ``List.cons [level]) type
  let rec aux : List Lean.Expr → Lean.Expr
    | []    => nilFn
    | a::as => mkApp2 consFn a (aux as)
  aux es

@[term_elab strataProgram]
def strataProgramImpl : TermElab := fun stx tp => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← (getInputContext : CoreM _)
  let s := (dialectExt.getState (←Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  match Elab.elabProgram s.loaded leanEnv inputCtx p e with
  | .ok pgm =>
    -- Get Lean name for dialect
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    return astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (toExpr pgm.commands)
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

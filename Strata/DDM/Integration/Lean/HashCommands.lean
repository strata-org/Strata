/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Elab.Command
public meta import Strata.DDM.Elab
public meta import Strata.DDM.Integration.Lean.Env
public meta import Strata.DDM.Integration.Lean.ToExpr
public meta import Strata.DDM.TaggedRegions
import Strata.DDM.Elab.DeclM
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.TaggedRegions

open Lean
open Lean.Elab (throwUnsupportedSyntax)
open Lean.Elab.Command (CommandElab CommandElabM liftCoreM)
open Lean.Elab.Term (TermElab)
open Lean.Parser (InputContext)
open System (FilePath)
open Strata.Lean (arrayToExpr listToExpr)

namespace Strata

public class HasInputContext (m : Type → Type _) [Functor m] where
  getInputContext : m InputContext
  getFileName : m FilePath :=
    (fun ctx => FilePath.mk ctx.fileName) <$> getInputContext

/--
Bundle returned by the `#strata` term region. Carries:

- `program`: the parsed `Strata.Program` with **file-global** AST byte offsets,
  so Boole-style consumers (and any code that uses byte offsets in obligation
  labels or diagnostic ranges) keep their existing behavior.
- `source`: the raw snippet text between `#strata` and `#end`. Test helpers
  use this to build a snippet-local `FileMap`.
- `basePos`: byte offset in the Lean file where the snippet starts, so
  helpers can convert file-global pipeline diagnostics back to snippet-local
  positions when matching against inline annotations.
- `baseLine` / `fileName`: enough info for helpers to render
  `<lean_file>:<line>:<col>` in error messages so editors / quickfix lists
  can jump straight to the offending source.
-/
public structure SourcedProgram where
  program  : Program
  source   : String
  basePos  : Nat
  baseLine : Nat
  fileName : String
  deriving Inhabited

/-- Forward `ToString` to the underlying `Program` so `#eval` printing keeps
    working at existing call sites. -/
public instance : ToString SourcedProgram where
  toString s := toString s.program

/-- Allow `SourcedProgram` to be used wherever a `Program` is expected; the
    source/positions are dropped. Removes ~200 explicit `.program` accessors
    at consumer call sites. -/
public instance : Coe SourcedProgram Program where
  coe s := s.program

-- Forwarders so existing call sites can keep using `.commands`, `.dialect`,
-- etc. on the result of `#strata` as if it were a `Program`.
namespace SourcedProgram

public abbrev commands (s : SourcedProgram) : Array Operation :=
  s.program.commands
public abbrev dialect (s : SourcedProgram) : DialectName :=
  s.program.dialect
public abbrev dialects (s : SourcedProgram) : DialectMap :=
  s.program.dialects
public abbrev globalContext (s : SourcedProgram) : GlobalContext :=
  s.program.globalContext
public abbrev format (s : SourcedProgram) (opts : FormatOptions := {}) : Std.Format :=
  s.program.format opts

end SourcedProgram

meta section

deriving instance Lean.ToExpr for SourcedProgram

public instance : HasInputContext CommandElabM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

public instance : HasInputContext CoreM where
  getInputContext := do
    let ctx ← read
    pure {
      inputString := ctx.fileMap.source
      fileName := ctx.fileName
      fileMap := ctx.fileMap
    }
  getFileName := return (← read).fileName

def mkScopedName {m} [Monad m] [MonadError m] [MonadEnv m] [MonadResolveName m] (name : Name) : m Name := do
  let scope ← getCurrNamespace
  let fullName := scope ++ name
  let env ← getEnv
  if env.contains fullName then
    throwError s!"Cannot define {name}: {fullName} already exists."
  return fullName

def offsetPos (base : String.Pos.Raw) (pos : String.Pos.Raw) : String.Pos.Raw :=
  ⟨base.byteIdx + pos.byteIdx⟩

def offsetSourceRange (base : String.Pos.Raw) (sr : SourceRange) : SourceRange :=
  { start := offsetPos base sr.start, stop := offsetPos base sr.stop }

def offsetMessage
    (fullCtx snippetCtx : InputContext)
    (base : String.Pos.Raw)
    (msg : Lean.Message) : Lean.Message :=
  let pos := fullCtx.fileMap.toPosition (offsetPos base (snippetCtx.fileMap.ofPosition msg.pos))
  let endPos := msg.endPos.map fun endPos =>
    fullCtx.fileMap.toPosition (offsetPos base (snippetCtx.fileMap.ofPosition endPos))
  { msg with fileName := fullCtx.fileName, pos := pos, endPos := endPos }

/--
Add a definition to environment and compile it.
-/
public def addDefn (name : Lean.Name)
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

public section

/--
Declare dialect and add to environment.
-/
def declareDialect (d : Dialect) : CommandElabM Unit := do
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
  let .isTrue mem := (inferInstance : Decidable (d.name ∈ s.loaded.dialects))
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
def strataDialectImpl: CommandElab := fun (stx : Syntax) => do
  let .atom i v := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let inputCtx ← HasInputContext.getInputContext
  let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
  let fm ← Strata.DialectFileMap.new loaded
  let (d, s) ← Strata.Elab.elabDialect fm inputCtx p e
  if !s.errors.isEmpty then
    for e in s.errors do
      logMessage e
    return
  -- Add dialect to command environment
  declareDialect d

declare_tagged_region term strataProgram "#strata" "#end"

@[term_elab strataProgram]
meta def strataProgramImpl : TermElab := fun stx _ => do
  let .atom i _ := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let fullInputCtx ← (HasInputContext.getInputContext : CoreM _)
  let snippet := String.Pos.Raw.extract fullInputCtx.inputString p e
  let inputCtx : InputContext := {
    inputString := snippet
    fileName := fullInputCtx.fileName
    fileMap := FileMap.ofString snippet
  }
  let s := (dialectExt.getState (←Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let baseLine : Nat := (fullInputCtx.fileMap.toPosition p).line
  match Elab.elabProgram s.loaded leanEnv inputCtx 0 inputCtx.endPos with
  | .ok pgm =>
    let commands := pgm.commands.map (fun cmd => cmd.mapAnn (offsetSourceRange p))
    let pgm := Program.create pgm.dialects pgm.dialect commands
    -- Get Lean name for dialect
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    let commandType := mkConst ``Operation
    let cmdToExpr (cmd : Strata.Operation) : CoreM Lean.Expr := do
          let n ← mkFreshUserName `command
          addDefn n commandType (toExpr cmd)
          pure <| mkConst n
    let commandExprs ← monadLift <| pgm.commands.mapM cmdToExpr
    let pgmExpr : Lean.Expr :=
      astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (arrayToExpr .zero commandType commandExprs)
    return mkApp5 (mkConst ``SourcedProgram.mk)
      pgmExpr
      (toExpr snippet)
      (toExpr (p.byteIdx : Nat))
      (toExpr baseLine)
      (toExpr fullInputCtx.fileName)
  | .error errors =>
    for e in errors do
      logMessage (offsetMessage fullInputCtx inputCtx p e)
    return mkApp2 (mkConst ``sorryAx [1]) (toTypeExpr SourcedProgram) (toExpr true)

syntax (name := loadDialectCommand) "#load_dialect" str : command

private def resolveLeanRelPath {m} [Monad m] [HasInputContext m] [MonadError m] (path : FilePath) : m FilePath := do
  if path.isAbsolute then
    pure path
  else
    let leanPath ← HasInputContext.getFileName
    let .some leanDir := leanPath.parent
      | throwError "Current file {leanPath} does not have a parent."
    pure <| leanDir / path

@[command_elab loadDialectCommand]
def loadDialectImpl : CommandElab := fun (stx : Syntax) => do
  match stx with
  | `(command|#load_dialect $pathStx) =>
    let dialectPath : FilePath := pathStx.getString
    let absPath ← resolveLeanRelPath dialectPath
    if ! (← absPath.pathExists) then
      throwErrorAt pathStx "Could not find file {dialectPath}"
    let loaded := (dialectExt.getState (←Lean.getEnv)).loaded
    let fm ← Strata.DialectFileMap.new loaded
    let r ← Elab.loadDialectFromFile fm (path := dialectPath) (actualPath := absPath)
    -- Add dialect to command environment
    match r with
    | .ok d =>
      declareDialect d
    | .error errorMessages =>
      assert! errorMessages.size > 0
      throwError (← Elab.mkErrorReport errorMessages)
  | _ =>
    throwUnsupportedSyntax

end
end

end Strata

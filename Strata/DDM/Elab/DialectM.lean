/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.DeclM
import Strata.DDM.Elab.Tree
import Strata.DDM.Elab.Core

namespace Strata.Elab

structure DialectContext where
  /-- Callback to load dialects dynamically upon demand. -/
  loadDialect : DialectName → StateT LoadedDialects BaseIO (Except String Dialect)
  inputContext : Parser.InputContext
  stopPos : String.Pos

structure DialectState where
  loaded : LoadedDialects
  declState : DeclState
  dialect : Dialect

abbrev DialectM := ReaderT DialectContext (StateRefT DialectState BaseIO)

def getCurrentDialect : DialectM Dialect := return (←get).dialect

instance :  MonadState DialectState DialectM := inferInstanceAs (MonadState DialectState (ReaderT _ _))

instance : MonadLift DeclM DialectM where
  monadLift act := fun c => do
    let { loaded := loaded, declState := ds, dialect := dialect } ← get
    let ctx : DeclContext := {
        inputContext := c.inputContext,
        stopPos := c.stopPos,
        loader := loaded
    }
    let (r, ds) := act ctx ds
    set ({ loaded := loaded, declState := ds, dialect := dialect } : DialectState)
    pure  r

def getDeclState : DialectM DeclState := fun _ => DialectState.declState <$> get

def modifyDeclState (f : DeclState → DeclState) : DialectM Unit := modify fun s => { s with declState := f s.declState }

def modifyDialect (f : Dialect → Dialect) : DialectM Unit := fun _ =>
  modify fun (s : DialectState) => { s with dialect := f s.dialect }

def addDeclToDialect (decl : Decl) : DialectM Unit :=
  modifyDialect fun d => d.addDecl decl

instance : ElabClass DialectM where
  getInputContext := fun c => pure c.inputContext
  getDialects := return (← get).loaded.dialects
  getOpenDialects := return (← get).declState.openDialectSet
  getGlobalContext := return (←get).declState.globalContext
  getErrorCount := return (←get).declState.errors.size
  logErrorMessage stx msg :=
    modifyDeclState fun s => { s with errors := s.errors.push (stx, msg) }

abbrev DialectElab := Tree → DialectM Unit

private def checkTypeDeclarationArgs (tree : Tree) : ElabM (Array String) := do
  let bindings := tree.optBindings!
  let mut m := ArgDeclsMap.empty bindings.size
  for t in bindings do
    let (arg, success) ← runChecked <| translateArgDecl m t
    if !success then
      return default
    if !arg.val.kind.isType then
      logErrorMF arg.typeStx mf!"Parameters for a type declaration must have category {q`Init.Type}."
      return default
    m := addBinding m arg
  return m.decls.map (·.val.ident)

private def elabTypeCommand (tree : Tree) : DialectM Unit := do
  let d ← getCurrentDialect
  assert! tree.children.size = 2

  -- Get arguments
  let ((name, argNames), success) ← runElab <| runChecked <| do
    -- Get name
    let .node (.ofIdentInfo nameInfo) _ := tree[0]!
      | panic! "Expected identifier"
    let name := nameInfo.val
    if name ∈ d.cache then
      logError nameInfo.stx  s!"{name} already declared."
    let args ← checkTypeDeclarationArgs tree[1]!
    pure (name, args)

  if success then
    let decl := { name, argNames }
    addTypeOrCatDecl d.name (.type decl)
    addDeclToDialect (.type decl)

/- Add a new operator. -/
def elabOpCommand (tree : Tree) : DialectM Unit := do
  let d ← getCurrentDialect
  assert! tree.children.size = 6
  let nameInfo := tree[0]!.info.asIdent!
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.stx s!"{name} already declared."; return

  let argDeclsTree := tree[1]!
  let (argDecls, argDeclsSuccess) ← runElab <| runChecked <| translateArgDecls argDeclsTree

  let categoryTree := tree[2]!
  let (category, categorySuccess) ← runElab <| runChecked <| translateSyntaxCat categoryTree.asBindingType!

  let opMetadataTree := tree[3]!
  let (opMetadata, opMetadataSuccess) ← runElab <| runChecked <| translateOptMetadata! argDecls opMetadataTree

  if !argDeclsSuccess then
    return

  let opMdTree := tree[4]!
  let opStxTree := tree[5]!
  let (opStx, opStxSuccess) ← runElab <| runChecked <| translateSyntaxDef argDecls opMdTree opStxTree

  -- FIXME. Change this to use stxArgDecls so we get better error messages.
  let argDecls := argDecls.decls.map (·.val)
  let (newBindings, newBindingErrors) := parseNewBindings opMetadata argDecls
  for err in newBindingErrors do
    logError opMetadataTree.info.stx err

  if !categorySuccess then
    return
  if !opStxSuccess then
    return

  let category ←
      match category with
      | .atom c =>
        pure c
      | .app _ _ =>
        logError categoryTree.info.stx s!"Expected atomic category"
        return

  let ctx := (←getDeclState).fixedParsers
  let ident : QualifiedIdent := { dialect := d.name, name }
  match ctx.opSyntaxParser category ident argDecls opStx with
  | .error msg =>
    logErrorMF opStxTree.info.stx msg
    return
  | .ok _ => pure ()
  if !opMetadataSuccess then
    return
  if !newBindingErrors.isEmpty then
    return
  let decl : OpDecl := {
    name,
    argDecls,
    category,
    syntaxDef := opStx,
    metadata := opMetadata,
    newBindings := newBindings
  }
  addDeclToDialect (.op decl)

def elabDialectImportCommand (tree : Tree) : DialectM Unit := do
  assert! tree.children.size = 1
  let identTree := tree[0]!.info
  let name := identTree.asIdent!.val
  let d ←
    match (← get).loaded.dialects[name]? with
    | some d =>
      pure d
    | none =>
      let loadCallback ← (·.loadDialect) <$> read
      let r ← fun _ ref => do
        let loaded := (← ref.get).loaded
        assert! "StrataDDL" ∈ loaded.dialects.map.keys
        let (r, loaded) ← loadCallback name loaded
        ref.modify fun s => { s with loaded := loaded }
        pure r
      match r with
      | .ok d =>
        pure d
      | .error msg =>
        logError identTree.stx msg
        return
  if name ∈ (←getDeclState).openDialectSet then
    logError identTree.stx <| s!"Dialect {name} already open."
    return
  modify fun s => { s with declState := s.declState.openLoadedDialect! s.loaded d }
  modifyDialect fun d => { d with imports := d.imports.push name }

private def elabCategoryCommand (tree : Tree) : DialectM Unit := do
  let d ← getCurrentDialect
  assert! d.name ∈ (← getDeclState).openDialectSet
  assert! tree.children.size = 1
  let name := tree.children[0]!.info.asIdent!
  if name.val ∈ d.cache then
    logError name.stx  s!"Category {name.val} already declared."
    return
  let decl : SynCatDecl := { name := name.val, argNames := #[] }
  addDeclToDialect (.syncat decl)
  addTypeOrCatDecl d.name (.syncat decl)
  modifyDeclState (·.addSynCat! d.name decl)

/- Evaluate a function. -/
def elabFnCommand (tree : Tree) : DialectM Unit := do
  let d ← getCurrentDialect
  assert! tree.children.size = 6

  let .ofIdentInfo nameInfo := tree[0]!.info
    | panic! "Expected identifier"
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.stx s!"{name} already declared."; return

  let argsTree := tree[1]!
  let (params, argDeclsSuccess) ← runElab <| runChecked <| translateArgDecls argsTree

  let returnTypeTree := tree[2]!.asBindingType!
  let isType : Array Bool := params.decls.map (·.val.kind.isType)
  let (result, resultSuccess) ← runElab <| runChecked <| translateTypeExpr params.argIndexMap isType.size (fun lvl => isType[lvl]!) returnTypeTree

  let opMetadataTree := tree[3]!
  let (opMetadata, opMetadataSuccess) ← runElab <| runChecked <| translateOptMetadata! params opMetadataTree

  if !argDeclsSuccess then
    return

  let opMdTree := tree[4]!
  let opStxTree := tree[5]!
  let (opStx, stxSuccess) ← runElab <| runChecked <| translateSyntaxDef params opMdTree opStxTree

  if !stxSuccess then
    return

  let argDecls := params.decls.map (·.val)

  let ident := { dialect := d.name, name }
  match (←getDeclState).fixedParsers.opSyntaxParser q`Init.Expr ident argDecls opStx with
  | .error msg =>
    logErrorMF tree.info.stx msg
  | .ok _ =>
    if !resultSuccess then
      return
    if !opMetadataSuccess then
      return
    let decl : FunctionDecl := {
      name,
      argDecls := argDecls,
      result := result,
      syntaxDef := opStx,
      metadata := opMetadata,
    }
    addDeclToDialect (.function decl)

def elabMdCommand (tree : Tree) : DialectM Unit := do
  let d ← getCurrentDialect
  assert! tree.children.size = 2

  let .ofIdentInfo nameInfo := tree[0]!.info
    | panic! "Expected identifier"
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.stx s!"{name} already declared."; return

  let optBindingsTree := tree[1]!

  let (argDecls, success) ← runChecked <| do
        let bindings := optBindingsTree.optBindings!
        let mut params : Std.HashSet String := {}
        let mut argTypes := Array.mkEmpty bindings.size
        for c in bindings do
          let (nameInfo, tpTree, _) := c.binding!
          if nameInfo.val ∈ params then
            logError nameInfo.stx s!"{nameInfo.val} already declared."
          params := params.insert nameInfo.val

          let (c, success) ← runElab <| runChecked <| translateSyntaxCat tpTree
          let mdType ←
            if success then
              elabMetadataArgCatType tpTree.info.stx c
            else
              pure default
          argTypes := argTypes.push { ident := nameInfo.val, type := mdType }
        pure argTypes
  if success then
    let dialect := d.name
    let decl := {
      name := name,
      args := argDecls
    }
    addDeclToDialect (.metadata decl)
    modifyDeclState fun s =>  { s with
      metadataDeclMap := s.metadataDeclMap.add dialect decl
    }

def dialectElabs : Std.HashMap QualifiedIdent DialectElab :=
  Std.HashMap.ofList <|
    [ (q`StrataDDL.importCommand, elabDialectImportCommand),
      (q`StrataDDL.categoryCommand, elabCategoryCommand),
      (q`StrataDDL.opCommand,   elabOpCommand),
      (q`StrataDDL.typeCommand, elabTypeCommand),
      (q`StrataDDL.fnCommand,   elabFnCommand),
      (q`StrataDDL.mdCommand,   elabMdCommand),
    ]

partial def runDialectCommand (leanEnv : Lean.Environment) : DialectM Bool := do
  assert! "StrataDDL" ∈ (← get).loaded.dialects.map.keys
  let (mtree, success) ← runChecked <| elabCommand leanEnv
  match mtree with
  | none =>
    pure false
  | some tree =>
    if success then
      let cmd := tree.info.asOp!.op
      match dialectElabs[cmd.name]? with
      | some act => act tree
      | none => panic! "Unexpected command"
    pure true

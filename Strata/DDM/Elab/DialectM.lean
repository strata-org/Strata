/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.DDM.Elab.Core

import Std.Data.HashMap
import all Strata.DDM.Util.Array
import all Strata.DDM.Util.Fin

set_option autoImplicit false

public section
namespace Strata

namespace PreType

/--
Apply a function f over all bound variables in expression.

Note this does not return variables referenced by .funMacro.
-/
private def foldBoundTypeVars {α} (tp : PreType) (init : α) (f : α → Nat → α) : α :=
  match tp with
  | .ident _ _ a => a.attach.foldl (init := init) fun r ⟨e, _⟩ => e.foldBoundTypeVars r f
  | .fvar _ _ a => a.attach.foldl (init := init) fun r ⟨e, _⟩ => e.foldBoundTypeVars r f
  | .bvar _ i => f init i
  | .arrow _ a r => r.foldBoundTypeVars (a.foldBoundTypeVars init f) f
  | .funMacro _ _ r => r.foldBoundTypeVars init f

end PreType

namespace Elab

/--
An argument declaration with annotations for the source location of name and type.
-/
structure ArgDeclWithLoc where
  nameLoc : SourceRange
  typeLoc : SourceRange
  val : ArgDecl
  deriving Inhabited

/--
Map for arg declarations.
-/
structure ArgDeclsMap (argc : Nat) where
  argIndexMap : Std.HashMap String Nat
  decls : Vector ArgDeclWithLoc argc
  argIndexMapSize : argIndexMap.size = argc
  mapIndicesValid : ∀(v : String) (p : v ∈ argIndexMap), argIndexMap[v] < argc

namespace ArgDeclsMap

def isType {argc} (m : ArgDeclsMap argc) (lvl : Fin argc) := m.decls[lvl].val.kind.isType

def empty (capacity : Nat := 0) : ArgDeclsMap 0 := {
  argIndexMap := {},
  decls := .emptyWithCapacity capacity,
  argIndexMapSize := by simp
  mapIndicesValid := fun v p => by simp at p
}

/--
Adds an additional declaration to the list of arguments.

Requires proof the name is new.
-/
protected def push {n} (m : ArgDeclsMap n) (d : ArgDeclWithLoc)
  (isUnused : d.val.ident ∉ m.argIndexMap) : ArgDeclsMap (n + 1) := {
  argIndexMap := m.argIndexMap.insert d.val.ident m.decls.size,
  decls := m.decls.push d
  argIndexMapSize := by
    have p := m.argIndexMapSize
    grind
  mapIndicesValid := by
    intro x mem
    simp [Std.HashMap.getElem_insert]
    if eq : d.val.ident = x then
      simp [eq]
    else
      simp [Std.HashMap.mem_insert, eq] at mem
      have v := m.mapIndicesValid x mem
      grind
}

def argLevel? {argc} (argDecls : ArgDeclsMap argc) (name : String) : Option (Fin argc) :=
  match r : argDecls.argIndexMap[name]? with
  | none => none
  | some lvl =>
    have lvlP : lvl < argc := by
      have q := argDecls.mapIndicesValid name;
      grind
    some ⟨lvl, lvlP⟩

end ArgDeclsMap

def asTypeVar {argc : Nat} (argDecls : ArgDeclsMap argc) (loc : SourceRange) (tpId : MaybeQualifiedIdent) (argChildren : Array Tree) : ElabM (Option PreType) := do
  if let .name name := tpId then
    if let some lvl := argDecls.argLevel? name then
      if !(argDecls.isType lvl) then
        logError loc s!"Expected type."
      else if let some _ := argChildren[0]? then
        logError loc s!"{name} does not have arguments."
      let idx := argc - lvl - 1
      return some (.bvar loc idx)
  return none

def translateFunMacro {argc : Nat} (argDecls : ArgDeclsMap argc) (loc : SourceRange) (bindingsTree : Tree) (rType : PreType) : ElabM PreType := do
  let .ofIdentInfo nameInfo := bindingsTree.info
    | panic! "Expected identifier"
  let .some lvl := argDecls.argLevel? nameInfo.val
    | logError nameInfo.loc s!"Unknown variable {nameInfo.val}"; return default
  if argDecls.isType lvl then
    logError nameInfo.loc s!"Expected type that creates variables."
    return default
  return .funMacro loc (argc - lvl - 1) rType

/--
Evaluate the tree as a type expression.
-/
def translatePreType {argc : Nat} (argDecls : ArgDeclsMap argc) (tree : Tree) : ElabM PreType := do
  match feq : flattenTypeApp tree #[] with
  | (⟨argInfo, argChildren⟩, args) =>
  let opInfo :=
        match argInfo with
        | .ofOperationInfo info => info
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match opInfo.op.name with
  | q`Init.TypeIdent => do
    let isTrue p := inferInstanceAs (Decidable (argChildren.size = 1))
      | return panic! "Invalid arguments to Init.TypeIdent"
    let ident := argChildren[0]
    let tpId := translateQualifiedIdent ident
    if let some tp ← asTypeVar argDecls ident.info.loc tpId args then
      return tp
    let some (qname, decl) ← resolveTypeOrCat ident.info.loc tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize argInfo.loc qname decl.argNames.size args
      let args ← args.attach.mapM fun ⟨a, _⟩ =>
        translatePreType argDecls a
      return .ident opInfo.loc qname args
    | _ =>
      logError ident.info.loc s!"Expected type"; pure default
  | q`Init.TypeArrow => do
    let isTrue p := inferInstanceAs (Decidable (argChildren.size = 2))
      | return panic! "Invalid arguments to Init.TypeArrow"
    let aTree := argChildren[0]
    let rTree := argChildren[1]
    let aType ← translatePreType argDecls aTree
    let rType ← translatePreType argDecls rTree
    return .arrow opInfo.loc aType rType

  | q`StrataDDL.TypeFn =>
    let isTrue p := inferInstanceAs (Decidable (argChildren.size = 2))
      | return panic! "Invalid arguments to Init.TypeArrow"
    let bindingsTree := argChildren[0]
    let valTree := argChildren[1]
    let rType ← translatePreType argDecls valTree
    translateFunMacro argDecls opInfo.loc bindingsTree rType
  | _ =>
    logInternalError opInfo.loc s!"translatePreType given invalid syntax {repr opInfo.op.name}"
    return default
  termination_by tree
  decreasing_by
    · have p : sizeOf a < sizeOf args := by decreasing_tactic
      have argsP : sizeOf args ≤ sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min argChildren
        simp [feq] at p
        omega
      decreasing_tactic
    · have p : sizeOf argChildren[0] < sizeOf argChildren := by decreasing_tactic
      have argcP : sizeOf argChildren < sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min args
        simp [feq] at p
        omega
      decreasing_tactic
    · have p : sizeOf argChildren[1] < sizeOf argChildren := by decreasing_tactic
      have argcP : sizeOf argChildren < sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min args
        simp [feq] at p
        omega
      decreasing_tactic
    · have p : sizeOf argChildren[1] < sizeOf argChildren := by decreasing_tactic
      have argcP : sizeOf argChildren < sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min args
        simp [feq] at p
        omega
      decreasing_tactic

/--
Evaluate the tree as a type expression.
-/
partial def translateArgDeclKind {argc} (argDecls : ArgDeclsMap argc) (tree : Tree) : ElabM ArgDeclKind := do
  let (⟨argInfo, argChildren⟩, args) := flattenTypeApp tree #[]
  let .ofOperationInfo opInfo := argInfo
    | return panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  let op := opInfo.op.name
  match op with
  | q`Init.TypeIdent => do
    assert! argChildren.size = 1
    let identTree := argChildren[0]!
    let declLoc := identTree.info.loc
    let tpId := translateQualifiedIdent identTree
    if let some tp ← asTypeVar argDecls declLoc tpId args then
      return .type tp
    if declLoc.isNone then
      panic! s!"{repr identTree} missing location information."
    let some (name, decl) ← resolveTypeOrCat declLoc tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize argInfo.loc name decl.argNames.size args
      let args ← args.mapM (translatePreType argDecls)
      return .type <| .ident opInfo.loc name args
    | .syncat decl =>
      checkArgSize argInfo.loc name decl.argNames.size args
      return .cat {
        ann := declLoc
        name := name
        args := ← args.mapM translateSyntaxCat
      }
  | q`Init.TypeArrow => do
    assert! argChildren.size = 2
    let aType ← translatePreType argDecls argChildren[0]!
    let rType ← translatePreType argDecls argChildren[1]!
    return .type (.arrow opInfo.loc aType rType)
  | q`StrataDDL.TypeFn => do
    let bindingsTree := argChildren[0]!
    let valTree := argChildren[1]!
    let rType ← translatePreType argDecls valTree
    .type <$> translateFunMacro argDecls opInfo.loc bindingsTree rType
  | _ =>
    logInternalError argInfo.loc s!"translateArgDeclKind given invalid kind {op}"
    return default

def elabMetadataName (loc : SourceRange) (mi : MaybeQualifiedIdent) : ElabM (QualifiedIdent × MetadataDecl) := do
  match mi with
  | .qid q =>
    logErrorMF loc mf!"Qualified ident {q} not yet supported." -- FIXME
    return default
  | .name ident =>
    let decls := (←read).metadataDeclMap.get ident
    let some (d, decl) := decls[0]?
      | logError loc s!"Unknown metadata attribute {ident}"
        return default
    -- Check if there is another possibility
    if let some (d_alt, _) := decls[1]? then
      logError loc s!"{ident} is ambiguous; declared in {d} and {d_alt}"
    return ({ dialect := d, name := ident }, decl.val)

/-- Translate a FunctionIterScope syntax tree to the AST type -/
def translateFunctionIterScope (tree : Tree) : ElabM FunctionIterScope := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for FunctionIterScope"
  match opInfo.op.name with
  | q`Init.scopePerConstructor => return .perConstructor
  | q`Init.scopePerField => return .perField
  | name => panic! s!"Unknown FunctionIterScope: {name.fullName}"

/-- Translate a NamePatternPart syntax tree to the AST type -/
def translateNamePatternPart (tree : Tree) : ElabM NamePatternPart := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for NamePatternPart"
  match opInfo.op.name with
  | q`Init.patternLiteral =>
    let .ofStrlitInfo strInfo := tree[0]!.info
      | panic! "Expected string literal for pattern literal"
    return .literal strInfo.val
  | q`Init.patternDatatype => return .datatype
  | q`Init.patternConstructor => return .constructor
  | q`Init.patternField => return .field
  | name => panic! s!"Unknown NamePatternPart: {name.fullName}"

/-- Translate a NamePattern syntax tree (array of NamePatternPart) -/
def translateNamePattern (tree : Tree) : ElabM (Array NamePatternPart) := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for NamePattern"
  assert! opInfo.op.name == q`Init.namePatternMk
  let some parts := tree[0]!.asCommaSepInfo?
    | panic! "Expected comma-separated list for name pattern"
  parts.mapM translateNamePatternPart

/-- Translate a TypeRef syntax tree to the AST type -/
def translateTypeRef (tree : Tree) : ElabM TypeRef := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for TypeRef"
  match opInfo.op.name with
  | q`Init.typeRefDatatype => return .datatype
  | q`Init.typeRefFieldType => return .fieldType
  | q`Init.typeRefBuiltin =>
    let .ofStrlitInfo strInfo := tree[0]!.info
      | panic! "Expected string literal for builtin type name"
    return .builtin strInfo.val
  | name => panic! s!"Unknown TypeRef: {name.fullName}"

/-- Translate a TypeRefList syntax tree (array of TypeRef) -/
def translateTypeRefList (tree : Tree) : ElabM (Array TypeRef) := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for TypeRefList"
  assert! opInfo.op.name == q`Init.typeRefListMk
  let some types := tree[0]!.asCommaSepInfo?
    | panic! "Expected comma-separated list for type ref list"
  types.mapM translateTypeRef

/-- Translate a FunctionTemplate syntax tree to the AST type -/
def translateFunctionTemplate (tree : Tree) : ElabM FunctionTemplate := do
  let .ofOperationInfo opInfo := tree.info
    | panic! "Expected operation for FunctionTemplate"
  assert! opInfo.op.name == q`Init.functionTemplateMk
  let scope ← translateFunctionIterScope tree[0]!
  let namePattern ← translateNamePattern tree[1]!
  let paramTypes ← translateTypeRefList tree[2]!
  let returnType ← translateTypeRef tree[3]!
  return { scope, namePattern, paramTypes, returnType }

partial def translateMetadataArg {argc} (args : ArgDeclsMap argc) (argName : String) (expected : MetadataArgType) (tree : Tree) : ElabM MetadataArg := do
  let .ofOperationInfo argInfo := tree.info
    | panic! "Expected an operator"
  match argInfo.op.name with
  | q`Init.MetadataArgIdent =>
    let .ofIdentInfo nameInfo := tree[0]!.info
      | panic! "Invalid term"
    match expected with
    | .ident  =>
      pure ()
    | .opt _ =>
      logErrorMF nameInfo.loc mf!"Expected optional value."
    | _ =>
      logErrorMF nameInfo.loc mf!"Unexpected identifier."
    let name := nameInfo.val
    let some lvl := args.argLevel? name
      | logErrorMF nameInfo.loc mf!"Unknown variable {name} for {argName}.}"; return default
    if let .type tp := args.decls[lvl].val.kind then
      logErrorMF nameInfo.loc mf!"{name} refers to expression with type {tp} when category is required."
      return default
    return .catbvar (argc - lvl - 1)
  | q`Init.MetadataArgNum =>
    let .ofNumInfo numInfo := tree[0]!.info
      | panic! "Invalid term"
    match expected with
    | .num =>
      pure ()
    | _ =>
      logErrorMF numInfo.loc mf!"Expected numeric literal."
    return .num numInfo.val
  | q`Init.MetadataArgFalse =>
    assert! tree.children.size = 0
    return .bool false
  | q`Init.MetadataArgTrue =>
    assert! tree.children.size = 0
    return .bool true
  | q`Init.MetadataArgParen =>
    assert! tree.children.size = 1
    translateMetadataArg args argName expected tree[0]!
  | q`Init.MetadataArgSome =>
    match expected with
    | .opt tp =>
      assert! tree.children.size = 1
      let a ← translateMetadataArg args argName tp tree[0]!
      return .option (some a)
    | _ =>
      logErrorMF argInfo.loc mf!"Expected option type."
      return default
  | q`Init.MetadataArgNone =>
    match expected with
    | .opt _ =>
      return .option none
    | _ =>
      logErrorMF argInfo.loc mf!"Expected {expected} value."
      return default
  | q`Init.MetadataArgFunctionTemplate =>
    match expected with
    | .functionTemplate =>
      let template ← translateFunctionTemplate tree[0]!
      return .functionTemplate template
    | _ =>
      logErrorMF argInfo.loc mf!"Expected {expected} value, got function template."
      return default
  | name =>
    panic! s!"Unknown metadata arg kind {name.fullName}"

def translateMetadataArgs {argc} (argDecls : ArgDeclsMap argc) (decl : MetadataDecl) (op : Tree) : ElabM (Array MetadataArg) := do
  assert! op.isSpecificOp q`Init.MetadataArgsMk
  assert! op.children.size = 1
  let tree := op[0]!
  let some actuals := tree.asCommaSepInfo?
    | return panic! "Expected comma sep info"
  -- This could really be a panic
  let (_, success) ← runChecked <| checkArgSize op.info.loc decl.name decl.args.size actuals
  if !success then
    return default
  let mut res : Array MetadataArg := #[]
  for ({ ident := argName, type := argType }, tree) in Array.zip decl.args actuals do
    let (arg, success) ← runChecked <| translateMetadataArg argDecls argName argType tree
    if !success then
      return default
    res := res.push arg
  return res

def translateMetadataAttr {argc} (args : ArgDeclsMap argc) (t : Tree) : ElabM MetadataAttr := do
  let #[identInfo, argTree] := t.children
    | panic! "badArgs"
  let ((ident, decl),success) ← runChecked <| elabMetadataName identInfo.info.loc (translateQualifiedIdent identInfo)
  if !success then
    return default
  let args ← match argTree.children with
             | #[] =>
                if !decl.args.isEmpty then
                  logError .none s!"Missing arguments to {decl.name}"
                  return default
                pure #[]
             | #[t] =>
              translateMetadataArgs args decl t
             | _ => panic! s!"Expected arg sequence"
  return { ident, args }

/-- This parses an optional metadata -/
def translateMetadata {argc} (argDecls : ArgDeclsMap argc) (tree : Tree) : ElabM Metadata := do
  assert! tree.isSpecificOp q`Init.MetadataMk
  assert! tree.children.size = 1
  match tree[0]!.asCommaSepInfo? with
  | none => panic! s!"translateMetadata given {repr tree[0]!.info}"
  | some args => .ofArray <$> args.mapM (translateMetadataAttr argDecls)

/-- Translate metadata if it is optional. -/
def translateOptMetadata {argc} (argDecls : ArgDeclsMap argc) (tree : Option Tree) : ElabM Metadata := do
  match tree with
  | none => pure .empty
  | some tree => translateMetadata argDecls tree

/-- Translate metadata if it is optional. -/
def translateOptMetadata! {argc} (argDecls : ArgDeclsMap argc) (tree : Tree) : ElabM Metadata := do
  match tree.asOption? with
  | none => panic! "Expected option"
  | some mtree => translateOptMetadata argDecls mtree

def translateArgDecl {argc} (argDecls : ArgDeclsMap argc) (t: Tree) : ElabM ArgDeclWithLoc := do
  let (name, tpTree, mdTree) := t.binding!
  let kind ← translateArgDeclKind argDecls tpTree
  let metadata : Metadata ← translateOptMetadata argDecls mdTree
  let b : ArgDecl := {
    ident := name.val,
    kind := kind,
    metadata := metadata
  }
  return {
    nameLoc := name.loc,
    typeLoc := tpTree.info.loc,
    val := b
  }

def translateArgDecls (tree : Tree) : ElabM (Σ argc, ArgDeclsMap argc) := do
  let bindings := tree.optBindings!
  let s : Σ argc, ArgDeclsMap argc := ⟨0, .empty bindings.size⟩
  bindings.foldlM (init := s) fun ⟨c, newArgs⟩ t => do
    let d ← translateArgDecl newArgs t
    if p : d.val.ident ∈ newArgs.argIndexMap then
      logError d.nameLoc s!"{d.val.ident} already declared."
      pure ⟨c, newArgs⟩
    else
      pure ⟨c+1, newArgs.push d p⟩

partial def elabMetadataArgCatType (loc : SourceRange) (cat : SyntaxCat) : DeclM MetadataArgType := do
  match cat.name with
  | q`Init.Bool => pure .bool
  | q`Init.Num => pure .num
  | q`Init.Ident => pure .ident
  | q`Init.Option =>
    assert! cat.args.size = 1
    .opt <$> elabMetadataArgCatType loc cat.args[0]!
  | q`Init.FunctionTemplate => pure .functionTemplate
  | c =>
    logErrorMF loc mf!"Unsupported metadata category {c}"
    pure default

/- Flag indicating if argument was set explicitly or implicitly. -/
inductive ArgSetStatus
| implicit
| explicit

partial def checkIdentUsedArgs {argc} (argDecls : Vector ArgDeclWithLoc argc) (argLevel : Fin argc) : StateT (Std.HashMap Nat ArgSetStatus) ElabM Unit := do
  match (← get)[argLevel]? with
  | some .explicit => do
    let b := argDecls[argLevel]
    .lift <| logError b.nameLoc s!"{b.val.ident} appears multiple times."
  | some .implicit =>
    modify (·.insert argLevel .explicit)
  | none =>
    -- If this argument is an expression, then all type variables in expression
    -- can be inferred if not already assigned.
    if let .type tp := argDecls[argLevel].val.kind then
      modify fun usedArgs =>
        tp.foldBoundTypeVars usedArgs fun s idx =>
          assert! idx < argLevel
          s.insert (argLevel - (idx + 1)) .implicit
    modify (·.insert argLevel .explicit)

partial
def elabSyntaxDefAtom {argc} (argDecls : ArgDeclsMap argc) (defaultPrec : Nat) (arg : Tree) : StateT (Std.HashMap Nat ArgSetStatus) ElabM SyntaxDefAtom := do
  let .node (.ofOperationInfo info) children := arg
      | return panic! s!"Unexpected argument type {eformat arg.arg}"
  match info.op.name, children with
  | q`Init.syntaxAtomIdent, #[.node (.ofIdentInfo vInfo) #[], .node (.ofOptionInfo _) precArgs ] =>
    let v := vInfo.val
    let some argLevel := argDecls.argLevel? v
      | .lift <| logError vInfo.loc s!"Unknown variable {v}"
        return default
    let prec : Nat :=
          match precArgs with
          | #[] => defaultPrec
          | #[.node (.ofOperationInfo info) #[.node (.ofNumInfo p) #[]]] =>
            assert! info.op.name = q`Init.syntaxAtomPrec
            p.val
          | _ =>
            panic! s!"elabSyntaxDefAtom invalid prec {eformat children[1]!.arg}"
    checkIdentUsedArgs argDecls.decls argLevel
    return .ident argLevel prec
  | q`Init.syntaxAtomString, #[.node (.ofStrlitInfo info) #[] ] =>
    return .str info.val
  | q`Init.syntaxAtomIndent, #[.node (.ofNumInfo nInfo) #[], .node (.ofSeqInfo _) args ] => do
    let r ← args.mapM fun a => elabSyntaxDefAtom argDecls defaultPrec a
    return .indent nInfo.val r
  | nm, _ =>
    return panic! s!"Syntax {nm.fullName} {children.size} {eformat info.op}"

def translateSyntaxDef {argc} (argDecls : ArgDeclsMap argc) (mdTree tree : Tree) : ElabM SyntaxDef := do
  let (syntaxMetadata, success) ← runChecked <| translateOptMetadata! argDecls mdTree
  if !success then
    return default

  let prec : Nat :=
      match syntaxMetadata[q`StrataDDL.prec]? with
      | some #[.num l] => l
      | some _ => panic! "Unexpected precedence" -- FIXME
      | none => maxPrec
  let op := tree.info.asOp!.op

  assert! tree.children.size = 1
  let .node (.ofSeqInfo _) args := tree[0]!
    | panic! s!"Expected many args"

  let isLeftAssoc := q`StrataDDL.leftassoc ∈ syntaxMetadata
  let isRightAssoc := q`StrataDDL.rightassoc ∈ syntaxMetadata

  let mut atoms : Array SyntaxDefAtom := #[]
  let mut usedArgs : Std.HashMap Nat ArgSetStatus := {}
  let mut success : Bool := true
  for ⟨i, _ilt⟩ in Fin.range args.size do
    let defaultPrec :=
      if isLeftAssoc  then
        if i = 0 then
          prec - 1
        else
          prec
      else if isRightAssoc then
        if i + 1 = args.size then
          prec - 1
        else
          prec
      else
        if args.size > 1 ∧ (i = 0 ∨ i + 1 = args.size) then
          prec
        else
          0
    let ((a, newUsedArgs), thisSuccess) ← runChecked <| elabSyntaxDefAtom argDecls defaultPrec args[i] usedArgs
    usedArgs := newUsedArgs
    atoms := atoms.push a
    if !thisSuccess then
      success := false

  if !success then
    return default

  -- Check every argument is used.
  for i in Fin.range argDecls.decls.size do
    if i.val ∉ usedArgs then
      logError argDecls.decls[i].nameLoc s!"Argument is not elaborated."
      return default

  return { atoms, prec }

structure DialectContext where
  /-- Callback to load dialects dynamically upon demand. -/
  loadDialect : LoadDialectCallback
  inputContext : Parser.InputContext
  stopPos : String.Pos.Raw

structure DialectState where
  loaded : LoadedDialects
  declState : DeclState
  dialect : Dialect
  /--
  Flag to indicate dialect is missing an import.
  Missing declarations will be silenced.
  -/
  missingImport : Bool

abbrev DialectM := ReaderT DialectContext (StateRefT DialectState BaseIO)

def getCurrentDialect : DialectM Dialect := return (←get).dialect

instance :  MonadState DialectState DialectM := inferInstanceAs (MonadState DialectState (ReaderT _ _))

instance : MonadLift DeclM DialectM where
  monadLift act := fun c => do
    let s ← get
    let dialect := s.dialect
    let missingImport := s.missingImport
    let ctx : DeclContext := {
        inputContext := c.inputContext,
        stopPos := c.stopPos,
        loader := s.loaded
        missingImport := missingImport
    }
    let (r, ds) := act ctx s.declState
    set ({ loaded := ctx.loader, declState := ds, dialect := dialect, missingImport } : DialectState)
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
  logErrorMessage msg :=
    modifyDeclState fun s => { s with errors := s.errors.push msg }

private def checkTypeDeclarationArgs (tree : Tree) : ElabM (Array (Ann String SourceRange)) := do
  let (⟨_, argDecls⟩, success) ← runChecked <| translateArgDecls tree
    if !success then
      return default
  for arg in argDecls.decls do
    if !arg.val.kind.isType then
      logErrorMF arg.typeLoc mf!"Parameters for a type declaration must have category {q`Init.Type}."
      return default
  return argDecls.decls.toArray.map fun a =>
    { ann := a.nameLoc, val := a.val.ident }

def checkTreeSize (tree : Tree) (size : Nat) : Decidable (tree.children.size = size) := inferInstance

abbrev DialectElab := Tree → DialectM Unit

def elabDialectImportCommand : DialectElab := fun tree => do
  let .isTrue _ := checkTreeSize tree 1
    | panic! "Invalid tree size"
  let identTree := tree[0].info
  let name := identTree.asIdent!.val
  if name ∈ (←getDeclState).openDialectSet then
    logError identTree.loc <| s!"Dialect {name} already open."
    return
  modifyDialect fun d => { d with imports := d.imports.push name }
  let d ←
    match (← get).loaded.dialects[name]? with
    | some d =>
      pure d
    | none =>
      let loadCallback ← (·.loadDialect) <$> read
      let r ← fun _ ref => do
        let loaded := (← ref.get).loaded
        assert! "StrataDDL" ∈ loaded.dialects
        let (loaded, r) ← loadCallback loaded name
        ref.modify fun s => { s with loaded := loaded }
        pure r
      match r with
      | .ok d =>
        pure d
      | .error msg =>
        logError identTree.loc msg
        modify fun s => { s with missingImport := true }
        return
  modify fun s => { s with declState := s.declState.openLoadedDialect! s.loaded d }

private def elabCategoryCommand : DialectElab := fun tree => do
  let .isTrue p := checkTreeSize tree 1
    | return panic! "Unexpected tree size."
  let d ← getCurrentDialect
  let name := tree.children[0].info.asIdent!
  if name.val ∈ d.cache then
    logError name.loc  s!"Category {name.val} already declared."
    return
  let decl : SynCatDecl := { name := name.val, argNames := #[] }
  addDeclToDialect (.syncat decl)
  addTypeOrCatDecl d.name (.syncat decl)
  modifyDeclState (·.addSynCat! d.name decl)

/- Add a new operator. -/
def elabOpCommand : DialectElab := fun tree => do
  let .isTrue _ := checkTreeSize tree 6
    | return panic! "Unexpected tree size."
  let d ← getCurrentDialect
  let nameInfo := tree[0].info.asIdent!
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.loc s!"{name} already declared."; return

  let argDeclsTree := tree[1]
  let (⟨_, argDeclMap⟩, argDeclsSuccess) ← runElab <| runChecked <| translateArgDecls argDeclsTree

  let categoryTree := tree[2]
  let (category, categorySuccess) ← runElab <| runChecked <| translateSyntaxCat categoryTree.asBindingType!

  let opMetadataTree := tree[3]
  let (opMetadata, opMetadataSuccess) ← runElab <| runChecked <| translateOptMetadata! argDeclMap opMetadataTree

  if !argDeclsSuccess then
    return

  let opMdTree := tree[4]
  let opStxTree := tree[5]
  let (syntaxDef, opStxSuccess) ← runElab <| runChecked <| translateSyntaxDef argDeclMap opMdTree opStxTree

  -- FIXME. Change this to use stxArgDecls so we get better error messages.
  let argDecls := ArgDecls.ofArray <| argDeclMap.decls.toArray.map (·.val)
  let (newBindings, newBindingErrors) := parseNewBindings opMetadata argDecls
  for err in newBindingErrors do
    logError opMetadataTree.info.loc err

  if !categorySuccess then
    return
  if !opStxSuccess then
    return

  if category.args.size > 0 then
      logError categoryTree.info.loc s!"Expected atomic category"
      return
  let category := category.name

  let ctx := (←getDeclState).fixedParsers
  let ident : QualifiedIdent := { dialect := d.name, name }
  match ctx.opSyntaxParser category ident argDecls syntaxDef with
  | .error msg =>
    logErrorMF opStxTree.info.loc msg
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
    syntaxDef := syntaxDef,
    metadata := opMetadata,
    newBindings := newBindings
  }
  addDeclToDialect (.op decl)

private def elabTypeCommand : DialectElab := fun tree => do
  let .isTrue _ := checkTreeSize tree 2
    | return panic! "Unexpected tree size."
  let d ← getCurrentDialect

  -- Get arguments
  let (decl, success) ← runElab <| runChecked <| do
    -- Get name
    let .node (.ofIdentInfo nameInfo) _ := tree[0]
      | panic! "Expected identifier"
    let name := nameInfo.val
    if name ∈ d.cache then
      logError nameInfo.loc  s!"{name} already declared."
    let args ← checkTypeDeclarationArgs tree[1]
    pure ({ name, argNames := args } : TypeDecl)
  if success then
    addTypeOrCatDecl d.name (.type decl)
    addDeclToDialect (.type decl)

/- Evaluate a function. -/
def elabFnCommand : DialectElab := fun tree => do
  let .isTrue _ := checkTreeSize tree 6
    | return panic! "Unexpected tree size."

  let d ← getCurrentDialect
  let .ofIdentInfo nameInfo := tree[0].info
    | panic! "Expected identifier"
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.loc s!"{name} already declared."; return

  let argsTree := tree[1]!
  let (⟨argc, argDeclsMap⟩, argDeclsSuccess) ← runElab <| runChecked <| translateArgDecls argsTree
  let argDecls := ArgDecls.ofArray <| argDeclsMap.decls.toArray.map (·.val)

  let returnTypeTree := tree[2].asBindingType!
  let (result, resultSuccess) ← runElab <| runChecked <| translatePreType argDeclsMap returnTypeTree

  let opMetadataTree := tree[3]
  let (opMetadata, opMetadataSuccess) ← runElab <| runChecked <| translateOptMetadata! argDeclsMap opMetadataTree

  if !argDeclsSuccess then
    return

  let opMdTree := tree[4]
  let opStxTree := tree[5]
  let (opStx, stxSuccess) ← runElab <| runChecked <| translateSyntaxDef argDeclsMap opMdTree opStxTree

  if !stxSuccess then
    return

  let ident : QualifiedIdent := { dialect := d.name, name }
  match (←getDeclState).fixedParsers.opSyntaxParser q`Init.Expr ident argDecls opStx with
  | .error msg =>
    logErrorMF tree.info.loc msg
  | .ok _ =>
    if !resultSuccess then
      return
    if !opMetadataSuccess then
      return
    let decl : FunctionDecl := {
      name,
      argDecls,
      result := result
      syntaxDef := opStx
      metadata := opMetadata
    }
    addDeclToDialect (.function decl)

def elabMdCommand : DialectElab := fun tree => do
  let .isTrue p := checkTreeSize tree 2
    | return panic! "Unexpected tree size."
  let d ← getCurrentDialect

  let .ofIdentInfo nameInfo := tree[0].info
    | panic! "Expected identifier"
  let name := nameInfo.val
  if name ∈ d.cache then
    logError nameInfo.loc s!"{name} already declared."; return

  let optBindingsTree := tree[1]

  let (argDecls, success) ← runChecked <| do
        let bindings := optBindingsTree.optBindings!
        let mut params : Std.HashSet String := {}
        let mut argTypes := Array.mkEmpty bindings.size
        for c in bindings do
          let (nameInfo, tpTree, _) := c.binding!
          if nameInfo.val ∈ params then
            logError nameInfo.loc s!"{nameInfo.val} already declared."
          params := params.insert nameInfo.val

          let (c, success) ← runElab <| runChecked <| translateSyntaxCat tpTree
          let mdType ←
            if success then
              elabMetadataArgCatType tpTree.info.loc c
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
  assert! "StrataDDL" ∈ (← get).loaded.dialects
  let (mtree, success) ← MonadLift.monadLift <| runChecked <| elabCommand leanEnv
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

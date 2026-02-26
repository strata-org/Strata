/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Elab.DeclM
public import Strata.DDM.Elab.Tree

import all Strata.DDM.Util.Array
import all Strata.DDM.Util.Fin
import all Strata.DDM.Util.Lean
import Strata.DDM.HNF

open Lean (
    Message
    Name
    Syntax
    nullKind
  )
open Strata.Parser (DeclParser InputContext)

public section
namespace Strata

namespace TypeExprF

/-
This applies global context to instantiate types and variables.

Free type alias variables bound to alias
-/
protected def instType {α} (d : TypeExprF α) (bindings : Array (TypeExprF α)) : TypeExprF α := Id.run <|
  d.instTypeM fun n idx =>
    if p : idx < bindings.size then
      pure <| bindings[bindings.size - (idx+1)]
    else
      .bvar n (idx - bindings.size)

end TypeExprF

/--
Get the kind as a qualified identifier.
-/
def qualIdentKind (stx : Syntax) : Option QualifiedIdent :=
  if let .str (.str .anonymous dialect) name := stx.getKind then
    some { dialect, name }
  else
    none

partial def expandMacros (m : DialectMap) (f : PreType) (args : Nat → Option Arg) : Except Unit TypeExpr :=
  match f with
  | .ident loc i a => .ident loc i <$> a.mapM fun e => expandMacros m e args
  | .arrow loc a b => .arrow loc <$> expandMacros m a args <*> expandMacros m b args
  | .fvar loc i a => .fvar loc i <$> a.mapM fun e => expandMacros m e args
  | .bvar loc idx => pure (.bvar loc idx)
  | .tvar loc name => pure (.tvar loc name)
  | .funMacro loc i r => do
    let r ← expandMacros m r args
    match args i with
    | none =>
      .error ()
    | some a =>
      let addType (tps : Array TypeExpr) loc _ s args : Array TypeExpr :=
        match resolveBindingIndices m loc s args with
        | some (.expr tp) => tps.push tp
        | some (.type _ _) => panic! s!"Expected binding to be expression."
        | none => tps
      let argTypes := foldOverArgBindingSpecs m addType (init := #[]) a
      pure <| argTypes.foldr (init := r) (.arrow loc)

namespace Elab

namespace TypingContext

/--
This expands type aliases appearing at the head of the term so
the head is in a normal form.
-/
partial def hnf (tctx : TypingContext) (e : TypeExpr) : TypeExpr :=
  match e with
  | .arrow .. | .ident .. | .tvar .. => e
  | .fvar _ idx args =>
    let gctx := tctx.globalContext
    match gctx.kindOf! idx with
    | .expr _ => panic! "Type free variable bound to expression."
    | .type params (some d) =>
      assert! params.length = args.size
      assert! !d.hasUnboundVar (bindingCount := args.size)
      hnf (.empty gctx) (d.instType args)
    | .type _ none => e
  | .bvar _ idx =>
    match tctx.bindings[tctx.bindings.size - 1 - idx]!.kind with
    | .type _ params (some d) =>
      assert! params.isEmpty
      assert! d.isGround
      hnf (tctx.drop (idx + 1)) d
    | .type _ _ none => e
    | .tvar _ _ => e
    | _ => panic! "Expected a type"

/--
Attempt to interpret `e` as a `n`-ary function, and
return the type of the arguments along with the return type if possible,
or `error (args, r)` where `args` is an array with size `args.size < n` and `r`
is the resulting type.
-/
def applyNArgs (tctx : TypingContext) (e : TypeExpr) (n : Nat) := aux #[] e
  where aux (args : Array TypeExpr) (e : TypeExpr) : Except (Array TypeExpr × TypeExpr) (Vector TypeExpr n × TypeExpr) :=
    if argsLt : args.size < n then
      match tctx.hnf e with
      | .arrow _ a r => aux (args.push a) r
      | e => .error (args, e)
    else
      if argsGt : args.size > n then
        .ok (⟨args.take n, by simp; omega⟩, e)
      else
        .ok (⟨args, by omega⟩, e)

end TypingContext

def commaPrec := 30

def elabIdent (stx : Syntax) : String :=
  assert! stx.getKind = `ident
  match stx with
  | .ident _ _ (.str .anonymous name) _ => name
  | _               => panic! s!"Unexpected syntax {stx}: ident expected."

-----------------------------------------------------------------------
-- Expression elaboration

structure ElabContext where
  dialects : DialectMap
  openDialectSet : Std.HashSet DialectName
  /-- Map for looking up types and categories by name. -/
  typeOrCatDeclMap : TypeOrCatDeclMap
  /-- Map for looking up metadata by name. -/
  metadataDeclMap : MetadataDeclMap
  /-- Syntax elaboration functions. -/
  syntaxElabs : SyntaxElabMap
  inputContext : InputContext
  globalContext : GlobalContext
  /-- Flag to indicate we are missing an import (silences some warnings)-/
  missingImport : Bool

structure ElabState where
  -- Errors found in elaboration.
  errors : Array Message := #[]

@[reducible, expose]
def ElabM α := ReaderT ElabContext (StateM ElabState) α

instance : ElabClass ElabM where
  getInputContext := return (←read).inputContext
  getDialects := return (←read).dialects
  getOpenDialects := return (←read).openDialectSet
  getGlobalContext := return (←read).globalContext
  getErrorCount := return (←get).errors.size
  logErrorMessage msg :=
    modify fun s => { s with errors := s.errors.push msg }

section

abbrev FailureArray := Array (Syntax × String)

inductive MaybeQualifiedIdent where
| qid : QualifiedIdent → MaybeQualifiedIdent
| name : String → MaybeQualifiedIdent
deriving Inhabited

def resolveTypeBinding (tctx : TypingContext) (loc : SourceRange) (name : String)
    (binding : TypingContext.VarBinding) (args : Array Tree) : ElabM Tree := do
  match binding with
  | .bvar idx k =>
    if let some a := args[0]? then
      logErrorMF a.info.loc mf!"Unexpected arguments to {name}."
      return default
    if let .type loc [] _ := k then
      let info : TypeInfo := { inputCtx := tctx, loc := loc, typeExpr := .bvar loc idx, isInferred := false }
      return .node (.ofTypeInfo info) #[]
    else if let .tvar loc tvarName := k then
      let info : TypeInfo := { inputCtx := tctx, loc := loc, typeExpr := .tvar loc tvarName, isInferred := false }
      return .node (.ofTypeInfo info) #[]
    else
      logErrorMF loc mf!"Expected a type instead of {k}"
      return default
  | .fvar fidx k =>
    match k with
    | .expr tp =>
      logErrorMF loc mf!"Expected a type instead of expression with type {tp}."
      return default
    | .type params _ =>
      let params := params.toArray
      -- Check args matches kind
      if params.size = args.size then
        let mut tpArgs : Array TypeExpr := .mkEmpty args.size
        let mut children : Array Tree := .mkEmpty args.size
        for i in Fin.range args.size do
          let c := args[i]
          let .ofTypeInfo cinfo := c.info
            | logErrorMF c.info.loc mf!"Expected type"
          tpArgs := tpArgs.push cinfo.typeExpr
          children := children.push c
        let tp :=  .fvar loc fidx tpArgs
        let info : TypeInfo := { inputCtx := tctx, loc := loc, typeExpr := tp, isInferred := false }
        return .node (.ofTypeInfo info) children
      else if let some a := args[params.size]? then
        logErrorMF a.info.loc mf!"Unexpected argument to {name}."
        return default
      else
        logErrorMF loc mf!"{name} expects {params.size} arguments."
        return default

/--
This translate a possibly qualified identifier into a declaration in an
open dialect.
-/
def resolveTypeOrCat (loc : SourceRange) (tpId : MaybeQualifiedIdent) : ElabM (Option (QualifiedIdent × TypeOrCatDecl)) := do
  match tpId with
  | .qid qid =>
    let decls := (← read).typeOrCatDeclMap.get qid.name
    let decls := decls.filter fun (dialect, _) => dialect = qid.dialect
    match decls[0]? with
    | none =>
      let isSilent := (←read).missingImport
      logErrorMF loc mf!"Undeclared type or category {qid}." (isSilent := isSilent)
      return none
    | some (_, decl) =>
      assert! decls.size = 1
      return some (qid, decl.val)
  | .name name =>
    let m := (← read).typeOrCatDeclMap
    let decls:= m.get name
    match decls[0]? with
    | none => do
      let isSilent := (←read).missingImport
      logErrorMF loc mf!"Undeclared type or category {name}." (isSilent := isSilent)
      return none
    | some (d, decl) =>
      if let some (candD, _) := decls[1]? then
        assert! d ≠ candD
        logError loc s!"{name} is ambiguous: declared in {d} and {candD}."
        return none
      else
        return some ({ dialect := d, name }, decl.val)

def translateQualifiedIdent (t : Tree) : MaybeQualifiedIdent :=
  let op := t.info.asOp!.op
  let args := op.args
  match op.name, sz : args.size with
  | q`Init.qualifiedIdentImplicit, 1 => Id.run do
    let .ident _ name := args[0]
      | return panic! "Expected ident"
    let name := name.dropPrefix "«" |>.dropSuffix "»" |>.toString
    match name.splitOn "." with
    | [dialect, rest] => .qid { dialect, name := rest }
    | _ => .name name
  | q`Init.qualifiedIdentExplicit, 2 => Id.run do
    let .ident _ dialect := args[0]
      | return panic! "Expected ident"
    let .ident _ name := args[1]
      | return panic! "Expected ident"
    .qid { dialect, name }
  | q`Init.qualifiedIdentType, 0 =>
    .qid { dialect := "Init", name := "Type" }
  | name, _ =>
    panic! s!"Unknown qualified ident {name.fullName}"

def asTypeInfo (tree : Tree) : ElabM TypeInfo := do
  match tree.info with
  | .ofTypeInfo info =>
    return info
  | _ =>
    logError tree.info.loc "Expected type."
    return default

def checkArgSize {α} [ToStrataFormat α] (loc : SourceRange) (name : α) (expected : Nat) (args : Array Tree) : ElabM Unit := do
  if p : expected < args.size then
    logErrorMF args[expected].info.loc mf!"Unexpected argument to {name}."
  else if expected > args.size then
    logErrorMF loc mf!"{name} expects {expected} arguments."

/--
This resolves a type identifer using the name of the type (as `name`) and the
arguments
-/
def translateTypeIdent (elabInfo : ElabInfo) (qualIdentInfo : Tree) (args : Array Tree) : ElabM Tree := do
  let loc := qualIdentInfo.info.loc
  let tctx := qualIdentInfo.info.inputCtx
  let tpId := translateQualifiedIdent qualIdentInfo

  if let .name name := tpId then
    if let some binding := tctx.lookupVar name then
      return ← resolveTypeBinding tctx loc name binding args
  let some (ident, decl) ← resolveTypeOrCat loc tpId
    | return default

  match decl with
  | .type decl =>
    checkArgSize loc ident decl.argNames.size args
    let tpArgs ← args.mapM fun a => return (← asTypeInfo a).typeExpr
    let tp := .ident loc ident tpArgs
    let info : TypeInfo := { toElabInfo := elabInfo, typeExpr := tp, isInferred := false }
    return .node (.ofTypeInfo info) args
  | .syncat decl =>
    let (_, success) ← runChecked <| checkArgSize loc ident decl.argNames.size args
    if !success then
      return default
    let mut scArgs : Array SyntaxCat := .emptyWithCapacity args.size
    for a in args do
      match a.info with
      | .ofCatInfo info =>
        scArgs := scArgs.push info.cat
      | _ =>
        logError a.info.loc "Expected category."
        return default
    let sc : SyntaxCat := SyntaxCatF.mk loc ident scArgs
    let info : CatInfo := { toElabInfo := elabInfo, cat := sc }
    return .node (.ofCatInfo info) args

end

def withBindings (b : Bindings) (fmt : StrataFormat) : StrataFormat :=
  fmt.withState fun s => b.toArray.foldl (init := s) (·.pushBinding ·.ident)

/--
This expands type aliases appearing at the head of the term so
the root is in a normal for,.

N.B. This expects that macros have already been expanded in e.
-/
partial def headExpandTypeAlias (gctx : GlobalContext) (e : TypeExpr) : TypeExpr :=
  match e with
  | .arrow .. | .ident .. | .bvar .. | .tvar .. => e
  | .fvar _ idx args =>
    match gctx.kindOf! idx with
    | .expr _ => panic! "Type free variable bound to expression."
    | .type params (some d) =>
      assert! params.length = args.size
      assert! !d.hasUnboundVar (bindingCount := args.size)
      headExpandTypeAlias gctx (d.instType args)
    | .type _ none => e

/--
This checks that two types `itype` and `rtype` are equivalent.

In this context, `itype` refers to a type inferred from an operator argument
at position `stx` and `rtype` refers to a type inferred or specifed by a previous
argument.
-/
partial def checkExpressionType (tctx : TypingContext) (itype rtype : TypeExpr) : ElabM Bool := do
  let itype := tctx.hnf itype
  let rtype := tctx.hnf rtype
  match itype, rtype with
  -- tvar matches anything (dialect responsible for typechecking)
  | .tvar _ n1, .tvar _ n2 => return n1 == n2
  | .tvar _ _, _ => return true
  | _, .tvar _ _ => return true
  | .ident _ iq ia, .ident _ rq ra =>
    if p : iq = rq ∧ ia.size = ra.size then do
      for i in Fin.range ia.size do
        if !(← checkExpressionType tctx ia[i] ra[i]) then
          return false
      return true
    else
      return false
  | .bvar _ ii, .bvar _ ri =>
    return ii = ri
  | .fvar _ ii ia, .fvar _ ri ra =>
    if p : ii = ri ∧ ia.size = ra.size then do
      for i in Fin.range ia.size do
        if !(← checkExpressionType tctx ia[i] ra[i]) then
          return false
      return true
    else
      return false
  | .arrow _ ia ir, .arrow _ ra rr =>
    return (← checkExpressionType tctx ia ra)
        && (← checkExpressionType tctx ir rr)
  | _, _ =>
    pure false

mutual

partial def unifyTypeVectors
  {argc : Nat}
  (b : Vector ArgDecl argc)
  (argLevel0 : Fin argc)
  (ea : Array TypeExpr)
  (tctx : TypingContext)
  (exprSyntax : Syntax)
  (ia : Array TypeExpr)
  (args : Vector (Option Tree) argc)
  : ElabM (Vector (Option Tree) argc) := do
  assert! ea.size = ia.size
  let mut res := args
  for i in Fin.range ea.size do
    res ← unifyTypes b argLevel0 ea[i] tctx exprSyntax ia[i]! res
  return res

/--
This compares the inferred type against the expected type for an argument to check if the
argument value is well-typed and determine if additional type variables can be automatically
inferred.

- `b` is the bindings for the expression/operator this is for.
- `argLevel` refers to the index of the argument in `args`
- `expectedType` is the type of the argument for the operation/expression.  Bound
  variables in it may refer to args in `args` less than `argIndex`.
- `tctx` is the typing context for `inferredType`.
- `exprSyntax` is the syntax of the expression/operator this is for.  Used for positions in
   error reporting.
- `inferredType` is the type inferred from bottom up type inference.
   Bound variables in it may refere to bound variables in `tctx`.
- `args` is the current arguments.  These may be refined by unifyTypes and the
   new arguments are returned.
-/
partial def unifyTypes
    {argc : Nat}
    (b : Vector ArgDecl argc)
    (argLevel0 : Fin argc)
    (expectedType : TypeExpr)
    (tctx : TypingContext)
    (exprSyntax : Syntax)
    (inferredType : TypeExpr)
    (args : Vector (Option Tree) argc)
    : ElabM (Vector (Option Tree) argc) := do
  let ⟨argLevel, argLevelP⟩ := argLevel0
  -- Expand defined free vars at root to get head norm form
  let expectedType := headExpandTypeAlias tctx.globalContext expectedType
  assert! exprSyntax.getKind != `null
  let some exprLoc := mkSourceRange? exprSyntax
    | panic! "unifyTypes missing source location"
  match expectedType with
  | .ident _ eid ea =>
    let inferredHead := tctx.hnf inferredType
    match inferredHead with
    | .ident _ iid ia =>
      if eid != iid then
        logErrorMF exprLoc mf!"Encountered {inferredHead} expression when {expectedType} expected."
        return args
      assert! ea.size = ia.size
      unifyTypeVectors b argLevel0 ea tctx exprSyntax ia args
    | .tvar _ _ =>
      -- tvar inferred types are passed through; type inference will catch mismatches
      pure args
    | _ =>
      logErrorMF exprLoc mf!"Encountered {inferredHead} expression when {expectedType} expected."
      return args
  | .fvar _ eid ea =>
    match tctx.hnf inferredType with
    | .fvar _ iid ia =>
      if eid != iid then
        logErrorMF exprLoc mf!"Encountered {inferredType} expression when {expectedType} expected."
        return args
      assert! ea.size = ia.size
      unifyTypeVectors b argLevel0 ea tctx exprSyntax ia args
    | .tvar _ _ =>
      -- tvar inferred types are passed through; type inference will catch mismatches
      pure args
    | ih =>
      logErrorMF exprLoc mf!"Encountered {ih} expression when {expectedType} expected."
      return args
  | .bvar _ idx =>
    let .isTrue idxP := inferInstanceAs (Decidable (idx < argLevel))
      | return panic! "Invalid index"
    let typeLevel := argLevel - (idx + 1)
    -- Verify type level is a type parameter.
    assert! b[typeLevel].kind.isType

    match args[typeLevel] with
    | none => do
      let info : TypeInfo := {
        loc := exprLoc
        inputCtx := tctx
        typeExpr := inferredType
        isInferred := true
      }
      return args.set typeLevel (some (.node (.ofTypeInfo info) #[]))
    | some t => do
      let .ofTypeInfo info := t.info
        | panic! "Expected type info"
      if !(← checkExpressionType tctx inferredType info.typeExpr) then
        logErrorMF exprLoc mf!"Expression has type {withBindings tctx.bindings (mformat inferredType)} when {withBindings tctx.bindings (mformat info.typeExpr)} expected."
      pure args
  | .tvar _ _ =>
    -- tvar nodes are passed through without attempting unification
    pure args
  | .arrow _ ea er =>
    match inferredType with
    | .ident .. | .bvar .. | .fvar .. =>
      logErrorMF exprLoc mf!"Expected {expectedType} when {inferredType} found"
      pure args
    | .tvar _ _ =>
      -- tvar inferred types are passed through; type inference will catch mismatches
      pure args
    | .arrow _ ia ir =>
      let res ← unifyTypes b argLevel0 ea tctx exprSyntax ia args
      unifyTypes b argLevel0 er tctx exprSyntax ir res

end

abbrev ElabArgFn := TypingContext → Syntax → ElabM Tree

private def elabManyElement (f : TypingContext → Syntax → ElabM Tree)
    : Array Tree × TypingContext → Syntax → ElabM (Array Tree × TypingContext)
| (args, tctx), astx =>  do
  let (t,success) ← runChecked <| f tctx astx
  let rtctx := if success then t.resultContext else tctx
  pure (args.push t, rtctx)

def elabOption (f : ElabArgFn) : ElabArgFn := fun tctx stx =>
  if stx.matchesNull 0 then do
    let some loc := mkSourceRange? stx
      | panic! "elabOption missing source location"
    let info : OptionInfo := { loc := loc, inputCtx := tctx }
    pure <| .node (.ofOptionInfo info) #[]
  else do
    assert! stx.matchesNull 1
    let astx := stx.getArg 0
    let some loc := mkSourceRange? stx
      | panic! "elabOption missing source location"
    let info : OptionInfo := { loc := loc, inputCtx := tctx }
    let tree ← f tctx astx
    pure <| .node (.ofOptionInfo info) #[tree]

def evalBindingNameIndex (trees : Vector Tree n) (idx : DebruijnIndex n) : String :=
  match trees[idx.toLevel].info with
  | .ofIdentInfo e => e.val
  | a => panic! s!"Expected ident at {idx.val} {repr a}"

/--
This collects the results of applying a function `f` to the bindings added to the
resulting context of `tree` after the initial number of bindings given by
`initialScope`.
-/
def collectNewBindingsM [Monad m] (initialScope : Nat) (tree : Tree)
    (f : SourceRange → Binding → m α) : m (Array α) := do
  assert! (initialScope ≤ tree.info.inputCtx.bindings.size)
  let loc := tree.info.loc
  let bindings := tree.resultContext.bindings.toArray
  let init : Array α := .mkEmpty (bindings.size - initialScope)
  bindings.foldlM (init := init) (start := initialScope) fun r b => r.push <$> f loc b

def elabArgIndex {α} {n}
    (initialScope : Nat)
    (trees : Vector Tree n)
    (argsIndex : Option (DebruijnIndex n))
    (f : SourceRange → Binding → ElabM α) :
    ElabM (Array α) := do
  match argsIndex with
  | none => pure #[]
  | some idx => collectNewBindingsM initialScope trees[idx.toLevel] f

/--
Parse TypeApp and TypeParen expressions to get Init.TypeExpr into head-format form.
-/
def flattenTypeApp (arg : Tree) (args : Array Tree) : Tree × Array Tree :=
  match arg with
  | .node (.ofOperationInfo info) children =>
    if case0 : info.op.name = q`Init.TypeApp ∧ children.size = 2 then
      flattenTypeApp children[0] (args.push children[1])
    else if case1 : info.op.name = q`Init.TypeParen ∧ children.size = 1 then
      flattenTypeApp children[0] args
    else
      (arg, args)
  | _ =>
    (arg, args)
termination_by arg

private theorem List_size1 [SizeOf α] {as : List α} (szp : as.length = 1) :
  sizeOf as = sizeOf as[0] + 2 := by
  match as with
  | [] => simp at szp
  | a :: r =>
    simp at szp
    simp [szp]
    omega

private theorem List_size2 [SizeOf α] {as : List α} (szp : as.length = 2) :
  sizeOf as = sizeOf as[0] + sizeOf as[1] + 3 := by
  match as with
  | [] => simp at szp
  | [one] => simp at szp
  | a :: b :: r =>
    simp at szp
    simp [szp]
    omega

theorem Array_size1 [SizeOf α] {as : Array α} (szp : as.size = 1) :
  sizeOf as = sizeOf as[0] + 3 := by
  match as with
  | ⟨ls⟩ =>
    simp [List_size1 szp]
    omega

theorem Array_size2 [SizeOf α] {as : Array α} (szp : as.size = 2) :
  sizeOf as = sizeOf as[0] + sizeOf as[1] + 4 := by
  match as with
  | ⟨ls⟩ =>
    simp [List_size2 szp]
    omega

theorem Pair_size [SizeOf α] [SizeOf β] (a : α) (b : β): sizeOf (a, b) = 1 + sizeOf a + sizeOf b := by
  simp

theorem flattenTypeApp_size (arg : Tree) (args : Array Tree) :
  sizeOf (flattenTypeApp arg args) ≤ sizeOf arg + sizeOf args + 1 := by
  match arg with
  | .node info children =>
    -- The simp and omega gets rid of all goals except operationInfo
    cases info  <;> (simp [flattenTypeApp] ; try omega)
    case ofOperationInfo info0 =>
      split
      case isTrue p =>
        have childrenP : sizeOf children[0] < sizeOf children := by decreasing_tactic
        have childBound := flattenTypeApp_size children[0] (args.push children[1])
        simp at childBound
        simp [Array_size2 p.right]
        omega
      case isFalse p =>
        split
        case isTrue q =>
          have childBound := flattenTypeApp_size children[0] args
          simp [Array_size1 q.right]
          omega
        case isFalse q =>
          simp
          omega
  termination_by sizeOf arg

def logInternalError {m} [ElabClass m] (loc : SourceRange) (msg : String) : m Unit :=
  logError loc msg

/--
Evaluate the tree as a type expression.
-/
partial def translateSyntaxCat (tree : Tree) : ElabM SyntaxCat := do
  let (⟨argInfo, argChildren⟩, args) := flattenTypeApp tree #[]
  let op :=
        match argInfo with
        | .ofOperationInfo info => info.op.name
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match op with
  | q`Init.TypeIdent => do
    assert! argChildren.size = 1
    let nameTree := argChildren[0]!
    let tpId := translateQualifiedIdent nameTree
    let nameLoc := nameTree.info.loc
    assert! !nameLoc.isNone
    let some (name, decl) ← resolveTypeOrCat nameLoc tpId
      | return default
    match decl with
    | .syncat decl =>
      checkArgSize argInfo.loc name decl.argNames.size args
      let scArgs ← args.mapM translateSyntaxCat
      pure { ann := nameLoc, name := name, args := scArgs }
    | _ =>
      logError nameLoc s!"Expected category"; pure default

  | q`StrataDDL.TypeFn => do
    logError argInfo.loc s!"Expected category"
    return default

  | _ =>
    logInternalError argInfo.loc s!"translateSyntaxCat given invalid op {op}"
    return default

/--
Evaluate the tree as a type expression.
-/
def translateTypeExpr (tree : Tree) : ElabM TypeExpr := do
  match feq : flattenTypeApp tree #[] with
  | (⟨argInfo, argChildren⟩, args) =>
  let opInfo :=
        match argInfo with
        | .ofOperationInfo info => info
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  let op := opInfo.op.name
  match op with
  | q`Init.TypeIdent => do
    let isTrue p := inferInstanceAs (Decidable (argChildren.size = 1))
      | return panic! "Invalid arguments to Init.TypeIdent"
    let ident := argChildren[0]
    let tpId := translateQualifiedIdent ident
    let some (qname, decl) ← resolveTypeOrCat ident.info.loc tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize opInfo.loc qname decl.argNames.size args
      let args ← args.attach.mapM fun ⟨a, _⟩ =>
        translateTypeExpr a
      return .ident opInfo.loc qname args
    | _ =>
      logError ident.info.loc s!"Expected type"; pure default
  | q`Init.TypeArrow => do
    let isTrue p := inferInstanceAs (Decidable (argChildren.size = 2))
      | return panic! "Invalid arguments to Init.TypeArrow"
    let aTree := argChildren[0]
    let rTree := argChildren[1]
    let aType ← translateTypeExpr aTree
    let rType ← translateTypeExpr rTree
    return .arrow opInfo.loc aType rType
  | q`StrataDDL.TypeFn =>
    logError opInfo.loc s!"Macros not supported"
    return default
  | nm =>
    logInternalError opInfo.loc s!"translateTypeExpr given unknown constructor {nm}"
    return default
  termination_by tree
  decreasing_by
    · have argsP : sizeOf args ≤ sizeOf tree := by
          have p := flattenTypeApp_size tree #[]
          have q := Array.sizeOf_min argChildren
          simp [feq] at p
          omega
      have p : sizeOf a < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have argcP : sizeOf argChildren < sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min args
        simp [feq] at p
        omega
      have p : sizeOf argChildren[0] < sizeOf argChildren := by decreasing_tactic
      decreasing_tactic
    · have argcP : sizeOf argChildren < sizeOf tree := by
        have p := flattenTypeApp_size tree #[]
        have q := Array.sizeOf_min args
        simp [feq] at p
        omega
      have p : sizeOf argChildren[1] < sizeOf argChildren := by decreasing_tactic
      decreasing_tactic

/--
Evaluate the tree as a type expression.
-/
def translateBindingKind (tree : Tree) : ElabM BindingKind := do
  let (⟨argInfo, argChildren⟩, args) := flattenTypeApp tree #[]
  let opInfo :=
        match argInfo with
        | .ofOperationInfo info => info
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match opInfo.op.name, szp : argChildren.size with
  | q`Init.TypeIdent, 1 => do
    let nameTree := argChildren[0]
    let tpId := translateQualifiedIdent nameTree
    let nameLoc := nameTree.info.loc
    let tctx := nameTree.info.inputCtx
    -- First check if the type is in the GlobalContext (for user-defined types like datatypes)
    if let .name name := tpId then
      if let some binding := tctx.lookupVar name then
        let tpArgs ← args.mapM translateTypeExpr
        match binding with
        | .fvar fidx k =>
          match k with
          | .type params _ =>
            let params := params.toArray
            if params.size = tpArgs.size then
              return .expr (.fvar nameLoc fidx tpArgs)
            else if let some a := tpArgs[params.size]? then
              logErrorMF a.ann mf!"Unexpected argument to {name}."
              return default
            else
              logErrorMF nameLoc mf!"{name} expects {params.size} arguments."
              return default
          | .expr _ =>
            logErrorMF nameLoc mf!"Expected a type instead of expression {name}."
            return default
        | .bvar idx k =>
          if let .type loc [] _ := k then
            if tpArgs.isEmpty then
              return .expr (.bvar loc idx)
            else
              logErrorMF nameLoc mf!"Unexpected arguments to type variable {name}."
              return default
          else if let .tvar loc tvarName := k then
            if tpArgs.isEmpty then
              return .expr (.tvar loc tvarName)
            else
              logErrorMF nameLoc mf!"Unexpected arguments to type variable {name}."
              return default
          else
            logErrorMF nameLoc mf!"Expected a type instead of {k}"
            return default
    -- Dialect-defined types
    let some (name, decl) ← resolveTypeOrCat nameLoc tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize opInfo.loc name decl.argNames.size args
      let args ← args.mapM translateTypeExpr
      return .expr (.ident opInfo.loc name args)
    | .syncat decl =>
      checkArgSize opInfo.loc name decl.argNames.size args
      let r : SyntaxCat := .atom nameLoc name
      let scArgs ← args.mapM translateSyntaxCat
      return .cat { ann := opInfo.loc, name := name, args := scArgs }
  | q`Init.TypeArrow, 2 => do
    let aType ← translateTypeExpr argChildren[0]
    let rType ← translateTypeExpr argChildren[1]
    pure <| .expr <| .arrow opInfo.loc aType rType
  | q`StrataDDL.TypeFn, _ => do
    logError argInfo.loc s!"Macros not supported"
    pure default
  | _, _ =>
    logInternalError argInfo.loc s!"translateArgDeclKind given invalid kind {opInfo.op.name}"
    return default

/-- Extract type parameter names from a bindings argument. -/
def elabTypeParams {n} (initSize : Nat) (args : Vector Tree n)
    (idx : Option (DebruijnIndex n)) : ElabM (List String) := do
  let params ← elabArgIndex initSize args idx fun argLoc b => do
    match b.kind with
    | .type _ [] _ => pure ()
    | .tvar _ _ => pure ()
    | .type .. | .expr _ | .cat _ =>
      logError argLoc s!"{b.ident} must have type Type instead of {repr b.kind}."
    return b.ident
  pure params.toList

/--
Construct a binding from a binding spec and the arguments to an operation.
-/
def evalBindingSpec
    {bindings}
    (loc : SourceRange)
    (initSize : Nat)
    (b : BindingSpec bindings)
    (args : Vector Tree bindings.size)
    : ElabM Binding := do
  match b with
  | .value b =>
    let ident := evalBindingNameIndex args b.nameIndex
    let (bindings, success) ← runChecked <| elabArgIndex initSize args b.argsIndex fun argLoc b =>
          match b.kind with
          | .expr tp =>
            pure (some (b.ident, tp))
          | .tvar .. =>
            pure none
          | .type .. | .cat _ => do
            logError argLoc "Expecting expressions in variable binding"
            pure none
    if !success then
      return default
    let bindings := bindings.filterMap id
    let typeTree := args[b.typeIndex.toLevel]
    let kind ←
          match typeTree.info with
          | .ofTypeInfo info =>
            pure <| .expr (.mkFunType loc bindings info.typeExpr)
          | .ofCatInfo info =>
            if !b.allowCat then
              panic! s!"Cannot bind {ident} unexpected category {repr info.cat}"
            else if !bindings.isEmpty then
              panic! s!"Arguments not allowed on category."
            else if info.cat.name == q`Init.Type then
              pure <| .type loc [] none
            else
              pure <| .cat info.cat
          | .ofOperationInfo _ => do
            translateBindingKind typeTree.asBindingType!
          | arg =>
            panic! s!"Cannot bind {ident}: Type at {b.typeIndex.val} has unexpected arg {repr arg}"
    -- TODO: Decide if new bindings for Type and Expr (or other categories) and should not be allowed?
    pure { ident, kind }
  | .type b =>
    let ident := evalBindingNameIndex args b.nameIndex
    let params ← elabTypeParams initSize args b.argsIndex
    let value : Option TypeExpr :=
          match b.defIndex with
          | none => none
          | some idx =>
            match args[idx.toLevel].info with
            | .ofTypeInfo info =>
              some info.typeExpr
            | _ =>
              panic! "Bad arg"
    pure { ident, kind := .type loc params value }
  | .datatype b =>
    let ident := evalBindingNameIndex args b.nameIndex
    let params ← elabTypeParams initSize args (some b.typeParamsIndex)
    pure { ident, kind := .type loc params none }
  | .tvar b =>
    let ident := evalBindingNameIndex args b.nameIndex
    pure { ident, kind := .tvar loc ident }

/--
Given a type expression and a natural number, this returns a
-/
def resultType! (tctx : TypingContext) (e : TypeExpr) (n : Nat) : TypeExpr :=
  match tctx.applyNArgs e n with
  | .ok (_, r) => r
  | .error (n, _) => panic! s!"{n.size} unexpected arguments to function."

/--
Returns the type of `e` in typing context `tctx`.
-/
partial def inferType (tctx : TypingContext) (e : Expr) : ElabM TypeExpr := do
  -- Compute head normal form of e.
  let ⟨f, a⟩ := e.hnf
  match f with
  | .bvar _ idx => do
    let .isTrue idxP := inferInstanceAs (Decidable (idx < tctx.bindings.size))
      | return panic! "Invalid index {idx}"
    let lvl := tctx.bindings.size - 1 - idx
    let b := tctx.bindings[lvl]
    match b.kind with
    | .expr tp =>
      -- Arguments in the type context
      return resultType! tctx (tp.incIndices (idx + 1)) a.val.size
    | _ => panic! "Expected an expression"
  | .fvar _ idx =>
    match tctx.globalContext.kindOf! idx with
    | .expr tp =>
      return resultType! tctx tp a.val.size
    | .type _ _ => panic! "Expected expression instead of type."
  | .fn _ ident => do
    let dm := (← read).dialects
    let .function decl := dm.decl! ident
      | panic! s!"Expected {ident} to be a function"
    let fnArgCount := decl.argDecls.size
    assert! fnArgCount ≤ a.val.size
    let tp := decl.result
    let mtp := expandMacros dm tp fun i =>
      assert! i < fnArgCount
      some a.val[fnArgCount - i - 1]!
    let .ok tp := mtp
        | return panic! "Unexpected expandMacros failure."
    let tp := Id.run <| tp.instTypeM fun _ i =>
        assert! i < fnArgCount
        let lvl := fnArgCount - i - 1
        match a.val[lvl]! with
        | .type tp => tp
        | arg =>
           panic! s!"Cannot instantiate type {repr tp} with args {repr a}"
    return resultType! tctx tp (a.val.size - fnArgCount)
  | .app _ f a => panic! "Invalid app in result of Expr.hnf"

/--
Given a tree from operations with category `Init.TypeExpr`, build a tree with the type or category
successfully translated.
-/
partial def translateTypeTree (arg : Tree) : ElabM Tree := do
  let (arg, args) := flattenTypeApp arg #[]
  match arg.info with
  | .ofOperationInfo info =>
    let op := info.op
    let argChildren := arg.children
    match op.name, argChildren with
    | q`Init.TypeIdent, #[opInfo] =>
      let args ← args.mapM translateTypeTree
      translateTypeIdent info.toElabInfo opInfo args
    | q`Init.TypeArrow, #[aTree, rTree] => do
      let aType ← translateTypeTree aTree
      let .ofTypeInfo aInfo := aType.info
        | logError aType.info.loc s!"Expected type"; return default
      let rType ← translateTypeTree rTree
      let .ofTypeInfo rInfo := rType.info
        | logError rType.info.loc s!"Expected type"; return default
      let tp := .arrow info.loc aInfo.typeExpr rInfo.typeExpr
      let info : TypeInfo := { toElabInfo := info.toElabInfo, typeExpr := tp, isInferred := false }
      return .node (.ofTypeInfo info) #[aType, rType]
    | _, _ =>
      logInternalError arg.info.loc s!"translateTypeTree given invalid operation {repr op}"
      return default
  | _ =>
    panic! s!"translateTypeExpr expected operator {repr arg}"

/--
Return the arguments to the given syntax declaration.

This should alway succeeed, but captures an internal error if an invariant check fails.
-/
def getSyntaxArgs (stx : Syntax) (ident : QualifiedIdent) (expected : Nat) : ElabM (Vector Syntax expected) := do
  let some loc := mkSourceRange? stx
    | panic! s!"elabOperation missing source location {repr stx}"
  let stxArgs := stx.getArgs
  let .isTrue stxArgP := inferInstanceAs (Decidable (stxArgs.size = expected))
    | logInternalError loc s!"{ident} expected {expected} arguments when {stxArgs.size} seen.\n  {repr stxArgs[0]!}"
      return default
  return ⟨stxArgs, stxArgP⟩

/-- Map a sequence category name to its separator format and child extraction function. -/
private def scopeSepFormat (name : QualifiedIdent)
    : Option (SepFormat × (Syntax → Array Syntax)) :=
  match name with
  | q`Init.Seq              => some (.none, Syntax.getArgs)
  | q`Init.CommaSepBy       => some (.comma, Syntax.getSepArgs)
  | q`Init.SpaceSepBy       => some (.space, Syntax.getSepArgs)
  | q`Init.SpacePrefixSepBy => some (.spacePrefix, Syntax.getArgs)
  | _ => none

/--
Extract type parameter names from a partially-elaborated typeParams tree.
Compares the tree's result context against the inherited binding count
to find newly introduced type/tvar bindings.
-/
private def extractParamNames (inheritedCount : Nat) (tpTree : Tree) : List String :=
  let tpCtx := tpTree.resultContext
  let newBindings := tpCtx.bindings.toArray.extract inheritedCount tpCtx.bindings.size
  let names := newBindings.filterMap fun (b : Binding) =>
    match b.kind with
    | .type _ [] _ => some b.ident
    | .tvar _ _    => some b.ident
    | _            => none
  names.toList

/-- Pre-register a batch of types in the global context.
Silently skips types that are already declared. -/
private def preRegisterTypes (gctx : GlobalContext)
    (registrations : Array (String × List String)) : GlobalContext :=
  registrations.foldl (init := gctx) fun gctx (name, params) =>
    gctx.ensureDefined name (.type params none)

/-- Look up the syntax level for a given arg level
via the precomputed `argElabIndex`. -/
private def argSyntaxLevel?
    (se : SyntaxElaborator) (argLevel : Nat) : Option Nat :=
  se.argElabIndex[argLevel]?.join.bind fun idx =>
    (se.argElaborators[idx]?).map (·.val.syntaxLevel)

mutual

partial def elabOperation (tctx : TypingContext) (stx : Syntax)
    (preElaborated : Array (Nat × Tree) := #[]) : ElabM Tree := do
  let some loc := mkSourceRange? stx
    | panic! s!"elabOperation missing source location {repr stx}"
  if stx.getKind = `choice then
    logError loc s!"Parsing ambiguity {stx}"
    return default
  let some i := qualIdentKind stx
    | return panic! s!"Unknown command {stx.getKind}"
  let some d := (←read).dialects[i.dialect]?
    | return panic! s!"Unknown dialect {i.dialect} in {stx}"
  let some decl := d.ops[i.name]?
    | return panic! (f!"unknown operation {eformat i}").pretty
  let some se := (←read).syntaxElabs[i]?
    | return panic! s!"Unknown elaborator {i.fullName}"
  let initSize := tctx.bindings.size
  let argDecls := decl.argDecls.toArray.toVector
  let (stxArgs, success) ← runChecked <| getSyntaxArgs stx i se.syntaxCount
  if not success then
    return default
  let ((args, newCtx), success) ← runChecked <|
    match se.preRegisterTypesScope with
    | some scopeArgLevel =>
      elaborateWithPreRegistration argDecls se tctx stxArgs scopeArgLevel
    | none =>
      runSyntaxElaborator argDecls se tctx stxArgs preElaborated
  if !success then
    return default
  let resultCtx ← decl.newBindings.foldlM (init := newCtx) <| fun ctx spec => do
    ctx.push <$> evalBindingSpec loc initSize spec args
  let op : Operation := { ann := loc, name := i, args := args.toArray.map (·.arg) }
  if loc.isNone then
    return panic! s!"Missing position info {repr stx}."
  let info : OperationInfo := { loc := loc, inputCtx := tctx, op, resultCtx }
  return .node (.ofOperationInfo info) args.toArray

partial def runSyntaxElaborator
  {argc : Nat}
  (argDecls : Vector ArgDecl argc)
  (se : SyntaxElaborator)
  (tctx0 : TypingContext)
  (args : Vector Syntax se.syntaxCount)
  (preElaborated : Array (Nat × Tree) := #[]) : ElabM (Vector Tree argc × TypingContext) := do
  let mut trees : Vector (Option Tree) argc := .replicate argc none
  -- Initialize from preElaborated
  for (argLevel, tree) in preElaborated do
    if h : argLevel < argc then
      trees := trees.set argLevel (some tree)
  for ⟨ae, sp⟩ in se.argElaborators do
    let argLevel := ae.argLevel
    let .isTrue argLevelP := inferInstanceAs (Decidable (argLevel < argc))
        | return panic! "Invalid argLevel"
    -- Skip pre-elaborated args
    if trees[argLevel].isSome then continue
    -- Compute the typing context for this argument
    let tctx ←
      /- Recursive datatypes make this a bit complicated, since we need to make
      sure the type is resolved as an fvar even while processing it. -/
      match ae.datatypeScope with
      | some (nameLevel, typeParamsLevel) =>
        let nameTree := trees[nameLevel]
        let typeParamsTree := trees[typeParamsLevel]
        match nameTree, typeParamsTree with
        | some nameT, some typeParamsT =>
          let datatypeName :=
            match nameT.info with
            | .ofIdentInfo info => info.val
            | _ => panic! "Expected identifier for datatype name"
          let baseCtx := typeParamsT.resultContext
          /- Extract type parameter names only from NEW bindings added by
          typeParams, not inherited bindings (which may include datatypes from
          previous commands) -/
          let inheritedCount := tctx0.bindings.size
          let typeParamNames := baseCtx.bindings.toArray.extract inheritedCount baseCtx.bindings.size
            |>.filterMap fun b =>
              match b.kind with
              | .type _ [] _ => some b.ident
              | _ => none
          -- Add the datatype name to the GlobalContext as a type
          -- Use tctx0.globalContext so pre-registered types are visible
          let gctx := tctx0.globalContext
          let gctx := gctx.ensureDefined datatypeName (GlobalKind.type typeParamNames.toList none)
          -- Add .tvar bindings for type parameters
          let loc := typeParamsT.info.loc
          -- Start with empty local bindings - don't inherit from baseCtx
          -- This prevents datatype names from leaking between mutual block entries
          let tctx := typeParamNames.foldl (init := TypingContext.empty gctx) fun ctx name =>
            ctx.push { ident := name, kind := .tvar loc name }
          pure tctx
        | _, _ => continue
      | none =>
        match ae.contextLevel with
        | some idx =>
          match trees[idx] with
          | some t => pure t.resultContext
          | none => continue
        | none => pure tctx0
    let astx := args[ae.syntaxLevel]
    let expectedKind := argDecls[argLevel].kind
    match expectedKind with
    | .type expectedType =>
      let (tree, success) ← runChecked <| elabExpr tctx astx
      -- If elaboration is successful, then we run type inference to see if we
      -- can resolve additional type arguments.
      if success then
        let expr := tree.info.asExpr!.expr
        let inferredType ← inferType tctx expr
        let dialects := (← read).dialects
        let resolveArg (i : Nat) : Option Arg := do
            assert! i < argLevel
            Tree.arg <$> trees[argLevel - i - 1]!
        match expandMacros dialects expectedType resolveArg with
        | .error () =>
          panic! "Could not infer type."
        | .ok expectedType => do
          trees ← unifyTypes argDecls ⟨argLevel, argLevelP⟩ expectedType tctx astx inferredType trees
          assert! trees[argLevel].isNone
          trees := trees.set argLevel (some tree)
      | .cat c =>
        let (tree, success) ← runChecked <| catElaborator c tctx astx
        if success then
          trees := trees.set argLevel (some tree)
  let treesr := trees.map (·.getD default)
  let mut tctx :=
    match se.resultScope with
    | none => tctx0
    | some idx => Id.run do
      let .isTrue p := inferInstanceAs (Decidable (idx < argc))
        | return panic! "Invalid index"
      treesr[idx].resultContext
  return (treesr, tctx)

/--
Two-phase elaboration for operations annotated with `@[preRegisterTypes]`.

When a parent operation (like `mutual`) has `@[preRegisterTypes(scope)]`, its children
may reference each other's types before they are declared. This function handles that by:

- **Phase 1**: For each child, partially elaborate name + typeParams args (which don't
  reference sibling types) to extract type names and parameter names.
- **Pre-register**: Pre-register all extracted types so mutual references resolve.
- **Phase 2**: Fully elaborate each child with the updated context. Name args that were
  already elaborated in Phase 1 are passed via `preElabMap` to avoid redundant work.
  The remaining parent args are then elaborated by `runSyntaxElaborator`.

**Known deviation**: typeParams args are elaborated twice — once in Phase 1 (against
`tctx0`) to extract param names, and again in Phase 2 (against the per-child context).
Phase 1 typeParams trees cannot be reused because `collectNewBindingsM` requires
`tree.info.inputCtx.bindings.size ≥ initialScope`, which fails when the Phase 1 context
is smaller than the Phase 2 per-child context.
-/
partial def elaborateWithPreRegistration
    {argc : Nat}
    (argDecls : Vector ArgDecl argc)
    (se : SyntaxElaborator)
    (tctx0 : TypingContext)
    (stxArgs : Vector Syntax se.syntaxCount)
    (scopeArgLevel : Nat) : ElabM (Vector Tree argc × TypingContext) := do
  -- Compute a fallback location from the first syntax arg for error reporting
  let fallbackLoc :=
    match stxArgs.toArray[0]? with
    | some stx0 => (mkSourceRange? stx0).getD SourceRange.none
    | none => SourceRange.none
  -- Resolve scope: find the scope arg's syntax, category, and children
  let some scopeSyntaxLevel := argSyntaxLevel? se scopeArgLevel
    | logInternalError fallbackLoc "elaborateWithPreRegistration: no syntax level for scope arg"
      return default
  let .isTrue scopeSLBound := inferInstanceAs (Decidable (scopeSyntaxLevel < se.syntaxCount))
    | logInternalError fallbackLoc "elaborateWithPreRegistration: scope syntax level out of bounds"
      return default
  let scopeStx := stxArgs[scopeSyntaxLevel]
  let .isTrue scopeALBound := inferInstanceAs (Decidable (scopeArgLevel < argc))
    | logInternalError fallbackLoc "elaborateWithPreRegistration: scope arg level out of bounds"
      return default
  let scopeArgDecl := argDecls[scopeArgLevel]
  let scopeCat ← do
    match scopeArgDecl.kind with
    | .cat c => pure c
    | _ =>
      logInternalError fallbackLoc "elaborateWithPreRegistration: expected category for scope arg"
      return default
  if scopeCat.args.size ≠ 1 then
    logInternalError fallbackLoc s!"elaborateWithPreRegistration: expected 1 scope cat arg, got {scopeCat.args.size}"
    return default
  let some (sep, getChildren) := scopeSepFormat scopeCat.name
    | logInternalError fallbackLoc s!"elaborateWithPreRegistration: unsupported scope category {scopeCat.name}"
      return default
  let children := getChildren scopeStx
  -- Phase 1: Partially elaborate each child to extract type names and params
  let mut allRegistrations : Array (String × List String) := #[]
  let mut childPreElabMaps : Array (Array (Nat × Tree)) := #[]
  for child in children do
    let (regs, preElabMap) ← extractChildTypeInfo tctx0 child
    allRegistrations := allRegistrations ++ regs
    childPreElabMaps := childPreElabMaps.push preElabMap
  -- Pre-register: add all types so mutual references resolve
  let gctx := preRegisterTypes tctx0.globalContext allRegistrations
  let updatedTctx := tctx0.withGlobalContext gctx
  -- Phase 2: Fully elaborate children sequentially, threading context
  let scopeLoc := (mkSourceRange? scopeStx).getD SourceRange.none
  let mut childTrees : Array Tree := #[]
  let mut currentCtx := updatedTctx
  for i in [:children.size] do
    let child := children[i]!
    let childPreElab := childPreElabMaps[i]!
    let (tree, success) ← runChecked <| elabOperation currentCtx child childPreElab
    let rtctx := if success then tree.resultContext else currentCtx
    childTrees := childTrees.push tree
    currentCtx := rtctx
  -- Build SeqInfo tree for the scope
  let seqInfo : SeqInfo := {
    loc := scopeLoc,
    inputCtx := updatedTctx,
    sep := sep,
    args := childTrees.map (·.arg),
    resultCtx := currentCtx
  }
  let scopeTree : Tree := .node (.ofSeqInfo seqInfo) childTrees
  -- Elaborate remaining parent args with the scope tree pre-elaborated
  runSyntaxElaborator argDecls se updatedTctx stxArgs #[(scopeArgLevel, scopeTree)]

/--
Phase 1 for a single child: elaborate its name and typeParams args to extract
the type name and parameter names for pre-registration.
Returns `(registrations, preElabMap)` where:
- `registrations`: array of `(typeName, paramNames)` pairs
- `preElabMap`: array of `(argLevel, tree)` for name args (passed to Phase 2)
-/
partial def extractChildTypeInfo (tctx0 : TypingContext) (child : Syntax)
    : ElabM (Array (String × List String) × Array (Nat × Tree)) := do
  let dialects := (← read).dialects
  let syntaxElabs := (← read).syntaxElabs
  let mut registrations : Array (String × List String) := #[]
  let mut preElabMap : Array (Nat × Tree) := #[]
  if let some childIdent := qualIdentKind child then
    let childLoc := (mkSourceRange? child).getD SourceRange.none
    let some childDecl := dialects.lookupOpDecl childIdent
      | logInternalError childLoc s!"extractChildTypeInfo: unknown op declaration {childIdent}"
        return default
    let some childSe := syntaxElabs[childIdent]?
      | logInternalError childLoc s!"extractChildTypeInfo: no syntax elaborator for {childIdent}"
        return default
    let childStxArgs := child.getArgs
    let childArgDecls := childDecl.argDecls.toArray
    for spec in childDecl.newBindings do
      let (nameArgLevel, typeParamsArgLevel?) ←
        match spec with
        | .datatype b => pure (b.nameIndex.toLevel, some b.typeParamsIndex.toLevel)
        | .type b => pure (b.nameIndex.toLevel, b.argsIndex.map (·.toLevel))
        | _ => continue
      -- Elaborate name arg
      let some nameSL := argSyntaxLevel? childSe nameArgLevel
        | logInternalError childLoc "extractChildTypeInfo: argLevelToSyntaxLevel failed for name"
          continue
      if nameSL ≥ childStxArgs.size then
        logInternalError childLoc s!"extractChildTypeInfo: nameSL {nameSL} out of bounds ({childStxArgs.size})"
        continue
      if nameArgLevel ≥ childArgDecls.size then
        logInternalError childLoc s!"extractChildTypeInfo: nameArgLevel {nameArgLevel} out of bounds ({childArgDecls.size})"
        continue
      let nameCat := childArgDecls[nameArgLevel]!.kind.categoryOf
      let (nameTree, nameSuccess) ← runChecked <|
        catElaborator nameCat tctx0 childStxArgs[nameSL]!
      if !nameSuccess then continue
      let name ←
        match nameTree.info with
        | .ofIdentInfo info => pure info.val
        | _ =>
          logInternalError childLoc "extractChildTypeInfo: expected ident for type name"
          continue
      preElabMap := preElabMap.push (nameArgLevel, nameTree)
      -- Elaborate typeParams to extract real param names
      -- (not added to preElabMap — Phase 2 re-elaborates with correct context)
      let some tpArgLevel := typeParamsArgLevel?
        | -- .type spec with no argsIndex: register with empty params
          registrations := registrations.push (name, [])
          continue
      let some tpSL := argSyntaxLevel? childSe tpArgLevel
        | logInternalError childLoc "extractChildTypeInfo: argLevelToSyntaxLevel failed for typeParams"
          continue
      if tpSL ≥ childStxArgs.size then
        logInternalError childLoc s!"extractChildTypeInfo: tpSL {tpSL} out of bounds ({childStxArgs.size})"
        continue
      if tpArgLevel ≥ childArgDecls.size then
        logInternalError childLoc s!"extractChildTypeInfo: tpArgLevel {tpArgLevel} out of bounds ({childArgDecls.size})"
        continue
      let tpCat := childArgDecls[tpArgLevel]!.kind.categoryOf
      let (tpTree, tpSuccess) ← runChecked <|
        catElaborator tpCat tctx0 childStxArgs[tpSL]!
      if !tpSuccess then
        return default
      registrations := registrations.push (name, extractParamNames tctx0.bindings.size tpTree)
  return (registrations, preElabMap)

partial def elabType (tctx : TypingContext) (stx : Syntax) : ElabM Tree := do
  let (tree, success) ← runChecked <| elabOperation tctx stx
  if !success then
    return default
  assert! tree.isSpecificOp q`Init.mkType
  assert! tree.children.size = 1
  let t := tree[0]!
  let (tree, success) ← runChecked <| translateTypeTree t
  if !success then
    return default
  match tree.info with
  | .ofTypeInfo _ =>
    pure ()
  | _ =>
    logErrorMF tree.info.loc mf!"Expected a type."
  pure tree

partial def catElaborator (c : SyntaxCat) : TypingContext → Syntax → ElabM Tree :=
  match c.name with
  | q`Init.Expr =>
    elabExpr
  | q`Init.Ident =>
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! "ident missing source location"
      let info : IdentInfo := { inputCtx := tctx, loc := loc, val := stx.getId.toString }
      pure <| .node (.ofIdentInfo info) #[]
  | q`Init.Num =>
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! "num missing source location"
      match stx.isNatLit? with
      | some v =>
        let info : NumInfo := { inputCtx := tctx, loc := loc, val := v }
        pure <| .node (.ofNumInfo info) #[]
      | none =>
        panic! s!"Invalid Init.Num {repr stx}"
  | q`Init.ByteArray =>
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! "bytes missing source location"
      match stx with
      | .node _ _ #[.atom _ contents] =>
        match ByteArray.unescapeBytes contents with
        | .error (_, _, msg) => panic! msg
        | .ok bytes =>
            let info : ConstInfo ByteArray := {
              inputCtx := tctx,
              loc := loc,
              val := bytes
            }
            pure <| .node (.ofBytesInfo info) #[]
      | _ =>
        logError loc s!"Unexpected byte syntax {repr stx}"
        pure default
  | q`Init.Decimal =>
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! "decimal missing source location"
      match stx.isScientificLit? with
      | some (m, eIsNeg, e) =>
        let d : Decimal := { mantissa := m, exponent := if eIsNeg then .negOfNat e else .ofNat e }
        let info : DecimalInfo := { inputCtx := tctx, loc := loc, val := d }
        pure <| .node (.ofDecimalInfo info) #[]
      | none =>
        panic! s!"Invalid Init.Num {repr stx}"
  | q`Init.Str =>
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! "str missing source location"
      match stx.isStrLit? with
      | some s =>
        let info : StrlitInfo := { inputCtx := tctx, loc := loc, val := s }
        pure <| .node (.ofStrlitInfo info) #[]
      | none =>
        panic! s!"String not supported {stx} {stx.isStrLit?}"
  | q`Init.Type => elabType
  | q`Init.TypeP =>
      fun tctx stx => do
        let (tree, true) ← runChecked <| elabOperation tctx stx
          | return default
        assert! tree.isSpecificOp q`Init.mkTypeP
        assert! tree.children.size = 1
        let (tree, true) ← runChecked <| translateTypeTree tree[0]!
          | return default
        let ok :=
              match tree.info with
              | .ofTypeInfo _ => true
              | .ofCatInfo info => info.cat.isType
              | _ => false
        if !ok then
          logErrorMF tree.info.loc mf!"Expected a type or Type instead of {c}"
        pure tree
  | q`Init.Option =>
    assert! c.args.size = 1
    let a := c.args[0]!
    elabOption (catElaborator a)
  |  q`Init.Seq =>
    elabSeqWith c .none "seq" (·.getArgs)
  | q`Init.CommaSepBy =>
    elabSeqWith c .comma "commaSepBy" (·.getSepArgs)
  | q`Init.SpaceSepBy =>
    elabSeqWith c .space "spaceSepBy" (·.getSepArgs)
  | q`Init.SpacePrefixSepBy =>
    elabSeqWith c .spacePrefix "spacePrefixSepBy" (·.getArgs)
  | _ =>
    assert! c.args.isEmpty
    fun tctx stx => elabOperation tctx stx

where
  elabSeqWith (c : SyntaxCat) (sep : SepFormat) (name : String) (getArgsFrom : Syntax → Array Syntax) : TypingContext → Syntax → ElabM Tree :=
    assert! c.args.size = 1
    let a := c.args[0]!
    let f := elabManyElement (catElaborator a)
    fun tctx stx => do
      let some loc := mkSourceRange? stx
        | panic! s!"{name} missing source location {repr stx}"
      let (args, resultCtx) ← (getArgsFrom stx).foldlM f (#[], tctx)
      let info : SeqInfo := { inputCtx := tctx, loc := loc, sep := sep, args := args.map (·.arg), resultCtx }
      pure <| .node (.ofSeqInfo info) args

partial def elabExpr (tctx : TypingContext) (stx : Syntax) : ElabM Tree := do
  match stx.getKind with
  | `Init.exprParen =>
    elabExpr tctx stx[1]
  | `Init.exprIdent =>
    let some loc := mkSourceRange? stx
      | panic! "exprIdent missing source location"
    let einfo : ElabInfo := { loc := loc, inputCtx := tctx }
    let name := elabIdent stx[0]
    let some binding := tctx.lookupVar name
      | logError loc s!"Unknown expr identifier {name}"
        return default
    match binding with
    | .bvar idx k => do
      match k with
      | .expr _ =>
        let info : ExprInfo := { toElabInfo := einfo, expr := .bvar loc idx }
        return .node (.ofExprInfo info) #[]
      | .type _ _params _ =>
        logErrorMF loc mf!"{name} is a type when an expression is required."
        return default
      | .tvar _ _ =>
        logErrorMF loc mf!"{name} is a type variable when an expression is required."
        return default
      | .cat c =>
        logErrorMF loc mf!"{name} has category {c} when an expression is required."
        return default
    | .fvar idx k =>
      let .expr _ := k
        | logError loc s!"{name} is a type when expression required."
          return default
      let info : ExprInfo := { toElabInfo := einfo, expr := .fvar loc idx }
      return .node (.ofExprInfo info) #[]
  | `Init.exprApp => do
    let some loc := mkSourceRange? stx
      | panic! "exprApp missing source location"
    let einfo : ElabInfo := { loc := loc, inputCtx := tctx }
    let some fnLoc := mkSourceRange? stx[0]
      | panic! "exprApp fn missing source location"
    let fn := elabIdent stx[0]
    let args := stx[2].getSepArgs
    let (fvar, k) ←
      match tctx.lookupVar fn with
      | some (.fvar idx k) =>
        pure (ExprF.fvar fnLoc idx, k)
      | some (.bvar idx (.expr tp)) =>
        -- Support bound function calls
        pure (ExprF.bvar fnLoc idx, .expr tp)
      | some (.bvar idx _) =>
        logError fnLoc s!"Bound variable {fn} is not a function"
        return default
      | none =>
        logError fnLoc s!"Unknown variable {fn}"
        return default
    let .expr tp := k
      | logError fnLoc s!"Expression expected."
        return default
    let (argTypes, r) ← do
      let tctx := TypingContext.empty tctx.globalContext
      match tctx.applyNArgs tp args.size with
      | .error (a, r) =>
        if a.size = 0 then
          logError fnLoc s!"Expected function"
        else
          logError fnLoc s!"Expected function with {a.size} arguments."
        return default
      | .ok p =>
        pure p
    let mkArgDecl (tp : TypeExpr) : ArgDecl :=
          { ident := "", kind := .type (.ofType tp) }
    let argDecls := argTypes.map mkArgDecl
    let se : SyntaxElaborator := {
            syntaxCount := args.size
            argElaborators := Array.ofFn fun (⟨lvl, lvlp⟩ : Fin args.size) =>
              let e := { syntaxLevel := lvl, argLevel := lvl }
              ⟨e, lvlp⟩
            resultScope := none
          }
    let (args, _) ← runSyntaxElaborator argDecls se tctx ⟨args, Eq.refl args.size⟩
    let e := args.toArray.foldl (init := fvar) fun e t =>
      .app { start := fnLoc.start, stop := t.info.loc.stop } e t.arg
    let info : ExprInfo := { toElabInfo := einfo, expr := e }
    return .node (.ofExprInfo info) args.toArray
  | _ => do
    let some loc := mkSourceRange? stx
      | panic! "evalExpr missing source location"
    let einfo : ElabInfo := { loc := loc, inputCtx := tctx }
    let some i := qualIdentKind stx
      | return panic! s!"Unknown expression {stx}"
    let some d := (←read).dialects[i.dialect]?
      | return panic! s!"Unknown dialect {i.dialect} in {stx}"
    let some fn := d.functions[i.name]?
      | return panic! (f!"unknown operation {eformat i}").pretty
    let some se := (←read).syntaxElabs[i]?
      | return panic! s!"Unknown expression elaborator {i.fullName}"
    let argDecls := fn.argDecls.toArray.toVector
    let (stxArgs, success) ← runChecked <| getSyntaxArgs stx i se.syntaxCount
    if !success then
      return default
    let ((args, _), success) ← runChecked <| runSyntaxElaborator argDecls se tctx stxArgs
    if !success then
      return default
    -- N.B. Every subterm gets the function location.
    let e := args.toArray.foldl (init := ExprF.fn loc i) fun e t => .app loc e t.arg
    let info : ExprInfo := { toElabInfo := einfo, expr := e }
    return .node (.ofExprInfo info) args.toArray

end

def runElab {α} (action : ElabM α) : DeclM α := do
  let loader := (← read).loader
  let s ← get
  let ctx : ElabContext := {
        dialects := loader.dialects,
        syntaxElabs := loader.syntaxElabMap,
        openDialectSet := s.openDialectSet,
        typeOrCatDeclMap := s.typeOrCatDeclMap,
        metadataDeclMap := s.metadataDeclMap,
        globalContext := s.globalContext,
        inputContext := (←read).inputContext,
        missingImport := (← read).missingImport
  }
  let errors := (←get).errors
  -- Clear errors from decl
  modify fun s => { s with errors := #[] }
  let s : ElabState := { errors }
  let (r, es) ← action ctx s
  modify fun s => { s with errors := es.errors }
  pure r

-- Exported interface

partial def elabCommand (leanEnv : Lean.Environment) : DeclM (Option Tree) := do
  let inputContext := (←read).inputContext
  let leanParserState :=
        Parser.runCatParser
          (←get).tokenTable
          (←get).parserMap
          leanEnv
          inputContext
          (←get).pos
          (←read).stopPos
          q`Init.Command
  if leanParserState.hasError then
    for (pos, stk, err) in leanParserState.allErrors do
      logErrorMessage <| Lean.mkErrorMessage inputContext pos stk err
    return none
  if leanParserState.stxStack.size == 0 then
    panic! "Cmmand state is empty"
  if leanParserState.stxStack.size > 1 then
    panic! "Command state has multiple entries."
  let stx := leanParserState.stxStack.back
  modify fun s => { s with pos := leanParserState.pos }
  assert! stx.getKind ≠ nullKind
  let glbl := (←get).globalContext
  runElab <| some <$> elabOperation (.empty glbl) stx

end Strata.Elab
end

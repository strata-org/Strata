/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Elab.DeclM
public import Strata.DDM.Elab.Tree
import Strata.DDM.HNF
import all Strata.DDM.Util.Array
import all Strata.DDM.Util.Fin
import all Strata.DDM.Util.Lean
import Strata.Util.DecideProp

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
  (isTypeP : Fin argc → Bool)
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
    res ← unifyTypes isTypeP argLevel0 ea[i] tctx exprSyntax ia[i]! res
  return res

/--
This compares the inferred type against the expected type for an argument to check if the
argument value is well-typed and determine if additional type variables can be automatically
inferred.

- `isTypeP` returns true if the argument at the given index is a type.
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
    (isTypeP : Fin argc → Bool)
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
      unifyTypeVectors isTypeP argLevel0 ea tctx exprSyntax ia args
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
      unifyTypeVectors isTypeP argLevel0 ea tctx exprSyntax ia args
    | .tvar _ _ =>
      -- tvar inferred types are passed through; type inference will catch mismatches
      pure args
    | ih =>
      logErrorMF exprLoc mf!"Encountered {ih} expression when {expectedType} expected."
      return args
  | .bvar _ idx =>
    let .isTrue idxP := decideProp (idx < argLevel)
      | return panic! "Invalid index"
    let typeLevel := argLevel - (idx + 1)
    -- Verify type level is a type parameter.
    assert! isTypeP ⟨typeLevel, by omega⟩

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
        logErrorMF exprLoc mf!"Expression has type {withBindings tctx.bindings (mformat inferredType)} when {withBindings tctx.bindings (mformat info.typeExpr)} expected." (globalContext? := some tctx.globalContext)
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
      -- Propagate the tvar to sub-components so that bvar type parameters
      -- (e.g., inTp/outTp in apply_expr) get filled with the tvar rather
      -- than being left unresolved.
      let res ← unifyTypes isTypeP argLevel0 ea tctx exprSyntax inferredType args
      unifyTypes isTypeP argLevel0 er tctx exprSyntax inferredType res
    | .arrow _ ia ir =>
      let res ← unifyTypes isTypeP argLevel0 ea tctx exprSyntax ia args
      unifyTypes isTypeP argLevel0 er tctx exprSyntax ir res

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

def evalBindingNameIndex {n} (trees : Vector Tree n) (idx : DebruijnIndex n) : String :=
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
    let isTrue p := decideProp (argChildren.size = 1)
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
    let isTrue p := decideProp (argChildren.size = 2)
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

private def checkIsTypeKind (argLoc : SourceRange) (b : Binding) : ElabM Unit :=
  match b.kind with
  | .type _ [] _ => pure ()
  | .tvar .. | .type .. | .expr _ | .cat _ =>
    logError argLoc s!"{b.ident} must have type Type instead of {repr b.kind}."

/-- Extract type parameter names from a bindings argument. -/
def elabTypeParams {n} (initSize : Nat) (args : Vector Tree n)
    (idx : Option (DebruijnIndex n)) : ElabM (List String) := do
  let params ← elabArgIndex initSize args idx fun argLoc b => do
    checkIsTypeKind argLoc b
    return b.ident
  pure params.toList

/--
Construct a binding from a binding spec and the arguments to an operation.
-/
def evalBindingSpec
    {bindings}
    (tctx : TypingContext)
    (loc : SourceRange)
    (initSize : Nat)
    (dialectName : DialectName)
    (b : BindingSpec bindings)
    (args : Vector Tree bindings.size)
    : ElabM TypingContext := do
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
    pure <| tctx.push { ident, kind }
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
    pure <| tctx.push { ident, kind := .type loc params value }
  | .scopedType b =>
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
    -- For scoped types, add to global context instead of local bindings
    let gctx := tctx.globalContext
    let gkind := GlobalKind.type params value
    let newGctx := gctx.ensureDefined ident gkind
    pure (tctx.withGlobalContext newGctx)
  | .datatype b =>
    let nameInfo := args[b.nameIndex.toLevel].info
    let (nameLoc, ident) ←
        match nameInfo with
        | .ofIdentInfo i =>
          pure (i.loc, i.val)
        | _ =>
          logInternalError nameInfo.loc s!"Expected ident"
          return tctx
    let params ← elabTypeParams initSize args (some b.typeParamsIndex)
    assert! tctx.bindings.size = 0
    let gctx := tctx.globalContext
    let gctx := gctx.ensureDefined ident (.type params none)

    let dialects := (← read).dialects

    let t := args[b.constructorsIndex.toLevel]
    match extractConstructorInfo dialects t.arg with
    | .ok info =>
      let mut seen : Std.HashSet String := {}
      for c in info do
        let name := c.name
        if name ∈ seen then
          logError loc s!"Duplicate constructor name '{name}'."
          continue
        seen := seen.insert name
      -- Expand function templates to catch name collisions early
      let datatypeIndex := gctx.findIndex? ident |>.getD (gctx.vars.size - 1)
      let datatypeType :=
        mkDatatypeTypeRef loc datatypeIndex params.toArray
      let (gctx, errors) := gctx.expandFunctionTemplates
        dialectName loc ident datatypeType info
        b.functionTemplates
      errors.forM (logError loc)
      pure <| .empty gctx
    | .error e =>
      logError loc e
      pure <| .empty gctx
  | .tvar b =>
    let ident := evalBindingNameIndex args b.nameIndex
    pure <| tctx.push { ident, kind := .tvar loc ident }

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
    let .isTrue idxP := decideProp (idx < tctx.bindings.size)
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
    let tp ← tp.instTypeM fun ann i => do
        assert! i < fnArgCount
        let lvl := fnArgCount - i - 1
        match a.val[lvl]! with
        | .type tp => pure tp
        | _ =>
           logError ann s!"Could not infer type parameter {i} for {ident}"
           pure default
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
  let .isTrue stxArgP := decideProp (stxArgs.size = expected)
    | logInternalError loc s!"{ident} expected {expected} arguments when {stxArgs.size} seen.\n  {repr stxArgs[0]!}"
      return default
  return ⟨stxArgs, stxArgP⟩

/-- The kind of elaboration to perform for an argument in `runSyntaxElaborator`.
Unlike `ArgDeclKind`, this distinguishes pre-types (which need macro expansion)
from already-resolved type expressions. -/
inductive ElabArgKind where
| preType (tp : PreType)
| typeExpr (tp : TypeExpr)
| cat (k : SyntaxCat)

namespace ElabArgKind

def isType : ElabArgKind → Bool
| .cat c => c.isType
| _ => false

def ofArgDeclKind : ArgDeclKind → ElabArgKind
| .type tp => .preType tp
| .cat c => .cat c

end ElabArgKind

/-- Map a sequence category name to its separator format and child extraction function. -/
private def scopeSepFormat (name : QualifiedIdent)
    : Option (SepFormat × (Syntax → Array Syntax)) :=
  match name with
  | q`Init.Seq              => some (.none, Syntax.getArgs)
  | q`Init.CommaSepBy       => some (.comma, Syntax.getSepArgs)
  | q`Init.SemicolonSepBy   => some (.semicolon, Syntax.getSepArgs)
  | q`Init.SpaceSepBy       => some (.space, Syntax.getSepArgs)
  | q`Init.SpacePrefixSepBy => some (.spacePrefix, Syntax.getArgs)
  | q`Init.NewlineSepBy     => some (.newline, Syntax.getArgs)
  | _ => none

/-- Look up the syntax level for a given arg level
via the precomputed `argElabIndex`. -/
private def argSyntaxLevel?
    (se : SyntaxElaborator) (argLevel : Nat) : Option Nat :=
  se.argElabIndex[argLevel]?.join.bind fun idx =>
    (se.argElaborators[idx]?).map (·.val.syntaxLevel)

/--
Compute the result `TypingContext` after elaboration. If the
`SyntaxElaborator` specifies a `resultScope`, returns the context from
that tree; otherwise returns the input context `tctx0` unchanged.
-/
private def resultContext {argc : Nat}
    (se : SyntaxElaborator) (tctx0 : TypingContext)
    (trees : Vector Tree argc) : TypingContext :=
  match se.resultScope with
  | none => tctx0
  | some idx => Id.run do
    let .isTrue p := decideProp (idx < argc)
      | return panic! "Invalid index"
    trees[idx].resultContext

mutual

partial def elabOperation (tctx : TypingContext) (stx : Syntax) : ElabM Tree := do
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
  let getKind i := .ofArgDeclKind argDecls[i].kind
  let ((args, newCtx), success) ← runChecked <|
    match se.preRegisterTypesScope with
    | some scopeArgLevel =>
      elaborateWithPreRegistrationCore argDecls se tctx loc stxArgs scopeArgLevel
        "elaborateWithPreRegistration" extractDatatypeInfo
    | none =>
    match se.preRegisterFunctionsScope with
    | some scopeArgLevel =>
      elaborateWithPreRegistrationCore argDecls se tctx loc stxArgs scopeArgLevel
        "elaborateWithFunctionPreRegistration" extractFunctionInfo
    | none => do
      let args ← runSyntaxElaborator (argc := argDecls.size) getKind se tctx stxArgs
      return (args, resultContext se tctx args)

  if !success then
    return default

  let resultCtx ← decl.newBindings.foldlM (init := newCtx) <| fun ctx spec => do
    evalBindingSpec ctx loc initSize i.dialect spec args
  let op : Operation := { ann := loc, name := i, args := args.toArray.map (·.arg) }
  if loc.isNone then
    return panic! s!"Missing position info {repr stx}."
  let info : OperationInfo := { loc := loc, inputCtx := tctx, op, resultCtx }
  return .node (.ofOperationInfo info) args.toArray

/-- Elaborate a single argument based on its `ElabArgKind`.
Returns the updated `trees` vector with the result placed at `argIdx`. -/
partial def elabSyntaxArg
    {argc : Nat}
    (getKind : Fin argc → ElabArgKind)
    (isTypeP : Fin argc → Bool)
    (tctx : TypingContext)
    (astx : Syntax)
    (argIdx : Fin argc)
    (trees : Vector (Option Tree) argc)
    : ElabM (Vector (Option Tree) argc) := do
  match getKind argIdx with
  | .preType expectedType =>
    let (tree, success) ← runChecked <| elabExpr tctx astx
    if success then
      let expr := tree.info.asExpr!.expr
      let inferredType ← inferType tctx expr
      let dialects := (← read).dialects
      let resolveArg (i : Nat) : Option Arg := do
          assert! i < argIdx.val
          Tree.arg <$> trees[argIdx.val - i - 1]!
      match expandMacros dialects expectedType resolveArg with
      | .error () =>
        panic! "Could not infer type."
      | .ok expectedType => do
        let trees ← unifyTypes isTypeP argIdx
          expectedType tctx astx inferredType trees
        assert! trees[argIdx].isNone
        return trees.set argIdx (some tree)
    else
      return trees
  | .typeExpr expectedType =>
    let (tree, success) ← runChecked <| elabExpr tctx astx
    if success then
      let expr := tree.info.asExpr!.expr
      let inferredType ← inferType tctx expr
      let trees ← unifyTypes isTypeP argIdx
        expectedType tctx astx inferredType trees
      assert! trees[argIdx].isNone
      return trees.set argIdx (some tree)
    else
      return trees
  | .cat c =>
    let (tree, success) ← runChecked <| catElaborator c tctx astx
    if success then
      return trees.set argIdx (some tree)
    else
      return trees

/-- Elaborate all syntax arguments for an operation according to the
`SyntaxElaborator`'s ordering. Iterates over `se.argElaborators`, computes
the typing context for each argument (handling datatype scopes for
recursive types), and delegates to `elabSyntaxArg` for the actual
elaboration. Returns the elaborated `Tree` vector and the result
`TypingContext`. -/
partial def runSyntaxElaborator
  {argc : Nat}
  (getKind : Fin argc → ElabArgKind)
  (se : SyntaxElaborator)
  (tctx0 : TypingContext)
  (args : Vector Syntax se.syntaxCount)
  : ElabM (Vector Tree argc) := do
  let isTypeP := fun i => (getKind i).isType
  let mut trees : Vector (Option Tree) argc := .replicate argc none
  for ⟨ae, sp⟩ in se.argElaborators do
    let argLevel := ae.argLevel
    let .isTrue argLevelP := decideProp (argLevel < argc)
        | return panic! "Invalid argLevel"
    -- Skip pre-elaborated args
    if trees[argLevel].isSome then continue
    -- Get syntax
    let astx := args[ae.syntaxLevel]
    let some aloc := mkSourceRange? astx
      | panic! "Arg syntax missing position information"
    -- Handle scoping annotations.
    if let some typeParamsLevel := ae.scopeTVar then
      let some typeParamsT := trees[typeParamsLevel]
        | logError aloc "Internal: missing type parameter"
          return default
      let tloc := typeParamsT.info.loc
      let paramCtx := typeParamsT.resultContext
      let (typeParamNames, success) ← runChecked <|
        paramCtx.bindings.toArray.foldlM (init := #[]) fun a b => do
          match b.kind with
          | .type _ [] _ =>
            pure <| a.push b.ident
          | _ =>
            logError tloc "Expected only type arguments."
            pure a
      if success = false then
        return default
      let tctx := TypingContext.empty tctx0.globalContext
      let tctx := typeParamNames.foldl (init := tctx) fun ctx name =>
          ctx.push { ident := name, kind := .tvar tloc name }
      trees ← elabSyntaxArg getKind isTypeP tctx astx ⟨argLevel, argLevelP⟩ trees
    else if let some idx := ae.contextLevel then
      let some t := trees[idx]
        | -- This failed so skip
          continue
      trees ← elabSyntaxArg getKind isTypeP t.resultContext astx ⟨argLevel, argLevelP⟩ trees
    else
      trees ← elabSyntaxArg getKind isTypeP tctx0 astx ⟨argLevel, argLevelP⟩ trees
  return trees.map (·.getD default)

/--
Two-phase elaboration for operations annotated with `@[preRegisterTypes]` or
`@[preRegisterFunctions]`.

- **Phase 1**: Resolve the scope argument, extract children, and fold `extractInfo`
  over them to pre-register names in the `GlobalContext`.
- **Phase 2**: Fully elaborate all args with the updated context.

`label` is used in error messages to identify the caller.

For `@[preRegisterTypes]`: pre-registers type-level bindings so mutual type references
resolve. **Known deviation**: typeParams args are elaborated twice — once in Phase 1
(against `tctx0`) to extract param names, and again in Phase 2 (against the per-child
context). Phase 1 typeParams trees cannot be reused because `collectNewBindingsM`
requires `tree.info.inputCtx.bindings.size ≥ initialScope`, which fails when the
Phase 1 context is smaller than the Phase 2 per-child context.

For `@[preRegisterFunctions]`: pre-registers expression-level bindings (function
signatures) so mutual calls resolve.
-/
partial def elaborateWithPreRegistrationCore
    {argc : Nat}
    (argDecls : Vector ArgDecl argc)
    (se : SyntaxElaborator)
    (tctx0 : TypingContext)
    (fallbackLoc : SourceRange)
    (stxArgs : Vector Syntax se.syntaxCount)
    (scopeArgLevel : Nat)
    (label : String)
    (extractInfo : GlobalContext → Syntax → ElabM GlobalContext)
    : ElabM (Vector Tree argc × TypingContext) := do
  let some scopeSyntaxLevel := argSyntaxLevel? se scopeArgLevel
    | logInternalError fallbackLoc s!"{label}: no syntax level for scope arg"
      return default
  let .isTrue scopeSLBound := decideProp (scopeSyntaxLevel < se.syntaxCount)
    | logInternalError fallbackLoc s!"{label}: scope syntax level out of bounds"
      return default
  let scopeStx := stxArgs[scopeSyntaxLevel]
  let .isTrue scopeALBound := decideProp (scopeArgLevel < argc)
    | logInternalError fallbackLoc s!"{label}: scope arg level out of bounds"
      return default
  let scopeArgDecl := argDecls[scopeArgLevel]
  let scopeCat ← do
    match scopeArgDecl.kind with
    | .cat c => pure c
    | _ =>
      logInternalError fallbackLoc s!"{label}: expected category for scope arg"
      return default
  if scopeCat.args.size ≠ 1 then
    logInternalError fallbackLoc s!"{label}: expected 1 scope cat arg, got {scopeCat.args.size}"
    return default
  let some (_sep, getChildren) := scopeSepFormat scopeCat.name
    | logInternalError fallbackLoc s!"{label}: unsupported scope category {scopeCat.name}"
      return default
  let children := getChildren scopeStx
  -- Phase 1: Pre-register all names so mutual references resolve
  if tctx0.bindings.size ≠ 0 then
    logInternalError fallbackLoc s!"{label}: expected empty local bindings"
    return default
  let gctx0 : GlobalContext := tctx0.globalContext
  let preGCtx ← children.foldlM (init := gctx0) fun gctx child =>
    extractInfo gctx child
  -- Phase 2: Elaborate with the pre-registered context
  let getKind (i : Fin argDecls.size) := ElabArgKind.ofArgDeclKind argDecls[i].kind
  let preCtx := .empty preGCtx
  let args ← runSyntaxElaborator (argc := argDecls.size) getKind se preCtx stxArgs
  pure (args, resultContext se preCtx args)

/--
Phase 1 helper for a single child function in a mutual recursive block.

Partially elaborates the child's name, bindings, and return type to extract
the function signature, then pre-registers it as an expression-level binding
in the GlobalContext. This makes all sibling function names (including self)
available when elaborating bodies in Phase 2.
-/
partial def extractFunctionInfo (gctx0 : GlobalContext) (child : Syntax) : ElabM GlobalContext := do
  let dialects := (← read).dialects
  let syntaxElabs := (← read).syntaxElabs
  let some childIdent := qualIdentKind child
    | return panic! s!"Unknown command {child.getKind}"
  let some childLoc := mkSourceRange? child
    | panic! "extractFunctionInfo: child missing source location"
  let some childDecl := dialects.lookupOpDecl childIdent
    | logInternalError childLoc s!"extractFunctionInfo: unknown op declaration {childIdent}"
      return default
  let some childSe := syntaxElabs[childIdent]?
    | logInternalError childLoc s!"extractFunctionInfo: no syntax elaborator for {childIdent}"
      return default
  let childStxArgs := child.getArgs
  let childArgDecls := childDecl.argDecls.toArray
  -- Look for @[declareFn(name, args, type)] metadata on the child op
  for spec in childDecl.newBindings do
    let (nameArgLevel, argsArgLevel, typeArgLevel) ←
      match spec with
      | .value b =>
        -- declareFn produces a .value binding with nameIndex, argsIndex, typeIndex
        match b.argsIndex with
        | some argsIdx => pure (b.nameIndex.toLevel, argsIdx.toLevel, b.typeIndex.toLevel)
        | none => continue
      | _ => continue
    -- Elaborate name
    let some nameSL := argSyntaxLevel? childSe nameArgLevel
      | continue
    if nameSL ≥ childStxArgs.size then continue
    let .isTrue _ := decideProp (nameArgLevel < childArgDecls.size)
      | continue
    let nameCat := childArgDecls[nameArgLevel].kind.categoryOf
    let (nameTree, nameSuccess) ← runChecked <|
      catElaborator nameCat (.empty gctx0) childStxArgs[nameSL]!
    if !nameSuccess then continue
    let name ←
      match nameTree.info with
      | .ofIdentInfo info => pure info.val
      | _ => logInternalError childLoc "extractFunctionInfo: expected ident for function name"
             continue
    -- Elaborate typeArgs (scope parent of bindings) to bring type params into scope
    let baseCtx := TypingContext.empty gctx0
    let elabCtx ← do
      let .isTrue hArgs := decideProp (argsArgLevel < childDecl.argDecls.size)
        | logInternalError childLoc
            s!"extractFunctionInfo: argsArgLevel {argsArgLevel} out of bounds ({childDecl.argDecls.size})"
          pure baseCtx
      match childDecl.argDecls.argScopeLevel ⟨argsArgLevel, hArgs⟩ with
      | .error e =>
        logInternalError childLoc s!"extractFunctionInfo: argScopeLevel error: {e}"
        pure baseCtx
      | .ok none => pure baseCtx
      | .ok (some taFin) =>
        let taLvl : Nat := taFin
        let some taSL := argSyntaxLevel? childSe taLvl
          | logInternalError childLoc "extractFunctionInfo: argSyntaxLevel? failed for typeArgs"
            pure baseCtx
        if taSL ≥ childStxArgs.size then
          logInternalError childLoc
            s!"extractFunctionInfo: typeArgs syntax level {taSL} out of bounds ({childStxArgs.size})"
          pure baseCtx
        else
          let taCat := childDecl.argDecls[taLvl].kind.categoryOf
          let (taTree, taOk) ← runChecked <|
            catElaborator taCat baseCtx childStxArgs[taSL]!
          if !taOk then
            logInternalError childLoc "extractFunctionInfo: failed to elaborate typeArgs"
            pure baseCtx
          else pure taTree.resultContext
    -- Elaborate bindings (parameters) to get parameter types
    let some argsSL := argSyntaxLevel? childSe argsArgLevel
      | continue
    if argsSL ≥ childStxArgs.size then continue
    let .isTrue _ := decideProp (argsArgLevel < childArgDecls.size)
      | continue
    let argsCat := childArgDecls[argsArgLevel].kind.categoryOf
    let (argsTree, argsSuccess) ← runChecked <|
      catElaborator argsCat elabCtx childStxArgs[argsSL]!
    if !argsSuccess then continue
    let params ← collectNewBindingsM 0 argsTree fun _argLoc b =>
      match b.kind with
      | .expr tp => pure (some (b.ident, tp))
      | _ => pure none
    let params := params.filterMap id
    -- Elaborate return type
    let some typeSL := argSyntaxLevel? childSe typeArgLevel
      | continue
    if typeSL ≥ childStxArgs.size then continue
    let .isTrue _ := decideProp (typeArgLevel < childArgDecls.size)
      | continue
    let typeCat := childArgDecls[typeArgLevel].kind.categoryOf
    let (typeTree, typeSuccess) ← runChecked <|
      catElaborator typeCat elabCtx childStxArgs[typeSL]!
    if !typeSuccess then continue
    let retType ←
      match typeTree.info with
      | .ofTypeInfo info => pure info.typeExpr
      | _ => logInternalError childLoc "extractFunctionInfo: expected type for return type"
             continue
    -- Build function type: (param1Type → param2Type → ... → retType)
    let fnType := TypeExprF.mkFunType childLoc params retType
    -- Register in GlobalContext as an expression binding
    let .isFalse nameIsNew := decideProp (name ∈ gctx0)
      | logError childLoc s!"Function '{name}' is already declared."
        continue
    return gctx0.define name (.expr fnType) nameIsNew
  return gctx0

/--
Phase 1 helper for a single child operation in a mutual block.

Partially elaborates the child's name and typeParams args to extract
the type name and parameter names, then pre-registers the type in the
`TypingContext`'s `GlobalContext` via `preRegisterType`. Returns the
updated `TypingContext` with the new type registered.
-/
partial def extractDatatypeInfo (gctx0 : GlobalContext) (child : Syntax) : ElabM GlobalContext := do
  let dialects := (← read).dialects
  let syntaxElabs := (← read).syntaxElabs
  let some childIdent := qualIdentKind child
    | return panic! s!"Unknown command {child.getKind}"

  let some childLoc := mkSourceRange? child
    | panic! "extractDatatypeInfo: child missing source location"
  let some childDecl := dialects.lookupOpDecl childIdent
    | logInternalError childLoc s!"extractDatatypeInfo: unknown op declaration {childIdent}"
      return default
  let some childSe := syntaxElabs[childIdent]?
    | logInternalError childLoc s!"extractDatatypeInfo: no syntax elaborator for {childIdent}"
      return default
  let childStxArgs := child.getArgs
  let childArgDecls := childDecl.argDecls.toArray
  let mut gctxLoop := gctx0
  for spec in childDecl.newBindings do
    let (nameArgLevel, typeParamsArgLevel?) ←
      match spec with
      | .datatype b => pure (b.nameIndex.toLevel, some b.typeParamsIndex.toLevel)
      | .type b => pure (b.nameIndex.toLevel, b.argsIndex.map (·.toLevel))
      | _ => continue
    -- Elaborate name arg
    let some nameSL := argSyntaxLevel? childSe nameArgLevel
      | logInternalError childLoc
          "extractDatatypeInfo: argLevelToSyntaxLevel \
           failed for name"
        continue
    if nameSL ≥ childStxArgs.size then
      logInternalError childLoc
        s!"extractDatatypeInfo: nameSL {nameSL} \
           out of bounds ({childStxArgs.size})"
      continue
    let .isTrue _ := decideProp (nameArgLevel < childArgDecls.size)
      | logInternalError childLoc
          s!"extractDatatypeInfo: nameArgLevel \
             {nameArgLevel} out of bounds \
             ({childArgDecls.size})"
        continue
    let nameCat := childArgDecls[nameArgLevel].kind.categoryOf
    let gctx := gctxLoop
    let (nameTree, nameSuccess) ← runChecked <|
      catElaborator nameCat (.empty gctx) childStxArgs[nameSL]!
    if !nameSuccess then continue
    let name ←
      match nameTree.info with
      | .ofIdentInfo info =>
        pure info.val
      | _ =>
        logInternalError childLoc "extractDatatypeInfo: expected ident for type name"
        continue

    let .isFalse nameIsNew := decideProp (name ∈ gctx)
      | logError nameTree.info.loc s!"Type '{name}' is already declared."
        continue

    -- Elaborate typeParams to extract real param names
    let some tpArgLevel := typeParamsArgLevel?
      | -- .type spec with no argsIndex: register with empty params
        gctxLoop := gctx.define name (.type [] none) nameIsNew
        continue
    let some tpSL := argSyntaxLevel? childSe tpArgLevel
      | logInternalError childLoc
          "extractDatatypeInfo: argLevelToSyntaxLevel \
           failed for typeParams"
        continue
    if tpSL ≥ childStxArgs.size then
      logInternalError childLoc
        s!"extractDatatypeInfo: tpSL {tpSL} \
           out of bounds ({childStxArgs.size})"
      continue
    if tpArgLevel ≥ childArgDecls.size then
      logInternalError childLoc
        s!"extractDatatypeInfo: tpArgLevel \
           {tpArgLevel} out of bounds \
           ({childArgDecls.size})"
      continue
    let tpCat := childArgDecls[tpArgLevel]!.kind.categoryOf
    let (tpTree, tpSuccess) ← runChecked <|
      catElaborator tpCat (.empty gctx0) childStxArgs[tpSL]!
    if !tpSuccess then
      return default
    let params ← collectNewBindingsM 0 tpTree fun argLoc b => do
      checkIsTypeKind argLoc b
      return b.ident
    gctxLoop := gctx.define name (.type params.toList none) nameIsNew

  return gctxLoop


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
      let info : IdentInfo := { inputCtx := tctx, loc := loc, val := stx.getId.toString (escape := false) }
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
  | q`Init.SemicolonSepBy =>
    elabSeqWith c .semicolon "semicolonSepBy" (·.getSepArgs)
  | q`Init.SpaceSepBy =>
    elabSeqWith c .space "spaceSepBy" (·.getArgs)
  | q`Init.SpacePrefixSepBy =>
    elabSeqWith c .spacePrefix "spacePrefixSepBy" (·.getArgs)
  | q`Init.NewlineSepBy =>
    elabSeqWith c .newline "newlineSepBy" (·.getArgs)
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
    let getKind (i : Fin argTypes.size) : ElabArgKind :=
          .typeExpr argTypes[i]
    let se : SyntaxElaborator := {
            syntaxCount := args.size
            argElaborators := Array.ofFn fun (⟨lvl, lvlp⟩ : Fin args.size) =>
              let e := { syntaxLevel := lvl, argLevel := lvl }
              ⟨e, lvlp⟩
            resultScope := none
          }
    let args ← runSyntaxElaborator getKind se tctx ⟨args, Eq.refl args.size⟩
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
    let getKind (i : Fin argDecls.size) :=
      ElabArgKind.ofArgDeclKind argDecls[i].kind
    let (args, success) ← runChecked <|
      runSyntaxElaborator getKind se tctx stxArgs
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

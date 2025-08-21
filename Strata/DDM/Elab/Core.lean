/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Elab.DeclM
import Strata.DDM.Elab.Tree

open Lean (
    Message
    Name
    Syntax
    nullKind
  )
open Strata.Parser (DeclParser InputContext ParserState)

namespace Strata

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
  | .ident i a => .ident i <$> a.mapM fun e => expandMacros m e args
  | .arrow a b => .arrow <$> expandMacros m a args <*> expandMacros m b args
  | .fvar i a => .fvar i <$> a.mapM fun e => expandMacros m e args
  | .bvar idx => pure (.bvar idx)
  | .funMacro i r => do
    let r ← expandMacros m r args
    match args i with
    | none =>
      .error ()
    | some a =>
      let addType tps _ s args := tps.push (resolveBindingType m s args)
      let argTypes := foldArgBindingSpecs m addType (init := #[]) a
      --let argTypes := foldOverArgAtLevel m addType (init := #[]) bindings args level
      pure <| argTypes.foldr (init := r) .arrow

namespace Elab

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

structure ElabState where
  -- Errors found in elaboration.
  errors : Array (Syntax × Message) := #[]

@[reducible]
def ElabM α := ReaderT ElabContext (StateM ElabState) α

instance : ElabClass ElabM where
  getInputContext := return (←read).inputContext
  getDialects := return (←read).dialects
  getOpenDialects := return (←read).openDialectSet
  getGlobalContext := return (←read).globalContext
  getErrorCount := return (←get).errors.size
  logErrorMessage stx msg :=
    modify fun s => { s with errors := s.errors.push (stx, msg) }

section

abbrev FailureArray := Array (Syntax × String)

inductive MaybeQualifiedIdent where
| qid : QualifiedIdent → MaybeQualifiedIdent
| name : String → MaybeQualifiedIdent
deriving Inhabited

def resolveTypeBinding (tctx : TypingContext) (stx : Syntax) (name : String)
    (binding : TypingContext.VarBinding) (args : Array Tree) : ElabM Tree := do
  match binding with
  | .bvar idx k =>
    if let some a := args[0]? then
      logErrorMF a.info.stx mf!"Unexpected arguments to {name}."
      return default
    if let .type [] _ := k then
      let info : TypeInfo := { inputCtx := tctx, stx := stx, typeExpr := .bvar idx, isInferred := false }
      return .node (.ofTypeInfo info) #[]
    else
      logErrorMF stx mf!"Expected a type instead of {k}"
      return default
  | .fvar fidx k =>
    match k with
    | .expr tp =>
      logErrorMF stx mf!"Expected a type instead of expression with type {tp}."
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
            | logErrorMF c.info.stx mf!"Expected type"
          tpArgs := tpArgs.push cinfo.typeExpr
          children := children.push c
        let tp :=  .fvar fidx tpArgs
        let info : TypeInfo := { inputCtx := tctx, stx := stx, typeExpr := tp, isInferred := false }
        return .node (.ofTypeInfo info) children
      else if let some a := args[params.size]? then
        logErrorMF a.info.stx mf!"Unexpected argument to {name}."
        return default
      else
        logErrorMF stx mf!"{name} expects {params.size} arguments."
        return default

/--
This translate a possibly qualified identifier into a declaration in an
open dialect.
-/
def resolveTypeOrCat (stx : Syntax) (tpId : MaybeQualifiedIdent) : ElabM (Option (QualifiedIdent × TypeOrCatDecl)) :=
  match tpId with
  | .qid qid => do
    let decls := (← read).typeOrCatDeclMap.get qid.name
    let decls := decls.filter fun (dialect, _) => dialect = qid.dialect
    match decls[0]? with
    | none => do
      logErrorMF stx mf!"Undeclared type or category {qid}."
      return none
    | some (_, decl) =>
      assert! decls.size = 1
      return some (qid, decl.val)
  | .name name => do
    let m := (← read).typeOrCatDeclMap
    let decls:= m.get name
    match decls[0]? with
    | none => do
      logErrorMF stx mf!"Undeclared type or category {name}."
      return none
    | some (d, decl) =>
      if let some (candD, _) := decls[1]? then
        assert! d ≠ candD
        logError stx s!"{name} is ambiguous: declared in {d} and {candD}."
        return none
      else
        return some ({ dialect := d, name }, decl.val)

def translateQualifiedIdent (t : Tree) : MaybeQualifiedIdent :=
  let op := t.info.asOp!.op
  match op.name, op.args with
  | q`Init.qualifiedIdentImplicit, #[.ident name] =>
    .name name
  | q`Init.qualifiedIdentExplicit, #[.ident dialect, .ident name] =>
    .qid { dialect, name }
  | q`Init.qualifiedIdentType, #[] =>
    .qid { dialect := "Init", name := "Type" }
  | name, _ =>
    panic! s!"Unknown qualified ident {name.fullName}"

def asTypeInfo (tree : Tree) : ElabM TypeInfo := do
  match tree.info with
  | .ofTypeInfo info =>
    return info
  | _ =>
    logError tree.info.stx "Expected type."
    return default

def checkArgSize {α} [ToStrataFormat α] (stx : Syntax) (name : α) (expected : Nat) (args : Array Tree) : ElabM Unit := do
  if p : expected < args.size then
    logErrorMF args[expected].info.stx mf!"Unexpected argument to {name}."
  else if expected > args.size then
    logErrorMF stx mf!"{name} expects {expected} arguments."

/--
This resolves a type identifer using the name of the type (as `name`) and the
arguments (as `args`) passed into it.
-/
def translateTypeIdent (elabInfo : ElabInfo) (qualIdentInfo : Tree) (args : Array Tree) : ElabM Tree := do
  let stx := qualIdentInfo.info.stx
  let tctx := qualIdentInfo.info.inputCtx
  let tpId := translateQualifiedIdent qualIdentInfo

  if let .name name := tpId then
    if let some binding := tctx.lookupVar name then
      return ← resolveTypeBinding tctx stx name binding args

  let some (ident, decl) ← resolveTypeOrCat stx tpId
    | return default

  match decl with
  | .type decl =>
    checkArgSize stx ident decl.argNames.size args
    let tpArgs ← args.mapM fun a => return (← asTypeInfo a).typeExpr
    let tp := .ident ident tpArgs
    let info : TypeInfo := { toElabInfo := elabInfo, typeExpr := tp, isInferred := false }
    return .node (.ofTypeInfo info) args
  | .syncat decl =>
    let (_, success) ← runChecked <| checkArgSize stx ident decl.argNames.size args
    if !success then
      return default
    let mut sc : SyntaxCat := .atom ident
    for a in args do
      match a.info with
      | .ofCatInfo info =>
        sc := .app sc info.cat
      | _ =>
        logError a.info.stx "Expected category."
        return default
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
partial def grnf (gctx : GlobalContext) (e : TypeExpr) : TypeExpr :=
  match e with
  | .arrow _ _ | .ident _ _ | .bvar _ => e
  | .fvar idx args =>
    match gctx.kindOf! idx with
    | .expr _ => panic! "Type free variable bound to expression."
    | .type params (some d) =>
      assert! params.length = args.size
      assert! !d.hasUnboundVar (bindingCount := args.size)
      grnf gctx (d.instType args)
    | .type _ none => e

/--
This expands type aliases appearing at the head of the term so
the root is in a normal form.
-/
partial def rnf (tctx : TypingContext) (e : TypeExpr) : TypeExpr :=
  match e with
  | .arrow _ _ | .ident _ _ => e
  | .fvar idx args =>
    let gctx := tctx.globalContext
    match gctx.kindOf! idx with
    | .expr _ => panic! "Type free variable bound to expression."
    | .type params (some d) =>
      assert! params.length = args.size
      assert! !d.hasUnboundVar (bindingCount := args.size)
      rnf (.empty gctx) (d.instType args)
    | .type _ none => e
  | .bvar idx =>
    match tctx.bindings[tctx.bindings.size - 1 - idx]!.kind with
    | .type params (some d) =>
      assert! params.isEmpty
      assert! d.isGround
      rnf (tctx.drop (idx + 1)) d
    | .type _ none => e
    | _ => panic! "Expected a type"

/--
This checks that two types `itype` and `rtype` are equivalent.

In this context, `itype` refers to a type inferred from an operator argument
at position `stx` and `rtype` refers to a type inferred or specifed by a previous
argument.
-/
partial def checkExpressionType (tctx : TypingContext) (itype rtype : TypeExpr) : ElabM Bool := do
  let itype := rnf tctx itype
  let rtype := rnf tctx rtype
  match itype, rtype with
  | .ident iq ia, .ident rq ra =>
    if p : iq = rq ∧ ia.size = ra.size then do
      for i in Fin.range ia.size do
        if !(← checkExpressionType tctx ia[i] ra[i]) then
          return false
      return true
    else
      return false
  | .bvar ii, .bvar ri =>
    return ii = ri
  | .fvar ii ia, .fvar ri ra =>
    if p : ii = ri ∧ ia.size = ra.size then do
      for i in Fin.range ia.size do
        if !(← checkExpressionType tctx ia[i] ra[i]) then
          return false
      return true
    else
      return false
  | .arrow ia ir, .arrow ra rr =>
    return (← checkExpressionType tctx ia ra)
        && (← checkExpressionType tctx ir rr)
  | _, _ =>
    pure false

mutual

partial def unifyTypeVectors
  (b : ArgDecls)
  (argLevel0 : Fin b.size)
  (ea : Array TypeExpr)
  (tctx : TypingContext)
  (exprSyntax : Syntax)
  (ia : Array TypeExpr)
  (args : Vector (Option Tree) b.size)
  : ElabM (Vector (Option Tree) b.size) := do
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
    (b : ArgDecls)
    (argLevel0 : Fin b.size)
    (expectedType : TypeExpr)
    (tctx : TypingContext)
    (exprSyntax : Syntax)
    (inferredType : TypeExpr)
    (args : Vector (Option Tree) b.size)
    : ElabM (Vector (Option Tree) b.size) :=
  let ⟨argLevel, argLevelP⟩ := argLevel0
  -- Expand defined free vars at root to get head norm form
  let expectedType := grnf tctx.globalContext expectedType
  match expectedType with
  | .ident eid ea => do
    let ih := rnf tctx inferredType
    match ih with
    | .ident iid ia =>
      if eid != iid then
        logErrorMF exprSyntax mf!"Encountered {ih} expression when {expectedType} expected."
        return args
      assert! ea.size = ia.size
      unifyTypeVectors b argLevel0 ea tctx exprSyntax ia args
    | _ =>
      logErrorMF exprSyntax mf!"Encountered {ih} expression when {expectedType} expected."
      return args
  | .fvar eid ea =>
    match rnf tctx inferredType with
    | .fvar iid ia => do
      if eid != iid then
        logErrorMF exprSyntax mf!"Encountered {inferredType} expression when {expectedType} expected."
        return args
      assert! ea.size = ia.size
      unifyTypeVectors b argLevel0 ea tctx exprSyntax ia args
    | ih => do
      logErrorMF exprSyntax mf!"Encountered {ih} expression when {expectedType} expected."
      return args
  | .bvar idx => do
    let .isTrue idxP := inferInstanceAs (Decidable (idx < argLevel))
      | return panic! "Invalid index"
    let typeLevel := argLevel - (idx + 1)
    have typeLevelP : typeLevel < b.size := by omega
    -- Verify type level is a type parameter.
    assert! b[typeLevel].kind.isType

    match args[typeLevel] with
    | none => do
      let einfo : ElabInfo := { stx := exprSyntax, inputCtx := tctx }
      let info : TypeInfo := { toElabInfo := einfo, typeExpr := inferredType, isInferred := true }
      return args.set typeLevel (some (.node (.ofTypeInfo info) #[]))
    | some t => do
      let .ofTypeInfo info := t.info
        | panic! "Expected type info"
      if !(← checkExpressionType tctx inferredType info.typeExpr) then
        logErrorMF exprSyntax mf!"Expression has type {withBindings tctx.bindings (mformat inferredType)} when {withBindings tctx.bindings (mformat info.typeExpr)} expected."
      pure args
  | .arrow ea er =>
    match inferredType with
    | .ident .. | .bvar _ | .fvar .. => do
      logErrorMF exprSyntax mf!"Expected {expectedType} when {inferredType} found"
      pure args
    | .arrow ia ir => do
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
  let info : OptionInfo := { stx := stx, inputCtx := tctx }
  if stx.matchesNull 0 then
    pure <| .node (.ofOptionInfo info) #[]
  else do
    assert! stx.matchesNull 1
    let tree ← f tctx (stx.getArg 0)
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
    (f : Syntax → Binding → m α) : m (Array α) := do
  assert! (initialScope ≤ tree.info.inputCtx.bindings.size)
  let stx := tree.info.stx
  let bindings := tree.resultContext.bindings.toArray
  let init : Array α := .mkEmpty (bindings.size - initialScope)
  bindings.foldlM (init := init) (start := initialScope) fun r b => r.push <$> f stx b

def elabArgIndex {α} {n}
    (initialScope : Nat)
    (trees : Vector Tree n)
    (argsIndex : Option (DebruijnIndex n))
    (f : Syntax → Binding → ElabM α) :
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

def logInternalError [ElabClass m] (stx : Syntax) (msg : String) : m Unit :=
  logError stx msg

/--
Evaluate the tree as a type expression.
-/
partial def translateSyntaxCat (tree : Tree) : ElabM SyntaxCat := do
  let (⟨argInfo, argChildren⟩, args) := flattenTypeApp tree #[]
  let op :=
        match argInfo with
        | .ofOperationInfo info => info.op.name
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match op, argChildren with
  | q`Init.TypeIdent, #[ident] => do
    let tpId := translateQualifiedIdent ident
    let some (qname, decl) ← resolveTypeOrCat ident.info.stx tpId
      | return default
    match decl with
    | .syncat decl =>
      checkArgSize argInfo.stx qname decl.argNames.size args
      let r : SyntaxCat := .atom qname
      args.attach.foldlM (init := r) fun r ⟨a, _⟩ => do
        have p : sizeOf a < sizeOf args := by decreasing_tactic
        return .app r (← translateSyntaxCat a)
    | _ =>
      logError ident.info.stx s!"Expected category"; pure default

  | q`StrataDDL.TypeFn, _ => do
    logError argInfo.stx s!"Expected category"
    return default

  | _, _ =>
    logInternalError argInfo.stx s!"translateSyntaxCat given invalid op {op}"
    return default

/--
Evaluate the tree as a type expression.
-/
def translateTypeExpr (tree : Tree) : ElabM TypeExpr := do
  match feq : flattenTypeApp tree #[] with
  | (⟨argInfo, argChildren⟩, args) =>
  have argcP : sizeOf argChildren < sizeOf tree := by
    have p := flattenTypeApp_size tree #[]
    have q := Array.sizeOf_min args
    simp [feq] at p
    omega
  have argsP : sizeOf args ≤ sizeOf tree := by
    have p := flattenTypeApp_size tree #[]
    have q := Array.sizeOf_min argChildren
    simp [feq] at p
    omega
  let op :=
        match argInfo with
        | .ofOperationInfo info => info.op.name
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match op, argC_eq : argChildren with
  | q`Init.TypeIdent, #[ident] => do
    let tpId := translateQualifiedIdent ident
    let some (qname, decl) ← resolveTypeOrCat ident.info.stx tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize argInfo.stx qname decl.argNames.size args
      let args ← args.attach.mapM fun ⟨a, _⟩ =>
        have p : sizeOf a < sizeOf args := by decreasing_tactic
        translateTypeExpr a
      return .ident qname args
    | _ =>
      logError ident.info.stx s!"Expected type"; pure default
  | q`Init.TypeArrow, #[aTree, rTree] => do
    have p : sizeOf aTree < sizeOf argChildren := by decreasing_tactic
    let aType ← translateTypeExpr aTree
    have p : sizeOf rTree < sizeOf argChildren := by decreasing_tactic
    let rType ← translateTypeExpr rTree
    return .arrow aType rType

  | q`StrataDDL.TypeFn, #[bindingsTree, valTree] =>
    logError argInfo.stx s!"Macros not supported"
    return default
  | _, _ =>
    logInternalError argInfo.stx s!"translateTypeExpr given invalid syntax {repr op}"
    return default
  termination_by tree

/--
Evaluate the tree as a type expression.
-/
partial def translateBindingKind (tree : Tree) : ElabM BindingKind := do
  let (⟨argInfo, argChildren⟩, args) := flattenTypeApp tree #[]
  let op :=
        match argInfo with
        | .ofOperationInfo info => info.op.name
        | _ => panic! s!"translateBindingTypeExpr expected operator, type or cat {repr argInfo}"
  match op, argChildren with
  | q`Init.TypeIdent, #[ident] => do
    let tpId := translateQualifiedIdent ident
    let stx := ident.info.stx
    let some (qname, decl) ← resolveTypeOrCat stx tpId
      | return default
    match decl with
    | .type decl =>
      checkArgSize argInfo.stx qname decl.argNames.size args
      let args ← args.mapM translateTypeExpr
      return .expr (.ident qname args)
    | .syncat decl =>
      checkArgSize argInfo.stx qname decl.argNames.size args
      let r : SyntaxCat := .atom qname
      let r ← args.foldlM (init := r) fun r a => do
        return .app r (← translateSyntaxCat a)
      return .cat r
  | q`Init.TypeArrow, #[aTree, rTree] => do
    let aType ← translateTypeExpr aTree
    let rType ← translateTypeExpr rTree
    pure <| .expr <| .arrow aType rType
  | q`StrataDDL.TypeFn, _ => do
    logError argInfo.stx s!"Macros not supported"
    pure default
  | _, _ =>
    logInternalError argInfo.stx s!"translateArgDeclKind given invalid kind {op}"
    return default

/--
Construct a binding from a binding spec and the arguments to a operation.
-/
def evalBindingSpec
    {bindings}
    (initSize : Nat)
    (b : BindingSpec bindings)
    (args : Vector Tree bindings.size)
    : ElabM Binding := do
  match b with
  | .value b =>
    let ident := evalBindingNameIndex args b.nameIndex
    let (bindings, success) ← runChecked <| elabArgIndex initSize args b.argsIndex fun stx b =>
          match b.kind with
          | .expr tp =>
            return (b.ident, tp)
          | .type _ _ | .cat _ => do
            logError stx "Expecting expressions in variable binding"
            pure default
    if !success then
      return default
    let typeTree := args[b.typeIndex.toLevel]
    let kind ←
          match typeTree.info with
          | .ofTypeInfo info =>
            pure <| .expr (.mkFunType bindings info.typeExpr)
          | .ofCatInfo info =>
            if !b.allowCat then
              panic! s!"Cannot bind {ident} unexpected category {repr info.cat}"
            else if !bindings.isEmpty then
              panic! s!"Arguments not allowed on category."
            else if let .atom q`Init.Type := info.cat then
              pure <| .type [] none
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
    let params ← elabArgIndex initSize args b.argsIndex fun stx b => do
          match b.kind with
          | .type [] _ =>
            pure ()
          | .type _ _ | .expr _ | .cat _ => do
            logError stx s!"{b.ident} must be have type Type instead of {repr b.kind}."
          return b.ident
    let value : Option TypeExpr :=
          match b.defIndex with
          | none => none
          | some idx =>
            match args[idx.toLevel].info with
            | .ofTypeInfo info =>
              some info.typeExpr
            | _ =>
              panic! "Bad arg"
    pure { ident, kind := .type params.toList value }

namespace TypingContext

/--
Attempt to interpret `e` as a `n`-ary function, and
return the type of the arguments along with the return type if possible,
or `error (args, r)` where `args` is an array with size `args.size < n` and `r`
is the resulting type.
-/
def applyNArgs (tctx : TypingContext) (e : TypeExpr) (n : Nat) := aux #[] e
  where aux (args : Array TypeExpr) (e : TypeExpr) : Except (Array TypeExpr × TypeExpr) (Vector TypeExpr n × TypeExpr) :=
    if argsLt : args.size < n then
      match rnf tctx e with
      | .arrow a r => aux (args.push a) r
      | e => .error (args, e)
    else
      if argsGt : args.size > n then
        .ok (⟨args.take n, by simp; omega⟩, e)
      else
        .ok (⟨args, by omega⟩, e)

end TypingContext

/--
Given a type expression and a natural number, this returns a
-/
def resultType! (tctx : TypingContext) (e : TypeExpr) (n : Nat) : TypeExpr :=
  match tctx.applyNArgs e n with
  | .ok (_, r) => r
  | .error (n, _) => panic! s!"{n.size} unexpected arguments to function."

partial def inferType (tctx : TypingContext) (e : Expr) : ElabM TypeExpr := do
  let ⟨f, a⟩ := e.hnf
  match f with
  | .bvar idx => do
    let .isTrue idxP := inferInstanceAs (Decidable (idx < tctx.bindings.size))
      | return panic! "Invalid index {idx}"
    let lvl := tctx.bindings.size - 1 - idx
    let b := tctx.bindings[lvl]
    match b.kind with
    | .expr tp =>
      -- Arguments in the type context
      return resultType! tctx (tp.incIndices (idx + 1)) a.val.size
    | _ => panic! "Expected an expression"
  | .fvar idx =>
    match tctx.globalContext.kindOf! idx with
    | .expr tp =>
      return resultType! tctx tp a.val.size
    | .type _ _ => panic! "Expected expression instead of type."
  | .fn ident => do
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
    let tp := Id.run <| tp.instTypeM fun i =>
        assert! i < fnArgCount
        let lvl := fnArgCount - i - 1
        match a.val[lvl]! with
        | .type tp => tp
        | arg =>
           panic! s!"Cannot instantiate type {repr tp} with args {repr a}"
    return resultType! tctx tp (a.val.size - fnArgCount)
  | .app f a => panic! "Invalid app in result of Expr.hnf"

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
        | logError aType.info.stx s!"Expected type"; return default
      let rType ← translateTypeTree rTree
      let .ofTypeInfo rInfo := rType.info
        | logError rType.info.stx s!"Expected type"; return default
      let tp := .arrow aInfo.typeExpr rInfo.typeExpr
      let info : TypeInfo := { toElabInfo := info.toElabInfo, typeExpr := tp, isInferred := false }
      return .node (.ofTypeInfo info) #[aType, rType]
    | _, _ =>
      logInternalError arg.info.stx s!"translateTypeTree given invalid operation {repr op}"
      return default
  | _ =>
    panic! s!"translateTypeExpr expected operator {repr arg}"

mutual

partial def elabOperation (tctx : TypingContext) (stx : Syntax) : ElabM Tree := do
  if stx.getKind = `choice then
    logError stx s!"Parsing ambiguity {stx}"
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
  let ((args, newCtx), success) ← runChecked <| runSyntaxElaborator se decl.argDecls tctx stx.getArgs
  if !success then
    return default
  let newBindings := decl.newBindings
  let resultCtx ← newBindings.foldlM (init := newCtx) <| fun ctx spec => do
    ctx.push <$> evalBindingSpec initSize spec args
  let op : Operation := { name := i, args := args.toArray.map (·.arg) }
  let info : OperationInfo := { stx := stx, inputCtx := tctx, op, resultCtx }
  return .node (.ofOperationInfo info) args.toArray

partial def runSyntaxElaborator
  (se : SyntaxElaborator)
  (b : ArgDecls)
  (tctx0 : TypingContext)
  (args : Array Syntax) : ElabM (Vector Tree b.size × TypingContext) := do
  let mut trees : Vector (Option Tree) b.size := .replicate b.size none
  for ae in se.argElaborators do
    let .isTrue syntaxLevelP := inferInstanceAs (Decidable (ae.syntaxLevel < args.size))
        | return panic! "Invalid syntaxLevel"
    let argLevel := ae.argLevel
    let .isTrue argLevelP := inferInstanceAs (Decidable (argLevel < b.size))
        | return panic! "Invalid argLevel"
    let tctx ←
      match ae.contextLevel with
      | some idx =>
        match trees[idx] with
        | some t => pure t.resultContext
        | none => continue
      | none => pure tctx0
    let astx := args[ae.syntaxLevel]
    let expectedKind := b[argLevel].kind
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
          logError astx s!"Could not infer type."
        | .ok expectedType => do
          trees ← unifyTypes b ⟨argLevel, argLevelP⟩ expectedType tctx astx inferredType trees
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
      let .isTrue p := inferInstanceAs (Decidable (idx < b.size))
        | return panic! "Invalid index"
      treesr[idx].resultContext
  return (treesr, tctx)

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
    logErrorMF stx mf!"Expected a type."
  pure tree

partial def catElaborator (c : SyntaxCat) : TypingContext → Syntax → ElabM Tree :=
  match c with
  | .atom q`Init.Expr =>
    elabExpr
  | .atom q`Init.Ident =>
    fun tctx stx =>
      let info : IdentInfo := { inputCtx := tctx, stx := stx, val := stx.getId.toString }
      pure <| .node (.ofIdentInfo info) #[]
  | .atom q`Init.Num =>
    fun tctx stx =>
      match stx.isNatLit? with
      | some v =>
        let info : NumInfo := { inputCtx := tctx, stx := stx, val := v }
        pure <| .node (.ofNumInfo info) #[]
      | none =>
        panic! s!"Invalid Init.Num {repr stx}"
  | .atom q`Init.Decimal =>
    fun tctx stx =>
      match stx.isScientificLit? with
      | some (m, eIsNeg, e) =>
        let d : Decimal := { mantissa := m, exponent := if eIsNeg then .negOfNat e else .ofNat e }
        let info : DecimalInfo := { inputCtx := tctx, stx := stx, val := d }
        pure <| .node (.ofDecimalInfo info) #[]
      | none =>
        panic! s!"Invalid Init.Num {repr stx}"
  | .atom q`Init.Str =>
    fun tctx stx =>
      match stx.isStrLit? with
      | some s =>
        let info : StrlitInfo := { inputCtx := tctx, stx := stx, val := s }
        pure <| .node (.ofStrlitInfo info) #[]
      | none =>
        panic! s!"String not supported {stx} {stx.isStrLit?}"
  | .atom q`Init.Type => elabType
  | .atom q`Init.TypeP =>
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
              | .ofCatInfo info => info.cat = .atom q`Init.Type
              | _ => false
        if !ok then
          logErrorMF stx mf!"Expected a type or Type instead of {c}"
        pure tree
  | .app (.atom q`Init.Option) a =>
    elabOption (catElaborator a)
  | .app (.atom q`Init.Seq) a =>
    let f := elabManyElement (catElaborator a)
    fun tctx stx => do
      let (args, resultCtx) ← stx.getArgs.foldlM f (#[], tctx)
      let info : SeqInfo := { inputCtx := tctx, stx := stx, args := args.map (·.arg), resultCtx }
      pure <| .node (.ofSeqInfo info) args
  | .app (.atom q`Init.CommaSepBy) a =>
    let f := elabManyElement (catElaborator a)
    fun tctx stx => do
      let (args, resultCtx) ← stx.getSepArgs.foldlM f (#[], tctx)
      let info : CommaSepInfo := { inputCtx := tctx, stx := stx, args := args.map (·.arg), resultCtx }
      pure <| .node (.ofCommaSepInfo info) args
  | .atom _ =>
    elabOperation
  | _ =>
    panic! s!"Unsupport category {eformat c}"

partial def elabExpr (tctx : TypingContext) (stx : Syntax) : ElabM Tree :=
  match stx.getKind with
  | `Init.exprParen =>
    elabExpr tctx stx[1]
  | `Init.exprIdent =>
    let name := elabIdent stx[0]
    if let some binding := tctx.lookupVar name then
      let einfo : ElabInfo := { stx, inputCtx := tctx }
      match binding with
      | .bvar idx k => do
        match k with
        | .expr _ =>
          let info : ExprInfo := { toElabInfo := einfo, expr := .bvar idx }
          return .node (.ofExprInfo info) #[]
        | .type _params _ =>
          logErrorMF stx mf!"{name} is a type when an expression is required."
          return default
        | .cat c =>
          logErrorMF stx mf!"{name} has category {c} when an expression is required."
          return default
      | .fvar idx k =>
        match k with
        | .expr _ =>
          let info : ExprInfo := { toElabInfo := einfo, expr := .fvar idx }
          return .node (.ofExprInfo info) #[]
        | _ => do
          logError stx s!"{name} is a type when expression required."
          return default
    else do
      logError stx s!"Unknown expr identifier {name}"
      return default
  | `Init.exprApp => do
    let fn := elabIdent stx[0]
    let args := stx[2].getSepArgs
    let ((fvar, bindings), success) ← runChecked <| do
          match tctx.lookupVar fn with
          | some (.fvar idx k) =>
            match k with
            | .expr tp =>
              let tctx : TypingContext := .empty tctx.globalContext
              match tctx.applyNArgs tp args.size with
              | .ok (argTypes, r) =>
                let b := Array.ofFn fun (i : Fin args.size) => {
                  ident := ""
                  kind := .type (.ofType argTypes[i])
                }
                pure (idx, b)
              | .error (a, r) =>
                if a.size = 0 then
                  logError stx[0] s!"Expected function"
                else
                  logError stx[0] s!"Expected function with {a.size} arguments."
                return default
            | .type _ _ =>
              logError stx[0] s!"Expression expected."
              return default
          | some (.bvar idx tp) =>
            logError stx[0] s!"Bound functions not yet supported."
            return default
          | none =>
            logError stx[0] s!"Unknown variable {fn}"
            return default
    if !success then
      return default
    let se : SyntaxElaborator := {
            argElaborators := Array.ofFn fun (⟨lvl, _⟩ : Fin args.size) =>
               { syntaxLevel := lvl, argLevel := lvl }
            resultScope := none
          }
    let (args, _) ← runSyntaxElaborator se bindings tctx args
    let e : Expr := Expr.fvar fvar
    let e := args.toArray.foldl (init := e) fun e t => .app e t.arg
    let info : ExprInfo := { stx := stx, inputCtx := tctx, expr := e }
    return .node (.ofExprInfo info) args.toArray
  | _ => do
    let some i := qualIdentKind stx
      | return panic! s!"Unknown expression {stx}"
    let some d := (←read).dialects[i.dialect]?
      | return panic! s!"Unknown dialect {i.dialect} in {stx}"
    let some fn := d.functions[i.name]?
      | return panic! (f!"unknown operation {eformat i}").pretty
    let some se := (←read).syntaxElabs[i]?
      | return panic! s!"Unknown expression elaborator {i.fullName}"
    let ((args, _), success) ← runChecked <| runSyntaxElaborator se fn.argDecls tctx stx.getArgs
    if !success then
      return default
    let e := args.toArray.foldl (init := Expr.fn i) fun e t => .app e t.arg
    let info : ExprInfo := { stx := stx, inputCtx := tctx, expr := e }
    return .node (.ofExprInfo info) args.toArray

end

def runElab (action : ElabM α) : DeclM α := do
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
      logErrorMessage stk.back <| Lean.mkErrorMessage inputContext pos stk err
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

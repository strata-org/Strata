/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.DDM.Format
set_option autoImplicit false

open Lean (Syntax)

public section
namespace Strata.Elab

/--
Information about the type or category of a bound variable.
-/
inductive BindingKind where
/-- Variable is an expression with the given type. -/
| expr (tp : TypeExpr)
/--
Variable is a type or parametric type.

Type variables may be declared as synonyms for existing
types.  In this case, the value is a type expression
over the parameters.
-/
| type (ann : SourceRange) (params : List String) (value : Option TypeExpr)
/--
Variable belongs to the particular category below.
-/
| cat (k : SyntaxCat)
/--
Variable is a polymorphic type variable (for function type parameters).
These are passed through to the dialect's typechecker for inference.
-/
| tvar (ann : SourceRange) (name : String)
deriving Inhabited, Repr

namespace BindingKind

instance : Coe TypeExpr BindingKind where
  coe tp := .expr tp

def ofCat (c : SyntaxCat) : BindingKind :=
  match c.name with
  | q`Init.Expr => panic! "Init.Expr may not appear as a category."
  | q`Init.Type => .type c.ann [] .none
  | _ => .cat c

def categoryOf : BindingKind → SyntaxCat
| .expr tp => .atom tp.ann q`Init.Expr
| .type loc _ _ => .atom loc q`Init.Type
| .tvar loc _ => .atom loc q`Init.Type
| .cat c => c

instance : ToStrataFormat BindingKind where
  mformat bk := private
    match bk with
    | .expr tp => mformat tp
    | .type _ params _ => mformat (params.foldr (init := f!"Type") (fun a f => f!"({a} : Type) -> {f}"))
    | .tvar _ name => mformat f!"tvar({name})"
    | .cat c => mformat c

end BindingKind

/--
A single binder may declare multiple identifiers, but they
all have the same type and metadata.
-/
structure Binding where
  ident : Var
  kind : BindingKind
deriving Inhabited, Repr

/--
A sequence of bindings.

Includes an additional map that maps the identifiers to the
index of the binder for them.
-/
structure Bindings where
  ofArray ::
  toArray : Array Binding

namespace Bindings

protected def ofList (l : List Binding) : Bindings := ofArray (l.toArray)

protected def isEmpty (b:Bindings) := b.toArray.isEmpty

protected def size (b:Bindings) := b.toArray.size

instance : GetElem Bindings Nat Binding (fun bs i => i < bs.size) where
  getElem bindings idx p := bindings.toArray[idx]'(by exact p)

protected def empty : Bindings where
  toArray := #[]

instance : EmptyCollection Bindings where
  emptyCollection := .empty

instance : Inhabited Bindings where
  default := .empty

instance : Repr Bindings where
  reprPrec b prec := Repr.addAppParen f!"ofArray {reprArg b.toArray}" prec

def push (bs : Bindings) (b : Binding) : Bindings where
  toArray := bs.toArray.push b

/-- Remove the last i pushed bindings -/
def drop (bs : Bindings) (count : Nat) : Bindings :=
  if count = 0 then
    bs
  else
    { toArray := bs.toArray.take (bs.toArray.size - count) }

end Bindings

structure TypingContext where
  private mk ::
  globalContext : GlobalContext := {}
  -- This stores all the bindings added to the typing context.
  bindings : Bindings := {}
  -- This maintains a map from variable names to the indices of variables
  -- with those names in bindings.
  -- The indices are stored in ascending order so that we can reset the
  -- typing context to an earlier state when needed.
  map : Std.HashMap Var (Array Nat) := {}
deriving Repr

namespace TypingContext

protected def empty (globalContext : GlobalContext) : TypingContext := { globalContext }

instance : Inhabited TypingContext where
  default := .empty {}

protected def push (tctx : TypingContext) (b : Binding) : TypingContext where
  globalContext := tctx.globalContext
  bindings := tctx.bindings.push b
  map := tctx.map.alter b.ident (fun md => md.getD #[] |>.push tctx.bindings.size)

/--
Remove the last `count` entries pushed to `tctx`.
-/
protected def drop (tctx : TypingContext) (count : Nat) : TypingContext where
  globalContext := tctx.globalContext
  bindings := tctx.bindings.drop count
  -- Update the map to remove the last entries.
  map :=
    tctx.bindings.toArray.foldr
      (init := tctx.map)
      (stop := tctx.bindings.size - count)
      fun b m => m.modify b.ident (·.pop)

protected def ofBindings (bs : Bindings) : TypingContext where
  globalContext := {}
  bindings := bs
  map :=
    bs.size.fold (init := {}) fun i p m =>
      m.alter bs[i].ident (fun md => md.getD #[] |>.push i)

protected def pushBindings (tctx : TypingContext) (b : Bindings) : TypingContext :=
  b.toArray.foldl .push tctx

/--
Create a new TypingContext with a different GlobalContext but the same local
bindings. Used for recursive datatype definitions where the datatype name needs to be added to the GlobalContext before parsing constructor field types.
-/
protected def withGlobalContext (tctx : TypingContext) (gctx : GlobalContext) : TypingContext where
  globalContext := gctx
  bindings := tctx.bindings
  map := tctx.map

/--
This contains information about a bound or global variable.
-/
inductive VarBinding
-- A bound variable with index
| bvar (idx : Nat) (tpc : BindingKind)
| fvar (idx : FreeVarIndex) (tp : GlobalKind)

protected def lookupVar (tctx : TypingContext) (var : String) : Option VarBinding :=
  let a := tctx.map.getD var #[]
  match a.back? with
  | some lvl =>
    assert! lvl < tctx.bindings.size
    let idx := tctx.bindings.size - 1 - lvl
    some (.bvar idx tctx.bindings[lvl]!.kind)
  | none =>
    let gctx := tctx.globalContext
    match gctx.findIndex? var with
    | some idx =>
      some (.fvar idx (gctx.kindOf! idx))
    | none =>
      none

end TypingContext

-----------------------------------------------------------------------
-- ElabInfo/Tree

/--
Common information for each node in the Strata info tree.
-/
structure ElabInfo where
  /-- Source location information. -/
  loc : SourceRange
  /-- The typing context for node. -/
  inputCtx : TypingContext
deriving Inhabited, Repr

structure OperationInfo extends ElabInfo where
  op : Operation
  resultCtx : TypingContext
deriving Inhabited, Repr

structure CatInfo extends ElabInfo where
  cat : SyntaxCat
deriving Inhabited, Repr

structure ExprInfo extends ElabInfo where
  expr : Expr
deriving Inhabited, Repr

structure TypeInfo extends ElabInfo where
  -- This may include macros so that it can be used in binding types.
  typeExpr : TypeExpr
  -- Flag that is set if the value was inferred from an expression type rather
  -- than set from an explicit type.
  -- When inferred from an expression, the syntax in the elab info points to the
  -- expression.
  isInferred : Bool
deriving Inhabited, Repr

structure ConstInfo (α : Type) extends ElabInfo where
  val : α
deriving Inhabited, Repr

abbrev IdentInfo := ConstInfo String

abbrev NumInfo := ConstInfo Nat

abbrev DecimalInfo := ConstInfo Decimal

abbrev StrlitInfo := ConstInfo String

structure OptionInfo extends ElabInfo where
  deriving Inhabited, Repr

structure SeqInfo extends ElabInfo where
  sep : SepFormat
  args : Array Arg
  resultCtx : TypingContext
deriving Inhabited, Repr

inductive Info
| ofOperationInfo (info : OperationInfo)
| ofCatInfo (info : CatInfo)
| ofExprInfo (info : ExprInfo)
| ofTypeInfo (info : TypeInfo)
| ofIdentInfo (info : IdentInfo)
| ofNumInfo (info : NumInfo)
| ofDecimalInfo (info : DecimalInfo)
| ofStrlitInfo (info : StrlitInfo)
| ofBytesInfo (info : ConstInfo ByteArray)
| ofOptionInfo (info : OptionInfo)
| ofSeqInfo (info : SeqInfo)
deriving Inhabited, Repr

namespace Info

def asOp! : Info → OperationInfo
| .ofOperationInfo info => info
| _ => panic! "Expected operation"

def asExpr! : Info → ExprInfo
| .ofExprInfo info => info
| info => panic! s!"Expected expression but given {repr info}"

def asType! : Info → TypeInfo
| .ofTypeInfo info => info
| info => panic! s!"Expected type but given {repr info}"

def asIdent! : Info → IdentInfo
| .ofIdentInfo info => info
| _ => panic! "Expected identifier"

def elabInfo (info : Info) : ElabInfo :=
  match info with
  | .ofOperationInfo info => info.toElabInfo
  | .ofCatInfo info => info.toElabInfo
  | .ofExprInfo info => info.toElabInfo
  | .ofTypeInfo info => info.toElabInfo
  | .ofIdentInfo info => info.toElabInfo
  | .ofNumInfo info => info.toElabInfo
  | .ofDecimalInfo info => info.toElabInfo
  | .ofStrlitInfo info => info.toElabInfo
  | .ofBytesInfo info => info.toElabInfo
  | .ofOptionInfo info => info.toElabInfo
  | .ofSeqInfo info => info.toElabInfo

def inputCtx (info : Info) : TypingContext := info.elabInfo.inputCtx

def loc (info : Info) : SourceRange := info.elabInfo.loc

end Info

inductive Tree
| node (info : Info) (children : Array Tree)
deriving Inhabited, Repr

namespace Tree

@[expose] def info : Tree → Info
| .node info _ => info

@[expose] def children : Tree → Array Tree
| .node _ c => c

instance : GetElem Tree Nat Tree fun t i => i < t.children.size where
  getElem xs i h := xs.children[i]

@[simp]
theorem node_getElem (info : Info) (c : Array Tree) (i : Nat) (p : i < (node info c).children.size) :
  (node info c)[i]'p = c[i]'(by apply p) := by rfl

def arg : Tree → Arg
| .node info children =>
  match info with
  | .ofOperationInfo info => .op info.op
  | .ofCatInfo info => .cat info.cat
  | .ofExprInfo info => .expr info.expr
  | .ofTypeInfo info => .type info.typeExpr
  | .ofIdentInfo info => .ident info.loc info.val
  | .ofNumInfo info => .num info.loc info.val
  | .ofDecimalInfo info => .decimal info.loc info.val
  | .ofStrlitInfo info => .strlit info.loc info.val
  | .ofBytesInfo info => .bytes info.loc info.val
  | .ofOptionInfo _ =>
    let r :=
      match children with
      | #[] => none
      | #[x] => some x.arg
      | _ => panic! "Unexpected option"
    .option info.loc r
  | .ofSeqInfo info => .seq info.loc info.sep info.args

theorem sizeOf_children (t : Tree) (i : Nat) (p : i < t.children.size) : sizeOf t[i] < sizeOf t := by
  match t with
  | .node info c =>
    have q := Array.sizeOf_getElem c i p
    simp [node_getElem]
    omega

def resultContext (t : Tree) : TypingContext :=
  match t.info with
  | .ofOperationInfo info => info.resultCtx
  | .ofCatInfo info => info.inputCtx
  | .ofExprInfo _ | .ofTypeInfo _ => t.info.inputCtx
  | .ofIdentInfo _ | .ofNumInfo _ | .ofDecimalInfo _ | .ofStrlitInfo _ | .ofBytesInfo .. => t.info.inputCtx
  | .ofOptionInfo info =>
    if p : t.children.size > 0 then
      have q : sizeOf t[0] < sizeOf t := sizeOf_children _ _ _
      resultContext t[0]
    else
      info.inputCtx
  | .ofSeqInfo info => info.resultCtx
termination_by t

def isSpecificOp (tree : Tree) (expected : QualifiedIdent) : Bool :=
  match tree.info with
  | .ofOperationInfo info => info.op.name = expected
  | _ => false

def asOption? (t : Tree) : Option (Option Tree) :=
  match t.info with
  | .ofOptionInfo _ => some t.children[0]?
  | _ => none

def asCommaSepInfo? (t : Tree) : Option (Array Tree) :=
  if let .ofSeqInfo info := t.info then
    if info.sep == .comma then
      some t.children
    else
      none
  else
    none

def asCommaSepInfo! (t : Tree) : Array Tree :=
  if let .ofSeqInfo info := t.info then
    if info.sep == .comma then
      t.children
    else
      panic! "Expected commaSepInfo"
  else
    panic! "Expected commaSepInfo"

/--
Retun array of bindings for a tree with category `Option Bindings`
-/
def optBindings! (optBindingsTree : Tree) : Array Tree :=
  match optBindingsTree.asOption? with
  | none => panic! "Expected option"
  | some none =>
    #[]
  | some (some t) =>
    assert! t.isSpecificOp q`StrataDDL.mkBindings
    assert! t.children.size = 1
    match t[0]!.asCommaSepInfo? with
    | none => panic! "Expected comma sep info"
    | some b => b

def asBindingType! (tree : Tree) : Tree :=
  assert! tree.isSpecificOp q`Init.mkBindingType
  assert! tree.children.size = 1
  tree[0]!

def binding! (tree : Tree) : IdentInfo × Tree × Option Tree := Id.run do
  assert! tree.isSpecificOp q`StrataDDL.mkBinding
  assert! tree.children.size = 3
  let .ofIdentInfo nameInfo := tree[0]!.info
    | panic! s!"Expected identifier {repr tree.info}"
  let some mdTree := tree[2]!.asOption?
      | panic! s!"Expected metadata to be option."
  return (nameInfo, tree[1]!.asBindingType!, mdTree)

end Tree

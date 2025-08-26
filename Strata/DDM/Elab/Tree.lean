/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DDM.Format

open Lean (Syntax)

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
| type (params : List String) (value : Option TypeExpr)
/--
Variable belongs to the particular category below.
-/
| cat (k : SyntaxCat)
deriving BEq, Inhabited, Repr

namespace BindingKind

instance : Coe TypeExpr BindingKind where
  coe tp := .expr tp

def ofCat (c : SyntaxCat) : BindingKind :=
  match c with
  | .atom q`Init.Expr => panic! "Init.Expr may not appear as a category."
  | .atom q`Init.Type => .type [] .none
  | c => .cat c

def categoryOf : BindingKind → SyntaxCat
| .expr _ => .atom q`Init.Expr
| .type _ _ => .atom q`Init.Type
| .cat c => c

instance : ToStrataFormat BindingKind where
  mformat
  | .expr tp => mformat tp
  | .type params _ => mformat (params.foldr (init := f!"Type") (fun a f => f!"({a} : Type) -> {f}"))
  | .cat c => mformat c

end BindingKind

/--
A single binder may declare multiple identifiers, but they
all have the same type and metadata.
-/
structure Binding where
  ident : Var
  kind : BindingKind
deriving Inhabited, Repr, BEq

/--
A sequence of bindings.

Includes an additional map that maps the identifiers to the
index of the binder for them.
-/
structure Bindings where
  ofArray ::
  toArray : Array Binding
  deriving BEq

namespace Bindings

protected def ofList (l : List Binding) : Bindings := ofArray (l.toArray)

protected def isEmpty (b:Bindings) := b.toArray.isEmpty

protected def size (b:Bindings) := b.toArray.size

instance : GetElem Bindings Nat Binding (fun bs i => i < bs.size) where
  getElem bindings idx p := bindings.toArray[idx]'p

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

structure ElabInfo where
  /-- The piece of syntax that the elaborator created this info for.
  Note that this also implicitly stores the code position in the syntax's SourceInfo. -/
  stx : Syntax
  /-- The piece of syntax that the elaborator created this info for.
  Note that this also implicitly stores the code position in the syntax's SourceInfo. -/
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

structure IdentInfo extends ElabInfo where
  val : String
deriving Inhabited, Repr

structure NumInfo extends ElabInfo where
  val : Nat
deriving Inhabited, Repr

structure DecimalInfo extends ElabInfo where
  val : Decimal
deriving Inhabited, Repr

structure StrlitInfo extends ElabInfo where
  val : String
deriving Inhabited, Repr

structure OptionInfo extends ElabInfo where
  deriving Inhabited, Repr

structure SeqInfo extends ElabInfo where
  args : Array Arg
  resultCtx : TypingContext
deriving Inhabited, Repr

structure CommaSepInfo extends ElabInfo where
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
| ofOptionInfo (info : OptionInfo)
| ofSeqInfo (info : SeqInfo)
| ofCommaSepInfo (info : CommaSepInfo)
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
  | .ofOptionInfo info => info.toElabInfo
  | .ofSeqInfo info => info.toElabInfo
  | .ofCommaSepInfo info => info.toElabInfo

def inputCtx (info : Info) : TypingContext := info.elabInfo.inputCtx

def stx (info : Info) : Syntax := info.elabInfo.stx

end Info

inductive Tree
| node (info : Info) (children : Array Tree)
deriving Inhabited, Repr

namespace Tree

def info : Tree → Info
| .node info _ => info

def children : Tree → Array Tree
| .node _ c => c

instance : GetElem Tree Nat Tree fun t i => i < t.children.size where
  getElem xs i h := xs.children[i]

@[simp]
theorem node_getElem (info : Info) (c : Array Tree) (i : Nat) (p : _) :
  (node info c)[i]'p = c[i]'p := rfl

def arg : Tree → Arg
| .node info children =>
  match info with
  | .ofOperationInfo info => .op info.op
  | .ofCatInfo info => .cat info.cat
  | .ofExprInfo info => .expr info.expr
  | .ofTypeInfo info => .type info.typeExpr
  | .ofIdentInfo info => .ident info.val
  | .ofNumInfo info => .num info.val
  | .ofDecimalInfo info => .decimal info.val
  | .ofStrlitInfo info => .strlit info.val
  | .ofOptionInfo _ =>
    match children with
    | #[] => .option none
    | #[x] => .option x.arg
    | _ => panic! "Unexpected option"
  | .ofSeqInfo info => .seq info.args
  | .ofCommaSepInfo info => .commaSepList info.args

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
  | .ofIdentInfo _ | .ofNumInfo _ | .ofDecimalInfo _ | .ofStrlitInfo _ => t.info.inputCtx
  | .ofOptionInfo info =>
    if p : t.children.size > 0 then
      have q : sizeOf t[0] < sizeOf t := sizeOf_children _ _ _
      resultContext t[0]
    else
      info.inputCtx
  | .ofSeqInfo info => info.resultCtx
  | .ofCommaSepInfo info => info.resultCtx
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
  if let .ofCommaSepInfo _ := t.info then
    some t.children
  else
    none

def asCommaSepInfo! (t : Tree) : Array Tree :=
  if let .ofCommaSepInfo _ := t.info then
    t.children
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
    | panic! s!"Expected identifier {repr tree.info.stx.getKind}"
  let some mdTree := tree[2]!.asOption?
      | panic! s!"Expected metadata to be option."
  return (nameInfo, tree[1]!.asBindingType!, mdTree)

end Tree

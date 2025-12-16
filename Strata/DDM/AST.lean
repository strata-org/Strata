/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Std.Data.HashMap
import Strata.DDM.Util.Array
import Strata.DDM.Util.ByteArray
import Strata.DDM.Util.Decimal
import Std.Data.HashMap.Lemmas

set_option autoImplicit false

namespace Strata.Array

theorem mem_iff_back_or_pop {α} (a : α) {as : Array α} (p : as.size > 0 := by get_elem_tactic) :
  a ∈ as ↔ (a = as.back ∨ a ∈ as.pop) := by
  simp [Array.mem_iff_getElem]
  grind

theorem of_mem_pop {α} {a : α} {as : Array α} : a ∈ as.pop → a ∈ as := by
  simp [Array.mem_iff_getElem]
  grind

end Strata.Array

namespace Strata

abbrev DialectName := String

structure QualifiedIdent where
  dialect : DialectName
  name : String
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace QualifiedIdent

def fullName (i : QualifiedIdent) : String := s!"{i.dialect}.{i.name}"

instance : ToString QualifiedIdent where
  toString := fullName

syntax:max (name := quoteIdent) "q`" noWs ident : term

section

open _root_.Lean

instance : Quote QualifiedIdent where
  quote i := Syntax.mkCApp ``QualifiedIdent.mk #[quote i.dialect, quote i.name]

@[macro quoteIdent] def quoteIdentImpl : Macro
  | `(q`$l:ident) =>
    if let .str (.str .anonymous d) suf := l.getId then
      pure (quote (QualifiedIdent.mk d suf) : Term)
    else
      throw (.error l.raw "Quoted identifiers must contain two components")
  | _ => Macro.throwUnsupported

end

end QualifiedIdent

#guard q`A.C = { dialect := "A", name := "C" }

/--
Denotes a fully specified syntax category in the Strata dialect.
-/
structure SyntaxCatF (α : Type) where
  ann : α
  name : QualifiedIdent
  args : Array (SyntaxCatF α)
deriving BEq, Inhabited, Repr

namespace SyntaxCatF

def atom {α} (ann : α) (ident : QualifiedIdent) : SyntaxCatF α where
  ann := ann
  name := ident
  args := #[]

/--
Return true if this corresponds to builtin category `Init.Type`
-/
def isType {α} (c : SyntaxCatF α) : Bool := c.name == q`Init.Type

def sizeOf_spec {α} [SizeOf α] (op : SyntaxCatF α) : sizeOf op = 1 + sizeOf op.ann + sizeOf op.name + sizeOf op.args :=
  match op with
  | { ann, name, args } => by simp

end SyntaxCatF

/-- This refers to a value introduced in the program. -/
abbrev FreeVarIndex := Nat

/-- An expression that denotes a type. -/
inductive TypeExprF (α : Type) where
  /-- A dialect defined type. -/
| ident (ann : α) (name : QualifiedIdent) (args : Array (TypeExprF α))
  /-- A bound type variable at the given deBruijn index in the context. -/
| bvar (ann : α) (index : Nat)
  /-- A reference to a global variable along with any arguments to ensure it is well-typed. -/
| fvar (ann : α) (fvar : FreeVarIndex) (args : Array (TypeExprF α))
  /-- A function type. -/
| arrow (ann : α) (arg : TypeExprF α) (res : TypeExprF α)
deriving BEq, Inhabited, Repr

namespace TypeExprF

def ann {α} : TypeExprF α → α
| .ident ann _ _ => ann
| .bvar ann _ => ann
| .fvar ann _ _ => ann
| .arrow ann _ _ => ann

def mkFunType {α} (n : α) (bindings : Array (String × TypeExprF α)) (res : TypeExprF α) : TypeExprF α :=
  bindings.foldr (init := res) fun (_, argType) tp => .arrow n argType tp

protected def incIndices {α} (tp : TypeExprF α) (count : Nat) : TypeExprF α :=
  match tp with
  | .ident n i args => .ident n i (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .fvar n f args => .fvar n f (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .bvar n idx => .bvar n (idx + count)
  | .arrow n a r => .arrow n (a.incIndices count) (r.incIndices count)

/-- Return true if type expression has a bound variable. -/
protected def hasUnboundVar {α} (bindingCount : Nat := 0) : TypeExprF α → Bool
| .ident _ _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .fvar _ _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .bvar _ idx => idx ≥ bindingCount
| .arrow _ a r => a.hasUnboundVar bindingCount || r.hasUnboundVar bindingCount
termination_by e => e

/-- Return true if type expression has no free variables. -/
protected def isGround {α} (tp : TypeExprF α) := !tp.hasUnboundVar

/--
Applies a transformation to each bound variable in a type expression.

Free type alias variables bound to alias
-/
protected def instTypeM {m α} [Monad m] (d : TypeExprF α) (bindings : α → Nat → m (TypeExprF α)) : m (TypeExprF α) :=
  match d with
  | .ident n i a =>
    .ident n i <$> a.attach.mapM (fun ⟨e, _⟩ => e.instTypeM bindings)
  | .bvar n idx => bindings n idx
  | .fvar n idx a => .fvar n idx <$> a.attach.mapM (fun ⟨e, _⟩ => e.instTypeM bindings)
  | .arrow n a b => .arrow n <$> a.instTypeM bindings <*> b.instTypeM bindings
termination_by d

def flattenArrow {α} : Array (TypeExprF α) → TypeExprF α → Array (TypeExprF α)
| a, .arrow _ l r => flattenArrow (a.push l) r
| a, r => a.push r

theorem flattenArrow_size {α} (args : Array (TypeExprF α)) (r : TypeExprF α) :
  sizeOf (flattenArrow args r) ≤ 1 + sizeOf args + sizeOf r := by
  unfold flattenArrow
  split
  case h_1 =>
    rename_i l r
    have h := flattenArrow_size (args.push l) r
    simp at *
    omega
  case h_2 =>
    decreasing_tactic
  termination_by r

end TypeExprF

mutual

inductive ExprF (α : Type) : Type where
| bvar (ann : α) (idx : Nat)
| fvar (ann : α) (idx : FreeVarIndex)
| fn (ann : α) (ident : QualifiedIdent)
| app (ann : α) (e : ExprF α) (a : ArgF α)
deriving Inhabited, Repr

structure OperationF (α : Type) : Type where
  ann : α
  name : QualifiedIdent
  args : Array (ArgF α)
deriving Inhabited, Repr

inductive ArgF (α : Type) : Type where
| op (o : OperationF α)
| cat (c : SyntaxCatF α)
| expr (e : ExprF α)
| type (e : TypeExprF α)
| ident (ann : α) (i : String)
| num (ann : α) (v : Nat)
| decimal (ann : α) (v : Decimal)
| strlit (ann : α) (i : String)
| bytes (ann : α) (a : ByteArray)
| option (ann : α) (l : Option (ArgF α))
| seq (ann : α) (l : Array (ArgF α))
| commaSepList (ann : α) (l : Array (ArgF α))
deriving Inhabited, Repr

end

mutual

def ExprF.ann {α : Type} : ExprF α → α
| .bvar ann _ => ann
| .fvar ann _ => ann
| .fn ann _ => ann
| .app ann _ _ => ann

def ArgF.ann {α : Type} : ArgF α → α
| .op o => o.ann
| .cat c => c.ann
| .expr e => e.ann
| .type t => t.ann
| .ident ann _ => ann
| .num ann _ => ann
| .decimal ann _ => ann
| .bytes ann _ => ann
| .strlit ann _ => ann
| .option ann _ => ann
| .seq ann _ => ann
| .commaSepList ann _ => ann

end

namespace OperationF

def sizeOf_spec {α} [SizeOf α] (op : OperationF α) : sizeOf op = 1 + sizeOf op.ann + sizeOf op.name + sizeOf op.args :=
  match op with
  | { ann, name, args } => by simp

theorem sizeOf_lt_of_op_arg {α} {e : ArgF α} {op : OperationF α} (p : e ∈ op.args) : sizeOf e < sizeOf op := by
  cases op with
  | mk ann name args =>
    have q : sizeOf e < sizeOf args := by decreasing_tactic
    decreasing_tactic

end OperationF

/--
Array ofelements whose sizes are bounded by a value.
-/
abbrev SizeBounded (α : Type _) [SizeOf α] {β} [SizeOf β] (e : β) (c : Int) := { a : α // sizeOf a ≤ sizeOf e + c }

namespace ExprF

/--
Head-normal form for an expression consists of an operation
-/
structure HNF {α} (e : ExprF α) where
  fn : ExprF α
  args : SizeBounded (Array (ArgF α)) e 1

protected def hnf {α} (e0 : ExprF α) : HNF e0 :=
  let rec aux (e : ExprF α) (args : Array (ArgF α) := #[])
              (szP : sizeOf e + sizeOf args ≤ sizeOf e0 + 2): HNF e0 :=
    match e with
    | .bvar .. | .fvar .. | .fn .. =>
      { fn := e, args := ⟨args.reverse, by simp at szP; simp; omega⟩ }
    | .app _ f a =>
      aux f (args.push a) (by simp at *; omega)
  aux e0 #[] (by simp)

partial def flatten {α} (e : ExprF α) (prev : List (ArgF α) := []) : ExprF α × List (ArgF α) :=
  match e with
  | .app _ f e => f.flatten (e :: prev)
  | _ => (e, prev)

end ExprF

namespace ArgF

def asOp! {α} [Inhabited α] [Repr α] : ArgF α → OperationF α
| .op a => a
| a => panic! s!"{repr a} is not an operation."

def asCat! {α} [Inhabited α] [Repr α] : ArgF α → SyntaxCatF α
| .cat a => a
| a => panic! s!"{repr a} is not a syntax category."

def asExpr! {α} [Inhabited α] [Repr α] : ArgF α → ExprF α
| .expr a => a
| a => panic! s!"{repr a} is not an expression."

def asType! {α} [Inhabited α] [Repr α] : ArgF α → TypeExprF α
| .type a => a
| a => panic! s!"{repr a} is not a type."

def asIdent! {α} [Repr α] : ArgF α → String
| .ident _ a => a
| a => panic! s!"{repr a} is not an identifier."

def asOption! {α} [Repr α] : ArgF α → Option (ArgF α)
| .option _ a => a
| a => panic! s!"{repr a} is not an option."

def asSeq! {α} [Repr α] : ArgF α → Array (ArgF α)
| .seq _ a => a
| a => panic! s!"{repr a} is not an sequence."

def asCommaSepList {α} [Repr α] : ArgF α → Array (ArgF α)
| .commaSepList _ a => a
| a => panic! s!"{repr a} is not an comma separated list."

end ArgF

/--
Source location information in the DDM is defined
by a range of bytes in a UTF-8 string with the input
Line/column information can be construced from a
`Lean.FileMap`

As an example, in the string `"123abc\ndef"`, the string
`"abc"` has the position `{start := 3, stop := 6 }` while
`"def"` has the position `{start := 7, stop := 10 }`.
-/
structure SourceRange where
  /-- The starting offset of the source range. -/
  start : String.Pos.Raw
  /-- One past the end of the range. -/
  stop : String.Pos.Raw
deriving BEq, Inhabited, Repr

namespace SourceRange

def none : SourceRange := { start := 0, stop := 0 }

def isNone (loc : SourceRange) : Bool := loc.start = 0 ∧ loc.stop = 0

end SourceRange

abbrev Arg := ArgF SourceRange
abbrev Expr := ExprF SourceRange
abbrev Operation := OperationF SourceRange
abbrev SyntaxCat := SyntaxCatF SourceRange
abbrev TypeExpr := TypeExprF SourceRange

mutual
/--
Decidable equality definitions of Expr, Operation and Arg.
They cannot be naturally derived from 'deriving DecidableEq'. It seems the
fact that their constructors use Array of themselves makes this hard.
-/
def ExprF.beq {α} [BEq α] (e1 e2 : ExprF α) : Bool :=
  match e1, e2 with
  | .bvar a1 i1, .bvar a2 i2
  | .fvar a1 i1, .fvar a2 i2
  | .fn a1 i1, .fn a2 i2 => a1 == a2 && i1 == i2
  | .app a1 x1 y1, .app a2 x2 y2 => a1 == a2 && ExprF.beq x1 x2 && ArgF.beq y1 y2
  | _, _ => false
termination_by sizeOf e1

def OperationF.beq {α} [BEq α] (o1 o2 : OperationF α) : Bool :=
  o1.ann == o2.ann
  && o1.name = o2.name
  && ArgF.array_beq o1.args o2.args
termination_by sizeOf o1
decreasing_by
  simp [OperationF.sizeOf_spec]
  omega

def ArgF.beq {α} [BEq α] (a1 a2 : ArgF α) : Bool :=
  match a1, a2 with
  | .op o1, .op o2 => OperationF.beq o1 o2
  | .cat c1, .cat c2 => c1 == c2
  | .expr e1, .expr e2 => ExprF.beq e1 e2
  | .type t1, .type t2 => t1 == t2
  | .ident a1 i1, .ident a2 i2 => a1 == a2 && i1 == i2
  | .num a1 n1, .num a2 n2 => a1 == a2 && n1 == n2
  | .decimal a1 v1, .decimal a2 v2 => a1 == a2 && v1 == v2
  | .strlit a1 i1, .strlit a2 i2 => a1 == a2 && i1 == i2
  | .option a1 o1, .option a2 o2 => a1 == a2 &&
    match o1,o2 with
    | .none, .none => true
    | .some v1, .some v2 => ArgF.beq v1 v2
    | _, _ => false
  | .seq a1 v1, .seq a2 v2 =>
    a1 == a2 && ArgF.array_beq v1 v2
  | .commaSepList a1 v1, .commaSepList a2 v2 =>
    a1 == a2 && ArgF.array_beq v1 v2
  | _, _ => false
termination_by sizeOf a1

def ArgF.array_beq {α} [BEq α] (a1 a2 : Array (ArgF α)) : Bool :=
  if size_eq : a1.size = a2.size then
    a1.size.all fun i p => ArgF.beq a1[i] a2[i]
  else
    false
termination_by sizeOf a1

end

-- TODO: extend these to LawfulBEq!
instance {α} [BEq α] : BEq (ExprF α) where beq := ExprF.beq
instance {α} [BEq α] : BEq (OperationF α) where beq := OperationF.beq
instance {α} [BEq α] : BEq (ArgF α) where beq := ArgF.beq

inductive MetadataArg where
| bool (e : Bool)
| catbvar (index : Nat) -- This is a deBrujin index into current typing environment.
| num (e : Nat)
| option (a : Option MetadataArg)
deriving BEq, Inhabited, Repr

namespace MetadataArg

protected def decEq (x y : MetadataArg) : Decidable (x = y) :=
  match x with
  | .bool x =>
    match y with
    | .bool y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .catbvar _ | .num _ | .option _ => .isFalse (by grind)
  | .catbvar x =>
    match y with
    | .catbvar y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .bool _ | .num _ | .option _ => .isFalse (by grind)
  | .num x =>
    match y with
    | .num y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .bool _ | .catbvar _ | .option _ => .isFalse (by grind)
  | .option x =>
    match y with
    | .option y =>
      match x, y with
      | none, none => .isTrue (by grind)
      | some x, some y =>
        match MetadataArg.decEq x y with
        | .isTrue p => .isTrue (by grind)
        | .isFalse p => .isFalse (by grind)
      | none, some _ | some _, none => .isFalse (by grind)
    | .bool _ | .catbvar _ | .num _ => .isFalse (by grind)

instance : DecidableEq MetadataArg := MetadataArg.decEq

end MetadataArg

structure MetadataAttr where
  ident : QualifiedIdent
  args : Array MetadataArg
deriving DecidableEq, Inhabited, Repr

namespace MetadataAttr

def scopeName := q`StrataDDL.scope

/-- Create scope using deBrujin index of environment. -/
def scope (idx : Nat) : MetadataAttr :=
  { ident := scopeName, args := #[.catbvar idx ] }

def declare (varIndex typeIndex : Nat) : MetadataAttr :=
  { ident := q`StrataDDL.declare, args := #[.catbvar varIndex, .catbvar typeIndex]}

def declareFn (varIndex bindingsIndex typeIndex : Nat) : MetadataAttr :=
  { ident := q`StrataDDL.declareFn, args := #[.catbvar varIndex, .catbvar bindingsIndex, .catbvar typeIndex]}

end MetadataAttr

structure Metadata where
  ofArray ::
  toArray : Array MetadataAttr
deriving DecidableEq, Repr

namespace Metadata

protected def emptyWithCapacity (c : Nat) : Metadata := { toArray := .emptyWithCapacity c }

protected def empty : Metadata := .emptyWithCapacity 0

protected def push (md : Metadata) (attr : MetadataAttr) : Metadata :=
  .ofArray <| md.toArray.push attr

instance : Inhabited Metadata where
  default := .empty

def isEmpty (md : Metadata) := md.toArray.isEmpty

def toList (m : Metadata) : List MetadataAttr := m.toArray.toList

instance : Membership QualifiedIdent Metadata where
  mem md x := md.toArray.any fun a => a.ident = x

instance (x : QualifiedIdent) (md : Metadata) : Decidable (x ∈ md) := by
  apply instDecidableEqBool

instance : GetElem? Metadata QualifiedIdent (Array MetadataArg) (fun md i => i ∈ md) where
  getElem md i _p :=
    match md.toArray.find? (·.ident = i) with
    | none => default
    | some a => a.args
  getElem? md i :=
    match md.toArray.find? (·.ident = i) with
    | none => none
    | some a => a.args

def scopeIndex (metadata : Metadata) : Option Nat :=
  match metadata[MetadataAttr.scopeName]? with
  | none => none
  | some #[.catbvar idx] => some idx
  | some _ => panic! s!"Unexpected argument count to {MetadataAttr.scopeName.fullName}"

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
def resultIndex (metadata : Metadata) : Option Nat :=
  match metadata[MetadataAttr.scopeName]? with
  | none => none
  | some #[.catbvar idx] =>
    pure idx
  | _ => panic! "Unexpected argument to {MetadataAttr.scopeName.fullName}"

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
def resultLevel (varCount : Nat) (metadata : Metadata) : Option (Fin varCount) :=
  match metadata.resultIndex with
  | none => none
  | some idx =>
    if _ : idx < varCount then
      some ⟨varCount - (idx + 1), by omega⟩
    else
      panic! s!"Scope index {idx} out of bounds (varCount = {varCount})"

end Metadata

abbrev Var := String

private def catbvarLevel (varCount : Nat) : MetadataArg → Nat
| .catbvar idx =>
  if idx < varCount then
    varCount - (idx + 1)
  else
    panic! s!"Scope index {idx} out of bounds (varCount = {varCount})"
| _ => panic! "Unexpected argument to catbvarIndex"

/--
PreTypes are partially resolved types that may depend on values
applied to other arguments.  These need to be resolved to
generate types.
-/
inductive PreType where
  /-- A dialect defined type. -/
| ident (ann : SourceRange) (name : QualifiedIdent) (args : Array PreType)
  /-- A bound type variable at the given deBruijn index in the context. -/
| bvar (ann : SourceRange) (index : Nat)
  /-- A reference to a global variable along with any arguments to ensure it is well-typed. -/
| fvar (ann : SourceRange) (fvar : FreeVarIndex) (args : Array PreType)
  /-- A function type. -/
| arrow (ann : SourceRange) (arg : PreType) (res : PreType)
  /-- A function created from a reference to bindings and a result type. -/
| funMacro (ann : SourceRange) (bindingsIndex : Nat) (res : PreType)
deriving BEq, Inhabited, Repr

namespace PreType

/-- Return annotation on pretype. -/
def ann : PreType → SourceRange
| .ident ann _ _ => ann
| .bvar ann _ => ann
| .fvar ann _ _ => ann
| .arrow ann _ _ => ann
| .funMacro ann _ _ => ann

def ofType : TypeExprF SourceRange → PreType
| .ident loc name args => .ident loc name (args.map fun a => .ofType a)
| .bvar loc idx => .bvar loc idx
| .fvar loc idx args => .fvar loc idx (args.map fun a => .ofType a)
| .arrow loc a r => .arrow loc (.ofType a) (.ofType r)
termination_by tp => tp

end PreType

def maxPrec := eval_prec max

/--
Precedence of an explicit function call `f(..)`.

This specifically addresses the priority between f and the open paren.
-/
def callPrec := 200

/-- Precedence of the empty application operator `f x` in expressions and types. -/
def appPrec := 20

/-- Precedence of the arrow operator `t -> u` in types. -/
def arrowPrec :=  17

/--
This describes how to format an operator.
-/
inductive SyntaxDefAtom
-- Format the argument with the given name.
-- Surround with parenthesis if the precedence of the argument is less than `prec`.
-- Note. If `prec` is zero, then parenthesis will never be added (even with pp.parens is true).
-- This is to avoid parens in categories that do not support them.
-- The unwrap parameter specifies if the value should be unwrapped to a raw type.
| ident (level : Nat) (prec : Nat) (unwrap : Bool := false)
| str (lit : String)
| indent (n : Nat) (args : Array SyntaxDefAtom)
deriving BEq, Inhabited, Repr

structure SyntaxDef where
  atoms : Array SyntaxDefAtom
  prec : Nat
deriving BEq, Repr, Inhabited

namespace SyntaxDef

/--
Creates syntax of the form `name(arg1, ..., argn)`.

If `n` is 0, then this is just `name`.
-/
def mkFunApp (name : String) (n : Nat) : SyntaxDef :=
  let atoms : Array SyntaxDefAtom :=
    if n = 0 then
      #[.str name]
    else
      let atoms := #[.str name, .str "(", .ident 0 0]
      let atoms := (n-1).fold (init := atoms) fun i _ a =>
        a |>.push (.str ", ") |>.push (.ident (i+1) 0)
      atoms.push (.str ")")
  {
    atoms := atoms
    prec := appPrec
  }

def ofList (atoms : List SyntaxDefAtom) (prec : Nat := maxPrec): SyntaxDef where
  atoms := atoms.toArray
  prec := prec

end SyntaxDef

/-- Structure that defines a binding introduced by an operation or function. -/
inductive SyntaxElabType
| type : PreType → SyntaxElabType
deriving Repr

structure DebruijnIndex (n : Nat) where
  val : Nat
  isLt : val < n
deriving Repr

namespace DebruijnIndex

def toLevel {n} : DebruijnIndex n → Fin n
| ⟨v, lt⟩ => ⟨n - (v+1), by omega⟩

end DebruijnIndex

/--
This is the type information for an operator or function declaration.
-/
inductive ArgDeclKind where
/-- Variable is an expression with the given type. -/
| type (tp : PreType)
/-- Variable belongs to the particular category -/
| cat (k : SyntaxCat)
deriving BEq, Inhabited, Repr

namespace ArgDeclKind

def categoryOf : ArgDeclKind → SyntaxCat
| .type tp => .atom tp.ann q`Init.Expr
| .cat c => c

/--
Return true if this corresponds to builtin category `Init.Type`
-/
def isType (k : ArgDeclKind) :=
  match k with
  | .cat c => c.isType
  | _ => false

end ArgDeclKind

/--
An argument declaration in an operator or function.
-/
structure ArgDecl where
  ident : Var
  kind : ArgDeclKind
  metadata : Metadata := .empty
deriving BEq, Inhabited, Repr

structure ArgDecls where
  ofArray ::
  toArray : Array ArgDecl
deriving BEq, Inhabited, Repr

namespace ArgDecls

protected def empty : ArgDecls := { toArray := #[] }

protected def size (a : ArgDecls) : Nat := a.toArray.size

protected def isEmpty (a : ArgDecls) : Bool := a.toArray.isEmpty

instance : GetElem ArgDecls Nat ArgDecl fun a i => i < a.size where
  getElem a i p := a.toArray[i]

protected def foldl {α} (a : ArgDecls) (f : α → ArgDecl → α) (init : α): α  := a.toArray.foldl f init

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
def argScopeLevel (argDecls : ArgDecls) (level : Fin argDecls.size) : Option (Fin level.val) :=
  match argDecls[level].metadata.scopeIndex with
  | none => none
  | some idx =>
    if h : idx < level.val then
      some ⟨level.val - (idx + 1), by omega⟩
    else
      -- TODO: Validate this is checked when attribute parsing occurs.
      let varCount := argDecls.size
      panic! s!"Scope index {idx} out of bounds ({level.val}, varCount = {varCount})"

end ArgDecls

/--
Indices for introducing a new expression or operation.
-/
structure ValueBindingSpec (argDecls : ArgDecls) where
  -- deBrujin level of variable name.
  nameIndex : DebruijnIndex argDecls.size
  -- deBrujin index of arguments if this is declaring a function (or none) if this declares a constant.
  argsIndex : Option (DebruijnIndex argDecls.size)
  -- deBrujin index of type or a type/cat literal.
  typeIndex : DebruijnIndex argDecls.size
  -- Whether categories are allowed
  allowCat : Bool
deriving Repr

/--
Indices for introducing a new type binding.
-/
structure TypeBindingSpec (argDecls : ArgDecls) where
  nameIndex : DebruijnIndex argDecls.size
  argsIndex : Option (DebruijnIndex argDecls.size)
  defIndex : Option (DebruijnIndex argDecls.size)
deriving Repr

/-
A spec for introducing a new binding into a type context.
-/
inductive BindingSpec (argDecls : ArgDecls) where
| value (_ : ValueBindingSpec argDecls)
| type (_ : TypeBindingSpec argDecls)
deriving Repr

namespace BindingSpec

def nameIndex {argDecls} : BindingSpec argDecls → DebruijnIndex argDecls.size
| .value v => v.nameIndex
| .type v => v.nameIndex

end BindingSpec

abbrev NewBindingM := StateM (Array String)

private def newBindingErr (msg : String) : NewBindingM Unit :=
  modify (·.push msg)

private def checkNameIndexIsIdent (args : ArgDecls) (nameIndex : DebruijnIndex args.size) : NewBindingM Unit :=
  let b := args[nameIndex.toLevel]
  match b.kind with
  | .cat (.atom _ q`Init.Ident) =>
    pure ()
  | _ =>
    newBindingErr s!"Expected {b.ident} to be an Ident."

private def mkValueBindingSpec
            (argDecls : ArgDecls)
            (nameIndex : DebruijnIndex argDecls.size)
            (typeIndex : DebruijnIndex argDecls.size)
            (argsIndex : Option (DebruijnIndex argDecls.size) := none)
            : NewBindingM (ValueBindingSpec argDecls) := do
  checkNameIndexIsIdent argDecls nameIndex
  let typeBinding := argDecls[typeIndex.toLevel]
  let allowCat ←
        match typeBinding.kind with
        | .cat (.atom _ q`Init.Type) =>
          pure false
        | .cat (.atom _ q`Init.TypeP) =>
          pure true
        | _ =>
          newBindingErr "Expected reference to type variable."
          pure default
  if allowCat && argsIndex.isSome then
    newBindingErr "Arguments only allowed when result is a type."
  return { nameIndex, argsIndex, typeIndex, allowCat }

def parseNewBindings (md : Metadata) (argDecls : ArgDecls) : Array (BindingSpec argDecls) × Array String :=
  let ins (attr : MetadataAttr) : NewBindingM (Option (BindingSpec argDecls)) := do
        match attr.ident with
        | q`StrataDDL.declare => do
          let #[.catbvar nameIndex, .catbvar typeIndex] := attr.args
            | newBindingErr "declare expects 2 arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          let .isTrue typeP := inferInstanceAs (Decidable (typeIndex < argDecls.size))
            | return panic! "Invalid name index"
          some <$> .value <$> mkValueBindingSpec argDecls ⟨nameIndex, nameP⟩ ⟨typeIndex, typeP⟩
        | q`StrataDDL.declareFn => do
          let #[.catbvar nameIndex, .catbvar argsIndex, .catbvar typeIndex] := attr.args
            | newBindingErr "declareFn missing required arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          let .isTrue argsP := inferInstanceAs (Decidable (argsIndex < argDecls.size))
            | return panic! "Invalid arg index"
          let .isTrue typeP := inferInstanceAs (Decidable (typeIndex < argDecls.size))
            | return panic! "Invalid name index"
          some <$> .value <$> mkValueBindingSpec argDecls ⟨nameIndex, nameP⟩ ⟨typeIndex, typeP⟩ (argsIndex := some ⟨argsIndex, argsP⟩)
        | q`StrataDDL.declareType => do
          let #[.catbvar nameIndex, .option mArgsArg ] := attr.args
            | newBindingErr s!"declareType has bad arguments {repr attr.args}."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          let nameIndex := ⟨nameIndex, nameP⟩
          checkNameIndexIsIdent argDecls nameIndex
          let argsIndex ←
                match mArgsArg with
                | none => pure none
                | some (.catbvar idx) =>
                  let .isTrue argsP := inferInstanceAs (Decidable (idx < argDecls.size))
                    | return panic! "Invalid arg index"
                  pure <| some ⟨idx, argsP⟩
                | _ => newBindingErr "declareType args invalid."; return none
          some <$> .type <$> pure { nameIndex, argsIndex, defIndex := none }
        | q`StrataDDL.aliasType => do
          let #[.catbvar nameIndex, .option mArgsArg, .catbvar defIndex] := attr.args
            | newBindingErr "aliasType missing arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          let nameIndex := ⟨nameIndex, nameP⟩
          checkNameIndexIsIdent argDecls nameIndex
          let argsIndex : DebruijnIndex argDecls.size ←
                match mArgsArg with
                | none => pure none
                | some (.catbvar idx) =>
                  let .isTrue argsP := inferInstanceAs (Decidable (idx < argDecls.size))
                    | return panic! "Invalid arg index"
                  pure <| some ⟨idx, argsP⟩
                | _ => newBindingErr "aliasType args invalid."; return none
          let .isTrue defP := inferInstanceAs (Decidable (defIndex < argDecls.size))
            | return panic! "Invalid def index"
          let defBinding := argDecls[argDecls.size - (defIndex+1)]
          match defBinding.kind with
          | .cat (.atom _ q`Init.Type) =>
            pure ()
          | _ =>
            newBindingErr s!"Expected {defBinding.ident} to be a Type."
          let defScopeIndex :=
            match defBinding.metadata.scopeIndex with
            | none => none
            | some idx => some (defIndex + idx + 1)
          if defScopeIndex ≠ (·.val) <$> argsIndex then
            newBindingErr s!"Scope of definition must match arg scope."
          let defIndex := ⟨defIndex, defP⟩
          some <$> .type <$> pure { nameIndex, argsIndex, defIndex := some defIndex }
        | _ =>
          pure none
  (md.toArray.filterMapM ins) #[]

def parseNewBindings! (md : Metadata) (argDecls : ArgDecls) : Array (BindingSpec argDecls) :=
  let (r, errs) := parseNewBindings md argDecls
  if let some msg := errs[0]? then
    panic! msg
  else
    r

structure SynCatDecl where
  name : String
  argNames : Array String := #[]
deriving Repr, DecidableEq, Inhabited

structure Ann (Base : Type) (α : Type) where
  ann : α
  val : Base
deriving BEq, DecidableEq, Inhabited, Repr

/--
A declaration of an algebraic data type.
-/
structure TypeDecl where
  name : String
  argNames : Array (Ann String SourceRange)
deriving BEq, Inhabited, Repr

/-- Operator declaration -/
structure OpDecl where
  /-- Name of operator -/
  name : String
  /-- Arguments to operator. -/
  argDecls : ArgDecls
  /-- Syntactic category of operator -/
  category : QualifiedIdent
  /-- Schema for operator -/
  syntaxDef : SyntaxDef
  /-- Metadata for operator. -/
  metadata : Metadata := .empty
  /-- New bindings -/
  newBindings : Array (BindingSpec argDecls) := parseNewBindings! metadata argDecls
deriving Inhabited, Repr

namespace OpDecl

instance : BEq OpDecl where
  beq x y :=
    x.name = y.name
    && x.argDecls == y.argDecls
    && x.category = y.category
    && x.syntaxDef == y.syntaxDef
    && x.metadata == y.metadata

def mk1
  (name : String)
  (argDecls : ArgDecls)
  (category : QualifiedIdent)
  (syntaxDef : SyntaxDef)
  (metadata : Metadata) : OpDecl :=
  { name, argDecls, category, syntaxDef, metadata }

end OpDecl

abbrev FnName := String

structure FunctionDecl where
  name : FnName
  argDecls : ArgDecls
  result : PreType
  syntaxDef : SyntaxDef
  metadata : Metadata := .empty
deriving BEq, Inhabited, Repr

inductive MetadataArgType
| num
| ident
| bool
| opt (tp : MetadataArgType)
deriving DecidableEq, Inhabited, Repr

structure MetadataArgDecl where
  ident : String
  type : MetadataArgType
deriving DecidableEq, Inhabited, Repr

/--
Declaration of a metadata tag in a dialect.

Metadata has an optional argument that must have
the specified type.

N.B. We may want to further restrict where metadata can appear.
-/
structure MetadataDecl where
  name : String
  args : Array MetadataArgDecl
deriving DecidableEq, Inhabited, Repr

inductive Decl where
| syncat (d : SynCatDecl)
| op (d : OpDecl)
| type (d : TypeDecl)
| function (d : FunctionDecl)
| metadata (d : MetadataDecl)
deriving BEq, Inhabited, Repr

namespace Decl

protected def name : Decl → String
| .syncat d => d.name
| .op d => d.name
| .type d => d.name
| .function d => d.name
| .metadata d => d.name

end Decl

structure Collection (α : Type) where
  declarations : Array Decl
  cache : Std.HashMap String Decl
  proj : Decl → Option α
  pretty : α → String

namespace Collection

instance {m α} : ForIn m (Collection α) α where
  forIn c i f := do
    let step d _h r :=
          match c.proj d with
          | .some v => f v r
          | .none => pure (.yield r)
    c.declarations.forIn' i step

protected def fold {α β} (f : β → α → β) (init : β) (c : Collection α) : β :=
  let proj := c.proj
  let step b d :=
        match proj d with
        | some v => f b v
        | none => b
  c.declarations.foldl step init

instance {α} : ToString (Collection α) where
  toString c :=
    let step i a :=
          let r := if i.fst then i.snd else i.snd ++ ", "
          (false, r ++ c.pretty a)
    (c.fold step (true, "{") |>.snd) ++ "}"

inductive Mem {α} (c : Collection α) (nm : String) : Prop
| intro : (h : nm ∈ c.cache) → (r : α) → c.proj (c.cache[nm]) = some r → Mem c nm

def Mem.inCache {α} {c : Collection α} {nm} : Mem c nm → nm ∈ c.cache
| .intro h _ _ => h

instance {α} : Membership String (Collection α) where
  mem := Mem

instance {α} (nm : String) (c : Collection α) : Decidable (nm ∈ c) :=
  match p : c.cache[nm]? with
  | none => isFalse fun (.intro inCache _ _) => by
    simp [getElem?_def] at p
    contradiction
  | some d =>
    match q: c.proj d with
    | none => isFalse fun (.intro inCache z z_eq) => by
      simp [getElem?_def] at p
      match p with
      | .intro _ eq =>
        simp only [eq, q] at z_eq
        contradiction
    | some z =>
      have inCache : nm ∈ c.cache := by
        simp [getElem?_def] at p
        match p with
        | Exists.intro i _ => exact i
      have val_eq : c.proj c.cache[nm] = some z := by
        simp [getElem?_def] at p
        match p with
        | Exists.intro h eq => simp only [eq, q]
      isTrue (Mem.intro inCache z val_eq)

end Collection

instance {α} : GetElem? (Collection α) String α (fun c nm => nm ∈ c) where
  getElem c nm p :=
    have inCache : nm ∈ c.cache := p.inCache
    match q : c.cache[nm] with
    | d =>
      match r : c.proj d with
      | some z => z
      | none => by
        apply False.elim
        match p with
        | .intro inCache z h =>
          simp only [q, r] at h
          contradiction
  getElem? c nm :=
    match c.cache[nm]? with
    | none => none
    | some d => c.proj d

/--
A dialect definition.
-/
structure Dialect where
  name : DialectName
  -- Names of dialects that are imported into this dialect
  imports : Array DialectName
  declarations : Array Decl := #[]
  cache : Std.HashMap String Decl :=
    declarations.foldl (init := {}) fun m d => m.insert d.name d
deriving Inhabited

namespace Dialect

instance : BEq Dialect where
  beq x y := x.name = y.name
    && x.imports = y.imports
    && x.declarations == y.declarations

def syncats (d : Dialect) : Collection SynCatDecl where
  declarations := d.declarations
  cache := d.cache
  proj
  | .syncat d => some d
  | _ => none
  pretty := (·.name)

def ops (d : Dialect) : Collection OpDecl where
  declarations := d.declarations
  cache := d.cache
  proj
  | .op d => some d
  | _ => none
  pretty := (·.name)

def types (d : Dialect) : Collection TypeDecl where
  declarations := d.declarations
  cache := d.cache
  proj
  | .type d => some d
  | _ => none
  pretty := (·.name)

def functions (d : Dialect) : Collection FunctionDecl where
  declarations := d.declarations
  cache := d.cache
  proj
  | .function d => some d
  | _ => none
  pretty := (·.name)

def metadata (d : Dialect) : Collection MetadataDecl where
  declarations := d.declarations
  cache := d.cache
  proj
  | .metadata d => some d
  | _ => none
  pretty := (·.name)

def ofArray
    (name : DialectName)
    (importDialects : Array DialectName)
    (a : Array Decl)
    : Dialect where
  name := name
  imports := importDialects
  declarations := a
  cache := a.foldl (fun m d => m.insert d.name d) {}

def addDecl (d : Dialect) (decl : Decl) : Dialect :=
  let name := decl.name
  if name ∈ d.cache then
    @panic _ ⟨d⟩ s!"Cannot add {name}: already added."
  else
    { d with
      declarations := d.declarations.push decl,
      cache := d.cache.insert name decl
      }

def declareSyntaxCat (d : Dialect) (decl : SynCatDecl) :=
  d.addDecl (.syncat decl)

def declareType (d : Dialect) (name : String) (argNames : Array (Ann String SourceRange)) :=
  d.addDecl (.type { name, argNames })

def declareMetadata (d : Dialect) (decl : MetadataDecl) : Dialect :=
  d.addDecl (.metadata decl)

instance : Membership String Dialect where
  mem d nm := nm ∈ d.cache

instance (nm : String) (d : Dialect) : Decidable (nm ∈ d) :=
  inferInstanceAs (Decidable (nm ∈ d.cache))

end Dialect

/-- BEq between two Std HashMap; checked by doing inclusion test twice -/
instance {α β} [BEq α] [Hashable α] [BEq β]: BEq (Std.HashMap α β) where
  beq x y := Id.run do
    if x.size ≠ y.size then
      return false
    for (k, v) in x do
      if y.get? k != Option.some v then
        return false
    return true

structure DialectMap where
  map : Std.HashMap DialectName Dialect
  closed : ∀(d : DialectName) (p: d ∈ map), map[d].imports.all (· ∈ map)

namespace DialectMap

instance : BEq DialectMap where
  beq x y := x.map == y.map

instance : EmptyCollection DialectMap where
  emptyCollection := { map := {}, closed := by simp }

instance : Inhabited DialectMap where
  default := {}

instance : Membership DialectName DialectMap where
  mem m d := d ∈ m.map

instance (d : DialectName) (m : DialectMap) : Decidable (d ∈ m) :=
  inferInstanceAs (Decidable (d ∈ m.map))

instance : GetElem? DialectMap DialectName Dialect (fun m d => d ∈ m) where
  getElem m d p := m.map[d]
  getElem? m d := m.map[d]?
  getElem! m d := m.map[d]!

/--
This inserts a new dialect into the dialect map.

This requires propositions to ensure we do not change the semantics
of dialects and imports are already in dialect.
-/
def insert (m : DialectMap) (d : Dialect) (_d_new : d.name ∉ m) (d_imports_ok : d.imports.all (· ∈ m)) : DialectMap :=
  { map := m.map.insert d.name d
    closed := by
      intro name mem
      if eq : d.name = name then
        simp at d_imports_ok
        simp [eq]
        intro i lt
        exact Or.inr (d_imports_ok i lt)
      else
        simp only [Std.HashMap.mem_insert, eq, beq_iff_eq, false_or] at mem
        have cl := m.closed name mem
        simp at cl
        simp [Std.HashMap.getElem_insert, eq]
        intro i lt
        exact Or.inr (cl i lt)
  }

/--
This inserts a dialect in to the dialect map.

It panics if a dialect with the same name is already in the map
or if the dialect imports a dialect not already in the map.
-/
def insert! (m : DialectMap) (d : Dialect) : DialectMap :=
  if d_new : d.name ∈ m then
    panic! s!"{d.name} already in map."
  else
    if d_imports_ok : d.imports.all (· ∈ m) then
      m.insert d d_new d_imports_ok
    else
      panic! s!"Missing import."

def ofList! (l : List Dialect) : DialectMap :=
  let map : Std.HashMap DialectName Dialect :=
        l.foldl (init := .emptyWithCapacity l.length) fun m d =>
          m.insert d.name d
  let check := map.toArray.all fun (nm, d) => d.imports.all (· ∈ map)
  if p : check then
    { map := map,
      closed := by
        intro name name_mem
        simp only [check, Array.all_eq_true_iff_forall_mem (xs := map.toArray)] at p
        have mem : (name, map[name]) ∈ map.toArray := by
          simp [Std.HashMap.mem_toArray_iff_getElem?_eq_some]
        exact p (name, map[name]) mem
    }
  else
    panic! "Invalid list"

def toList (m : DialectMap) : List Dialect := m.map.values

def decl! (dm : DialectMap) (ident : QualifiedIdent) : Decl :=
  match dm.map[ident.dialect]? with
  | none => panic! s!"Unknown dialect {ident.dialect}"
  | some d =>
    match d.cache[ident.name]? with
    | some decl => decl
    | none => panic! s!"Unknown declaration {ident.fullName}"

def opDecl! (dm : DialectMap) (ident : QualifiedIdent) : OpDecl :=
  match dm.decl! ident with
  | .op decl => decl
  | _ => panic! s!"Unknown operation {ident.fullName}"

/--
Return set of all dialects that are imported by `dialect`.

This includes transitive imports.
-/
partial def importedDialects (dm : DialectMap) (dialect : DialectName) (p : dialect ∈ dm) : DialectMap :=
    aux {} #[dialect] (by simp; exact p) (by simp)
  where aux (map : Std.HashMap DialectName Dialect)
            (next : Array DialectName)
            (nextp : ∀name, name ∈ next → name ∈ dm)
            (inv : ∀name (mem : name ∈ map), map[name].imports.all (fun i => i ∈ map ∨ i ∈ next))
            : DialectMap :=
          if emptyP : next.isEmpty then
            { map := map,
              closed := by intro d mem; grind
            }
          else
            have next_size_pos : next.size > 0 := by
              simp only [Array.isEmpty_iff] at emptyP
              grind
            let name  := next.back (h := next_size_pos)
            if name_mem : name ∈ map then
              aux map next.pop
                (by
                  intro d p
                  exact nextp _ (Array.of_mem_pop p))
                (by
                  simp only [Array.all_eq_true']
                  intro d d_mem e e_mem
                  simp only [Array.all_eq_true'] at inv
                  have inv2 := inv d d_mem e e_mem
                  simp only [Array.mem_iff_back_or_pop e next_size_pos] at inv2
                  grind)
            else
              have name_in_dm : name ∈ dm := nextp name (by grind)
              let d := dm[name]
              aux (map.insert name d) (next.pop ++ d.imports)
                (by
                  intro nm nm_mem
                  simp at nm_mem
                  match nm_mem with
                  | .inl nm_mem =>
                    exact nextp _ (Array.of_mem_pop nm_mem)
                  | .inr nm_mem =>
                    have inv := dm.closed name name_in_dm
                    simp only [Array.all_eq_true'] at inv
                    have inv2 := inv nm nm_mem
                    simp at inv2
                    exact inv2)
                (by
                  intro n n_mem
                  if n_eq : name = n then
                    simp [n_eq]
                  else
                    simp [n_eq] at n_mem
                    simp [n_eq, Std.HashMap.getElem_insert]
                    intro i lt
                    have mem := Array.mem_iff_back_or_pop (map[n].imports[i]) next_size_pos
                    grind)

end DialectMap

mutual

/--
Invoke a function `f` over each of the declaration specifications for an arg.
-/
partial def foldOverArgBindingSpecs {α β}
    (m : DialectMap)
    (f : β → α → ∀(argDecls : ArgDecls), BindingSpec argDecls → Vector (ArgF α) argDecls.size → β)
    (init : β)
    (a : ArgF α)
    : β :=
  match a with
  | .op op => op.foldBindingSpecs m f init
  | .expr _ | .type _ | .cat _ | .ident .. | .num .. | .decimal .. | .bytes .. | .strlit .. => init
  | .option _ none => init
  | .option _ (some a) => foldOverArgBindingSpecs m f init a
  | .seq _ a => a.attach.foldl (init := init) fun init ⟨a, _⟩ => foldOverArgBindingSpecs m f init a
  | .commaSepList _ a => a.attach.foldl (init := init) fun init ⟨a, _⟩ => foldOverArgBindingSpecs m f init a

/--
Invoke a function `f` over each of the declaration specifications for an operator.
-/
partial def OperationF.foldBindingSpecs {α β}
    (m : DialectMap)
    (f : β → α → ∀{argDecls : ArgDecls}, BindingSpec argDecls → Vector (ArgF α) argDecls.size → β)
    (init : β)
    (op : OperationF α)
    : β :=
  let decl := m.opDecl! op.name
  let argDecls := decl.argDecls
  let args := op.args
  if h : args.size = argDecls.size then
    let argsV : Vector (ArgF α) argDecls.size := ⟨args, h⟩
    let init :=
      match decl.metadata.resultLevel argDecls.size with
      | none => init
      | some lvl => foldOverArgAtLevel m f init argDecls argsV lvl
    decl.newBindings.foldl (init := init) fun a b => f a op.ann b argsV
  else
    @panic _ ⟨init⟩ "Expected arguments to match bindings"

/--
Invoke a function `f` over a given argument for a function or operation so that
the result context for that argument can be constructed.
-/
partial def foldOverArgAtLevel {α β}
    (m : DialectMap)
    (f : β → α → ∀{argDecls : ArgDecls}, BindingSpec argDecls → Vector (ArgF α) argDecls.size → β)
    (init : β)
    (bindings : ArgDecls)
    (args : Vector (ArgF α) bindings.size)
    (level : Fin bindings.size)
    : β :=
  let init :=
        match bindings.argScopeLevel level with
        | none => init
        | some lvl => foldOverArgAtLevel m f init bindings args ⟨lvl, by omega⟩
  foldOverArgBindingSpecs m f init args[level]

end

inductive GlobalKind where
| expr (tp : TypeExpr)
| type (params : List String) (definition : Option TypeExpr)
deriving BEq, Inhabited, Repr

/-- Resolves a binding spec into a global kind. -/
partial def resolveBindingIndices { argDecls : ArgDecls } (m : DialectMap) (src : SourceRange) (b : BindingSpec argDecls) (args : Vector Arg argDecls.size) : GlobalKind :=
  match b with
  | .value b =>
    match args[b.typeIndex.toLevel] with
    | .type tp =>
      match b.argsIndex with
      | none =>
        .expr tp
      | some idx =>
        let f (a : Array _) (l : SourceRange) {argDecls : ArgDecls} (b : BindingSpec argDecls) args :=
                let type :=
                      match resolveBindingIndices m l b args with
                      | .expr tp => tp
                      | .type _ _ => panic! s!"Expected binding to be expression."
                a.push type
        let fnBindings : Array TypeExpr :=
          foldOverArgAtLevel m f #[] argDecls args idx.toLevel
        .expr <| fnBindings.foldr (init := tp) fun argType tp => .arrow src argType tp
    | .cat c =>
      if c.name = q`Init.Type then
        .type [] none
      else
        panic! s!"Expected new binding to be Type instead of {repr c}."
    | a =>
      panic! s!"Expected new binding to be bound to type instead of {repr a}."
  | .type b =>
    let params : Array String :=
        match b.argsIndex with
        | none => #[]
        | some idx =>
          let addBinding (a : Array String) (_ : SourceRange) {argDecls : _} (b : BindingSpec argDecls) (args : Vector Arg argDecls.size) :=
              match args[b.nameIndex.toLevel] with
              | .ident _ name => a.push name
              | a => panic! s!"Expected ident at {idx.val} {repr a}"
          foldOverArgAtLevel m addBinding #[] argDecls args idx.toLevel
    let value :=
            match b.defIndex with
            | none => none
            | some idx =>
              match args[idx.toLevel] with
              | .type tp =>
                some tp
              | _ => panic! "Bad arg"
    .type params.toList value

/--
Typing environment created from declarations in an environment.
-/
structure GlobalContext where
  nameMap : Std.HashMap Var FreeVarIndex := {}
  vars : Array (Var × GlobalKind) := #[]
deriving BEq, Repr

namespace GlobalContext

instance : Inhabited GlobalContext where
  default := {}

instance : Membership Var GlobalContext where
  mem ctx v := v ∈ ctx.nameMap

theorem mem_def (v : Var) (ctx : GlobalContext) : v ∈ ctx ↔ v ∈ ctx.nameMap := by trivial

instance (v : Var) (ctx : GlobalContext) : Decidable (v ∈ ctx) := by
  rw [mem_def]; infer_instance

def push (ctx : GlobalContext) (v : Var) (k : GlobalKind) : GlobalContext :=
  if v ∈ ctx then
    panic! s!"Var {v} already defined"
  else
    let idx := ctx.vars.size
    { nameMap := ctx.nameMap.insert v idx, vars := ctx.vars.push (v, k) }

/-- Return the index of the variable with the given name. -/
def findIndex? (ctx : GlobalContext) (v : Var) : Option FreeVarIndex := ctx.nameMap.get? v

def nameOf? (ctx : GlobalContext) (idx : FreeVarIndex) : Option String := ctx.vars[idx]? |>.map (·.fst)

def kindOf! (ctx : GlobalContext) (idx : FreeVarIndex) : GlobalKind :=
  assert! idx < ctx.vars.size
  ctx.vars[idx]!.snd

def addCommand (dialects : DialectMap) (init : GlobalContext) (op : Operation) : GlobalContext :=
    op.foldBindingSpecs dialects addBinding init
  where addBinding (gctx : GlobalContext) l _ b args :=
          let name :=
                match args[b.nameIndex.toLevel] with
                | .ident _ e => e
                | a => panic! s!"Expected ident at {b.nameIndex.toLevel} {repr a}"
          let kind := resolveBindingIndices dialects l b args
          gctx.push name kind

end GlobalContext

structure Program where
  mk ::
  /-- Map from dialect names to the dialect definition. -/
  dialects : DialectMap
  /-- Main dialect for program. -/
  dialect : DialectName
  /-- Top level commands in file. -/
  commands : Array Operation := #[]
  /-- Final global context for program. -/
  globalContext : GlobalContext :=
    commands.foldl (init := {}) (·.addCommand dialects ·)

namespace Program

instance : BEq Program where
  beq x y := x.dialect == y.dialect && x.commands == y.commands

instance : Inhabited Program where
  default := { dialects := {}, dialect := default }

def addCommand (env : Program) (cmd : Operation) : Program :=
  { env with
    commands := env.commands.push cmd,
    globalContext := env.globalContext.addCommand env.dialects cmd
  }

/--
This creates a program.  It is added in addition to `Program.mk` to simplify the
`ToExpr Program` instance.
-/
def create (dialects : DialectMap) (dialect : DialectName) (commands : Array Operation) : Program :=
  { dialects, dialect, commands }

end Program

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`. -/
macro "sizeOf_op_arg_dec" : tactic =>
  `(tactic| first
    | with_reducible apply sizeOf_lt_of_op_arg; assumption; done
    | with_reducible
        apply Nat.lt_of_lt_of_le (sizeOf_lt_of_op_arg ?h)
        case' h => assumption
      simp_arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| sizeOf_op_arg_dec)

end Strata

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Std.Data.HashMap.Basic
public import Strata.DDM.AST.Datatype
public import Strata.DDM.Util.ByteArray
public import Strata.DDM.Util.Decimal
public import Strata.DDM.Util.SourceRange

import Std.Data.HashMap
import all Strata.DDM.Util.Array
import all Strata.DDM.Util.ByteArray

set_option autoImplicit false

public section
namespace Strata
open Std (ToFormat Format format)

abbrev DialectName := String

structure QualifiedIdent where
  dialect : DialectName
  name : String
  deriving DecidableEq, Hashable, Inhabited, Repr

namespace QualifiedIdent

def fullName (i : QualifiedIdent) : String := s!"{i.dialect}.{i.name}"

instance : ToString QualifiedIdent where
  toString := fullName

def ofString (fullname : String) : Option QualifiedIdent := do
  let pos := fullname.find (· = '.')
  if p : pos ≠ fullname.endPos then
    return {
      dialect := fullname.extract fullname.startPos pos
      name := fullname.extract (pos.next p) fullname.endPos
    }
  else
    none

section
open _root_.Lean
public protected def quote (i : QualifiedIdent) : Term :=
  Syntax.mkCApp ``QualifiedIdent.mk #[quote i.dialect, quote i.name]

instance : Quote QualifiedIdent where
  quote := QualifiedIdent.quote

syntax:max (name := quoteIdent) "q`" noWs ident : term

@[macro quoteIdent] meta def quoteIdentImpl : Macro
  | `(q`$l:ident) =>
    if let .str (.str .anonymous d) suf := l.getId then
      pure <| Syntax.mkCApp ``QualifiedIdent.mk #[quote d, quote suf]
    else
      throw (.error l.raw "Quoted identifiers must contain two components")
  | _ => Macro.throwUnsupported
end

end QualifiedIdent

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
  /-- A polymorphic type variable (universally quantified).
      Used for polymorphic function type parameters -/
| tvar (ann : α) (name : String)
  /-- A reference to a global variable along with any arguments to ensure it is well-typed. -/
| fvar (ann : α) (fvar : FreeVarIndex) (args : Array (TypeExprF α))
  /-- A function type. -/
| arrow (ann : α) (arg : TypeExprF α) (res : TypeExprF α)
deriving BEq, Inhabited, Repr

namespace TypeExprF

def ann {α} : TypeExprF α → α
| .ident ann _ _ => ann
| .bvar ann _ => ann
| .tvar ann _ => ann
| .fvar ann _ _ => ann
| .arrow ann _ _ => ann

def mkFunType {α} (n : α) (bindings : Array (String × TypeExprF α)) (res : TypeExprF α) : TypeExprF α :=
  bindings.foldr (init := res) fun (_, argType) tp => .arrow n argType tp

protected def incIndices {α} (tp : TypeExprF α) (count : Nat) : TypeExprF α :=
  match tp with
  | .ident n i args => .ident n i (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .fvar n f args => .fvar n f (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .bvar n idx => .bvar n (idx + count)
  | .tvar n name => .tvar n name  -- tvar doesn't use indices
  | .arrow n a r => .arrow n (a.incIndices count) (r.incIndices count)

/-- Return true if type expression has a bound variable. -/
protected def hasUnboundVar {α} (bindingCount : Nat := 0) : TypeExprF α → Bool
| .ident _ _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .fvar _ _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .bvar _ idx => idx ≥ bindingCount
| .tvar _ _ => true
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
  | .tvar n name => pure (.tvar n name)
  | .fvar n idx a => .fvar n idx <$> a.attach.mapM (fun ⟨e, _⟩ => e.instTypeM bindings)
  | .arrow n a b => .arrow n <$> a.instTypeM bindings <*> b.instTypeM bindings
termination_by d

/-- Monadic map over all annotations in a type expression. -/
@[specialize]
def mapAnnM {α β} {m} [Monad m] (t : TypeExprF α) (f : α → m β)
    : m (TypeExprF β) := do
  match t with
  | .ident ann name args =>
    return .ident (← f ann) name
      (← args.attach.mapM fun ⟨e, _⟩ => e.mapAnnM f)
  | .bvar ann index => return .bvar (← f ann) index
  | .tvar ann name => return .tvar (← f ann) name
  | .fvar ann fv args =>
    return .fvar (← f ann) fv
      (← args.attach.mapM fun ⟨e, _⟩ => e.mapAnnM f)
  | .arrow ann arg res =>
    return .arrow (← f ann) (← arg.mapAnnM f) (← res.mapAnnM f)
termination_by t

/-- Map over all annotations in a type expression. -/
@[specialize]
def mapAnn {α β} (t : TypeExprF α) (f : α → β) : TypeExprF β :=
  t.mapAnnM (m := Id) f

end TypeExprF

/-- Separator format for sequence formatting -/
inductive SepFormat where
| none           -- No separator (original Seq)
| comma          -- Comma separator (CommaSepBy)
| space          -- Space separator (SpaceSepBy)
| spacePrefix    -- Space before each element (SpacePrefixSepBy)
| newline        -- Newline separator (NewlineSepBy)
deriving Inhabited, Repr, BEq

namespace SepFormat

def toString : SepFormat → String
  | .none => "seq"
  | .comma => "commaSepBy"
  | .space => "spaceSepBy"
  | .spacePrefix => "spacePrefixSepBy"
  | .newline => "newlineSepBy"

def fromCategoryName? : QualifiedIdent → Option SepFormat
  | q`Init.Seq => some .none
  | q`Init.CommaSepBy => some .comma
  | q`Init.SpaceSepBy => some .space
  | q`Init.SpacePrefixSepBy => some .spacePrefix
  | q`Init.NewlineSepBy => some .newline
  | _ => none

instance : ToString SepFormat where
  toString := SepFormat.toString

end SepFormat

mutual

inductive ExprF (α : Type) : Type where
  /--
  A bound variable reference (de Bruijn index).

  If this is a function, then the arguments are always value-level;
  type arguments are omitted.
  -/
| bvar (ann : α) (idx : Nat)
  /--
  A free variable reference.

  If this is a function, then the arguments are always value-level;
  type arguments are omitted.
  -/
| fvar (ann : α) (idx : FreeVarIndex)
  /-- A named dialect function. -/
| fn (ann : α) (ident : QualifiedIdent)
  /-- Function application. -/
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
| seq (ann : α) (sep : SepFormat) (l : Array (ArgF α))
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
| .seq ann _ _ => ann

end

namespace OperationF

theorem sizeOf_spec {α} [SizeOf α] (op : OperationF α) : sizeOf op = 1 + sizeOf op.ann + sizeOf op.name + sizeOf op.args :=
  match op with
  | { ann, name, args } => by simp

private theorem sizeOf_lt_of_op_arg {α} {e : ArgF α} {op : OperationF α} (p : e ∈ op.args) : sizeOf e < sizeOf op := by
  let ⟨ann, name, args⟩ := op
  have q : sizeOf e < sizeOf args := by decreasing_tactic
  decreasing_tactic

end OperationF

namespace ExprF

/--
Flattens a curried application expression into its head and list of arguments.
For example, `((f a) b) c` becomes `(f, [a, b, c])`.
-/
public def flatten {α} (e : ExprF α) (prev : List (ArgF α) := []) : ExprF α × List (ArgF α) :=
  match e with
  | .app _ f e => f.flatten (e :: prev)
  | _ => (e, prev)

end ExprF

/-- Monadic map over all annotations in a syntax category. -/
@[specialize]
def SyntaxCatF.mapAnnM {α β} {m} [Monad m] (c : SyntaxCatF α)
    (f : α → m β) : m (SyntaxCatF β) := do
  return {
    ann := ← f c.ann
    name := c.name
    args := ← c.args.attach.mapM fun ⟨e, _⟩ => e.mapAnnM f
  }
termination_by sizeOf c
decreasing_by
  cases c
  case mk ann name args =>
    decreasing_tactic

/-- Map over all annotations in a syntax category. -/
@[specialize]
def SyntaxCatF.mapAnn {α β} (c : SyntaxCatF α) (f : α → β) : SyntaxCatF β :=
  c.mapAnnM (m := Id) f

mutual

/-- Monadic map over all annotations in an expression. -/
@[specialize]
def ExprF.mapAnnM {α β} {m} [Monad m] (e : ExprF α) (f : α → m β)
    : m (ExprF β) := do
  match e with
  | .bvar ann idx => return .bvar (← f ann) idx
  | .fvar ann idx => return .fvar (← f ann) idx
  | .fn ann ident => return .fn (← f ann) ident
  | .app ann e a =>
    return .app (← f ann) (← e.mapAnnM f) (← a.mapAnnM f)
termination_by sizeOf e

/-- Monadic map over all annotations in an argument. -/
@[specialize]
def ArgF.mapAnnM {α β} {m} [Monad m] (a : ArgF α) (f : α → m β)
    : m (ArgF β) := do
  match a with
  | .op o => return .op (← o.mapAnnM f)
  | .cat c => return .cat (← c.mapAnnM f)
  | .expr e => return .expr (← e.mapAnnM f)
  | .type t => return .type (← t.mapAnnM f)
  | .ident ann i => return .ident (← f ann) i
  | .num ann v => return .num (← f ann) v
  | .decimal ann v => return .decimal (← f ann) v
  | .strlit ann i => return .strlit (← f ann) i
  | .bytes ann b => return .bytes (← f ann) b
  | .option ann none => return .option (← f ann) none
  | .option ann (some a) =>
    return .option (← f ann) (some (← a.mapAnnM f))
  | .seq ann sep l =>
    return .seq (← f ann) sep
      (← l.attach.mapM fun ⟨e, _⟩ => e.mapAnnM f)
termination_by sizeOf a

/-- Map a monadic function over all annotations in an operation. -/
@[specialize]
def OperationF.mapAnnM {α β} {m} [Monad m] (op : OperationF α)
    (f : α → m β) : m (OperationF β) := do
  return {
    ann := ← f op.ann
    name := op.name
    args := ← op.args.attach.mapM fun ⟨e, _⟩ => e.mapAnnM f
  }
termination_by sizeOf op
decreasing_by
  cases op
  case mk ann name args =>
    decreasing_tactic

end

/-- Map a pure function over all annotations in an expression. -/
@[specialize]
def ExprF.mapAnn {α β} (e : ExprF α) (f : α → β) : ExprF β :=
  e.mapAnnM (m := Id) f

/-- Map a pure function over all annotations in an argument. -/
@[specialize]
def ArgF.mapAnn {α β} (a : ArgF α) (f : α → β) : ArgF β :=
  a.mapAnnM (m := Id) f

/-- Map a pure function over all annotations in an operation. -/
@[specialize]
def OperationF.mapAnn {α β} (op : OperationF α) (f : α → β) : OperationF β :=
  op.mapAnnM (m := Id) f

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
private def ExprF.beq {α} [BEq α] (e1 e2 : ExprF α) : Bool :=
  match e1, e2 with
  | .bvar a1 i1, .bvar a2 i2
  | .fvar a1 i1, .fvar a2 i2
  | .fn a1 i1, .fn a2 i2 => a1 == a2 && i1 == i2
  | .app a1 x1 y1, .app a2 x2 y2 => a1 == a2 && ExprF.beq x1 x2 && ArgF.beq y1 y2
  | _, _ => false
termination_by sizeOf e1

private def OperationF.beq {α} [BEq α] (o1 o2 : OperationF α) : Bool :=
  o1.ann == o2.ann
  && o1.name = o2.name
  && ArgF.array_beq o1.args o2.args
termination_by sizeOf o1
decreasing_by
  simp [OperationF.sizeOf_spec]
  omega

private def ArgF.beq {α} [BEq α] (a1 a2 : ArgF α) : Bool :=
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
  | .seq a1 sep1 v1, .seq a2 sep2 v2 =>
    a1 == a2 && sep1 == sep2 && ArgF.array_beq v1 v2
  | _, _ => false
termination_by sizeOf a1

private def ArgF.array_beq {α} [BEq α] (a1 a2 : Array (ArgF α)) : Bool :=
  if size_eq : a1.size = a2.size then
    a1.size.all fun i p => ArgF.beq a1[i] a2[i]
  else
    false
termination_by sizeOf a1

end

-- TODO: extend these to DecidableEq
instance {α} [BEq α] : BEq (ExprF α) where beq := private ExprF.beq
instance {α} [BEq α] : BEq (OperationF α) where beq := private OperationF.beq
instance {α} [BEq α] : BEq (ArgF α) where beq := private ArgF.beq

inductive MetadataArg where
| bool (e : Bool)
| catbvar (index : Nat) -- This is a deBrujin index into current typing environment.
| num (e : Nat)
| option (a : Option MetadataArg)
| functionTemplate (t : FunctionTemplate) -- Function template for datatype declarations
deriving BEq, Inhabited, Repr

namespace MetadataArg

@[instance]
protected def instDecidableEq (x y : MetadataArg) : Decidable (x = y) :=
  match x with
  | .bool x =>
    match y with
    | .bool y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .catbvar _ | .num _ | .option _ | .functionTemplate _ => .isFalse (by grind)
  | .catbvar x =>
    match y with
    | .catbvar y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .bool _ | .num _ | .option _ | .functionTemplate _ => .isFalse (by grind)
  | .num x =>
    match y with
    | .num y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by grind)
    | .bool _ | .catbvar _ | .option _ | .functionTemplate _ => .isFalse (by grind)
  | .option x =>
    match y with
    | .option y =>
      match x, y with
      | none, none => .isTrue (by grind)
      | some x, some y =>
        match MetadataArg.instDecidableEq x y with
        | .isTrue p => .isTrue (by grind)
        | .isFalse p => .isFalse (by grind)
      | none, some _ | some _, none => .isFalse (by grind)
    | .bool _ | .catbvar _ | .num _ | .functionTemplate _ => .isFalse (by grind)
  | .functionTemplate x =>
    match y with
    | .functionTemplate y =>
      if p : x = y then
        .isTrue (congrArg _ p)
      else
        .isFalse (by intro h; injection h; contradiction)
    | .bool _ | .catbvar _ | .num _ | .option _ => .isFalse (by grind)

end MetadataArg

structure MetadataAttr where
  ident : QualifiedIdent
  args : Array MetadataArg
deriving DecidableEq, Inhabited, Repr

namespace MetadataAttr

private def scopeName := q`StrataDDL.scope

/-- Create scope using deBrujin index of environment. -/
def scope (idx : Nat) : MetadataAttr :=
  { ident := scopeName, args := #[.catbvar idx ] }

end MetadataAttr

structure Metadata where
  ofArray ::
  toArray : Array MetadataAttr
deriving DecidableEq, Repr

namespace Metadata

protected def emptyWithCapacity (c : Nat) : Metadata := { toArray := .emptyWithCapacity c }

protected def empty : Metadata := .emptyWithCapacity 0

instance : EmptyCollection Metadata where
  emptyCollection := .empty

protected def push (md : Metadata) (attr : MetadataAttr) : Metadata :=
  .ofArray <| md.toArray.push attr

instance : Inhabited Metadata where
  default := {}

def isEmpty (md : Metadata) := md.toArray.isEmpty

def toList (m : Metadata) : List MetadataAttr := m.toArray.toList

instance : Membership QualifiedIdent Metadata where
  mem md x := private md.toArray.any fun a => a.ident = x

@[instance]
def instDecidableMem (x : QualifiedIdent) (md : Metadata) : Decidable (x ∈ md) := by
  apply instDecidableEqBool

instance : GetElem? Metadata QualifiedIdent (Array MetadataArg) (fun md i => i ∈ md) where
  getElem md i _p := private
    match md.toArray.find? (·.ident = i) with
    | none => default
    | some a => a.args
  getElem? md i := private
    match md.toArray.find? (·.ident = i) with
    | none => none
    | some a => a.args

private def scopeIndex (metadata : Metadata) : Option Nat :=
  match metadata[MetadataAttr.scopeName]? with
  | none => none
  | some #[.catbvar idx] => some idx
  | some _ => panic! s!"Unexpected argument count to {MetadataAttr.scopeName.fullName}"

/-- Returns the datatype scope indices (nameIndex, typeParamsIndex) if @[scopeDatatype] is present. -/
def scopeDatatypeIndex (metadata : Metadata) : Option (Nat × Nat) :=
  match metadata[q`StrataDDL.scopeDatatype]? with
  | none => none
  | some #[.catbvar nameIdx, .catbvar typeParamsIdx] => some (nameIdx, typeParamsIdx)
  | some _ => panic! s!"Unexpected argument count to scopeDatatype"

/-- Returns the name index if @[declareTVar] is present.
    Used for operations that introduce a type variable (creates .tvar binding in result context). -/
def declareTVarIndex (metadata : Metadata) : Option Nat :=
  match metadata[q`StrataDDL.declareTVar]? with
  | none => none
  | some #[.catbvar nameIdx] => some nameIdx
  | some _ => panic! s!"Unexpected argument count to declareTVar"

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
private def resultIndex (metadata : Metadata) : Option Nat :=
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

/--
Converts a deBruijn index to a level (counting from the start rather than
the end). Used internally for metadata argument processing.
-/
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
  /-- A bound type variable at the given deBruijn index in the context.
      Used for type alias parameters -/
| bvar (ann : SourceRange) (index : Nat)
  /-- A polymorphic type variable (universally quantified).
      Used for polymorphic function type parameters -/
| tvar (ann : SourceRange) (name : String)
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
| .tvar ann _ => ann
| .fvar ann _ _ => ann
| .arrow ann _ _ => ann
| .funMacro ann _ _ => ann

def ofType : TypeExprF SourceRange → PreType
| .ident loc name args => .ident loc name (args.map fun a => .ofType a)
| .bvar loc idx => .bvar loc idx
| .tvar loc name => .tvar loc name
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
A token in a syntax definition.
-/
inductive SyntaxDefAtom
/-- Argument reference. Parenthesizes when the argument's precedence is
≤ `prec`; `prec = 0` disables parenthesization. -/
| ident (level : Nat) (prec : Nat)
/-- Literal string token. -/
| str (lit : String)
/-- Indented block of tokens. -/
| indent (n : Nat) (args : Array SyntaxDefAtom)
deriving BEq, Inhabited, Repr

/--
Syntax definition for an operator or function.
-/
inductive SyntaxDef
/-- Standard syntax with explicit atoms and precedence. -/
| std (atoms : Array SyntaxDefAtom) (prec : Nat)
/-- Single-argument syntax that inherits the argument's precedence. -/
| passthrough
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
  .std atoms appPrec

def ofList (atoms : List SyntaxDefAtom) (prec : Nat := maxPrec) : SyntaxDef :=
  .std atoms.toArray prec

end SyntaxDef

structure DebruijnIndex (n : Nat) where
  val : Nat
  isLt : val < n
deriving Repr

namespace DebruijnIndex

def toLevel {n} : DebruijnIndex n → Fin n
| ⟨v, lt⟩ => ⟨n - (v+1), by omega⟩

protected def ofNat {n : Nat} [NeZero n] (a : Nat) : DebruijnIndex n :=
  ⟨a % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

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
  metadata : Metadata := {}
deriving BEq, Inhabited, Repr

structure ArgDecls where
  ofArray ::
  toArray : Array ArgDecl
deriving BEq, Inhabited, Repr

namespace ArgDecls

protected def empty : ArgDecls := { toArray := #[] }

instance : EmptyCollection ArgDecls where
  emptyCollection := .empty

@[expose] protected def size (a : ArgDecls) : Nat := a.toArray.size

protected def isEmpty (a : ArgDecls) : Bool := a.toArray.isEmpty

instance : GetElem ArgDecls Nat ArgDecl fun a i => i < a.size where
  getElem a i p := private a.toArray[i]

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

/-- Returns the datatype scope indices (nameLevel, typeParamsLevel) if @[scopeDatatype] is present.
    This is used for recursive datatype definitions where the datatype name must be in scope
    when parsing constructor field types. -/
def argScopeDatatypeLevel (argDecls : ArgDecls) (level : Fin argDecls.size) : Option (Fin level.val × Fin level.val) :=
  match argDecls[level].metadata.scopeDatatypeIndex with
  | none => none
  | some (nameIdx, typeParamsIdx) =>
    if h1 : nameIdx < level.val then
      if h2 : typeParamsIdx < level.val then
        some (⟨level.val - (nameIdx + 1), by omega⟩, ⟨level.val - (typeParamsIdx + 1), by omega⟩)
      else
        panic! s!"scopeDatatype typeParams index {typeParamsIdx} out of bounds ({level.val})"
    else
      panic! s!"scopeDatatype name index {nameIdx} out of bounds ({level.val})"

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

/-! ## Datatype Type Building Functions -/

/--
Resolve a type reference to a concrete TypeExpr. A type reference is
either a datatype, field type (within perField/perConstructor scope),
or a built-in (e.g. "bool")
-/
def resolveTypeRef (ref : TypeRef)
    (datatypeType : TypeExpr)
    (fieldType : Option TypeExpr := none)
    (dialectName : String) : Except String TypeExpr :=
  match ref with
  | .datatype => .ok datatypeType
  | .fieldType =>
    match fieldType with
    | some ft => .ok ft
    | none => .error "TypeRef.fieldType is only valid in perField scope"
  | .builtin name => .ok <| TypeExprF.ident default ⟨dialectName, name⟩ #[]

/--
Information about a single constructor in a datatype.
-/
structure ConstructorInfo where
  /-- Constructor name -/
  name : String
  /-- Fields as (fieldName, fieldType) pairs -/
  fields : Array (String × TypeExpr)
  deriving Repr

/--
Build a TypeExpr reference to the datatype with type parameters, using
`.fvar` for the datatype's GlobalContext index and `.tvar` for type parameters.
-/
def mkDatatypeTypeRef (ann : SourceRange) (datatypeIndex : FreeVarIndex) (typeParams : Array String) : TypeExpr :=
  let typeArgs := typeParams.map fun name => TypeExprF.tvar ann name
  TypeExprF.fvar ann datatypeIndex typeArgs

/--
Build an arrow type from field types to the datatype type. E.g. for cons,
creates `a -> List a -> List a`.
-/
def mkConstructorType (ann : SourceRange) (datatypeType : TypeExpr) (fields : Array (String × TypeExpr)) : TypeExpr :=
  fields.foldr (init := datatypeType) fun (_, fieldType) resultType =>
    TypeExprF.arrow ann fieldType resultType

/--
Build a function type from parameter types and return type.
Returns an arrow type: param1 -> param2 -> ... -> returnType
-/
def buildFunctionType (template : FunctionTemplate)
    (datatypeType : TypeExpr)
    (fieldType : Option TypeExpr)
    (dialectName : String) : Except String TypeExpr := do
  -- Resolve all parameter types
  let paramTypes ← template.paramTypes.mapM fun ref =>
    resolveTypeRef ref datatypeType fieldType dialectName
  -- Resolve return type
  let returnType ← resolveTypeRef template.returnType datatypeType fieldType dialectName
  -- Build arrow type: param1 -> param2 -> ... -> returnType
  .ok <| paramTypes.foldr (init := returnType) fun argType tp => .arrow default argType tp

/--
Result of expanding a single template.
Contains the generated function signatures and any errors encountered.
-/
structure TemplateExpansionResult where
  /-- Generated function signatures as (name, type) pairs -/
  functions : Array (String × TypeExpr)
  /-- Errors encountered during expansion -/
  errors : Array String
  deriving Repr

/--
Expand a single function template based on its scope.

Function templates specify patterns for generating auxiliary functions
from datatype declarations. This function expands one template according to
its iteration scope:

- **perConstructor**: Generates one function per constructor (e.g., testers
like `..isNone`)
- **perField**: Generates one function per unique field across all constructors
(e.g., accessors)

**Parameters:**
- `datatypeName`: Name of the datatype (used in name pattern expansion)
- `datatypeType`: TypeExpr for the datatype (used in function signatures)
- `constructorInfo`: Array of constructor information
- `template`: The function template to expand
- `dialectName`: Dialect name (for resolving builtin types)
- `existingNames`: Set of already-used names (for duplicate detection)

**Example:** For a `perConstructor` template defined as:
```
perConstructor([.datatype, .literal "..is", .constructor], [.datatype],
.builtin "bool")
```
This specifies:
- Name pattern: `[.datatype, .literal "..is", .constructor]` → generates names
like `Option..isNone`
- Parameter types: `[.datatype]` → takes one parameter of the datatype type
- Return type: `.builtin "bool"` → returns a boolean

Applied to `Option<T>` with constructors `None` and `Some`, this generates:
- `Option..isNone : Option<T> -> bool`
- `Option..isSome : Option<T> -> bool`
-/
def expandSingleTemplate
    (datatypeName : String)
    (datatypeType : TypeExpr)
    (constructorInfo : Array ConstructorInfo)
    (template : FunctionTemplate)
    (dialectName : String)
    (existingNames : Std.HashSet String) : TemplateExpansionResult :=
  -- First validate the pattern
  match validateNamePattern template.namePattern template.scope with
  | some err => { functions := #[], errors := #[err] }
  | none =>
    match template.scope with
    | .perConstructor =>
      -- Generate one function per constructor
      let (funcs, errs, _) := constructorInfo.foldl (init := (#[], #[], existingNames)) fun (funcs, errs, names) constr =>
        let funcName := expandNamePattern template.namePattern datatypeName (some constr.name)
        if names.contains funcName then
          (funcs, errs.push s!"Duplicate function name: {funcName}", names)
        else
          match buildFunctionType template datatypeType none dialectName with
          | .ok funcType =>
            (funcs.push (funcName, funcType), errs, names.insert funcName)
          | .error e =>
            (funcs, errs.push e, names)
      { functions := funcs, errors := errs }

    | .perField =>
      -- Generate one function per unique field across all constructors
      -- Error if the same field name appears with different types
      let allFields := constructorInfo.foldl (init := #[]) fun acc c => acc ++ c.fields
      let (funcs, errs, _) := allFields.foldl (init := (#[], #[], existingNames)) fun (funcs, errs, names) (fieldName, fieldTp) =>
        let funcName := expandNamePattern template.namePattern datatypeName none (some fieldName)
        if names.contains funcName then
          (funcs, errs.push s!"Duplicate field name '{fieldName}' across constructors in datatype '{datatypeName}'", names)
        else
          match buildFunctionType template datatypeType (some fieldTp) dialectName with
          | .ok funcType =>
            (funcs.push (funcName, funcType), errs, names.insert funcName)
          | .error e =>
            (funcs, errs.push e, names)
      { functions := funcs, errors := errs }

/--
This function generates function signatures for an array of function templates
in order. Templates are specified in `@[declareDatatype]` annotations
to automatically generate auxiliary functions like testers and field accessors.
Within each template, functions are generated in constructor/field declaration order.

**Parameters:**
- `datatypeName`: Name of the datatype
- `datatypeType`: TypeExpr for the datatype
- `constructorInfo`: Array of constructor information
- `templates`: Array of function templates to expand
- `dialectName`: Dialect name (for resolving builtin types)
- `existingNames`: Optional set of pre-existing names to avoid
-/
def expandFunctionTemplates
    (datatypeName : String)
    (datatypeType : TypeExpr)
    (constructorInfo : Array ConstructorInfo)
    (templates : Array FunctionTemplate)
    (dialectName : String)
    (existingNames : Std.HashSet String := {}) : TemplateExpansionResult :=
  templates.foldl (init := { functions := #[], errors := #[] }) fun acc template =>
    -- Track names from previous templates to detect cross-template duplicates
    let currentNames := acc.functions.foldl (init := existingNames) fun s (name, _) => s.insert name
    let result := expandSingleTemplate datatypeName datatypeType constructorInfo template dialectName currentNames
    { functions := acc.functions ++ result.functions
      errors := acc.errors ++ result.errors }

/--
Specification for datatype declarations.
Includes indices for extracting datatype information and optional function templates.
-/
structure DatatypeBindingSpec (argDecls : ArgDecls) where
  /-- deBrujin index of datatype name -/
  nameIndex : DebruijnIndex argDecls.size
  /-- deBrujin index of type parameters -/
  typeParamsIndex : DebruijnIndex argDecls.size
  /-- deBrujin index of constructors -/
  constructorsIndex : DebruijnIndex argDecls.size
  /-- Optional list of function templates to expand -/
  functionTemplates : Array FunctionTemplate := #[]
  deriving Repr

/--
Specification for declaring a single type variable.
Creates a .tvar binding in the result context.
-/
structure TvarBindingSpec (argDecls : ArgDecls) where
  /-- deBrujin index of the identifier to become a type variable -/
  nameIndex : DebruijnIndex argDecls.size
  deriving Repr

/-
A spec for introducing a new binding into a type context.
-/
inductive BindingSpec (argDecls : ArgDecls) where
| value (_ : ValueBindingSpec argDecls)
| type (_ : TypeBindingSpec argDecls)
| typeForward (_ : TypeBindingSpec argDecls)  -- Forward declaration (no AST node)
| datatype (_ : DatatypeBindingSpec argDecls)
| tvar (_ : TvarBindingSpec argDecls)
deriving Repr

namespace BindingSpec

def nameIndex {argDecls} : BindingSpec argDecls → DebruijnIndex argDecls.size
| .value v => v.nameIndex
| .type v => v.nameIndex
| .typeForward v => v.nameIndex
| .datatype v => v.nameIndex
| .tvar v => v.nameIndex

end BindingSpec

/-- Monad for parsing new binding specifications, accumulating error messages. -/
private abbrev NewBindingM := StateM (Array String)

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

/-- Parse function templates from metadata arguments. -/
private def parseFunctionTemplates (args : Array MetadataArg) : Array FunctionTemplate :=
  args.filterMap fun arg =>
    match arg with
    | .functionTemplate t => some t
    | _ => none

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
        | q`StrataDDL.declareTypeForward => do
          let #[.catbvar nameIndex, .option mArgsArg ] := attr.args
            | newBindingErr s!"declareTypeForward has bad arguments {repr attr.args}."; return none
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
                | _ => newBindingErr "declareTypeForward args invalid."; return none
          some <$> .typeForward <$> pure { nameIndex, argsIndex, defIndex := none }
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
        | { dialect := _, name := "declareDatatype" } => do
          let args := attr.args
          if args.size < 3 then
            newBindingErr "declareDatatype expects at least 3 arguments (name, typeParams, constructors)."
            return none
          let .catbvar nameIndex := args[0]!
            | newBindingErr "declareDatatype: invalid name index"; return none
          let .catbvar typeParamsIndex := args[1]!
            | newBindingErr "declareDatatype: invalid typeParams index"; return none
          let .catbvar constructorsIndex := args[2]!
            | newBindingErr "declareDatatype: invalid constructors index"; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          let .isTrue typeParamsP := inferInstanceAs (Decidable (typeParamsIndex < argDecls.size))
            | return panic! "Invalid typeParams index"
          let .isTrue constructorsP := inferInstanceAs (Decidable (constructorsIndex < argDecls.size))
            | return panic! "Invalid constructors index"
          -- Parse function templates from remaining arguments (args[3..])
          let functionTemplates := parseFunctionTemplates (args.extract 3 args.size)
          some <$> .datatype <$> pure {
            nameIndex := ⟨nameIndex, nameP⟩,
            typeParamsIndex := ⟨typeParamsIndex, typeParamsP⟩,
            constructorsIndex := ⟨constructorsIndex, constructorsP⟩,
            functionTemplates
          }
        | q`StrataDDL.declareTVar => do
          let #[.catbvar nameIndex] := attr.args
            | newBindingErr "declareTVar expects 1 argument."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < argDecls.size))
            | return panic! "Invalid name index"
          some <$> .tvar <$> pure { nameIndex := ⟨nameIndex, nameP⟩ }
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
  metadata : Metadata := {}
  /-- New bindings -/
  newBindings : Array (BindingSpec argDecls) := parseNewBindings! metadata argDecls
deriving Inhabited, Repr

namespace OpDecl

instance : BEq OpDecl where
  beq x y := private
    x.name = y.name
    && x.argDecls == y.argDecls
    && x.category = y.category
    && x.syntaxDef == y.syntaxDef
    && x.metadata == y.metadata

end OpDecl

abbrev FnName := String

structure FunctionDecl where
  name : FnName
  argDecls : ArgDecls
  result : PreType
  syntaxDef : SyntaxDef
  metadata : Metadata := {}
deriving BEq, Inhabited, Repr

inductive MetadataArgType
| num
| ident
| bool
| opt (tp : MetadataArgType)
| functionTemplate  -- Function template for datatype declarations
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

instance {m α} [Monad m] : ForIn m (Collection α) α where
  forIn c i f := private do
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
  toString c := private
    let step i a :=
          let r := if i.fst then i.snd else i.snd ++ ", "
          (false, r ++ c.pretty a)
    (c.fold step (true, "{") |>.snd) ++ "}"

private inductive Mem {α} (c : Collection α) (nm : String) : Prop
| intro : (h : nm ∈ c.cache) → (r : α) → c.proj (c.cache[nm]) = some r → Mem c nm

private def Mem.inCache {α} {c : Collection α} {nm} : Mem c nm → nm ∈ c.cache
| .intro h _ _ => h

instance {α} : Membership String (Collection α) where
  mem := private Mem

def decideMap {α} (nm : String) (c : Collection α) : Decidable (nm ∈ c) :=
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

@[instance]
def instDecidableMem {α} (nm : String) (c : Collection α) : Decidable (nm ∈ c) :=
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

instance {α} : GetElem? (Collection α) String α (fun c nm => nm ∈ c) where
  getElem c nm p := private
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
  getElem? c nm := private
    match c.cache[nm]? with
    | none => none
    | some d => c.proj d

end Collection

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

namespace Dialect

instance : Inhabited Dialect where
  default := {
    name := default
    imports := #[]
  }

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

instance : Membership String Dialect where
  mem d nm := private nm ∈ d.cache

@[instance]
def instDecidableMem (nm : String) (d : Dialect) : Decidable (nm ∈ d) :=
  inferInstanceAs (Decidable (nm ∈ d.cache))

end Dialect

/-- BEq between two Std HashMap; checked by doing inclusion test twice -/
private instance {α β} [BEq α] [Hashable α] [BEq β]: BEq (Std.HashMap α β) where
  beq x y := Id.run do
    if x.size ≠ y.size then
      return false
    for (k, v) in x do
      if y.get? k != Option.some v then
        return false
    return true

def DialectMap.Closed (map : Std.HashMap DialectName Dialect) :=
  ∀(d : DialectName) (p: d ∈ map), map[d].imports.all (· ∈ map)

structure DialectMap where
  private map : Std.HashMap DialectName Dialect
  private closed : DialectMap.Closed map

namespace DialectMap

private instance : BEq DialectMap where
  beq x y := x.map == y.map

protected def empty : DialectMap := { map := {}, closed := fun _ p => by simp at p }

instance : EmptyCollection DialectMap where
  emptyCollection := .empty

instance : Inhabited DialectMap where
  default := private .empty

instance : Membership DialectName DialectMap where
  mem m d := private d ∈ m.map

@[instance]
def instDecidableMem (d : DialectName) (m : DialectMap) : Decidable (d ∈ m) :=
  inferInstanceAs (Decidable (d ∈ m.map))

instance : GetElem? DialectMap DialectName Dialect (fun m d => d ∈ m) where
  getElem m d p := private m.map[d]
  getElem? m d := private m.map[d]?
  getElem! m d := private m.map[d]!

private theorem insert_preserves_closed
  (m : Std.HashMap DialectName Dialect)
  (m_closed : DialectMap.Closed m)
  (d : Dialect)
  (d_imports_ok : d.imports.all (· ∈ m))
  (name : DialectName)
  (mem : name ∈ m.insert d.name d) :
      ((m.insert d.name d)[name].imports.all fun x => decide (x ∈ m.insert d.name d)) = true := by
  if eq : d.name = name then
    simp at d_imports_ok
    simp [eq]
    intro i lt
    exact Or.inr (d_imports_ok i lt)
  else
    simp only [Std.HashMap.mem_insert, eq, beq_iff_eq, false_or] at mem
    have cl := m_closed name mem
    simp at cl
    simp [Std.HashMap.getElem_insert, eq]
    intro i lt
    exact Or.inr (cl i lt)

/--
This inserts a new dialect into the dialect map.

This requires propositions to ensure we do not change the semantics
of dialects and imports are already in dialect.
-/
def insert (m : DialectMap) (d : Dialect) (_d_new : d.name ∉ m) (d_imports_ok : d.imports.all (· ∈ m)) : DialectMap :=
  { map := m.map.insert d.name d
    closed := insert_preserves_closed m.map m.closed d d_imports_ok
  }

/--
This inserts a dialect in to the dialect map.

It panics if a dialect with the same name is already in the map
or if the dialect imports a dialect not already in the map.
-/
def insert! (m : DialectMap) (d : Dialect) : DialectMap :=
  if d_new : d.name ∈ m.map then
    panic! s!"{d.name} already in map."
  else
    if d_imports_ok : d.imports.all (· ∈ m.map) then
      m.insert d d_new d_imports_ok
    else
      panic! s!"Missing import."

def ofList! (l : List Dialect) : DialectMap :=
  let map : Std.HashMap DialectName Dialect :=
        l.foldl (init := .emptyWithCapacity l.length) fun m d =>
          m.insert d.name d
  let check := map.toArray.all fun (_, d) => d.imports.all (· ∈ map)
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

private def toListAux (m : DialectMap) : List Dialect := m.map.values

protected def toList (m : DialectMap) : List Dialect := toListAux m

def decl! (dm : DialectMap) (ident : QualifiedIdent) : Decl :=
  match dm.map[ident.dialect]? with
  | none => panic! s!"Unknown dialect {ident.dialect}"
  | some d =>
    match d.cache[ident.name]? with
    | some decl => decl
    | none => panic! s!"Unknown declaration {ident.fullName}"

/--
Return set of all dialects that are imported by `dialect`.

This includes transitive imports.
-/
private partial def importedDialectsAux (dmm : Std.HashMap DialectName Dialect) (dmm_closed : DialectMap.Closed dmm) (dialect : DialectName) (p : dialect ∈ dmm) : DialectMap :=
    aux {} #[dialect] (by simp; exact p) (by simp)
  where aux (map : Std.HashMap DialectName Dialect)
            (next : Array DialectName)
            (nextp : ∀name, name ∈ next → name ∈ dmm)
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
              have name_in_dm : name ∈ dmm := nextp name (by grind)
              let d := dmm[name]
              aux (map.insert name d) (next.pop ++ d.imports)
                (by
                  intro nm nm_mem
                  simp at nm_mem
                  match nm_mem with
                  | .inl nm_mem =>
                    exact nextp _ (Array.of_mem_pop nm_mem)
                  | .inr nm_mem =>
                    have inv := dmm_closed name name_in_dm
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

/--
Return set of all dialects that are imported by `dialect`.

This includes transitive imports.
-/
partial def importedDialects (dm : DialectMap) (dialect : DialectName) (p : dialect ∈ dm) : DialectMap :=
  importedDialectsAux dm.map dm.closed dialect p

end DialectMap

mutual

/--
Recursively folds over all binding specifications declared within an argument.
Used to collect type bindings, value bindings, and other declarations that
appear nested within operation arguments.
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
  | .seq _ _ a => a.attach.foldl (init := init) fun init ⟨a, _⟩ => foldOverArgBindingSpecs m f init a

/--
Invoke a function `f` over each of the declaration specifications for an operator.
-/
private partial def OperationF.foldBindingSpecs {α β}
    (m : DialectMap)
    (f : β → α → ∀{argDecls : ArgDecls}, BindingSpec argDecls → Vector (ArgF α) argDecls.size → β)
    (init : β)
    (op : OperationF α)
    : β :=

  match m.decl! op.name with
  | .op decl =>
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
      @panic _ ⟨init⟩ s!"{op.name} expects {argDecls.size} arguments when {args.size} provided."
  | _ => @panic _ ⟨init⟩ s!"Unknown operation {op.name}"

/--
Invoke a function `f` over a given argument for a function or operation so that
the result context for that argument can be constructed.
-/
private partial def foldOverArgAtLevel {α β}
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

/-- State of a symbol in the GlobalContext -/
inductive DeclState where
  | forward   -- Symbol is forward-declared (no AST node will be generated)
  | defined   -- Symbol has a complete definition
deriving BEq, DecidableEq, Repr, Inhabited

/-- Resolves a binding spec into a global kind. -/
partial def resolveBindingIndices { argDecls : ArgDecls } (m : DialectMap) (src : SourceRange) (b : BindingSpec argDecls) (args : Vector Arg argDecls.size) : Option GlobalKind :=
  match b with
  | .value b =>
    match args[b.typeIndex.toLevel] with
    | .type tp =>
      match b.argsIndex with
      | none =>
        some <| .expr tp
      | some idx =>
        let f (a : Array _) (l : SourceRange) {argDecls : ArgDecls} (b : BindingSpec argDecls) args :=
                match resolveBindingIndices m l b args with
                | some (.expr tp) => a.push tp
                | some (.type _ _) => panic! s!"Expected binding to be expression."
                | none => a
        let fnBindings : Array TypeExpr :=
          foldOverArgAtLevel m f #[] argDecls args idx.toLevel
        some <| .expr <| fnBindings.foldr (init := tp) fun argType tp => .arrow src argType tp
    | .cat c =>
      if c.name = q`Init.Type then
        some <| .type [] none
      else
        panic! s!"Expected new binding to be Type instead of {repr c}."
    | a =>
      panic! s!"Expected new binding to be bound to type instead of {repr a}."
  | .type b | .typeForward b =>
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
    some <| .type params.toList value
  | .datatype b =>
    /- For datatypes, resolveBindingIndices only returns the datatype type
    itself; the constructors and template-generated functions are handled
    separately in addDatatypeBindings. -/
    let params : Array String :=
        let addBinding (a : Array String) (_ : SourceRange) {argDecls : _} (b : BindingSpec argDecls) (args : Vector Arg argDecls.size) :=
            match args[b.nameIndex.toLevel] with
            | .ident _ name => a.push name
            | a => panic! s!"Expected ident for type param {repr a}"
        foldOverArgAtLevel m addBinding #[] argDecls args b.typeParamsIndex.toLevel
    some <| .type params.toList none
  | .tvar _ =>
    -- tvar bindings are local only, not added to GlobalContext
    none

/--
Typing environment created from declarations in an environment.
-/
structure GlobalContext where
  nameMap : Std.HashMap Var FreeVarIndex
  vars : Array (Var × GlobalKind × DeclState)
deriving Repr

namespace GlobalContext

instance : EmptyCollection GlobalContext where
  emptyCollection := private { nameMap := {}, vars := {}}

--deriving instance BEq for GlobalContext

instance : Inhabited GlobalContext where
  default := {}

instance : Membership Var GlobalContext where
  mem ctx v := v ∈ ctx.nameMap

@[instance]
def instDecidableMem (v : Var) (ctx : GlobalContext) : Decidable (v ∈ ctx) :=
  inferInstanceAs (Decidable (v ∈ ctx.nameMap))

/-- Add a forward declaration (must not exist). Used by @[declareTypeForward].
    This adds to GlobalContext for name resolution but will NOT generate an AST node. -/
def declareForward (ctx : GlobalContext) (v : Var) (k : GlobalKind) : Except String GlobalContext :=
  if v ∈ ctx then
    .error s!"Symbol '{v}' is already in scope"
  else
    let idx := ctx.vars.size
    .ok { nameMap := ctx.nameMap.insert v idx,
          vars := ctx.vars.push (v, k, .forward) }

/-- Define a symbol. Used by @[declareDatatype], @[declareFn] with body, etc.
    Replaces forward declaration, or adds new as defined. -/
def define (ctx : GlobalContext) (v : Var) (k : GlobalKind) : Except String GlobalContext :=
  match ctx.nameMap.get? v with
  | none =>
    -- Not declared, add as defined directly
    let idx := ctx.vars.size
    .ok { nameMap := ctx.nameMap.insert v idx,
          vars := ctx.vars.push (v, k, .defined) }
  | some idx =>
    let (name, _, state) := ctx.vars[idx]!
    match state with
    | .forward =>
      -- Replace forward declaration with definition (update in place)
      .ok { ctx with vars := ctx.vars.set! idx (name, k, .defined) }
    | .defined =>
      .error s!"Symbol '{v}' is already defined"

/-- Check if a symbol is forward-declared (not yet defined). -/
def isForward (ctx : GlobalContext) (idx : FreeVarIndex) : Bool :=
  match ctx.vars[idx]? with
  | some (_, _, .forward) => true
  | _ => false

/-- Add a symbol as defined. -/
def push (ctx : GlobalContext) (v : Var) (k : GlobalKind) : GlobalContext :=
  match ctx.define v k with
  | .ok ctx' => ctx'
  | .error msg => panic! msg

/-- Return the index of the variable with the given name. -/
def findIndex? (ctx : GlobalContext) (v : Var) : Option FreeVarIndex := ctx.nameMap.get? v

def nameOf? (ctx : GlobalContext) (idx : FreeVarIndex) : Option String := ctx.vars[idx]? |>.map (·.fst)

def kindOf! (ctx : GlobalContext) (idx : FreeVarIndex) : GlobalKind :=
  assert! idx < ctx.vars.size
  ctx.vars[idx]!.2.1

/-!
## Annotation-based Constructor Info Extraction

The following functions implement constructor info extraction using
`@[constructor(name, fields)]` and `@[field(name, tp)]` annotations.

The annotation-based approach:
1. Looks up the operation in the dialect's operation declarations
2. Checks if the operation has the appropriate metadata annotation
3. Uses the indices from the annotation to extract the relevant arguments
-/

/--
Look up an operation's metadata in the dialect.
Returns the OpDecl if found, or none if the operation is not in the dialect.
-/
private def lookupOpDecl (dialects : DialectMap) (opName : QualifiedIdent) : Option OpDecl :=
  match dialects[opName.dialect]? with
  | none => none
  | some dialect => dialect.ops[opName.name]?

/--
Check if an operation has the @[constructor(name, fields)] annotation.
Returns the (nameIndex, fieldsIndex) if present.
-/
private def getConstructorAnnotation (opDecl : OpDecl) : Option (Nat × Nat) :=
  match opDecl.metadata[q`StrataDDL.constructor]? with
  | some #[.catbvar nameIdx, .catbvar fieldsIdx] => some (nameIdx, fieldsIdx)
  | _ => none

/--
Check if an operation has the @[constructorListAtom(c)] annotation.
Returns the constructor index if present.
-/
private def getConstructorListAtomAnnotation (opDecl : OpDecl) : Option Nat :=
  match opDecl.metadata[q`StrataDDL.constructorListAtom]? with
  | some #[.catbvar constrIdx] => some constrIdx
  | _ => none

/--
Check if an operation has the @[constructorListPush(list, c)] annotation.
Returns the (listIndex, constructorIndex) if present.
-/
private def getConstructorListPushAnnotation (opDecl : OpDecl) : Option (Nat × Nat) :=
  match opDecl.metadata[q`StrataDDL.constructorListPush]? with
  | some #[.catbvar listIdx, .catbvar constrIdx] => some (listIdx, constrIdx)
  | _ => none

/--
Extract fields from a Bindings argument using the existing @[declare] annotations.
-/
private def extractFieldsFromBindings (dialects : DialectMap) (arg : Arg) : Array (String × TypeExpr) :=
  let addField (acc : Array (String × TypeExpr)) (_ : SourceRange)
      {argDecls : ArgDecls} (b : BindingSpec argDecls) (args : Vector Arg argDecls.size) : Array (String × TypeExpr) :=
    match b with
    | .value vb =>
      match args[vb.nameIndex.toLevel], args[vb.typeIndex.toLevel] with
      | .ident _ name, .type tp => acc.push (name, tp)
      | _, _ => acc
    | _ => acc
  foldOverArgBindingSpecs dialects addField #[] arg

/--
Extract constructor information using the @[constructor] annotation.
-/
private def extractSingleConstructor (dialects : DialectMap) (arg : Arg) : Option ConstructorInfo :=
  match arg with
  | .op op =>
    match lookupOpDecl dialects op.name with
    | none => none
    | some opDecl =>
      match getConstructorAnnotation opDecl with
      | none => none
      | some (nameIdx, fieldsIdx) =>
        -- Convert deBruijn indices to levels
        let argCount := opDecl.argDecls.size
        if nameIdx < argCount && fieldsIdx < argCount then
          let nameLevel := argCount - nameIdx - 1
          let fieldsLevel := argCount - fieldsIdx - 1
          if h1 : nameLevel < op.args.size then
            if h2 : fieldsLevel < op.args.size then
              match op.args[nameLevel] with
              | .ident _ constrName =>
                -- Extract fields from the Bindings argument using @[declare] annotations
                let fields := match op.args[fieldsLevel] with
                  | .option _ (some bindingsArg) => extractFieldsFromBindings dialects bindingsArg
                  | .option _ none => #[]
                  | other => extractFieldsFromBindings dialects other
                some { name := constrName, fields := fields }
              | _ => none
            else none
          else none
        else none
  | _ => none

/--
This function traverses a constructor list AST node and extracts structured
information about each constructor, including its name and fields using the
dialect annotations `@[constructor]`, `@[constructorListAtom]`,
`@[constructorListPush]`.

**Example:** For `{ None(), Some(value: T) }`, returns:
```
#[
  { name := "None", fields := #[] },
  { name := "Some", fields := #[("value", <TypeExpr for T>)] }
]
```
-/
def extractConstructorInfo (dialects : DialectMap) (arg : Arg) : Array ConstructorInfo :=
  match arg with
  | .op op =>
    match lookupOpDecl dialects op.name with
    | none => #[]
    | some opDecl =>
      match getConstructorListAtomAnnotation opDecl with
      | some constrIdx =>
        let argCount := opDecl.argDecls.size
        if constrIdx < argCount then
          let constrLevel := argCount - constrIdx - 1
          if h : constrLevel < op.args.size then
            match extractSingleConstructor dialects op.args[constrLevel] with
            | some constr => #[constr]
            | none => #[]
          else #[]
        else #[]
      | none =>
        match getConstructorListPushAnnotation opDecl with
        | some (listIdx, constrIdx) =>
          let argCount := opDecl.argDecls.size
          if listIdx < argCount && constrIdx < argCount then
            let listLevel := argCount - listIdx - 1
            let constrLevel := argCount - constrIdx - 1
            if h1 : listLevel < op.args.size then
              if h2 : constrLevel < op.args.size then
                let prevConstrs := extractConstructorInfo dialects op.args[listLevel]
                match extractSingleConstructor dialects op.args[constrLevel] with
                | some constr => prevConstrs.push constr
                | none => prevConstrs
              else #[]
            else #[]
          else #[]
        | none =>
          -- Could be a direct constructor operation
          match extractSingleConstructor dialects arg with
          | some constr => #[constr]
          | none => #[]
  | _ => #[]
  decreasing_by
    simp_wf; rw[OperationF.sizeOf_spec]
    have := Array.sizeOf_get op.args (opDecl.argDecls.size - listIdx - 1) (by omega); omega

/--
Add all bindings for a datatype declaration to the GlobalContext when
`@[declareDatatype]` is encountered. Bindings are 1) the type itself (added as
`GlobalKind.type`) 2) the constructors (e.g. `a → List a → List a` for `Cons`)
3) template-generated functions as specified via `perConstructor` or `perFields`
templates.

The entries are generated in the following order: datatype type, constructors
in declaration order, then template functions in specification order. The
FreeVarIndex values are consistent with this order.

**Parameters:**
- `dialects`: Map of all loaded dialects (needed for annotation lookup)
- `gctx`: Current GlobalContext to extend
- `src`: Source location for generated type expressions
- `dialectName`: Name of the dialect containing the datatype
- `b`: DatatypeBindingSpec with indices for name, type params, constructors, and templates
- `args`: Actual arguments from the parsed operation

**Example:** For `datatype Option<T> { None(), Some(value: T) }` with a tester template,
this adds entries for: `Option` (type), `None` (constructor), `Some` (constructor),
`Option..isNone` (tester), `Option..isSome` (tester).
-/
private def addDatatypeBindings
    (dialects : DialectMap)
    (gctx : GlobalContext)
    (src : SourceRange)
    (dialectName : DialectName)
    {argDecls : ArgDecls}
    (b : DatatypeBindingSpec argDecls)
    (args : Vector Arg argDecls.size)
    : GlobalContext :=

  let datatypeName :=
    match args[b.nameIndex.toLevel] with
    | .ident _ e => e
    | a => panic! s!"Expected ident for datatype name {repr a}"

  let typeParams : Array String :=
    let addBinding (a : Array String) (_ : SourceRange) {argDecls : _} (bs : BindingSpec argDecls) (args : Vector Arg argDecls.size) :=
        match args[bs.nameIndex.toLevel] with
        | .ident _ name => a.push name
        | a => panic! s!"Expected ident for type param {repr a}"
    foldOverArgAtLevel dialects addBinding #[] argDecls args b.typeParamsIndex.toLevel

  let constructorInfo := extractConstructorInfo dialects args[b.constructorsIndex.toLevel]

  -- Step 1: Add datatype type (or update forward declaration)
  let gctx := match gctx.define datatypeName (GlobalKind.type typeParams.toList none) with
    | .ok gctx' => gctx'
    | .error msg => panic! s!"addDatatypeBindings: {msg}"
  let datatypeIndex := gctx.findIndex? datatypeName |>.getD (gctx.vars.size - 1)
  let datatypeType := mkDatatypeTypeRef src datatypeIndex typeParams

  -- Step 2: Add constructor signatures
  let gctx := constructorInfo.foldl (init := gctx) fun gctx constr =>
    let constrType := mkConstructorType src datatypeType constr.fields
    gctx.push constr.name (.expr constrType)

  -- Step 3: Expand and add function templates
  let existingNames : Std.HashSet String := gctx.nameMap.fold (init := {}) fun s name _ => s.insert name
  let result := expandFunctionTemplates datatypeName datatypeType constructorInfo b.functionTemplates dialectName existingNames

  if !result.errors.isEmpty then
    panic! s!"Datatype template expansion errors: {result.errors}"
  else
    result.functions.foldl (init := gctx) fun gctx (funcName, funcType) =>
      gctx.push funcName (.expr funcType)

def addCommand (dialects : DialectMap) (init : GlobalContext) (op : Operation) : GlobalContext :=
    let dialectName := op.name.dialect
    op.foldBindingSpecs dialects (addBinding dialectName) init
  where addBinding (dialectName : DialectName) (gctx : GlobalContext) l {argDecls} (b : BindingSpec argDecls) args :=
          match b with
          | .datatype datatypeSpec =>
            addDatatypeBindings dialects gctx l dialectName datatypeSpec args
          | .typeForward typeSpec =>
            let name :=
                  match args[typeSpec.nameIndex.toLevel] with
                  | .ident _ e => e
                  | a => panic! s!"Expected ident at {typeSpec.nameIndex.toLevel} {repr a}"
            match resolveBindingIndices dialects l b args with
            | some kind =>
              match gctx.declareForward name kind with
              | .ok gctx' => gctx'
              | .error msg => panic! msg
            | none => gctx
          | _ =>
            let name :=
                  match args[b.nameIndex.toLevel] with
                  | .ident _ e => e
                  | a => panic! s!"Expected ident at {b.nameIndex.toLevel} {repr a}"
            match resolveBindingIndices dialects l b args with
            | some kind => gctx.push name kind
            | none => gctx

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
  default := private { dialects := .empty, dialect := default }

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
end

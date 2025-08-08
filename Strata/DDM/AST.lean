/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Std.Data.HashMap
import Strata.DDM.Util.Array
import Strata.DDM.Util.Decimal

namespace Strata

abbrev DialectName := String

structure QualifiedIdent where
  dialect : DialectName
  name : String
  deriving Hashable, Inhabited, DecidableEq, Repr

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
  | `(q`$l:ident ) =>
    if let .str (.str .anonymous d) suf := l.getId then
      pure (quote (QualifiedIdent.mk d suf) : Term)
    else
      throw (.error l.raw "Quoted identifiers must contain two components")
  | _ => Macro.throwUnsupported

end

end QualifiedIdent

/--
info: { dialect := "A", name := "C" }
-/
#guard_msgs in
#eval q`A.C

/-- This refers to a value introduced in the program. -/
abbrev FreeVarIndex := Nat

/-- An expression that denotes a type. -/
inductive TypeExpr where
  /-- A dialect defined type. -/
| ident (name : QualifiedIdent) (args : Array TypeExpr)
  /-- A bound type variable at the given deBruijn index in the context. -/
| bvar (index : Nat)
  /-- A reference to a global variable along with any arguments to ensure it is well-typed. -/
| fvar (fvar : FreeVarIndex) (args : Array TypeExpr)
  /-- A function type. -/
| arrow (arg : TypeExpr) (res : TypeExpr)
deriving BEq, Inhabited, Repr

namespace TypeExpr

def mkFunType (bindings : Array (String × TypeExpr)) (res : TypeExpr) : TypeExpr :=
  bindings.foldr (init := res) fun (_, argType) tp => .arrow argType tp
protected def incIndices (tp : TypeExpr) (count : Nat) : TypeExpr :=
  match tp with
  | .ident i args => .ident i (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .fvar f args => .fvar f (args.attach.map fun ⟨e, _⟩ => e.incIndices count)
  | .bvar idx => .bvar (idx + count)
  | .arrow a r => .arrow (a.incIndices count) (r.incIndices count)

/-- Return true if type expression has a bound variable. -/
protected def hasUnboundVar (bindingCount : Nat := 0) : TypeExpr → Bool
| .ident _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .fvar _ args => args.attach.any (fun ⟨e, _⟩ => e.hasUnboundVar bindingCount)
| .bvar idx => idx ≥ bindingCount
| .arrow a r => a.hasUnboundVar bindingCount || r.hasUnboundVar bindingCount
termination_by e => e

/-- Return true if type expression has no free variables. -/
protected def isGround (tp : TypeExpr) := !tp.hasUnboundVar

/-
This applies global context to instantiate types and variables.

Free type alias variables bound to alias
-/
protected def instType (d : TypeExpr) (bindings : Array TypeExpr) : TypeExpr :=
  match d with
  | .ident i a =>
    .ident i (a.attach.map (fun ⟨e, _⟩ => e.instType bindings))
  | .bvar idx =>
    assert! idx < bindings.size
    bindings[bindings.size - (idx+1)]!
  | .fvar idx a => .fvar idx (a.attach.map (fun ⟨e, _⟩ => e.instType bindings))
  | .arrow a b => .arrow (a.instType bindings) (b.instType bindings)
termination_by d

/-
This applies global context to instantiate types and variables.

Free type alias variables bound to alias
-/
protected def instTypeM [Monad m] (d : TypeExpr) (bindings : Nat → m TypeExpr) : m TypeExpr :=
  match d with
  | .ident i a =>
    .ident i <$> a.attach.mapM (fun ⟨e, _⟩ => e.instTypeM bindings)
  | .bvar idx => bindings idx
  | .fvar idx a => .fvar idx <$> a.attach.mapM (fun ⟨e, _⟩ => e.instTypeM bindings)
  | .arrow a b => .arrow <$> a.instTypeM bindings <*> b.instTypeM bindings
termination_by d

end TypeExpr

inductive SyntaxCat where
| atom (ident : QualifiedIdent)
| app (h : SyntaxCat) (a : SyntaxCat)
deriving Inhabited, Repr, DecidableEq

namespace SyntaxCat

protected def head : SyntaxCat → QualifiedIdent
| .atom i => i
| .app h _ => h.head

protected def args : SyntaxCat → Array SyntaxCat
| .atom _ => #[]
| .app h a => h.args |>.push a

end SyntaxCat


mutual

inductive Expr where
| bvar (idx : Nat)
| fvar (idx : FreeVarIndex)
| fn (ident : QualifiedIdent)
| app (e : Expr) (a : Arg)
deriving Inhabited, Repr

structure Operation where
  name : QualifiedIdent
  args : Array Arg
deriving Inhabited, Repr

inductive Arg where
| op (o : Operation)
| cat (c : SyntaxCat)
| expr (e : Expr)
| type (e : TypeExpr)
| ident (i : String)
| num (v : Nat)
| decimal (v : Decimal)
| strlit (i : String)
| option (l : Option Arg)
| seq (l : Array Arg)
| commaSepList (l : Array Arg)
deriving Inhabited, Repr

end

namespace Operation

def sizeOf_spec (op : Operation) : sizeOf op = 1 + sizeOf op.name + sizeOf op.args :=
  match op with
  | { name, args } => by simp

end Operation

/--
Array ofelements whose sizes are bounded by a value.
-/
abbrev SizeBounded (α : Type _) [SizeOf α] {β} [SizeOf β] (e : β) (c : Int) := { a : α // sizeOf a ≤ sizeOf e + c }

namespace Expr

/--
Head-normal form for an expression consists of an operation
-/
structure HNF (e : Expr) where
  fn : Expr
  args : SizeBounded (Array Arg) e 1

protected def hnf (e0 : Expr) : HNF e0 :=
  let rec aux (e : Expr) (args : Array Arg := #[])
              (szP : sizeOf e + sizeOf args = sizeOf e0 + 2): HNF e0 :=
    match e with
    | .bvar _ | .fvar _ | .fn _ => { fn := e, args := ⟨args.reverse, by simp at szP; simp ; omega⟩ }
    | .app f a => aux f (args.push a) (by simp at *; omega)
  aux e0 #[] (by simp)

partial def flatten (e : Expr) (prev : List Arg := []) : Expr × List Arg :=
  match e with
  | .app f e => f.flatten (e :: prev)
  | _ => (e, prev)

end Expr

namespace Arg

def asOp! : Arg → Operation
| .op a => a
| a => panic! s!"{repr a} is not an operation."

def asCat! : Arg → SyntaxCat
| .cat a => a
| a => panic! s!"{repr a} is not a syntax category."

def asExpr! : Arg → Expr
| .expr a => a
| a => panic! s!"{repr a} is not an expression."

def asType! : Arg → TypeExpr
| .type a => a
| a => panic! s!"{repr a} is not a type."

def asIdent! : Arg → String
| .ident a => a
| a => panic! s!"{repr a} is not an identifier."

def asOption! : Arg → Option Arg
| .option a => a
| a => panic! s!"{repr a} is not an option."

def asSeq! : Arg → Array Arg
| .seq a => a
| a => panic! s!"{repr a} is not an sequence."

def asCommaSepList : Arg → Array Arg
| .commaSepList a => a
| a => panic! s!"{repr a} is not an comma separated list."

end Arg

inductive MetadataArg where
| catbvar (index : Nat) -- This is a deBrujin index into current typing environment.
| bool (e : Bool)
| num (e : Nat)
| option (a : Option MetadataArg)
deriving Inhabited, Repr, BEq

structure MetadataAttr where
  ident : QualifiedIdent
  args : Array MetadataArg
deriving Inhabited, Repr, BEq

namespace MetadataAttr

def scopeName := q`StrataDDL.scope

/-- Create scope using deBrujin index of environment. -/
def scope (idx : Nat) : MetadataAttr :=
  { ident := scopeName, args := #[.catbvar idx ] }

def declare (varIndex typeIndex : Nat) : MetadataAttr :=
  { ident := q`StrataDDL.declare, args := #[.catbvar varIndex, .catbvar typeIndex]}

def declareFn (varIndex bindingsIndex typeIndex : Nat) : MetadataAttr :=
  { ident := q`StrataDDL.declareFn, args := #[.catbvar varIndex, .catbvar bindingsIndex, .catbvar typeIndex]}

def declareMD (varIndex typeIndex metadataIndex : Nat) : MetadataAttr :=
  { ident := q`StrataDDL.declareMD, args := #[.catbvar varIndex, .catbvar typeIndex, .catbvar metadataIndex]}

end MetadataAttr

structure Metadata where
  ofArray ::
  toArray : Array MetadataAttr
deriving Repr, BEq

namespace Metadata

protected def empty : Metadata := { toArray := #[] }

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
| ident (name : QualifiedIdent) (args : Array PreType)
  /-- A bound type variable at the given deBruijn index in the context. -/
| bvar (index : Nat)
  /-- A reference to a global variable along with any arguments to ensure it is well-typed. -/
| fvar (fvar : FreeVarIndex) (args : Array PreType)
  /-- A function type. -/
| arrow (arg : PreType) (res : PreType)
  /-- A function created from a reference to bindings and a result type. -/
| funMacro (bindingsIndex : Nat) (res : PreType)
deriving BEq, Inhabited, Repr

def maxPrec := eval_prec max

/--
This describes how to format an operator.
-/
inductive SyntaxDefAtom
-- Format the argument with the given name.
-- Surround with parenthesis if the precedence of the argument is less than `prec`.
-- Note. If `prec` is zero, then parenthesis will never be added (even with pp.parens is true).
-- This is to avoid parens in categories that do not support them.
| ident (level : Nat) (prec : Nat)
| str (lit : String)
| indent (n : Nat) (args : Array SyntaxDefAtom)
deriving Inhabited, Repr, BEq

structure SyntaxDef where
  atoms : Array SyntaxDefAtom
  prec : Nat
deriving Repr, Inhabited, BEq

def SyntaxDef.ofList (atoms : List SyntaxDefAtom) (prec : Nat := maxPrec): SyntaxDef where
  atoms := atoms.toArray
  prec := prec

/-- Structure that defines a binding introduced by an operation or function. -/
inductive SyntaxElabType
| type : PreType → SyntaxElabType
deriving Repr

structure DebruijnIndex (n : Nat) where
  val : Nat
  isLt : val < n
  deriving Repr

namespace DebruijnIndex

def toLevel : DebruijnIndex n → Fin n
| ⟨v, lt⟩ => ⟨n - (v+1), by omega⟩

end DebruijnIndex

private def varNameByIndex {n} (args : Vector Arg n) (idx : DebruijnIndex n) : String :=
  match args[idx.toLevel] with
  | .ident e => e
  | a => panic! s!"Expected ident at {idx.val} {repr a}"

inductive DeclBindingKind where
/-- Variable is an expression with the given type. -/
| expr (tp : PreType)
/-- Variable belongs to the particular category -/
| cat (k : SyntaxCat)
deriving BEq, Inhabited, Repr

namespace DeclBindingKind

def categoryOf : DeclBindingKind → SyntaxCat
| .expr _ => .atom q`Init.Expr
| .cat c => c

end DeclBindingKind

/--
A single binder may declare multiple identifiers, but they
all have the same type and metadata.
-/
structure DeclBinding where
  ident : Var
  kind : DeclBindingKind
  metadata : Metadata := .empty
deriving Inhabited, Repr, BEq

abbrev DeclBindings := Array DeclBinding

/--
Indices for introducing a new expression or operation.
-/
structure ValueBindingSpec (bindings : DeclBindings) where
  -- deBrujin level of variable name.
  nameIndex : DebruijnIndex bindings.size
  -- deBrujin index of arguments if this is declaring a function (or none) if this declares a constant.
  argsIndex : Option (DebruijnIndex bindings.size)
  -- deBrujin index of type or a type/cat literal.
  typeIndex : DebruijnIndex bindings.size
  -- deBrujin index of metadata
  metadataIndex : Option (DebruijnIndex bindings.size)
  -- Whether categories are allowed
  allowCat : Bool
deriving Repr

/--
Indices for introducing a new type binding.
-/
structure TypeBindingSpec (bindings : DeclBindings) where
  nameIndex : DebruijnIndex bindings.size
  argsIndex : Option (DebruijnIndex bindings.size)
  defIndex : Option (DebruijnIndex bindings.size)
deriving Repr

/-
A spec for introducing a new binding into a type context.
-/
inductive BindingSpec (bindings : DeclBindings) where
| value (_ : ValueBindingSpec bindings)
| type (_ : TypeBindingSpec bindings)
deriving Repr

namespace BindingSpec

def nameIndex : BindingSpec bindings → DebruijnIndex bindings.size
| .value v => v.nameIndex
| .type v => v.nameIndex

def varName (b : BindingSpec bindings) (args : Vector Arg bindings.size) : String :=
  varNameByIndex args b.nameIndex

end BindingSpec

abbrev NewBindingM := StateM (Array String)

private def newBindingErr (msg : String) : NewBindingM Unit :=
  modify (·.push msg)

private def checkNameIndexIsIdent (bindings : DeclBindings) (nameIndex : DebruijnIndex bindings.size) : NewBindingM Unit :=
  let b := bindings[nameIndex.toLevel]
  match b.kind with
  | .cat (.atom q`Init.Ident) =>
    pure ()
  | _ =>
    newBindingErr s!"Expected {b.ident} to be an Ident."

private def mkValueBindingSpec
            (bindings : DeclBindings)
            (nameIndex : DebruijnIndex bindings.size)
            (typeIndex : DebruijnIndex bindings.size)
            (argsIndex : Option (DebruijnIndex bindings.size) := none)
            (metadataIndex : Option (DebruijnIndex bindings.size) := none)
            : NewBindingM (ValueBindingSpec bindings) := do
  checkNameIndexIsIdent bindings nameIndex
  let typeBinding := bindings[typeIndex.toLevel]
  let allowCat ←
        match typeBinding.kind with
        | .cat (.atom q`Init.Type) =>
          pure false
        | .cat (.atom q`Init.TypeP) =>
          pure true
        | _ =>
          newBindingErr "Expected reference to type variable."
          pure default
  if allowCat && argsIndex.isSome then
    newBindingErr "Arguments only allowed when result is a type."
  return { nameIndex, argsIndex, typeIndex, metadataIndex, allowCat }

def parseNewBindings (md : Metadata) (bindings : DeclBindings) : Array (BindingSpec bindings) × Array String :=
  let ins (attr : MetadataAttr) : NewBindingM (Option (BindingSpec bindings)) := do
        match attr.ident with
        | q`StrataDDL.declare => do
          let #[.catbvar nameIndex, .catbvar typeIndex] := attr.args
            | newBindingErr "declare does not have expected 2 arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < bindings.size))
            | return panic! "Invalid name index"
          let .isTrue typeP := inferInstanceAs (Decidable (typeIndex < bindings.size))
            | return panic! "Invalid name index"
          some <$> .value <$> mkValueBindingSpec bindings ⟨nameIndex, nameP⟩ ⟨typeIndex, typeP⟩
        | q`StrataDDL.declareMD => do
          let #[.catbvar nameIndex, .catbvar typeIndex, .catbvar metadataIndex ] := attr.args
            | newBindingErr "declareMD missing required arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < bindings.size))
            | return panic! "Invalid name index"
          let .isTrue typeP := inferInstanceAs (Decidable (typeIndex < bindings.size))
            | return panic! "Invalid name index"
          let .isTrue mdP := inferInstanceAs (Decidable (metadataIndex < bindings.size))
            | return panic! "Invalid metadata index"
          some <$> .value <$> mkValueBindingSpec bindings ⟨nameIndex, nameP⟩ ⟨typeIndex, typeP⟩ (metadataIndex := .some ⟨metadataIndex, mdP⟩)
        | q`StrataDDL.declareFn => do
          let #[.catbvar nameIndex, .catbvar argsIndex, .catbvar typeIndex] := attr.args
            | newBindingErr "declareFn missing required arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < bindings.size))
            | return panic! "Invalid name index"
          let .isTrue argsP := inferInstanceAs (Decidable (argsIndex < bindings.size))
            | return panic! "Invalid arg index"
          let .isTrue typeP := inferInstanceAs (Decidable (typeIndex < bindings.size))
            | return panic! "Invalid name index"
          some <$> .value <$> mkValueBindingSpec bindings ⟨nameIndex, nameP⟩ ⟨typeIndex, typeP⟩ (argsIndex := some ⟨argsIndex, argsP⟩)
        | q`StrataDDL.declareType => do
          let #[.catbvar nameIndex, .option mArgsArg ] := attr.args
            | newBindingErr s!"declareType has bad arguments {repr attr.args}."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < bindings.size))
            | return panic! "Invalid name index"
          let nameIndex := ⟨nameIndex, nameP⟩
          checkNameIndexIsIdent bindings nameIndex
          let argsIndex ←
                match mArgsArg with
                | none => pure none
                | some (.catbvar idx) =>
                  let .isTrue argsP := inferInstanceAs (Decidable (idx < bindings.size))
                    | return panic! "Invalid arg index"
                  pure <| some ⟨idx, argsP⟩
                | _ => newBindingErr "declareType args invalid."; return none
          some <$> .type <$> pure { nameIndex, argsIndex, defIndex := none }
        | q`StrataDDL.aliasType => do
          let #[.catbvar nameIndex, .option mArgsArg, .catbvar defIndex] := attr.args
            | newBindingErr "aliasType missing arguments."; return none
          let .isTrue nameP := inferInstanceAs (Decidable (nameIndex < bindings.size))
            | return panic! "Invalid name index"
          let nameIndex := ⟨nameIndex, nameP⟩
          checkNameIndexIsIdent bindings nameIndex
          let argsIndex ←
                match mArgsArg with
                | none => pure none
                | some (.catbvar idx) =>
                  let .isTrue argsP := inferInstanceAs (Decidable (idx < bindings.size))
                    | return panic! "Invalid arg index"
                  pure <| some ⟨idx, argsP⟩
                | _ => newBindingErr "aliasType args invalid."; return none
          let .isTrue defP := inferInstanceAs (Decidable (defIndex < bindings.size))
            | return panic! "Invalid def index"
          let defBinding := bindings[bindings.size - (defIndex+1)]
          match defBinding.kind with
          | .cat (.atom q`Init.Type) =>
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

def parseNewBindings! (md : Metadata) (bindings : DeclBindings) : Array (BindingSpec bindings) :=
  let (r, errs) := parseNewBindings md bindings
  if let some msg := errs[0]? then
    panic! msg
  else
    r

structure SynCatDecl where
  name : String
  argNames : Array String := #[]
deriving Repr, DecidableEq, Inhabited

/--
A declaration of an algebraic data type.
-/
structure TypeDecl where
  name : String
  argNames : Array String
deriving Repr, DecidableEq, Inhabited

/-- Operator declaration -/
structure OpDecl where
  /-- Name of operator -/
  name : String
  /-- Arguments to operator. -/
  argDecls : DeclBindings
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
  (argDecls : DeclBindings)
  (category : QualifiedIdent)
  (syntaxDef : SyntaxDef)
  (metadata : Metadata) : OpDecl :=
  { name, argDecls, category, syntaxDef, metadata }

end OpDecl

abbrev FnName := String

structure FunctionDecl where
  name : FnName
  argDecls : DeclBindings
  result : PreType
  syntaxDef : SyntaxDef
  metadata : Metadata := .empty
deriving Inhabited, Repr, BEq

inductive MetadataArgType
| num
| ident
| bool
| opt (tp : MetadataArgType)
deriving Repr, DecidableEq, Inhabited

structure MetadataArgDecl where
  ident : String
  type : MetadataArgType
deriving Repr, Inhabited, DecidableEq

/--
Declaration of a metadata tag in a dialect.

Metadata has an optional argument that must have
the specified type.

N.B. We may want to further resitrct where metadata can appear.
-/
structure MetadataDecl where
  name : String
  args : Array MetadataArgDecl
deriving Repr, Inhabited, DecidableEq

inductive Decl where
| syncat (d : SynCatDecl)
| op (d : OpDecl)
| type (d : TypeDecl)
| function (d : FunctionDecl)
| metadata (d : MetadataDecl)
deriving Repr, BEq, Inhabited

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

instance : ForIn m (Collection α) α where
  forIn c i f := do
    let step d _h r :=
          match c.proj d with
          | .some v => f v r
          | .none => pure (.yield r)
    c.declarations.forIn' i step

protected def fold (f : β → α → β) (init : β) (c : Collection α) : β :=
  let proj := c.proj
  let step b d :=
        match proj d with
        | some v => f b v
        | none => b
  c.declarations.foldl step init

instance : ToString (Collection α) where
  toString c :=
    let step i a :=
          let r := if i.fst then i.snd else i.snd ++ ", "
          (false, r ++ c.pretty a)
    (c.fold step (true, "{") |>.snd) ++ "}"

inductive Mem (c : Collection α) (nm : String) : Prop
| intro : (h : nm ∈ c.cache) → (r : α) → c.proj (c.cache[nm]) = some r → Mem c nm

def Mem.inCache : Mem c nm → nm ∈ c.cache
| .intro h _ _ => h

instance : Membership String (Collection α) where
  mem := Mem

instance (nm : String) (c : Collection α) : Decidable (nm ∈ c) :=
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

instance : GetElem? (Collection α) String α (fun c nm => nm ∈ c) where
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
  imports : Array DialectName := #[]
  declarations : Array Decl := #[]
  cache : Std.HashMap String Decl := {}
deriving Inhabited

namespace Dialect

instance : BEq Dialect where
  beq x y := x.name = y.name && x.imports = y.imports && x.declarations == y.declarations

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

def declareType (d : Dialect) (name : String) (argNames : Array String) :=
  d.addDecl (.type { name, argNames })

def declareMetadata (d : Dialect) (decl : MetadataDecl) : Dialect :=
  d.addDecl (.metadata decl)

instance : Membership String Dialect where
  mem d nm := nm ∈ d.cache

instance (nm : String) (d : Dialect) : Decidable (nm ∈ d) :=
  inferInstanceAs (Decidable (nm ∈ d.cache))

end Dialect

namespace DeclBindings

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
def argScopeLevel (bindings : DeclBindings) (level : Fin bindings.size) : Option (Fin level.val) :=
  match bindings[level].metadata.scopeIndex with
  | none => none
  | some idx =>
    if h : idx < level.val then
      some ⟨level.val - (idx + 1), by omega⟩
    else
      -- TODO: Validate this is checked when attribute parsing occurs.
      let varCount := bindings.size
      panic! s!"Scope index {idx} out of bounds ({level.val}, varCount = {varCount})"

end DeclBindings

/-- Returns the index of the value in the binding for the given variable of the scope to use. -/
def Metadata.resultLevel (varCount : Nat) (metadata : Metadata) : Option (Fin varCount) :=
  match metadata.resultIndex with
  | none => none
  | some idx =>
    if _ : idx < varCount then
      some ⟨varCount - (idx + 1), by omega⟩
    else
      panic! s!"Scope index {idx} out of bounds (varCount = {varCount})"

structure DialectMap where
  map : Std.HashMap DialectName Dialect
  deriving Inhabited

namespace DialectMap

instance : EmptyCollection DialectMap where
  emptyCollection := .mk {}

instance : Membership DialectName DialectMap where
  mem m d := d ∈ m.map

instance (d : DialectName) (m : DialectMap) : Decidable (d ∈ m) :=
  inferInstanceAs (Decidable (d ∈ m.map))

instance : GetElem? DialectMap DialectName Dialect (fun m d => d ∈ m) where
  getElem m d p := m.map[d]
  getElem? m d := m.map[d]?
  getElem! m d := m.map[d]!

/--
This inserts a dialect in to the dialect map.

It panics if a dialect with the same name is already in the map
or if the dialect imports a dialect not already in the map.
-/
def insert! (m : DialectMap) (d : Dialect) : DialectMap :=
  assert! d.name ∉ m
  assert! d.imports.all (· ∈ m)
  { map := m.map.insert d.name d }

def ofList! (l : List Dialect) : DialectMap :=
  let m := l.foldl (init := {}) fun m d =>
    assert! d.name ∉ m;
    m.insert d.name d
  assert! l.all fun d => d.imports.all (· ∈ m)
  { map := m }

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

end DialectMap

mutual

/--
Invoke a function `f` over each of the binding specifications for an arg
so that a result type context can be constructed.
-/
partial def foldArgBindingSpecs
    (m : DialectMap)
    (f : α → ∀(bindings : DeclBindings), BindingSpec bindings → Vector Arg bindings.size → α)
    (init : α)
    (a : Arg)
    : α :=
  match a with
  | .op op => foldOverOpBindings m f init op
  | .expr _ | .type _ | .cat _ | .ident _ | .num _ | .decimal _ | .strlit _ => init
  | .option none => init
  | .option (some a) => foldArgBindingSpecs m f init a
  | .seq a => a.attach.foldl (init := init) (fun init ⟨a, _⟩ => foldArgBindingSpecs m f init a)
  | .commaSepList a => a.attach.foldl (init := init) (fun init ⟨a, _⟩ => foldArgBindingSpecs m f init a)

/--
Invoke a function `f` over each of the binding specifications for an operator
so that a result type context can be constructed.
-/
partial def foldOverOpBindings
    (m : DialectMap)
    (f : α → ∀(bindings : DeclBindings), BindingSpec bindings → Vector Arg bindings.size → α)
    (init : α)
    (op : Operation)
    : α :=
  let decl := m.opDecl! op.name
  let bindings := decl.argDecls
  let args := op.args
  if h : args.size = bindings.size then
    let argsV : Vector Arg bindings.size := ⟨args, h⟩
    let init :=
      match decl.metadata.resultLevel bindings.size with
      | none => init
      | some lvl => foldOverArgAtLevel m f init bindings argsV lvl
    decl.newBindings.foldl (init := init) (fun a b => f a bindings b ⟨args, by omega⟩)
  else
    @panic _ ⟨init⟩ "Expected arguments to match bindings"

/--
Invoke a function `f` over a given argument for a function or operation so that
the result context for that argument can be constructed.
-/
partial def foldOverArgAtLevel
    (m : DialectMap)
    (f : α → ∀(bindings : DeclBindings), BindingSpec bindings → Vector Arg bindings.size → α)
    (init : α)
    (bindings : DeclBindings)
    (args : Vector Arg bindings.size)
    (level : Fin bindings.size)
    : α :=
  let init :=
        match bindings.argScopeLevel level with
        | none => init
        | some lvl => foldOverArgAtLevel m f init bindings args ⟨lvl, by omega⟩
  foldArgBindingSpecs m f init args[level]

end

inductive GlobalKind where
| expr (tp : TypeExpr)
| type (params : List String) (definition : Option TypeExpr)
deriving Inhabited, Repr

mutual

/-- Resolves binding spec for a new value to its type. -/
partial def resolveBindingType (m : DialectMap) (b : BindingSpec bindings) (argsV : Vector Arg bindings.size) : TypeExpr :=
  match resolveBindingIndices m b argsV with
  | .expr tp => tp
  | .type _ _ => panic! s!"Expecbted binding to be expression."

/-- Resolves a binding spec into a global kind. -/
partial def resolveBindingIndices (m : DialectMap) (b : BindingSpec bindings) (argsV : Vector Arg bindings.size) : GlobalKind :=
  match b with
  | .value b =>
    let fnBindings : Array (String × TypeExpr) :=
      match b.argsIndex with
      | none =>
        #[]
      | some idx =>
        let f (a : Array _) (bindings : DeclBindings) (b : BindingSpec bindings) argsV :=
              let name := varNameByIndex argsV b.nameIndex
              let type := resolveBindingType m b argsV
              a.push (name, type)
        foldOverArgAtLevel m f #[] bindings argsV idx.toLevel
    match argsV[b.typeIndex.toLevel] with
      | .type tp => .expr (.mkFunType fnBindings tp)
      | .cat (.atom q`Init.Type) => .type [] none
      | a => panic! s!"Expected new binding to be bound to type instead of {repr a}."
  | .type b =>
    let params : Array String :=
        match b.argsIndex with
        | none => #[]
        | some idx =>
          let addBinding (a : Array String) (bindings : _) (b : BindingSpec bindings) (argsV : Vector Arg bindings.size) :=
              a.push (varNameByIndex argsV b.nameIndex)
          foldOverArgAtLevel m addBinding #[] bindings argsV idx.toLevel
    let value :=
            match b.defIndex with
            | none => none
            | some idx =>
              match argsV[idx.toLevel] with
              | .type tp =>
                some tp
              | _ => panic! "Bad arg"
    .type params.toList value

end

/--
Typing environment created from declarations in an environment.
-/
structure GlobalContext where
  nameMap : Std.HashMap Var FreeVarIndex := {}
  vars : Array (Var × GlobalKind) := #[]
deriving Repr

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
    foldOverOpBindings dialects addBinding init op
  where addBinding gctx _ b args :=
          let name := varNameByIndex args b.nameIndex
          let kind := resolveBindingIndices dialects b args
          gctx.push name kind

end GlobalContext

structure Environment where
  mk ::
  -- Map from dialect names to the dialect definition
  dialects : DialectMap := {}
  -- Dialects considered open for pretty-printing purposes.
  openDialects : Array DialectName := #["Init"]
  -- Top level commands in file.
  commands : Array Operation := #[]
  -- Operations at the top command level.
  globalContext : GlobalContext

namespace Environment

def empty : Environment := {
  globalContext := {}
}

instance : Inhabited Environment where
  default := .empty

def addCommand (env : Environment) (cmd : Operation) : Environment :=
  { env with
    commands := env.commands.push cmd,
    globalContext := env.globalContext.addCommand env.dialects cmd
  }

def create (dialects : DialectMap) (openDialects : Array DialectName) (commands : Array Operation) : Environment :=
  { dialects,
    openDialects,
    commands := commands,
    globalContext := commands.foldl (init := {}) (·.addCommand dialects ·)
  }

def openDialect (env : Environment) (d : DialectName) : Environment :=
  if d ∈ env.openDialects then
    env
  else
    { env with openDialects := env.openDialects.push d }

end Environment

theorem sizeOf_lt_of_op_arg {e : Arg} {op : Operation} (p : e ∈ op.args) : sizeOf e < sizeOf op := by
  cases op with
  | mk name args =>
  have q : sizeOf e < sizeOf args := by decreasing_tactic
  decreasing_tactic

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

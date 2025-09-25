/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Elab.Term
import Strata.DDM.AST

namespace Strata

open Lean

namespace QualifiedIdent

instance : ToExpr QualifiedIdent where
  toTypeExpr := mkConst ``QualifiedIdent
  toExpr i := mkApp2 (mkConst ``QualifiedIdent.mk) (toExpr i.dialect) (toExpr i.name)

end QualifiedIdent

section

open Lean.Elab

private def rootIdent (name : Name) : Ident :=
  .mk (.ident .none name.toString.toSubstring name [.decl name []])

private def emptyLevel : Lean.Expr := mkApp (mkConst ``List.nil [.zero]) (mkConst ``Level)

/--
Lift a DDM AST constructor that takes a polymorphic annotation value to
the expression level with the correct number of arguments.

For example, `astExpr! ArgF.ident ann` returns a function that expects one
Lean expression and returns another.
-/
syntax:max (name := astExprElab) "astExpr!" ident term:max : term

@[term_elab astExprElab]
def astExprElabImpl : Term.TermElab := fun stx _expectedType => do
  match stx with
  | `(astExpr! $ident $ann) => do
    let ctor ← realizeGlobalConstNoOverloadWithInfo ident
    let cv ← getConstVal ctor
    let argc := cv.type.getForallBinderNames.length
    assert! argc ≥ 3 ∧ argc ≤ 10
    let ann ← Term.elabTerm ann none
    let annType ← Meta.inferType ann
    let annTypeInst ← Meta.synthInstance (mkApp (mkConst ``ToExpr [.zero]) annType)
    let .sort (.succ .zero) ←  Meta.inferType annType
      | throwError m!"Annotation must have type Type."
    let mkAppName : Name := `Lean |>.str s!"mkApp{argc}"
    let ctorExpr := mkApp2 (mkConst ``mkConst) (toExpr ctor) emptyLevel
    let annTypeExpr := mkApp2 (mkConst ``toTypeExpr [.zero]) annType annTypeInst
    let annExpr := mkApp3 (mkConst ``toExpr [.zero]) annType annTypeInst ann
    return mkApp3 (mkConst mkAppName) ctorExpr annTypeExpr annExpr
  | _ => do
    throwUnsupportedSyntax

end

namespace SyntaxCatF

protected def typeExpr (α : Type) [ToExpr α] := mkApp (mkConst ``SyntaxCatF) (toTypeExpr α)

protected def toExpr {α} [ToExpr α] (cat : SyntaxCatF α) : Lean.Expr :=
  let args := arrayToExpr (SyntaxCatF.typeExpr α) (cat.args.map fun e => e.toExpr)
  astExpr! SyntaxCatF.mk cat.ann (toExpr cat.name) args
decreasing_by
  simp [SyntaxCatF.sizeOf_spec cat]
  decreasing_tactic

instance {α} [ToExpr α] : ToExpr (SyntaxCatF α) where
  toTypeExpr := SyntaxCatF.typeExpr α
  toExpr := SyntaxCatF.toExpr

end SyntaxCatF

namespace TypeExprF

protected def typeExpr (ann : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``TypeExprF) ann

protected def toExpr {α} [ToExpr α] : TypeExprF α → Lean.Expr
| .ident ann nm a =>
  let ae := arrayToExpr (TypeExprF.typeExpr (toTypeExpr α)) (a.map (·.toExpr))
  astExpr! ident ann (toExpr nm) ae
| .bvar ann idx =>
  astExpr! bvar ann (toExpr idx)
| .fvar ann idx a =>
  let ae := arrayToExpr (TypeExprF.typeExpr (toTypeExpr α)) (a.map (·.toExpr))
  astExpr! fvar ann (toExpr idx) ae
| .arrow ann a r =>
  astExpr! arrow ann a.toExpr r.toExpr

instance {α} [ToExpr α] : ToExpr (TypeExprF α) where
  toTypeExpr := TypeExprF.typeExpr (toTypeExpr α)
  toExpr := TypeExprF.toExpr

end TypeExprF

protected def ExprF.typeExpr := mkApp (mkConst ``ExprF)

protected def ArgF.typeExpr (α : Type) [ToExpr α] := mkApp (mkConst ``ArgF) (toTypeExpr α)

protected def OperationF.typeExpr := mkApp (mkConst ``OperationF)

mutual

protected def ExprF.toExpr {α} [ToExpr α] : ExprF α → Lean.Expr
| .bvar ann i => astExpr! ExprF.bvar ann (toExpr i)
| .fvar ann idx => astExpr! ExprF.fvar ann (toExpr idx)
| .fn ann ident => astExpr! ExprF.fn ann (toExpr ident)
| .app ann f a => astExpr! ExprF.app ann f.toExpr a.toExpr
termination_by e => sizeOf e

def ArgF.toExpr {α} [ToExpr α] : ArgF α → Lean.Expr
| .op o =>
  mkApp2 (mkConst ``ArgF.op) (toTypeExpr α) o.toExpr
| .expr e =>
  mkApp2 (mkConst ``ArgF.expr) (toTypeExpr α) (e.toExpr)
| .type e =>
  mkApp2 (mkConst ``ArgF.type) (toTypeExpr α) (toExpr e)
| .cat e =>
  mkApp2 (mkConst ``ArgF.cat) (toTypeExpr α) (toExpr e)
| .ident ann e =>
  astExpr! ArgF.ident ann (toExpr e)
| .num ann e =>
  astExpr! ArgF.num ann (toExpr e)
| .decimal ann e =>
  astExpr! ArgF.decimal ann (toExpr e)
| .strlit ann e =>
  astExpr! ArgF.strlit ann (toExpr e)
| .option ann a =>
  let tpe := ArgF.typeExpr α
  astExpr! ArgF.option ann (optionToExpr tpe <| a.attach.map fun ⟨e, _⟩ => e.toExpr)
| .seq ann a =>
  let tpe := ArgF.typeExpr α
  astExpr! ArgF.seq ann <| arrayToExpr tpe <| a.map (·.toExpr)
| .commaSepList ann a =>
  let tpe := ArgF.typeExpr α
  astExpr! ArgF.commaSepList ann <| arrayToExpr tpe <| a.map (·.toExpr)
termination_by a => sizeOf a

protected def OperationF.toExpr {α} [ToExpr α] (op : OperationF α) : Lean.Expr :=
  let args := arrayToExpr (ArgF.typeExpr α) (op.args.map fun e => e.toExpr)
  astExpr! OperationF.mk op.ann (toExpr op.name) args
termination_by sizeOf op
decreasing_by
  · simp [OperationF.sizeOf_spec]
    decreasing_tactic

end

instance ExprF.instToExpr {α} [ToExpr α] : ToExpr (ExprF α) where
  toTypeExpr := ExprF.typeExpr (toTypeExpr α)
  toExpr := (·.toExpr)

instance ArgF.instToExpr {α} [ToExpr α] : ToExpr (ArgF α)  where
  toTypeExpr := ArgF.typeExpr α
  toExpr := (·.toExpr)

instance OperationF.instToExpr {α} [ToExpr α] : ToExpr (OperationF α) where
  toTypeExpr := OperationF.typeExpr (toTypeExpr α)
  toExpr := OperationF.toExpr

instance : ToExpr String.Pos where
  toTypeExpr := mkConst ``String.Pos
  toExpr e := mkApp (mkConst ``String.Pos.mk) (toExpr e.byteIdx)

instance SourceRange.instToExpr : ToExpr SourceRange where
  toTypeExpr := mkConst ``SourceRange
  toExpr e := mkApp2 (mkConst ``SourceRange.mk) (toExpr e.start) (toExpr e.stop)

namespace Ann

instance {Base α} [ToExpr Base] [ToExpr α] : ToExpr (Ann Base α) where
  toTypeExpr := mkApp2 (mkConst ``Ann) (toTypeExpr Base) (toTypeExpr α)
  toExpr a := mkApp4 (mkConst ``Ann.mk) (toTypeExpr Base) (toTypeExpr α) (toExpr a.ann) (toExpr a.val)

end Ann


namespace PreType

protected def typeExpr : Lean.Expr := mkConst ``PreType

protected def toExpr : PreType → Lean.Expr
| .ident loc nm a =>
  mkApp3
    (mkConst ``ident)
    (toExpr loc)
    (toExpr nm)
    (arrayToExpr  PreType.typeExpr (a.map (·.toExpr)))
| .bvar loc idx => mkApp2 (mkConst ``bvar) (toExpr loc) (toExpr idx)
| .fvar loc idx a =>
  mkApp3
    (mkConst ``fvar)
    (toExpr loc)
    (toExpr idx)
    (arrayToExpr  PreType.typeExpr (a.map (·.toExpr)))
| .arrow loc a r => mkApp3 (mkConst ``arrow) (toExpr loc) a.toExpr r.toExpr
| .funMacro loc i r => mkApp3 (mkConst ``funMacro) (toExpr loc) (toExpr i) r.toExpr

instance : ToExpr PreType where
  toTypeExpr := mkConst ``PreType
  toExpr := PreType.toExpr

end PreType

namespace MetadataArg

protected def typeExpr := mkConst ``MetadataArg

protected def toExpr : MetadataArg → Lean.Expr
| .bool b   => mkApp (mkConst ``bool) (toExpr b)
| .num n    => mkApp (mkConst ``num) (toExpr n)
| .catbvar n => mkApp (mkConst ``catbvar) (toExpr n)
| .option ma =>
  let maExpr := optionToExpr MetadataArg.typeExpr (ma.attach.map fun ⟨a, _⟩ => a.toExpr)
  mkApp (mkConst ``MetadataArg.option) maExpr

instance : ToExpr MetadataArg where
  toTypeExpr := MetadataArg.typeExpr
  toExpr := MetadataArg.toExpr

end MetadataArg

instance MetadataAttr.instToExpr : ToExpr MetadataAttr where
  toTypeExpr := mkConst ``MetadataAttr
  toExpr a := mkAppN (mkConst ``MetadataAttr.mk) #[toExpr a.ident, toExpr a.args]

instance Metadata.instToExpr : ToExpr Metadata where
  toTypeExpr := mkConst ``Metadata
  toExpr m :=
    let init := mkConst ``Metadata.empty
    let push := (mkConst ``Metadata.push)
    m.toArray.foldl (init := init) fun m a => mkApp2 push m (toExpr a)

namespace ArgDeclKind

instance : ToExpr ArgDeclKind where
  toTypeExpr := mkConst ``ArgDeclKind
  toExpr
  | .cat c => mkApp (mkConst ``cat) (toExpr c)
  | .type tp => mkApp (mkConst ``type) (toExpr tp)

end ArgDeclKind

namespace ArgDecl

instance : ToExpr ArgDecl where
  toTypeExpr := mkConst ``ArgDecl
  toExpr  b := mkAppN (mkConst ``mk) #[toExpr b.ident, toExpr b.kind, toExpr b.metadata]

end ArgDecl

namespace SyntaxDefAtom

protected def typeExpr : Lean.Expr := mkConst ``SyntaxDefAtom

protected def toExpr : SyntaxDefAtom → Lean.Expr
| .ident v p => mkAppN (mkConst ``ident) #[toExpr v, toExpr p]
| .str l     => mkAppN (mkConst ``str) #[toExpr l]
| .indent n a => mkAppN (mkConst ``indent) #[toExpr n, arrayToExpr SyntaxDefAtom.typeExpr (a.map (·.toExpr))]

instance : ToExpr SyntaxDefAtom where
  toTypeExpr := SyntaxDefAtom.typeExpr
  toExpr := SyntaxDefAtom.toExpr

end SyntaxDefAtom

namespace SyntaxDef

instance : ToExpr SyntaxDef where
  toTypeExpr := mkConst ``SyntaxDef
  toExpr s := mkApp2 (mkConst ``SyntaxDef.mk) (toExpr s.atoms) (toExpr s.prec)

end SyntaxDef

instance SynCatDecl.instToExpr : ToExpr SynCatDecl where
  toTypeExpr := mkConst ``SynCatDecl
  toExpr d := mkAppN (mkConst ``SynCatDecl.mk) #[toExpr d.name, toExpr d.argNames]

namespace DebruijnIndex

def ofNat {n : Nat} [NeZero n] (a : Nat) : DebruijnIndex n :=
  ⟨a % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

instance : ToExpr (DebruijnIndex n) where
  toTypeExpr := .app (mkConst ``DebruijnIndex) (toExpr n)
  toExpr a :=
    mkApp3 (.const ``DebruijnIndex.ofNat [])
        (toExpr n)
        (.app (.const ``Nat.instNeZeroSucc []) (mkNatLit (n-1)))
        (mkRawNatLit a.val)

end DebruijnIndex

namespace ValueBindingSpec

protected def toExpr {argDecls} (b : ValueBindingSpec argDecls) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``ValueBindingSpec.mk) #[
    bindingsExpr,
    toExpr b.nameIndex,
    toExpr b.argsIndex,
    toExpr b.typeIndex,
    toExpr b.allowCat
  ]

end ValueBindingSpec

namespace TypeBindingSpec

protected def toExpr (b : TypeBindingSpec bindings) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``TypeBindingSpec.mk) #[
    bindingsExpr,
    toExpr b.nameIndex,
    toExpr b.argsIndex,
    toExpr b.defIndex
  ]

end TypeBindingSpec

namespace BindingSpec

def typeExpr (bindingsExpr : Lean.Expr) : Lean.Expr := mkApp (mkConst ``BindingSpec) bindingsExpr

def toExpr (bi : BindingSpec bindings) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  match bi with
  | .value b => mkApp2 (mkConst ``value) bindingsExpr (b.toExpr bindingsExpr)
  | .type b => mkApp2 (mkConst ``type) bindingsExpr (b.toExpr bindingsExpr)

end BindingSpec

instance ArgDecls.instToExpr : ToExpr ArgDecls where
  toTypeExpr := mkConst ``ArgDecls
  toExpr a := mkApp (mkConst ``ArgDecls.ofArray) (toExpr a.toArray)

namespace OpDecl

instance : ToExpr OpDecl where
  toTypeExpr := mkConst ``OpDecl
  toExpr d :=
    let be := toExpr d.argDecls
    mkAppN (mkConst ``OpDecl.mk) #[
      toExpr d.name,
      be,
      toExpr d.category,
      toExpr d.syntaxDef,
      toExpr d.metadata,
      arrayToExpr (BindingSpec.typeExpr be) (d.newBindings.map (·.toExpr be))
    ]

end OpDecl

namespace TypeDecl

instance : ToExpr TypeDecl where
  toTypeExpr := mkConst ``TypeDecl
  toExpr d := mkApp2 (mkConst ``mk) (toExpr d.name) (toExpr d.argNames)

end TypeDecl

namespace FunctionDecl

instance : ToExpr FunctionDecl where
  toTypeExpr := mkConst ``FunctionDecl
  toExpr d := mkAppN (mkConst ``mk) #[toExpr d.name, toExpr d.argDecls, toExpr d.result, toExpr d.syntaxDef, toExpr d.metadata]

end FunctionDecl

namespace MetadataArgType

protected def toExpr : MetadataArgType → Lean.Expr
| .bool      => mkConst ``bool
| .num      => mkConst ``num
| .ident    => mkConst ``ident
| .opt tp => mkApp (mkConst ``opt) tp.toExpr

instance : ToExpr MetadataArgType where
  toTypeExpr := mkConst ``MetadataArgType
  toExpr := MetadataArgType.toExpr

end MetadataArgType

instance MetadataArgDecl.instToExpr : ToExpr MetadataArgDecl where
  toTypeExpr := mkConst ``MetadataArgDecl
  toExpr d := mkApp2 (mkConst ``MetadataArgDecl.mk) (toExpr d.ident) (toExpr d.type)

instance MetadataDecl.instToExpr : ToExpr MetadataDecl where
  toTypeExpr := mkConst ``MetadataDecl
  toExpr d := mkApp2 (mkConst ``MetadataDecl.mk) (toExpr d.name) (toExpr d.args)

instance Decl.instToExpr : ToExpr Decl where
  toTypeExpr := mkConst ``Decl
  toExpr
  | .syncat d   => mkApp (mkConst ``Decl.syncat)   (toExpr d)
  | .op d       => mkApp (mkConst ``Decl.op)       (toExpr d)
  | .type d     => mkApp (mkConst ``Decl.type)     (toExpr d)
  | .function d => mkApp (mkConst ``Decl.function) (toExpr d)
  | .metadata d => mkApp (mkConst ``Decl.metadata) (toExpr d)

instance Dialect.instToExpr : ToExpr Dialect where
  toTypeExpr := mkConst ``Dialect
  toExpr d :=
    mkApp3 (mkConst ``Dialect.ofArray)
           (toExpr d.name)
           (toExpr d.imports)
           (toExpr d.declarations)

namespace DialectMap

instance : ToExpr DialectMap where
  toTypeExpr := mkConst ``DialectMap
  toExpr d := mkApp (mkConst ``DialectMap.ofList!) (toExpr d.toList)

end DialectMap

instance Program.instToExpr : ToExpr Program where
  toTypeExpr := mkConst ``Program
  toExpr ms := mkApp3 (mkConst ``Program.create)
    (toExpr ms.dialects)
    (toExpr ms.dialect)
    (toExpr ms.commands)

end Strata

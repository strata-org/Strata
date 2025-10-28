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
syntax:max (name := astExprElab) "astExpr!" ident : term

@[term_elab astExprElab]
def astExprElabImpl : Term.TermElab := fun stx _expectedType => do
  match stx with
  | `(astExpr! $ident) => do
    let ctor ← realizeGlobalConstNoOverloadWithInfo ident
    let cv ← getConstVal ctor
    let argc := cv.type.getForallBinderNames.length
    let ctorExpr := mkApp2 (mkConst ``mkConst) (toExpr ctor) emptyLevel
    if argc = 0 then
      return ctorExpr
    else if argc > 10 then
      throwError s!"astExpr! does not support constructors with more than 10 arguments."
    let mkAppName : Name :=
      if argc = 1 then
        `Lean |>.str s!"mkApp"
      else
        `Lean |>.str s!"mkApp{argc}"
    return mkApp (mkConst mkAppName) ctorExpr
  | _ => do
    throwUnsupportedSyntax

syntax:max (name := astAnnExprElab) "astAnnExpr!" ident term:max : term

@[term_elab astAnnExprElab]
def astAnnExprElabImpl : Term.TermElab := fun stx _expectedType => do
  match stx with
  | `(astAnnExpr! $ident $ann) => do
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
  astAnnExpr! SyntaxCatF.mk cat.ann (toExpr cat.name) args
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
  astAnnExpr! ident ann (toExpr nm) ae
| .bvar ann idx =>
  astAnnExpr! bvar ann (toExpr idx)
| .fvar ann idx a =>
  let ae := arrayToExpr (TypeExprF.typeExpr (toTypeExpr α)) (a.map (·.toExpr))
  astAnnExpr! fvar ann (toExpr idx) ae
| .arrow ann a r =>
  astAnnExpr! arrow ann a.toExpr r.toExpr

instance {α} [ToExpr α] : ToExpr (TypeExprF α) where
  toTypeExpr := TypeExprF.typeExpr (toTypeExpr α)
  toExpr := TypeExprF.toExpr

end TypeExprF

protected def ExprF.typeExpr := mkApp (mkConst ``ExprF)

protected def ArgF.typeExpr (α : Type) [ToExpr α] := mkApp (mkConst ``ArgF) (toTypeExpr α)

protected def OperationF.typeExpr := mkApp (mkConst ``OperationF)

mutual

protected def ExprF.toExpr {α} [ToExpr α] : ExprF α → Lean.Expr
| .bvar ann i => astAnnExpr! ExprF.bvar ann (toExpr i)
| .fvar ann idx => astAnnExpr! ExprF.fvar ann (toExpr idx)
| .fn ann ident => astAnnExpr! ExprF.fn ann (toExpr ident)
| .app ann f a => astAnnExpr! ExprF.app ann f.toExpr a.toExpr
termination_by e => sizeOf e

def ArgF.toExpr {α} [ToExpr α] : ArgF α → Lean.Expr
| .op o => mkApp2 (mkConst ``ArgF.op) (toTypeExpr α) o.toExpr
| .expr e => mkApp2 (mkConst ``ArgF.expr) (toTypeExpr α) (e.toExpr)
| .type e => mkApp2 (mkConst ``ArgF.type) (toTypeExpr α) (toExpr e)
| .cat e => mkApp2 (mkConst ``ArgF.cat) (toTypeExpr α) (toExpr e)
| .ident ann e => astAnnExpr! ArgF.ident ann (toExpr e)
| .num ann e => astAnnExpr! ArgF.num ann (toExpr e)
| .decimal ann e => astAnnExpr! ArgF.decimal ann (toExpr e)
| .strlit ann e => astAnnExpr! ArgF.strlit ann (toExpr e)
| .option ann a =>
  let tpe := ArgF.typeExpr α
  astAnnExpr! ArgF.option ann (optionToExpr tpe <| a.attach.map fun ⟨e, _⟩ => e.toExpr)
| .seq ann a =>
  let tpe := ArgF.typeExpr α
  astAnnExpr! ArgF.seq ann <| arrayToExpr tpe <| a.map (·.toExpr)
| .commaSepList ann a =>
  let tpe := ArgF.typeExpr α
  astAnnExpr! ArgF.commaSepList ann <| arrayToExpr tpe <| a.map (·.toExpr)
termination_by a => sizeOf a

protected def OperationF.toExpr {α} [ToExpr α] (op : OperationF α) : Lean.Expr :=
  let args := arrayToExpr (ArgF.typeExpr α) (op.args.map (·.toExpr))
  astAnnExpr! OperationF.mk op.ann (toExpr op.name) args
termination_by sizeOf op
decreasing_by
  simp only [OperationF.sizeOf_spec]
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
  let args := arrayToExpr  PreType.typeExpr (a.map (·.toExpr))
  astExpr! ident (toExpr loc) (toExpr nm) args
| .bvar loc idx => astExpr! bvar (toExpr loc) (toExpr idx)
| .fvar loc idx a =>
    let args := arrayToExpr  PreType.typeExpr (a.map (·.toExpr))
    astExpr! fvar (toExpr loc) (toExpr idx) args
| .arrow loc a r =>
  astExpr! arrow (toExpr loc) a.toExpr r.toExpr
| .funMacro loc i r =>
  astExpr! funMacro (toExpr loc) (toExpr i) r.toExpr

instance : ToExpr PreType where
  toTypeExpr := mkConst ``PreType
  toExpr := PreType.toExpr

end PreType

namespace MetadataArg

protected def typeExpr := mkConst ``MetadataArg

protected def toExpr : MetadataArg → Lean.Expr
| .bool b => astExpr! bool (toExpr b)
| .num n => astExpr! num (toExpr n)
| .catbvar n => astExpr! catbvar (toExpr n)
| .option ma =>
  let maExpr := optionToExpr MetadataArg.typeExpr (ma.attach.map fun ⟨a, _⟩ => a.toExpr)
  astExpr! option maExpr

instance : ToExpr MetadataArg where
  toTypeExpr := MetadataArg.typeExpr
  toExpr := MetadataArg.toExpr

end MetadataArg

instance MetadataAttr.instToExpr : ToExpr MetadataAttr where
  toTypeExpr := astExpr! MetadataAttr
  toExpr a := astExpr! MetadataAttr.mk (toExpr a.ident) (toExpr a.args)

instance Metadata.instToExpr : ToExpr Metadata where
  toTypeExpr := astExpr! Metadata
  toExpr m :=
    let init := astExpr! Metadata.empty
    let push := astExpr! Metadata.push
    m.toArray.foldl (init := init) fun m a => push m (toExpr a)

namespace ArgDeclKind

instance : ToExpr ArgDeclKind where
  toTypeExpr := mkConst ``ArgDeclKind
  toExpr
  | .cat c => astExpr! cat (toExpr c)
  | .type tp => astExpr! type (toExpr tp)

end ArgDeclKind

namespace ArgDecl

instance : ToExpr ArgDecl where
  toTypeExpr := mkConst ``ArgDecl
  toExpr  b := astExpr! mk (toExpr b.ident) (toExpr b.kind) (toExpr b.metadata)

end ArgDecl

namespace SyntaxDefAtom

protected def typeExpr : Lean.Expr := mkConst ``SyntaxDefAtom

protected def toExpr : SyntaxDefAtom → Lean.Expr
| .ident v p => astExpr! ident (toExpr v) (toExpr p)
| .str l     => astExpr! str (toExpr l)
| .indent n a =>
  let args := arrayToExpr SyntaxDefAtom.typeExpr (a.map (·.toExpr))
  astExpr! indent (toExpr n) args

instance : ToExpr SyntaxDefAtom where
  toTypeExpr := SyntaxDefAtom.typeExpr
  toExpr := SyntaxDefAtom.toExpr

end SyntaxDefAtom

namespace SyntaxDef

instance : ToExpr SyntaxDef where
  toTypeExpr := mkConst ``SyntaxDef
  toExpr s := astExpr! mk (toExpr s.atoms) (toExpr s.prec)

end SyntaxDef

instance SynCatDecl.instToExpr : ToExpr SynCatDecl where
  toTypeExpr := mkConst ``SynCatDecl
  toExpr d := astExpr! mk (toExpr d.name) (toExpr d.argNames)

namespace DebruijnIndex

protected def ofNat {n : Nat} [NeZero n] (a : Nat) : DebruijnIndex n :=
  ⟨a % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

instance {n} : ToExpr (DebruijnIndex n) where
  toTypeExpr := .app (mkConst ``DebruijnIndex) (toExpr n)
  toExpr a :=
    astExpr! DebruijnIndex.ofNat
        (toExpr n)
        (.app (.const ``Nat.instNeZeroSucc []) (mkNatLit (n-1)))
        (mkRawNatLit a.val)

end DebruijnIndex

namespace ValueBindingSpec

protected def toExpr {argDecls} (b : ValueBindingSpec argDecls) (argDeclsExpr : Lean.Expr) : Lean.Expr :=
  astExpr! mk
    argDeclsExpr
    (toExpr b.nameIndex)
    (toExpr b.argsIndex)
    (toExpr b.typeIndex)
    (toExpr b.allowCat)

end ValueBindingSpec

namespace TypeBindingSpec

protected def toExpr {argDecls} (b : TypeBindingSpec argDecls) (argDeclsExpr : Lean.Expr) : Lean.Expr :=
  astExpr! mk
    argDeclsExpr
    (toExpr b.nameIndex)
    (toExpr b.argsIndex)
    (toExpr b.defIndex)

end TypeBindingSpec

namespace BindingSpec

def typeExpr (argDeclsExpr : Lean.Expr) : Lean.Expr := mkApp (mkConst ``BindingSpec) argDeclsExpr

/--
Converts a bindings specification to a Lean expression.

To avoid recomputations, this takes the argDecls and its representation as an expression.
-/
def toExpr {argDecls} (bi : BindingSpec argDecls) (argDeclsExpr : Lean.Expr) : Lean.Expr :=
  match bi with
  | .value b => astExpr! value argDeclsExpr (b.toExpr argDeclsExpr)
  | .type b => astExpr! type argDeclsExpr (b.toExpr argDeclsExpr)

end BindingSpec

instance ArgDecls.instToExpr : ToExpr ArgDecls where
  toTypeExpr := astExpr! ArgDecls
  toExpr a := astExpr! ArgDecls.ofArray (toExpr a.toArray)

namespace OpDecl

instance : ToExpr OpDecl where
  toTypeExpr := mkConst ``OpDecl
  toExpr d :=
    let be := toExpr d.argDecls
    let bindings := arrayToExpr (BindingSpec.typeExpr be) (d.newBindings.map (·.toExpr be))
    astExpr! mk
      (toExpr d.name)
      be
      (toExpr d.category)
      (toExpr d.syntaxDef)
      (toExpr d.metadata)
      bindings

end OpDecl

namespace TypeDecl

instance : ToExpr TypeDecl where
  toTypeExpr := mkConst ``TypeDecl
  toExpr d := astExpr! mk (toExpr d.name) (toExpr d.argNames)

end TypeDecl

namespace FunctionDecl

instance : ToExpr FunctionDecl where
  toTypeExpr := mkConst ``FunctionDecl
  toExpr d :=
    astExpr! mk
      (toExpr d.name)
      (toExpr d.argDecls)
      (toExpr d.result)
      (toExpr d.syntaxDef)
      (toExpr d.metadata)

end FunctionDecl

namespace MetadataArgType

protected def toExpr : MetadataArgType → Lean.Expr
| .bool => astExpr! bool
| .num => astExpr! num
| .ident => astExpr! ident
| .opt tp => astExpr! opt tp.toExpr

instance : ToExpr MetadataArgType where
  toTypeExpr := mkConst ``MetadataArgType
  toExpr := MetadataArgType.toExpr

end MetadataArgType

instance MetadataArgDecl.instToExpr : ToExpr MetadataArgDecl where
  toTypeExpr := mkConst ``MetadataArgDecl
  toExpr d := astExpr! MetadataArgDecl.mk (toExpr d.ident) (toExpr d.type)

instance MetadataDecl.instToExpr : ToExpr MetadataDecl where
  toTypeExpr := mkConst ``MetadataDecl
  toExpr d := astExpr! MetadataDecl.mk (toExpr d.name) (toExpr d.args)

namespace Decl

instance Decl.instToExpr : ToExpr Decl where
  toTypeExpr := mkConst ``Decl
  toExpr
  | .syncat d   => astExpr! syncat (toExpr d)
  | .op d       => astExpr! op (toExpr d)
  | .type d     => astExpr! type (toExpr d)
  | .function d => astExpr! function (toExpr d)
  | .metadata d => astExpr! metadata (toExpr d)

end Decl

instance Dialect.instToExpr : ToExpr Dialect where
  toTypeExpr := mkConst ``Dialect
  toExpr d :=
    astExpr! Dialect.ofArray (toExpr d.name) (toExpr d.imports) (toExpr d.declarations)

namespace DialectMap

instance : ToExpr DialectMap where
  toTypeExpr := mkConst ``DialectMap
  toExpr d := astExpr! ofList! (toExpr d.toList)

end DialectMap

instance Program.instToExpr : ToExpr Program where
  toTypeExpr := mkConst ``Program
  toExpr ms :=
    astExpr! Program.create
      (toExpr ms.dialects)
      (toExpr ms.dialect)
      (toExpr ms.commands)

end Strata

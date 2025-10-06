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

end

namespace SyntaxCat

protected def toExpr : SyntaxCat → Lean.Expr
| .atom a => mkApp (mkConst ``SyntaxCat.atom) (toExpr a)
| .app f a => mkApp2 (mkConst ``SyntaxCat.app) (f.toExpr) (a.toExpr)

instance : ToExpr SyntaxCat where
  toTypeExpr := mkConst ``SyntaxCat
  toExpr := SyntaxCat.toExpr

end SyntaxCat

namespace TypeExpr

protected def typeExpr : Lean.Expr := mkConst ``TypeExpr

protected def toExpr : TypeExpr → Lean.Expr
| .ident nm a =>
  let ae := arrayToExpr TypeExpr.typeExpr (a.map (·.toExpr))
  astExpr! ident (toExpr nm) ae
| .bvar idx =>
  astExpr! bvar (toExpr idx)
| .fvar idx a =>
  let ae := arrayToExpr TypeExpr.typeExpr (a.map (·.toExpr))
  astExpr! fvar (toExpr idx) ae
| .arrow a r =>
  astExpr! arrow a.toExpr r.toExpr

instance  : ToExpr TypeExpr where
  toTypeExpr := TypeExpr.typeExpr
  toExpr := TypeExpr.toExpr

end TypeExpr

protected def Expr.typeExpr := mkConst ``Expr

protected def Arg.typeExpr := mkConst ``Arg

protected def Operation.typeExpr := mkConst ``Operation

mutual

protected def Expr.toExpr : Expr → Lean.Expr
| .bvar i => astExpr!  Expr.bvar (toExpr i)
| .fvar idx => astExpr! Expr.fvar (toExpr idx)
| .fn ident => astExpr! Expr.fn (toExpr ident)
| .app f a => astExpr! Expr.app f.toExpr a.toExpr
termination_by e => sizeOf e

def Arg.toExpr : Arg → Lean.Expr
| .op o => astExpr! Arg.op o.toExpr
| .expr e => astExpr! Arg.expr (e.toExpr)
| .type e => astExpr! Arg.type  (toExpr e)
| .cat e => astExpr! Arg.cat (toExpr e)
| .ident e => astExpr! Arg.ident (toExpr e)
| .num e => astExpr! Arg.num (toExpr e)
| .decimal e => astExpr! Arg.decimal (toExpr e)
| .strlit e => astExpr! Arg.strlit (toExpr e)
| .option a => astExpr! Arg.option (optionToExpr Arg.typeExpr (a.attach.map (fun ⟨e, _⟩ => e.toExpr)))
| .seq a => astExpr! Arg.seq (arrayToExpr Arg.typeExpr (a.map (·.toExpr)))
| .commaSepList a => astExpr! Arg.commaSepList (arrayToExpr Arg.typeExpr (a.map (·.toExpr)))
termination_by a => sizeOf a

protected def Operation.toExpr (op : Operation) : Lean.Expr :=
  let args := arrayToExpr Arg.typeExpr (op.args.map (·.toExpr))
  astExpr! Operation.mk (toExpr op.name) args
termination_by sizeOf op
decreasing_by
  simp only [Operation.sizeOf_spec]
  decreasing_tactic

end

instance Expr.instToExpr : ToExpr Expr where
  toTypeExpr := Expr.typeExpr
  toExpr := (·.toExpr)

instance Art.instToExpr : ToExpr Arg where
  toTypeExpr := Arg.typeExpr
  toExpr := Arg.toExpr

instance Operation.instToExpr : ToExpr Operation where
  toTypeExpr := Operation.typeExpr
  toExpr := Operation.toExpr

namespace PreType

protected def typeExpr : Lean.Expr := mkConst ``PreType

protected def toExpr : PreType → Lean.Expr
| .ident nm a =>
  let args := arrayToExpr  PreType.typeExpr (a.map (·.toExpr))
  astExpr! ident (toExpr nm) args
| .bvar idx => astExpr! bvar (toExpr idx)
| .fvar idx a =>
    let args := arrayToExpr  PreType.typeExpr (a.map (·.toExpr))
    astExpr! fvar (toExpr idx) args
| .arrow a r =>
  astExpr! arrow a.toExpr r.toExpr
| .funMacro i r =>
  astExpr! funMacro (toExpr i) r.toExpr

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
  toTypeExpr := mkConst ``MetadataAttr
  toExpr a := astExpr! MetadataAttr.mk (toExpr a.ident) (toExpr a.args)

instance Metadata.instToExpr : ToExpr Metadata where
  toTypeExpr := mkConst ``Metadata
  toExpr m := astExpr! Metadata.ofArray (toExpr m.toArray)

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

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Lean.Elab.App

namespace Strata

open Lean

@[inline]
private def optionToExpr (type : Lean.Expr) (a : Option Lean.Expr) : Lean.Expr :=
  match a with
  | none => mkApp (mkConst ``Option.none [levelZero]) type
  | some a => mkApp2 (mkConst ``Option.some [levelZero]) type a

@[inline]
private def arrayToExpr (type : Lean.Expr) (a : Array Lean.Expr) : Lean.Expr :=
  let init := mkApp2 (mkConst ``Array.mkEmpty [levelZero]) type (toExpr a.size)
  let pushFn := mkApp (mkConst ``Array.push [levelZero]) type
  a.foldl (init := init) (mkApp2 pushFn)

instance : ToExpr QualifiedIdent where
  toTypeExpr := mkConst ``QualifiedIdent
  toExpr i := mkApp2 (mkConst ``QualifiedIdent.mk) (toExpr i.dialect) (toExpr i.name)

namespace TypeExpr

protected def typeExpr : Lean.Expr := mkConst ``TypeExpr

protected def toExpr : TypeExpr → Lean.Expr
| .ident nm a =>
  mkApp2
    (mkConst ``TypeExpr.ident)
    (toExpr nm)
    (arrayToExpr TypeExpr.typeExpr (a.map (·.toExpr)))
| .bvar idx => mkApp (mkConst ``TypeExpr.bvar) (toExpr idx)
| .fvar idx a =>
  mkApp2
    (mkConst ``TypeExpr.fvar)
    (toExpr idx)
    (arrayToExpr TypeExpr.typeExpr (a.map (·.toExpr)))
| .arrow a r => mkApp2 (mkConst ``arrow) a.toExpr r.toExpr

instance : ToExpr TypeExpr where
  toTypeExpr := TypeExpr.typeExpr
  toExpr := TypeExpr.toExpr

end TypeExpr

namespace PreType

protected def typeExpr : Lean.Expr := mkConst ``PreType

protected def toExpr : PreType → Lean.Expr
| .ident nm a =>
  mkApp2
    (mkConst ``ident)
    (toExpr nm)
    (arrayToExpr  PreType.typeExpr (a.map (·.toExpr)))
| .bvar idx => mkApp (mkConst ``bvar) (toExpr idx)
| .fvar idx a =>
  mkApp2
    (mkConst ``fvar)
    (toExpr idx)
    (arrayToExpr  PreType.typeExpr (a.map (·.toExpr)))
| .arrow a r => mkApp2 (mkConst ``arrow) a.toExpr r.toExpr
| .funMacro i r => mkApp2 (mkConst ``funMacro) (toExpr i) r.toExpr

instance : ToExpr PreType where
  toTypeExpr := mkConst ``PreType
  toExpr := PreType.toExpr

end PreType

namespace SyntaxCat

protected def toExpr : SyntaxCat → Lean.Expr
| .atom a => mkApp (mkConst ``SyntaxCat.atom) (toExpr a)
| .app f a => mkApp2 (mkConst ``SyntaxCat.app) (f.toExpr) (a.toExpr)

instance : ToExpr SyntaxCat where
  toTypeExpr := mkConst ``SyntaxCat
  toExpr := SyntaxCat.toExpr

end SyntaxCat

protected def Expr.typeExpr := mkConst ``Expr

protected def Arg.typeExpr := mkConst ``Arg

protected def Operation.typeExpr := mkConst ``Operation

mutual

protected def Expr.toExpr : Expr → Lean.Expr
| .bvar i => mkApp (mkConst ``Expr.bvar) (toExpr i)
| .fvar idx => mkApp (mkConst ``Expr.fvar) (toExpr idx)
| .fn ident => mkApp (mkConst ``Expr.fn) (toExpr ident)
| .app f a => mkApp2 (mkConst ``Expr.app) f.toExpr a.toExpr
termination_by e => sizeOf e

def Arg.toExpr : Arg → Lean.Expr
| .op o => mkApp (mkConst ``Arg.op) o.toExpr
| .expr e     => mkApp (mkConst ``Arg.expr)  (e.toExpr)
| .type e     => mkApp (mkConst ``Arg.type)  (toExpr e)
| .cat e      => mkApp (mkConst ``Arg.cat)   (toExpr e)
| .ident e    => mkApp (mkConst ``Arg.ident) (toExpr e)
| .num e      => mkApp (mkConst ``Arg.num) (toExpr e)
| .decimal e  => mkApp (mkConst ``Arg.decimal) (toExpr e)
| .strlit e    => mkApp (mkConst ``Arg.strlit) (toExpr e)
| .option a => mkApp (mkConst ``Arg.option) (optionToExpr Arg.typeExpr (a.attach.map (fun ⟨e, _⟩ => e.toExpr)))
| .seq a => mkApp (mkConst ``Arg.seq) (arrayToExpr Arg.typeExpr (a.map (·.toExpr)))
| .commaSepList a => mkApp (mkConst ``Arg.commaSepList) (arrayToExpr Arg.typeExpr (a.map (·.toExpr)))
termination_by a => sizeOf a

protected def Operation.toExpr (op : Operation) : Lean.Expr :=
  let args := arrayToExpr Arg.typeExpr (op.args.map (·.toExpr))
  mkApp2 (mkConst ``Operation.mk) (toExpr op.name) args
termination_by sizeOf op

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
  toExpr m := mkAppN (mkConst ``Metadata.ofArray) #[toExpr m.toArray]

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

protected
def ValueBindingSpec.toExpr {bindings} (b : ValueBindingSpec bindings) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``ValueBindingSpec.mk) #[
    bindingsExpr,
    toExpr b.nameIndex,
    toExpr b.argsIndex,
    toExpr b.typeIndex,
    toExpr b.metadataIndex,
    toExpr b.allowCat
  ]

protected
def TypeBindingSpec.toExpr (b : TypeBindingSpec bindings) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  mkAppN (mkConst ``TypeBindingSpec.mk) #[
    bindingsExpr,
    toExpr b.nameIndex,
    toExpr b.argsIndex,
    toExpr b.defIndex
  ]

namespace BindingSpec

def typeExpr (bindingsExpr : Lean.Expr) : Lean.Expr := mkApp (mkConst ``BindingSpec) bindingsExpr

def toExpr (bi : BindingSpec bindings) (bindingsExpr : Lean.Expr) : Lean.Expr :=
  match bi with
  | .value b => mkApp2 (mkConst ``value) bindingsExpr (b.toExpr bindingsExpr)
  | .type b => mkApp2 (mkConst ``type) bindingsExpr (b.toExpr bindingsExpr)

end BindingSpec

instance OpDecl.instToExpr : ToExpr OpDecl where
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

instance TypeDecl.instToExpr : ToExpr TypeDecl where
  toTypeExpr := mkConst ``TypeDecl
  toExpr d := mkApp2 (mkConst ``TypeDecl.mk) (toExpr d.name) (toExpr d.argNames)

instance FunctionDecl.instToExpr : ToExpr FunctionDecl where
  toTypeExpr := mkConst ``FunctionDecl
  toExpr d := mkAppN (mkConst ``FunctionDecl.mk) #[toExpr d.name, toExpr d.argDecls, toExpr d.result, toExpr d.syntaxDef, toExpr d.metadata]

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

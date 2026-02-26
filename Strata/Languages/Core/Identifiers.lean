/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.Factory
namespace Core

open Std

abbrev CoreIdent := Lambda.Identifier Unit

abbrev CoreExprMetadata := Unit
abbrev CoreLParams: Lambda.LExprParams := {Metadata := CoreExprMetadata, IDMeta := Unit}
abbrev CoreLabel := String

def CoreIdentDec : DecidableEq CoreIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))

instance : Coe String CoreIdent where
  coe | s => ⟨s, ()⟩

def CoreIdent.toPretty (x : CoreIdent) : String := x.name

instance : ToFormat CoreIdent where
  format i := CoreIdent.toPretty i

-- Explicit instances for CoreLParams field access
instance : ToFormat CoreLParams.Identifier :=
  show ToFormat CoreIdent from inferInstance

instance : DecidableEq CoreLParams.Identifier :=
  show DecidableEq CoreIdent from inferInstance



/-- Full representation of Strata Core Identifier with scope.
  This can be useful for both debugging and generating "unique" strings,
  for example, as labels of proof obligations in the VC generator.

  As a general guideline, whenever conversion from a `CoreIdent` to `String`
  is needed, _always use the `toString` method_." -/
instance : ToString CoreIdent where
  toString | ⟨s, ()⟩ => s

instance : Repr CoreIdent where
  reprPrec | ⟨s, ()⟩, _  => ToFormat.format s

instance : Inhabited CoreIdent where
  default := ⟨"_", ()⟩

instance : Lambda.HasGen Unit where
  genVar T := let (sym, state') := (Lambda.TState.genExprSym T.genState)
              (⟨sym, ()⟩, { T with genState := state' })

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono
/-- Elaborator for Core identifiers -/
def elabCoreIdent : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return mkApp3 (mkConst ``Lambda.Identifier.mk) (mkConst ``Unit) (mkStrLit s) (mkConst ``Unit.unit)
  | _ => throwUnsupportedSyntax

instance : MkLExprParams ⟨CoreExprMetadata, Unit⟩ where
  elabIdent := elabCoreIdent
  toExpr := mkApp2 (mkConst ``Lambda.LExprParams.mk) (mkConst ``CoreExprMetadata) (mkConst ``Unit)

elab "eb[" e:lexprmono "]" : term => elabLExprMono (T:=⟨CoreExprMetadata, Unit⟩) e

/--
info: Lambda.LExpr.op () { name := "old", metadata := () }
  none : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[~old]

/--
info: Lambda.LExpr.app () (Lambda.LExpr.op () { name := "old", metadata := () } none)
  (Lambda.LExpr.fvar () { name := "a", metadata := () }
    none) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(~old a)]

open Lambda.LTy.Syntax in

/--
info: Lambda.LExpr.fvar () { name := "x", metadata := () }
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(x : bool)]

end Syntax

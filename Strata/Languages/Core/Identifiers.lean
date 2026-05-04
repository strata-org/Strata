/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Factory
public import Strata.DDM.Util.SourceRange
public meta import Strata.DL.Lambda.LExpr
namespace Core

public section

open Std

@[expose]
abbrev CoreIdent := Lambda.Identifier Unit

@[expose]
abbrev CoreExprMetadata := Strata.SourceRange
@[expose]
abbrev CoreLParams: Lambda.LExprParams := {Metadata := CoreExprMetadata, IDMeta := Unit}
@[expose]
abbrev CoreLabel := String

def CoreIdentDec : DecidableEq CoreIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Unit))

instance : Coe String CoreIdent where
  coe | s => ⟨s, ()⟩

def CoreIdent.toPretty (x : CoreIdent) : String := x.name

/-- String used to prefix identifiers representing pre-state inout parameters. -/
@[expose]
def CoreIdent.oldStr : String := "old "

/-- Create the `old name` identifier for an inout parameter named `name`. -/
@[expose]
def CoreIdent.mkOld (name : String) : CoreIdent := ⟨CoreIdent.oldStr ++ name, ()⟩

/-- `g ≠ CoreIdent.mkOld g.name` because `"old " ++ s` is strictly longer than `s`. -/
theorem CoreIdent.ne_mkOld (g : CoreIdent) : g ≠ CoreIdent.mkOld g.name := by
  intro h
  have h_name := congrArg Lambda.Identifier.name h
  simp [CoreIdent.mkOld, CoreIdent.oldStr] at h_name
  have h1 : g.name.length < ("old " ++ g.name).length := by
    rw [String.length_append]
    have : (0 : Nat) < "old ".length := by decide
    omega
  rw [← h_name] at h1; omega

/-- `mkOld` is injective on the underlying name. -/
theorem CoreIdent.mkOld_injective {a b : String} (h : CoreIdent.mkOld a = CoreIdent.mkOld b) :
    a = b := by
  have h_name := congrArg Lambda.Identifier.name h
  simp [CoreIdent.mkOld, CoreIdent.oldStr] at h_name
  have h1 := congrArg String.toList h_name
  simp at h1
  exact String.ext h1

/-- Check whether an identifier is already an `old`-prefixed global name. -/
def CoreIdent.isOldIdent (ident : CoreIdent) : Bool := ident.name.startsWith CoreIdent.oldStr

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


end -- public section

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono
/-- Elaborator for Core identifiers -/
meta def elabCoreIdent : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return mkApp3 (mkConst ``Lambda.Identifier.mk) (mkConst ``Unit) (mkStrLit s) (mkConst ``Unit.unit)
  | _ => throwUnsupportedSyntax

meta instance : MkLExprParams ⟨CoreExprMetadata, Unit⟩ where
  elabIdent := elabCoreIdent
  toExpr := mkApp2 (mkConst ``Lambda.LExprParams.mk) (mkConst ``CoreExprMetadata) (mkConst ``Unit)
  defaultMetadata := return mkConst ``Strata.SourceRange.none

elab "eb[" e:lexprmono "]" : term => elabLExprMono (T:=⟨CoreExprMetadata, Unit⟩) e

/--
info: Lambda.LExpr.op Strata.SourceRange.none { name := "old", metadata := () }
  none : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[~old]

/--
info: Lambda.LExpr.app Strata.SourceRange.none
  (Lambda.LExpr.op Strata.SourceRange.none { name := "old", metadata := () } none)
  (Lambda.LExpr.fvar Strata.SourceRange.none { name := "a", metadata := () }
    none) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(~old a)]

open Lambda.LTy.Syntax in

/--
info: Lambda.LExpr.fvar Strata.SourceRange.none { name := "x", metadata := () }
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Unit }.mono
-/
#guard_msgs in
#check eb[(x : bool)]

end Syntax

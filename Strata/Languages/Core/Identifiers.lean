/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.Factory
namespace Core

open Std

/--
 The purpose of `Visiblity` is to denote the visibility/scope of a Strata Core
 identifier.

 For example, global variables should have a `.glob` (i.e., global) visibility,
 and variables declared within a procedure should have a `.locl` (i.e., local)
 visibility. This distinction can be useful when one wants to refer to a global
 variable that is shadowed by a local variable.

 See `WF.lean` and `ProgramWF.lean` for how `.glob` and `.locl` are used to
 ensure well-formedness of type-checked programs.

 We do not require the parser or the pretty-printer to handle the scoping
 component, thus they should always assume the default `.unres` (i.e.,
 unresolved) visibility, and leave the task of scoping resolution and annotation
 to the type checker or some other semantic-aware processing utilities.

 The `.temp` scope is a reserved scope that should only be used for _generated
 variables_. This is to ensure that generated variable names never overlap with
 existing variable names, since they will never have the `.temp` visibility. It
 is the responsibility of the variable generator to ensure that the generated
 names themselves are unique (i.e., do not have duplicates).

 See `CoreGenState` for a unique generator for Strata Core Identifiers.
-/
inductive Visibility where
  | unres
  | glob
  | locl
  | temp
deriving DecidableEq, Repr, Inhabited

instance : ToFormat Visibility where
  format
  | .unres => "u:"
  | .glob => "g:"
  | .locl => "l:"
  | .temp => "t:"

abbrev CoreIdent := Lambda.Identifier Visibility
instance : ToString Visibility where
  toString v := toString $ ToFormat.format v

abbrev CoreExprMetadata := Unit
abbrev CoreLParams: Lambda.LExprParams := {Metadata := CoreExprMetadata, IDMeta := Visibility}
abbrev CoreLabel := String

def CoreIdentDec : DecidableEq CoreIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Visibility))


@[match_pattern]
def CoreIdent.unres (s : String) : CoreIdent := ⟨s, Visibility.unres⟩
@[match_pattern]
def CoreIdent.glob (s : String) : CoreIdent := ⟨s, Visibility.glob⟩
@[match_pattern]
def CoreIdent.locl (s : String) : CoreIdent := ⟨s, Visibility.locl⟩
@[match_pattern]
def CoreIdent.temp (s : String) : CoreIdent := ⟨s, Visibility.temp⟩

def CoreIdent.isUnres (id : CoreIdent) : Bool := match id with
  | .unres _ => true | _ => false
def CoreIdent.isGlob (id : CoreIdent) : Bool := match id with
  | .glob _ => true | _ => false
def CoreIdent.isLocl (id : CoreIdent) : Bool := match id with
  | .locl _ => true | _ => false
def CoreIdent.isTemp (id : CoreIdent) : Bool := match id with
  | .temp _ => true | _ => false

def CoreIdent.isGlobOrLocl (id : CoreIdent) : Bool :=
  CoreIdent.isGlob id ∨ CoreIdent.isLocl id

instance : Coe String CoreIdent where
  coe | s => .unres s

-- instance : DecidableEq CoreIdent := instDecidableEqProd

/-- The pretty-printer for Strata Core Identifiers.
  We ignore the visibility part so that the output can be parsed again -/
def CoreIdent.toPretty (x : CoreIdent) : String :=
  match x with | ⟨s, _⟩ => s

/-- The pretty-printer for Strata Core Identifiers.
  We ignore the visibility part so that the output can be parsed again -/
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
  is needed, _always use the `toString` method_." Since `toString` includes the
  scoping information, consistency is ensured. Moreover, we could change the
  string representation fairly easily by overriding the method, if needed.
-/
instance : ToString CoreIdent where
  toString | ⟨s, v⟩ => (toString $ ToFormat.format v) ++ (toString $ ToFormat.format s)

instance : Repr CoreIdent where
  reprPrec | ⟨s, v⟩, _  => (ToFormat.format v) ++ (ToFormat.format s)

instance : Inhabited CoreIdent where
  default := ⟨"_", .unres⟩

instance : Lambda.HasGen Visibility where
  genVar T := let (sym, state') := (Lambda.TState.genExprSym T.genState)
              (CoreIdent.temp sym, { T with genState := state' })

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
def elabCoreIdent : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return ← mkAppM ``CoreIdent.unres #[mkStrLit s]
  | _ => throwUnsupportedSyntax

instance : MkLExprParams ⟨CoreExprMetadata, Visibility⟩ where
  elabIdent := elabCoreIdent
  toExpr := mkApp2 (mkConst ``Lambda.LExprParams.mk) (mkConst ``CoreExprMetadata) (.const ``Visibility [])

elab "eb[" e:lexprmono "]" : term => elabLExprMono (T:=⟨CoreExprMetadata, Visibility⟩) e

/--
info: Lambda.LExpr.op () (CoreIdent.unres "old")
  none : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[~old]

/--
info: Lambda.LExpr.app () (Lambda.LExpr.op () (CoreIdent.unres "old") none)
  (Lambda.LExpr.fvar () (CoreIdent.unres "a")
    none) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[(~old a)]

open Lambda.LTy.Syntax in

/--
info: Lambda.LExpr.fvar () (CoreIdent.unres "x")
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
-/
#guard_msgs in
#check eb[(x : bool)]

end Syntax

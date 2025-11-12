/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExprTypeEnv
namespace Boogie

open Std

/--
 The purpose of `Visiblity` is to denote the visibility/scope of a Boogie identifier.

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

 See `BoogieGenState` for a unique generator for Boogie Identifiers.
-/
inductive Visibility where
  | unres
  | glob
  | locl
  | temp
deriving DecidableEq, Repr

instance : ToFormat Visibility where
  format
  | .unres => "u:"
  | .glob => "g:"
  | .locl => "l:"
  | .temp => "t:"

instance : ToString Visibility where
  toString v := toString $ ToFormat.format v

abbrev BoogieIdent := Lambda.Identifier Visibility
abbrev BoogieLabel := String

def BoogieIdentDec : DecidableEq BoogieIdent := inferInstanceAs (DecidableEq (Lambda.Identifier Visibility))


@[match_pattern]
def BoogieIdent.unres (s : String) : BoogieIdent := ⟨s, Visibility.unres⟩
@[match_pattern]
def BoogieIdent.glob (s : String) : BoogieIdent := ⟨s, Visibility.glob⟩
@[match_pattern]
def BoogieIdent.locl (s : String) : BoogieIdent := ⟨s, Visibility.locl⟩
@[match_pattern]
def BoogieIdent.temp (s : String) : BoogieIdent := ⟨s, Visibility.temp⟩

def BoogieIdent.isUnres (id : BoogieIdent) : Bool := match id with
  | .unres _ => true | _ => false
def BoogieIdent.isGlob (id : BoogieIdent) : Bool := match id with
  | .glob _ => true | _ => false
def BoogieIdent.isLocl (id : BoogieIdent) : Bool := match id with
  | .locl _ => true | _ => false
def BoogieIdent.isTemp (id : BoogieIdent) : Bool := match id with
  | .temp _ => true | _ => false

def BoogieIdent.isGlobOrLocl (id : BoogieIdent) : Bool :=
  BoogieIdent.isGlob id ∨ BoogieIdent.isLocl id

instance : Coe String BoogieIdent where
  coe | s => .unres s

-- instance : DecidableEq BoogieIdent := instDecidableEqProd

/-- The pretty-printer for Boogie Identifiers.
  We ignore the visibility part so that the output can be parsed again -/
def BoogieIdent.toPretty (x : BoogieIdent) : String :=
  match x with | ⟨s, _⟩ => s

/-- The pretty-printer for Boogie Identifiers.
  We ignore the visibility part so that the output can be parsed again -/
instance : ToFormat BoogieIdent where
  format i := BoogieIdent.toPretty i

/-- Full representation of Boogie Identifier with scope.
  This can be useful for both debugging and generating "unique" strings,
  for example, as labels of proof obligations in the VC generator.

  As a general guideline, whenever conversion from a `BoogieIdent` to `String`
  is needed, _always use the `toString` method_." Since `toString` includes the
  scoping information, consistency is ensured. Moreover, we could change the
  string representation fairly easily by overriding the method, if needed.
-/
instance : ToString BoogieIdent where
  toString | ⟨s, v⟩ => (toString $ ToFormat.format v) ++ (toString $ ToFormat.format s)

instance : Repr BoogieIdent where
  reprPrec | ⟨s, v⟩, _  => (ToFormat.format v) ++ (ToFormat.format s)

instance : Inhabited BoogieIdent where
  default := ⟨"_", .unres⟩

instance : Lambda.HasGen Visibility where
  genVar T := let (sym, state') := (Lambda.TState.genExprSym T.genState)
              (BoogieIdent.temp sym, { T with genState := state' })

namespace Syntax

open Lean Elab Meta Lambda.LExpr.SyntaxMono

scoped syntax ident : lidentmono
/-- Elaborator for String identifiers, construct a String instance -/
def elabBoogieIdent : Syntax → MetaM Expr
  | `(lidentmono| $s:ident) => do
    let s := toString s.getId
    return ← mkAppM ``BoogieIdent.unres #[mkStrLit s]
  | _ => throwUnsupportedSyntax

instance : MkIdent Visibility where
  elabIdent := elabBoogieIdent
  toExpr := .const ``Visibility []

elab "eb[" e:lexprmono "]" : term => elabLExprMono (IDMeta:=Visibility) e

/-- info: Lambda.LExpr.op (BoogieIdent.unres "old") none : Lambda.LExpr Lambda.LMonoTy Visibility -/
#guard_msgs in
#check eb[~old]

/--
info: (Lambda.LExpr.op (BoogieIdent.unres "old") none).app
  (Lambda.LExpr.fvar (BoogieIdent.unres "a") none) : Lambda.LExpr Lambda.LMonoTy Visibility
-/
#guard_msgs in
#check eb[(~old a)]

open Lambda.LTy.Syntax in
/-- info: Lambda.LExpr.fvar (BoogieIdent.unres "x")
  (some (Lambda.LMonoTy.tcons "bool" [])) : Lambda.LExpr Lambda.LMonoTy Visibility  -/
#guard_msgs in
#check eb[(x : bool)]

end Syntax

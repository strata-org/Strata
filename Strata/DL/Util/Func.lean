/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.ListMap
public import Strata.DL.Util.FuncAttr

/-!
## Generic Function Structure

This module defines a generic function structure that can be instantiated for
different expression languages. It is parameterized by identifier, expression,
type, and metadata types.

For Lambda expressions, see `LFunc` in `Strata.DL.Lambda.Factory`.
For Imperative expressions, see `PureFunc` in `Strata.DL.Imperative.PureExpr`.
-/

namespace Strata.DL.Util

open Std (ToFormat Format format)

public section

/-- Type identifiers for generic type arguments. Alias for String. -/
@[expose] abbrev TyIdentifier := String

/-- A precondition with its associated metadata -/
structure FuncPrecondition (ExprT : Type) (MetadataT : Type) where
  expr : ExprT
  md : MetadataT
  deriving DecidableEq

/--
A generic function structure, parameterized by identifier, expression, type, and metadata types.

This structure can be instantiated for different expression languages.
For Lambda expressions, use `Lambda.LFunc` (`Strata.DL.Lambda.Factory`), which
extends this structure with a concrete evaluation function. For other expression
systems, instantiate with appropriate types.

(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure Func (IdentT : Type) (ExprT : Type) (TyT : Type) (MetadataT : Type) where
  name     : IdentT
  typeArgs : List TyIdentifier := []
  isConstr : Bool := false --whether function is datatype constructor
  isRecursive : Bool := false
  inputs   : ListMap IdentT TyT
  output   : TyT
  body     : Option ExprT := .none
  -- Structured attributes controlling partial evaluator behavior (inlining, etc.)
  attr     : Array FuncAttr := #[]
  axioms   : List ExprT := []  -- For axiomatic definitions
  preconditions : List (FuncPrecondition ExprT MetadataT) := []
  measure  : Option ExprT := .none -- Termination measure expression (from `decreases` clause)
  deriving DecidableEq

def Func.format {IdentT ExprT TyT MetadataT : Type} [ToFormat IdentT] [ToFormat ExprT] [ToFormat TyT] [Inhabited ExprT] (f : Func IdentT ExprT TyT MetadataT) : Format :=
  let attr := if f.attr.isEmpty then f!"" else f!"@[{f.attr}]{Format.line}"
  let typeArgs : Format := if f.typeArgs.isEmpty
                  then f!""
                  else f!"∀{f.typeArgs}."
  -- Format inputs recursively like Signature.format
  let rec formatInputs (inputs : List (IdentT × TyT)) : Format :=
    match inputs with
    | [] => f!""
    | [(k, v)] => f!"({k} : {v})"
    | (k, v) :: rest => f!"({k} : {v}) " ++ formatInputs rest
  let type := f!"{typeArgs} ({formatInputs f.inputs}) → {f.output}"
  let preconds := f.preconditions.map (f!"  requires {·.expr}")
  let precondsStr := if preconds.isEmpty then f!"" else Format.line ++ Format.joinSep preconds Format.line
  let measureStr := match f.measure with
    | some m => Format.line ++ f!"  decreases {m}"
    | none => f!""
  let sep := if f.body.isNone then f!";" else f!" :="
  let body := if f.body.isNone then f!"" else Std.Format.indentD f!"({f.body.get!})"
  let recPrefix := if f.isRecursive then f!"rec " else f!""
  f!"{attr}\
     {recPrefix}func {f.name} : {type}{precondsStr}{measureStr}{sep}\
     {body}"

instance {IdentT ExprT TyT MetadataT : Type} [ToFormat IdentT] [ToFormat ExprT] [ToFormat TyT] [Inhabited ExprT] : ToFormat (Func IdentT ExprT TyT MetadataT) where
  format := Func.format

/--
Well-formedness properties of Func. These are split from Func because
otherwise it becomes impossible to create a 'temporary' Func object whose
wellformedness might not hold yet.

The `getName`, `getVarNames` and `getTyFreeVars` functions are used to extract
names from identifiers, expressions and types, allowing this structure to work
with different types.
-/
structure FuncWF {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT) where
  -- No args have same name.
  arg_nodup:
    List.Nodup (f.inputs.map (getName ·.1))
  -- Free variables of body must be arguments.
  body_freevars:
    ∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)
  -- No typeArgs have same name
  typeArgs_nodup:
    List.Nodup f.typeArgs
  -- All type vars in input and output are in typeArg
  inputs_typevars_in_typeArgs:
    ∀ ty, ty ∈ f.inputs.values →
      getTyFreeVars ty ⊆ f.typeArgs
  output_typevars_in_typeArgs:
    getTyFreeVars f.output ⊆ f.typeArgs
  -- Free variables of preconditions must be arguments.
  precond_freevars:
    ∀ p, p ∈ f.preconditions →
      getVarNames p.expr ⊆ f.inputs.map (getName ·.1)

instance FuncWF.arg_nodup_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (List.Nodup (f.inputs.map (getName ·.1))) := by
  apply List.nodupDecidable

instance FuncWF.body_freevars_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)) :=
  by exact f.body.decidableForallMem

instance FuncWF.typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (List.Nodup f.typeArgs) := by
  apply List.nodupDecidable

instance FuncWF.inputs_typevars_in_typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ ty, ty ∈ f.inputs.values →
      getTyFreeVars ty ⊆ f.typeArgs) := by
  exact List.decidableBAll (fun x => getTyFreeVars x ⊆ f.typeArgs)
    (ListMap.values f.inputs)

instance FuncWF.output_typevars_in_typeArgs_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getTyFreeVars : TyT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (getTyFreeVars f.output ⊆ f.typeArgs) := by
  apply List.instDecidableRelSubsetOfDecidableEq

instance FuncWF.precond_freevars_decidable
    {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ p, p ∈ f.preconditions →
      getVarNames p.expr ⊆ f.inputs.map (getName ·.1)) := by
  exact List.decidableBAll (fun x => getVarNames x.expr ⊆ f.inputs.map (getName ·.1))
    f.preconditions

end -- public section
end Strata.DL.Util

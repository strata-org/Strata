/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.ListMap

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

/-- Type identifiers for generic type arguments. Alias for String. -/
abbrev TyIdentifier := String

/--
A generic function structure, parameterized by identifier, expression, type, and metadata types.

This structure can be instantiated for different expression languages.
For Lambda expressions, use `LFunc`. For other expression systems, instantiate
with appropriate types.

A optional evaluation function can be provided in the `concreteEval` field for
each factory function to allow the partial evaluator to do constant propagation
when all the arguments of a function are concrete. Such a function should take
two inputs: a function call expression and also -- somewhat redundantly, but
perhaps more conveniently -- the list of arguments in this expression.  Here's
an example of a `concreteEval` function for `Int.Add`:

```
(fun e args => match args with
               | [e1, e2] =>
                 let e1i := LExpr.denoteInt e1
                 let e2i := LExpr.denoteInt e2
                 match e1i, e2i with
                 | some x, some y => (.const (toString (x + y)) mty[int])
                 | _, _ => e
               | _ => e)
```

Note that if there is an arity mismatch or if the arguments are not
concrete/constants, this fails and it returns .none.

(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure Func (IdentT : Type) (ExprT : Type) (TyT : Type) (MetadataT : Type) where
  name     : IdentT
  typeArgs : List TyIdentifier := []
  isConstr : Bool := false --whether function is datatype constructor
  inputs   : ListMap IdentT TyT
  output   : TyT
  body     : Option ExprT := .none
  -- (TODO): Add support for a fixed set of attributes (e.g., whether to inline
  -- a function, etc.).
  attr     : Array String := #[]
  -- The MetadataT argument is the metadata that will be attached to the
  -- resulting expression of concreteEval if evaluation was successful.
  concreteEval : Option (MetadataT → List ExprT → Option ExprT) := .none
  axioms   : List ExprT := []  -- For axiomatic definitions

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
  let sep := if f.body.isNone then f!";" else f!" :="
  let body := if f.body.isNone then f!"" else Std.Format.indentD f!"({f.body.get!})"
  f!"{attr}\
     func {f.name} : {type}{sep}\
     {body}"

instance {IdentT ExprT TyT MetadataT : Type} [ToFormat IdentT] [ToFormat ExprT] [ToFormat TyT] [Inhabited ExprT] : ToFormat (Func IdentT ExprT TyT MetadataT) where
  format := Func.format

/--
Well-formedness properties of Func. These are split from Func because
otherwise it becomes impossible to create a 'temporary' Func object whose
wellformedness might not hold yet.

The `getName` and `getVarNames` functions are used to extract names from
identifiers and expressions, allowing this structure to work with different types.
-/
structure FuncWF {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT) where
  -- No args have same name.
  arg_nodup:
    List.Nodup (f.inputs.map (getName ·.1))
  -- Free variables of body must be arguments.
  body_freevars:
    ∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)
  -- concreteEval does not succeed if the length of args is incorrect.
  concreteEval_argmatch:
    ∀ fn md args res, f.concreteEval = .some fn
      → fn md args = .some res
      → args.length = f.inputs.length

instance FuncWF.arg_nodup_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (_ : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (List.Nodup (f.inputs.map (getName ·.1))) := by
  apply List.nodupDecidable

instance FuncWF.body_freevars_decidable {IdentT ExprT TyT MetadataT : Type}
    (getName : IdentT → String) (getVarNames : ExprT → List String)
    (f : Func IdentT ExprT TyT MetadataT):
    Decidable (∀ b, f.body = .some b →
      getVarNames b ⊆ f.inputs.map (getName ·.1)) :=
  by exact f.body.decidableForallMem

-- FuncWF.concreteEval_argmatch is not decidable.

end Strata.DL.Util

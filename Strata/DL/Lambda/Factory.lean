/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DL.Util.ListMap

/-!
## Lambda's Factory

This module formalizes Lambda's _factory_, which is a mechanism to extend the
type checker (see `Strata.DL.Lambda.LExprT`) and partial evaluator (see
`Strata.DL.Lambda.LExprEval`) by providing a map from operations to their types
and optionally, denotations. The factory allows adding type checking and
evaluation support for new operations without modifying the implementation of
either or any core ASTs.

Also see `Strata.DL.Lambda.IntBoolFactory` for a concrete example of a factory.
-/


namespace Lambda

open Std (ToFormat Format format)

---------------------------------------------------------------------

open LTy.Syntax

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier] [Inhabited Identifier]

/--
A signature is a map from variable identifiers to types.
-/
abbrev Signature (Identifier : Type) (Ty : Type) := ListMap Identifier Ty

def Signature.format (ty : Signature Identifier Ty) [Std.ToFormat Ty] : Std.Format :=
  match ty with
  | [] => ""
  | [(k, v)] => f!"({k} : {v})"
  | (k, v) :: rest =>
    f!"({k} : {v}) " ++ Signature.format rest

abbrev LMonoTySignature := Signature Identifier LMonoTy

abbrev LTySignature := Signature Identifier LTy


/--
A Lambda factory function, where the body can be optional. Universally
quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.

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
concrete/constants, this fails and we return the original term `e`.

(TODO) Can we enforce well-formedness of the denotation function? E.g., that it
has the right number and type of arguments, etc.?
(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure LFunc (MetadataType : Type) (Identifier : Type) where
  name     : Identifier
  typeArgs : List TyIdentifier := []
  inputs   : @LMonoTySignature Identifier
  output   : LMonoTy
  body     : Option (LExpr MetadataType LMonoTy Identifier) := .none
  -- (TODO): Add support for a fixed set of attributes (e.g., whether to inline
  -- a function, etc.).
  attr     : Array String := #[]
  concreteEval : Option ((LExpr MetadataType LMonoTy Identifier) → List (LExpr MetadataType LMonoTy Identifier) → (LExpr MetadataType LMonoTy Identifier)) := .none
  axioms   : List (LExpr MetadataType LMonoTy Identifier) := []  -- For axiomatic definitions

instance [Inhabited MetadataType] [Inhabited Identifier] : Inhabited (LFunc MetadataType Identifier) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

instance : ToFormat (LFunc MetadataType Identifier) where
  format f :=
    let attr := if f.attr.isEmpty then f!"" else f!"@[{f.attr}]{Format.line}"
    let typeArgs := if f.typeArgs.isEmpty
                    then f!""
                    else f!"∀{f.typeArgs}."
    let type := f!"{typeArgs} ({Signature.format f.inputs}) → {f.output}"
    let sep := if f.body.isNone then f!";" else f!" :="
    let body := if f.body.isNone then f!"" else Std.Format.indentD f!"({f.body.get!})"
    f!"{attr}\
       func {f.name} : {type}{sep}\
       {body}"

def LFunc.type (f : (LFunc Identifier)) : Except Format LTy := do
  if !f.inputs.keys.Nodup then
    .error f!"[{f.name}] Duplicates found in the formals!\
              {Format.line}\
              {f.inputs}"
  else if !f.typeArgs.Nodup then
    .error f!"[{f.name}] Duplicates found in the universally \
              quantified type identifiers!\
              {Format.line}\
              {f.typeArgs}"
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  match input_tys with
  | [] => .ok (.forAll f.typeArgs f.output)
  | ity :: irest =>
    .ok (.forAll f.typeArgs (Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)))

def LFunc.opExpr [Inhabited MetadataType] (f: LFunc MetadataType Identifier) : LExpr MetadataType LMonoTy Identifier :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op default f.name (some ty)

def LFunc.inputPolyTypes (f : (LFunc MetadataType Identifier)) : @LTySignature Identifier :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFunc.outputPolyType (f : (LFunc MetadataType Identifier)) : LTy :=
  .forAll f.typeArgs f.output

/--
The type checker and partial evaluator for Lambda is parameterizable by
a user-provided `Factory`.

We don't have any "built-in" functions like `+`, `-`, etc. in `(LExpr
Identifier)` -- lambdas are our only tool. `Factory` gives us a way to add
support for concrete/symbolic evaluation and type checking for `FunFactory`
functions without actually modifying any core logic or the ASTs.
-/
def Factory (MetadataType : Type) (Identifier : Type) := Array (LFunc MetadataType Identifier)

def Factory.default : @Factory MetadataType Identifier := #[]

instance : Inhabited (@Factory MetadataType Identifier) where
  default := @Factory.default MetadataType Identifier

def Factory.getFunctionNames (F : @Factory MetadataType Identifier) : Array Identifier :=
  F.map (fun f => f.name)

def Factory.getFactoryLFunc (F : @Factory MetadataType Identifier) (name : Identifier) : Option (LFunc MetadataType Identifier) :=
  F.find? (fun fn => fn.name == name)

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def Factory.addFactoryFunc (F : @Factory MetadataType Identifier) (func : (LFunc MetadataType Identifier)) : Except Format (@Factory MetadataType Identifier) :=
  match F.getFactoryLFunc func.name with
  | none => .ok (F.push func)
  | some func' =>
    .error f!"A function of name {func.name} already exists! \
              Redefinitions are not allowed.\n\
              Existing Function: {func'}\n\
              New Function:{func}"

/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def Factory.addFactory (F newF : @Factory MetadataType Identifier) : Except Format (@Factory MetadataType Identifier) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF

def getLFuncCall (e : (LExpr MetadataType LMonoTy Identifier)) : (LExpr MetadataType LMonoTy Identifier) × List (LExpr MetadataType LMonoTy Identifier) :=
  go e []
  where go e (acc : List (LExpr MetadataType LMonoTy Identifier)) :=
  match e with
  | .app _ (.app _ e' arg1) arg2 =>  go e' ([arg1, arg2] ++ acc)
  | .app _ (.op _ fn  fnty) arg1 =>  ((.op default fn fnty), ([arg1] ++ acc))
  | _ => (e, acc)

def getConcreteLFuncCall (e : (LExpr MetadataType LMonoTy Identifier)) : (LExpr MetadataType LMonoTy Identifier) × List (LExpr MetadataType LMonoTy Identifier) :=
  let (op, args) := getLFuncCall e
  if args.all LExpr.isConst then (op, args) else (e, [])

/--
If `e` is a call of a factory function, get the operator (`.op`), a list
of all the actuals, and the `(LFunc Identifier)`.
-/
def Factory.callOfLFunc (F : @Factory MetadataType Identifier) (e : (LExpr MetadataType LMonoTy Identifier)) : Option ((LExpr MetadataType LMonoTy Identifier) × List (LExpr MetadataType LMonoTy Identifier) × (LFunc MetadataType Identifier)) :=
  let (op, args) := getLFuncCall e
  match op with
  | .op name _ =>
    let maybe_func := getFactoryLFunc F name
    match maybe_func with
    | none => none
    | some func =>
      -- Note that we don't do any type or well-formedness checking here; this
      -- is just a simple arity check.
      match args.length == func.inputs.length with
      | true => (op, args, func) | false => none
  | _ => none

end Lambda

---------------------------------------------------------------------

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy

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
abbrev Signature (Identifier : Type) (Ty : Type) := Map Identifier Ty

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

A optional denotation function can be provided in the `denote` field for each
factory function. Such a function should take two inputs: a function call
expression and also -- somewhat redundantly, but perhaps more conveniently --
the list of arguments in this expression.  Here's an example of a `denote`
function for `Int.Add`:

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
concrete/constants and `denoteInt` fails, we return the original term `e`.

(TODO) Can we enforce well-formedness of the denotation function? E.g., that it
has the right number and type of arguments, etc.?
(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure LFunc (Identifier : Type) where
  name     : Identifier
  typeArgs : List TyIdentifier := []
  inputs   : @LMonoTySignature Identifier
  output   : LMonoTy
  body     : Option (LExpr Identifier) := .none
  -- (TODO): Add support for a fixed set of attributes (e.g., whether to inline
  -- a function, etc.).
  attr     : Array String := #[]
  denote   : Option ((LExpr Identifier) → List (LExpr Identifier) → (LExpr Identifier)) := .none
  axioms   : List (LExpr Identifier) := []  -- For axiomatic definitions

instance : Inhabited (LFunc Identifier) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

instance : ToFormat (LFunc Identifier) where
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

def LFunc.inputPolyTypes (f : (LFunc Identifier)) : @LTySignature Identifier :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFunc.outputPolyType (f : (LFunc Identifier)) : LTy :=
  .forAll f.typeArgs f.output

/--
The type checker and partial evaluator for Lambda is parameterizable by
a user-provided `Factory`.

We don't have any "built-in" functions like `+`, `-`, etc. in `(LExpr
Identifier)` -- lambdas are our only tool. `Factory` gives us a way to add
support for concrete/symbolic evaluation and type checking for `FunFactory`
functions without actually modifying any core logic or the ASTs.
-/
def Factory := Array (LFunc Identifier)

def Factory.default : @Factory Identifier := #[]

instance : Inhabited (@Factory Identifier) where
  default := @Factory.default Identifier

def Factory.getFunctionNames (F : @Factory Identifier) : Array Identifier :=
  F.map (fun f => f.name)

def Factory.getFactoryLFunc (F : @Factory Identifier) (name : Identifier) : Option (LFunc Identifier) :=
  F.find? (fun fn => fn.name == name)

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def Factory.addFactoryFunc (F : @Factory Identifier) (func : (LFunc Identifier)) : Except Format (@Factory Identifier) :=
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
def Factory.addFactory (F newF : @Factory Identifier) : Except Format (@Factory Identifier) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF

def getLFuncCall (e : (LExpr Identifier)) : (LExpr Identifier) × List (LExpr Identifier) :=
  go e []
  where go e (acc : List (LExpr Identifier)) :=
  match e with
  | .app (.app  e' arg1) arg2 =>  go e' ([arg1, arg2] ++ acc)
  | .app (.op  fn  fnty) arg1 =>  ((.op fn fnty), ([arg1] ++ acc))
  | _ => (e, acc)

def getConcreteLFuncCall (e : (LExpr Identifier)) : (LExpr Identifier) × List (LExpr Identifier) :=
  let (op, args) := getLFuncCall e
  if args.all LExpr.isConst then (op, args) else (e, [])

/--
If `e` is a call of a factory function, get the operator (`.op`), a list
of all the actuals, and the `(LFunc Identifier)`.
-/
def Factory.callOfLFunc (F : @Factory Identifier) (e : (LExpr Identifier)) : Option ((LExpr Identifier) × List (LExpr Identifier) × (LFunc Identifier)) :=
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

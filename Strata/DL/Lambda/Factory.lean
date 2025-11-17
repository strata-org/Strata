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

section Factory

variable {IDMeta : Type} [DecidableEq IDMeta] [Inhabited IDMeta]

/--
A signature is a map from variable identifiers to types.
-/
abbrev Signature (IDMeta : Type) (Ty : Type) := ListMap (Identifier IDMeta) Ty

def Signature.format (ty : Signature IDMeta Ty) [Std.ToFormat Ty] : Std.Format :=
  match ty with
  | [] => ""
  | [(k, v)] => f!"({k} : {v})"
  | (k, v) :: rest =>
    f!"({k} : {v}) " ++ Signature.format rest

abbrev LMonoTySignature := Signature IDMeta LMonoTy

abbrev LTySignature := Signature IDMeta LTy


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
structure LFunc (IDMeta : Type) where
  name     : Identifier IDMeta
  typeArgs : List TyIdentifier := []
  isConstr : Bool := false --whether function is datatype constructor
  inputs   : @LMonoTySignature IDMeta
  output   : LMonoTy
  body     : Option (LExpr LMonoTy IDMeta) := .none
  -- (TODO): Add support for a fixed set of attributes (e.g., whether to inline
  -- a function, etc.).
  attr     : Array String := #[]
  concreteEval : Option ((LExpr LMonoTy IDMeta) → List (LExpr LMonoTy IDMeta) → (LExpr LMonoTy IDMeta)) := .none
  axioms   : List (LExpr LMonoTy IDMeta) := []  -- For axiomatic definitions

instance : Inhabited (LFunc IDMeta) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

instance : ToFormat (LFunc IDMeta) where
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

def LFunc.type (f : (LFunc IDMeta)) : Except Format LTy := do
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

def LFunc.opExpr (f: LFunc IDMeta) : LExpr LMonoTy IDMeta :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op f.name ty

def LFunc.inputPolyTypes (f : (LFunc IDMeta)) : @LTySignature IDMeta :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFunc.outputPolyType (f : (LFunc IDMeta)) : LTy :=
  .forAll f.typeArgs f.output

def LFunc.eraseTypes (f : LFunc IDMeta) : LFunc IDMeta :=
  { f with
    body := f.body.map LExpr.eraseTypes,
    axioms := f.axioms.map LExpr.eraseTypes
  }

/--
The type checker and partial evaluator for Lambda is parameterizable by
a user-provided `Factory`.

We don't have any "built-in" functions like `+`, `-`, etc. in `(LExpr
IDMeta)` -- lambdas are our only tool. `Factory` gives us a way to add
support for concrete/symbolic evaluation and type checking for `FunFactory`
functions without actually modifying any core logic or the ASTs.
-/
def Factory := Array (LFunc IDMeta)

def Factory.default : @Factory IDMeta := #[]

instance : Inhabited (@Factory IDMeta) where
  default := @Factory.default IDMeta

def Factory.getFunctionNames (F : @Factory IDMeta) : Array (Identifier IDMeta) :=
  F.map (fun f => f.name)

def Factory.getFactoryLFunc (F : @Factory IDMeta) (name : String) : Option (LFunc IDMeta) :=
  F.find? (fun fn => fn.name.name == name)

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def Factory.addFactoryFunc (F : @Factory IDMeta) (func : (LFunc IDMeta)) : Except Format (@Factory IDMeta) :=
  match F.getFactoryLFunc func.name.name with
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
def Factory.addFactory (F newF : @Factory IDMeta) : Except Format (@Factory IDMeta) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF

def getLFuncCall {GenericTy} (e : (LExpr GenericTy IDMeta))
    : (LExpr GenericTy IDMeta) × List (LExpr GenericTy IDMeta) :=
  go e []
  where go e (acc : List (LExpr GenericTy IDMeta)) :=
  match e with
  | .app (.app  e' arg1) arg2 =>  go e' ([arg1, arg2] ++ acc)
  | .app (.op  fn  fnty) arg1 =>  ((.op fn fnty), ([arg1] ++ acc))
  | _ => (e, acc)

/--
If `e` is a call of a factory function, get the operator (`.op`), a list
of all the actuals, and the `(LFunc IDMeta)`.
-/
def Factory.callOfLFunc {GenericTy} (F : @Factory IDMeta)
    (e : (LExpr GenericTy IDMeta))
    : Option ((LExpr GenericTy IDMeta) × List (LExpr GenericTy IDMeta) × (LFunc IDMeta)) :=
  let (op, args) := getLFuncCall e
  match op with
  | .op name _ =>
    let maybe_func := getFactoryLFunc F name.name
    match maybe_func with
    | none => none
    | some func =>
      -- Note that we don't do any type or well-formedness checking here; this
      -- is just a simple arity check.
      match args.length == func.inputs.length with
      | true => (op, args, func) | false => none
  | _ => none

end Factory

variable {IDMeta: Type}

theorem getLFuncCall.go_size {GenericTy} {e: LExpr GenericTy IDMeta} {op args acc} : getLFuncCall.go e acc = (op, args) →
op.sizeOf + List.sum (args.map LExpr.sizeOf) <= e.sizeOf + List.sum (acc.map LExpr.sizeOf) := by
  fun_induction go generalizing op args
  case case1 acc e' arg1 arg2 IH =>
    intros Hgo; specialize (IH Hgo); simp_all; omega
  case case2 acc fn fnty arg1 =>
    simp_all; intros op_eq args_eq; subst op args; simp; omega
  case case3 op' args' _ _ => intros Hop; cases Hop; omega

theorem LExpr.sizeOf_pos {GenericTy} (e: LExpr GenericTy IDMeta): 0 < sizeOf e := by
  cases e<;> simp <;> omega

theorem List.sum_size_le (f: α → Nat) {l: List α} {x: α} (x_in: x ∈ l): f x ≤ List.sum (l.map f) := by
  induction l; simp_all; grind

theorem getLFuncCall_smaller {GenericTy} {e: LExpr GenericTy IDMeta} {op args} : getLFuncCall e = (op, args) → (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  unfold getLFuncCall; intros Hgo; have Hsize := (getLFuncCall.go_size Hgo);
  simp_all; have Hop:= LExpr.sizeOf_pos op; intros a a_in;
  have Ha := List.sum_size_le LExpr.sizeOf a_in; omega

theorem Factory.callOfLFunc_smaller {GenericTy} {F : @Factory IDMeta} {e : (LExpr GenericTy IDMeta)} {op args F'} : Factory.callOfLFunc F e = some (op, args, F') →
(forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  simp[Factory.callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp; cases op <;> simp
  rename_i o ty; cases (F.getFactoryLFunc o.name) <;> simp
  rename_i F'
  cases (args.length == List.length F'.inputs) <;> simp; intros op_eq args_eq F_eq; subst op args F'; exact (getLFuncCall_smaller Hfunc)

end Lambda

---------------------------------------------------------------------

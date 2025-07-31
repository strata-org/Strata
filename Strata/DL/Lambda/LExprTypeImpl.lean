/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

namespace LExpr
open LTy

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier]

/-! ### Type inference for unannotated Lambda expressions. -/

/-- Infer the type of `.fvar x fty`. -/
def inferFVar (T : (TEnv Identifier)) (x : Identifier) (fty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv Identifier)) :=
  match T.context.types.find? x with
  | none => .error f!"Cannot find this fvar in the context! \
                      {LExpr.fvar x fty}"
  | some ty => do
    let (ty, T) ← LTy.instantiateWithCheck ty T
    match fty with
    | none => .ok (ty, T)
    | some fty =>
      -- We do not support expressions to be annotated with type synonyms yet.
      -- As such, if `fty` is a synonym, then the following may raise an error.
      let S ← Constraints.unify [(fty, ty)] T.state.subst
      .ok (ty, TEnv.updateSubst T S)

/--
Infer the type of `.const c cty`. Here, we use the term "constant" in the same
sense as "literal".

For now, we have built-in support for booleans, integers, and strings. Note that
`LExpr` is extensible in the sense that support for new constants can be added
in the `Factory`, where a 0-ary function could be used to stand in for a
constant. However, pragmatically, we may want to incorporate first-class support
for some kinds of constants, especially for types with really large or infinite
members (e.g., bitvectors, natural numbers, etc.). `.const` is the place to do
that.
-/
def inferConst (T : (TEnv Identifier)) (c : String) (cty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv Identifier)) :=
  open LTy.Syntax in
  match c, cty with
  -- Annotated Booleans
  | "true", some LMonoTy.bool | "false", some LMonoTy.bool => .ok (mty[bool], T)
  -- Unannotated Booleans: note that `(.const "true" none)` and
  -- `(.const "false" none)` will be interpreted as booleans.
  | "true", none | "false", none =>
    if t[bool] ∈ T.knownTypes then
      .ok (mty[bool], T)
    else
      .error f!"Booleans are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const Identifier c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Integers
  | c, some LMonoTy.int =>
    if t[int] ∈ T.knownTypes then
      if c.isInt then .ok (mty[int], T)
                 else .error f!"Constant annotated as an integer, but it is not.\n\
                                {@LExpr.const Identifier c cty}"
    else
      .error f!"Integers are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const Identifier c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Reals
  | c, some LMonoTy.real =>
    if t[real] ∈ T.knownTypes then
      .ok (mty[real], T)
    else
      .error f!"Reals are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const Identifier c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated BitVecs
  | c, some (LMonoTy.bitvec n) =>
    let ty := LMonoTy.bitvec n
    if .forAll [] ty ∈ T.knownTypes then
      (.ok (ty, T))
    else
      .error f!"Bit vectors of size {n} are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const Identifier c cty}\n\
                Known Types: {T.knownTypes}"
  -- Annotated Strings
  | c, some LMonoTy.string =>
    if t[string] ∈ T.knownTypes then
      .ok (mty[string], T)
    else
      .error f!"Strings are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {@LExpr.const Identifier c cty}\n\
                Known Types: {T.knownTypes}"
  | _, _ =>
  -- Unannotated Integers
    if c.isInt then
      if t[int] ∈ T.knownTypes then
        .ok (mty[int], T)
      else
        .error f!"Integers are not registered in the known types.\n\
                  Constant {@LExpr.const Identifier c cty}\n\
                  Known Types: {T.knownTypes}"
    else
      .error f!"Cannot infer the type of this constant: \
                {@LExpr.const Identifier c cty}"

open LTy.Syntax in
mutual
/--
Type inference for `LExpr`s.

Also see `LExpr.annotate` for a function that annotates a given `LExpr` with the
inferred types.

(TODO) Prove termination.
-/
partial def infer (T : (TEnv Identifier)) (e : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) :=
  match e with
  | .mdata _ e   => infer T e
  | .const c cty => inferConst T c cty
  | .op o oty    => inferOp T o oty
  | .bvar _      => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar x fty  => inferFVar T x fty
  | .app e1 e2   => inferApp T e1 e2
  | .abs _ e     => inferAbs T e
  | .quant _ _ e => inferQuant T e
  | .eq e1 e2    => inferEq T e1 e2
  | .ite c th el => inferIte T c th el

/-- Infer the type of an operation `.op o oty`, where an operation is defined in
  the factory. -/
partial def inferOp (T : (TEnv Identifier)) (o : Identifier) (oty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv Identifier)) :=
  open LTy.Syntax in
  match T.functions.find? (fun fn => fn.name == o) with
  | none =>
    .error f!"{toString $ T.functions.getFunctionNames} Cannot infer the type of this operation: \
              {LExpr.op (toString o) oty}"
  | some func => do
      -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
      -- where there are duplicates in the formals, etc.).
      let type ← func.type
      let (ty, T) ← LTy.instantiateWithCheck type T
      let T ←
        match func.body with
        | none => .ok T
        | some body =>
          if body.freeVars.keys.all (fun k => k ∈ func.inputs.keys) then
            -- Temporarily add formals in the context.
            let T := T.pushEmptyContext
            let T := T.addToContext func.inputPolyTypes
            -- Type check the body and ensure that it unifies with the return type.
            let (bodyty, T) ← infer T body
            let (retty, T) ← func.outputPolyType.instantiateWithCheck T
            let S ← Constraints.unify [(retty, bodyty)] T.state.subst
            let T := T.updateSubst S
            let T := T.popContext
            .ok T
          else
            .error f!"Function body contains free variables!\n\
                      {func}"
      match oty with
      | none => .ok (ty, T)
      | some cty =>
        let S ← Constraints.unify [(cty, ty)] T.state.subst
        .ok (ty, TEnv.updateSubst T S)

partial def inferApp (T : (TEnv Identifier)) (e1 e2 : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) := do
  let (ty1, T) ← infer T e1
  let (ty2, T) ← infer T e2
  let (fresh_name, T) := TEnv.genTyVar T
  let freshty := (.ftvar fresh_name)
  let S ← Constraints.unify [(ty1, (.tcons "arrow" [ty2, freshty]))] T.state.subst
  .ok (freshty, TEnv.updateSubst T S)

partial def inferAbs (T : (TEnv Identifier)) (e : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) := do
  let (xv, T) := HasGen.genVar T
  let e' := LExpr.varOpen 0 (xv, none) e
  let (xt', T) := TEnv.genTyVar T
  let xt := .forAll [] (.ftvar xt')
  let T := T.insertInContext xv xt
  let (et, T) ← infer T e'
  let T := T.eraseFromContext xv
  let ty := (.tcons "arrow" [(.ftvar xt'), et])
  .ok (ty, T)

partial def inferQuant (T : (TEnv Identifier)) (e : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) := do
  let (xv, T) := HasGen.genVar T
  let e' := LExpr.varOpen 0 (xv, none) e
  let (xt', T) := TEnv.genTyVar T
  let xt := .forAll [] (.ftvar xt')
  let T := T.insertInContext xv xt
  let (et, T) ← infer T e'
  let T := T.eraseFromContext xv
  if et = LMonoTy.bool then
     let ty := (.tcons "bool" [])
     .ok (ty, T)
  else .error f!"Quantifier body {e} has type {et}, not 'bool'."

partial def inferEq (T : (TEnv Identifier)) (e1 e2 : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) := do
  -- `.eq A B` is well-typed if there is some instantiation of
  -- type parameters in `A` and `B` that gives them the same type.
  let (ty1, T) ← infer T e1
  let (ty2, T) ← infer T e2
  let S ← Constraints.unify [(ty1, ty2)] T.state.subst
  .ok (mty[bool], TEnv.updateSubst T S)

partial def inferIte (T : (TEnv Identifier)) (c th el : (LExpr Identifier)) : Except Format (LMonoTy × (TEnv Identifier)) := do
  let (cty, T) ← infer T c
  let (tty, T) ← infer T th
  let (ety, T) ← infer T el
  let S ← Constraints.unify [(cty, mty[bool]), (tty, ety)] T.state.subst
  .ok (tty, TEnv.updateSubst T S)

end
/--
Infer the monotype `ty` of `e` and then apply the global type substitution
`TEnv.TState.subst` to `ty` as well as the type context.
-/
def inferType
(T : TEnv Identifier) (e : LExpr Identifier) : Except Format (LMonoTy × (TEnv Identifier)) := do
  let (lty, T) ← infer T e
  let context := T.context.subst T.state.subst
  let T := { T with context := context }
  .ok (LMonoTy.subst T.state.subst lty, T)

/--
Infer the monotypes of expressions `es`, and then apply the global type
substitution `TEnv.TState.subst` to them as well as the type context.
-/
def inferTypes (T : (TEnv Identifier)) (es : List (LExpr Identifier)) : Except Format (List LMonoTy × (TEnv Identifier)) := do
  match es with
  | [] => .ok ([], T)
  | e :: erest => do
    let (e_ty, T) ← inferType T e
    let (erest_ty, T) ← inferTypes T erest
    .ok (e_ty :: erest_ty, T)

end LExpr
---------------------------------------------------------------------
end Lambda

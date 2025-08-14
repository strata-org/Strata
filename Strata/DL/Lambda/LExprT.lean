/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprWF

/-! ## Type Inference Transform for Lambda Expressions.

Type inference that transforms `LExpr` to annotated `LExprT`. `LExprT` is very
similar to `LExpr`, except that we mandate every constructor's annotation with
an inferred (mono)type.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)
open LTy

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier]

/--
Monotype-annotated Lambda expressions, obtained after a type inference transform
from Lambda expressions `LExpr`.
-/
inductive LExprT (Identifier : Type): Type where
  | const (c : String) (ty : LMonoTy)
  | op    (c : Identifier) (ty : LMonoTy)
  | bvar (deBruijnIndex : Nat) (ty : LMonoTy)
  | fvar (name : Identifier) (ty : LMonoTy)
  | mdata (info : Info) (e : LExprT Identifier)
  | abs (e : LExprT Identifier) (ty : LMonoTy)
  | quant (k : QuantifierKind) (argTy : LMonoTy) (e : LExprT Identifier)
  | app (fn e : LExprT Identifier) (ty : LMonoTy)
  | ite (c t e : LExprT Identifier) (ty : LMonoTy)
  | eq (e1 e2 : LExprT Identifier) (ty : LMonoTy)
  deriving Repr, DecidableEq

partial def LExprT.format (et : (LExprT Identifier)) : Std.Format :=
  match et with
  | .const c ty => f!"(#{c} : {ty})"
  | .op o ty => f!"(~{o} : {ty})"
  | .bvar i ty => f!"(%{i} : {ty})"
  | .fvar x ty => f!"({x} : {ty})"
  | .mdata m e => f!"(.mdata {repr m} {LExprT.format e})"
  | .abs e ty => f!"((λ {LExprT.format e}) : {ty})"
  | .quant .all ty e => f!"(∀({ty}) {LExprT.format e})"
  | .quant .exist ty e => f!"(∃({ty}) {LExprT.format e})"
  | .app e1 e2 ty => f!"({LExprT.format e1} {LExprT.format e2}) : {ty})"
  | .ite c t f ty => f!"(if {LExprT.format c} then \
                            {LExprT.format t} else \
                            {LExprT.format f}) : {ty})"
  | .eq e1 e2 ty => f!"({LExprT.format e1} == {LExprT.format e2}) : {ty})"

instance : ToFormat (LExprT Identifier) where
  format := LExprT.format

---------------------------------------------------------------------

namespace LExprT

/--
Obtain the monotype from `LExprT e`.
-/
def toLMonoTy (e : (LExprT Identifier)) : LMonoTy :=
  match e with
  | .const _ ty | .op _ ty | .bvar _ ty | .fvar _ ty
  | .app _ _ ty | .abs _ ty | .ite _ _ _ ty | .eq _ _ ty => ty
  | .quant _ _ _ => LMonoTy.bool
  | .mdata _ et => LExprT.toLMonoTy et

/--
Obtain an `LExpr` from an `LExprT`. We erase type annotations for all
expressions, except the constants `.const`s, `.op`s, and free variables
`.fvar`s.
-/
def toLExpr (e : (LExprT Identifier)) : (LExpr Identifier) :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar b _ => .bvar b
  | .fvar f ty => .fvar f ty
  | .app e1 e2 _ =>
    .app e1.toLExpr e2.toLExpr
  | .abs e (.arrow aty _) => .abs aty e.toLExpr
  | .abs e _ => .abs .none e.toLExpr
  | .quant qk ty e => .quant qk ty e.toLExpr
  | .ite c t f _ => .ite c.toLExpr t.toLExpr f.toLExpr
  | .eq e1 e2 _ => .eq e1.toLExpr e2.toLExpr
  | .mdata m e => .mdata m e.toLExpr

/--
Apply type substitution `S` to `LExprT e`.
-/
def applySubst (e : (LExprT Identifier)) (S : Subst) : (LExprT Identifier) :=
  match e with
  | .const c ty =>
    let ty := LMonoTy.subst S ty
    .const c ty
  | .op o ty =>
    let ty := LMonoTy.subst S ty
    .op o ty
  | .bvar b ty =>
    let ty := LMonoTy.subst S ty
    .bvar b ty
  | .fvar x ty =>
    let ty := LMonoTy.subst S ty
    .fvar x ty
  | .app e1 e2 ty =>
    let e1 := LExprT.applySubst e1 S
    let e2 := LExprT.applySubst e2 S
    let ty := LMonoTy.subst S ty
    .app e1 e2 ty
  | .abs e ty =>
    let e := LExprT.applySubst e S
    let ty := LMonoTy.subst S ty
    .abs e ty
  | .quant qk ty e =>
    let e := LExprT.applySubst e S
    .quant qk ty e
  | .ite c t f ty =>
    let c := LExprT.applySubst c S
    let t := LExprT.applySubst t S
    let f := LExprT.applySubst f S
    let ty := LMonoTy.subst S ty
    .ite c t f ty
  | .eq e1 e2 ty =>
    let e1 := LExprT.applySubst e1 S
    let e2 := LExprT.applySubst e2 S
    let ty := LMonoTy.subst S ty
    .eq e1 e2 ty
  | .mdata m e =>
    let e := LExprT.applySubst e S
    .mdata m e

/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varClose k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)` in an `LExprT e`.

Also see `LExpr.varClose` for an analogous function for `LExpr`s.
-/
protected def varClose (k : Nat) (x : Identifier) (e : (LExprT Identifier)) : (LExprT Identifier) :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar i ty => .bvar i ty
  | .fvar y yty => if (x == y) then (.bvar k yty)
                               else (.fvar y yty)
  | .mdata info e' => .mdata info (.varClose k x e')
  | .abs e' ty => .abs (.varClose (k + 1) x e') ty
  | .quant qk ty e' => .quant qk ty (.varClose (k + 1) x e')
  | .app e1 e2 ty => .app (.varClose k x e1) (.varClose k x e2) ty
  | .ite c t e ty => .ite (.varClose k x c) (.varClose k x t) (.varClose k x e) ty
  | .eq e1 e2 ty => .eq (.varClose k x e1) (.varClose k x e2) ty

---------------------------------------------------------------------

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
      let S ← Constraints.unify [(fty, ty)] T.state.substInfo
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

mutual
partial def fromLExprAux (T : (TEnv Identifier)) (e : (LExpr Identifier)) :
    Except Format ((LExprT Identifier) × (TEnv Identifier)) :=
  open LTy.Syntax in do
  match e with
  | .mdata m e =>
    let (et, T) ← fromLExprAux T e
    .ok ((.mdata m et), T)
  | .const c cty =>
    let (ty, T) ← inferConst T c cty
    .ok (.const c ty, T)
  | .op o oty =>
    let (ty, T) ← inferOp T o oty
    .ok (.op o ty, T)
  | .bvar _ => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar x fty =>
    let (ty, T) ← inferFVar T x fty
    .ok (.fvar x ty, T)
  | .app e1 e2   => fromLExprAux.app T e1 e2
  | .abs ty e    => fromLExprAux.abs T ty e
  | .quant qk ty e => fromLExprAux.quant T qk ty e
  | .eq e1 e2    => fromLExprAux.eq T e1 e2
  | .ite c th el => fromLExprAux.ite T c th el

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
            -- let (bodyty, T) ← infer T body
            let (body_typed, T) ← fromLExprAux T body
            let bodyty := body_typed.toLMonoTy
            let (retty, T) ← func.outputPolyType.instantiateWithCheck T
            let S ← Constraints.unify [(retty, bodyty)] T.state.substInfo
            let T := T.updateSubst S
            let T := T.popContext
            .ok T
          else
            .error f!"Function body contains free variables!\n\
                      {func}"
      match oty with
      | none => .ok (ty, T)
      | some cty =>
        let (optTyy, T) := (cty.aliasInst T)
        let S ← Constraints.unify [(ty, optTyy.getD cty )] T.state.substInfo
        .ok (ty, TEnv.updateSubst T S)

partial def fromLExprAux.ite (T : (TEnv Identifier)) (c th el : (LExpr Identifier)) := do
  let (ct, T) ← fromLExprAux T c
  let (tt, T) ← fromLExprAux T th
  let (et, T) ← fromLExprAux T el
  let cty := ct.toLMonoTy
  let tty := tt.toLMonoTy
  let ety := et.toLMonoTy
  let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] T.state.substInfo
  .ok (.ite ct tt et tty, TEnv.updateSubst T S)

partial def fromLExprAux.eq (T : (TEnv Identifier)) (e1 e2 : (LExpr Identifier)) := do
  -- `.eq A B` is well-typed if there is some instantiation of
  -- type parameters in `A` and `B` that makes them have the same type.
  let (e1t, T) ← fromLExprAux T e1
  let (e2t, T) ← fromLExprAux T e2
  let ty1 := e1t.toLMonoTy
  let ty2 := e2t.toLMonoTy
  let S ← Constraints.unify [(ty1, ty2)] T.state.substInfo
  .ok (.eq e1t e2t LMonoTy.bool, TEnv.updateSubst T S)

partial def fromLExprAux.abs (T : (TEnv Identifier)) (oty : Option LMonoTy) (e : (LExpr Identifier)) := do
  let (xv, T) := HasGen.genVar T
  let (xt', T) := TEnv.genTyVar T
  let xt := .forAll [] (.ftvar xt')
  let T := T.insertInContext xv xt
  let e' := LExpr.varOpen 0 (xv, some (.ftvar xt')) e
  let (et, T) ← fromLExprAux T e'
  let ety := et.toLMonoTy
  let etclosed := .varClose 0 xv et
  let T := T.eraseFromContext xv
  let ty := (.tcons "arrow" [(.ftvar xt'), ety])
  let mty := LMonoTy.subst T.state.substInfo.subst ty
  match mty, oty with
  | .arrow aty _, .some ty =>
    if aty == ty
    then .ok ()
    else .error "Type annotation on LTerm.abs doesn't match inferred argument type"
  | _, _ => .ok ()
  .ok (.abs etclosed mty, T)

partial def fromLExprAux.quant (T : (TEnv Identifier)) (qk : QuantifierKind) (oty : Option LMonoTy) (e : (LExpr Identifier)) := do
  let (xv, T) := HasGen.genVar T
  let (xt', T) := TEnv.genTyVar T
  let xt := .forAll [] (.ftvar xt')
  let S ← match oty with
  | .some ty =>
    let (optTyy, T) := (ty.aliasInst T)
    (Constraints.unify [(.ftvar xt', optTyy.getD ty)] T.state.substInfo)
  | .none =>
    .ok T.state.substInfo

  let T := TEnv.updateSubst T S

  let T := T.insertInContext xv xt
  let e' := LExpr.varOpen 0 (xv, some (.ftvar xt')) e
  let (et, T) ← fromLExprAux T e'
  let ety := et.toLMonoTy
  let mty := LMonoTy.subst T.state.substInfo.subst (.ftvar xt')
  match oty with
  | .some ty =>
    let (optTyy, _) := (ty.aliasInst T)
    if optTyy.getD ty == mty
    then .ok ()
    else .error f!"Type annotation on LTerm.quant {ty} (alias for {optTyy.getD ty}) doesn't match inferred argument type"
  | _ => .ok ()
  if ety = LMonoTy.bool then do
    let etclosed := .varClose 0 xv et
    let T := T.eraseFromContext xv
    .ok (.quant qk mty etclosed, T)
  else
    .error f!"Quantifier body has non-Boolean type: {ety}"

partial def fromLExprAux.app (T : (TEnv Identifier)) (e1 e2 : (LExpr Identifier)) := do
  let (e1t, T) ← fromLExprAux T e1
  let ty1 := e1t.toLMonoTy
  let (e2t, T) ← fromLExprAux T e2
  let ty2 := e2t.toLMonoTy
  let (fresh_name, T) := TEnv.genTyVar T
  let freshty := (.ftvar fresh_name)
  -- Indirection for type aliases
  let (optTyy1, T) := (ty1.aliasInst T)
  let (fresh_name1, T) := TEnv.genTyVar T
  let freshty1: LMonoTy := (.ftvar fresh_name1)
  let (optTyy2, T) := (ty2.aliasInst T)
  let (fresh_name2, T) := TEnv.genTyVar T
  let freshty2: LMonoTy := (.ftvar fresh_name2)
  let S ← Constraints.unify [(freshty1, optTyy1.getD ty1 )] T.state.substInfo
  let T := TEnv.updateSubst T S
  let S ← Constraints.unify [(freshty2, optTyy2.getD ty2 )] T.state.substInfo
  let T := TEnv.updateSubst T S

  let S ← Constraints.unify [(freshty1, (.tcons "arrow" [freshty2, freshty]))] T.state.substInfo
  let mty := LMonoTy.subst S.subst freshty
  .ok (.app e1t e2t mty, TEnv.updateSubst T S)

end

protected def fromLExpr (T : (TEnv Identifier)) (e : (LExpr Identifier)) :
    Except Format ((LExprT Identifier) × (TEnv Identifier)) := do
  let (et, T) ← fromLExprAux T e
  .ok (LExprT.applySubst et T.state.substInfo.subst, T)

protected def fromLExprs (T : (TEnv Identifier)) (es : List (LExpr Identifier)) :
    Except Format (List (LExprT Identifier) × (TEnv Identifier)) := do
  match es with
  | [] => .ok ([], T)
  | e :: erest =>
    let (et, T) ← LExprT.fromLExpr T e
    let (erestt, T) ← LExprT.fromLExprs T erest
    .ok ((et :: erestt), T)

end LExprT

---------------------------------------------------------------------

/--
Annotate an `LExpr e` with inferred monotypes.
-/
def LExpr.annotate (T : (TEnv Identifier)) (e : (LExpr Identifier)) :
    Except Format ((LExpr Identifier) × (TEnv Identifier)) := do
  let (e_a, T) ← LExprT.fromLExpr T e
  return (LExprT.toLExpr e_a, T)

/--
Apply type substitution `S` to `LExpr e`.
-/
def LExpr.applySubst (e : (LExpr Identifier)) (S : Subst) : (LExpr Identifier) :=
  match e with
  | .const c ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .const c ty
  | .op o ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .op o ty
  | .fvar x ty =>
      match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .fvar x ty
  | .bvar _ => e
  | .abs ty e => .abs ty (e.applySubst S)
  | .quant qk ty e => .quant qk ty (e.applySubst S)
  | .app e1 e2 => .app (e1.applySubst S) (e2.applySubst S)
  | .ite c t f => .ite (c.applySubst S) (t.applySubst S) (f.applySubst S)
  | .eq e1 e2 => .eq (e1.applySubst S) (e2.applySubst S)
  | .mdata m e => .mdata m (e.applySubst S)

---------------------------------------------------------------------

end Lambda

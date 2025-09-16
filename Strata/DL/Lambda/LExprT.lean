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

variable {T : LExprParams} [ToString T.Identifier] [DecidableEq T.Identifier] [ToFormat T.Identifier] [HasGen T.Identifier]

abbrev LExprT (T : LExprParamsT) :=
  LExpr (LExprParamsT.typed T)

partial def LExprT.format {T : LExprParamsT} [ToFormat T.base.Identifier] (et : LExprT T) : Std.Format :=
  match et with
  | .const m c _ => f!"(#{c} : {m.type})"
  | .op m o _ => f!"(~{o} : {m.type})"
  | .bvar m i => f!"(%{i} : {m.type})"
  | .fvar m x _ => f!"({x} : {m.type})"
  | .abs m _ e => f!"((λ {LExprT.format e}) : {m.type})"
  | .quant _ .all argTy _ e => f!"(∀({argTy}) {LExprT.format e})"
  | .quant _ .exist argTy _ e => f!"(∃({argTy}) {LExprT.format e})"
  | .app m e1 e2 => f!"({LExprT.format e1} {LExprT.format e2}) : {m.type})"
  | .ite m c t f => f!"(if {LExprT.format c} then \
                            {LExprT.format t} else \
                            {LExprT.format f}) : {m.type})"
  | .eq m e1 e2 => f!"({LExprT.format e1} == {LExprT.format e2}) : {m.type})"

instance {T : LExprParamsT} [ToFormat T.base.Identifier] : ToFormat (LExprT T) where
  format := LExprT.format

---------------------------------------------------------------------

namespace LExpr

/--
Obtain the monotype from `LExprT e`.
-/
def toLMonoTy {T : LExprParamsT} (e : LExprT T) : LMonoTy :=
  match e with
  | .const m _ _ | .op m _ _ | .bvar m _ | .fvar m _ _
  | .app m _ _ | .abs m _ _ | .ite m _ _ _ | .eq m _ _ => m.type
  | .quant _ _ _ _ _ => LMonoTy.bool

/--
Remove any type annotation stored in metadata for all
expressions, except the constants `.const`s, `.op`s, and free variables
`.fvar`s.
-/
def unresolved {T : LExprParamsT} (e : LExprT T) : LExpr T.base.mono :=
  match e with
  | .const m c _ => .const m.underlying c (some m.type)
  | .op m o _ => .op m.underlying o (some m.type)
  | .bvar m b => .bvar m.underlying b
  | .fvar m f _ => .fvar m.underlying f (some m.type)
  | .app m e1 e2 =>
    .app m.underlying e1.unresolved e2.unresolved
  | .abs ⟨underlying, .arrow aty _⟩ _ e =>
    .abs underlying (some aty) e.unresolved
  | .abs m t e => .abs m.underlying t e.unresolved
  -- Since quantifiers are bools, the type stored in their
  -- metadata is the type of the argument
  | .quant m qk _ tr e => .quant m.underlying qk (some m.type) tr.unresolved e.unresolved
  | .ite m c t f => .ite m.underlying c.unresolved t.unresolved f.unresolved
  | .eq m e1 e2 => .eq m.underlying e1.unresolved e2.unresolved

/--
Transform metadata in an expression using a callback function.
-/
def replaceMetadata {T : LExprParamsT} (e : LExprT T) (f : T.typed.base.Metadata → T.typed.base.Metadata) : LExprT T :=
  match e with
  | .const m c uty =>
    .const (f m) c uty
  | .op m o uty =>
    .op (f m) o uty
  | .bvar m b =>
    .bvar (f m) b
  | .fvar m x uty =>
    .fvar (f m) x uty
  | .app m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .app (f m) e1 e2
  | .abs m uty e =>
    let e := replaceMetadata e f
    .abs (f m) uty e
  | .quant m qk argTy tr e =>
    let e := replaceMetadata e f
    let tr := replaceMetadata tr f
    .quant (f m) qk argTy tr e
  | .ite m c t f_expr =>
    let c := replaceMetadata c f
    let t := replaceMetadata t f
    let f_expr := replaceMetadata f_expr f
    .ite (f m) c t f_expr
  | .eq m e1 e2 =>
    let e1 := replaceMetadata e1 f
    let e2 := replaceMetadata e2 f
    .eq (f m) e1 e2

/--
Apply type substitution `S` to `LExprT e`.
-/
def applySubst {T : LExprParamsT} (e : LExprT T) (S : Subst) : LExprT T :=
  replaceMetadata e (fun m: T.typed.base.Metadata => {m with type := LMonoTy.subst S m.type})

---------------------------------------------------------------------

/-- Infer the type of `.fvar x fty`. -/
def inferFVar (Env : TEnv T.Identifier) (x : T.Identifier) (fty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T.Identifier)) :=
  match Env.context.types.find? x with
  | none => .error f!"Cannot find this fvar in the context! \
                      {x}"
  | some ty => do
    let (ty, Env) ← LTy.instantiateWithCheck ty Env
    match fty with
    | none => .ok (ty, Env)
    | some fty =>
      -- We do not support expressions to be annotated with type synonyms yet.
      -- As such, if `fty` is a synonym, then the following may raise an error.
      let S ← Constraints.unify [(fty, ty)] Env.state.substInfo
      .ok (ty, TEnv.updateSubst Env S)

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
def inferConst (Env : TEnv T.Identifier) (c : String) (cty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T.Identifier)) :=
  open LTy.Syntax in
  match c, cty with
  -- Annotated Booleans
  | "true", some LMonoTy.bool | "false", some LMonoTy.bool => .ok (mty[bool], Env)
  -- Unannotated Booleans: note that `(.const "true" none)` and
  -- `(.const "false" none)` will be interpreted as booleans.
  | "true", none | "false", none =>
    if { name := "bool" } ∈ Env.knownTypes then
      .ok (mty[bool], Env)
    else
      .error f!"Booleans are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {Env.knownTypes}"
  -- Annotated Integers
  | c, some LMonoTy.int =>
    if { name := "int" } ∈ Env.knownTypes then
      if c.isInt then .ok (mty[int], Env)
                 else .error f!"Constant annotated as an integer, but it is not.\n\
                                {c}"
    else
      .error f!"Integers are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {Env.knownTypes}"
  -- Annotated Reals
  | c, some LMonoTy.real =>
    if { name := "real" } ∈ Env.knownTypes then
      .ok (mty[real], Env)
    else
      .error f!"Reals are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {Env.knownTypes}"
  -- Annotated BitVecs
  | c, some (LMonoTy.bitvec n) =>
    let ty := LMonoTy.bitvec n
    if { name := "bitvec", arity := 1 } ∈ Env.knownTypes then
      (.ok (ty, Env))
    else
      .error f!"Bit vectors of size {n} are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {Env.knownTypes}"
  -- Annotated Strings
  | c, some LMonoTy.string =>
    if { name := "string" } ∈ Env.knownTypes then
      .ok (mty[string], Env)
    else
      .error f!"Strings are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {Env.knownTypes}"
  | _, _ =>
  -- Unannotated Integers
    if c.isInt then
      if { name := "int" } ∈ Env.knownTypes then
        .ok (mty[int], Env)
      else
        .error f!"Integers are not registered in the known types.\n\
                  Constant {c}\n\
                  Known Types: {Env.knownTypes}"
    else
      .error f!"Cannot infer the type of this constant: \
                {c}"

mutual
partial def fromLExprAux (Env : TEnv T.Identifier) (e : LExpr T.mono) :
    Except Format (LExprT T.mono × (TEnv T.Identifier)) :=
  open LTy.Syntax in do
  match e with

  | .const m c cty =>
    let (ty, TEnv) ← inferConst Env c cty
    .ok (.const ⟨m, ty⟩ c cty, Env)
  | .op m o oty =>
    let (ty, Env) ← inferOp Env o oty
    .ok (.op ⟨m, ty⟩ o oty, Env)
  | .bvar _ _ => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar m x fty =>
    let (ty, Env) ← inferFVar Env x fty
    .ok (.fvar ⟨m, ty⟩ x ty, Env)
  | .app m e1 e2   => fromLExprAux.app Env e1 e2
  | .abs m ty e    => fromLExprAux.abs Env ty e
  | .quant m qk ty tr e => fromLExprAux.quant Env qk ty tr e
  | .eq m e1 e2    => fromLExprAux.eq Env e1 e2
  | .ite m c th el => fromLExprAux.ite Env m c th el

/-- Infer the type of an operation `.op o oty`, where an operation is defined in
  the factory. -/
partial def inferOp (Env : TEnv T.Identifier) (o : T.Identifier) (oty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T.Identifier)) :=
  open LTy.Syntax in
  match Env.functions.find? (fun fn => fn.name == o) with
  | none =>
    .error f!"Cannot infer the type of this operation: \
              {o}"
  | some func => do
      -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
      -- where there are duplicates in the formals, etc.).
      let type ← func.type
      let (ty, Env) ← LTy.instantiateWithCheck type Env
      let Env ←
        match func.body with
        | none => .ok Env
        | some body =>
          if body.freeVars.idents.all (fun k => k ∈ func.inputs.keys) then
            -- Temporarily add formals in the context.
            let Env := Env.pushEmptyContext
            let Env := Env.addToContext func.inputPolyTypes
            -- Type check the body and ensure that it unifies with the return type.
            -- let (bodyty, Env) ← infer Env body
            let (body_typed, Env) ← fromLExprAux Env body
            let bodyty := body_typed.toLMonoTy
            let (retty, Env) ← func.outputPolyType.instantiateWithCheck Env
            let S ← Constraints.unify [(retty, bodyty)] Env.state.substInfo
            let Env := Env.updateSubst S
            let Env := Env.popContext
            .ok Env
          else
            .error f!"Function body contains free variables!\n\
                      {func}"
      match oty with
      | none => .ok (ty, Env)
      | some cty =>
        let (optTyy, Env) := (cty.resolveAliases Env)
        let S ← Constraints.unify [(ty, optTyy.getD cty )] Env.state.substInfo
        .ok (ty, Env.updateSubst S)

partial def fromLExprAux.ite (Env : TEnv T.Identifier) (m : T.Metadata) (c th el : LExpr ⟨T, LMonoTy⟩) := do
  let (ct, Env) ← fromLExprAux Env c
  let (tt, Env) ← fromLExprAux Env th
  let (et, Env) ← fromLExprAux Env el
  let cty := ct.toLMonoTy
  let tty := tt.toLMonoTy
  let ety := et.toLMonoTy
  let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] Env.state.substInfo
  .ok (.ite ⟨m, tty⟩ ct tt et, Env.updateSubst S)

partial def fromLExprAux.eq (Env : TEnv T.Identifier) (e1 e2 : LExpr T.mono) := do
  -- `.eq A B` is well-typed if there is some instantiation of
  -- type parameters in `A` and `B` that makes them have the same type.
  let (e1t, Env) ← fromLExprAux Env e1
  let (e2t, Env) ← fromLExprAux Env e2
  let ty1 := e1t.toLMonoTy
  let ty2 := e2t.toLMonoTy
  let S ← Constraints.unify [(ty1, ty2)] Env.state.substInfo
  .ok (.eq e1t e2t LMonoTy.bool, TEnv.updateSubst Env S)

partial def fromLExprAux.abs (Env : TEnv T.Identifier) (oty : Option LMonoTy) (e : (LExpr T.mono)) := do
  let (xv, Env) := HasGen.genVar Env
  let (xt', Env) := TEnv.genTyVar Env
  let xt := .forAll [] (.ftvar xt')
  let Env := Env.insertInContext xv xt
  let e' := LExpr.varOpen 0 (xv, some (.ftvar xt')) e
  let (et, Env) ← fromLExprAux Env e'
  let ety := et.toLMonoTy
  let etclosed := .varClose 0 xv et
  let Env := Env.eraseFromContext xv
  let ty := (.tcons "arrow" [(.ftvar xt'), ety])
  let mty := LMonoTy.subst Env.state.substInfo.subst ty
  match mty, oty with
  | .arrow aty _, .some ty =>
    if aty == ty
    then .ok ()
    else .error "Type annotation on LTerm.abs doesn't match inferred argument type"
  | _, _ => .ok ()
  .ok (.abs etclosed mty, Env)

partial def fromLExprAux.quant (Env : TEnv T.Identifier) (qk : QuantifierKind) (oty : Option LMonoTy) (triggers : LExpr T.mono) (e : (LExpr T.mono)) := do
  let (xv, Env) := HasGen.genVar Env
  let (xt', Env) := TEnv.genTyVar Env
  let xt := .forAll [] (.ftvar xt')
  let S ← match oty with
  | .some ty =>
    let (optTyy, Env) := (ty.resolveAliases Env)
    (Constraints.unify [(.ftvar xt', optTyy.getD ty)] Env.state.substInfo)
  | .none =>
    .ok Env.state.substInfo
  let Env := TEnv.updateSubst Env S
  let Env := Env.insertInContext xv xt
  let e' := LExpr.varOpen 0 (xv, some (.ftvar xt')) e
  let triggers' := LExpr.varOpen 0 (xv, some (.ftvar xt')) triggers
  let (et, Env) ← fromLExprAux Env e'
  let (triggersT, Env) ← fromLExprAux Env triggers'
  let ety := et.toLMonoTy
  let mty := LMonoTy.subst Env.state.substInfo.subst (.ftvar xt')
  match oty with
  | .some ty =>
    let (optTyy, _) := (ty.resolveAliases Env)
    if optTyy.getD ty == mty
    then .ok ()
    else .error f!"Type annotation on LTerm.quant {ty} (alias for {optTyy.getD ty}) doesn't match inferred argument type"
  | _ => .ok ()
  if ety = LMonoTy.bool then do
    let etclosed := .varClose 0 xv et
    let triggersClosed := .varClose 0 xv triggersT
    let Env := Env.eraseFromContext xv
    .ok (.quant qk mty triggersClosed etclosed, Env)
  else
    .error f!"Quantifier body has non-Boolean type: {ety}"

partial def fromLExprAux.app (Env : TEnv T.Identifier) (e1 e2 : LExpr T.mono) := do
  let (e1t, Env) ← fromLExprAux Env e1
  let ty1 := e1t.toLMonoTy
  let (e2t, Env) ← fromLExprAux Env e2
  let ty2 := e2t.toLMonoTy
  let (fresh_name, Env) := TEnv.genTyVar Env
  let freshty := (.ftvar fresh_name)
  let (optTyy1, Env) := (ty1.resolveAliases Env)
  let (optTyy2, Env) := (ty2.resolveAliases Env)
  -- Batch all unification constraints
  let constraints := [
    (ty1, optTyy1.getD ty1),
    (ty2, optTyy2.getD ty2),
    (ty1, (.tcons "arrow" [ty2, freshty]))
  ]
  let S ← Constraints.unify constraints Env.state.substInfo
  let mty := LMonoTy.subst S.subst freshty
  .ok (.app e1t e2t mty, TEnv.updateSubst Env S)

protected partial def fromLExpr (Env : TEnv T.Identifier) (e : LExpr T.mono) :
    Except Format ((LExprT T.mono) × (TEnv T.Identifier)) := do
  let (et, Env) ← fromLExprAux Env e
  .ok (LExprT.applySubst et Env.state.substInfo.subst, Env)

end

protected def fromLExprs (Env : TEnv T.Identifier) (es : List (LExpr T.mono)) :
    Except Format (List (LExprT T.mono) × (TEnv T.Identifier)) := do
  go Env es []
  where
    go (Env : TEnv T.Identifier) (rest : List (LExpr T.mono))
        (acc : List (LExprT T.mono)) := do
      match rest with
      | [] => .ok (acc.reverse, Env)
      | e :: erest =>
        let (et, T) ← fromLExpr Env e
        go T erest (et :: acc)

end LExpr

---------------------------------------------------------------------

/--
Annotate an `LExpr e` with inferred monotypes.
-/
def LExpr.annotate (T : TEnv T.Identifier) (e : (LExpr T.mono)) :
    Except Format ((LExpr T.mono) × (TEnv T.Identifier)) := do
  let (e_a, T) ← LExprT.fromLExpr T e
  return (LExprT.toLExpr e_a, T)

/--
Apply type substitution `S` to `LExpr e`.
-/
def LExpr.applySubst (e : (LExpr T.mono)) (S : Subst) : (LExpr T.mono) :=
  match e with
  | .const c ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .const () c (some ty)
  | .op o ty =>
    match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .op () o (some ty)
  | .fvar x ty =>
      match ty with
    | none => e
    | some ty =>
      let ty := LMonoTy.subst S ty
      .fvar () x (some ty)
  | .bvar _ => e
  | .abs m ty e => .abs m ty (e.applySubst S)
  | .quant m qk ty tr e => .quant m qk ty (tr.applySubst S) (e.applySubst S)
  | .app m e1 e2 => .app m (e1.applySubst S) (e2.applySubst S)
  | .ite m c t f => .ite m (c.applySubst S) (t.applySubst S) (f.applySubst S)
  | .eq m e1 e2 => .eq m (e1.applySubst S) (e2.applySubst S)

---------------------------------------------------------------------

end Lambda

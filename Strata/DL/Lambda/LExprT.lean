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

variable {T : LExprParams} [ToString T.Identifier] [DecidableEq T.Identifier] [ToFormat T.Identifier] [HasGen T] [ToFormat (LFunc T)]

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
def replaceMetadata {T : LExprParamsT} (e : LExpr T) (f : T.base.Metadata → T.base.Metadata) : LExpr T :=
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

def replaceUserProvidedType {T : LExprParamsT} (e : LExpr T) (f : T.TypeType → T.TypeType) : LExpr T :=
  match e with
  | .const m c uty =>
    .const m c (uty.map f)
  | .op m o uty =>
    .op m o (uty.map f)
  | .bvar m b =>
    .bvar m b
  | .fvar m x uty =>
    .fvar m x (uty.map f)
  | .app m e1 e2 =>
    let e1 := replaceUserProvidedType e1 f
    let e2 := replaceUserProvidedType e2 f
    .app m e1 e2
  | .abs m uty e =>
    let e := replaceUserProvidedType e f
    .abs m (uty.map f) e
  | .quant m qk argTy tr e =>
    let e := replaceUserProvidedType e f
    let tr := replaceUserProvidedType tr f
    .quant m qk (argTy.map f) tr e
  | .ite m c t f_expr =>
    let c := replaceUserProvidedType c f
    let t := replaceUserProvidedType t f
    let f_expr := replaceUserProvidedType f_expr f
    .ite m c t f_expr
  | .eq m e1 e2 =>
    let e1 := replaceUserProvidedType e1 f
    let e2 := replaceUserProvidedType e2 f
    .eq m e1 e2

/--
Apply type substitution `S` to `LExpr e`.
This is only for user-defined types, not metadata-stored resolved types
If e is an LExprT whose metadata contains type information, use applySubstT
-/
def applySubst {T : LExprParams} (e : LExpr T.mono) (S : Subst) : LExpr T.mono :=
  replaceUserProvidedType e (fun t: LMonoTy => LMonoTy.subst S t)

/--
Apply type substitution `S` to `LExpr e`.
This is for metadata-stored types.
To change user-defined types, use applySubst
-/
def applySubstT (e : LExprT T.mono) (S : Subst) : LExprT T.mono :=
  LExpr.replaceMetadata e <|
    fun ⟨m, ty⟩ =>
      let ty := LMonoTy.subst S ty
      ⟨m, ty⟩


/--
This function turns some free variables into bound variables to build an
abstraction, given its body. `varCloseT k x e` keeps track of the number `k`
of abstractions that have passed by; it replaces all `(.fvar x)` with
`(.bvar k)` in an `LExprT e`.

Also see `LExpr.varClose` for an analogous function for `LExpr`s.
-/
protected def varCloseT (k : Nat) (x : T.Identifier) (e : (LExprT T.mono)) : (LExprT T.mono) :=
  match e with
  | .const m c ty => .const m c ty
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y yty => if (x == y) then (.bvar m k)
                                else (.fvar m y yty)
  | .abs m ty e' => .abs m ty (.varCloseT (k + 1) x e')
  | .quant m qk ty tr' e' => .quant m qk ty (.varCloseT (k + 1) x tr') (.varCloseT (k + 1) x e')
  | .app m e1 e2 => .app m (.varCloseT k x e1) (.varCloseT k x e2)
  | .ite m c t e => .ite m (.varCloseT k x c) (.varCloseT k x t) (.varCloseT k x e)
  | .eq m e1 e2 => .eq m (.varCloseT k x e1) (.varCloseT k x e2)

---------------------------------------------------------------------

/-- Infer the type of `.fvar x fty`. -/
def inferFVar (Env : TEnv T) (x : T.Identifier) (fty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T)) :=
  match Env.context.types.find? x with
  | none => .error f!"Cannot find this fvar in the context! \
                      {x}"
  | some ty => do
    let (ty, Env) ← LTy.instantiateWithCheck ty Env
    match fty with
    | none => .ok (ty, Env)
    | some fty =>
      let (fty, Env) ← LMonoTy.instantiateWithCheck fty Env
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
def inferConst (Env : TEnv T) (c : String) (cty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T)) :=
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
partial def fromLExprAux (Env : TEnv T) (e : LExpr T.mono) :
    Except Format (LExprT T.mono × (TEnv T)) :=
  open LTy.Syntax in do
  match e with

  | .const m c cty =>
    let (ty, Env) ← inferConst Env c cty
    .ok (.const ⟨m, ty⟩ c (.some ty), Env)
  | .op m o oty =>
    let (ty, Env) ← inferOp Env o oty
    .ok (.op ⟨m, ty⟩ o (.some ty), Env)
  | .bvar _ _ => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar m x fty =>
    let (ty, Env) ← inferFVar Env x fty
    .ok (.fvar ⟨m, ty⟩ x ty, Env)
  | .app m e1 e2   => fromLExprAux.app Env m e1 e2
  | .abs m ty e    => fromLExprAux.abs Env m ty e
  | .quant m qk ty tr e => fromLExprAux.quant Env m qk ty tr e
  | .eq m e1 e2    => fromLExprAux.eq Env m e1 e2
  | .ite m c th el => fromLExprAux.ite Env m c th el

/-- Infer the type of an operation `.op o oty`, where an operation is defined in
  the factory. -/
partial def inferOp (Env : TEnv T) (o : T.Identifier) (oty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T)) :=
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
      | some oty =>
        let (oty, Env) ← LMonoTy.instantiateWithCheck oty Env
        let S ← Constraints.unify [(ty, oty)] Env.state.substInfo
        .ok (ty, TEnv.updateSubst Env S)

partial def fromLExprAux.ite (Env : TEnv T) (m : T.Metadata) (c th el : LExpr ⟨T, LMonoTy⟩) := do
  let (ct, Env) ← fromLExprAux Env c
  let (tt, Env) ← fromLExprAux Env th
  let (et, Env) ← fromLExprAux Env el
  let cty := ct.toLMonoTy
  let tty := tt.toLMonoTy
  let ety := et.toLMonoTy
  let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] Env.state.substInfo
  .ok (.ite ⟨m, tty⟩ ct tt et, Env.updateSubst S)

partial def fromLExprAux.eq (Env : TEnv T) (m: T.Metadata) (e1 e2 : LExpr T.mono) := do
  -- `.eq A B` is well-typed if there is some instantiation of
  -- type parameters in `A` and `B` that makes them have the same type.
  let (e1t, Env) ← fromLExprAux Env e1
  let (e2t, Env) ← fromLExprAux Env e2
  let ty1 := e1t.toLMonoTy
  let ty2 := e2t.toLMonoTy
  let S ← Constraints.unify [(ty1, ty2)] Env.state.substInfo
  .ok (.eq ⟨m, LMonoTy.bool⟩ e1t e2t, TEnv.updateSubst Env S)

partial def fromLExprAux.abs (Env : TEnv T) (m: T.Metadata) (bty : Option LMonoTy) (e : LExpr T.mono) := do
  -- Generate a fresh expression variable to stand in for the bound variable
  let (xv, Env) := HasGen.genVar Env
  -- Generate a fresh type variable to stand in for the type of the bound
  -- variable.
  let (xt', Env) := TEnv.genTyVar Env
  let xmt := .ftvar xt'
  let xt := .forAll [] xmt
  let Env := Env.insertInContext xv xt
  -- Construct `e'` from `e`, where the bound variable has been replaced by
  -- `xv`.
  let e' := LExpr.varOpen 0 (xv, some xmt) e
  let (et, Env) ← fromLExprAux Env e'
  let ety := et.toLMonoTy
  let etclosed := .varClose 0 (xv, some xmt) et
  -- Safe to erase fresh variable from context after closing the expressions.
  let Env := Env.eraseFromContext xv
  let ty := (.tcons "arrow" [xmt, ety])
  let mty := LMonoTy.subst Env.state.substInfo.subst ty
  match bty with
  | none => .ok ((.abs ⟨m, mty⟩ bty etclosed), Env)
  | some bty =>
    let (bty, Env) ← LMonoTy.instantiateWithCheck bty Env
    let S ← Constraints.unify [(mty, bty)] Env.state.substInfo
    .ok (.abs ⟨m, mty⟩ bty etclosed, TEnv.updateSubst Env S)

partial def fromLExprAux.quant (Env : TEnv T) (m: T.Metadata) (qk : QuantifierKind) (bty : Option LMonoTy)
    (triggers e : LExpr T.mono) := do
  -- Generate a fresh variable to stand in for the bound variable.
  let (xv, Env) := HasGen.genVar Env
  -- Generate a fresh type variable to stand in for the type of the bound
  -- variable.
  let (xt', Env) := TEnv.genTyVar Env
  let xmt := Lambda.LMonoTy.ftvar xt'
  let xt := Lambda.LTy.forAll [] xmt
  let Env := Env.insertInContext xv xt
  -- Construct new expressions, where the bound variable has been replaced by
  -- `xv`.
  let e' := LExpr.varOpen 0 (xv, some xmt) e
  let triggers' := LExpr.varOpen 0 (xv, some xmt) triggers
  let (et, Env) ← fromLExprAux Env e'
  let (triggersT, Env) ← fromLExprAux Env triggers'
  let ety := et.toLMonoTy
  let mty := LMonoTy.subst Env.state.substInfo.subst xmt
  let etclosed := Lambda.LExpr.varClose (T:=T.typed) 0 (xv, some xmt) et
  let triggersClosed := Lambda.LExpr.varClose (T:=T.typed) 0 (xv, some xmt) triggersT
  -- Safe to erase fresh variable from context after closing the expressions.
  let Env := Env.eraseFromContext xv
  if ety != LMonoTy.bool then do
    .error f!"Quantifier body has non-Boolean type: {ety}"
  else
    match bty with
    | none => .ok (LExpr.quant ⟨m, mty⟩ qk bty triggersClosed etclosed, Env)
    | some bty =>
      let (bty, Env) ← LMonoTy.instantiateWithCheck bty Env
      let S ← Constraints.unify [(mty, bty)] Env.state.substInfo
      .ok (.quant ⟨m, mty⟩ qk bty triggersClosed etclosed, TEnv.updateSubst Env S)

partial def fromLExprAux.app (Env : TEnv T) (m: T.Metadata) (e1 e2 : LExpr T.mono) := do
  let (e1t, Env) ← fromLExprAux Env e1
  let ty1 := e1t.toLMonoTy
  let (e2t, Env) ← fromLExprAux Env e2
  let ty2 := e2t.toLMonoTy
  let (fresh_name, Env) := TEnv.genTyVar Env
  let freshty := (.ftvar fresh_name)
  let constraints := [(ty1, (.tcons "arrow" [ty2, freshty]))]
  let S ← Constraints.unify constraints Env.state.substInfo
  let mty := LMonoTy.subst S.subst freshty
  .ok (.app ⟨m, mty⟩ e1t e2t, TEnv.updateSubst Env S)

protected partial def fromLExpr (Env : TEnv T) (e : LExpr T.mono) :
    Except Format ((LExprT T.mono) × (TEnv T)) := do
  let (et, Env) ← fromLExprAux Env e
  .ok (LExpr.applySubstT et Env.state.substInfo.subst, Env)

end

protected def fromLExprs (Env : TEnv T) (es : List (LExpr T.mono)) :
    Except Format (List (LExprT T.mono) × (TEnv T)) := do
  go Env es []
  where
    go (Env : TEnv T) (rest : List (LExpr T.mono))
        (acc : List (LExprT T.mono)) := do
      match rest with
      | [] => .ok (acc.reverse, Env)
      | e :: erest =>
        let (et, T) ← LExpr.fromLExpr Env e
        go T erest (et :: acc)

end LExpr

---------------------------------------------------------------------

/--
Annotate an `LExpr e` with inferred monotypes.
-/
def LExpr.annotate (Env : TEnv T) (e : (LExpr T.mono)) :
    Except Format ((LExpr T.mono) × (TEnv T)) := do
  let (e_a, Env) ← LExpr.fromLExpr Env e
  return (unresolved e_a, Env)

---------------------------------------------------------------------

end Lambda

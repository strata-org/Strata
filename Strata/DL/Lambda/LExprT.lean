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

variable {T : LExprParams} [ToString T.IDMeta] [DecidableEq T.IDMeta] [ToFormat T.IDMeta] [HasGen T.IDMeta] [ToFormat (LFunc T)]

abbrev LExprT (T : LExprParamsT) :=
  LExpr (LExprParamsT.typed T)

partial def LExprT.format {T : LExprParamsT} [ToFormat T.base.IDMeta] (et : LExprT T) : Std.Format :=
  match et with
  | .const m c => f!"(#{c} : {m.type})"
  | .op m o _ => f!"(~{o} : {m.type})"
  | .bvar m i => f!"(%{i} : {m.type})"
  | .fvar m x _ => f!"({x} : {m.type})"
  | .abs m _ e => f!"((λ {LExprT.format e}) : {m.type})"
  | .quant m .all _ _ e => f!"(∀({m.type}) {LExprT.format e})"
  | .quant m .exist _ _ e => f!"(∃({m.type}) {LExprT.format e})"
  | .app m e1 e2 => f!"({LExprT.format e1} {LExprT.format e2}) : {m.type})"
  | .ite m c t f => f!"(if {LExprT.format c} then \
                            {LExprT.format t} else \
                            {LExprT.format f}) : {m.type})"
  | .eq m e1 e2 => f!"({LExprT.format e1} == {LExprT.format e2}) : {m.type})"

instance (priority := high) {T : LExprParamsT} [ToFormat T.base.IDMeta] : ToFormat (LExprT T) where
  format := LExprT.format

-- More specific instance that matches when the metadata is explicitly Typed
instance (priority := high) {M : Type} {IDMeta : Type} [ToFormat IDMeta] : ToFormat (LExpr ⟨⟨Typed M, IDMeta⟩, LMonoTy⟩) where
  format e := LExprT.format (T := ⟨⟨M, IDMeta⟩, LMonoTy⟩) e

---------------------------------------------------------------------

namespace LExpr

/--
Obtain the monotype from `LExprT e`.
-/
def toLMonoTy {T : LExprParamsT} (e : LExprT T) : LMonoTy :=
  match e with
  | .const m _ | .op m _ _ | .bvar m _ | .fvar m _ _
  | .app m _ _ | .abs m _ _ | .ite m _ _ _ | .eq m _ _ => m.type
  | .quant _ _ _ _ _ => LMonoTy.bool

/--
Remove any type annotation stored in metadata for all
expressions, except the `.op`s and free variables
`.fvar`s.
-/
def unresolved {T : LExprParamsT} (e : LExprT T) : LExpr T.base.mono :=
  match e with
  | .const m c => .const m.underlying c
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

def replaceUserProvidedType {T : LExprParamsT} (e : LExpr T) (f : T.TypeType → T.TypeType) : LExpr T :=
  match e with
  | .const m c =>
    .const m c
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
  LExpr.replaceMetadata (T:=T.mono.typed) (NewMetadata:=T.mono.typed.base.Metadata) e <|
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
  | .const m c => .const m c
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

/--
Generate a fresh identifier `xv` for a bound variable. Use the type annotation
`ty` if present, otherwise generate a fresh type variable. Add `xv` along with
its type to the type context.
-/
def typeBoundVar (C: LContext T) (Env : TEnv T.IDMeta) (ty : Option LMonoTy) :
  Except Format (T.Identifier × LMonoTy × TEnv T.IDMeta) := do
  let (xv, Env) := liftGenEnv HasGen.genVar Env
  let (xty, Env) ← match ty with
    | some bty =>
      let ans := LMonoTy.instantiateWithCheck bty C Env
      match ans with
      | .error e => .error e
      | .ok (bty, Env) => .ok (bty, Env)
    | none =>
      let (xtyid, Env) := TEnv.genTyVar Env
      let xty := (LMonoTy.ftvar xtyid)
      .ok (xty, Env)
  let Env := Env.addInNewestContext [(xv, (.forAll [] xty))]
  return (xv, xty, Env)

/-- Infer the type of `.fvar x fty`. -/
def inferFVar (C: LContext T) (Env : TEnv T.IDMeta) (x : T.Identifier) (fty : Option LMonoTy) :
  Except Format (LMonoTy × (TEnv T.IDMeta)) :=
  match Env.context.types.find? x with
  | none => .error f!"Cannot find this fvar in the context! \
                      {x}"
  | some ty => do
    let (ty, Env) ← LTy.instantiateWithCheck ty C Env
    match fty with
    | none => .ok (ty, Env)
    | some fty =>
      let (fty, Env) ← LMonoTy.instantiateWithCheck fty C Env
      let S ← Constraints.unify [(fty, ty)] Env.stateSubstInfo |>.mapError format
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
def inferConst (C: LContext T) (Env : TEnv T.IDMeta) (c : LConst) :
  Except Format (LMonoTy × (TEnv T.IDMeta)) :=
  if C.knownTypes.containsName c.tyName then
    .ok (c.ty, Env)
  else .error (c.tyNameFormat ++ f!" are not registered in the known types.\n\
                Don't know how to interpret the following constant:\n\
                {c}\n\
                Known Types: {C.knownTypes}")

def resolveAux (C: LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono) :
    Except Format (LExprT T.mono × TEnv T.IDMeta) :=
  open LTy.Syntax in do
  match e with
  | .const m c =>
    let (ty, Env) ← inferConst C Env c
    .ok (.const ⟨m, ty⟩ c, Env)
  | .op m o oty =>
    /- Infer the type of an operation `.op o oty`, where an operation is defined in
      the factory. -/
    let (ty, Env) ← do
      match C.functions.find? (fun fn => fn.name == o) with
      | none =>
        .error f!"{toString $ C.functions.getFunctionNames} Cannot infer the type of this operation: \
                  {o}"
      | some func => do
          -- `LFunc.type` below will also catch any ill-formed functions (e.g.,
          -- where there are duplicates in the formals, etc.).
          let type ← func.type
          let (ty, Env) ← LTy.instantiateWithCheck type C Env
          match oty with
          | none => .ok (ty, Env)
          | some oty =>
            let (oty, Env) ← LMonoTy.instantiateWithCheck oty C Env
            let S ← Constraints.unify [(ty, oty)] Env.stateSubstInfo |>.mapError format
            .ok (ty, TEnv.updateSubst Env S)
    .ok (.op ⟨m, ty⟩ o (.some ty), Env)

  | .bvar _ _ => .error f!"Cannot infer the type of this bvar: {e}"
  | .fvar m x fty =>
    let (ty, Env) ← inferFVar C Env x fty
    .ok (.fvar ⟨m, ty⟩ x ty, Env)

  | .app m e1 e2   =>
    let (e1t, Env) ← resolveAux C Env e1
    let ty1 := e1t.toLMonoTy
    let (e2t, Env) ← resolveAux C Env e2
    let ty2 := e2t.toLMonoTy
    -- `freshty` is the type variable whose identifier is `fresh_name`. It denotes
    -- the type of `(.app e1 e2)`.
    let (fresh_name, Env) := TEnv.genTyVar Env
    let freshty := (.ftvar fresh_name)
    -- `ty1` must be of the form `ty2 → freshty`.
    let constraints := [(ty1, (.tcons "arrow" [ty2, freshty]))]
    let S ← Constraints.unify constraints Env.stateSubstInfo |>.mapError format
    let mty := LMonoTy.subst S.subst freshty
    -- `freshty` can now be safely removed from the substitution list.
    have hWF : SubstWF (Maps.remove S.subst fresh_name) := by
      apply @SubstWF_of_remove S.subst fresh_name S.isWF
    let S := { S with subst := S.subst.remove fresh_name, isWF := hWF }
    .ok (.app ⟨m, mty⟩ e1t e2t, TEnv.updateSubst Env S)

  | .abs m bty e    =>
    -- Generate a fresh expression variable to stand in for the bound variable
    -- For the bound variable, use type annotation if present. Otherwise,
    -- generate a fresh type variable.
    let (xv, xty, Env) ← typeBoundVar C Env bty
    -- Construct `e'` from `e`, where the bound variable has been replaced by
    -- `xv`.
    let e' := LExpr.varOpen 0 (xv, some xty) e
    have He'_size: (varOpen 0 (xv, some xty) e).sizeOf < 2 + e.sizeOf := by
      rw [varOpen_sizeOf]
      omega
    let (et, Env) ← resolveAux C Env e'
    let etclosed := .varCloseT 0 xv et
    let ety := etclosed.toLMonoTy
    let mty := LMonoTy.subst Env.stateSubstInfo.subst (.tcons "arrow" [xty, ety])
    -- Safe to erase fresh variable from context after closing the expressions.
    -- Note that we don't erase `xty` (if it was a fresh type variable) from the substitution
    -- list because it may occur in `etclosed`, which hasn't undergone a
    -- substitution. We could, of course, substitute `xty` in `etclosed`, but
    -- that'd require crawling over that expression, which could be expensive.
    let Env := Env.eraseFromContext xv
    .ok ((.abs ⟨m, mty⟩ bty etclosed), Env)

  | .quant m qk bty triggers e =>
    let (xv, xty, Env) ← typeBoundVar C Env bty
    let e' := LExpr.varOpen 0 (xv, some xty) e
    have He'_size: (varOpen 0 (xv, some xty) e).sizeOf < 2 + e.sizeOf := by
      rw [varOpen_sizeOf]
      omega

    let triggers' := LExpr.varOpen 0 (xv, some xty) triggers
    have He'_size_w_trigger:
      (varOpen 0 (xv, some xty) triggers).sizeOf < 3 + e.sizeOf + triggers.sizeOf := by
      rw [varOpen_sizeOf]
      omega

    let (et, Env) ← resolveAux C Env e'
    let (triggersT, Env) ← resolveAux C Env triggers'
    let ety := et.toLMonoTy
    let xty := LMonoTy.subst Env.stateSubstInfo.subst xty
    let etclosed := Lambda.LExpr.varCloseT 0 xv et
    let triggersClosed := Lambda.LExpr.varCloseT 0 xv triggersT
    -- Safe to erase fresh variable from context after closing the expressions.
    -- Again, as in `abs`, we do not erase `xty` (if it was a fresh variable) from the
    -- substitution list.
    let Env := Env.eraseFromContext xv
    if ety != LMonoTy.bool then do
      .error f!"Quantifier body has non-Boolean type: {ety}"
    else
      .ok (.quant ⟨m, xty⟩ qk xty triggersClosed etclosed, Env)

  | .eq m e1 e2    =>
    -- `.eq A B` is well-typed if there is some instantiation of
    -- type parameters in `A` and `B` that makes them have the same type.
    let (e1t, Env) ← resolveAux C Env e1
    let (e2t, Env) ← resolveAux C Env e2
    let ty1 := e1t.toLMonoTy
    let ty2 := e2t.toLMonoTy
    let S ← Constraints.unify [(ty1, ty2)] Env.stateSubstInfo |>.mapError format
    .ok (.eq ⟨m, LMonoTy.bool⟩ e1t e2t, TEnv.updateSubst Env S)

  | .ite m c th el =>
    let (ct, Env) ← resolveAux C Env c
    let (tt, Env) ← resolveAux C Env th
    let (et, Env) ← resolveAux C Env el
    let cty := ct.toLMonoTy
    let tty := tt.toLMonoTy
    let ety := et.toLMonoTy
    let S ← Constraints.unify [(cty, LMonoTy.bool), (tty, ety)] Env.stateSubstInfo |>.mapError format
    .ok (.ite ⟨m, tty⟩ ct tt et, Env.updateSubst S)

  termination_by e.sizeOf

protected def resolve (C: LContext T) (Env : TEnv T.IDMeta) (e : LExpr T.mono) :
    Except Format (LExprT T.mono × TEnv T.IDMeta) := do
  let (et, Env) ← resolveAux C Env e
  .ok (LExpr.applySubstT et Env.stateSubstInfo.subst, Env)


protected def resolves (C: LContext T) (Env : TEnv T.IDMeta) (es : List (LExpr T.mono)) :
    Except Format (List (LExprT T.mono) × TEnv T.IDMeta) := do
  go Env es []
  where
    go (Env : TEnv T.IDMeta) (rest : List (LExpr T.mono))
        (acc : List (LExprT T.mono)) := do
      match rest with
      | [] => .ok (acc.reverse, Env)
      | e :: erest =>
        let (et, T) ← LExpr.resolve C Env e
        go T erest (et :: acc)

end LExpr

---------------------------------------------------------------------

/--
Annotate an `LExpr e` with inferred monotypes.
-/
def LExpr.annotate (C: LContext T) (Env : TEnv T.IDMeta) (e : (LExpr T.mono)) :
    Except Format (LExpr T.mono × TEnv T.IDMeta) := do
  let (e_a, Env) ← LExpr.resolve C Env e
  return (unresolved e_a, Env)

---------------------------------------------------------------------

end Lambda

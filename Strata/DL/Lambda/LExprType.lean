/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.LTyMatch
import Strata.Util.ListMapProps

/-! ## Lambda Expression Typing -/

namespace Lambda

open Strata

public section

/--
Apply type substitution `S` to all type annotations in an `LExpr`.
This is only for user-defined types, not metadata-stored resolved types.
If e is an LExprT whose metadata contains type information, use applySubstT.
-/
def LExpr.applyTypeSubst {T : LExprParams} (e : LExpr T.mono) (S : Subst) : LExpr T.mono :=
  if S.hasEmptyScopes then e else replaceUserProvidedType e (LMonoTy.subst S)

/-- Apply type substitution `S` to every type of `f`: its input and output
types and the type annotations of its body, axioms, preconditions and measure.
Its name and type parameters are unchanged. -/
def LFuncDefined.applyTypeSubst {T : LExprParams} (f : LFuncDefined T) (S : Subst) :
    LFuncDefined T :=
  { f with
    inputs := f.inputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)),
    output := LMonoTy.subst S f.output,
    body := f.body.map (·.applyTypeSubst S),
    axioms := f.axioms.map (·.applyTypeSubst S),
    preconditions := f.preconditions.map (fun p => { p with expr := p.expr.applyTypeSubst S }),
    measure := f.measure.map (·.applyTypeSubst S) }

/-- A type substitution keeps a function's input names. It sits beside the
definition because this module has no companion `Props` file. -/
theorem LFuncDefined.applyTypeSubst_inputs_keys {T : LExprParams} (f : LFuncDefined T)
    (S : Subst) : (LFuncDefined.applyTypeSubst f S).inputs.keys = f.inputs.keys :=
  ListMap.keys_map_values _ _

/-- The type variables of the signature of `f`: its type parameters and the free type
variables of its output and input types. -/
def LFuncDefined.sigTyVars {T : LExprParams} (f : LFuncDefined T) : List String :=
  f.typeArgs ++ f.output.freeVars ++ f.inputs.flatMap (fun (_, mty) => mty.freeVars)

/-- The types written in the annotations of `f`'s expressions. -/
def LFuncDefined.annotTys {T : LExprParams} (f : LFuncDefined T) :
    List LMonoTy :=
  f.exprs.flatMap exprAnnotTys

/-- The type variables `f` mentions, given the types `annot` it writes:
those of its signature (`sigTyVars`) and those of `annot`. -/
def LFuncDefined.mentionedTyVarsIn {T : LExprParams} (f : LFuncDefined T)
    (annot : List LMonoTy) : List String :=
  f.sigTyVars ++ annot.flatMap LMonoTy.freeVars

/-- The type variables `f` mentions in its signature and annotations. -/
def LFuncDefined.mentionedTyVars {T : LExprParams} (f : LFuncDefined T) : List String :=
  f.mentionedTyVarsIn f.annotTys

/-- The type parameters `typeArgs` with `a` renamed to `n` for each pair `(a, n)` of `ren`; a
parameter `ren` does not list keeps its name. -/
def renameTyArgList (ren : List (String × String)) (typeArgs : List String) : List String :=
  typeArgs.map fun a => (ren.lookup a).getD a

/-- `f` with its type parameters renamed by `ren` throughout, as
`renameTyArgList` does to the parameter list. -/
def LFuncDefined.renameTypeArgs {T : LExprParams} (f : LFuncDefined T)
    (ren : List (String × String)) : LFuncDefined T :=
  { LFuncDefined.applyTypeSubst f (Subst.ofRenaming ren) with
    typeArgs := renameTyArgList ren f.typeArgs }

/-- Renaming type parameters keeps a function's name. -/
theorem LFuncDefined.renameTypeArgs_name {T : LExprParams} (f : LFuncDefined T)
    (ren : List (String × String)) : (f.renameTypeArgs ren).name = f.name := by
  unfold LFuncDefined.renameTypeArgs LFuncDefined.applyTypeSubst
  rfl

/-- Renaming type parameters keeps a function's input names. -/
theorem LFuncDefined.renameTypeArgs_inputs_keys {T : LExprParams} (f : LFuncDefined T)
    (ren : List (String × String)) : (f.renameTypeArgs ren).inputs.keys = f.inputs.keys :=
  LFuncDefined.applyTypeSubst_inputs_keys _ _

/-- Typecheck an annotated `LExpr`, returning `some τ` if well-typed, `none`
otherwise. `ctx` maps de Bruijn indices to their types from enclosing
binders. -/
@[expose]
def LExpr.typeCheck {T : LExprParams} (ctx : List LMonoTy) : LExpr T.mono → Option LMonoTy
  | .const _ c => if c.wt then some c.ty else none
  | .op _ _ (some ty) => some ty
  | .op _ _ none => none
  | .fvar _ _ (some ty) => some ty
  | .fvar _ _ none => none
  | .bvar _ i => ctx[i]?
  | .abs _ _ (some aty) body => do
    let rty ← typeCheck (aty :: ctx) body
    some (.arrow aty rty)
  | .abs _ _ none _ => none
  | .quant _ _ _ (some qty) tr body => do
    let _ ← typeCheck (qty :: ctx) tr
    let bty ← typeCheck (qty :: ctx) body
    guard (bty == .bool)
    some .bool
  | .quant _ _ _ none _ _ => none
  | .app _ fn arg => do
    let fty ← typeCheck ctx fn
    let aty ← typeCheck ctx arg
    let (dom, cod) ← fty.isArrow
    guard (dom == aty)
    some cod
  | .ite _ c t e => do
    let cty ← typeCheck ctx c
    let tty ← typeCheck ctx t
    let ety ← typeCheck ctx e
    guard (cty == .bool)
    guard (tty == ety)
    some tty
  | .eq _ e1 e2 => do
    let ty1 ← typeCheck ctx e1
    let ty2 ← typeCheck ctx e2
    guard (ty1 == ty2)
    some .bool

/-! ### `LExpr.typeCheck`'s rules for one node

The `app`, `ite` and `eq` rules of `LExpr.typeCheck`, as functions of the
children's types, for callers that compute those types another way (such as the
memoized check of common subexpression elimination). `LExpr.typeCheck` keeps
its rules inline, because the proofs about it unfold its body; the
`typeCheck_app`, `typeCheck_ite` and `typeCheck_eq` lemmas below state that
each of its cases is the corresponding rule, so the two cannot drift apart. -/

/-- The type of an application whose function has type `fty` and whose argument
has type `aty`: the codomain of `fty`, if `fty` is an arrow from `aty`. -/
@[expose]
def LMonoTy.appTy? (fty aty : LMonoTy) : Option LMonoTy := do
  let (dom, cod) ← fty.isArrow
  guard (dom == aty)
  some cod

/-- The type of `if c then t else e` with `c : cty`, `t : tty` and `e : ety`:
`tty`, if `cty` is `bool` and the branches agree. -/
@[expose]
def LMonoTy.iteTy? (cty tty ety : LMonoTy) : Option LMonoTy := do
  guard (cty == .bool)
  guard (tty == ety)
  some tty

/-- The type of `e1 == e2` with `e1 : ty1` and `e2 : ty2`: `bool`, if the sides
agree. -/
@[expose]
def LMonoTy.eqTy? (ty1 ty2 : LMonoTy) : Option LMonoTy := do
  guard (ty1 == ty2)
  some .bool

/-- `LExpr.typeCheck` types an application by typing its function and its
argument, then applying `LMonoTy.appTy?` to the two types. -/
theorem LExpr.typeCheck_app {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (fn arg : LExpr T.mono) :
    LExpr.typeCheck ctx (.app m fn arg) = (do
      let fty ← LExpr.typeCheck ctx fn
      let aty ← LExpr.typeCheck ctx arg
      LMonoTy.appTy? fty aty) := rfl

/-- `LExpr.typeCheck` types `if c then t else e` by typing the condition and
both branches, then applying `LMonoTy.iteTy?` to the three types. -/
theorem LExpr.typeCheck_ite {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (c t e : LExpr T.mono) :
    LExpr.typeCheck ctx (.ite m c t e) = (do
      let cty ← LExpr.typeCheck ctx c
      let tty ← LExpr.typeCheck ctx t
      let ety ← LExpr.typeCheck ctx e
      LMonoTy.iteTy? cty tty ety) := rfl

/-- `LExpr.typeCheck` types `e1 == e2` by typing both sides, then applying
`LMonoTy.eqTy?` to the two types. -/
theorem LExpr.typeCheck_eq {T : LExprParams} (ctx : List LMonoTy) (m : T.mono.base.Metadata)
    (e1 e2 : LExpr T.mono) :
    LExpr.typeCheck ctx (.eq m e1 e2) = (do
      let ty1 ← LExpr.typeCheck ctx e1
      let ty2 ← LExpr.typeCheck ctx e2
      LMonoTy.eqTy? ty1 ty2) := rfl

/-- The type arguments of `fn` bound by one-way matching its declared type against the annotation
    `opTy`: empty when `fn` is monomorphic; `none` without one or on a mismatch. -/
def LFuncDefined.opInstance? {T : LExprParams} (fn : LFuncDefined T)
    (opTy : Option LMonoTy) : Option SubstOne := do
  if fn.typeArgs.isEmpty then return Util.HMap.empty
  let instTy ← opTy
  let declTy := LMonoTy.mkArrow' fn.output fn.inputs.values
  LMonoTy.matchTy? fn.typeArgs Util.HMap.empty declTy instTy

/-- The type arguments of `fn` at a call, matched one-way against the operator's annotation or
    else the arguments' known types; `none` on a mismatch or when no type is known. On a
    type-checked program the operator's annotation matches, so the fallback to the arguments'
    types serves callers that pass a program that was not type-checked. -/
def LFuncDefined.callInstance? {T : LExprParams} (fn : LFuncDefined T) (callee : LExpr T.mono)
    (args : List (LExpr T.mono)) : Option SubstOne :=
  let fromOp := match callee with
    | .op _ _ opTy => fn.opInstance? opTy
    | _ => none
  let pairs := fn.inputs.values.zip (args.map (LExpr.typeCheck []))
  fromOp <|> if pairs.all (·.2.isNone) then none else LMonoTys.matchKnown? fn.typeArgs pairs

/-- The substitution instantiating `fn` by `σ`, with each type parameter `σ` leaves unbound
    mapped to `callTyVarPrefix ++ toString i`, where `i` is its position. -/
def LFunc.instanceSubst {T : LExprParams} (fn : LFunc T) (σ : SubstOne) :
    Subst :=
  [SubstOne.completeParams fn.typeArgs callTyVarPrefix σ]

/-- The instance of `fn` at a call with operator `callee`, matched one-way against its annotation:
    empty when `fn` is monomorphic; `none` without an annotation or on a mismatch. -/
@[expose] def LFunc.opTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    : Option Subst :=
  if fn.typeArgs.isEmpty then some Subst.empty
  else match callee with
    | .op _ _ opTy => (LFuncDefined.opInstance? fn.toFunc opTy).map fn.instanceSubst
    | _ => none

/-- The instance of `fn` at a call with operator `callee` and arguments `args`, given by
    `LFuncDefined.callInstance?`: empty when `fn` is monomorphic. -/
@[expose] def LFunc.computeTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    (args : List (LExpr T.mono)) : Option Subst :=
  if fn.typeArgs.isEmpty then some Subst.empty
  else (LFuncDefined.callInstance? fn.toFunc callee args).map fn.instanceSubst

/-- `body` instantiated at a call of `fn`: its types by `fn.computeTypeSubst`, its parameters by
    `args`. -/
def LFunc.instantiateBody? {T : LExprParams} [DecidableEq T.IDMeta]
    (fn : LFunc T) (body callee : LExpr T.mono) (args : List (LExpr T.mono)) :
    Option (LExpr T.mono) :=
  (fn.computeTypeSubst callee args).map fun tySubst =>
    LExpr.substFvarsLifting (body.applyTypeSubst tySubst) (fn.inputs.keys.zip args)

/--
Check every operator annotation of `e` against the factory `F`: an `.op` naming
a function `fn` of `F` must be annotated, and its annotation must be an instance of
`fn`'s type `inputs → output`, that is, `LMonoTy.matchSubst` finds a substitution of the
type variables of `fn`'s type that turns it into the annotation. The annotation's own type
variables are not substituted. Operators that `F` does not define are not constrained.

The check implies the declarative `OpsConsistentR` (`opsConsistent_sound`), but not
`OpsConsistent`, which requires the annotation to equal the function's type under the
substitution `LFunc.opTypeSubst`. That substitution differs from the one `matchSubst`
finds in two ways. A function with no `typeArgs` gets the empty substitution, even when
its type mentions a type variable that `matchSubst` binds. And `opTypeSubst` binds only
the function's `typeArgs` and treats every other type variable as fixed, while
`matchSubst` binds every type variable of the signature.
-/
@[expose]
def LExpr.opsConsistent {T : LExprParams} (F : Factory T) : LExpr T.mono → Bool
  | .op _ name ty =>
    match F[name.name]?, ty with
    | none, _ => true
    | some fn, some tyOp =>
      ((LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).matchSubst tyOp).isSome
    | some _, none => false
  | .app _ fn arg => opsConsistent F fn && opsConsistent F arg
  | .abs _ _ _ body => opsConsistent F body
  | .ite _ c t f => opsConsistent F c && opsConsistent F t && opsConsistent F f
  | .eq _ e1 e2 => opsConsistent F e1 && opsConsistent F e2
  | .quant _ _ _ _ tr body => opsConsistent F tr && opsConsistent F body
  | _ => true

/-- Type check `e` (as `LExpr.typeCheck`) against the factory `F`: `none` unless
every operator annotation of `e` agrees with its signature in `F`. -/
@[expose]
def LExpr.typeCheckWith {T : LExprParams} (F : Factory T) (ctx : List LMonoTy)
    (e : LExpr T.mono) : Option LMonoTy :=
  if e.opsConsistent F then e.typeCheck ctx else none

end -- public section
end Lambda

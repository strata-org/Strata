/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LState

/-! ## Partial evaluator for Lambda expressions

See function `Lambda.LExpr.eval` for the implementation.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open Strata.DL.Util (FuncAttr)

namespace LExpr

variable {T : LExprParamsT} {TBase : LExprParams} [BEq T.TypeType] [DecidableEq T.base.Metadata] [DecidableEq TBase.IDMeta] [ToFormat T.base.Metadata]
         [Inhabited T.base.IDMeta] [DecidableEq T.base.IDMeta] [ToFormat T.base.IDMeta] [Traceable EvalProvenance TBase.Metadata]

inductive EvalProvenance
  | Original -- The metadata of the original expression
  | ReplacementVar -- The original bound variable that was replaced
  | Abstraction -- The lambda that triggered the replacement

/--
Check for boolean equality of two expressions `e1` and `e2` after erasing any
type annotations.
-/
def eqModuloTypes (e1 e2 : LExpr T) : Bool :=
  e1.eraseMetadata.eraseTypes == e2.eraseMetadata.eraseTypes

/--
Canonical values of `LExpr`s.

Equality is simply `==` (or more accurately, `eqModuloTypes`) for these
`LExpr`s. Also see `eql` for a version that can tolerate nested metadata.

If `e:LExpr` is `.app`, say `e1 e2 .. en`, `e` is a canonical value if
(1) `e1` is a constructor and `e2 .. en` are all canonical values, or
(2) `e1` is a named function `f` (not abstraction) and `n` is less than the
    number of arguments required to run the function `f`.

The intuition of case (2) is as follows. Let's assume that we would like to
calculate `Int.Add 1 (2+3)`. According to the small step semantics, we would
like to calculate `2+3` to `5`, hence it becomes `Int.Add 1 5` and eventually 6.
Without (2), this is impossible because the `reduce_2` rule of small step
semantics only fires when `Int.Add 1` is a 'canonical value'. Therefore, without
(2), the semantics stuck and `2+3` can never be evaluated to `5`.
-/
def isCanonicalValue (F : @Factory T.base) (e : LExpr T) : Bool :=
  match he: e with
  | .const _ _ => true
  | .abs _ _ _ | .quant _ _ _ _ _ =>
    -- We're using the locally nameless representation, which guarantees that
    -- `closed (.abs e) = closed e` (see theorem `closed_abs`).
    -- So we could simplify the following to `closed e`, but leave it as is for
    -- clarity.
    LExpr.closed e
  | e' =>
    match h: Factory.callOfLFunc F e true with
    | some (_, args, f) =>
      (f.isConstr || Nat.blt args.length f.inputs.length) &&
      List.all (args.attach.map (fun ⟨ x, _⟩ =>
        have : x.sizeOf < e'.sizeOf := by
          have Hsmall := Factory.callOfLFunc_smaller h; grind
        (isCanonicalValue F x))) id
    | none => false
  termination_by e.sizeOf

/--
Check if `e` is a constructor application.
-/
def isConstrApp (F : @Factory T.base) (e : LExpr T) : Bool :=
  match Factory.callOfLFunc F e true with
  | some (_, _, f) => f.isConstr
  | none => false

/--
Equality of canonical values `e1` and `e2`.

We can tolerate nested metadata here.
-/
def eql (F : @Factory T.base) (e1 e2 : LExpr T)
  (_h1 : isCanonicalValue F e1) (_h2 : isCanonicalValue F e2) : Bool :=
  if eqModuloTypes e1 e2 then
    true
  else
    eqModuloTypes e1 e2

instance [ToFormat T.TypeType]: ToFormat (Except Format (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => err

instance [ToFormat T.TypeType]: ToFormat (Except Strata.DiagnosticModel (LExpr T)) where
  format x := match x with
              | .ok e => format e
              | .error err => f!"{err.message}"

/--
Embed `core` in an abstraction whose depth is `arity`. Used to implement
eta-expansion.

E.g., `mkAbsOfArity 2 core` will give `λxλy ((core y) x)`.
-/
def mkAbsOfArity (arity : Nat) (core : LExpr T) : (LExpr T) :=
  go 0 arity core
  where go (bvarcount arity : Nat) (core : LExpr T) : (LExpr T) :=
  match arity with
  | 0 => core
  | n + 1 =>
    go (bvarcount + 1) n (.abs core.metadata .none (.app core.metadata core (.bvar core.metadata bvarcount)))

/--
A metadata merger. It will be invoked 'subst s e' is invoked, to create a new
metadata.
-/
def mergeMetadataForSubst (metaAbs metaE2 metaReplacementVar: TBase.Metadata) :=
  Traceable.combine
  [(EvalProvenance.Original,       metaE2),
    (EvalProvenance.ReplacementVar, metaReplacementVar),
    (EvalProvenance.Abstraction,    metaAbs)]


mutual
/--
(Partial) evaluator for Lambda expressions w.r.t. a module, written using a fuel
argument.

Note that this function ascribes Curry-style semantics to `LExpr`s, i.e., we
can evaluate ill-typed terms w.r.t. a given type system here.

We prefer Curry-style semantics because they separate the type system from
evaluation, allowing us to potentially apply different type systems with our
expressions, along with supporting dynamically-typed languages.

Currently evaluator only supports LExpr with LMonoTy because LFuncs registered
at Factory must have LMonoTy.
-/
def eval (n : Nat) (σ : LState TBase) (e : (LExpr TBase.mono))
    : LExpr TBase.mono :=
  match n with
  | 0 => e
  | n' + 1 =>
    if isCanonicalValue σ.config.factory e then
      e
    else
      -- Special handling for Factory functions.
      match σ.config.factory.callOfLFunc e with
      | some (op_expr, args, lfunc) =>
        let args := args.map (fun a => eval n' σ a)
        let constrArgAt (idx : Option Nat) :=
          match idx with
          | some i => (args[i]? |>.map (isConstrApp σ.config.factory)).getD false
          | none => false
        if h: lfunc.body.isSome && (lfunc.attr.contains .inline ||
          constrArgAt (FuncAttr.findInlineIfConstr lfunc.attr)) then
          -- Inline a function only if it has a body.
          let body := lfunc.body.get (by simp_all)
          let input_map := lfunc.inputs.keys.zip args
          let new_e := substFvars body input_map
          eval n' σ new_e
        else
          let new_e := @mkApp TBase.mono e.metadata op_expr args
            -- All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
          if args.all (isCanonicalValue σ.config.factory) ||
            -- Other functions (e.g. Eliminators) only require the designated
            -- arg to be a constructor
            constrArgAt (FuncAttr.findEvalIfConstr lfunc.attr) then
            match lfunc.concreteEval with
            | none => new_e
            | some ceval =>
              match ceval new_e.metadata args with
              | .some e' => eval n' σ e'
              | .none => new_e
          else
            -- At least one argument in the function call is symbolic.
            new_e
      | none =>
        -- Not a call of a factory function.
        evalCore n' σ e

def evalCore  (n' : Nat) (σ : LState TBase) (e : LExpr TBase.mono) : LExpr TBase.mono :=
  match e with
  | .const _ _  => e
  | .op _ _ _     => e
  | .bvar _ _     => e
  | .fvar _ x ty  => (σ.state.findD x (ty, e)).snd
   -- Note: closed .abs terms are canonical values; we'll be here if .abs
   -- contains free variables.
  | .abs _ _ _   => LExpr.substFvarsFromState σ e
  | .quant _ _ _ _ _ => LExpr.substFvarsFromState σ e
  | .app _ e1 e2 => evalApp n' σ e e1 e2
  | .eq m e1 e2 => evalEq n' σ m e1 e2
  | .ite m c t f => evalIte n' σ m c t f

def evalIte (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (c t f : LExpr TBase.mono) : LExpr TBase.mono :=
  let c' := eval n' σ c
  match c' with
  | .true _ => eval n' σ t
  | .false _ => eval n' σ f
  | _ =>
    -- It's important to at least substitute `.fvar`s in both branches of the
    -- `ite` here so that we can replace the variables by the values in the
    -- state; these variables can come from an imperative dialect.
    -- (TODO): Is it worth it to evaluate these branches instead?
    -- let t' := eval n' σ t
    -- let f' := eval n' σ f
    let t' := substFvarsFromState σ t
    let f' := substFvarsFromState σ f
    .ite m c' t' f'

def evalEq (n' : Nat) (σ : LState TBase) (m: TBase.Metadata) (e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  open LTy.Syntax in
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  if eqModuloTypes e1'.eraseMetadata e2'.eraseMetadata then
    -- Short-circuit: e1' and e2' are syntactically the same after type erasure.
    LExpr.true m
  else if h: isCanonicalValue σ.config.factory e1' ∧
             isCanonicalValue σ.config.factory e2' then
    if eql σ.config.factory e1' e2' h.left h.right then
      LExpr.true m
    else LExpr.false m
  else
    .eq m e1' e2'

def evalApp (n' : Nat) (σ : LState TBase) (e e1 e2 : LExpr TBase.mono) : LExpr TBase.mono :=
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match e1' with
  | .abs mAbs _ e1' =>
    let e' := subst (fun metaReplacementVar =>
      let newMeta := mergeMetadataForSubst mAbs e2'.metadata metaReplacementVar
      replaceMetadata1 newMeta e2') e1'
    if eqModuloTypes e e' then e else eval n' σ e'
  | .op m fn _ =>
    match σ.config.factory.getFactoryLFunc fn.name with
    | none => LExpr.app m e1' e2'
    | some lfunc =>
      let e' := LExpr.app m e1' e2'
      -- In `e'`, we have already supplied one input to `fn`.
      -- Note that we can't have 0-arity Factory functions at this point.
      let e'' := @mkAbsOfArity TBase.mono (lfunc.inputs.length - 1) (e' : LExpr TBase.mono)
      eval n' σ e''
  | _ => .app e.metadata e1' e2'
end

instance : Traceable EvalProvenance Unit where
  combine _ := ()

end LExpr
end Lambda

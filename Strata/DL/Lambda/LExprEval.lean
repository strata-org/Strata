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

namespace LExpr

variable {IDMeta : Type} [DecidableEq IDMeta]
/--
Check for boolean equality of two expressions `e1` and `e2` after erasing any
type annotations.
-/
def eqModuloTypes {GenericTy} [DecidableEq GenericTy]
    (e1 e2 : (LExpr GenericTy IDMeta)) : Bool :=
  e1.eraseTypes == e2.eraseTypes

/--
Canonical values of `LExpr`s.

Equality is simply `==` (or more accurately, `eqModuloTypes`) for these
`LExpr`s. Also see `eql` for a version that can tolerate nested metadata.
-/
def isCanonicalValue {GenericTy} (σ : LState IDMeta)
    (e : LExpr GenericTy IDMeta) : Bool :=
  match he: e with
  | .const _ => true
  | .abs _ _ =>
    -- We're using the locally nameless representation, which guarantees that
    -- `closed (.abs e) = closed e` (see theorem `closed_abs`).
    -- So we could simplify the following to `closed e`, but leave it as is for
    -- clarity.
    LExpr.closed e
  | .mdata _ e' => isCanonicalValue σ e'
  | e' =>
    match h: Factory.callOfLFunc σ.config.factory e with
    | some (_, args, f) =>
      f.isConstr && List.all (args.attach.map (fun ⟨ x, _⟩ =>
        have : x.sizeOf < e'.sizeOf := by
          have Hsmall := Factory.callOfLFunc_smaller h; grind
      (isCanonicalValue σ x))) id
    | none => false
  termination_by e.sizeOf

/--
Equality of canonical values `e1` and `e2`.

We can tolerate nested metadata here.
-/
def eql {GenericTy} [DecidableEq GenericTy]
  (σ : LState IDMeta) (e1 e2 : LExpr GenericTy IDMeta)
  (_h1 : isCanonicalValue σ e1) (_h2 : isCanonicalValue σ e2) : Bool :=
  if eqModuloTypes e1 e2 then
    true
  else
    let e1' := removeAllMData e1
    let e2' := removeAllMData e2
    eqModuloTypes e1' e2'

instance : ToFormat (Except Format (LExpr LMonoTy IDMeta)) where
  format x := match x with
              | .ok e => format e
              | .error err => err

/--
Embed `core` in an abstraction whose depth is `arity`. Used to implement
eta-expansion.

E.g., `mkAbsOfArity 2 core` will give `λxλy ((core y) x)`.
-/
def mkAbsOfArity {GenericTy} (arity : Nat) (core : (LExpr GenericTy IDMeta))
    : (LExpr GenericTy IDMeta) :=
  go 0 arity core
  where go (bvarcount arity : Nat) (core : (LExpr GenericTy IDMeta))
      : (LExpr GenericTy IDMeta) :=
  match arity with
  | 0 => core
  | n + 1 =>
    go (bvarcount + 1) n (.abs .none (.app core (.bvar bvarcount)))

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
def eval (n : Nat) (σ : (LState IDMeta)) (e : (LExpr LMonoTy IDMeta))
    : (LExpr LMonoTy IDMeta) :=
  match n with
  | 0 => e
  | n' + 1 =>
    if isCanonicalValue σ e then
      e
    else
      -- Special handling for Factory functions.
      match σ.config.factory.callOfLFunc e with
      | some (op_expr, args, lfunc) =>
        let args := args.map (fun a => eval n' σ a)
        if h: "inline" ∈ lfunc.attr && lfunc.body.isSome then
          -- Inline a function only if it has a body.
          let body := lfunc.body.get (by simp_all)
          let input_map := lfunc.inputs.keys.zip args
          let new_e := substFvars body input_map
          eval n' σ new_e
        else
          let new_e := mkApp op_expr args
          if args.all (isCanonicalValue σ) then
            -- All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
            match lfunc.concreteEval with
            | none => new_e | some ceval => eval n' σ (ceval new_e args)
          else
            -- At least one argument in the function call is symbolic.
            new_e
      | none =>
        -- Not a call of a factory function.
        evalCore n' σ e

def evalCore (n' : Nat) (σ : (LState IDMeta)) (e : (LExpr LMonoTy IDMeta)) : (LExpr LMonoTy IDMeta) :=
  match e with
  | .const _  => e
  | .op _ _     => e
  | .bvar _     => e
  | .fvar x ty  => (σ.state.findD x (ty, e)).snd
   -- (FIXME): Perform metadata transform instead of erasing it here.
  | .mdata _ e' => eval n' σ e'
   -- Note: closed .abs terms are canonical values; we'll be here if .abs
   -- contains free variables.
  | .abs _ _   => substFvarsFromState σ e
  | .quant _ _ _ _ => substFvarsFromState σ e
  | .app e1 e2 => evalApp n' σ e e1 e2
  | .eq  e1 e2 => evalEq n' σ e1 e2
  | .ite c t f => evalIte n' σ c t f

def evalIte (n' : Nat) (σ : (LState IDMeta)) (c t f : (LExpr LMonoTy IDMeta)) : (LExpr LMonoTy IDMeta) :=
  let c' := eval n' σ c
  match c' with
  | .true => eval n' σ t
  | .false => eval n' σ f
  | _ =>
    -- It's important to at least substitute `.fvar`s in both branches of the
    -- `ite` here so that we can replace the variables by the values in the
    -- state; these variables can come from an imperative dialect.
    -- (TODO): Is it worth it to evaluate these branches instead?
    -- let t' := eval n' σ t
    -- let f' := eval n' σ f
    let t' := substFvarsFromState σ t
    let f' := substFvarsFromState σ f
    ite c' t' f'

def evalEq (n' : Nat) (σ : (LState IDMeta)) (e1 e2 : (LExpr LMonoTy IDMeta)) : (LExpr LMonoTy IDMeta) :=
  open LTy.Syntax in
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  if eqModuloTypes e1' e2' then
    -- Short-circuit: e1' and e2' are syntactically the same after type erasure.
    LExpr.true
  else if h: isCanonicalValue σ e1' ∧ isCanonicalValue σ e2' then
      if eql σ e1' e2' h.left h.right then
        LExpr.true
      else LExpr.false
  else
    .eq e1' e2'

def evalApp (n' : Nat) (σ : (LState IDMeta)) (e e1 e2 : (LExpr LMonoTy IDMeta)) : (LExpr LMonoTy IDMeta) :=
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match e1' with
  | .abs _ e1' =>
    let e' := subst e2' e1'
    if eqModuloTypes e e' then e else eval n' σ e'
  | .op fn _ =>
    match σ.config.factory.getFactoryLFunc fn.name with
    | none => LExpr.app e1' e2'
    | some lfunc =>
      let e' := LExpr.app e1' e2'
      -- In `e'`, we have already supplied one input to `fn`.
      -- Note that we can't have 0-arity Factory functions at this point.
      let e'' := mkAbsOfArity (lfunc.inputs.length - 1) e'
      eval n' σ e''
  | _ => LExpr.app e1' e2'

end

end LExpr
end Lambda

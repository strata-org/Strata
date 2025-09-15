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

variable {T : LExprParams} [BEq T.Metadata] [DecidableEq T.Metadata] [ToFormat T.Metadata]
         [Inhabited T.Identifier] [BEq T.Identifier] [DecidableEq T.Identifier] [ToFormat T.Identifier] [Traceable EvalProvenance T.Metadata]

inductive EvalProvenance
  | Original -- The metadata of the original expression
  | ReplacementVar -- The original bound variable that was replaced
  | Abstraction -- The lambda that triggered the replacement

/--
Check for boolean equality of two expressions `e1` and `e2` after erasing any
type annotations.
-/
def eqModuloTypes (e1 e2 : (LExpr T.mono)) : Bool :=
  e1.eraseTypes == e2.eraseTypes

/--
Canonical values of `LExpr`s.

Equality is simply `==` (or more accurately, `eqModuloTypes`) for these
`LExpr`s. Also see `eql` for a version that can tolerate nested metadata.
-/
def isCanonicalValue (e : (LExpr T.mono)) : Bool :=
  match e with
  | .const _ _ _ => true
  | .abs _ _ _ =>
    -- We're using the locally nameless representation, which guarantees that
    -- `closed (.abs e) = closed e` (see theorem `closed_abs`).
    -- So we could simplify the following to `closed e`, but leave it as is for
    -- clarity.
    LExpr.closed e
  | _ => false

/--
Equality of canonical values `e1` and `e2`.

We can tolerate nested metadata here.
-/
def eql (e1 e2 : (LExpr T.mono))
  (_h1 : isCanonicalValue e1) (_h2 : isCanonicalValue e2) : Bool :=
  eqModuloTypes e1 e2

instance : ToFormat (Except Format (LExpr T.mono)) where
  format x := match x with
              | .ok e => format e
              | .error err => err

/--
Embed `core` in an abstraction whose depth is `arity`. Used to implement
eta-expansion.

E.g., `mkAbsOfArity 2 core` will give `λxλy ((core y) x)`.
-/
def mkAbsOfArity (arity : Nat) (core : (LExpr T.mono)) : (LExpr T.mono) :=
  go 0 arity core
  where go (bvarcount arity : Nat) (core : (LExpr T.mono)) : (LExpr T.mono) :=
  match arity with
  | 0 => core
  | n + 1 =>
    go (bvarcount + 1) n (.abs core.metadata .none (.app core.metadata core (.bvar core.metadata bvarcount)))

mutual
/--
(Partial) evaluator for Lambda expressions w.r.t. a module, written using a fuel
argument.

Note that this function ascribes Curry-style semantics to `LExpr`s, i.e., we
can evaluate ill-typed terms w.r.t. a given type system here.

We prefer Curry-style semantics because they separate the type system from
evaluation, allowing us to potentially apply different type systems with our
expressions, along with supporting dynamically-typed languages.
-/
partial def eval (n : Nat) (σ : LState T) (e : LExpr T.mono) : LExpr T.mono :=
  -- FIXME: Remove partial keyword once https://github.com/leanprover/lean4/issues/10353 is fixed
  match n with
  | 0 => e
  | n' + 1 =>
    if isCanonicalValue e then
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
          let new_e := @mkApp T.mono e.metadata op_expr args
          if args.all (isConst T.mono) then
            -- All arguments in the function call are concrete.
            -- We can, provided a denotation function, evaluate this function
            -- call.
            match lfunc.concreteEval with
            | none => new_e | some ceval => ceval new_e args
          else
            -- At least one argument in the function call is symbolic.
            new_e
      | none =>
        -- Not a call of a factory function.
        evalCore n' σ e

partial def evalCore  (n' : Nat) (σ : LState T) (e : LExpr T.mono) : LExpr T.mono :=
  match e with
  | .const _ _ _  => e
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

partial def evalIte (n' : Nat) (σ : LState T) (m: T.Metadata) (c t f : LExpr T.mono) : LExpr T.mono :=
  let c' := eval n' σ c
  match c' with
  | .const _ "true" _ => eval n' σ t
  | .const _ "false" _ => eval n' σ f
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

partial def evalEq (n' : Nat) (σ : LState T) (m: T.Metadata) (e1 e2 : LExpr T.mono) : LExpr T.mono :=
  open LTy.Syntax in
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  if eqModuloTypes e1' e2' then
    -- Short-circuit: e1' and e2' are syntactically the same after type erasure.
    LExpr.true T m
  else if h: isCanonicalValue e1' ∧ isCanonicalValue e2' then
      if eql e1' e2' h.left h.right then
        LExpr.true T m
      else LExpr.false T m
  else
    .eq m e1' e2'

partial def evalApp (n' : Nat) (σ : LState T) (e e1 e2 : LExpr T.mono) : LExpr T.mono :=
  let e1' := eval n' σ e1
  let e2' := eval n' σ e2
  match e1' with
  | .abs mAbs _ e1' =>
    let replacer := fun (replacementVar: T.Metadata) =>
     (@LExpr.replaceMetadata (T := T.mono) (
      Traceable.combine
      [(EvalProvenance.Original,       e2'.metadata),
       (EvalProvenance.ReplacementVar, replacementVar),
       (EvalProvenance.Abstraction,    mAbs)]) e2');
    let e' := subst replacer e1'
    if eqModuloTypes e e' then e else eval n' σ e'
  | .op m fn _ =>
    match σ.config.factory.getFactoryLFunc fn with
    | none => .app m e1' e2'
    | some lfunc2 =>
      let e' := LExpr.app m e1' e2'
      -- In `e'`, we have already supplied one input to `fn`.
      -- Note that we can't have 0-arity Factory functions at this point.
      let e'' := @mkAbsOfArity T (lfunc2.inputs.length - 1) (e' : LExpr T.mono)
      eval n' σ e''
  | _ => .app e.metadata e1' e2'
end

end LExpr
end Lambda

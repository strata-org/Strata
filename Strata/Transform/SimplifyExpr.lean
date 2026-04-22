/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CoreTransform
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.Rewriting

/-! # Expression Simplification

Algebraic simplification rules for boolean operations that the Factory's
`concreteEval` / function body inlining cannot optimize further (e.g., when
one operand is symbolic).

The main entry point is `simplifyExpr`, which alternates between
`LExpr.eval` (partial evaluation via the Factory) and pattern-based
boolean simplification until a fixed point or fuel exhaustion. -/

public section

namespace Core
namespace SimplifyExpr

open Core.Transform Lambda

/-! ## Boolean simplification as a set of rewrite rules

The algebraic boolean laws below are expressed as `RewriteRule`s over
`Expression.Expr` (see `Strata.DL.Lambda.Rewriting`). Each rule's `lhs` is a
pattern built from the relevant `Bool.*` operator applied to a mix of concrete
boolean constants and a pattern variable (`x`); its `rhs` is the simplified
form. The first-order matcher binds the pattern variable and the rule's `rhs`
is instantiated accordingly. -/

namespace Rules

/-- Metadata-free boolean constant patterns/results. -/
private def cTrue  : Expression.Expr := .true ()
private def cFalse : Expression.Expr := .false ()

/-- Pattern variable used by the boolean rules. -/
private def pX : Expression.Expr := .fvar () "x" none

/-- Build the application of a boolean operator `name` to `args`. -/
private def boolOp (name : String) (args : List Expression.Expr) : Expression.Expr :=
  LExpr.mkApp () (.op () name none) args

/-- The set of algebraic boolean simplification rules. They mirror the laws
    that `LExpr.eval` cannot apply when one operand is symbolic:

    * `Bool.And`: identity by `true`, annihilation by `false`
    * `Bool.Or` : identity by `false`, annihilation by `true`
    * `Bool.Not`: double-negation elimination
    * `Bool.Implies`: absorption by `false`/`true`
    * `Bool.Equiv`: identity by `true` -/
def boolRules : List (RewriteRule CoreLParams.mono) :=
  [ -- Bool.And
    ⟨boolOp "Bool.And" [cTrue, pX],  pX⟩,      -- true && x  = x
    ⟨boolOp "Bool.And" [pX, cTrue],  pX⟩,      -- x && true  = x
    ⟨boolOp "Bool.And" [cFalse, pX], cFalse⟩,  -- false && x = false
    ⟨boolOp "Bool.And" [pX, cFalse], cFalse⟩,  -- x && false = false
    -- Bool.Or
    ⟨boolOp "Bool.Or" [cFalse, pX], pX⟩,       -- false || x = x
    ⟨boolOp "Bool.Or" [pX, cFalse], pX⟩,       -- x || false = x
    ⟨boolOp "Bool.Or" [cTrue, pX],  cTrue⟩,    -- true || x  = true
    ⟨boolOp "Bool.Or" [pX, cTrue],  cTrue⟩,    -- x || true  = true
    -- Bool.Not
    ⟨boolOp "Bool.Not" [boolOp "Bool.Not" [pX]], pX⟩,  -- !!x = x
    -- Bool.Implies
    ⟨boolOp "Bool.Implies" [cFalse, pX], cTrue⟩,  -- false ==> x = true
    ⟨boolOp "Bool.Implies" [pX, cTrue],  cTrue⟩,  -- x ==> true = true
    ⟨boolOp "Bool.Implies" [cTrue, pX],  pX⟩,     -- true ==> x = x
    -- Bool.Equiv
    ⟨boolOp "Bool.Equiv" [cTrue, pX], pX⟩,        -- true <==> x = x
    ⟨boolOp "Bool.Equiv" [pX, cTrue], pX⟩ ]       -- x <==> true = x

end Rules

/-- Try to simplify a boolean expression by one step using algebraic laws.
    Applies the first matching rule from `Rules.boolRules` at the top of `e`.
    Only handles cases where `LExpr.eval` cannot reduce further, i.e., when
    one operand is symbolic. Returns `some simplified` if a rule fires. -/
def simplifyBoolOp (e : Expression.Expr) : Option Expression.Expr :=
  RewriteRules.apply Rules.boolRules e

/-- Bottom-up traversal of an expression. Recursively processes sub-expressions
    of `app`, `ite`, and `eq` nodes, then applies `f` once to the rebuilt node.
    Skips `.abs` and `.quant` (bound-variable binders).
    Returns `some e'` if `f` fired anywhere, `none` if nothing changed. -/
def traverseExpr (f : Expression.Expr → Option Expression.Expr) (e : Expression.Expr)
    : Option Expression.Expr :=
  match e with
  | .app m fn arg =>
    let fn'  := traverseExpr f fn
    let arg' := traverseExpr f arg
    let e' := .app m (fn'.getD fn) (arg'.getD arg)
    match f e' with
    | some e'' => some e''
    | none => if fn'.isSome || arg'.isSome then some e' else none
  | .ite m c t el =>
    let c'  := traverseExpr f c
    let t'  := traverseExpr f t
    let el' := traverseExpr f el
    let e' := .ite m (c'.getD c) (t'.getD t) (el'.getD el)
    match f e' with
    | some e'' => some e''
    | none => if c'.isSome || t'.isSome || el'.isSome then some e' else none
  | .eq m e1 e2 =>
    let e1' := traverseExpr f e1
    let e2' := traverseExpr f e2
    let e' := .eq m (e1'.getD e1) (e2'.getD e2)
    match f e' with
    | some e'' => some e''
    | none => if e1'.isSome || e2'.isSome then some e' else none
  | .const _ _         => f e
  | .op _ _ _          => f e
  | .bvar _ _          => f e
  | .fvar _ _ _        => f e
  | .abs _ _ _ _       => f e
  | .quant _ _ _ _ _ _ => f e

/-- Partially evaluate and simplify `e`. Alternates between `LExpr.eval`
    (Factory-based partial evaluation) and `simplifyBoolOp` (algebraic
    boolean rules applied bottom-up) until a fixed point or fuel exhaustion. -/
def simplifyExpr (fuel : Nat) (σ : LState CoreLParams) (e : Expression.Expr)
    : Expression.Expr :=
  let e' := LExpr.eval σ.config.fuel σ e
  match fuel with
  | 0 => e'
  | n + 1 =>
    match traverseExpr simplifyBoolOp e' with
    | none => e'  -- nothing changed, fixed point reached
    | some e'' =>
      -- Re-run the full pipeline after boolean simplification in case
      -- it unlocks further reductions.
      simplifyExpr n σ e''

end SimplifyExpr
end Core

end -- public section

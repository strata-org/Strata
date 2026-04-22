/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprWF

/-! # A simple first-order rewriting system for Lambda expressions

This module implements a lightweight term-rewriting engine over `LExpr`.
There is no higher-order matching (e.g., matching a pattern 'P x' with
term 'x + 1' is not supported). -/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

namespace LExpr

variable {T : LExprParamsT} [DecidableEq T.base.IDMeta] [BEq T.base.IDMeta] [DecidableEq T.TypeType]

/-- A substitution produced by matching is a `Map` from pattern variables to the
    terms they bind, i.e. exactly the map consumed by `LExpr.substFvars`. -/
abbrev Subst (T : LExprParamsT) := Map (Identifier T.base.IDMeta) (LExpr T)

/-- Two expressions are considered equal for matching purposes when they agree
    after erasing all metadata. -/
def eqMatch (e1 e2 : LExpr T) : Bool :=
  decide (e1.eraseMetadata = e2.eraseMetadata)

/-- Worker for `matchPattern`, threading an accumulating substitution `acc`.

    Recurses structurally on `pat`. Pattern free variables bind to sub-terms;
    every other constructor must match structurally (ignoring metadata, optional
    type annotations, and binder pretty names). -/
def matchAux (acc : Subst T) (pat term : LExpr T) : Option (Subst T) := do
  match pat with
  | .fvar _ name _ =>
    -- A pattern variable: bind `name` to `term`, checking consistency with any
    -- existing binding.
    match acc.find? name with
    | some bound => if eqMatch bound term then some acc else none
    | none => some (acc.insert name term)
  | .const _ c =>
    let .const _ c' := term | none
    guard (c = c'); pure acc
  | .op _ o _ =>
    let .op _ o' _ := term | none
    guard (o = o'); pure acc
  | .bvar _ i =>
    let .bvar _ i' := term | none
    guard (i = i'); pure acc
  | .app _ pfn parg =>
    -- No higher-order matching: the function position of an application may not
    -- be a bare pattern variable.
    match pfn with
    | .fvar _ _ _ => none
    | _ =>
      let .app _ tfn targ := term | none
      let acc ← matchAux acc pfn tfn
      matchAux acc parg targ
  | .eq _ pe1 pe2 =>
    let .eq _ te1 te2 := term | none
    let acc ← matchAux acc pe1 te1
    matchAux acc pe2 te2
  | .ite _ pc pt pe =>
    let .ite _ tc tt te := term | none
    let acc ← matchAux acc pc tc
    let acc ← matchAux acc pt tt
    matchAux acc pe te
  | .abs _ _ _ pe =>
    let .abs _ _ _ te := term | none
    matchAux acc pe te
  | .quant _ pk _ _ ptr pe =>
    let .quant _ tk _ _ ttr te := term | none
    guard (pk = tk)
    let acc ← matchAux acc ptr ttr
    matchAux acc pe te

/-- First-order matcher. Returns a substitution witnessing that `term` is an
    instance of `pattern`, or `none` if they do not match. -/
def matchPattern (pattern term : LExpr T) : Option (Subst T) :=
  matchAux [] pattern term

end LExpr

---------------------------------------------------------------------

/-- A rewrite rule: rewrite instances of `lhs` into the corresponding instance
    of `rhs`. -/
structure RewriteRule (T : LExprParamsT) where
  lhs : LExpr T
  rhs : LExpr T

namespace RewriteRule

variable {T : LExprParamsT} [DecidableEq T.base.IDMeta] [BEq T.base.IDMeta] [DecidableEq T.TypeType]

def apply (r : RewriteRule T) (term : LExpr T) : Option (LExpr T) :=
  match LExpr.matchPattern r.lhs term with
  | some s => some (LExpr.substFvars r.rhs s)
  | none => none

/-- A rule is well-formed when every free variable in `rhs` also occurs free in
    `lhs`. This rules out rules that would introduce unbound variables, since
    only the variables bound by matching `lhs` get substituted into `rhs`. -/
def isWellFormed (r : RewriteRule T) : Bool :=
  r.rhs.collectFvarNames.all (· ∈ r.lhs.collectFvarNames)

end RewriteRule

namespace RewriteRules

variable {T : LExprParamsT} [DecidableEq T.base.IDMeta] [BEq T.base.IDMeta] [DecidableEq T.TypeType]

def apply (rules : List (RewriteRule T)) (term : LExpr T) : Option (LExpr T) :=
  match rules with
  | [] => none
  | r :: rest =>
    match r.apply term with
    | some e => some e
    | none => apply rest term

end RewriteRules

end -- public section
end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lean.Elab.Tactic

/-!
# Tactics

This module provides tactics that are useful throughout Strata and have no
dependencies
-/


open Lean Meta Elab Tactic

-- A tactic for proving termination

/-
  A common pattern for rose-tree-like AST structures: we have
  `x ∈ xs` and we need `sizeOf x < ... + sizeOf xs`, which follows from
  `List.sizeOf_lt_of_mem`, `Array.sizeOf_lt_of_mem`, or a specialized lemma.
  Instead of having to manually name (and rename) hypotheses,
  this file provides a tactic `add_mem_size_lemmas` that finds hypotheses
  matching this pattern and automatically populates the context, as well as
  a tactic `term_by_mem` that solves most termination goals
-/

/-- Check if type is of the form `x ∈ xs` and return
  (x, xs, containerType) if so -/
private def getMemInfo? (ty : Expr) : MetaM (Option (Expr × Expr × Name)) := do
  let ty ← whnf ty
  match_expr ty with
  | List.Mem _ x xs => return some (x, xs, ``List)
  | Array.Mem _ xs x => return some (x, xs, ``Array)
  | _ => return none

/-- Get the head type name from an expression's type -/
private def getElemTypeName (x : Expr) : MetaM (Option Name) := do
  let ty ← inferType x
  let ty ← whnf ty
  return ty.getAppFn.constName?

/-- Core implementation: add size lemmas with optional custom mappings -/
private def addMemSizeLemmasCore (customLemmas : Array (Name × Name)) :
TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    for decl in lctx do
      let ty ← instantiateMVars decl.type
      if let some (x, _, containerType) ← getMemInfo? ty then
        let elemTypeName ← getElemTypeName x
        -- Check custom lemmas first (by element type)
        let mut lemmaName? : Option Name := none
        if let some elemName := elemTypeName then
          for (typeName, lemma) in customLemmas do
            if elemName == typeName ||
              elemName.toString.endsWith typeName.toString then
              lemmaName? := some lemma
              break
        -- Fall back to built-in lemmas (by container type)
        if lemmaName?.isNone then
          lemmaName? :=
            if containerType == ``List
            then some ``List.sizeOf_lt_of_mem
            else if containerType == ``Array
            then some ``Array.sizeOf_lt_of_mem
            else none
        if let some lemmaName := lemmaName? then
          try
            -- Use fvarId for unique name
            let hypExpr := mkFVar decl.fvarId
            let hypStx ← Term.exprToSyntax hypExpr
            evalTactic (← `(tactic| have := $(mkIdent lemmaName) $hypStx))
          catch e => dbg_trace s!"add_mem_size_lemmas error: {← e.toMessageData.toString}"

/-- Adds sizeOf lemmas for all `x ∈ xs` hypotheses in context -/
elab "add_mem_size_lemmas" : tactic => addMemSizeLemmasCore #[]

/-- Adds sizeOf lemmas with custom (ElemType, Lemma) mappings -/
syntax "add_mem_size_lemmas" "[" (ident "," ident),* "]" : tactic

elab_rules : tactic
  | `(tactic| add_mem_size_lemmas [ $[$types , $lemmas],* ]) => do
    let customLemmas := Array.zip (types.map (·.getId)) (lemmas.map (·.getId))
    addMemSizeLemmasCore customLemmas

/-- Termination tactic: add size lemmas for `List` and `Array` membership,
  then closes with `simp_all` and `omega` -/
macro "term_by_mem" : tactic =>
  `(tactic| solve | (add_mem_size_lemmas; (try simp_all); (try omega)))

/-- Termination tactic with custom (ElemType, Lemma) mappings - adds size
  lemmas for `List`, `Array`, and according to the custom mapping, then
  closes with `simp_all` and `omega`
  Example, suppose we have a custom `size` operator on type `ty` and a lemma
  `ty_size_mem : ty ∈ tys → ty.size < tys.size`. Then
  `term_by_mem[ty, ty_size_mem]` will automatically add `ty_size_mem` to the
  hypotheses if `ty₁ ∈ tys₁` appears.   -/
syntax "term_by_mem" "[" (ident "," ident),* "]" : tactic

macro_rules
  | `(tactic| term_by_mem [ $[$types , $lemmas],* ]) =>
    `(tactic| solve | (add_mem_size_lemmas [$[$types, $lemmas],*]; (try simp_all); (try omega)))

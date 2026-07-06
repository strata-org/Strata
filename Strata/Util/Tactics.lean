/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Init.Grind.Cases
public meta import Init.Grind.Ext
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Generalize
public meta import Lean.Meta.Tactic.Split
public meta import Lean.Meta.Tactic.SplitIf
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Rewrite
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Elab.Tactic.Location
public meta import Std.Do -- shake: keep
import Lean.Exception

public section
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
private meta def getMemInfo? (ty : Expr) : MetaM (Option (Expr × Expr × Name)) := do
  let ty ← whnf ty
  match_expr ty with
  | List.Mem _ x xs => return some (x, xs, ``List)
  | Array.Mem _ xs x => return some (x, xs, ``Array)
  | _ => return none

/-- Get the head type name from an expression's type -/
private meta def getElemTypeName (x : Expr) : MetaM (Option Name) := do
  let ty ← inferType x
  let ty ← whnf ty
  return ty.getAppFn.constName?

/-- Core implementation: add size lemmas with optional custom mappings -/
private meta def addMemSizeLemmasCore (customLemmas : Array (Name × Name)) :
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

open Lean Meta Elab Tactic in
/-- Generalize the last argument of the LHS of an equality goal. -/
elab "generalize_lhs_last_arg" : tactic => do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := goalType.eq? | throwError "Goal is not an equality"
  match lhs with
  | Expr.app _fn lastArg =>
    let (_, newGoal) ← goal.generalize #[{ expr := lastArg }]
    replaceMainGoal [newGoal]
  | _ => throwError "LHS is not a function application"

end

/-! ## `split_ns` — a `simp`-free `split`

The built-in `split` tactic case-splits an `if`/`match` and then normalizes the
result by running the full `simp` engine (`simpIfTarget`/`simpMatchTargetCore`)
over the *entire* goal or hypothesis. On a large `do`-chain of guards whose
conditions `simp` cannot decide (each stuck on a free variable), the `ite`
reduction recursively re-`simp`s every nested condition and blows the default
100000-step budget: `simp failed: maximum number of steps exceeded`.

`split_ns` reuses `split`'s (`simp`-free) case-split machinery — `byCasesDec`
for `ite`/`dite`, `Lean.Meta.Split.applyMatchSplitter` for `match` — but
replaces the `simp` normalization with a *targeted* reduction of only the one
`if`/`match` that was split:

* `ite`/`dite`: rewrite with the exact `if_pos`/`if_neg`/`dif_pos`/`dif_neg`
  equation built from the branch condition hypothesis;
* `match`: iota-reduce only the split matcher (its discriminants are now
  concrete constructors) via `reduceRecMatcher?` and `replaceTargetDefEq`.

Nested stuck `if`/`match` subterms are left completely untouched, so cost is
independent of chain length. -/
public section
section SplitNoSimp
open Lean Meta Elab Tactic
open Lean.Meta.Split (applyMatchSplitter isDiscrGenException throwDiscrGenError)

namespace SplitNoSimp

/--
Build the exact `ite`/`dite` reduction equation for one branch, given a proof
`hcond` of the branch condition (`cond` for the then-branch, `¬cond` for the
else-branch). Returns `e = reduced` with no `simp`. `isThen` picks the positive
lemma, `isDite` picks the dependent lemma. -/
meta def mkIteRedEq (e : Expr) (hcond : Expr) (isThen isDite : Bool) : MetaM Expr := do
  -- `ite`/`dite α c inst t el` : args are [α, c, inst, t, el]
  let u := e.getAppFn.constLevels!
  let α    := e.getArg! 0 5
  let c    := e.getArg! 1 5
  let inst := e.getArg! 2 5
  let t    := e.getArg! 3 5
  let el   := e.getArg! 4 5
  let lemmaName :=
    match isDite, isThen with
    | false, true  => ``if_pos
    | false, false => ``if_neg
    | true,  true  => ``dif_pos
    | true,  false => ``dif_neg
  -- Positional args for `{c} {h} (hcond) {α} {t} {e}`.
  return mkAppN (mkConst lemmaName u) #[c, inst, hcond, α, t, el]

/-- Rewrite the equation `heq : e = e'` at the local hypothesis `fvarId`. -/
meta def rewriteHypWithEq (mvarId : MVarId) (fvarId : FVarId) (heq : Expr) :
    MetaM MVarId := mvarId.withContext do
  let hypType ← instantiateMVars (← fvarId.getType)
  let r ← mvarId.rewrite hypType heq
  let rres ← mvarId.replaceLocalDecl fvarId r.eNew r.eqProof
  return rres.mvarId

/-- Rewrite the equation `heq : e = e'` in the goal target. -/
meta def rewriteTargetWithEq (mvarId : MVarId) (heq : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let r ← mvarId.rewrite target heq
    mvarId.replaceTargetEq r.eNew r.eqProof

/-- Reduce the `ite`/`dite` `e` in one branch and rewrite it into `fvarId?`
(a hypothesis) or the target. `s` is the `byCasesDec` subgoal carrying the
branch condition hypothesis. -/
meta def reduceIteBranch (s : ByCasesSubgoal) (e : Expr) (fvarId? : Option FVarId)
    (isThen isDite : Bool) : MetaM MVarId := s.mvarId.withContext do
  let hcond := mkFVar s.fvarId
  let heq ← mkIteRedEq e hcond isThen isDite
  match fvarId? with
  | some fvarId => rewriteHypWithEq s.mvarId fvarId heq
  | none        => rewriteTargetWithEq s.mvarId heq

/-- Case-split a single `ite`/`dite` candidate `e` in target (`fvarId? = none`)
or hypothesis, reducing only that `if` in each branch. Returns `[then, else]`. -/
meta def splitIte? (mvarId : MVarId) (e : Expr) (fvarId? : Option FVarId) :
    MetaM (List MVarId) := mvarId.withContext do
  let cond := e.getArg! 1 5
  let dec  := e.getArg! 2 5
  let isDite := e.isAppOf ``dite
  let hName ← mkFreshUserName `h
  let (sThen, sElse) ← mvarId.byCasesDec cond dec hName
  let mThen ← reduceIteBranch sThen e fvarId? (isThen := true)  isDite
  let mElse ← reduceIteBranch sElse e fvarId? (isThen := false) isDite
  return [mThen, mElse]

/-- Iota-reduce only the applications of `matcherName` in the target (the ones
the splitter just specialized with concrete constructors); nested stuck
matchers are left untouched. Definitional, so update via `replaceTargetDefEq`. -/
meta def reduceMatcherInTarget (mvarId : MVarId) (matcherName : Name) :
    MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let pre (e : Expr) : MetaM TransformStep := do
    if e.isAppOf matcherName then
      match (← reduceRecMatcher? e) with
      | some e' => return .done e'
      | none    => return .continue
    else
      return .continue
  let targetNew ← transform target (pre := pre)
  if targetNew == target then
    return mvarId
  mvarId.replaceTargetDefEq targetNew

/-- Case-split a single `match` candidate `e` in the target, reducing only the
split matcher in each branch. Reuses the `simp`-free `applyMatchSplitter`. -/
meta def splitMatchTarget (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) :=
  mvarId.withContext do
    let some app ← matchMatcherApp? e | throwError "`split_ns`: not a matcher application"
    let mvarIds ← applyMatchSplitter mvarId app.matcherName app.matcherLevels
      app.params app.discrs
    mvarIds.mapM fun m => reduceMatcherInTarget m app.matcherName

/-- Split the first `if`/`match` candidate in the target, without `simp`.

Mirrors `Lean.Meta.splitTarget?`: if a `match` discriminant generalization
fails (the internal `discrGeneralizationFailure` exception), that candidate is
added to `badCases` and we look for another one, instead of letting the internal
exception escape. -/
meta partial def splitTarget? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  commitWhenSome? do mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    let rec go (badCases : ExprSet) : MetaM (Option (List MVarId)) := do
      if let some e ← findSplit? target .both badCases then
        if e.isIte || e.isDIte then
          return some (← splitIte? mvarId e none)
        else
          try
            return some (← splitMatchTarget mvarId e)
          catch ex =>
            unless isDiscrGenException ex do throw ex
            go (badCases.insert e)
      else
        return none
    go {}

/-- Split the first `if`/`match` candidate in hypothesis `fvarId`, without
`simp`.

Mirrors `Lean.Meta.splitLocalDecl?` for the `match` case: reverting the
hypothesis and splitting can fail with `discrGeneralizationFailure`; we recover
by asserting a copy and retrying (for let-decls / hypotheses with forward
dependencies), and otherwise fail cleanly with the standard discriminant
generalization error rather than leaking the internal exception. -/
meta def splitLocalDecl? (mvarId : MVarId) (fvarId : FVarId) :
    MetaM (Option (List MVarId)) := commitWhenSome? do mvarId.withContext do
  let some e ← findSplit? (← inferType (mkFVar fvarId)) | return none
  if e.isIte || e.isDIte then
    return some (← splitIte? mvarId e (some fvarId))
  else
    -- First attempt: revert, split in target, re-introduce.
    let result? ← commitWhenSome? do try
      let (fvarIds, mvarId) ← mvarId.revert #[fvarId]
      let num := fvarIds.size
      let mvarIds ← splitMatchTarget mvarId e
      let mvarIds ← mvarIds.mapM fun m => return (← m.introNP num).2
      return some mvarIds
    catch ex =>
      if isDiscrGenException ex then return none else throw ex
    if result?.isSome then
      return result?
    -- Generalization failed; if `fvarId` is a let-decl or has forward
    -- dependencies, assert a copy and try again.
    let localDecl ← fvarId.getDecl
    if (← pure localDecl.isLet <||> exprDependsOn (← mvarId.getType) fvarId <||> fvarId.hasForwardDeps) then
      try
        let mvarId ← mvarId.assert localDecl.userName localDecl.type localDecl.toExpr
        let mvarIds ← splitMatchTarget mvarId e
        let mvarIds ← mvarIds.mapM fun m => return (← m.intro1P).2
        return some mvarIds
      catch ex =>
        if isDiscrGenException ex then throwDiscrGenError e else throw ex
    throwDiscrGenError e

end SplitNoSimp

/-- Like `split`, but reduces only the `if`/`match` it splits on instead of
running `simp` over the whole goal. Use on large `do`-chains where `split`
overflows `simp`'s step budget. -/
elab "split_ns" : tactic => do
  liftMetaTactic fun mvarId => do
    let some mvarIds ← SplitNoSimp.splitTarget? mvarId
      | throwError "`split_ns` failed: no `if`/`match` to split in the goal"
    return mvarIds

/-- Like `split at h`, but reduces only the `if`/`match` it splits on instead of
running `simp` over the whole hypothesis. -/
elab "split_ns" "at" h:ident : tactic => do
  let fvarId ← getFVarId h
  liftMetaTactic fun mvarId => do
    let some mvarIds ← SplitNoSimp.splitLocalDecl? mvarId fvarId
      | throwError "`split_ns` failed: no `if`/`match` to split in hypothesis `{h.getId}`"
    return mvarIds

end SplitNoSimp
end -- public section

/-- Splits on `h` once, then closes every resulting branch that `simp at h` or
    `contradiction` can fully discharge. Fails unless at least one branch is
    closed, so a `split` that produces no error branch is rejected. Handles
    error branches in any position — first, last, or interleaved.

    Uses the `simp`-free `split_ns` so that large `do`-chains of stuck guards do
    not overflow `simp`'s step budget during the split itself. -/
macro "elim_err" h:ident : tactic =>
  `(tactic| (split_ns at $h:ident; any_goals (solve | simp at $h:ident | contradiction)))

/-- Like `elim_err h`, but additionally names the hypotheses introduced on the
    surviving (success) branch via `rename_i`. Abstracts the ubiquitous
    `elim_err h; rename_i a b …` pattern into a single step. -/
macro "elim_err" h:ident "with" ids:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| (split_ns at $h:ident
             any_goals (solve | simp at $h:ident | contradiction)
             rename_i $ids*))

/-- Repeatedly applies the `elim_err` step to `h`: splits and closes error
    branches until a split no longer produces a closable branch. -/
macro "elim_errs" h:ident : tactic =>
  `(tactic| repeat (split_ns at $h:ident; any_goals (solve | simp at $h:ident | contradiction)))

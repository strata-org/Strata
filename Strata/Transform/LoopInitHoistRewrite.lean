/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.Cmd
public import Strata.Transform.LoopInitHoist

import all Strata.DL.Imperative.Cmd
import all Strata.DL.Imperative.Stmt
import all Strata.Transform.LoopInitHoist

public section

namespace Imperative

variable {P : PureExpr}

/-! # Phase 7.5 redesign: rewrite predicate `RewriteSum`

This file establishes the predicate framework used to characterise the
output of `Block.liftInitsInLoopBody` for the merged `loop_preserves_struct`
theorem in Phase 8. The eventual consumer (the `.loop` arm of the hoisting
preservation proof) needs a STRUCTURAL relation between a source body
`body₁` and the pass's emitted `body₂ = (Block.liftInitsInLoopBody body₁).snd`,
parametrised by the hoisted-names list
`hoistedNames = (Block.liftInitsInLoopBody body₁).fst.flatMap Cmd.definedVars`.

## Encoding

The encoding is a SINGLE inductive predicate `RewriteSum` over the sum
`Stmt P (Cmd P) ⊕ List (Stmt P (Cmd P))`. This avoids `mutual inductive`
(which fails Lean's `induction` tactic on Prop-valued mutuals) and the
function-form alternative (which forced ~395 LoC of `applyHoistRewrite_*`
infrastructure for the discharge — 5–8x the budget).

`Stmt.InitsRewrittenAsSets` and `Block.InitsRewrittenAsSets` are thin
wrappers that publicly project to the appropriate `.inl`/`.inr` side; the
discharge proof works internally on `RewriteSum` and uses the wrappers as
the user-facing API.

## Caveat — `stmt_non_hoisted_cmd` carries `Cmd.definedVars c = []`

The non-init constructor's premise is a STRUCTURAL fact about the cmd
(rather than a name-list relation), tightening β's predicate compared to
the plan's spec. This is correct for THIS use site because
`liftInitsInLoopBody` only emits non-init cmds (whose `definedVars = []`).
If a future hoist optimisation extends the rewrite to `set y rhs` shapes
(which DO have non-empty `definedVars`), this constructor must add a
`stmt_passthrough_cmd` companion with the original disjointness premise.
-/

/-! ## Step 3 — `DisjointModuloRewrite` predicate

The eventual `loop_preserves_struct` consumer also needs a positional
disjointness predicate: every body stmt must be disjoint from the
hoistedNames list, EXCEPT at the rewrite sites themselves (a `set y _ _`
in the OUTPUT body whose `y ∈ hoistedNames` came from an original
`init y _ _ _` rewrite — `y ∈ hoistedNames` is allowed in modifiedVars
precisely because it IS the rewrite target).

`Stmt.DisjointModuloRewrite` is a *function-form* `Prop` recursing
structurally over Stmt. The predicate is shaped to match the OUTPUT of
`liftInitsInLoopBody`:
- `init y _ _ _` cmds at hoistedName positions are FORBIDDEN (the output
  never has them — they've all been rewritten to `set`).
- `set y rhs _` cmds permit `y ∈ hoistedNames` (rewrite-site carve-out)
  but require RHS vars disjoint from hoistedNames.
- `assert/assume/cover _ e _` cmds require `e`'s vars disjoint from
  hoistedNames.

Anti-monotonicity in `hoistedNames` makes the `.ite` arm of the discharge
load-bearing — each branch's witness must be lifted from its own
harvested-name list to the union. The discharge threads
`Block.uniqueInits` (for branch-disjoint harvests) and a strengthened
`Block.hoistedNamesFreshInRhsAndGuards` (for RHS-freshness across the
entire program). -/

mutual

/-- Stmt-level disjointness modulo the rewrite. -/
@[expose] def Stmt.DisjointModuloRewrite [HasVarsPure P P.Expr]
    (hoistedNames : List P.Ident) :
    Stmt P (Cmd P) → Prop
  | .cmd (.init y _ rhs _) =>
    -- Output never has init at hoistedName positions. Plus RHS-freshness.
    y ∉ hoistedNames ∧ ∀ z ∈ hoistedNames, z ∉ ExprOrNondet.getVars rhs
  | .cmd (.set _ rhs _) =>
    -- Rewrite-site allowed: y MAY be in hoistedNames. But rhs is fresh.
    ∀ z ∈ hoistedNames, z ∉ ExprOrNondet.getVars rhs
  | .cmd (.assert _ e _) =>
    ∀ z ∈ hoistedNames, z ∉ HasVarsPure.getVars e
  | .cmd (.assume _ e _) =>
    ∀ z ∈ hoistedNames, z ∉ HasVarsPure.getVars e
  | .cmd (.cover _ e _) =>
    ∀ z ∈ hoistedNames, z ∉ HasVarsPure.getVars e
  | .block _ bss _ => Block.DisjointModuloRewrite hoistedNames bss
  | .ite _ tss ess _ =>
    Block.DisjointModuloRewrite hoistedNames tss ∧
    Block.DisjointModuloRewrite hoistedNames ess
  | .loop _ _ _ body _ =>
    Block.DisjointModuloRewrite hoistedNames body
  | .exit _ _ => True
  | .funcDecl _ _ => True
  | .typeDecl _ _ => True
  termination_by s => sizeOf s

/-- Block-level disjointness modulo the rewrite. -/
@[expose] def Block.DisjointModuloRewrite [HasVarsPure P P.Expr]
    (hoistedNames : List P.Ident) :
    List (Stmt P (Cmd P)) → Prop
  | [] => True
  | s :: rest =>
    Stmt.DisjointModuloRewrite hoistedNames s ∧
    Block.DisjointModuloRewrite hoistedNames rest
  termination_by ss => sizeOf ss

end

/-! ## Strengthened freshness predicate `namesFreshInExprs`

Parametric form: "every `names` element is fresh in every cmd
expression / loop guard / inv / measure at any depth in `s`". Used by
the discharge below to lift each branch's `DisjointModuloRewrite`
witness across the `.ite` union.

The predicate is MONOTONE in `names`'s subset relation (smaller names
list = weaker requirement). It generalises `hoistedNamesFreshInGuards`
by adding the cmd-expression-freshness clause. -/

/-- Helper: list-membership test using `P.EqIdent` (the only decidable
equality available on `P.Ident`). Returns `true` iff `z ∉ vars`. -/
@[expose] def freshFromIdents (z : P.Ident) (vars : List P.Ident) : Bool :=
  vars.all (fun v => ¬ (P.EqIdent z v).decide)

mutual

/-- "names is fresh in s": every name z ∈ names doesn't appear in any
cmd's expression, loop guard, invariant, or measure at any depth in s.
This explicitly does NOT carve out rewrite-target positions — that's
fine because `init y _ rhs _` and `set y _ rhs _` only check `rhs`'s
vars (the modifiedVar y is not constrained by this predicate). -/
@[expose] def Stmt.namesFreshInExprs [HasVarsPure P P.Expr]
    (names : List P.Ident) (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd (.init _ _ rhs _) =>
    names.all (fun z => freshFromIdents z (ExprOrNondet.getVars rhs))
  | .cmd (.set _ rhs _) =>
    names.all (fun z => freshFromIdents z (ExprOrNondet.getVars rhs))
  | .cmd (.assert _ e _) =>
    names.all (fun z => freshFromIdents z (HasVarsPure.getVars e))
  | .cmd (.assume _ e _) =>
    names.all (fun z => freshFromIdents z (HasVarsPure.getVars e))
  | .cmd (.cover _ e _) =>
    names.all (fun z => freshFromIdents z (HasVarsPure.getVars e))
  | .block _ bss _ => Block.namesFreshInExprs names bss
  | .ite g tss ess _ =>
    names.all (fun z => freshFromIdents z (ExprOrNondet.getVars g)) &&
    Block.namesFreshInExprs names tss && Block.namesFreshInExprs names ess
  | .loop g m inv body _ =>
    names.all (fun z => freshFromIdents z (ExprOrNondet.getVars g)) &&
    (match m with
     | none => true
     | some me => names.all (fun z => freshFromIdents z (HasVarsPure.getVars me))) &&
    inv.all (fun p => names.all (fun z => freshFromIdents z (HasVarsPure.getVars p.snd))) &&
    Block.namesFreshInExprs names body
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

/-- "names is fresh in ss": same as `Stmt.namesFreshInExprs` lifted
pointwise across the block. -/
@[expose] def Block.namesFreshInExprs [HasVarsPure P P.Expr]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest =>
    Stmt.namesFreshInExprs names s && Block.namesFreshInExprs names rest
  termination_by sizeOf ss

end

/-- The strengthened freshness predicate: existing
`hoistedNamesFreshInGuards` PLUS `namesFreshInExprs` for the body's own
init-vars. -/
@[expose] def Block.hoistedNamesFreshInRhsAndGuards [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P))) : Bool :=
  Block.hoistedNamesFreshInGuards ss &&
  Block.namesFreshInExprs (Block.initVars ss) ss

/-! ## Expression shape-freedom predicate `exprsShapeFree`

A front-end well-formedness assumption on a source program: every variable
read by any expression occurring in the program — `init`/`set` rhs, `assert`
/`assume`/`cover` conditions, loop guards/measures/invariants, `.ite` guards
— is a "shape-free" name: it is never the identifier of a string carrying the
generator's `_<digits>` suffix.  Equivalently, source programs only mention
program names, which never collide with the generator's freshly-minted naming
scheme.

The predicate is `Prop`-valued (function-form recursion, like
`DisjointModuloRewrite` above) because its leaf condition quantifies over the
`Prop`-valued `String.HasUnderscoreDigitSuffix`.  It mirrors the recursion
shape of `namesFreshInExprs`/`noExit`, descending into `.block`/`.ite`/`.loop`
bodies, and is threaded through the hoisting-preservation proof exactly like
the source-shape-freedom invariant carried for the carrier names.  The
discharge consumer is the `.loop` arm, which needs that the freshly minted
harvest targets (all suffix-shaped) cannot appear among `body`'s read-vars. -/

mutual

/-- "Every read-var occurring in `s` is shape-free": no expression read by `s`
is the identifier of a `_<digits>`-suffixed string. -/
@[expose] def Stmt.exprsShapeFree [HasIdent P] [HasVarsPure P P.Expr]
    (s : Stmt P (Cmd P)) : Prop :=
  match s with
  | .cmd (.init _ _ rhs _) =>
    ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars rhs
  | .cmd (.set _ rhs _) =>
    ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars rhs
  | .cmd (.assert _ e _) =>
    ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .cmd (.assume _ e _) =>
    ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .cmd (.cover _ e _) =>
    ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .block _ bss _ => Block.exprsShapeFree bss
  | .ite g tss ess _ =>
    (∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
    Block.exprsShapeFree tss ∧ Block.exprsShapeFree ess
  | .loop g m inv body _ =>
    (∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
    (match m with
     | none => True
     | some me => ∀ str : String, String.HasUnderscoreDigitSuffix str →
        HasIdent.ident (P := P) str ∉ HasVarsPure.getVars me) ∧
    (∀ p ∈ inv, ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars p.snd) ∧
    Block.exprsShapeFree body
  | .exit _ _ => True
  | .funcDecl _ _ => True
  | .typeDecl _ _ => True
  termination_by sizeOf s

/-- "Every read-var occurring in `ss` is shape-free": pointwise lift of
`Stmt.exprsShapeFree` across the block. -/
@[expose] def Block.exprsShapeFree [HasIdent P] [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P))) : Prop :=
  match ss with
  | [] => True
  | s :: rest =>
    Stmt.exprsShapeFree s ∧ Block.exprsShapeFree rest
  termination_by sizeOf ss

end

/-! ## Shape-only freshness helpers

Name-agnostic helpers over `namesFreshInExprs` retained after the Option E
prune of the same-name rewrite engine. `Stmt/Block.namesFreshInExprs_subset`
is consumed by the §F top-level theorem (to weaken the names argument to
`[]`); `freshFromIdents_not_mem` is its membership lemma. -/

/-! ### Helper: `freshFromIdents` membership characterisation -/

/-- `freshFromIdents z vars = true` implies `z ∉ vars`. -/
private theorem freshFromIdents_not_mem
    {z : P.Ident} {vars : List P.Ident}
    (h : freshFromIdents z vars = true) :
    z ∉ vars := by
  unfold freshFromIdents at h
  rw [List.all_eq_true] at h
  intro hmem
  have h_z := h z hmem
  have h_eq : (P.EqIdent z z).decide = true := by simp
  rw [h_eq] at h_z
  exact absurd h_z (by decide)

/-- `z ∉ vars` implies `freshFromIdents z vars = true`. -/
private theorem freshFromIdents_of_not_mem
    {z : P.Ident} {vars : List P.Ident}
    (h : z ∉ vars) :
    freshFromIdents z vars = true := by
  unfold freshFromIdents
  rw [List.all_eq_true]
  intro v hv
  have h_ne : z ≠ v := fun heq => h (heq ▸ hv)
  have hfalse : (P.EqIdent z v).decide = false := by
    rw [decide_eq_false_iff_not]; exact h_ne
  simp only [hfalse]
  decide

/-! ### Helper: monotonicity in the names list -/

mutual
/-- If `names₁ ⊆ names₂` and `names₂ is fresh in s`, then `names₁ is fresh
in s`. (Smaller names list = weaker constraint = easier to satisfy.) -/
private theorem Stmt.namesFreshInExprs_subset
    [HasVarsPure P P.Expr] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInExprs names₂ s = true) :
    Stmt.namesFreshInExprs names₁ s = true := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.namesFreshInExprs, List.all_eq_true] at h ⊢
        intro z hz; exact h z (h_sub hz)
  | block lbl bss md =>
    simp only [Stmt.namesFreshInExprs] at h ⊢
    exact Block.namesFreshInExprs_subset h_sub bss h
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInExprs, Bool.and_eq_true, List.all_eq_true] at h ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro z hz; exact h.1.1 z (h_sub hz)
    · exact Block.namesFreshInExprs_subset h_sub tss h.1.2
    · exact Block.namesFreshInExprs_subset h_sub ess h.2
  | loop g m inv body md =>
    -- Carefully unfold both sides preserving structure
    unfold Stmt.namesFreshInExprs at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨h_g, h_m⟩, h_inv⟩, h_body⟩ := h
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- guard
      rw [List.all_eq_true] at h_g ⊢
      intro z hz; exact h_g z (h_sub hz)
    · -- measure
      cases m with
      | none => exact h_m
      | some me =>
        simp only at h_m ⊢
        rw [List.all_eq_true] at h_m ⊢
        intro z hz; exact h_m z (h_sub hz)
    · -- inv
      rw [List.all_eq_true] at h_inv ⊢
      intro p hp
      have h_p := h_inv p hp
      rw [List.all_eq_true] at h_p ⊢
      intro z hz; exact h_p z (h_sub hz)
    · -- body
      exact Block.namesFreshInExprs_subset h_sub body h_body
  | exit lbl md =>
    simp only [Stmt.namesFreshInExprs]
  | funcDecl d md =>
    simp only [Stmt.namesFreshInExprs]
  | typeDecl t md =>
    simp only [Stmt.namesFreshInExprs]
  termination_by sizeOf s

private theorem Block.namesFreshInExprs_subset
    [HasVarsPure P P.Expr] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInExprs names₂ ss = true) :
    Block.namesFreshInExprs names₁ ss = true := by
  match ss with
  | [] =>
    simp only [Block.namesFreshInExprs]
  | s :: rest =>
    simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · exact Stmt.namesFreshInExprs_subset h_sub s h.1
    · exact Block.namesFreshInExprs_subset h_sub rest h.2
  termination_by sizeOf ss
end

/-! ### `exprsShapeFree` ⇒ `namesFreshInExprs` for suffix-shaped names

If every name in `names` is the identifier of a `_<digits>`-suffixed string,
and `ss` is shape-free (its read-vars are never suffix-shaped idents), then
`names` is fresh in `ss`'s expressions.  This is the generic core driving the
`.loop` arm's `h_B_fresh` discharge: the harvest TARGETS are all suffix-shaped
idents, the source body is shape-free, so the targets cannot appear among the
body's read-vars. -/

/-- Local helper: a single suffix-shaped name is fresh in a read-var set,
given that set contains no suffix-shaped ident. -/
private theorem freshFromIdents_of_shapefree_leaf [HasIdent P]
    {z : P.Ident} {vars : List P.Ident}
    (h_z : ∃ str : String, z = HasIdent.ident str ∧ String.HasUnderscoreDigitSuffix str)
    (h_sf : ∀ str : String, String.HasUnderscoreDigitSuffix str →
      HasIdent.ident (P := P) str ∉ vars) :
    freshFromIdents z vars = true := by
  obtain ⟨str, h_eq, h_suf⟩ := h_z
  exact freshFromIdents_of_not_mem (h_eq ▸ h_sf str h_suf)

mutual
/-- `exprsShapeFree s` plus "every `names` element is a suffix-shaped ident"
implies `names` is fresh in `s`'s expressions. -/
private theorem Stmt.namesFreshInExprs_of_exprsShapeFree
    [HasIdent P] [HasVarsPure P P.Expr] {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ String.HasUnderscoreDigitSuffix str)
    (s : Stmt P (Cmd P))
    (h : Stmt.exprsShapeFree (P := P) s) :
    Stmt.namesFreshInExprs names s = true := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.exprsShapeFree] at h
        simp only [Stmt.namesFreshInExprs, List.all_eq_true]
        intro z hz
        exact freshFromIdents_of_shapefree_leaf (h_names_suffix z hz) h
  | block lbl bss md =>
    simp only [Stmt.exprsShapeFree] at h
    simp only [Stmt.namesFreshInExprs]
    exact Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix bss h
  | ite g tss ess md =>
    simp only [Stmt.exprsShapeFree] at h
    obtain ⟨h_g, h_tss, h_ess⟩ := h
    simp only [Stmt.namesFreshInExprs, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro z hz
      exact freshFromIdents_of_shapefree_leaf (h_names_suffix z hz) h_g
    · exact Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix tss h_tss
    · exact Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix ess h_ess
  | loop g m inv body md =>
    unfold Stmt.exprsShapeFree at h
    obtain ⟨h_g, h_m, h_inv, h_body⟩ := h
    unfold Stmt.namesFreshInExprs
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro z hz
      exact freshFromIdents_of_shapefree_leaf (h_names_suffix z hz) h_g
    · cases m with
      | none => rfl
      | some me =>
        simp only
        rw [List.all_eq_true]
        intro z hz
        exact freshFromIdents_of_shapefree_leaf (h_names_suffix z hz) h_m
    · rw [List.all_eq_true]
      intro p hp
      rw [List.all_eq_true]
      intro z hz
      exact freshFromIdents_of_shapefree_leaf (h_names_suffix z hz) (fun str hstr => h_inv p hp str hstr)
    · exact Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix body h_body
  | exit lbl md => simp only [Stmt.namesFreshInExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInExprs]
  termination_by sizeOf s

private theorem Block.namesFreshInExprs_of_exprsShapeFree
    [HasIdent P] [HasVarsPure P P.Expr] {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ String.HasUnderscoreDigitSuffix str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) ss) :
    Block.namesFreshInExprs names ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInExprs]
  | s :: rest =>
    simp only [Block.exprsShapeFree] at h
    simp only [Block.namesFreshInExprs, Bool.and_eq_true]
    exact ⟨Stmt.namesFreshInExprs_of_exprsShapeFree h_names_suffix s h.1,
           Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix rest h.2⟩
  termination_by sizeOf ss
end

/-- Public form: `exprsShapeFree ss` plus suffix-shaped `names` give
freshness in exprs.  Re-exported (non-`private`) so the `.loop` arm's
`h_B_fresh` discharge in the WF layer can consume it. -/
theorem Block.namesFreshInExprs_of_exprsShapeFree'
    [HasIdent P] [HasVarsPure P P.Expr] {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ String.HasUnderscoreDigitSuffix str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) ss) :
    Block.namesFreshInExprs names ss = true :=
  Block.namesFreshInExprs_of_exprsShapeFree h_names_suffix ss h

/-! ### `liftInitsInLoopBody` is identity when `initVars = []` -/

/-- Under `Stmt.initVars s = []`, `Stmt.liftInitsInLoopBody s` returns
`([], [s])` (s unchanged).

**Option E port.** This shape-only identity (no `init` anywhere ⇒ nothing
harvested, residual = input) is now proven canonically against the monadic
pass in `LoopInitHoist.lean` as `Stmt.liftInitsInLoopBody_no_inits_eq`: the
fresh-name generator never fires under the no-inits precondition, so the
output is name-independent. This lemma is a thin re-export under the
pure-wrapper API, requiring `[HasIdent P]` (which the wrapper itself needs). -/
private theorem Stmt.liftInitsInLoopBody_no_inits [HasIdent P]
    (s : Stmt P (Cmd P))
    (h_iv : Stmt.initVars s = []) :
    Stmt.liftInitsInLoopBody s = ([], [s]) :=
  Stmt.liftInitsInLoopBody_no_inits_eq s h_iv

/-- Under `Block.initVars ss = []`, `Block.liftInitsInLoopBody ss` returns
`([], ss)` (block unchanged). Thin re-export of the canonical monadic-pass
identity `Block.liftInitsInLoopBody_no_inits_eq`. -/
private theorem Block.liftInitsInLoopBody_no_inits [HasIdent P]
    (ss : List (Stmt P (Cmd P)))
    (h_iv : Block.initVars ss = []) :
    Block.liftInitsInLoopBody ss = ([], ss) :=
  Block.liftInitsInLoopBody_no_inits_eq ss h_iv

end Imperative

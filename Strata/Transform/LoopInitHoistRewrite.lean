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

/-! ## RHS-only freshness predicate `namesFreshInRhsExprs`

A relaxation of `namesFreshInExprs` that checks freshness only against
command *right-hand-side* expressions (`init`/`set` rhs, assertion / assume /
cover conditions) at every depth, but NOT against `.ite`/`.loop` *guard*,
invariant, or measure expressions.  This is the freshness role that
`hoistedNamesFreshInRhsAndGuards` actually consumes for its `initVars`
component: the hoisting proof only ever reads back the RHS / body-recursion
parts of that conjunct — the guard-read clauses are always discarded (the
load-bearing guard freshness comes instead from `hoistedNamesFreshInGuards`
and from the hoist-accumulated-name `namesFreshInExprs A`/`B` instances).

Restricting to RHS positions makes the predicate satisfiable on a pass output
that synthesises `.ite (.det (mkFvar g)) …` / `.loop (.det (mkFvar g)) …`
guards reading a freshly-minted `g` that is simultaneously a top-level
init-var: such an output reads `g` only in a *guard*, never in a command RHS,
so it is RHS-fresh even though it is not guard-fresh.

`namesFreshInExprs names s ⇒ namesFreshInRhsExprs names s` (it drops
hypotheses), proven below as `*_of_namesFreshInExprs`. -/

mutual

/-- "names is fresh in every command RHS of `s`": every `z ∈ names` is absent
from each `init`/`set` rhs and each `assert`/`assume`/`cover` condition at any
depth in `s`, with `.ite`/`.loop` recursing into branches/body only (the
guard/invariant/measure read positions are NOT checked). -/
@[expose] def Stmt.namesFreshInRhsExprs [HasVarsPure P P.Expr]
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
  | .block _ bss _ => Block.namesFreshInRhsExprs names bss
  | .ite _ tss ess _ =>
    Block.namesFreshInRhsExprs names tss && Block.namesFreshInRhsExprs names ess
  | .loop _ _ _ body _ =>
    Block.namesFreshInRhsExprs names body
  | .exit _ _ => true
  | .funcDecl _ _ => true
  | .typeDecl _ _ => true
  termination_by sizeOf s

/-- Block-level RHS-only freshness, lifted pointwise across the block. -/
@[expose] def Block.namesFreshInRhsExprs [HasVarsPure P P.Expr]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest =>
    Stmt.namesFreshInRhsExprs names s && Block.namesFreshInRhsExprs names rest
  termination_by sizeOf ss

end

mutual

/-- The full `namesFreshInExprs` implies the RHS-only relaxation: dropping the
guard/invariant/measure conjuncts only weakens the predicate. -/
theorem Stmt.namesFreshInRhsExprs_of_namesFreshInExprs [HasVarsPure P P.Expr]
    (names : List P.Ident) (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInExprs names s = true) :
    Stmt.namesFreshInRhsExprs names s = true := by
  match s with
  | .cmd (.init _ _ rhs _) => simpa only [Stmt.namesFreshInExprs, Stmt.namesFreshInRhsExprs] using h
  | .cmd (.set _ rhs _) => simpa only [Stmt.namesFreshInExprs, Stmt.namesFreshInRhsExprs] using h
  | .cmd (.assert _ e _) => simpa only [Stmt.namesFreshInExprs, Stmt.namesFreshInRhsExprs] using h
  | .cmd (.assume _ e _) => simpa only [Stmt.namesFreshInExprs, Stmt.namesFreshInRhsExprs] using h
  | .cmd (.cover _ e _) => simpa only [Stmt.namesFreshInExprs, Stmt.namesFreshInRhsExprs] using h
  | .block _ bss _ =>
      simp only [Stmt.namesFreshInExprs] at h
      simp only [Stmt.namesFreshInRhsExprs]
      exact Block.namesFreshInRhsExprs_of_namesFreshInExprs names bss h
  | .ite g tss ess _ =>
      simp only [Stmt.namesFreshInExprs, Bool.and_eq_true] at h
      simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true]
      exact ⟨Block.namesFreshInRhsExprs_of_namesFreshInExprs names tss h.1.2,
             Block.namesFreshInRhsExprs_of_namesFreshInExprs names ess h.2⟩
  | .loop g m inv body _ =>
      unfold Stmt.namesFreshInExprs at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨⟨_, _⟩, _⟩, h_body⟩ := h
      simp only [Stmt.namesFreshInRhsExprs]
      exact Block.namesFreshInRhsExprs_of_namesFreshInExprs names body h_body
  | .exit _ _ => simp only [Stmt.namesFreshInRhsExprs]
  | .funcDecl _ _ => simp only [Stmt.namesFreshInRhsExprs]
  | .typeDecl _ _ => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_of_namesFreshInExprs [HasVarsPure P P.Expr]
    (names : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInExprs names ss = true) :
    Block.namesFreshInRhsExprs names ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
      simp only [Block.namesFreshInExprs, Bool.and_eq_true] at h
      simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true]
      exact ⟨Stmt.namesFreshInRhsExprs_of_namesFreshInExprs names s h.1,
             Block.namesFreshInRhsExprs_of_namesFreshInExprs names rest h.2⟩
  termination_by sizeOf ss

end

mutual
/-- `namesFreshInRhsExprs` is monotone in the `names` subset relation: a
smaller name list is a weaker requirement. -/
theorem Stmt.namesFreshInRhsExprs_subset
    [HasVarsPure P P.Expr] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (s : Stmt P (Cmd P))
    (h : Stmt.namesFreshInRhsExprs names₂ s = true) :
    Stmt.namesFreshInRhsExprs names₁ s = true := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.namesFreshInRhsExprs, List.all_eq_true] at h ⊢
        intro z hz; exact h z (h_sub hz)
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs] at h ⊢
    exact Block.namesFreshInRhsExprs_subset h_sub bss h
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true] at h ⊢
    exact ⟨Block.namesFreshInRhsExprs_subset h_sub tss h.1,
           Block.namesFreshInRhsExprs_subset h_sub ess h.2⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs] at h ⊢
    exact Block.namesFreshInRhsExprs_subset h_sub body h
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_subset
    [HasVarsPure P P.Expr] {names₁ names₂ : List P.Ident}
    (h_sub : names₁ ⊆ names₂)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.namesFreshInRhsExprs names₂ ss = true) :
    Block.namesFreshInRhsExprs names₁ ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true] at h ⊢
    exact ⟨Stmt.namesFreshInRhsExprs_subset h_sub s h.1,
           Block.namesFreshInRhsExprs_subset h_sub rest h.2⟩
  termination_by sizeOf ss
end

/-- `Block.namesFreshInRhsExprs` distributes over `++`. -/
theorem Block.namesFreshInRhsExprs_append
    [HasVarsPure P P.Expr] {names : List P.Ident}
    (xs ys : List (Stmt P (Cmd P)))
    (hx : Block.namesFreshInRhsExprs names xs = true)
    (hy : Block.namesFreshInRhsExprs names ys = true) :
    Block.namesFreshInRhsExprs names (xs ++ ys) = true := by
  induction xs with
  | nil => simpa only [List.nil_append] using hy
  | cons x rest ih =>
    simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true] at hx
    simp only [List.cons_append, Block.namesFreshInRhsExprs, Bool.and_eq_true]
    exact ⟨hx.1, ih hx.2⟩

mutual
/-- The empty name list is RHS-fresh in every statement. -/
theorem Stmt.namesFreshInRhsExprs_nil [HasVarsPure P P.Expr] (s : Stmt P (Cmd P)) :
    Stmt.namesFreshInRhsExprs (P := P) [] s = true := by
  cases s with
  | cmd c => cases c <;> simp only [Stmt.namesFreshInRhsExprs, List.all_nil]
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs]; exact Block.namesFreshInRhsExprs_nil bss
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true]
    exact ⟨Block.namesFreshInRhsExprs_nil tss, Block.namesFreshInRhsExprs_nil ess⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs]; exact Block.namesFreshInRhsExprs_nil body
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_nil [HasVarsPure P P.Expr] (ss : List (Stmt P (Cmd P))) :
    Block.namesFreshInRhsExprs (P := P) [] ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true]
    exact ⟨Stmt.namesFreshInRhsExprs_nil s, Block.namesFreshInRhsExprs_nil rest⟩
  termination_by sizeOf ss
end

mutual
/-- `namesFreshInRhsExprs` over a `cons` name list splits as the head-singleton
freshness and the tail freshness (the leaf is `names.all`, which splits as
`f hd && tail.all f`). -/
theorem Stmt.namesFreshInRhsExprs_cons_names
    [HasVarsPure P P.Expr] (hd : P.Ident) (tl : List P.Ident) (s : Stmt P (Cmd P))
    (h_hd : Stmt.namesFreshInRhsExprs (P := P) [hd] s = true)
    (h_tl : Stmt.namesFreshInRhsExprs (P := P) tl s = true) :
    Stmt.namesFreshInRhsExprs (P := P) (hd :: tl) s = true := by
  cases s with
  | cmd c =>
    cases c <;>
      · simp only [Stmt.namesFreshInRhsExprs, List.all_cons, List.all_nil,
          Bool.and_true] at h_hd h_tl ⊢
        exact Bool.and_eq_true _ _ ▸ ⟨h_hd, h_tl⟩
  | block lbl bss md =>
    simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact Block.namesFreshInRhsExprs_cons_names hd tl bss h_hd h_tl
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInRhsExprs, Bool.and_eq_true] at h_hd h_tl ⊢
    exact ⟨Block.namesFreshInRhsExprs_cons_names hd tl tss h_hd.1 h_tl.1,
           Block.namesFreshInRhsExprs_cons_names hd tl ess h_hd.2 h_tl.2⟩
  | loop g m inv body md =>
    simp only [Stmt.namesFreshInRhsExprs] at h_hd h_tl ⊢
    exact Block.namesFreshInRhsExprs_cons_names hd tl body h_hd h_tl
  | exit lbl md => simp only [Stmt.namesFreshInRhsExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInRhsExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInRhsExprs]
  termination_by sizeOf s

theorem Block.namesFreshInRhsExprs_cons_names
    [HasVarsPure P P.Expr] (hd : P.Ident) (tl : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h_hd : Block.namesFreshInRhsExprs (P := P) [hd] ss = true)
    (h_tl : Block.namesFreshInRhsExprs (P := P) tl ss = true) :
    Block.namesFreshInRhsExprs (P := P) (hd :: tl) ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInRhsExprs]
  | s :: rest =>
    simp only [Block.namesFreshInRhsExprs, Bool.and_eq_true] at h_hd h_tl ⊢
    exact ⟨Stmt.namesFreshInRhsExprs_cons_names hd tl s h_hd.1 h_tl.1,
           Block.namesFreshInRhsExprs_cons_names hd tl rest h_hd.2 h_tl.2⟩
  termination_by sizeOf ss
end

/-- Assemble `namesFreshInRhsExprs names ss` from per-name singleton facts. -/
theorem Block.namesFreshInRhsExprs_of_forall_mem
    [HasVarsPure P P.Expr] (names : List P.Ident) (ss : List (Stmt P (Cmd P)))
    (h : ∀ z ∈ names, Block.namesFreshInRhsExprs (P := P) [z] ss = true) :
    Block.namesFreshInRhsExprs (P := P) names ss = true := by
  induction names with
  | nil => exact Block.namesFreshInRhsExprs_nil ss
  | cons hd tl ih =>
    exact Block.namesFreshInRhsExprs_cons_names hd tl ss
      (h hd (List.mem_cons_self ..)) (ih (fun z hz => h z (List.mem_cons_of_mem _ hz)))

/-- The strengthened freshness predicate: existing
`hoistedNamesFreshInGuards` PLUS RHS-only freshness for the body's own
init-vars.  The second conjunct uses `namesFreshInRhsExprs` (not the full
`namesFreshInExprs`): the hoisting preservation proof reads back only the
RHS / body-recursion parts of this conjunct, so the guard-read clauses would
be dead weight — and dropping them lets a pass output that reads a fresh
init-var only in a synthesised guard still satisfy the predicate. -/
@[expose] def Block.hoistedNamesFreshInRhsAndGuards [HasVarsPure P P.Expr]
    (ss : List (Stmt P (Cmd P))) : Bool :=
  Block.hoistedNamesFreshInGuards ss &&
  Block.namesFreshInRhsExprs (Block.initVars ss) ss

/-! ## Expression shape-freedom predicate `exprsShapeFree`

A front-end well-formedness assumption on a source program: every variable
read by any expression occurring in the program — `init`/`set` rhs, `assert`
/`assume`/`cover` conditions, loop guards/measures/invariants, `.ite` guards
— is a "kind-free" name: it never satisfies the *kind predicate* `Q` on the
underlying label string (the kind of name *this* pass mints).  Instantiating
`Q := String.HasUnderscoreDigitSuffix` recovers the blanket "shape-free"
condition: source programs only mention program names, which never collide
with the generator's freshly-minted naming scheme.  A per-kind `Q` lets a
composition argument restrict the obligation to just the labels this pass
mints rather than every gen-suffix-shaped name.

The predicate is `Prop`-valued (function-form recursion, like
`DisjointModuloRewrite` above) because its leaf condition quantifies over the
`Prop`-valued kind predicate `Q`.  It mirrors the recursion shape of
`namesFreshInExprs`/`noExit`, descending into `.block`/`.ite`/`.loop` bodies,
and is threaded through the hoisting-preservation proof exactly like the
source-shape-freedom invariant carried for the carrier names.  The discharge
consumer is the `.loop` arm, which needs that the freshly minted harvest
targets (all of kind `Q`) cannot appear among `body`'s read-vars. -/

mutual

/-- "Every read-var occurring in `s` is kind-free": no expression read by `s`
is the identifier of a `Q`-kind label string. -/
@[expose] def Stmt.exprsShapeFree [HasIdent P] [HasVarsPure P P.Expr]
    (Q : String → Prop)
    (s : Stmt P (Cmd P)) : Prop :=
  match s with
  | .cmd (.init _ _ rhs _) =>
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars rhs
  | .cmd (.set _ rhs _) =>
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars rhs
  | .cmd (.assert _ e _) =>
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .cmd (.assume _ e _) =>
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .cmd (.cover _ e _) =>
    ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars e
  | .block _ bss _ => Block.exprsShapeFree Q bss
  | .ite g tss ess _ =>
    (∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
    Block.exprsShapeFree Q tss ∧ Block.exprsShapeFree Q ess
  | .loop g m inv body _ =>
    (∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ ExprOrNondet.getVars g) ∧
    (match m with
     | none => True
     | some me => ∀ str : String, Q str →
        HasIdent.ident (P := P) str ∉ HasVarsPure.getVars me) ∧
    (∀ p ∈ inv, ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ HasVarsPure.getVars p.snd) ∧
    Block.exprsShapeFree Q body
  | .exit _ _ => True
  | .funcDecl _ _ => True
  | .typeDecl _ _ => True
  termination_by sizeOf s

/-- "Every read-var occurring in `ss` is kind-free": pointwise lift of
`Stmt.exprsShapeFree` across the block. -/
@[expose] def Block.exprsShapeFree [HasIdent P] [HasVarsPure P P.Expr]
    (Q : String → Prop)
    (ss : List (Stmt P (Cmd P))) : Prop :=
  match ss with
  | [] => True
  | s :: rest =>
    Stmt.exprsShapeFree Q s ∧ Block.exprsShapeFree Q rest
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

/-- Public membership characterisation of `freshFromIdents` (both directions),
re-exported (non-`private`) so cross-pass bridges can decode the
`hoistedNamesFreshInGuards` enclosing-vars leaf. -/
theorem freshFromIdents_iff_not_mem
    {z : P.Ident} {vars : List P.Ident} :
    freshFromIdents z vars = true ↔ z ∉ vars :=
  ⟨freshFromIdents_not_mem, freshFromIdents_of_not_mem⟩

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

mutual
/-- The empty name list is fresh in every statement's expressions: each leaf is
`[].all _`, which is `true`. -/
theorem Stmt.namesFreshInExprs_nil [HasVarsPure P P.Expr] (s : Stmt P (Cmd P)) :
    Stmt.namesFreshInExprs (P := P) [] s = true := by
  cases s with
  | cmd c => cases c <;> simp only [Stmt.namesFreshInExprs, List.all_nil]
  | block lbl bss md =>
    simp only [Stmt.namesFreshInExprs]; exact Block.namesFreshInExprs_nil bss
  | ite g tss ess md =>
    simp only [Stmt.namesFreshInExprs, List.all_nil, Bool.true_and, Bool.and_eq_true]
    exact ⟨Block.namesFreshInExprs_nil tss, Block.namesFreshInExprs_nil ess⟩
  | loop g m inv body md =>
    unfold Stmt.namesFreshInExprs
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, Block.namesFreshInExprs_nil body⟩
    · simp only [List.all_nil]
    · cases m <;> simp only [List.all_nil]
    · rw [List.all_eq_true]; intro p _; simp only [List.all_nil]
  | exit lbl md => simp only [Stmt.namesFreshInExprs]
  | funcDecl d md => simp only [Stmt.namesFreshInExprs]
  | typeDecl t md => simp only [Stmt.namesFreshInExprs]
  termination_by sizeOf s

theorem Block.namesFreshInExprs_nil [HasVarsPure P P.Expr] (ss : List (Stmt P (Cmd P))) :
    Block.namesFreshInExprs (P := P) [] ss = true := by
  match ss with
  | [] => simp only [Block.namesFreshInExprs]
  | s :: rest =>
    simp only [Block.namesFreshInExprs, Bool.and_eq_true]
    exact ⟨Stmt.namesFreshInExprs_nil s, Block.namesFreshInExprs_nil rest⟩
  termination_by sizeOf ss
end

/-! ### `exprsShapeFree` ⇒ `namesFreshInExprs` for kind-shaped names

If every name in `names` is the identifier of a `Q`-kind label string, and
`ss` is kind-free (its read-vars are never `Q`-kind idents), then `names` is
fresh in `ss`'s expressions.  This is the generic core driving the `.loop`
arm's `h_B_fresh` discharge: the harvest TARGETS are all of this pass's kind,
the source body is kind-free, so the targets cannot appear among the body's
read-vars. -/

/-- Local helper: a single `Q`-kind name is fresh in a read-var set, given
that set contains no `Q`-kind ident. -/
private theorem freshFromIdents_of_shapefree_leaf [HasIdent P]
    {Q : String → Prop}
    {z : P.Ident} {vars : List P.Ident}
    (h_z : ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (h_sf : ∀ str : String, Q str →
      HasIdent.ident (P := P) str ∉ vars) :
    freshFromIdents z vars = true := by
  obtain ⟨str, h_eq, h_suf⟩ := h_z
  exact freshFromIdents_of_not_mem (h_eq ▸ h_sf str h_suf)

mutual
/-- `exprsShapeFree s` plus "every `names` element is a `Q`-kind ident"
implies `names` is fresh in `s`'s expressions. -/
private theorem Stmt.namesFreshInExprs_of_exprsShapeFree
    [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (s : Stmt P (Cmd P))
    (h : Stmt.exprsShapeFree (P := P) Q s) :
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
    [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q ss) :
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

/-- Public form: `exprsShapeFree ss` plus `Q`-kind `names` give freshness in
exprs.  Re-exported (non-`private`) so the `.loop` arm's `h_B_fresh` discharge
in the WF layer can consume it. -/
theorem Block.namesFreshInExprs_of_exprsShapeFree'
    [HasIdent P] [HasVarsPure P P.Expr] {Q : String → Prop} {names : List P.Ident}
    (h_names_suffix : ∀ z ∈ names,
      ∃ str : String, z = HasIdent.ident str ∧ Q str)
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exprsShapeFree (P := P) Q ss) :
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

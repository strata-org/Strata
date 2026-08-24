/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.LangDef
public import Strata.Languages.Core.StatementSemanticsProps
import all Strata.Languages.Core.Logic.LangDef
import all Strata.Languages.Core.StatementSemanticsProps
import all Strata.DL.Imperative.StmtProps
import all Strata.DL.Imperative.StmtSemanticsProps

/-! # Lowering and preservation of the Core initial-environment conditions

`Core.Logic.InitEnvWF` and `BlockInitEnvWF` are the initial-environment
well-formedness conditions of `Lang.core` and
`Lang.coreBlock`.  A *compositional* program logic over those languages needs to
move a condition around a derivation, in two directions:

* **lowering** — from an enclosing statement (or statement list) to a
  sub-derivation: `blockInitEnvWF_cons_head`, `blockInitEnvWF_singleton`,
  `blockInitEnvWF_append_head`, `blockInitEnvWF_of_block`,
  `blockInitEnvWF_of_ite_then` / `_else`, `blockInitEnvWF_of_loop_body`;
* **preservation** — re-establishing a condition at the environment a sub-derivation
  terminates in: `blockInitEnvWF_cons_tail` (after the head statement runs),
  `blockInitEnvWF_append_tail` (after a whole prefix list runs) and
  `initEnvWF_loop_iterate` (after one loop-body iteration).

Together these are exactly the side conditions the structural rules of
`Imperative.Logic.Hoare` ask for, so `Strata.Languages.Core.Logic.Hoare` can
state its rules directly over `Lang.core` / `Lang.coreBlock`.

## Two facts do the work

1. **`defUseOk` subsumes `readWritesDefined`.**  `Stmt.defUseWellFormed` is
   flow-sensitive and decomposes structurally, so it is available at every level
   of a derivation; and by `Imperative.Stmt.defined_of_mem_touchedVars` it
   *implies* the flat `readWritesDefined` condition.  So `readWritesDefined` is
   never transferred — it is re-derived wherever it is needed.  That is what
   makes lowering possible at all: the flat condition on a statement list exempts
   names its *siblings* define, which the flat condition on one member does not.

2. **`projectStore` restores the parent's store domain.**  Leaving a block puts back
   exactly the definedness the parent had, so a condition stated in terms of the store's
   domain survives the exit unchanged.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

variable (π : String → Option Procedure)
variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-! ## Builders that discharge `readWritesDefined` from `defUseOk` -/

/-- Core commands have no nested scope, so `Command.definedVars` ignores the
    `excludeScoped` flag.  This is the side condition of the def-use bridge
    `Imperative.Stmt.defined_of_mem_touchedVars`. -/
private theorem cmdDefinedVarsFlagIrrelevant :
    Imperative.CmdDefinedVarsFlagIrrelevant Expression Command := fun _ _ h => h

/-- Build an `InitEnvWF` without supplying `readWritesDefined`: it follows from
    `defUseOk` via `Imperative.Stmt.defined_of_mem_touchedVars`. -/
theorem InitEnvWF.of_defUseOk {params : InitEnvWFParams} {s : Statement}
    {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hdefs : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone)
    (hdnr : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hfnr : ∀ n ∈ Stmt.funcDeclNames s false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hres : ∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hdu : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs s = Bool.true)
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true) :
    InitEnvWF params s ρ where
  toWellFormedSemanticEval := hwf
  storeWellDefined := hsv
  readWritesDefined := fun _ hn hnd =>
    Imperative.Stmt.defined_of_mem_touchedVars cmdDefinedVarsFlagIrrelevant hdu hn hnd
  defsUndefined := hdefs
  definedVarsNotReserved := hdnr
  funcDeclNamesNotReserved := hfnr
  reservedFresh := hres
  defUseOk := hdu
  factoryDeclared := hfd

/-- Build a `BlockInitEnvWF` without supplying `readWritesDefined`: it follows from
    `defUseOk`. -/
theorem BlockInitEnvWF.of_defUseOk {params : InitEnvWFParams} {bss : Statements}
    {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hdefs : ∀ n ∈ Block.definedVars bss false, (ρ.store n).isNone)
    (hdnr : ∀ n ∈ Block.definedVars bss false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hfnr : ∀ n ∈ Block.funcDeclNames bss false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hres : ∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hdu : Block.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs bss = Bool.true)
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true) :
    BlockInitEnvWF params bss ρ where
  toWellFormedSemanticEval := hwf
  storeWellDefined := hsv
  readWritesDefined := fun _ hn hnd =>
    Imperative.Block.defined_of_mem_touchedVars cmdDefinedVarsFlagIrrelevant hdu hn hnd
  defsUndefined := hdefs
  definedVarsNotReserved := hdnr
  funcDeclNamesNotReserved := hfnr
  reservedFresh := hres
  defUseOk := hdu
  factoryDeclared := hfd

/-! ## Lowering: enclosing condition → sub-derivation condition

Each of these drops `readWritesDefined` on the floor (it is re-derived by
`of_defUseOk`) and otherwise just restricts the remaining fields along the
corresponding `Stmt.*`/`Block.*` accessor equation. -/

/-- Head of a statement list: the block condition on `s :: ss` lowers to the
    statement condition on `s`.  Note this is *not* pure subsetting — the block's
    `readWritesDefined` exempts names `ss` defines, which `s`'s does not; it is
    the head conjunct of `defUseOk` that closes the gap. -/
theorem blockInitEnvWF_cons_head {params : InitEnvWFParams} {s : Statement} {ss : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params (s :: ss) ρ) :
    InitEnvWF params s ρ := by
  have hdu := h.defUseOk
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  refine InitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => h.defsUndefined n (by rw [Block.definedVars]; exact List.mem_append.mpr (Or.inl hn)))
    (fun n hn => h.definedVarsNotReserved n (by rw [Block.definedVars]; exact List.mem_append.mpr (Or.inl hn)))
    (fun n hn => h.funcDeclNamesNotReserved n (by rw [Block.funcDeclNames]; exact List.mem_append.mpr (Or.inl hn)))
    h.reservedFresh hdu.1 h.factoryDeclared

/-- Singleton statement list: the block condition on `[s]` lowers to the statement
    condition on `s`. -/
theorem blockInitEnvWF_singleton {params : InitEnvWFParams} {s : Statement}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params [s] ρ) :
    InitEnvWF params s ρ :=
  blockInitEnvWF_cons_head h

/-- Names a statement list scopes are undefined at its entry: `defsUndefined` covers the
    `excludeScoped := false` set, which contains the `true` one.  This is what makes
    leaving a block a *drop* of exactly those names, as `PostWF` reads it. -/
theorem blockInitEnvWF_bodyDefsUndefined {params : InitEnvWFParams} {ss : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params ss ρ) :
    ∀ x ∈ Block.definedVars (P := Expression) (C := Command) ss true, ρ.store x = none :=
  fun x hx => by
    have hn := h.defsUndefined x (Imperative.Block.definedVars_true_subset_false
      cmdDefinedVarsFlagIrrelevant hx)
    simpa using hn

/-- Prefix of a statement list: the block condition on `ss₁ ++ ss₂` lowers to the
    block condition on `ss₁`.  There is no suffix counterpart at the same
    environment — `ss₂` was checked against the predicates `ss₁` extends, so it needs
    the environment `ss₁` terminates in; that is `blockInitEnvWF_append_tail`. -/
theorem blockInitEnvWF_append_head {params : InitEnvWFParams} {ss₁ ss₂ : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params (ss₁ ++ ss₂) ρ) :
    BlockInitEnvWF params ss₁ ρ := by
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  have hfnr := h.funcDeclNamesNotReserved
  rw [Imperative.Block.definedVars_append] at hdefs hdnr
  rw [Imperative.Block.funcDeclNames_append] at hfnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hfnr n (List.mem_append.mpr (Or.inl hn)))
    h.reservedFresh (Imperative.Block.defUseWellFormed_of_append_left h.defUseOk)
    h.factoryDeclared

/-- Block statement: the statement condition on `.block l ss md` lowers to the
    block condition on the body `ss`. -/
theorem blockInitEnvWF_of_block {params : InitEnvWFParams} {ss : Statements}
    {l : String} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.block l ss md) ρ) :
    BlockInitEnvWF params ss ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  have hfnr := h.funcDeclNamesNotReserved
  simp only [Stmt.defUseWellFormed] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, if_false] at hdefs hdnr
  simp only [Stmt.funcDeclNames, Bool.false_eq_true, if_false] at hfnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined hdefs hdnr hfnr
    h.reservedFresh hdu h.factoryDeclared

/-- `ite`: the statement condition lowers to the block condition on the *then*
    branch. -/
theorem blockInitEnvWF_of_ite_then {params : InitEnvWFParams} {c : Expression.Expr}
    {tss ess : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.ite (.det c) tss ess md) ρ) :
    BlockInitEnvWF params tss ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  have hfnr := h.funcDeclNamesNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, if_false] at hdefs hdnr
  simp only [Stmt.funcDeclNames, Bool.false_eq_true, if_false] at hfnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hfnr n (List.mem_append.mpr (Or.inl hn)))
    h.reservedFresh hdu.1.2 h.factoryDeclared

/-- `ite`: the statement condition lowers to the block condition on the *else*
    branch. -/
theorem blockInitEnvWF_of_ite_else {params : InitEnvWFParams} {c : Expression.Expr}
    {tss ess : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.ite (.det c) tss ess md) ρ) :
    BlockInitEnvWF params ess ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  have hfnr := h.funcDeclNamesNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, if_false] at hdefs hdnr
  simp only [Stmt.funcDeclNames, Bool.false_eq_true, if_false] at hfnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inr hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inr hn)))
    (fun n hn => hfnr n (List.mem_append.mpr (Or.inr hn)))
    h.reservedFresh hdu.2 h.factoryDeclared

/-- `loop`: the statement condition lowers to the block condition on the body. -/
theorem blockInitEnvWF_of_loop_body {params : InitEnvWFParams} {g : Expression.Expr}
    {m : Option Expression.Expr} {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.loop (.det g) m inv body md) ρ) :
    BlockInitEnvWF params body ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  have hfnr := h.funcDeclNamesNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, if_false] at hdefs hdnr
  simp only [Stmt.funcDeclNames, Bool.false_eq_true, if_false] at hfnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined hdefs hdnr hfnr
    h.reservedFresh hdu.2 h.factoryDeclared

/-! ## Preservation: re-establishing a condition after a sub-derivation runs

Every field of the conditions transfers structurally except `storeWellDefined`, which
is a statement about *values* rather than about the store's domain, and so is the one
field a run has to be shown to preserve.  Both lemmas below get it from
`Imperative.Config.storeWellDefined_star_of`, whose only side condition is
`Stmt.noFuncDecl s = true` (resp. `Block.noFuncDecl ss = true`) — syntactic and
decidable.  It makes the factory constant across the run
(`Imperative.noFuncDecl_preserves_factory`), so value-hood is trivially preserved.

The call needs no recursion into the callee: every rule that writes to the store,
`call` included, supplies a value of the factory in force. -/

/-- Tail of a statement list: after the head `s` runs to `ρ'`, the block condition
    holds on the tail `ss` at `ρ'`.

    `hnofd` is the strong "no `funcDecl` anywhere" rather than "none at top level"
    because it also has to keep the factory and the declared-function set constant
    across the run. -/
theorem blockInitEnvWF_cons_tail {params : InitEnvWFParams} {s : Statement} {ss : Statements}
    {ρ ρ' : Imperative.Env Expression}
    (hnofd : Stmt.noFuncDecl (P := Expression) (C := Command) s = Bool.true)
    (h : BlockInitEnvWF params (s :: ss) ρ)
    (hrun : CoreStepStar π φ (.stmt s ρ) (.terminal ρ')) :
    BlockInitEnvWF params ss ρ' := by
  have hfdn : Stmt.funcDeclNames (P := Expression) (C := Command) s true = [] :=
    Imperative.Stmt.funcDeclNames_eq_nil_of_noFuncDecl s true hnofd
  have hfac : ρ'.factory = ρ.factory :=
    Imperative.stmt_noFuncDecl_preserves_factory Expression (EvalCommand π φ) (EvalPureFunc φ)
      s ρ ρ' hnofd (Core.CoreStepStar_to_StepStmtStar hrun)
  -- The tail was checked against `defined ∪ Stmt.definedVars s true` …
  have hdu := h.defUseOk
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  -- … and that predicate is exactly `ρ'`'s definedness predicate.
  have hstore : (fun n => (ρ'.store n).isSome)
      = (fun n => (ρ.store n).isSome ||
          decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) := by
    funext n; exact core_stmt_run_terminal_store_isSome_eq π φ hrun n
  -- `declaredFuncs` accumulates too, but `hnofd` makes that extension inert.
  have hdecl : (fun n => params.declaredFuncs n ||
      decide (n ∈ Stmt.funcDeclNames (P := Expression) (C := Command) s true))
      = params.declaredFuncs := by
    funext n; simp [hfdn]
  -- Names the tail defines are fresh in that predicate, hence undefined in `ρ`
  -- and not defined at the head's top level — so they survive `s` undefined.
  have hfresh : ∀ n ∈ Block.definedVars (P := Expression) (C := Command) ss false,
      ρ.store n = none ∧ n ∉ Stmt.definedVars (P := Expression) (C := Command) s true := by
    intro n hn
    have hb := Imperative.Block.not_defined_of_mem_definedVars hdu.2 hn
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hb
    refine ⟨?_, by simpa using h2⟩
    cases hq : ρ.store n with
    | none => rfl
    | some v => rw [hq] at h1; simp at h1
  refine BlockInitEnvWF.of_defUseOk
    (by rw [hfac]; exact h.toWellFormedSemanticEval)
    (Imperative.Config.storeWellDefined_star_of
      (evalCmd := EvalCommand π φ) (extendFactory := EvalPureFunc φ)
      (fun hc hs => Core.evalCommand_storeWellDefined π φ hc hs)
      (Core.CoreStepStar_to_StepStmtStar hrun) hnofd h.storeWellDefined)
    (fun n hn => ?_) (fun n hn => h.definedVarsNotReserved n ?_)
    (fun n hn => h.funcDeclNamesNotReserved n ?_) (fun n hn => ?_) ?_ h.factoryDeclared
  · -- defsUndefined on the tail
    obtain ⟨hnone, hnotdef⟩ := hfresh n hn
    rw [core_stmt_run_terminal_preserves_none_of_not_definedVars_true π φ hnotdef hnone hrun]
    rfl
  · rw [Block.definedVars]; exact List.mem_append.mpr (Or.inr hn)
  · rw [Block.funcDeclNames]; exact List.mem_append.mpr (Or.inr hn)
  · -- reservedFresh at `ρ'`: a name defined there was defined in `ρ`, or is one
    -- of the head's top-level definitions (which the enclosing condition covers).
    have hn' : ((ρ.store n).isSome ||
        decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) = Bool.true := by
      rw [← congrFun hstore n]; exact hn
    rcases Bool.or_eq_true_iff.mp hn' with hold | hnew
    · exact h.reservedFresh n hold
    · refine h.definedVarsNotReserved n ?_
      rw [Block.definedVars]
      exact List.mem_append.mpr (Or.inl
        (Imperative.Stmt.definedVars_true_subset_false cmdDefinedVarsFlagIrrelevant
          (by simpa using hnew)))
  · -- defUseOk on the tail, by rewriting both predicates
    rw [hstore, ← hdecl]; exact hdu.2

/-- Suffix of a statement list: after the prefix `ss₁` runs to `ρ'`, the block
    condition holds on `ss₂` at `ρ'`.

    One statement at a time, by `blockInitEnvWF_cons_tail`: `ss₁`'s run splits at each
    head, and the enclosing condition on `(s :: rest) ++ ss₂` is literally the one on
    `s :: (rest ++ ss₂)` that the cons lemma consumes. -/
theorem blockInitEnvWF_append_tail {params : InitEnvWFParams} {ss₁ ss₂ : Statements}
    {ρ ρ' : Imperative.Env Expression}
    (hnofd : Block.noFuncDecl (P := Expression) (C := Command) ss₁ = Bool.true)
    (h : BlockInitEnvWF params (ss₁ ++ ss₂) ρ)
    (hrun : CoreStepStar π φ (.stmts ss₁ ρ) (.terminal ρ')) :
    BlockInitEnvWF params ss₂ ρ' := by
  suffices hgen : ∀ (pfx : Statements) (ρ₀ : Imperative.Env Expression),
      Block.noFuncDecl (P := Expression) (C := Command) pfx = Bool.true →
      BlockInitEnvWF params (pfx ++ ss₂) ρ₀ →
      CoreStepStar π φ (.stmts pfx ρ₀) (.terminal ρ') →
      BlockInitEnvWF params ss₂ ρ' from hgen ss₁ ρ hnofd h hrun
  intro pfx
  induction pfx with
  | nil =>
    intro ρ₀ _ hb hr
    have heq : ρ₀ = ρ' :=
      Imperative.stmts_nil_terminal (EvalCommand π φ) (EvalPureFunc φ) ρ₀ ρ'
        (Core.CoreStepStar_to_StepStmtStar hr)
    subst heq; simpa using hb
  | cons s rest ih =>
    intro ρ₀ hnofd' hb hr
    simp only [Imperative.Block.noFuncDecl, Bool.and_eq_true] at hnofd'
    have hsplit : ∃ ρ_mid,
        Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.stmt s ρ₀) (.terminal ρ_mid) ∧
        Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.stmts rest ρ_mid) (.terminal ρ') := by
      cases Core.CoreStepStar_to_StepStmtStar hr with
      | step _ _ _ hstep hrest => cases hstep with
        | step_stmts_cons =>
          exact Imperative.seq_reaches_terminal Expression (EvalCommand π φ)
            (EvalPureFunc φ) hrest
    obtain ⟨ρ_mid, hs, hrest⟩ := hsplit
    exact ih ρ_mid hnofd'.2
      (blockInitEnvWF_cons_tail π φ hnofd'.1 hb (Core.StepStmtStar_to_CoreStepStar hs))
      (Core.StepStmtStar_to_CoreStepStar hrest)

/-- One loop iteration: the loop's own condition is re-established at the environment
    the body's block leaves behind.

    Leaving the body's block projects the inner store through the parent's and
    restores the parent factory, so that environment has *pointwise the same*
    definedness predicate and the same factory as the one the iteration started
    from.  Every field of `InitEnvWF` sees the environment only through those two,
    so the condition transfers unchanged. -/
theorem initEnvWF_loop_iterate {params : InitEnvWFParams} {g : Expression.Expr}
    {m : Option Expression.Expr} {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression}
    {ρ ρ_inner : Imperative.Env Expression}
    (hnofd : Block.noFuncDecl (P := Expression) (C := Command) body = Bool.true)
    (h : InitEnvWF params (.loop (.det g) m inv body md) ρ)
    (hrun : CoreStepStar π φ (.stmts body ρ) (.terminal ρ_inner)) :
    InitEnvWF params (.loop (.det g) m inv body md)
      { ρ_inner with store := projectStore ρ.store ρ_inner.store, factory := ρ.factory } := by
  have hstore : ∀ n, ((projectStore ρ.store ρ_inner.store) n).isSome = (ρ.store n).isSome := by
    intro n
    by_cases hn : (ρ.store n).isSome = Bool.true
    · simp only [projectStore, hn, if_true]
      exact core_stmts_preserves_isSome π φ hrun hn
    · have hnone : ρ.store n = none := by
        cases hq : ρ.store n with
        | none => rfl
        | some v => rw [hq] at hn; simp at hn
      simp [projectStore, hnone]
  have hfun : (fun n => ((projectStore ρ.store ρ_inner.store) n).isSome)
      = (fun n => (ρ.store n).isSome) := funext hstore
  -- `noFuncDecl` keeps the factory constant, so the inner store holds only values of
  -- `ρ.factory`; and `projectStore` only ever keeps a binding or drops it.
  have hproj : Imperative.WellFormedStore (projectStore ρ.store ρ_inner.store) ρ.factory := by
    have hfac : ρ_inner.factory = ρ.factory :=
      Imperative.block_noFuncDecl_preserves_factory Expression (EvalCommand π φ)
        (EvalPureFunc φ) body ρ ρ_inner hnofd (Core.CoreStepStar_to_StepStmtStar hrun)
    have hinner : Imperative.WellFormedStore ρ_inner.store ρ.factory := by
      rw [← hfac]
      exact Imperative.Config.storeWellDefined_star_of
        (evalCmd := EvalCommand π φ) (extendFactory := EvalPureFunc φ)
        (fun hc hs => Core.evalCommand_storeWellDefined π φ hc hs)
        (Core.CoreStepStar_to_StepStmtStar hrun) hnofd h.storeWellDefined
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact hinner x w hx
    · exact absurd hx (by simp)
  refine InitEnvWF.of_defUseOk h.toWellFormedSemanticEval hproj (fun n hn => ?_)
    h.definedVarsNotReserved h.funcDeclNamesNotReserved (fun n hn => ?_) ?_ h.factoryDeclared
  · -- defsUndefined: `isNone` is `¬ isSome`, and the predicate is unchanged.
    have := h.defsUndefined n hn
    show (projectStore ρ.store ρ_inner.store n).isNone
    rw [Option.isNone_iff_eq_none] at this ⊢
    simp [projectStore, this]
  · -- reservedFresh: same predicate.
    exact h.reservedFresh n (by rw [← hstore n]; exact hn)
  · -- defUseOk: same predicate.
    show Stmt.defUseWellFormed
      (fun n => ((projectStore ρ.store ρ_inner.store) n).isSome) params.declaredFuncs _ = Bool.true
    rw [hfun]; exact h.defUseOk


/-! ## A trivially-satisfiable condition

For an *empty* body every field of `BlockInitEnvWF` that mentions the statements is
vacuous, so the condition reduces to the generic evaluator well-formedness,
`storeWellDefined`, and the two conditions that mention only `params`.  This is what
lets a test exhibit a concrete initial environment (to *refute* a contract) without
discharging the def-use and freshness machinery. -/

/-- The block condition on an *empty* body, from evaluator well-formedness, store
    well-definedness, and the two conditions that mention only `params`.  Every
    remaining field quantifies over the body's statements and so is vacuous. -/
theorem blockInitEnvWF_nil {params : InitEnvWFParams} {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hpref : params.prefixIdents = [])
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true →
      params.declaredFuncs ⟨nm, ()⟩ = Bool.true) :
    BlockInitEnvWF params [] ρ := by
  refine BlockInitEnvWF.of_defUseOk hwf hsv (fun n hn => ?_) (fun n hn => ?_) (fun n hn => ?_)
    (fun n _ p hp => ?_) rfl hfd
  · simp [Block.definedVars] at hn
  · simp [Block.definedVars] at hn
  · simp [Block.funcDeclNames] at hn
  · rw [hpref] at hp; simp at hp

/-- The block condition for an empty procedure body wrapped as its procedure block:
    every clause that mentions the statements is vacuous. -/
theorem blockInitEnvWF_procBlock_nil {params : InitEnvWFParams} {ρ : Imperative.Env Expression}
    {l : String} {md : Imperative.MetaData Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hpref : params.prefixIdents = [])
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true →
      params.declaredFuncs ⟨nm, ()⟩ = Bool.true) :
    BlockInitEnvWF params [Imperative.Stmt.block l [] md] ρ := by
  refine BlockInitEnvWF.of_defUseOk hwf hsv (fun n hn => ?_) (fun n hn => ?_) (fun n hn => ?_)
    (fun n _ p hp => ?_) ?_ hfd
  · simp [Block.definedVars, Stmt.definedVars] at hn
  · simp [Block.definedVars, Stmt.definedVars] at hn
  · simp [Block.funcDeclNames, Stmt.funcDeclNames] at hn
  · rw [hpref] at hp; simp at hp
  · simp [Block.defUseWellFormed, Stmt.defUseWellFormed]

end Core.Logic

end -- public section

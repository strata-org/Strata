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
well-formedness conditions of `EventLang.core` and
`EventLang.coreBlock`.  A *compositional* program logic over those languages needs to
move a condition around a derivation, in two directions:

* **lowering** — from an enclosing statement (or statement list) to a
  sub-derivation: `blockInitEnvWF_cons_head`, `blockInitEnvWF_singleton`,
  `blockInitEnvWF_append_head`, `blockInitEnvWF_of_block`,
  `blockInitEnvWF_of_ite_then` / `_else`, `blockInitEnvWF_of_loop_body`;
* **preservation** — re-establishing a condition at the environment an
  event-trace sub-derivation terminates in: `blockInitEnvWF_cons_tailE`,
  `blockInitEnvWF_append_tailE`, and `initEnvWF_loop_iterateE`.

Together these are exactly the side conditions the structural rules of
`Imperative.Logic.Hoare` ask for, so `Strata.Languages.Core.Logic.Hoare` can
state its rules directly over `EventLang.core` / `EventLang.coreBlock`.

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

/-- The reserved prefixes of `base.extend prefixes` are `prefixes` followed by
the base's reserved prefixes. -/
@[simp] theorem InitEnvWFParams.extend_prefixIdents
    (base : InitEnvWFParams) (prefixes : List String) :
    (base.extend prefixes).prefixIdents = prefixes ++ base.prefixIdents := rfl

/-- Extending the reserved prefixes keeps the declared functions. -/
@[simp] theorem InitEnvWFParams.extend_declaredFuncs
    (base : InitEnvWFParams) (prefixes : List String) :
    (base.extend prefixes).declaredFuncs = base.declaredFuncs := rfl

variable (π : String → Option Procedure)

/-! ## Builders that discharge `readWritesDefined` from `defUseOk` -/

/-- Core commands have no nested scope, so `Command.definedVars` ignores the
    `excludeScoped` flag.  This is the side condition of the def-use bridge
    `Imperative.Stmt.defined_of_mem_touchedVars`. -/
private theorem cmdDefinedVarsFlagIrrelevant :
    Imperative.CmdDefinedVarsFlagIrrelevant Expression Command := fun _ _ h => h

/-- Every Core identifier is represented by its string name. -/
private theorem ident_eq_ident_name (ident : Expression.Ident) :
    ident = HasIdent.ident (P := Expression) ident.name := by
  cases ident with
  | mk name metadata => cases metadata; rfl

/-- Core-shaped view of the generic reserved-prefix condition on block
definitions. -/
theorem BlockInitEnvWF.definedVarsNotReservedCore
    {params : InitEnvWFParams} {bss : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params bss ρ)
    (ident : Expression.Ident) (hident : ident ∈ Block.definedVars bss false)
    (pfx : String) (hpfx : pfx ∈ params.prefixIdents) :
    ¬ pfx.toList.isPrefixOf ident.name.toList :=
  h.definedVarsNotReserved ident hident ident.name
    (ident_eq_ident_name ident) pfx hpfx

/-- Core-shaped view of the generic reserved-prefix condition on existing
bindings. -/
theorem BlockInitEnvWF.reservedFreshCore
    {params : InitEnvWFParams} {bss : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params bss ρ)
    (ident : Expression.Ident) (hdefined : (ρ.store ident).isSome)
    (pfx : String) (hpfx : pfx ∈ params.prefixIdents) :
    ¬ pfx.toList.isPrefixOf ident.name.toList :=
  h.reservedFresh ident hdefined ident.name
    (ident_eq_ident_name ident) pfx hpfx

/-- Core-shaped view of the generic reserved-prefix condition on CFG
definitions. -/
theorem CFGInitEnvWF.definedVarsNotReservedCore
    {params : InitEnvWFParams} {cfg : Core.DetCFG}
    {ρ : Imperative.Env Expression} (h : CFGInitEnvWF params cfg ρ)
    (ident : Expression.Ident)
    (hident : ident ∈ HasVarsImp.definedVars (P := Expression) cfg false)
    (pfx : String) (hpfx : pfx ∈ params.prefixIdents) :
    ¬ pfx.toList.isPrefixOf ident.name.toList :=
  h.definedVarsNotReserved ident hident ident.name
    (ident_eq_ident_name ident) pfx hpfx

/-- Core-shaped view of the generic reserved-prefix condition on existing CFG
bindings. -/
theorem CFGInitEnvWF.reservedFreshCore
    {params : InitEnvWFParams} {cfg : Core.DetCFG}
    {ρ : Imperative.Env Expression} (h : CFGInitEnvWF params cfg ρ)
    (ident : Expression.Ident) (hdefined : (ρ.store ident).isSome)
    (pfx : String) (hpfx : pfx ∈ params.prefixIdents) :
    ¬ pfx.toList.isPrefixOf ident.name.toList :=
  h.reservedFresh ident hdefined ident.name
    (ident_eq_ident_name ident) pfx hpfx

/-- Build an `InitEnvWF` without supplying `readWritesDefined`: it follows from
    `defUseOk` via `Imperative.Stmt.defined_of_mem_touchedVars`. -/
theorem InitEnvWF.of_defUseOk {params : InitEnvWFParams} {s : Statement}
    {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hdefs : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone)
    (hdnr : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hres : ∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hdu : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs s = Bool.true)
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true)
    (hinit : Stmt.InitTypesInhabited (P := Expression) (C := Command) ρ.factory s)
    (hty : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧ Stmt.fvarTypesWellAnnotated Γ s) :
    InitEnvWF params s ρ where
  toWellFormedSemanticEval := hwf
  storeWellDefined := hsv
  readWritesDefined := fun _ hn hnd =>
    Imperative.Stmt.defined_of_mem_touchedVars cmdDefinedVarsFlagIrrelevant hdu hn hnd
  defsUndefined := hdefs
  definedVarsNotReserved := hdnr
  reservedFresh := hres
  defUseOk := hdu
  factoryDeclared := hfd
  initTypesInhabited := hinit
  fvarTypesOk := hty

/-- Every variable read by a well-formed block avoids every reserved prefix. -/
theorem BlockInitEnvWF.getVarsNotReserved {params : InitEnvWFParams}
    {bss : Statements} {ρ : Imperative.Env Expression}
    (h : BlockInitEnvWF params bss ρ) {n : Expression.Ident}
    (hn : n ∈ Block.getVars bss) {p : String} (hp : p ∈ params.prefixIdents) :
    ¬ p.toList.isPrefixOf n.name.toList := by
  by_cases hd : n ∈ Block.definedVars bss false
  · exact h.definedVarsNotReservedCore n hd p hp
  · exact h.reservedFreshCore n
      (h.readWritesDefined n (by simp [Block.touchedVars, hn]) hd) p hp

/-- Build a `BlockInitEnvWF` without supplying `readWritesDefined`: it follows from
    `defUseOk`. -/
theorem BlockInitEnvWF.of_defUseOk {params : InitEnvWFParams} {bss : Statements}
    {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hdefs : ∀ n ∈ Block.definedVars bss false, (ρ.store n).isNone)
    (hdnr : ∀ n ∈ Block.definedVars bss false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hres : ∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hdu : Block.defUseWellFormed (fun n => (ρ.store n).isSome) params.declaredFuncs bss = Bool.true)
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true)
    (hinit : Block.InitTypesInhabited (P := Expression) (C := Command) ρ.factory bss)
    (hty : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧ Block.fvarTypesWellAnnotated Γ bss) :
    BlockInitEnvWF params bss ρ where
  toWellFormedSemanticEval := hwf
  storeWellDefined := hsv
  readWritesDefined := fun _ hn hnd =>
    Imperative.Block.defined_of_mem_touchedVars
      cmdDefinedVarsFlagIrrelevant hdu hn hnd
  defsUndefined := hdefs
  defUseOk := hdu
  definedVarsNotReserved := by
    intro ident hident name heq pfx hpfx
    have hname : ident.name = name := congrArg (fun i : Expression.Ident => i.name) heq
    rw [← hname]
    exact hdnr ident hident pfx hpfx
  reservedFresh := by
    intro ident hdefined name heq pfx hpfx
    have hname : ident.name = name := congrArg (fun i : Expression.Ident => i.name) heq
    rw [← hname]
    exact hres ident hdefined pfx hpfx
  factoryDeclared := hfd
  initTypesInhabited := hinit
  fvarTypesOk := hty

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
    (fun n hn => h.definedVarsNotReservedCore n
      (by rw [Block.definedVars]; exact List.mem_append.mpr (Or.inl hn)))
    h.reservedFreshCore hdu.1 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by rw [Block.initTypes]; exact List.mem_append.mpr (Or.inl hty)))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      simp only [Block.fvarTypesWellAnnotated] at hw
      exact ⟨Γ, hσ, hw.1⟩)

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
    the environment `ss₁` terminates in; that is `blockInitEnvWF_append_tailE`. -/
theorem blockInitEnvWF_append_head {params : InitEnvWFParams} {ss₁ ss₂ : Statements}
    {ρ : Imperative.Env Expression} (h : BlockInitEnvWF params (ss₁ ++ ss₂) ρ) :
    BlockInitEnvWF params ss₁ ρ := by
  have hdefs := h.defsUndefined
  rw [Imperative.Block.definedVars_append] at hdefs
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => h.definedVarsNotReservedCore n
      (by rw [Imperative.Block.definedVars_append]
          exact List.mem_append.mpr (Or.inl hn)))
    h.reservedFreshCore (Imperative.Block.defUseWellFormed_of_append_left h.defUseOk)
    h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by rw [Block.initTypes_append]; exact List.mem_append.mpr (Or.inl hty)))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      exact ⟨Γ, hσ, Imperative.Block.fvarTypesWellAnnotated_of_append_left hw⟩)

/-- Block statement: the statement condition on `.block l ss md` lowers to the
    block condition on the body `ss`. -/
theorem blockInitEnvWF_of_block {params : InitEnvWFParams} {ss : Statements}
    {l : String} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.block l ss md) ρ) :
    BlockInitEnvWF params ss ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Stmt.defUseWellFormed] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined hdefs hdnr
    h.reservedFresh hdu h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty (by simp only [Stmt.initTypes]; exact hty))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      simp only [Stmt.fvarTypesWellAnnotated] at hw
      exact ⟨Γ, hσ, hw⟩)

/-- `ite`: the statement condition lowers to the block condition on the *then*
    branch. -/
theorem blockInitEnvWF_of_ite_then {params : InitEnvWFParams} {c : Expression.Expr}
    {tss ess : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.ite (.det c) tss ess md) ρ) :
    BlockInitEnvWF params tss ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inl hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inl hn)))
    h.reservedFresh hdu.1.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by simp only [Stmt.initTypes]; exact List.mem_append.mpr (Or.inl hty)))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      simp only [Stmt.fvarTypesWellAnnotated] at hw
      exact ⟨Γ, hσ, hw.2.1⟩)

/-- `ite`: the statement condition lowers to the block condition on the *else*
    branch. -/
theorem blockInitEnvWF_of_ite_else {params : InitEnvWFParams} {c : Expression.Expr}
    {tss ess : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.ite (.det c) tss ess md) ρ) :
    BlockInitEnvWF params ess ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined
    (fun n hn => hdefs n (List.mem_append.mpr (Or.inr hn)))
    (fun n hn => hdnr n (List.mem_append.mpr (Or.inr hn)))
    h.reservedFresh hdu.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty
      (by simp only [Stmt.initTypes]; exact List.mem_append.mpr (Or.inr hty)))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      simp only [Stmt.fvarTypesWellAnnotated] at hw
      exact ⟨Γ, hσ, hw.2.2⟩)

/-- `loop`: the statement condition lowers to the block condition on the body. -/
theorem blockInitEnvWF_of_loop_body {params : InitEnvWFParams} {g : Expression.Expr}
    {m : Option Expression.Expr} {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression} {ρ : Imperative.Env Expression}
    (h : InitEnvWF params (.loop (.det g) m inv body md) ρ) :
    BlockInitEnvWF params body ρ := by
  have hdu := h.defUseOk
  have hdefs := h.defsUndefined
  have hdnr := h.definedVarsNotReserved
  simp only [Stmt.defUseWellFormed, Bool.and_eq_true] at hdu
  simp only [Stmt.definedVars, Bool.false_eq_true, ite_false] at hdefs hdnr
  exact BlockInitEnvWF.of_defUseOk h.toWellFormedSemanticEval h.storeWellDefined hdefs hdnr
    h.reservedFresh hdu.2 h.factoryDeclared
    (fun ty hty => h.initTypesInhabited ty (by simp only [Stmt.initTypes]; exact hty))
    (by
      obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
      simp only [Stmt.fvarTypesWellAnnotated] at hw
      exact ⟨Γ, hσ, hw.2.2.2⟩)

/-! ## Preservation: re-establishing a condition after a sub-derivation runs

Every field of the conditions transfers structurally except `storeWellDefined`, which
is a statement about *values* rather than about the store's domain, and so is the one
field a run has to be shown to preserve. Factory preservation keeps value-hood
measured against the same evaluator throughout the run.

The call needs no recursion into the callee: every rule that writes to the store,
`call` included, supplies a value of the factory in force.

The lemmas below are stated for the event semantics (`StepStmtStarE` /
`EvalCommandE`), so the event Hoare rule `Core.Logic.Hoare.seq` can re-establish
`BlockInitEnvWF` on the suffix after a prefix run. -/

/-- After the head `s` runs to `ρ'`
along the event semantics, the block condition holds on the tail `ss` at `ρ'`. -/
theorem blockInitEnvWF_cons_tailE {params : InitEnvWFParams} {s : Statement} {ss : Statements}
    {ρ ρ' : Imperative.Env Expression} {tr : Imperative.Trace Expression}
    (h : BlockInitEnvWF params (s :: ss) ρ)
    (hrun : Imperative.StepStmtStarE Expression (EvalCommandE π)
      (.stmt s ρ) tr (.terminal ρ')) :
    BlockInitEnvWF params ss ρ' := by
  have hdu := h.defUseOk
  simp only [Block.defUseWellFormed, Bool.and_eq_true] at hdu
  -- The tail's definedness predicate is exactly `ρ'`'s.
  have hstore : (fun n => (ρ'.store n).isSome)
      = (fun n => (ρ.store n).isSome ||
          decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) := by
    funext n; exact core_stmt_run_terminal_store_isSome_eqE π hrun n
  have hfresh : ∀ n ∈ Block.definedVars (P := Expression) (C := Command) ss false,
      ρ.store n = none ∧ n ∉ Stmt.definedVars (P := Expression) (C := Command) s true := by
    intro n hn
    have hb := Imperative.Block.not_defined_of_mem_definedVars hdu.2 hn
    obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp hb
    refine ⟨?_, by simpa using h2⟩
    cases hq : ρ.store n with
    | none => rfl
    | some v => rw [hq] at h1; simp at h1
  have hpres : ∀ {f : Expression.Factory} {σ σ' : CoreStore} {c : Command} {emitted : Imperative.Trace Expression},
      EvalCommandE π f σ c σ' emitted →
      Imperative.WellFormedStore σ f → Imperative.WellFormedStore σ' f :=
    fun hc hs => Core.evalCommandE_storeWellDefined π hc hs
  -- The run preserves the factory.
  have hfac : ρ.factory = ρ'.factory := Imperative.starE_preserves_factory hrun
  refine BlockInitEnvWF.of_defUseOk
    (hfac ▸ h.toWellFormedSemanticEval)
    (Imperative.Config.storeWellDefined_star_ofE
      (EvalCmd := EvalCommandE π) hpres
      hrun
      h.storeWellDefined)
    (fun n hn => ?_) (fun n hn => h.definedVarsNotReservedCore n ?_)
    (fun n hn => ?_) ?_ h.factoryDeclared
    (fun ty hty => hfac ▸ h.initTypesInhabited ty
      (by rw [Block.initTypes]; exact List.mem_append.mpr (Or.inr hty)))
    ?_
  · obtain ⟨hnone, hnotdef⟩ := hfresh n hn
    rw [core_stmt_run_terminal_preserves_none_of_not_definedVars_trueE π hnotdef hnone hrun]
    rfl
  · rw [Block.definedVars]; exact List.mem_append.mpr (Or.inr hn)
  · have hn' : ((ρ.store n).isSome ||
        decide (n ∈ Stmt.definedVars (P := Expression) (C := Command) s true)) = Bool.true := by
      rw [← congrFun hstore n]; exact hn
    rcases Bool.or_eq_true_iff.mp hn' with hold | hnew
    · exact h.reservedFreshCore n hold
    · refine h.definedVarsNotReservedCore n ?_
      rw [Block.definedVars]
      exact List.mem_append.mpr (Or.inl
        (Imperative.Stmt.definedVars_true_subset_false cmdDefinedVarsFlagIrrelevant
          (by simpa using hnew)))
  · rw [hstore]; exact hdu.2
  · obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
    simp only [Block.fvarTypesWellAnnotated] at hw
    exact ⟨_, core_stmt_run_storeHasTyping_extendE π hrun hσ, hw.2⟩

/-- After the prefix `ss₁` runs to
    `ρ'` along the event semantics, the block condition holds on `ss₂` at `ρ'`.
    One statement at a time, splitting the event run with `stmts_cons_headE` /
    `seq_reaches_terminalE`. -/
theorem blockInitEnvWF_append_tailE {params : InitEnvWFParams} {ss₁ ss₂ : Statements}
    {ρ ρ' : Imperative.Env Expression} {tr : Imperative.Trace Expression}
    (h : BlockInitEnvWF params (ss₁ ++ ss₂) ρ)
    (hrun : Imperative.StepStmtStarE Expression (EvalCommandE π)
      (.stmts ss₁ ρ) tr (.terminal ρ')) :
    BlockInitEnvWF params ss₂ ρ' := by
  suffices hgen : ∀ (pfx : Statements) (ρ₀ : Imperative.Env Expression)
      (tr₀ : Imperative.Trace Expression),
      BlockInitEnvWF params (pfx ++ ss₂) ρ₀ →
      Imperative.StepStmtStarE Expression (EvalCommandE π)
        (.stmts pfx ρ₀) tr₀ (.terminal ρ') →
      BlockInitEnvWF params ss₂ ρ' from hgen ss₁ ρ tr h hrun
  intro pfx
  induction pfx with
  | nil =>
    intro ρ₀ tr₀ hb hr
    obtain ⟨_, hcfg⟩ := Imperative.stmts_nil_runE (EvalCommandE π) hr
    rcases hcfg with hcfg | hcfg
    · exact absurd hcfg (by simp)
    · injection hcfg with hρ; subst hρ; simpa using hb
  | cons s rest ih =>
    intro ρ₀ tr₀ hb hr
    rcases Imperative.stmts_cons_headE (EvalCommandE π) hr with
      ⟨hcfg, _⟩ | hseq
    · exact absurd hcfg (by simp)
    · obtain ⟨ρ_mid, _, _, _, hs, hrest⟩ :=
        Imperative.seq_reaches_terminalE (EvalCommandE π) hseq
      exact ih ρ_mid _
        (blockInitEnvWF_cons_tailE π hb hs) hrest


/-- After one event-native loop-body
iteration the loop's own condition is re-established at the environment the
body's block leaves behind. Leaving the block projects the inner store through
the parent's and restores the parent factory, preserving the definedness
predicate and factory observed by `InitEnvWF`. -/
theorem initEnvWF_loop_iterateE {params : InitEnvWFParams} {g : Expression.Expr}
    {m : Option Expression.Expr} {inv : List (String × Expression.Expr)}
    {body : Statements} {md : Imperative.MetaData Expression}
    {ρ ρ_inner : Imperative.Env Expression} {tr : Imperative.Trace Expression}
    (h : InitEnvWF params (.loop (.det g) m inv body md) ρ)
    (hrun : Imperative.StepStmtStarE Expression (EvalCommandE π)
      (.stmts body ρ) tr (.terminal ρ_inner)) :
    InitEnvWF params (.loop (.det g) m inv body md)
      { ρ_inner with store := projectStore ρ.store ρ_inner.store } := by
  have hstore : ∀ n, ((projectStore ρ.store ρ_inner.store) n).isSome = (ρ.store n).isSome := by
    intro n
    by_cases hn : (ρ.store n).isSome = Bool.true
    · simp only [projectStore, hn, ite_true]
      exact core_stmts_preserves_isSomeE π hrun hn
    · have hnone : ρ.store n = none := by
        cases hq : ρ.store n with
        | none => rfl
        | some v => rw [hq] at hn; simp at hn
      simp [projectStore, hnone]
  have hfun : (fun n => ((projectStore ρ.store ρ_inner.store) n).isSome)
      = (fun n => (ρ.store n).isSome) := funext hstore
  have hfac : ρ.factory = ρ_inner.factory := Imperative.starE_preserves_factory hrun
  have hproj : Imperative.WellFormedStore (projectStore ρ.store ρ_inner.store) ρ_inner.factory := by
    have hpres : ∀ {f : Expression.Factory} {σ σ' : CoreStore} {c : Command} {emitted : Imperative.Trace Expression},
        EvalCommandE π f σ c σ' emitted →
        Imperative.WellFormedStore σ f → Imperative.WellFormedStore σ' f :=
      fun hc hs => Core.evalCommandE_storeWellDefined π hc hs
    have hinner : Imperative.WellFormedStore ρ_inner.store ρ_inner.factory :=
      Imperative.Config.storeWellDefined_star_ofE
        (EvalCmd := EvalCommandE π) hpres
        hrun
        h.storeWellDefined
    intro x w hx
    simp only [projectStore] at hx
    split at hx
    · exact hinner x w hx
    · exact absurd hx (by simp)
  refine InitEnvWF.of_defUseOk (hfac ▸ h.toWellFormedSemanticEval) hproj (fun n hn => ?_)
    h.definedVarsNotReserved (fun n hn => ?_) ?_ h.factoryDeclared
    (hfac ▸ h.initTypesInhabited) ?_
  · have hdef := h.defsUndefined n hn
    show (projectStore ρ.store ρ_inner.store n).isNone
    rw [Option.isNone_iff_eq_none] at hdef ⊢
    simp [projectStore, hdef]
  · exact h.reservedFresh n (by rw [← hstore n]; exact hn)
  · show Stmt.defUseWellFormed
      (fun n => ((projectStore ρ.store ρ_inner.store) n).isSome) params.declaredFuncs _ = Bool.true
    rw [hfun]; exact h.defUseOk
  · obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
    refine ⟨Γ, fun y ty hy => ?_, hw⟩
    have hsome : (ρ.store y).isSome = Bool.true := by
      obtain ⟨w, hw', _⟩ := hσ y ty hy
      simp [hw']
    obtain ⟨v, hv, hvt⟩ := core_stmts_preserves_typedAtE π hrun (hσ y ty hy)
    exact ⟨v, by simp [projectStore, hsome, hv], hvt⟩


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
  refine BlockInitEnvWF.of_defUseOk hwf hsv (fun n hn => ?_) (fun n hn => ?_)
    (fun n _ p hp => ?_) rfl hfd (by intro ty hty; simp [Block.initTypes] at hty)
    ⟨fun _ => none, fun _ _ h => by simp at h, trivial⟩
  · simp [Block.definedVars] at hn
  · simp [Block.definedVars] at hn
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
  refine BlockInitEnvWF.of_defUseOk hwf hsv (fun n hn => ?_) (fun n hn => ?_)
    (fun n _ p hp => ?_) ?_ hfd (by intro ty hty; simp [Block.initTypes, Stmt.initTypes] at hty)
    ⟨fun _ => none, fun _ _ h => by simp at h,
      by simp [Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated]⟩
  · simp [Block.definedVars, Stmt.definedVars] at hn
  · simp [Block.definedVars, Stmt.definedVars] at hn
  · rw [hpref] at hp; simp at hp
  · simp [Block.defUseWellFormed, Stmt.defUseWellFormed]

/-- A Core block condition projects to its generic Imperative parent. -/
theorem BlockInitEnvWF.toImperative {params : InitEnvWFParams}
    {bss : Statements} {ρ : Imperative.Env Expression}
    (h : BlockInitEnvWF params bss ρ) :
    Imperative.Logic.BlockInitEnvWF (P := Expression) (CmdT := Command)
      params bss ρ :=
  h.toBlockInitEnvWF

end Core.Logic

end -- public section

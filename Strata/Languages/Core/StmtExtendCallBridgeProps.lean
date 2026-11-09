/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Logic.LangDefProps
public import Strata.DL.Imperative.StmtExtendCallBridgeProps

/-! # Core-specific residue of the call-free bridge

The generic call-free bridge between extended (`CmdExt P`) and base (`Cmd P`)
Imperative syntax, and all of its command-generic properties, live in
`Strata.DL.Imperative.StmtExtendCallBridge(Props)`.  Core specializes that bridge
at its expression type `Expression` (so `CmdExt Expression = Command`) simply by
using the generic `embed*` / `project*` API.

This module keeps only what is genuinely Core-specific — the facts that mention a
concrete call predicate or Core's init-environment well-formedness, and cannot be
stated at the generic layer:

* projection succeeds exactly on the call-free fragment, phrased with Core's
  `Statement.isNotCall` / `Statements.noCalls`; and
* Core `BlockInitEnvWF` transports across projection and embedding
  (`Core.Logic`), phrased with `InitEnvWFParams` and both the Core and generic
  `BlockInitEnvWF`.

Everything else (inversion, round trips, injectivity, analysis commutation, and
the native event-step/star correspondence) is reused from the generic module. -/

public section

namespace Core

open Imperative

/-! ## Projection succeeds exactly on the call-free fragment

These are the only bridge facts that mention Core's concrete call predicates
`Statement.isNotCall` / `Statements.noCalls`, so they stay Core-side. -/

mutual
/-- A Core statement all of whose substatements are non-calls projects
successfully to a base statement. -/
theorem projectStmt_some_of_allSubstmts {s : Statement}
    (h : Imperative.Stmt.allSubstmts Statement.isNotCall s = true) :
    ∃ b, projectStmt s = some b := by
  cases s with
  | cmd c =>
      cases c with
      | cmd cc => exact ⟨.cmd cc, by simp [projectStmt, projectCommand]⟩
      | call pn as md => simp [Stmt.allSubstmts, Statement.isNotCall] at h
  | block label ss md =>
      simp only [Stmt.allSubstmts, Statement.isNotCall, Bool.true_and] at h
      obtain ⟨bs, hbs⟩ := projectStmts_some_of_allSubstmts h
      exact ⟨.block label bs md, by simp [projectStmt, hbs]⟩
  | ite cond tss ess md =>
      simp only [Stmt.allSubstmts, Statement.isNotCall, Bool.true_and, Bool.and_eq_true] at h
      obtain ⟨tbs, htbs⟩ := projectStmts_some_of_allSubstmts h.1
      obtain ⟨ebs, hebs⟩ := projectStmts_some_of_allSubstmts h.2
      exact ⟨.ite cond tbs ebs md, by simp [projectStmt, htbs, hebs]⟩
  | loop guard measure invariant body md =>
      simp only [Stmt.allSubstmts, Statement.isNotCall, Bool.true_and] at h
      obtain ⟨bbs, hbbs⟩ := projectStmts_some_of_allSubstmts h
      exact ⟨.loop guard measure invariant bbs md, by simp [projectStmt, hbbs]⟩
  | exit label md => exact ⟨.exit label md, by simp [projectStmt]⟩
  | typeDecl tc md => exact ⟨.typeDecl tc md, by simp [projectStmt]⟩

/-- A Core statement list all of whose substatements are non-calls projects
successfully to base statements. -/
theorem projectStmts_some_of_allSubstmts {ss : Statements}
    (h : Imperative.Block.allSubstmts Statement.isNotCall ss = true) :
    ∃ bs, projectStmts ss = some bs := by
  cases ss with
  | nil => exact ⟨[], by simp [projectStmts]⟩
  | cons s rest =>
      simp only [Block.allSubstmts, Bool.and_eq_true] at h
      obtain ⟨b, hb⟩ := projectStmt_some_of_allSubstmts h.1
      obtain ⟨bs, hbs⟩ := projectStmts_some_of_allSubstmts h.2
      exact ⟨b :: bs, by simp [projectStmts, hb, hbs]⟩
end

/-- A call-free list of Core statements is the embedding of its projection:
    projection succeeds and re-embeds to the original. -/
theorem noCalls_projectStmts {ss : Statements} (h : Statements.noCalls ss = true) :
    ∃ bs, projectStmts ss = some bs ∧ embedStmts bs = ss := by
  simp only [Statements.noCalls] at h
  obtain ⟨bs, hbs⟩ := projectStmts_some_of_allSubstmts h
  exact ⟨bs, hbs, embedStmts_projectStmts hbs⟩

/-! ## The embedding lands in the call-free fragment -/

mutual
/-- Every substatement of an embedded base statement is a non-call. -/
theorem embedStmt_allSubstmts_isNotCall (s : Imperative.Stmt Expression (Cmd Expression)) :
    Imperative.Stmt.allSubstmts Statement.isNotCall (embedStmt s) = true := by
  cases s with
  | cmd c => simp [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall]
  | block lbl ss md =>
      simp only [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and]
      exact embedStmts_allSubstmts_isNotCall ss
  | ite cond tss ess md =>
      simp only [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and]
      rw [Bool.and_eq_true]; exact ⟨embedStmts_allSubstmts_isNotCall tss,
                                  embedStmts_allSubstmts_isNotCall ess⟩
  | loop g m inv body md =>
      simp only [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall, Bool.true_and]
      exact embedStmts_allSubstmts_isNotCall body
  | exit lbl md => simp [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall]
  | typeDecl t md => simp [embedStmt, Imperative.Stmt.allSubstmts, Statement.isNotCall]

/-- Every substatement of an embedded base statement list is a non-call. -/
theorem embedStmts_allSubstmts_isNotCall (ss : List (Imperative.Stmt Expression (Cmd Expression))) :
    Imperative.Block.allSubstmts Statement.isNotCall (embedStmts ss) = true := by
  cases ss with
  | nil => simp [embedStmts, Imperative.Block.allSubstmts]
  | cons s rest =>
      simp only [embedStmts, Imperative.Block.allSubstmts]
      rw [Bool.and_eq_true]; exact ⟨embedStmt_allSubstmts_isNotCall s,
                                  embedStmts_allSubstmts_isNotCall rest⟩
end

/-- The embedding of any base block is call-free. -/
theorem noCalls_embedStmts (ss : List (Imperative.Stmt Expression (Cmd Expression))) :
    Statements.noCalls (embedStmts ss) = true :=
  embedStmts_allSubstmts_isNotCall ss

/-- A Core block that projects successfully is call-free: projection succeeds
    exactly on the call-free fragment. -/
theorem noCalls_of_projectStmts_ok {ss : Statements}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))}
    (h : projectStmts ss = some bs) : Statements.noCalls ss = true := by
  have hemb : embedStmts bs = ss := embedStmts_projectStmts h
  rw [← hemb]; exact noCalls_embedStmts bs

end Core

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

variable (π : String → Option Procedure)

/-- **Output transport.**  Re-establish the full Core `BlockInitEnvWF` on an
    *embedded* base block `embedStmts bs` from the corresponding base
    conditions stated over `bs`.

    The statement-independent fields (evaluator well-formedness, store
    well-definedness, reserved-prefix freshness, factory-declaredness) are passed
    through verbatim; the block-shaped fields (`defsUndefined`,
    `definedVarsNotReserved`, `defUseOk`, `initTypesInhabited`, `fvarTypesOk`, and the
    `readWritesDefined` it subsumes) are discharged by rewriting each Core
    analysis on `embedStmts bs` to the corresponding base analysis on `bs`. -/
theorem BlockInitEnvWF.ofBaseEmbed {params : InitEnvWFParams}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))}
    {ρ : Imperative.Env Expression}
    (hwf : WellFormedSemanticEval (P := Expression) ρ.factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hdefs : ∀ n ∈ Block.definedVars (C := Cmd Expression) bs false, (ρ.store n).isNone)
    (hdnr : ∀ n ∈ Block.definedVars (C := Cmd Expression) bs false, ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hres : ∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
      ¬ p.toList.isPrefixOf n.name.toList)
    (hdu : Block.defUseWellFormed (C := Cmd Expression)
      (fun n => (ρ.store n).isSome) params.declaredFuncs bs = Bool.true)
    (hfd : ∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true)
    (hinit : Block.InitTypesInhabited (P := Expression) (C := Cmd Expression) ρ.factory bs)
    (hty : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧
      Block.fvarTypesWellAnnotated (C := Cmd Expression) Γ bs) :
    BlockInitEnvWF params (embedStmts bs) ρ := by
  refine BlockInitEnvWF.of_defUseOk hwf hsv ?_ ?_ hres ?_ hfd ?_ ?_
  · intro n hn; exact hdefs n (by rwa [Imperative.embedStmts_definedVars] at hn)
  · intro n hn; exact hdnr n (by rwa [Imperative.embedStmts_definedVars] at hn)
  · rw [Imperative.embedStmts_defUseWellFormed (P := Expression)]; exact hdu
  · exact (Imperative.embedStmts_InitTypesInhabited ρ.factory bs).mpr hinit
  · obtain ⟨Γ, hσ, hw⟩ := hty
    exact ⟨Γ, hσ, by rw [Imperative.embedStmts_fvarTypesWellAnnotated]; exact hw⟩

/-- **Input transport (to the generic gate).**  A Core `BlockInitEnvWF` on `ss`
    weakens to the generic `Imperative.Logic.BlockInitEnvWF` on the base block
    `bs` that `ss` projects to, with the same `params`.  This is the bridged
    analogue of `BlockInitEnvWF.toImperative`, exposing the
    generic base-language gate for the projected block. -/
theorem BlockInitEnvWF.toImperativeProject {params : InitEnvWFParams}
    {ss : Statements}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))}
    {ρ : Imperative.Env Expression}
    (h : BlockInitEnvWF params ss ρ) (hp : projectStmts ss = some bs) :
    Imperative.Logic.BlockInitEnvWF (P := Expression)
      (CmdT := Cmd Expression) params bs ρ := by
  have hemb : embedStmts bs = ss := embedStmts_projectStmts hp
  have hdefs : Block.definedVars (C := Command) ss false =
      Block.definedVars (C := Cmd Expression) bs false := by
    rw [← hemb, Imperative.embedStmts_definedVars]
  have htouched : Block.touchedVars (C := Command) ss =
      Block.touchedVars (C := Cmd Expression) bs := by
    rw [← hemb, Imperative.embedStmts_touchedVars]
  refine
    { toWellFormedSemanticEval := h.toWellFormedSemanticEval
      storeWellDefined := h.storeWellDefined
      readWritesDefined := ?_
      defsUndefined := ?_
      definedVarsNotReserved := ?_
      reservedFresh := h.reservedFresh
      defUseOk := ?_
      initTypesInhabited := ?_
      fvarTypesOk := ?_ }
  · intro ident htouchedBase hnotDefinedBase
    exact h.readWritesDefined ident (by rwa [htouched]) (by rwa [hdefs])
  · intro ident hdefinedBase
    exact h.defsUndefined ident (by rwa [hdefs])
  · intro ident hdefinedBase name heq pfx hpfx
    exact h.definedVarsNotReserved ident (by rwa [hdefs]) name heq pfx hpfx
  · have hdu := h.defUseOk
    rw [← hemb,
      Imperative.embedStmts_defUseWellFormed (P := Expression)] at hdu
    exact hdu
  · have hinitTypes := h.initTypesInhabited
    rw [← hemb] at hinitTypes
    exact (Imperative.embedStmts_InitTypesInhabited ρ.factory bs).mp hinitTypes
  · obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
    rw [← hemb, Imperative.embedStmts_fvarTypesWellAnnotated] at hw
    exact ⟨Γ, hσ, hw⟩

/-- Extract every Core initial-environment condition for the projected base
block `bs`. -/
theorem blockInitEnvWF_projectBase {params : InitEnvWFParams} {ss : Statements}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))} {ρ : Imperative.Env Expression}
    (h : BlockInitEnvWF params ss ρ) (hp : projectStmts ss = some bs) :
    WellFormedSemanticEval (P := Expression) ρ.factory
    ∧ Imperative.WellFormedStore ρ.store ρ.factory
    ∧ (∀ n ∈ Block.definedVars (C := Cmd Expression) bs false, (ρ.store n).isNone)
    ∧ (∀ n ∈ Block.definedVars (C := Cmd Expression) bs false, ∀ p ∈ params.prefixIdents,
        ¬ p.toList.isPrefixOf n.name.toList)
    ∧ (∀ n, (ρ.store n).isSome → ∀ p ∈ params.prefixIdents,
        ¬ p.toList.isPrefixOf n.name.toList)
    ∧ Block.defUseWellFormed (C := Cmd Expression)
        (fun n => (ρ.store n).isSome) params.declaredFuncs bs = Bool.true
    ∧ (∀ nm, Core.isNameInFactory nm = Bool.true → params.declaredFuncs ⟨nm, ()⟩ = Bool.true)
    ∧ Block.InitTypesInhabited (P := Expression) (C := Cmd Expression) ρ.factory bs
    ∧ (∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧
        Block.fvarTypesWellAnnotated (C := Cmd Expression) Γ bs) := by
  have hemb : embedStmts bs = ss := embedStmts_projectStmts hp
  refine ⟨h.toWellFormedSemanticEval, h.storeWellDefined, ?_, ?_, h.reservedFreshCore, ?_,
    h.factoryDeclared, ?_, ?_⟩
  · intro n hn
    exact h.defsUndefined n (by rw [← hemb, Imperative.embedStmts_definedVars]; exact hn)
  · intro n hn
    exact h.definedVarsNotReservedCore n
      (by rw [← hemb, Imperative.embedStmts_definedVars]; exact hn)
  · have hdefUse := h.defUseOk
    rw [← hemb, Imperative.embedStmts_defUseWellFormed (P := Expression)] at hdefUse
    exact hdefUse
  · have hinitTypes := h.initTypesInhabited
    rw [← hemb] at hinitTypes
    exact (Imperative.embedStmts_InitTypesInhabited ρ.factory bs).mp hinitTypes
  · obtain ⟨Γ, hσ, hw⟩ := h.fvarTypesOk
    rw [← hemb, Imperative.embedStmts_fvarTypesWellAnnotated] at hw
    exact ⟨Γ, hσ, hw⟩

/-- Projecting a call-free Core block to base statements and re-embedding it
preserves `BlockInitEnvWF`. -/
theorem blockInitEnvWF_project_embed {params : InitEnvWFParams} {ss : Statements}
    {bs : List (Imperative.Stmt Expression (Cmd Expression))} {ρ : Imperative.Env Expression}
    (h : BlockInitEnvWF params ss ρ) (hp : projectStmts ss = some bs) :
    BlockInitEnvWF params (embedStmts bs) ρ := by
  obtain ⟨hwf, hsv, hdefs, hdnr, hres, hdu, hfd, hinit, hty⟩ := blockInitEnvWF_projectBase h hp
  exact BlockInitEnvWF.ofBaseEmbed hwf hsv hdefs hdnr hres hdu hfd hinit hty

end Core.Logic

end -- public section

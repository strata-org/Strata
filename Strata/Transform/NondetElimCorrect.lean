/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.NondetElim
public import Strata.Transform.NondetElimProps
public import Strata.Transform.LoopInitHoist
public import Strata.Transform.Specification
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.Logic.TraceRelations
public import Strata.DL.Imperative.Logic.LangDefProps
import Strata.DL.Imperative.Logic.TraceRelationsProps
import all Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Util.StringGen
import all Strata.Util.Relations
import all Strata.Util.RelationsProps

/-! # Nondeterminism elimination correctness

This module proves the generic event-trace correctness of `Block.nondetElim`.
The Core-specific result in `NondetElimCoreCorrect` builds on it.

Key results:
  * Output shape — `nondetElim_containsNondetLoop`,
    `Block.nondetElim_exitsCoveredByBlocks`, and
    `Block.nondetElim_getBlockLabels` (each with its `Stmt`/`Block.nondetElimM_*`
    pair).
  * Output initializers — `Block.nondetElimM_initVars_classified` and the
    `Stmt`/`Block.nondetElimM_initTypes_classified` pair classify every output
    initializer as a source initializer or a generated Boolean guard;
    `Block.nondetElim_initsUndefinedAndInhabited` transports the initial
    environment's init conditions to the output.
  * Trace simulation — `NondetElim.Internal.overapproximates_upto_base`: every
    finite source trace prefix is matched under
    `Trace.WithWF (EventArg.ExtendsEnv NdExtra)`, where `NdExtra` classifies
    the generated guard registers, because generated
    guard commands are event-silent and source commands replay one-for-one.
    Terminal and exiting environments extend the source only with generated
    guard registers. The proof uses the configuration simulation `NdSim`. -/

public section

namespace Imperative

/-! ## Structural postcondition: the pass output has no nondeterministic control

`Block.noNondetGuards` holds of every output of `Block.nondetElim` (spec guarantee
2): the rewrite replaces each nondeterministic `.ite`/`.loop` guard with a
deterministic read, so no `.ite .nondet`/`.loop .nondet` survives. The generic
mutual `Stmt.nondetElimM_noNondetGuards` / `Block.nondetElimM_noNondetGuards` and
the top-level `nondetElim_noNondetGuards` are proved (over an arbitrary command
type) in `NondetElimProps`; the corollary below specialises them. -/

/-- `nondetElim` removes nondeterministic loops, so its output satisfies
`containsNondetLoop = false` (via the `noNondetGuards` postcondition). -/
theorem nondetElim_containsNondetLoop {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.containsNondetLoop (Block.nondetElim ss) = false :=
  Block.not_containsNondetLoop_of_noNondetGuards _ (nondetElim_noNondetGuards ss)

/-! ### `initVars` classification of the `nondetElim` output

Every init target of the rewritten output is either an original source init
target or a freshly-generated `Q`-guard (the `.ite .nondet`/`.loop .nondet` arms
emit `init $g := *` for a `Q`-kind `g`).  This is the `Q`-generic analogue of the
`NondetElim.isGeneratedName`-keyed `nondetElimM_initVars_classified` below (proved here so the
cons-arm tail premise can be re-established without a forward import). -/

section InitVarsClassified

mutual
private theorem Stmt.nondetElimM_initVars_classified_Q {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.initVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ Q str) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil] at hx ⊢
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified_Q hQgen bss σ x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, List.mem_append] at hx ⊢
      rcases hx with h | h
      · rcases Block.nondetElimM_initVars_classified_Q hQgen tss σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen ess _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [HasInit.init, Block.definedVars, Stmt.definedVars, HasVarsImp.definedVars,
        Cmd.definedVars, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append,
        List.nil_append, List.mem_cons, List.mem_append] at hx ⊢
      rcases hx with h_g | h_t | h_e
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixIte σ).1, h_g, hQgen.1 σ⟩
      · rcases Block.nondetElimM_initVars_classified_Q hQgen tss _ x h_t with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen ess _ x h_e with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.definedVars, Stmt.definedVars, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] at hx ⊢
      exact Block.nondetElimM_initVars_classified_Q hQgen body σ x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [HasInit.init, HasHavoc.havoc, Block.definedVars, Stmt.definedVars,
        HasVarsImp.definedVars, Cmd.definedVars, Bool.false_eq_true, ↓reduceIte,
        Block.initVars_append, List.append_nil, List.cons_append, List.nil_append,
        List.mem_cons] at hx ⊢
      rcases hx with h_g | h_body
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g, hQgen.2 σ⟩
      · rcases Block.nondetElimM_initVars_classified_Q hQgen body _ x h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil,
        List.not_mem_nil] at hx
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.definedVars, Stmt.definedVars, List.append_nil,
        List.not_mem_nil] at hx
  termination_by sizeOf s

private theorem Block.nondetElimM_initVars_classified_Q {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    {Q : String → Prop}
    (hQgen : (∀ sg, Q (StringGenState.gen NondetElim.prefixIte sg).1)
            ∧ (∀ sg, Q (StringGenState.gen NondetElim.prefixLoop sg).1))
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ Q str) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.definedVars, List.not_mem_nil] at hx
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.initVars_append] at hx
      simp only [List.mem_append] at hx
      rw [Block.initVars_cons, List.mem_append]
      rcases hx with h | h
      · rcases Stmt.nondetElimM_initVars_classified_Q hQgen s σ x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initVars_classified_Q hQgen rest _ x h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

end InitVarsClassified

/-! ### Generation-freshness of the `nondetElim` output write-set

Refinement of the `initVars`/`modVars` classification: every variable the
rewritten output writes is either an original source write, or a string the pass
generated *freshly* w.r.t. the input generator state `σ` (`∉ σ.stringGens`).
Threads `WF σ`; each recursive sub-block's freshness (w.r.t. its advanced input
state) is lifted back to freshness w.r.t. `σ` by `GenStep.subset`, and each
freshly generated guard `(gen pf σ).1` is `∉ σ.stringGens` by
`StringGenState.stringGens_gen_not_in`.  Together these show a guard already
generated by `σ` (`g ∈ σ.stringGens`) is never written by a block the pass
produced from `σ` — the frame precondition for guard-value preservation. -/

section WriteVarsFresh

mutual
/-- With a well-formed generator state, every modified variable in a rewritten
statement comes from the source statement or has a name fresh for that state. -/
private theorem Stmt.nondetElimM_modVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.modifiedVars (P := P) (Stmt.nondetElimM s σ).1,
      x ∈ Stmt.modifiedVars s ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
  match s with
  | .cmd c =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, List.append_nil] at hx
      exact Or.inl hx
  | .block lbl bss md =>
      intro x hx
      rw [Stmt.nondetElimM_block_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_fresh bss σ hwf x hx
  | .ite (.det e) tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil, List.mem_append] at hx ⊢
      have hstep : StringGenState.GenStep σ (Block.nondetElimM tss σ).2 := Block.nondetElimM_genStep tss σ
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_fresh tss σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_fresh ess (Block.nondetElimM tss σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  | .ite .nondet tss ess md =>
      intro x hx
      rw [Stmt.nondetElimM_ite_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil, List.mem_append] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixIte σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixIte σ
      have hwf1 : StringGenState.WF
          (StringGenState.gen NondetElim.prefixIte σ).2 :=
        hstep0.wf_mono hwf
      have hstep1 : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
          (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2 :=
        Block.nondetElimM_genStep tss _
      rcases hx with h | h
      · rcases Block.nondetElimM_modVars_fresh tss
          (StringGenState.gen NondetElim.prefixIte σ).2 hwf1 x h with
          h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inl h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
      · rcases Block.nondetElimM_modVars_fresh ess
          (Block.nondetElimM tss
            (StringGenState.gen NondetElim.prefixIte σ).2).2
          (hstep1.wf_mono hwf1) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep1.subset (hstep0.subset hc))⟩
  | .loop (.det e) m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_det_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx ⊢
      exact Block.nondetElimM_modVars_fresh body σ hwf x hx
  | .loop .nondet m inv body md =>
      intro x hx
      rw [Stmt.nondetElimM_loop_nondet_out] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, init_modVars, List.nil_append,
        List.append_nil] at hx ⊢
      rw [Block.modifiedVars_append] at hx
      simp only [Block.modifiedVars, Stmt.modifiedVars, havoc_modVars, List.append_nil,
        List.mem_append, List.mem_singleton] at hx ⊢
      have hstep0 : StringGenState.GenStep σ (StringGenState.gen NondetElim.prefixLoop σ).2 :=
        StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
      rcases hx with h | h_g
      · rcases Block.nondetElimM_modVars_fresh body
          (StringGenState.gen NondetElim.prefixLoop σ).2
          (hstep0.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl h'
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep0.subset hc)⟩
      · exact Or.inr ⟨(StringGenState.gen NondetElim.prefixLoop σ).1, h_g,
          StringGenState.stringGens_gen_not_in NondetElim.prefixLoop σ hwf⟩
  | .exit lbl md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  | .typeDecl t md =>
      intro x hx
      simp only [Stmt.nondetElimM, Block.modifiedVars, Stmt.modifiedVars, List.append_nil] at hx
      exact absurd hx List.not_mem_nil
  termination_by sizeOf s

/-- With a well-formed generator state, every modified variable in a rewritten
block comes from the source block or has a name fresh for that state. -/
private theorem Block.nondetElimM_modVars_fresh {P : PureExpr}
    [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) (hwf : StringGenState.WF σ) :
    ∀ x ∈ Block.modifiedVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.modifiedVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ str ∉ σ.stringGens) := by
  match ss with
  | [] =>
      intro x hx
      simp only [Block.nondetElimM, Block.modifiedVars] at hx
      exact absurd hx List.not_mem_nil
  | s :: rest =>
      intro x hx
      rw [Block.nondetElimM_cons_out, Block.modifiedVars_append] at hx
      simp only [List.mem_append] at hx
      simp only [Block.modifiedVars, List.mem_append]
      have hstep : StringGenState.GenStep σ (Stmt.nondetElimM s σ).2 := Stmt.nondetElimM_genStep s σ
      rcases hx with h | h
      · rcases Stmt.nondetElimM_modVars_fresh s σ hwf x h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_modVars_fresh rest (Stmt.nondetElimM s σ).2 (hstep.wf_mono hwf) x h with h' | ⟨str, heq, hfr⟩
        · exact Or.inl (Or.inr h')
        · exact Or.inr ⟨str, heq, fun hc => hfr (hstep.subset hc)⟩
  termination_by sizeOf ss
end

end WriteVarsFresh

/-! ### The nondetElim label *kind*

`nondetElim` generates labels under exactly two prefixes: `NondetElim.prefixIte` and
`NondetElim.prefixLoop`. `NondetElim.isGeneratedName s` is the precise predicate
"`s` is a name this pass could have generated": it equals a `gen` output for one
of those prefixes. This is the per-kind `Q` to instantiate the kind-generalized
simulation at, replacing the blanket `HasUnderscoreDigitSuffix` (which would
overcommit a composition partner to keeping *every* gen-shaped name fresh). -/

section NondetElimStructural
variable {P : PureExpr}

/-- Every `initVars` element of the `nondetElim` output of a block is either an
original source `initVars` element or a freshly-generated
`NondetElim.isGeneratedName` guard. -/
theorem Block.nondetElimM_initVars_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ x ∈ Block.initVars (P := P) (Block.nondetElimM ss σ).1,
      x ∈ Block.initVars ss ∨
      (∃ str : String, x = HasIdent.ident (P := P) str ∧ NondetElim.isGeneratedName str) :=
  Block.nondetElimM_initVars_classified_Q NondetElim.isGeneratedName_gen ss σ

mutual
/-- Every `initTypes` element of the `nondetElim` output of a statement is either
an original source `initTypes` element or the Boolean type of a freshly-generated
guard havoc. -/
theorem Stmt.nondetElimM_initTypes_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    ∀ ty ∈ Block.initTypes (P := P) (Stmt.nondetElimM s σ).1,
      ty ∈ Stmt.initTypes s ∨ ty = HasBool.boolTy := by
  match s with
  | .cmd c =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Or.inl hty
  | .block lbl bss md =>
      intro ty hty
      rw [Stmt.nondetElimM_block_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Block.nondetElimM_initTypes_classified bss σ ty hty
  | .ite (.det e) tss ess md =>
      intro ty hty
      rw [Stmt.nondetElimM_ite_det_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil, List.mem_append] at hty ⊢
      rcases hty with h | h
      · rcases Block.nondetElimM_initTypes_classified tss σ ty h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified ess _ ty h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .ite .nondet tss ess md =>
      intro ty hty
      rw [Stmt.nondetElimM_ite_nondet_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes, Cmd.initTypes, HasInit.init,
        List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hty ⊢
      rcases hty with h_g | h_t | h_e
      · exact Or.inr h_g
      · rcases Block.nondetElimM_initTypes_classified tss _ ty h_t with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified ess _ ty h_e with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .loop (.det e) m inv body md =>
      intro ty hty
      rw [Stmt.nondetElimM_loop_det_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, List.append_nil] at hty ⊢
      exact Block.nondetElimM_initTypes_classified body σ ty hty
  | .loop .nondet m inv body md =>
      intro ty hty
      rw [Stmt.nondetElimM_loop_nondet_out] at hty
      simp only [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes, Cmd.initTypes, HasInit.init,
        HasHavoc.havoc, Block.initTypes_append, List.append_nil, List.cons_append, List.nil_append, List.mem_cons] at hty ⊢
      rcases hty with h_g | h_body
      · exact Or.inr h_g
      · rcases Block.nondetElimM_initTypes_classified body _ ty h_body with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
  | .exit lbl md =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil,
        List.not_mem_nil] at hty
  | .typeDecl t md =>
      intro ty hty
      simp only [Stmt.nondetElimM, Block.initTypes, Stmt.initTypes, List.append_nil,
        List.not_mem_nil] at hty
  termination_by sizeOf s

/-- Block-level `initTypes` classification of the `nondetElim` output. -/
theorem Block.nondetElimM_initTypes_classified [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    ∀ ty ∈ Block.initTypes (P := P) (Block.nondetElimM ss σ).1,
      ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy := by
  match ss with
  | [] =>
      intro ty hty
      simp only [Block.nondetElimM, Block.initTypes, List.not_mem_nil] at hty
  | s :: rest =>
      intro ty hty
      rw [Block.nondetElimM_cons_out, Block.initTypes_append] at hty
      simp only [List.mem_append] at hty
      rw [Block.initTypes, List.mem_append]
      rcases hty with h | h
      · rcases Stmt.nondetElimM_initTypes_classified s σ ty h with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Block.nondetElimM_initTypes_classified rest _ ty h with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  termination_by sizeOf ss
end

/-- NondetElim preserves initial-variable undefinedness and init-type
inhabitance, accounting for its fresh Boolean guard initializers. -/
theorem Block.nondetElim_initsUndefinedAndInhabited
    {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (ρ : Env P)
    (hdefs : ∀ x ∈ Block.initVars ss, ρ.store x = none)
    (hgens : Env.varsUndefined (P := P) NondetElim.isGeneratedName ρ)
    (hinhab : Block.InitTypesInhabited (P := P) ρ.factory ss) :
    (∀ x ∈ Block.initVars (Block.nondetElim ss), ρ.store x = none)
    ∧ Block.InitTypesInhabited (P := P) ρ.factory (Block.nondetElim ss) := by
  constructor
  · intro x hx
    rcases Block.nondetElimM_initVars_classified ss StringGenState.emp x hx with
      hsource | ⟨name, rfl, hname⟩
    · exact hdefs x hsource
    · exact Env.varsUndefined_apply hgens name hname
  · intro ty hty
    rcases Block.nondetElimM_initTypes_classified ss StringGenState.emp ty hty with
      hsource | rfl
    · exact hinhab ty hsource
    · exact ⟨HasBool.ttVal ρ.factory, (HasBool.boolIsValOfTy ρ.factory).1⟩

section NondetElimCoverage

variable [HasFvar P] [HasBoolOps P] [HasIdent P]

mutual
/-- `Stmt.nondetElimM` preserves exit coverage: the fresh guard `init`/`havoc`
commands it emits are `.cmd`s (trivially covered), and it never introduces or
relabels a `.block`/`.exit`. -/
theorem Stmt.nondetElimM_exitsCoveredByBlocks
    (labels : List String) (s : Stmt P (Cmd P)) (σ : StringGenState)
    (h : Stmt.exitsCoveredByBlocks labels s) :
    Block.exitsCoveredByBlocks labels
      (Stmt.nondetElimM s σ).1 := by
  match s with
  | .cmd c => simp only [Stmt.nondetElimM]; exact coveredBlock_singleton labels (.cmd c) trivial
  | .block lbl bss md =>
    rw [Stmt.nondetElimM_block_out]
    exact coveredBlock_singleton labels (.block lbl _ md)
      (Block.nondetElimM_exitsCoveredByBlocks (lbl :: labels) bss _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .ite (.det e) tss ess md =>
    rw [Stmt.nondetElimM_ite_det_out]
    obtain ⟨ht, he⟩ := h
    exact coveredBlock_singleton labels (.ite (.det e) _ _ md)
      ⟨Block.nondetElimM_exitsCoveredByBlocks labels tss _ ht,
       Block.nondetElimM_exitsCoveredByBlocks labels ess _ he⟩
  | .ite .nondet tss ess md =>
    rw [Stmt.nondetElimM_ite_nondet_out]
    obtain ⟨ht, he⟩ := h
    refine ⟨trivial, ?_, trivial⟩
    exact ⟨Block.nondetElimM_exitsCoveredByBlocks labels tss _ ht,
      Block.nondetElimM_exitsCoveredByBlocks labels ess _ he⟩
  | .loop (.det e) m inv body md =>
    rw [Stmt.nondetElimM_loop_det_out]
    exact coveredBlock_singleton labels (.loop (.det e) m inv _ md)
      (Block.nondetElimM_exitsCoveredByBlocks labels body _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
  | .loop .nondet m inv body md =>
    rw [Stmt.nondetElimM_loop_nondet_out]
    refine ⟨trivial, ?_, trivial⟩
    exact block_exitsCoveredByBlocks_append labels _ _
      (Block.nondetElimM_exitsCoveredByBlocks labels body _
        (by simpa [Stmt.exitsCoveredByBlocks] using h))
      (⟨trivial, trivial⟩ :
        Block.exitsCoveredByBlocks labels
          [Stmt.cmd (HasHavoc.havoc (HasIdent.ident (P := P)
            (StringGenState.gen NondetElim.prefixLoop σ).1) md)])
  | .exit lbl md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.exit lbl md) h
  | .typeDecl t md =>
    simp only [Stmt.nondetElimM]
    exact coveredBlock_singleton labels (.typeDecl t md) trivial
  termination_by sizeOf s

/-- `Block.nondetElimM` preserves exit coverage. -/
theorem Block.nondetElimM_exitsCoveredByBlocks
    (labels : List String) (ss : List (Stmt P (Cmd P))) (σ : StringGenState)
    (h : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels
      (Block.nondetElimM ss σ).1 := by
  match ss with
  | [] => simp only [Block.nondetElimM]; exact trivial
  | s :: rest =>
    rw [Block.nondetElimM_cons_out]
    exact block_exitsCoveredByBlocks_append labels _ _
      (Stmt.nondetElimM_exitsCoveredByBlocks labels s σ h.1)
      (Block.nondetElimM_exitsCoveredByBlocks labels rest _ h.2)
  termination_by sizeOf ss
end

/-- `Block.nondetElim` preserves exit coverage (top-level wrapper). -/
theorem Block.nondetElim_exitsCoveredByBlocks
    (ss : List (Stmt P (Cmd P)))
    (h : Block.exitsCoveredByBlocks [] ss) :
    Block.exitsCoveredByBlocks [] (Block.nondetElim ss) :=
  Block.nondetElimM_exitsCoveredByBlocks [] ss StringGenState.emp h

end NondetElimCoverage

end NondetElimStructural

/-! ## `nondetElim` preserves `getBlockLabels`

Template (from `NondetElimProps`): `Stmt/Block.nondetElimM_loopHasNoInvariants`. The pass keeps every
`.block` label, recurses into sub-bodies, and the only generated statements (the
`init $g := *` havoc and, for nondet loops, the body-tail re-havoc of `$g`) are
`.cmd`s. -/

mutual
/-- `Stmt.nondetElimM` preserves `getBlockLabels` at any threaded state. -/
theorem Stmt.nondetElimM_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    Block.getBlockLabels (Stmt.nondetElimM s σ).1 = Block.getBlockLabels [s] := by
  match s with
  | .cmd c =>
      rw [Stmt.nondetElimM]
  | .block lbl bss md =>
      rw [Stmt.nondetElimM_block_out,
          show ([Stmt.block lbl (Block.nondetElimM bss σ).1 md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl (Block.nondetElimM bss σ).1 md :: [] from rfl,
          Block.getBlockLabels_block_cons,
          show ([Stmt.block lbl bss md] : List (Stmt P (Cmd P)))
            = Stmt.block lbl bss md :: [] from rfl,
          Block.getBlockLabels_block_cons,
          Block.nondetElimM_getBlockLabels bss σ]
  | .ite (.det e) tss ess md =>
      rw [Stmt.nondetElimM_ite_det_out,
          show ([Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                  (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) (Block.nondetElimM tss σ).1
                (Block.nondetElimM ess (Block.nondetElimM tss σ).2).1 md :: [] from rfl,
          Block.getBlockLabels_ite_cons,
          show ([Stmt.ite (.det e) tss ess md] : List (Stmt P (Cmd P)))
            = Stmt.ite (.det e) tss ess md :: [] from rfl,
          Block.getBlockLabels_ite_cons,
          Block.nondetElimM_getBlockLabels tss σ,
          Block.nondetElimM_getBlockLabels ess _]
  | .ite .nondet tss ess md =>
      rw [Stmt.nondetElimM_ite_nondet_out]
      -- The output is `[init $g, ite (.det $g) tss' ess']`; the prelude `init`
      -- is a `.cmd` (label-free), and both branches recurse. Finish by the
      -- structural cons lemmas + the branch IHs.
      simp only [Block.getBlockLabels_cmd_cons,
                 Block.nondetElimM_getBlockLabels tss,
                 Block.nondetElimM_getBlockLabels ess, Block.getBlockLabels_nil,
                 Block.getBlockLabels_ite_cons]
  | .loop (.det e) m inv body md =>
      rw [Stmt.nondetElimM_loop_det_out,
          show ([Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md]
              : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv (Block.nondetElimM body σ).1 md :: [] from rfl,
          Block.getBlockLabels_loop_cons,
          show ([Stmt.loop (.det e) m inv body md] : List (Stmt P (Cmd P)))
            = Stmt.loop (.det e) m inv body md :: [] from rfl,
          Block.getBlockLabels_loop_cons,
          Block.nondetElimM_getBlockLabels body σ]
  | .loop .nondet m inv body md =>
      rw [Stmt.nondetElimM_loop_nondet_out]
      -- The output is `[init $g, loop (body' ++ [havoc $g])]`; the prelude
      -- `init` and the body-tail `havoc` are `.cmd`s (label-free), and the loop
      -- body recurses. Generalise the generated name/state and finish by the
      -- structural cons/append lemmas + the body IH.
      simp only [Block.getBlockLabels_cmd_cons, Block.getBlockLabels_append,
                 Block.nondetElimM_getBlockLabels body, Block.getBlockLabels_nil,
                 Block.getBlockLabels_loop_cons, List.append_nil]
  | .exit lbl md =>
      rw [Stmt.nondetElimM]
  | .typeDecl t md =>
      rw [Stmt.nondetElimM]
  termination_by sizeOf s

/-- `Block.nondetElimM` preserves `getBlockLabels` at any threaded state. -/
theorem Block.nondetElimM_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) (σ : StringGenState) :
    Block.getBlockLabels (Block.nondetElimM ss σ).1 = Block.getBlockLabels ss := by
  match ss with
  | [] => simp [Block.nondetElimM, Block.getBlockLabels]
  | s :: rest =>
      rw [Block.nondetElimM_cons_out, Block.getBlockLabels_append,
          show (s :: rest) = [s] ++ rest from rfl, Block.getBlockLabels_append,
          Stmt.nondetElimM_getBlockLabels s σ,
          Block.nondetElimM_getBlockLabels rest _]
  termination_by sizeOf ss
end

/-- Pure-wrapper corollary: `Block.nondetElim` preserves `getBlockLabels`. -/
theorem Block.nondetElim_getBlockLabels {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (ss : List (Stmt P (Cmd P))) :
    Block.getBlockLabels (Block.nondetElim ss) = Block.getBlockLabels ss := by
  rw [Block.nondetElim, Block.nondetElimM_getBlockLabels]

/-! ## `nondetElim` per-pass event-trace overapproximation instance

The pass's `OverapproximatesTracesUptoWhen` instance uses the event-trace block
language with `EvalCmdE P`. Target-only registers are generated guards;
`Trace.WithWF (EventArg.ExtendsEnv NdExtra)` relates same-kind event snapshots
with environment extension, free-variable store agreement, and evaluator
well-formedness. Its
`toExtendsEnv` theorem recovers the weaker `TraceExtendsEnv` relation.
`Env.ExtendsWith` relates final environments. Nondeterministic loops are
represented by separate preheader, body, and latch states so the source loop
choice selects the corresponding silent target guard update. -/
section NondetElimOverapprox
open Specification Specification.Transform Imperative.Logic

namespace NondetElimTrace

/-! ### Classified registers and leaf invariants -/

/-- Target-only registers introduced by `nondetElim`: the identifiers of the
generated guard names. -/
abbrev NdExtra {P : PureExpr} [HasIdent P] : P.Ident → Prop :=
  IdentOfStringKind (P := P) NondetElim.isGeneratedName

/-- Leaf invariant relating a source environment to its target counterpart at
generator position `σ`: the target extends the source with generated guards
only, the source holds no generated guard, every generated name not yet
produced by `σ` is undefined in the target, and every generated guard bound in
the target holds a Boolean value. -/
structure NdLeaf {P : PureExpr} [HasBool P] [HasIdent P]
    (σ : StringGenState) (ρs ρt : Env P) : Prop where
  ext : Env.ExtendsWith (NdExtra (P := P)) ρs ρt
  srcFresh : ∀ x, NdExtra (P := P) x → ρs.store x = none
  fresh : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σ ρt.store
  typed : ∀ x v, NdExtra (P := P) x → ρt.store x = some v →
    HasVal.valueOfTy ρt.factory v HasBool.boolTy

/-- The trailing target statements of a statement list: none, or the pending
latch havoc of an enclosing rewritten nondeterministic loop. -/
@[expose] def ndTail {P : PureExpr} : Option (P.Ident × MetaData P) → List (Stmt P (Cmd P))
  | none => []
  | some (g, md) => [.cmd (HasHavoc.havoc g md)]

/-- The latch guard of the trailing tail (if any) is defined in a store. -/
@[expose] def NdTailDef {P : PureExpr} (tail : Option (P.Ident × MetaData P))
    (σ : SemanticStore P) : Prop :=
  ∀ g md, tail = some (g, md) → (σ g).isSome = true

/-- The latch guard of the trailing tail (if any) is defined throughout a
configuration (operative store and every enclosing parent store). -/
@[expose] def NdTailCfg {P : PureExpr} (tail : Option (P.Ident × MetaData P))
    (c : Config P (Cmd P)) : Prop :=
  ∀ g md, tail = some (g, md) → Config.varsDefined (· = g) c

/-- Guard generated for a nondeterministic `ite` at generator state `σ`. -/
abbrev ndIteGuard {P : PureExpr} [HasIdent P] (σ : StringGenState) : P.Ident :=
  HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixIte σ).1

/-- Guard generated for a nondeterministic loop at generator state `σ`. -/
abbrev ndLoopGuard {P : PureExpr} [HasIdent P] (σ : StringGenState) : P.Ident :=
  HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixLoop σ).1

/-- The rewritten deterministic `ite` emitted for a nondeterministic `ite`. -/
abbrev ndIteTgt {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (tss ess : List (Stmt P (Cmd P))) (md : MetaData P) (σ : StringGenState) :
    Stmt P (Cmd P) :=
  .ite (.det (HasFvar.mkTypedFvar (ndIteGuard (P := P) σ) HasBool.boolTy))
    (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).1
    (Block.nondetElimM ess
      (Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2).2).1 md

/-- The rewritten deterministic loop emitted for a nondeterministic loop: its
body is the rewritten source body followed by the latch havoc. -/
abbrev ndLoopTgt {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (m : Option P.Expr) (inv : List (String × P.Expr)) (body : List (Stmt P (Cmd P)))
    (md : MetaData P) (σ : StringGenState) : Stmt P (Cmd P) :=
  .loop (.det (HasFvar.mkTypedFvar (ndLoopGuard (P := P) σ) HasBool.boolTy)) m inv
    ((Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).1 ++
      [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)]) md

/-- Shared invariant of the nondeterministic-loop head states: the source has
finished one body iteration (and possibly left its scope), while the target
sits before its latch havoc inside the iteration scope. -/
structure NdHeadInv {P : PureExpr} [HasFvars P] [HasBool P] [HasIdent P]
    (σ σb : StringGenState) (body : List (Stmt P (Cmd P)))
    (σps σpt : SemanticStore P) (ρsb ρtb : Env P) : Prop where
  wf : StringGenState.WF (StringGenState.gen NondetElim.prefixLoop σ).2
  noGen : SrcNoGenWrites (P := P) NondetElim.isGeneratedName body
  noRead : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName body
  parent : StoreExtendsWith (NdExtra (P := P)) σps σpt
  parentFresh : SemanticStore.isReserved (P := P)
    NondetElim.isGeneratedName
    (StringGenState.gen NondetElim.prefixLoop σ).2 σpt
  parentGuard : (σpt (ndLoopGuard (P := P) σ)).isSome = true
  leaf : NdLeaf σb ρsb ρtb
  guard : (ρtb.store (ndLoopGuard (P := P) σ)).isSome = true

/-! ### Generator-indexed configuration simulation

`NdSim tail σe cs ct` relates an in-flight source configuration `cs` to a
target configuration `ct` of the rewritten program.  `σe` is the generator
state reached once the source configuration's pending code has been
rewritten; the continuation of an enclosing sequence was generated from it.
`tail` records whether the enclosing statement list is the body of a rewritten
nondeterministic loop, whose target list carries the trailing latch havoc. -/
inductive NdSim {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P] :
    Option (P.Ident × MetaData P) → StringGenState →
    Config P (Cmd P) → Config P (Cmd P) → Prop where
  /-- A source statement list and its rewrite (plus the tail). -/
  | stmts {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM ss σ).2 (.stmts ss ρs)
        (.stmts ((Block.nondetElimM ss σ).1 ++ ndTail tail) ρt)
  /-- A source statement whose rewrite is a single statement. -/
  | stmt {σ : StringGenState} {s s' : Stmt P (Cmd P)} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [s] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [s] →
      (Stmt.nondetElimM s σ).1 = [s'] →
      NdSim none (Stmt.nondetElimM s σ).2 (.stmt s ρs) (.stmt s' ρt)
  /-- Terminated configurations. -/
  | terminal {σe : StringGenState} {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → NdSim none σe (.terminal ρs) (.terminal ρt)
  /-- A finished loop body: the target still has to run the latch havoc. -/
  | pendingHavoc {σe : StringGenState} {g : P.Ident} {md : MetaData P} {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → (ρt.store g).isSome = true →
      NdSim (some (g, md)) σe (.terminal ρs) (.stmts [.cmd (HasHavoc.havoc g md)] ρt)
  /-- Exiting configurations. -/
  | exiting {tail : Option (P.Ident × MetaData P)} {σe : StringGenState} {l : String}
      {ρs ρt : Env P} :
      NdLeaf σe ρs ρt → NdSim tail σe (.exiting l ρs) (.exiting l ρt)
  /-- A sequence frame whose continuation was rewritten from `σr`. -/
  | seq {tail : Option (P.Ident × MetaData P)} {σr : StringGenState}
      {inner inner' : Config P (Cmd P)} {rest : List (Stmt P (Cmd P))} :
      NdSim none σr inner inner' → StringGenState.WF σr →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailCfg tail inner' →
      NdSim tail (Block.nondetElimM rest σr).2 (.seq inner rest)
        (.seq inner' ((Block.nondetElimM rest σr).1 ++ ndTail tail))
  /-- A block frame; projection through the parents restores freshness at `σe`. -/
  | block {σi σe : StringGenState} {l : Option String} {σps σpt : SemanticStore P}
      {inner inner' : Config P (Cmd P)} :
      NdSim none σi inner inner' → StoreExtendsWith (NdExtra (P := P)) σps σpt →
      SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt →
      NdSim none σe (.block l σps inner) (.block l σpt inner')
  /-- Preheader of a nondeterministic `ite`: the target has not yet chosen its
  guard; the source's branch choice will drive the guard's initial value. -/
  | seqIte {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
      {rest : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.ite .nondet tss ess md] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
        [.ite .nondet tss ess md] →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).2
        (.seq (.stmt (.ite .nondet tss ess md) ρs) rest)
        (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndIteTgt tss ess md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
              ndTail tail)))
  /-- Preheader of a nondeterministic loop: the source's first enter/exit choice
  will drive the guard's initial value. -/
  | seqLoop {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
      {m : Option P.Expr} {inv : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
      {md : MetaData P} {rest : List (Stmt P (Cmd P))} {ρs ρt : Env P} :
      StringGenState.WF σ → NdLeaf σ ρs ρt →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.loop .nondet m inv body md] →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
        [.loop .nondet m inv body md] →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest →
      NdTailDef tail ρt.store →
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).2
        (.seq (.stmt (.loop .nondet m inv body md) ρs) rest)
        (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndLoopTgt m inv body md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
              ndTail tail)))
  /-- One running iteration of a nondeterministic loop: the body runs under the
  latch-havoc tail. -/
  | iter {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {cs ct : Config P (Cmd P)} :
      StringGenState.WF (StringGenState.gen NondetElim.prefixLoop σ).2 →
      SrcNoGenWrites (P := P) NondetElim.isGeneratedName body →
      Block.exprsShapeFree (P := P) NondetElim.isGeneratedName body →
      StoreExtendsWith (NdExtra (P := P)) σps σpt →
      SemanticStore.isReserved (P := P) NondetElim.isGeneratedName
        (StringGenState.gen NondetElim.prefixLoop σ).2 σpt →
      (σpt (ndLoopGuard (P := P) σ)).isSome = true →
      NdSim (some (ndLoopGuard (P := P) σ, md)) σb cs ct →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.block none σps cs) [.loop .nondet m inv body md])
        (.seq (.block none σpt ct) [ndLoopTgt m inv body md σ])
  /-- Loop head, source left the iteration scope. -/
  | headTerm {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.terminal { ρsb with store := projectStore σps ρsb.store })
          [.loop .nondet m inv body md])
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- Loop head, source resumed its loop continuation. -/
  | headStmts {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.stmts [.loop .nondet m inv body md] { ρsb with store := projectStore σps ρsb.store })
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- Loop head, source about to choose enter/exit. -/
  | headStmt {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
      {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
      {ρsb ρtb : Env P} :
      NdHeadInv σ σb body σps σpt ρsb ρtb →
      NdSim none (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2
        (.seq (.stmt (.loop .nondet m inv body md)
          { ρsb with store := projectStore σps ρsb.store }) [])
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ])
  /-- An exit escaping a loop iteration scope, before the sequence propagates it. -/
  | seqExit {σe : StringGenState} {l : String} {ρs ρt : Env P}
      {ss ss' : List (Stmt P (Cmd P))} :
      NdLeaf σe ρs ρt → NdSim none σe (.seq (.exiting l ρs) ss) (.seq (.exiting l ρt) ss')

/-! ### Source write-set decomposition -/

/-- The empty source block has an empty write set, so it vacuously writes no
name of kind `Q`. -/
private theorem noGen_nil {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop} :
    SrcNoGenWrites (P := P) Q [] := by
  intro s _ hmem
  simp [Block.definedVars, Block.modifiedVars] at hmem

/-- If a cons block writes no name of kind `Q`, neither does its head statement
taken on its own. -/
private theorem noGen_head {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : SrcNoGenWrites (P := P) Q (s :: ss)) : SrcNoGenWrites (P := P) Q [s] := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inl h)
  · exact .inr (.inl h)

/-- If a cons block writes no name of kind `Q`, neither does its tail. -/
private theorem noGen_tail {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {s : Stmt P (Cmd P)} {ss : List (Stmt P (Cmd P))}
    (h : SrcNoGenWrites (P := P) Q (s :: ss)) : SrcNoGenWrites (P := P) Q ss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inr h)
  · exact .inr (.inr h)

/-- If a singleton `.block` statement writes no name of kind `Q`, neither does
its inner body. -/
private theorem noGen_block {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {l : String} {bss : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.block l bss md]) : SrcNoGenWrites (P := P) Q bss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  exact hmem

/-- If a singleton `.ite` statement writes no name of kind `Q`, neither does its
then branch. -/
private theorem noGen_ite_then {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {c : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.ite c tss ess md]) : SrcNoGenWrites (P := P) Q tss := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inl h)
  · exact .inr (.inl h)

/-- If a singleton `.ite` statement writes no name of kind `Q`, neither does its
else branch. -/
private theorem noGen_ite_else {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {c : ExprOrNondet P} {tss ess : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.ite c tss ess md]) : SrcNoGenWrites (P := P) Q ess := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact .inl (.inr h)
  · exact .inr (.inr h)

/-- If a singleton `.loop` statement writes no name of kind `Q`, neither does its
body. -/
private theorem noGen_loop {P : PureExpr} [HasFvars P] [HasIdent P] {Q : String → Prop}
    {g : ExprOrNondet P} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P}
    (h : SrcNoGenWrites (P := P) Q [.loop g m inv body md]) : SrcNoGenWrites (P := P) Q body := by
  intro name hq hmem
  apply h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hmem ⊢
  exact hmem

/-- If a singleton command writes no name of kind `Q`, then no identifier of kind
`Q` lies among the command's defined or modified variables. -/
private theorem noGen_cmd {P : PureExpr} [HasFvars P] [HasIdent P]
    {Q : String → Prop} {c : Cmd P}
    (h : SrcNoGenWrites (P := P) Q [.cmd c]) {x : P.Ident}
    (hx : IdentOfStringKind (P := P) Q x) :
    x ∉ Cmd.definedVars c ∧ x ∉ Cmd.modifiedVars c := by
  obtain ⟨name, hq, rfl⟩ := hx
  have h' := h name hq
  simp only [Block.definedVars, Block.modifiedVars, Stmt.definedVars, Stmt.modifiedVars,
    HasVarsImp.definedVars, HasVarsImp.modifiedVars, List.append_nil, List.mem_append,
    not_or] at h'
  exact h'

/-- Canonical events emitted by replaying a read-fresh command carry the
NondetElim argument relation. -/
private theorem cmd_emitted_neTraceRel {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBool P] [HasVal P] [HasIdent P]
    {c : Cmd P} {fs ft : P.Factory} {σs σt : SemanticStore P}
    (hread : ∀ name, NondetElim.isGeneratedName name →
      HasIdent.ident (P := P) name ∉ Cmd.getVars c)
    (hfactory : fs = ft)
    (hext : StoreExtendsWith (NdExtra (P := P)) σs σt)
    (hsourceWF : WellFormedStore σs fs) (htargetWF : WellFormedStore σt ft)
    (hcongr : WellFormedSemanticEvalExprCongr fs) :
    Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra)
      (Cmd.emittedEvents P c fs σs) (Cmd.emittedEvents P c ft σt) := by
  have hfv : ∀ x ∈ Cmd.getVars c, σs x = σt x := by
    intro x hx
    apply hext.lookup_eq_of_not_extra
    rintro ⟨name, hname, rfl⟩
    exact hread name hname hx
  cases c with
  | init | set => exact .nil
  | assert label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil
  | assume label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil
  | cover label expr metadata =>
      exact .cons
        ⟨⟨hfactory, hext, rfl, rfl, rfl⟩,
          (fun x hx => hfv x (by simpa [Cmd.getVars] using hx)),
          hsourceWF, htargetWF, hcongr⟩ .nil

/-! ### Event command frame facts -/

/-- A command leaves a register's value unchanged when the register is neither
defined nor modified by the command. -/
private theorem evalCmdE_eq_of_not_written {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {y : P.Ident}
    (h : EvalCmdE P f σ c σ' emitted)
    (hd : y ∉ Cmd.definedVars c) (hm : y ∉ Cmd.modifiedVars c) : σ' y = σ y := by
  cases h with
  | eval_init _ hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hd (by simp [Cmd.definedVars]))
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hd (by simp [Cmd.definedVars]))
  | eval_set _ hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hm (by simp [Cmd.modifiedVars]))
  | eval_set_nondet hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact hm (by simp [Cmd.modifiedVars]))
  | eval_assert => rfl
  | eval_assume => rfl
  | eval_cover => rfl

/-- A register that the command defines (via `init`) must have been undefined in
the pre-state. -/
private theorem evalCmdE_defined_none {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {x : P.Ident}
    (h : EvalCmdE P f σ c σ' emitted) (hx : x ∈ Cmd.definedVars c) : σ x = none := by
  cases h with
  | eval_init _ hinit _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at hx
    subst hx
    cases hinit with
    | init hnone _ _ => exact hnone
  | eval_init_unconstrained hinit _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at hx
    subst hx
    cases hinit with
    | init hnone _ _ => exact hnone
  | eval_set => simp [Cmd.definedVars] at hx
  | eval_set_nondet => simp [Cmd.definedVars] at hx
  | eval_assert => simp [Cmd.definedVars] at hx
  | eval_assume => simp [Cmd.definedVars] at hx
  | eval_cover => simp [Cmd.definedVars] at hx

/-! ### Leaf-invariant transport -/

/-- The leaf invariant is preserved when the generator state advances by one
generation step; only the freshness component weakens. -/
private theorem NdLeaf.mono {P : PureExpr} [HasBool P] [HasIdent P]
    {σ σ' : StringGenState} {ρs ρt : Env P}
    (hstep : StringGenState.GenStep σ σ') (h : NdLeaf σ ρs ρt) : NdLeaf σ' ρs ρt :=
  { h with fresh := SemanticStore.isReserved.mono hstep h.fresh }

/-- Replaying a user command keeps the leaf invariant and relates the emitted
snapshots. -/
private theorem NdLeaf.cmd_step {P : PureExpr} [HasFvar P] [HasFvars P]
    [HasBoolOps P] [HasVal P] [HasIdent P] [DecidableEq P.Ident]
    {σ : StringGenState} {ρs ρt : Env P} {c : Cmd P} {σs' : SemanticStore P}
    {e : Trace P}
    (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.cmd c])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [.cmd c])
    (hsourceWF : WellFormedStore ρs.store ρs.factory)
    (htargetWF : WellFormedStore ρt.store ρt.factory)
    (hcongr : WellFormedSemanticEvalExprCongr ρs.factory)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (heval : EvalCmdE P ρs.factory ρs.store c σs' e) :
    ∃ σt', EvalCmdE P ρt.factory ρt.store c σt'
        (Cmd.emittedEvents P c ρt.factory ρt.store) ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e
        (Cmd.emittedEvents P c ρt.factory ρt.store) ∧
      NdLeaf σ { ρs with store := σs' } { ρt with store := σt' } := by
  obtain ⟨hfac, hstore⟩ := hl.ext
  have htrace : Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e
      (Cmd.emittedEvents P c ρt.factory ρt.store) := by
    rw [heval.emitted_eq]
    exact cmd_emitted_neTraceRel
      (Stmt.exprsShapeFree_cmd.mp (Block.exprsShapeFree_singleton.mp hread))
      hfac hstore hsourceWF htargetWF hcongr
  have hinit : ∀ x ∈ Cmd.definedVars c, ρt.store x = none := by
    intro x hx
    have hsrc : ρs.store x = none := evalCmdE_defined_none heval hx
    cases hxt : ρt.store x with
    | none => rfl
    | some w =>
      exfalso
      rcases hstore.2 x (by simp [hxt]) with hs | hextra
      · simp [hsrc] at hs
      · exact (noGen_cmd hng hextra).1 hx
  obtain ⟨σt', hevt, hext', _⟩ :=
    evalCmdE_replay_extends (NdExtra (P := P)) ρs.factory ρs.store ρt.store σs' c e
      hstore heval hmono hinit
  rw [hfac] at hevt
  refine ⟨σt', hevt, htrace, ⟨⟨hfac, hext'⟩, ?_, ?_, ?_⟩⟩
  · intro x hx
    show σs' x = none
    rw [evalCmdE_eq_of_not_written heval (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
    exact hl.srcFresh x hx
  · intro s hs hnin
    have hx : NdExtra (P := P) (HasIdent.ident s) := ⟨s, hs, rfl⟩
    show σt' (HasIdent.ident s) = none
    rw [evalCmdE_eq_of_not_written hevt (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
    exact hl.fresh s hs hnin
  · intro x v hx hv
    have hv' : ρt.store x = some v := by
      rw [← evalCmdE_eq_of_not_written hevt (noGen_cmd hng hx).1 (noGen_cmd hng hx).2]
      exact hv
    exact hl.typed x v hx hv'

/-- Leaving a block scope projects both sides through related parent stores. -/
private theorem ndLeaf_project {P : PureExpr} [HasBool P] [HasIdent P]
    {σe : StringGenState} {ρs ρt : Env P} {σps σpt : SemanticStore P}
    (hext : Env.ExtendsWith (NdExtra (P := P)) ρs ρt)
    (hsrc : ∀ x, NdExtra (P := P) x → ρs.store x = none)
    (htyped : ∀ x v, NdExtra (P := P) x → ρt.store x = some v →
      HasVal.valueOfTy ρt.factory v HasBool.boolTy)
    (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρs with store := projectStore σps ρs.store }
      { ρt with store := projectStore σpt ρt.store } := by
  refine ⟨⟨hext.1, StoreExtendsWith.projectStore hp hext.2⟩, ?_, ?_, ?_⟩
  · intro x hx
    show projectStore σps ρs.store x = none
    simp only [projectStore, hsrc x hx]
    split <;> rfl
  · intro s hs hnin
    show projectStore σpt ρt.store (HasIdent.ident s) = none
    simp only [projectStore, hf s hs hnin]
    simp
  · intro x v hx hv
    change projectStore σpt ρt.store x = some v at hv
    simp only [projectStore] at hv
    split at hv
    · exact htyped x v hx hv
    · simp at hv

/-- Leaving a block scope preserves the leaf invariant: it projects the source
and target stores through related parent stores, with the exit generator state
fresh for the projected target store. -/
private theorem NdLeaf.project {P : PureExpr} [HasBool P] [HasIdent P]
    {σi σe : StringGenState} {ρs ρt : Env P} {σps σpt : SemanticStore P}
    (hl : NdLeaf σi ρs ρt) (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρs with store := projectStore σps ρs.store }
      { ρt with store := projectStore σpt ρt.store } :=
  ndLeaf_project hl.ext hl.srcFresh hl.typed hp hf

/-- Initializing a freshly generated guard with a Boolean value. -/
private theorem NdLeaf.init_guard {P : PureExpr} [HasBool P] [HasIdent P] [DecidableEq P.Ident]
    [LawfulHasIdent P]
    {σ : StringGenState} {ρs ρt : Env P} {pf : String}
    (hwf : StringGenState.WF σ) (hQ : NondetElim.isGeneratedName (StringGenState.gen pf σ).1)
    (hl : NdLeaf σ ρs ρt) {v : P.Val} (hv : HasVal.valueOfTy ρt.factory v HasBool.boolTy) :
    ρt.store (HasIdent.ident (StringGenState.gen pf σ).1) = none ∧
    NdLeaf (StringGenState.gen pf σ).2 ρs
      { ρt with
        store := SemanticStore.update ρt.store
          (HasIdent.ident (StringGenState.gen pf σ).1) v } := by
  have hg : NdExtra (P := P) (HasIdent.ident (StringGenState.gen pf σ).1) := ⟨_, hQ, rfl⟩
  have hnone := SemanticStore.isReserved.gen_slot_none pf hl.fresh hwf hQ
  refine ⟨hnone, ⟨⟨hl.ext.1,
    StoreExtendsWith.update_target hl.ext.2 (hl.srcFresh _ hg) hg⟩,
    hl.srcFresh, SemanticStore.isReserved.storeWith_gen pf v hl.fresh, ?_⟩⟩
  intro x w hx hw
  change SemanticStore.update ρt.store _ v x = some w at hw
  by_cases hxg : x = HasIdent.ident (StringGenState.gen pf σ).1
  · subst hxg
    simp only [SemanticStore.update, ↓reduceIte, Option.some.injEq] at hw
    subst hw
    exact hv
  · simp only [SemanticStore.update, ite_eq_right hxg] at hw
    exact hl.typed x w hx hw

/-- Re-havocking a defined guard at the latch and leaving the iteration scope. -/
private theorem NdLeaf.latch {P : PureExpr} [HasBool P] [HasIdent P] [DecidableEq P.Ident]
    {σb σe : StringGenState} {ρsb ρtb : Env P} {σps σpt : SemanticStore P}
    {g : P.Ident} {v : P.Val}
    (hl : NdLeaf σb ρsb ρtb) (hg : NdExtra (P := P) g)
    (hv : HasVal.valueOfTy ρtb.factory v HasBool.boolTy)
    (hp : StoreExtendsWith (NdExtra (P := P)) σps σpt)
    (hf : SemanticStore.isReserved (P := P) NondetElim.isGeneratedName σe σpt) :
    NdLeaf σe { ρsb with store := projectStore σps ρsb.store }
      { ρtb with store := projectStore σpt (SemanticStore.update ρtb.store g v) } := by
  have htyped : ∀ x w, NdExtra (P := P) x → SemanticStore.update ρtb.store g v x = some w →
      HasVal.valueOfTy ρtb.factory w HasBool.boolTy := by
    intro x w hx hw
    by_cases hxg : x = g
    · subst hxg
      simp only [SemanticStore.update, ↓reduceIte, Option.some.injEq] at hw
      subst hw
      exact hv
    · simp only [SemanticStore.update, ite_eq_right hxg] at hw
      exact hl.typed x w hx hw
  exact ndLeaf_project (ρt := { ρtb with store := SemanticStore.update ρtb.store g v })
    ⟨hl.ext.1, StoreExtendsWith.update_target hl.ext.2 (hl.srcFresh g hg) hg⟩
    hl.srcFresh htyped hp hf

/-! ### Guard evaluation -/

/-- Reading a guard register immediately after writing it returns the written
boolean value. -/
private theorem eval_guard_update {P : PureExpr} [HasBool P] [HasFvar P]
    [HasFvars P] [DecidableEq P.Ident]
    [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {f : P.Factory} {σ : SemanticStore P} {g : P.Ident} {v : P.Val}
    (hv : HasVal.valueOfTy f v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar f) (hmono : WellFormedSemanticEvalMono f) :
    P.eval f (SemanticStore.update σ g v) (HasFvar.mkTypedFvar g HasBool.boolTy) = some v :=
  eval_mkTypedFvar_storeWith f σ g v (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hvar hmono

/-- Reading a guard register after a latch havoc and a block-store projection
returns the written boolean value, provided the parent store keeps the guard
defined. -/
private theorem eval_guard_latch {P : PureExpr} [HasBool P] [HasFvar P] [DecidableEq P.Ident]
    [HasOps P] [LawfulHasFvar P] [HasFvars P] [LawfulHasVal P]
    {f : P.Factory} {σpt σ : SemanticStore P} {g : P.Ident} {v : P.Val}
    (hpg : (σpt g).isSome = true)
    (hv : HasVal.valueOfTy f v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar f) (hmono : WellFormedSemanticEvalMono f) :
    P.eval f (projectStore σpt (SemanticStore.update σ g v))
      (HasFvar.mkTypedFvar g HasBool.boolTy) = some v :=
  eval_mkTypedFvar_of_value f _ g v (LawfulHasVal.valueOfTy_isVal _ _ _ hv)
    (by simp [projectStore, hpg, SemanticStore.update]) hvar hmono

/-! ### Target run builders -/

/-- Prepend a silent (empty-trace) event step to a target run, leaving the run's
trace unchanged. -/
private theorem starE_cons_nil {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {c c' c'' : Config P (Cmd P)} {tr : Trace P}
    (h : StepStmtE P (EvalCmdE P) c [] c') (hr : StepStmtStarE P (EvalCmdE P) c' tr c'') :
    StepStmtStarE P (EvalCmdE P) c tr c'' :=
  .step _ [] _ tr _ h hr

/-- Initialize a guard and enter the statement it guards. -/
private theorem tgt_init_then {P : PureExpr} [HasFvar P] [HasBoolOps P] [DecidableEq P.Ident]
    {g : P.Ident} {md : MetaData P} {X : Stmt P (Cmd P)} {R : List (Stmt P (Cmd P))}
    {ρt : Env P} {v : P.Val}
    (hnone : ρt.store g = none) (hv : HasVal.valueOfTy ρt.factory v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar ρt.factory) :
    StepStmtStarE P (EvalCmdE P)
      (.seq (.stmt (.cmd (HasInit.init g HasBool.boolTy .nondet md)) ρt) (X :: R)) []
      (.seq (.stmt X { ρt with store := SemanticStore.update ρt.store g v }) R) := by
  have hinit : InitState P ρt.store g v (SemanticStore.update ρt.store g v) :=
    InitState.init hnone (by simp [SemanticStore.update])
      (by intro y hy; simp [SemanticStore.update, Ne.symm hy])
  have hcmd : EvalCmdE P ρt.factory ρt.store (HasInit.init g HasBool.boolTy .nondet md)
      (SemanticStore.update ρt.store g v) [] :=
    EvalCmdE.eval_init_unconstrained hinit hv hvar
  refine starE_cons_nil (.step_seq_inner (.step_cmd hcmd)) ?_
  refine starE_cons_nil .step_seq_done ?_
  exact starE_cons_nil .step_stmts_cons (.refl _)

/-- Run the pending latch havoc, leave the iteration scope, and resume the loop. -/
private theorem tgt_latch {P : PureExpr} [HasFvar P] [HasBoolOps P] [DecidableEq P.Ident]
    {g : P.Ident} {md : MetaData P} {σpt : SemanticStore P} {ρtb : Env P}
    {L' : Stmt P (Cmd P)} {prev v : P.Val}
    (hprev : ρtb.store g = some prev)
    (hprevTy : HasVal.valueOfTy ρtb.factory prev HasBool.boolTy)
    (hv : HasVal.valueOfTy ρtb.factory v HasBool.boolTy)
    (hvar : WellFormedSemanticEvalVar ρtb.factory) :
    StepStmtStarE P (EvalCmdE P)
      (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc g md)] ρtb)) [L']) []
      (.seq (.stmt L'
        { ρtb with store := projectStore σpt (SemanticStore.update ρtb.store g v) }) []) := by
  have hupd : UpdateState P ρtb.store g v (SemanticStore.update ρtb.store g v) :=
    UpdateState.update hprev (by simp [SemanticStore.update])
      (by intro y hy; simp [SemanticStore.update, Ne.symm hy])
  have hcmd : EvalCmdE P ρtb.factory ρtb.store (HasHavoc.havoc g md)
      (SemanticStore.update ρtb.store g v) [] :=
    EvalCmdE.eval_set_nondet hupd ⟨prev, HasBool.boolTy, hprev, hprevTy, hv⟩ hvar
  refine starE_cons_nil (.step_seq_inner (.step_block_body .step_stmts_cons)) ?_
  refine starE_cons_nil
    (.step_seq_inner (.step_block_body (.step_seq_inner (.step_cmd hcmd)))) ?_
  refine starE_cons_nil (.step_seq_inner (.step_block_body .step_seq_done)) ?_
  refine starE_cons_nil (.step_seq_inner (.step_block_body .step_stmts_nil)) ?_
  refine starE_cons_nil (.step_seq_inner .step_block_done) ?_
  refine starE_cons_nil .step_seq_done ?_
  exact starE_cons_nil .step_stmts_cons (.refl _)

/-! ### Source step inversion -/

/-- Case analysis on one event step of a `.seq` configuration: either the inner
configuration steps, or it was terminal (and the sequence advances to its
continuation), or it was exiting (and the exit propagates). -/
private theorem stepE_seq_cases {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {e : Trace P}
    {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.seq inner ss) e c') :
    (∃ inner', StepStmtE P (EvalCmdE P) inner e inner' ∧ c' = .seq inner' ss) ∨
    (∃ ρ, inner = .terminal ρ ∧ e = [] ∧ c' = .stmts ss ρ) ∨
    (∃ l ρ, inner = .exiting l ρ ∧ e = [] ∧ c' = .exiting l ρ) := by
  cases h with
  | step_seq_inner h => exact .inl ⟨_, h, rfl⟩
  | step_seq_done => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  | step_seq_exit => exact .inr (.inr ⟨_, _, rfl, rfl, rfl⟩)

/-- A `.stmts` configuration steps silently (empty trace), either to a terminal
when the list is empty or to a `.seq` of its head statement with the remaining
list. -/
private theorem stepE_stmts_cases {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {ss : List (Stmt P (Cmd P))} {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.stmts ss ρ) e c') :
    e = [] ∧ ((ss = [] ∧ c' = .terminal ρ) ∨
      (∃ s rest, ss = s :: rest ∧ c' = .seq (.stmt s ρ) rest)) := by
  cases h with
  | step_stmts_nil => exact ⟨rfl, .inl ⟨rfl, rfl⟩⟩
  | step_stmts_cons => exact ⟨rfl, .inr ⟨_, _, rfl, rfl⟩⟩

/-- A terminal configuration takes no event step. -/
private theorem stepE_terminal_false {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (h : StepStmtE P (EvalCmdE P) (.terminal ρ) e c') : False := by
  cases h

/-- A non-command statement configuration steps silently by an administrative
control-flow step. -/
private theorem stepE_stmt_admin {P : PureExpr} [HasFvar P] [HasBoolOps P]
    {s : Stmt P (Cmd P)} {ρ : Env P} {e : Trace P} {c' : Config P (Cmd P)}
    (hs : ∀ c, s ≠ .cmd c)
    (h : StepStmtE P (EvalCmdE P) (.stmt s ρ) e c') :
    e = [] ∧ StepStmtE P (EvalCmdE P) (.stmt s ρ) [] c' := by
  have h' := h
  cases h with
  | step_cmd _ => exact absurd rfl (hs _)
  | _ => exact ⟨rfl, h'⟩

/-! ### Rewrite shapes -/

/-- Normal form: the pass maps the empty block to the empty block and leaves the
generator state unchanged. -/
private theorem nondetElimM_nil {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (σ : StringGenState) :
    Block.nondetElimM (P := P) (CmdT := Cmd P) [] σ = ([], σ) := by
  simp [Block.nondetElimM]

/-- Normal form: a singleton block rewrites to the same output statements as its
single statement. -/
private theorem nondetElimM_singleton_out {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Block.nondetElimM [s] σ).1 = (Stmt.nondetElimM s σ).1 := by
  rw [Block.nondetElimM_cons_out, nondetElimM_nil, List.append_nil]

/-- Normal form: a singleton block advances the generator state exactly as its
single statement does. -/
private theorem nondetElimM_singleton_state {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P]
    [HasBool P] (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (Block.nondetElimM [s] σ).2 = (Stmt.nondetElimM s σ).2 := by
  rw [Block.nondetElimM_cons_state, nondetElimM_nil]

/-- Normal form: the pass leaves a command statement and the generator state
unchanged. -/
private theorem nondetElimM_cmd {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (c : Cmd P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (.cmd c) σ = ([.cmd c], σ) := by
  simp [Stmt.nondetElimM]

/-- Normal form: the pass leaves an `.exit` statement and the generator state
unchanged. -/
private theorem nondetElimM_exit {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (l : String) (md : MetaData P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (CmdT := Cmd P) (.exit l md) σ = ([.exit l md], σ) := by
  simp [Stmt.nondetElimM]

/-- Normal form: the pass leaves a `.typeDecl` statement and the generator state
unchanged. -/
private theorem nondetElimM_typeDecl {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (t : TypeConstructor) (md : MetaData P) (σ : StringGenState) :
    Stmt.nondetElimM (P := P) (CmdT := Cmd P) (.typeDecl t md) σ = ([.typeDecl t md], σ) := by
  simp [Stmt.nondetElimM]

/-- Every statement rewrites to a single statement, except nondeterministic
conditionals and loops, which gain a guard preheader. -/
private theorem stmt_nondetElimM_shape {P : PureExpr} [HasIdent P] [HasFvar P] [HasBool P]
    (s : Stmt P (Cmd P)) (σ : StringGenState) :
    (∃ s', (Stmt.nondetElimM s σ).1 = [s']) ∨
    (∃ tss ess md, s = .ite .nondet tss ess md) ∨
    (∃ m inv body md, s = .loop .nondet m inv body md) := by
  cases s with
  | cmd c => exact .inl ⟨.cmd c, by rw [nondetElimM_cmd]⟩
  | block l bss md => exact .inl ⟨_, Stmt.nondetElimM_block_out l bss md σ⟩
  | ite c tss ess md =>
    cases c with
    | det e => exact .inl ⟨_, Stmt.nondetElimM_ite_det_out e tss ess md σ⟩
    | nondet => exact .inr (.inl ⟨tss, ess, md, rfl⟩)
  | loop g m inv body md =>
    cases g with
    | det e => exact .inl ⟨_, Stmt.nondetElimM_loop_det_out e m inv body md σ⟩
    | nondet => exact .inr (.inr ⟨m, inv, body, md, rfl⟩)
  | exit l md => exact .inl ⟨.exit l md, by rw [nondetElimM_exit]⟩
  | typeDecl t md => exact .inl ⟨.typeDecl t md, by rw [nondetElimM_typeDecl]⟩

/-! ### Tail-guard definedness transport -/

/-- The pending-latch tail-definedness condition on a configuration is preserved
by any target run: a generated guard register, once defined, stays defined. -/
private theorem NdTailCfg.run {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [DecidableEq P.Ident]
    {tail : Option (P.Ident × MetaData P)} {c c' : Config P (Cmd P)} {tr : Trace P}
    (h : NdTailCfg tail c) (hrun : StepStmtStarE P (EvalCmdE P) c tr c') :
    NdTailCfg tail c' :=
  fun g md ht =>
    Config.varsDefined_star_ofE (fun he hs => evalCmdE_preserves_isSome he hs) hrun (h g md ht)

/-- A statement configuration satisfies the tail-definedness condition whenever
its store does. -/
private theorem NdTailCfg.of_def {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {ρ : Env P} (s : Stmt P (Cmd P)) (h : NdTailDef tail ρ.store) :
    NdTailCfg tail (.stmt s ρ) :=
  fun g md ht _ hy => hy ▸ h g md ht

/-- The tail-definedness condition transfers from a configuration to the `.seq`
built on it; both read the same environment. -/
private theorem NdTailCfg.seq_of {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {c : Config P (Cmd P)} {R : List (Stmt P (Cmd P))} (h : NdTailCfg tail c) :
    NdTailCfg tail (.seq c R) := h

/-- The tail-definedness condition transfers from a `.seq` configuration to its
inner configuration. -/
private theorem NdTailCfg.seq_inner {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {c : Config P (Cmd P)} {R : List (Stmt P (Cmd P))} (h : NdTailCfg tail (.seq c R)) :
    NdTailCfg tail c := h

/-- Extract the tail-definedness condition on a terminal configuration's store. -/
private theorem NdTailDef.of_terminal {P : PureExpr} {tail : Option (P.Ident × MetaData P)}
    {ρ : Env P} (h : NdTailCfg tail (.terminal ρ)) : NdTailDef tail ρ.store :=
  fun g md ht => h g md ht g rfl

/-- With no pending latch guard, the tail-definedness condition holds of every
store vacuously. -/
private theorem NdTailDef.none' {P : PureExpr} (σ : SemanticStore P) :
    NdTailDef (none : Option (P.Ident × MetaData P)) σ :=
  fun _ _ h => by cases h

/-- With no pending latch guard, the tail-definedness condition holds of every
configuration vacuously. -/
private theorem NdTailCfg.none' {P : PureExpr} (c : Config P (Cmd P)) :
    NdTailCfg (none : Option (P.Ident × MetaData P)) c :=
  fun _ _ h => by cases h

/-! ### Derived constructors -/

/-- Derived `NdSim.stmts` constructor with no pending latch guard: from a leaf
state, a rewritten statement list simulates its source list. -/
private theorem NdSim.stmts_none {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {σ : StringGenState} {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss) :
    NdSim none (Block.nondetElimM ss σ).2 (.stmts ss ρs)
      (.stmts (Block.nondetElimM ss σ).1 ρt) := by
  have h := NdSim.stmts (tail := none) hwf hl hng hread (NdTailDef.none' _)
  simpa [ndTail] using h

/-- Derived constructor: a simulation of inner configurations lifts to a
simulation of the two `.seq`s that have an empty continuation. -/
private theorem NdSim.seq_nil {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {σe : StringGenState} {inner inner' : Config P (Cmd P)}
    (h : NdSim none σe inner inner') (hwf : StringGenState.WF σe) :
    NdSim none σe (.seq inner []) (.seq inner' []) := by
  have h' := NdSim.seq (tail := none) (rest := []) h hwf noGen_nil
    Block.exprsShapeFree_nil (NdTailCfg.none' _)
  rw [nondetElimM_nil] at h'
  simpa [ndTail] using h'

/-! ### One-step simulation of leaf configurations -/

/-- A single-statement rewrite simulates one source statement step. -/
private theorem step_stmt {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident]
    {σ : StringGenState} {s s' : Stmt P (Cmd P)} {ρs ρt : Env P} {e : Trace P}
    {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [s])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName [s])
    (hout : (Stmt.nondetElimM s σ).1 = [s'])
    (hsourceWF : WellFormedStore ρs.store ρs.factory)
    (htargetWF : WellFormedStore ρt.store ρt.factory)
    (hcongr : WellFormedSemanticEvalExprCongr ρs.factory)
    (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P) (.stmt s ρs) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P) (.stmt s' ρt) e' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧
      NdSim none (Stmt.nondetElimM s σ).2 cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hguard : ∀ {c : P.Expr} {b : P.Val}, P.eval ρs.factory ρs.store c = some b →
      P.eval ρt.factory ρt.store c = some b := by
    intro c b hc
    rw [← hfac]
    exact hmono c b ρs.store ρt.store
      (storeAgreement_supplies_mono_premise _ _ hl.ext.2.1) hc
  have hreadStmt : Stmt.exprsShapeFree (P := P)
      NondetElim.isGeneratedName s :=
    Block.exprsShapeFree_singleton.mp hread
  cases s with
  | cmd c =>
    simp only [nondetElimM_cmd] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨σs', heval, rfl⟩ := StepStmtE.cmd_cases hstep
    obtain ⟨σt', hevt, htr, hl'⟩ :=
      hl.cmd_step hng hread hsourceWF htargetWF hcongr hmono heval
    exact ⟨_, _, StepStmtStarE.single (.step_cmd hevt), htr, .terminal hl'⟩
  | block l bss md =>
    rw [Stmt.nondetElimM_block_out] at hout
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    rw [Stmt.nondetElimM_block_state]
    exact ⟨_, [], StepStmtStarE.single .step_block, .nil,
      .block (NdSim.stmts_none hwf hl (noGen_block hng)
          (Stmt.exprsShapeFree_block.mp hreadStmt)) hl.ext.2
        (SemanticStore.isReserved.mono (Block.nondetElimM_genStep bss σ) hl.fresh)⟩
  | ite c tss ess md =>
    cases c with
    | det c =>
      rw [Stmt.nondetElimM_ite_det_out] at hout
      obtain rfl := (List.singleton_inj.mp hout).symm
      obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
      rw [Stmt.nondetElimM_ite_det_state]
      have hstepT : StringGenState.GenStep σ
          (Block.nondetElimM ess (Block.nondetElimM tss σ).2).2 :=
        (Block.nondetElimM_genStep tss σ).trans (Block.nondetElimM_genStep ess _)
      have hfresh := SemanticStore.isReserved.mono hstepT hl.fresh
      cases hadmin with
      | step_ite_true hc =>
        exact ⟨_, [], StepStmtStarE.single (.step_ite_true (hfac ▸ hguard hc)), .nil,
          .block (NdSim.stmts_none hwf hl (noGen_ite_then hng)
            (Stmt.exprsShapeFree_ite.mp hreadStmt).2.1) hl.ext.2 hfresh⟩
      | step_ite_false hc =>
        have hstep₁ := Block.nondetElimM_genStep tss σ
        exact ⟨_, [], StepStmtStarE.single (.step_ite_false (hfac ▸ hguard hc)), .nil,
          .block (NdSim.stmts_none (hstep₁.wf_mono hwf) (hl.mono hstep₁)
            (noGen_ite_else hng) (Stmt.exprsShapeFree_ite.mp hreadStmt).2.2) hl.ext.2 hfresh⟩
    | nondet =>
      rw [Stmt.nondetElimM_ite_nondet_out] at hout
      simp at hout
  | loop g m inv body md =>
    cases g with
    | det c =>
      rw [Stmt.nondetElimM_loop_det_out] at hout
      obtain rfl := (List.singleton_inj.mp hout).symm
      obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
      cases hadmin with
      | step_loop_enter hc =>
        refine ⟨_, [], StepStmtStarE.single (.step_loop_enter (hfac ▸ hguard hc)), .nil, ?_⟩
        have hinner : NdSim none σ (.block none ρs.store (.stmts body ρs))
            (.block none ρt.store (.stmts (Block.nondetElimM body σ).1 ρt)) :=
          .block (NdSim.stmts_none hwf hl (noGen_loop hng)
            (Stmt.exprsShapeFree_loop.mp hreadStmt).2.2.2) hl.ext.2 hl.fresh
        have h := NdSim.seq (tail := none) (rest := [.loop (.det c) m inv body md])
          hinner hwf hng hread (NdTailCfg.none' _)
        rw [nondetElimM_singleton_state, nondetElimM_singleton_out,
          Stmt.nondetElimM_loop_det_out] at h
        simpa [ndTail] using h
      | step_loop_exit hc =>
        exact ⟨_, [], StepStmtStarE.single (.step_loop_exit (hfac ▸ hguard hc)), .nil,
          .terminal (hl.mono (Stmt.nondetElimM_genStep _ σ))⟩
    | nondet =>
      rw [Stmt.nondetElimM_loop_nondet_out] at hout
      simp at hout
  | exit l md =>
    simp only [nondetElimM_exit] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    exact ⟨_, [], StepStmtStarE.single .step_exit, .nil, .exiting hl⟩
  | typeDecl t md =>
    simp only [nondetElimM_typeDecl] at hout ⊢
    obtain rfl := (List.singleton_inj.mp hout).symm
    obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hstep
    cases hadmin
    exact ⟨_, [], StepStmtStarE.single .step_typeDecl, .nil, .terminal hl⟩

/-- A statement-list leaf simulates one source step; a nondeterministic head
statement moves to its preheader state without consuming a target command. -/
private theorem step_stmts {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {ss : List (Stmt P (Cmd P))} {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName ss)
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName ss)
    (htail : NdTailDef tail ρt.store)
    (hstep : StepStmtE P (EvalCmdE P) (.stmts ss ρs) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.stmts ((Block.nondetElimM ss σ).1 ++ ndTail tail) ρt) e' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧
      NdSim tail (Block.nondetElimM ss σ).2 cs' ct' := by
  obtain ⟨rfl, hcases⟩ := stepE_stmts_cases hstep
  rcases hcases with ⟨rfl, rfl⟩ | ⟨s, rest, rfl, rfl⟩
  · simp only [nondetElimM_nil, List.nil_append]
    cases tail with
    | none => exact ⟨_, [], StepStmtStarE.single .step_stmts_nil, .nil, .terminal hl⟩
    | some gm =>
      obtain ⟨g, md⟩ := gm
      exact ⟨_, [], .refl _, .nil, .pendingHavoc hl (htail g md rfl)⟩
  · have hng₁ := noGen_head hng
    have hngr := noGen_tail hng
    have ⟨hread₁, hreadr⟩ := Block.exprsShapeFree_cons_iff.mp hread
    have hreadHead : Block.exprsShapeFree (P := P)
        NondetElim.isGeneratedName [s] :=
      Block.exprsShapeFree_singleton.mpr hread₁
    have hwf₁ : StringGenState.WF (Stmt.nondetElimM s σ).2 :=
      (Stmt.nondetElimM_genStep s σ).wf_mono hwf
    rw [Block.nondetElimM_cons_out, Block.nondetElimM_cons_state]
    rcases stmt_nondetElimM_shape s σ with
      ⟨s', hs'⟩ | ⟨tss, ess, md, rfl⟩ | ⟨m, inv, body, md, rfl⟩
    · rw [hs', List.singleton_append, List.cons_append]
      exact ⟨_, [], StepStmtStarE.single .step_stmts_cons, .nil,
        .seq (.stmt hwf hl hng₁ hreadHead hs') hwf₁ hngr hreadr
          (NdTailCfg.of_def _ htail)⟩
    · rw [Stmt.nondetElimM_ite_nondet_out]
      dsimp only
      simp only [List.cons_append, List.nil_append]
      exact ⟨_, [], StepStmtStarE.single .step_stmts_cons, .nil,
        .seqIte hwf hl hng₁ hreadHead hngr hreadr htail⟩
    · rw [Stmt.nondetElimM_loop_nondet_out]
      dsimp only
      simp only [List.cons_append, List.nil_append]
      exact ⟨_, [], StepStmtStarE.single .step_stmts_cons, .nil,
        .seqLoop hwf hl hng₁ hreadHead hngr hreadr htail⟩

/-- Preheader of a nondeterministic `ite`: the source branch choice drives the
target guard initialization, and the target then enters the matching branch
of the rewritten deterministic `ite`, emitting no events. -/
private theorem step_seqIte {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {tss ess : List (Stmt P (Cmd P))} {md : MetaData P} {rest : List (Stmt P (Cmd P))}
    {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.ite .nondet tss ess md])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
      [.ite .nondet tss ess md])
    (hngr : SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest)
    (hreadr : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest)
    (htail : NdTailDef tail ρt.store)
    (hvar : WellFormedSemanticEvalVar ρs.factory) (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P) (.seq (.stmt (.ite .nondet tss ess md) ρs) rest) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndIteTgt tss ess md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
              ndTail tail))) e' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).2
        cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hvarT : WellFormedSemanticEvalVar ρt.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρt.factory := hfac ▸ hmono
  have hstep₁ := StringGenState.GenStep.of_gen NondetElim.prefixIte σ
  have hwf₁ := hstep₁.wf_mono hwf
  have hstepR : StringGenState.GenStep (StringGenState.gen NondetElim.prefixIte σ).2
      (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 := by
    rw [Stmt.nondetElimM_ite_nondet_state]
    exact (Block.nondetElimM_genStep tss _).trans (Block.nondetElimM_genStep ess _)
  have hwfR : StringGenState.WF (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2 :=
    (Stmt.nondetElimM_genStep _ σ).wf_mono hwf
  have htc : NdTailCfg tail
      (.seq (.stmt (.cmd (HasInit.init (ndIteGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
        (ndIteTgt tss ess md σ ::
          ((Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail))) :=
    NdTailCfg.seq_of (NdTailCfg.of_def _ htail)
  have hreadIte := Stmt.exprsShapeFree_ite.mp
    (Block.exprsShapeFree_singleton.mp hread)
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_ite_nondet_true =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).1
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.1 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndIteGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _ (tgt_init_then (md := md) (X := ndIteTgt tss ess md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_ite_true hg)))
      exact ⟨_, _, hrun, .nil,
        .seq (.block (NdSim.stmts_none hwf₁ hl₁ (noGen_ite_then hng) hreadIte.2.1)
          hl₁.ext.2
          (SemanticStore.isReserved.mono hstepR hl₁.fresh)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
    | step_ite_nondet_false =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).2
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.1 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndIteGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _ (tgt_init_then (md := md) (X := ndIteTgt tss ess md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.ite .nondet tss ess md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_ite_false hg)))
      have hstep₂ := Block.nondetElimM_genStep tss (StringGenState.gen NondetElim.prefixIte σ).2
      exact ⟨_, _, hrun, .nil,
        .seq (.block (NdSim.stmts_none (hstep₂.wf_mono hwf₁) (hl₁.mono hstep₂)
            (noGen_ite_else hng) hreadIte.2.2) hl₁.ext.2
          (SemanticStore.isReserved.mono hstepR hl₁.fresh)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
  · cases h
  · cases h

/-- Preheader of a nondeterministic loop: the source's first enter/exit choice
drives the target guard initialization, after which the rewritten
deterministic loop takes the same decision, emitting no events. -/
private theorem step_seqLoop {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σ : StringGenState}
    {m : Option P.Expr} {inv : List (String × P.Expr)} {body : List (Stmt P (Cmd P))}
    {md : MetaData P} {rest : List (Stmt P (Cmd P))}
    {ρs ρt : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hwf : StringGenState.WF σ) (hl : NdLeaf σ ρs ρt)
    (hng : SrcNoGenWrites (P := P) NondetElim.isGeneratedName [.loop .nondet m inv body md])
    (hread : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName
      [.loop .nondet m inv body md])
    (hngr : SrcNoGenWrites (P := P) NondetElim.isGeneratedName rest)
    (hreadr : Block.exprsShapeFree (P := P) NondetElim.isGeneratedName rest)
    (htail : NdTailDef tail ρt.store)
    (hvar : WellFormedSemanticEvalVar ρs.factory) (hmono : WellFormedSemanticEvalMono ρs.factory)
    (hstep : StepStmtE P (EvalCmdE P)
      (.seq (.stmt (.loop .nondet m inv body md) ρs) rest) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
          (ndLoopTgt m inv body md σ ::
            ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
              ndTail tail))) e' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧
      NdSim tail (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).2
        cs' ct' := by
  have hfac : ρs.factory = ρt.factory := hl.ext.1
  have hvarT : WellFormedSemanticEvalVar ρt.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρt.factory := hfac ▸ hmono
  have hstep₁ := StringGenState.GenStep.of_gen NondetElim.prefixLoop σ
  have hwf₁ := hstep₁.wf_mono hwf
  have hσr : (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 =
      (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 :=
    Stmt.nondetElimM_loop_nondet_state m inv body md σ
  have hstepR : StringGenState.GenStep (StringGenState.gen NondetElim.prefixLoop σ).2
      (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 := by
    rw [hσr]
    exact Block.nondetElimM_genStep body _
  have hwfR : StringGenState.WF (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2 :=
    (Stmt.nondetElimM_genStep _ σ).wf_mono hwf
  have htc : NdTailCfg tail
      (.seq (.stmt (.cmd (HasInit.init (ndLoopGuard (P := P) σ) HasBool.boolTy .nondet md)) ρt)
        (ndLoopTgt m inv body md σ ::
          ((Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail))) :=
    NdTailCfg.seq_of (NdTailCfg.of_def _ htail)
  have hreadLoop := Stmt.exprsShapeFree_loop.mp
    (Block.exprsShapeFree_singleton.mp hread)
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_loop_nondet_enter =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).1
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.2 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndLoopGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_init_then (md := md) (X := ndLoopTgt m inv body md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_loop_enter hg)))
      have hgdef : (SemanticStore.update ρt.store (ndLoopGuard (P := P) σ)
          (HasBool.ttVal ρt.factory) (ndLoopGuard (P := P) σ)).isSome = true := by
        simp [SemanticStore.update]
      have hbody := NdSim.stmts (tail := some (ndLoopGuard (P := P) σ, md)) hwf₁ hl₁
        (noGen_loop hng) hreadLoop.2.2.2 (fun g' md' h => by cases h; exact hgdef)
      have hiter := NdSim.iter (m := m) (inv := inv) hwf₁ (noGen_loop hng)
        hreadLoop.2.2.2 hl₁.ext.2 hl₁.fresh hgdef hbody
      rw [← hσr] at hiter
      exact ⟨_, _, hrun, .nil,
        .seq hiter hwfR hngr hreadr (htc.run hrun).seq_inner⟩
    | step_loop_nondet_exit =>
      have hv := (HasBool.boolIsValOfTy ρt.factory).2
      obtain ⟨hnone, hl₁⟩ := hl.init_guard hwf (NondetElim.isGeneratedName_gen.2 σ) hv
      have hg := eval_guard_update (σ := ρt.store) (g := ndLoopGuard (P := P) σ) hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_init_then (md := md) (X := ndLoopTgt m inv body md σ)
          (R := (Block.nondetElimM rest (Stmt.nondetElimM (.loop .nondet m inv body md) σ).2).1 ++
            ndTail tail) hnone hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_loop_exit hg)))
      exact ⟨_, _, hrun, .nil,
        .seq (.terminal (hl₁.mono hstepR)) hwfR hngr hreadr
          (htc.run hrun).seq_inner⟩
  · cases h
  · cases h

/-- Loop latch: the source's enter/exit choice at the loop head drives the
pending target latch havoc; the target leaves the iteration scope and its
rewritten loop takes the same decision, realigning silently. -/
private theorem step_headStmt {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {σ σb : StringGenState} {m : Option P.Expr} {inv : List (String × P.Expr)}
    {body : List (Stmt P (Cmd P))} {md : MetaData P} {σps σpt : SemanticStore P}
    {ρsb ρtb : Env P} {e : Trace P} {cs' : Config P (Cmd P)}
    (hinv : NdHeadInv σ σb body σps σpt ρsb ρtb)
    (hvar : WellFormedSemanticEvalVar ρsb.factory) (hmono : WellFormedSemanticEvalMono ρsb.factory)
    (hstep : StepStmtE P (EvalCmdE P)
      (.seq (.stmt (.loop .nondet m inv body md)
        { ρsb with store := projectStore σps ρsb.store }) []) e cs') :
    ∃ ct' e', StepStmtStarE P (EvalCmdE P)
        (.seq (.block none σpt (.stmts [.cmd (HasHavoc.havoc (ndLoopGuard (P := P) σ) md)] ρtb))
          [ndLoopTgt m inv body md σ]) e' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧
      NdSim none
        (Block.nondetElimM body
          (StringGenState.gen NondetElim.prefixLoop σ).2).2 cs' ct' := by
  have hfac : ρsb.factory = ρtb.factory := hinv.leaf.ext.1
  have hvarT : WellFormedSemanticEvalVar ρtb.factory := hfac ▸ hvar
  have hmonoT : WellFormedSemanticEvalMono ρtb.factory := hfac ▸ hmono
  have hgx : NdExtra (P := P) (ndLoopGuard (P := P) σ) :=
    ⟨_, NondetElim.isGeneratedName_gen.2 σ, rfl⟩
  obtain ⟨prev, hprev⟩ := Option.isSome_iff_exists.mp hinv.guard
  have hprevTy := hinv.leaf.typed _ prev hgx hprev
  have hwfE : StringGenState.WF
      (Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2).2 :=
    (Block.nondetElimM_genStep body _).wf_mono hinv.wf
  rcases stepE_seq_cases hstep with ⟨inner', hinner, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
  · obtain ⟨rfl, hadmin⟩ := stepE_stmt_admin (fun _ h => by cases h) hinner
    cases hadmin with
    | step_loop_nondet_enter =>
      have hv := (HasBool.boolIsValOfTy ρtb.factory).1
      have hl' := hinv.leaf.latch hgx hv hinv.parent hinv.parentFresh
      have hg := eval_guard_latch (σ := ρtb.store) hinv.parentGuard hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_latch (md := md) (σpt := σpt) (L' := ndLoopTgt m inv body md σ) hprev hprevTy hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_loop_enter hg)))
      have hgdef : (projectStore σpt (SemanticStore.update ρtb.store (ndLoopGuard (P := P) σ)
          (HasBool.ttVal ρtb.factory)) (ndLoopGuard (P := P) σ)).isSome = true := by
        simp [projectStore, hinv.parentGuard, SemanticStore.update]
      have hbody := NdSim.stmts (tail := some (ndLoopGuard (P := P) σ, md)) hinv.wf hl'
        hinv.noGen hinv.noRead (fun g' md' h => by cases h; exact hgdef)
      have hiter := NdSim.iter (m := m) (inv := inv) hinv.wf hinv.noGen hinv.noRead
        hl'.ext.2 hl'.fresh hgdef hbody
      exact ⟨_, _, hrun, .nil, NdSim.seq_nil hiter hwfE⟩
    | step_loop_nondet_exit =>
      have hv := (HasBool.boolIsValOfTy ρtb.factory).2
      have hl' := hinv.leaf.latch hgx hv hinv.parent hinv.parentFresh
      have hg := eval_guard_latch (σ := ρtb.store) hinv.parentGuard hv hvarT hmonoT
      have hrun := ReflTransTrace.trans _
        (tgt_latch (md := md) (σpt := σpt) (L' := ndLoopTgt m inv body md σ) hprev hprevTy hv hvarT)
        (StepStmtStarE.single (.step_seq_inner (.step_loop_exit hg)))
      exact ⟨_, _, hrun, .nil,
        NdSim.seq_nil (.terminal (hl'.mono (Block.nondetElimM_genStep body _))) hwfE⟩
  · cases h
  · cases h

/-! ### Forward simulation -/

/-- One source event step is matched by a finite target run under
`Trace.WithWF (EventArg.ExtendsEnv NdExtra)`; user commands replay in lockstep
and all generated guard steps are silent. -/
private theorem NdSim.step {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σe : StringGenState}
    {cs ct : Config P (Cmd P)} (h : NdSim tail σe cs ct) :
    ∀ {e : Trace P} {cs' : Config P (Cmd P)},
      Config.storeWellDefined cs →
      Config.storeWellDefined ct →
      WellFormedSemanticEvalExprCongr cs.getEnv.factory →
      WellFormedSemanticEvalVar cs.getEnv.factory →
      WellFormedSemanticEvalMono cs.getEnv.factory →
      StepStmtE P (EvalCmdE P) cs e cs' →
      ∃ ct' e', StepStmtStarE P (EvalCmdE P) ct e' ct' ∧
        Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) e e' ∧ NdSim tail σe cs' ct' := by
  induction h with
  | stmts hwf hl hng hread htail =>
    intro e cs' _ _ _ _ _ hstep
    exact step_stmts hwf hl hng hread htail hstep
  | stmt hwf hl hng hread hout =>
    intro e cs' hsourceWF htargetWF hcongr _ hmono hstep
    exact step_stmt hwf hl hng hread hout hsourceWF htargetWF hcongr hmono hstep
  | terminal _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (stepE_terminal_false hstep).elim
  | pendingHavoc _ _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (stepE_terminal_false hstep).elim
  | exiting _ =>
    intro e cs' _ _ _ _ _ hstep
    exact (StepStmtE.exiting_false hstep).elim
  | seq hinner hwf hng hread htail ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases stepE_seq_cases hstep with
      ⟨inner'', hinnerStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l, ρ, rfl, rfl, rfl⟩
    · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
        ih hsourceWF htargetWF hcongr hvar hmono hinnerStep
      exact ⟨_, e', seq_inner_starE _ hrun, htr,
        .seq hsim hwf hng hread (htail.run hrun)⟩
    · cases hinner with
      | terminal hl =>
        exact ⟨_, [], StepStmtStarE.single .step_seq_done, .nil,
          .stmts hwf hl hng hread (NdTailDef.of_terminal htail)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single .step_seq_exit, .nil,
          .exiting (hl.mono (Block.nondetElimM_genStep _ _))⟩
  | block hinner hp hf ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases StepStmtE.block_cases hstep with
      ⟨inner'', hinnerStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l', ρ, rfl, rfl, hlbl, rfl⟩ |
        ⟨l', ρ, rfl, rfl, hlbl, rfl⟩
    · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
        ih hsourceWF.2 htargetWF.2 hcongr hvar hmono hinnerStep
      exact ⟨_, e', block_inner_starE hrun, htr, .block hsim hp hf⟩
    · cases hinner with
      | terminal hl =>
        exact ⟨_, [], StepStmtStarE.single .step_block_done, .nil,
          .terminal (hl.project hp hf)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_block_exit_match hlbl), .nil,
          .terminal (hl.project hp hf)⟩
    · cases hinner with
      | exiting hl =>
        exact ⟨_, [], StepStmtStarE.single (.step_block_exit_mismatch hlbl), .nil,
          .exiting (hl.project hp hf)⟩
  | seqIte hwf hl hng hread hngr hreadr htail =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_seqIte hwf hl hng hread hngr hreadr htail hvar hmono hstep
  | seqLoop hwf hl hng hread hngr hreadr htail =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_seqLoop hwf hl hng hread hngr hreadr htail hvar hmono hstep
  | iter hwf hng hread hp hf hg hbody ih =>
    intro e cs' hsourceWF htargetWF hcongr hvar hmono hstep
    rcases stepE_seq_cases hstep with ⟨inner'', hinnerStep, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, _, _⟩
    · rcases StepStmtE.block_cases hinnerStep with
        ⟨cs'', hbodyStep, rfl⟩ | ⟨ρ, rfl, rfl, rfl⟩ | ⟨l', ρ, rfl, rfl, hlbl, rfl⟩ |
          ⟨l', ρ, rfl, rfl, hlbl, rfl⟩
      · obtain ⟨ct', e', hrun, htr, hsim⟩ :=
          ih hsourceWF.2 htargetWF.2 hcongr hvar hmono hbodyStep
        exact ⟨_, e', seq_inner_starE _ (block_inner_starE hrun), htr,
          .iter hwf hng hread hp hf hg hsim⟩
      · cases hbody with
        | pendingHavoc hl hgdef =>
          exact ⟨_, [], .refl _, .nil, .headTerm ⟨hwf, hng, hread, hp, hf, hg, hl, hgdef⟩⟩
      · cases hlbl
      · cases hbody with
        | exiting hl =>
          exact ⟨_, [], StepStmtStarE.single (.step_seq_inner
              (.step_block_exit_mismatch hlbl)), .nil,
            .seqExit
              (hl.project hp
                (SemanticStore.isReserved.mono
                  (Block.nondetElimM_genStep _ _) hf))⟩
    · cases h
    · cases h
  | headTerm hinv =>
    intro e cs' _ _ _ _ _ hstep
    rcases stepE_seq_cases hstep with ⟨_, hinnerStep, rfl⟩ | ⟨_, h, rfl, rfl⟩ | ⟨_, _, h, _, _⟩
    · exact (stepE_terminal_false hinnerStep).elim
    · cases h
      exact ⟨_, [], .refl _, .nil, .headStmts hinv⟩
    · cases h
  | headStmts hinv =>
    intro e cs' _ _ _ _ _ hstep
    obtain ⟨rfl, hcases⟩ := stepE_stmts_cases hstep
    rcases hcases with ⟨h, _⟩ | ⟨_, _, h, rfl⟩
    · cases h
    · cases h
      exact ⟨_, [], .refl _, .nil, .headStmt hinv⟩
  | headStmt hinv =>
    intro e cs' _ _ _ hvar hmono hstep
    exact step_headStmt hinv hvar hmono hstep
  | seqExit hl =>
    intro e cs' _ _ _ _ _ hstep
    rcases stepE_seq_cases hstep with ⟨_, hinnerStep, rfl⟩ | ⟨_, h, _, _⟩ | ⟨_, _, h, rfl, rfl⟩
    · exact (StepStmtE.exiting_false hinnerStep).elim
    · cases h
    · cases h
      exact ⟨_, [], StepStmtStarE.single .step_seq_exit, .nil, .exiting hl⟩

/-- Every finite source trace prefix is matched by a target trace prefix
reaching a related configuration. -/
private theorem NdSim.trace {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P] [HasOps P] [LawfulHasFvar P] [LawfulHasVal P]
    {tail : Option (P.Ident × MetaData P)} {σe : StringGenState}
    {cs ct cs' : Config P (Cmd P)} {tr : Trace P}
    (h : NdSim tail σe cs ct)
    (hcongr : WellFormedSemanticEvalExprCongr cs.getEnv.factory)
    (hsourceWF : Config.storeWellDefined cs)
    (htargetWF : Config.storeWellDefined ct)
    (hsourceVal : WellFormedSemanticEvalVal (P := P) cs.getEnv.factory)
    (htargetVal : WellFormedSemanticEvalVal (P := P) ct.getEnv.factory)
    (hvar : WellFormedSemanticEvalVar cs.getEnv.factory)
    (hmono : WellFormedSemanticEvalMono cs.getEnv.factory)
    (hrun : StepStmtStarE P (EvalCmdE P) cs tr cs') :
    ∃ ct' tr', StepStmtStarE P (EvalCmdE P) ct tr' ct' ∧
      Trace.WithWF (P := P) (EventArg.ExtendsEnv NdExtra) tr tr' ∧ NdSim tail σe cs' ct' := by
  induction hrun generalizing ct with
  | refl => exact ⟨ct, [], .refl _, .nil, h⟩
  | step c e c₁ rest c₂ hstep _ ih =>
    obtain ⟨ct₁, e', hrun₁, htr₁, h₁⟩ :=
      h.step hsourceWF htargetWF hcongr hvar hmono hstep
    have hsourceWF₁ : Config.storeWellDefined c₁ :=
      Config.storeWellDefined_step_evalCmdE hsourceVal hstep hsourceWF
    have htargetWF₁ : Config.storeWellDefined ct₁ :=
      Config.storeWellDefined_star_evalCmdE htargetVal hrun₁ htargetWF
    have hfac : c.getEnv.factory = c₁.getEnv.factory := stepE_preserves_factory hstep
    have htargetFac : ct.getEnv.factory = ct₁.getEnv.factory :=
      starE_preserves_factory hrun₁
    obtain ⟨ct₂, tr', hrun₂, htr₂, h₂⟩ :=
      ih h₁ (hfac ▸ hcongr) hsourceWF₁ htargetWF₁
        (hfac ▸ hsourceVal) (htargetFac ▸ htargetVal)
        (hfac ▸ hvar) (hfac ▸ hmono)
    exact ⟨ct₂, e' ++ tr', ReflTransTrace.trans _ hrun₁ hrun₂,
      htr₁.append htr₂, h₂⟩

end NondetElimTrace

section NondetElimAnnotations

variable {P : PureExpr} [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P]

omit [HasIdent P] in
/-- The annotation of the guard `g : bool` that `nondetElim` reads holds once `g` is
    defined with type `bool`. -/
private theorem annotates_generatedGuard [LawfulHasFvars P] (Γ : VarTyping P) (g : P.Ident) :
    (Γ.extend [(g, HasBool.boolTy)]).annotates
      (ExprOrNondet.getTypedVars (.det (HasFvar.mkTypedFvar (P := P) g HasBool.boolTy))) := by
  intro x ty hm
  have hm' := LawfulHasFvars.mkTypedFvar_getTypedFvars (P := P) g HasBool.boolTy hm
  simp only [List.mem_singleton, Prod.mk.injEq] at hm'
  obtain ⟨rfl, rfl⟩ := hm'
  simp [VarTyping.extend]

omit [HasFvar P] [HasFvars P] in
/-- Extending a typing at a generated name keeps it agreeing with another typing on every
    name that is not generated. -/
private theorem extend_generated {Γs Γt : VarTyping P} {g : P.Ident}
    (hg : IdentOfStringKind NondetElim.isGeneratedName g)
    (hN : ∀ y, ¬ IdentOfStringKind NondetElim.isGeneratedName y → Γt y = Γs y) :
    ∀ y, ¬ IdentOfStringKind NondetElim.isGeneratedName y →
      Γt.extend [(g, HasBool.boolTy)] y = Γs y := by
  intro y hy
  have hgy : g ≠ y := fun h => hy (h ▸ hg)
  simp [VarTyping.extend, hgy, hN y hy]

mutual
/-- The output of `Stmt.nondetElimM s`, followed by `ys`, passes the annotation check against
    a typing `Γt` that agrees with the source's typing `Γs` on every name that is not
    generated, given that `s` reads no generated name and that `ys` passes it against every
    such typing extended with the definitions of `s`. -/
private theorem Stmt.nondetElimM_fvarTypes [LawfulHasFvars P] (s : Stmt P (Cmd P))
    (σ : StringGenState)
    (Γs Γt : VarTyping P)
    (hN : ∀ y, ¬ IdentOfStringKind NondetElim.isGeneratedName y → Γt y = Γs y)
    (hreads : ∀ y ∈ Stmt.getVars s, ¬ IdentOfStringKind NondetElim.isGeneratedName y)
    (hs : Stmt.fvarTypesWellAnnotated Γs s) (ys : List (Stmt P (Cmd P)))
    (hys : ∀ Γt' : VarTyping P,
      (∀ y, ¬ IdentOfStringKind NondetElim.isGeneratedName y →
        Γt' y = Γs.extend (Stmt.typedDefinedVars s) y) →
      Block.fvarTypesWellAnnotated Γt' ys) :
    Block.fvarTypesWellAnnotated Γt ((Stmt.nondetElimM s σ).1 ++ ys) := by
  match s with
  | .cmd c =>
    simp only [Stmt.nondetElimM, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars, HasVarsImp.readVars] at hreads
    refine ⟨VarTyping.annotates_congr hs fun x ty hm =>
        hN x (hreads x (Cmd.mem_getVars_of_typed c (ty := ty) ?_)),
      hys _ fun y hy => VarTyping.extend_congr _ (hN y hy)⟩
    simpa [HasTypedVarsImp.typedReadVars] using hm
  | .block l bss md =>
    rcases hB : Block.nondetElimM bss σ with ⟨bss', σ'⟩
    simp only [Stmt.nondetElimM, hB, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars] at hreads
    have hb := Block.nondetElimM_fvarTypes bss σ Γs Γt hN hreads hs [] fun _ => trivial
    rw [hB, List.append_nil] at hb
    exact ⟨hb, hys Γt hN⟩
  | .ite (.det e) tss ess md =>
    rcases hT : Block.nondetElimM tss σ with ⟨tss', σ₁⟩
    rcases hE : Block.nondetElimM ess σ₁ with ⟨ess', σ₂⟩
    simp only [Stmt.nondetElimM, hT, hE, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars, List.mem_append] at hreads
    obtain ⟨hc, ht, he⟩ := hs
    have ht' := Block.nondetElimM_fvarTypes tss σ Γs Γt hN
      (fun y hy => hreads y (.inl (.inr hy))) ht [] fun _ => trivial
    have he' := Block.nondetElimM_fvarTypes ess σ₁ Γs Γt hN
      (fun y hy => hreads y (.inr hy)) he [] fun _ => trivial
    rw [hT, List.append_nil] at ht'
    rw [hE, List.append_nil] at he'
    exact ⟨⟨VarTyping.annotates_congr hc fun x _ hm =>
      hN x (hreads x (.inl (.inl (ExprOrNondet.mem_getVars_of_typed _ hm)))), ht', he'⟩, hys Γt hN⟩
  | .ite .nondet tss ess md =>
    rcases hT : Block.nondetElimM tss (StringGenState.gen NondetElim.prefixIte σ).2
      with ⟨tss', σ₂⟩
    rcases hE : Block.nondetElimM ess σ₂ with ⟨ess', σ₃⟩
    simp only [Stmt.nondetElimM, hT, hE, List.cons_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars, List.mem_append] at hreads
    obtain ⟨-, ht, he⟩ := hs
    have hg : IdentOfStringKind NondetElim.isGeneratedName
        (HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixIte σ).1) :=
      ⟨_, NondetElim.isGeneratedName_gen.1 σ, rfl⟩
    have hN₁ := extend_generated (Γt := Γt) hg hN
    have ht' := Block.nondetElimM_fvarTypes tss (StringGenState.gen NondetElim.prefixIte σ).2
      Γs _ hN₁ (fun y hy => hreads y (.inl (.inr hy))) ht [] fun _ => trivial
    have he' := Block.nondetElimM_fvarTypes ess σ₂ Γs _ hN₁
      (fun y hy => hreads y (.inr hy)) he [] fun _ => trivial
    rw [hT, List.append_nil] at ht'
    rw [hE, List.append_nil] at he'
    refine ⟨?_, ⟨annotates_generatedGuard Γt _, ht', he'⟩, hys _ hN₁⟩
    intro x ty hm
    simp [HasTypedVarsImp.typedReadVars, HasInit.init, Cmd.getTypedVars,
      ExprOrNondet.getTypedVars] at hm
  | .loop (.det e) m inv body md =>
    rcases hB : Block.nondetElimM body σ with ⟨body', σ'⟩
    simp only [Stmt.nondetElimM, hB, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars, List.mem_append] at hreads
    obtain ⟨hc, hm, hi, hb⟩ := hs
    have hb' := Block.nondetElimM_fvarTypes body σ Γs Γt hN
      (fun y hy => hreads y (.inr hy)) hb [] fun _ => trivial
    rw [hB, List.append_nil] at hb'
    refine ⟨⟨VarTyping.annotates_congr hc fun x _ hx =>
        hN x (hreads x (.inl (.inl (.inl (ExprOrNondet.mem_getVars_of_typed _ hx))))),
      VarTyping.annotates_congr hm fun x ty hx => hN x (hreads x (.inl (.inl (.inr ?_)))),
      VarTyping.annotates_congr hi fun x ty hx => hN x (hreads x (.inl (.inr ?_))), hb'⟩, hys Γt hN⟩
    · cases m with
      | none => simp at hx
      | some m => exact LawfulHasFvars.mem_getFvars_of_typed _ _ _ hx
    · obtain ⟨lp, hlp, hx⟩ := List.mem_flatMap.1 hx
      exact List.mem_flatMap.2 ⟨lp, hlp, LawfulHasFvars.mem_getFvars_of_typed _ _ _ hx⟩
  | .loop .nondet m inv body md =>
    rcases hB : Block.nondetElimM body (StringGenState.gen NondetElim.prefixLoop σ).2
      with ⟨body', σ'⟩
    simp only [Stmt.nondetElimM, hB, List.cons_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated] at hs ⊢
    simp only [Stmt.getVars, List.mem_append] at hreads
    obtain ⟨-, hm, hi, hb⟩ := hs
    have hg : IdentOfStringKind NondetElim.isGeneratedName
        (HasIdent.ident (P := P) (StringGenState.gen NondetElim.prefixLoop σ).1) :=
      ⟨_, NondetElim.isGeneratedName_gen.2 σ, rfl⟩
    have hN₁ := extend_generated (Γt := Γt) hg hN
    have hb' := Block.nondetElimM_fvarTypes body (StringGenState.gen NondetElim.prefixLoop σ).2
      Γs _ hN₁ (fun y hy => hreads y (.inr hy)) hb
      [.cmd (HasHavoc.havoc (HasIdent.ident (P := P)
        (StringGenState.gen NondetElim.prefixLoop σ).1) md)]
      fun _ => ⟨fun x ty hx => by
        simp [HasTypedVarsImp.typedReadVars, HasHavoc.havoc, Cmd.getTypedVars,
          ExprOrNondet.getTypedVars] at hx, trivial⟩
    rw [hB] at hb'
    refine ⟨?_, ⟨annotates_generatedGuard Γt _,
      VarTyping.annotates_congr hm fun x ty hx => hN₁ x (hreads x (.inl (.inl (.inr ?_)))),
      VarTyping.annotates_congr hi fun x ty hx => hN₁ x (hreads x (.inl (.inr ?_))), hb'⟩,
      hys _ hN₁⟩
    · intro x ty hx
      simp [HasTypedVarsImp.typedReadVars, HasInit.init, Cmd.getTypedVars,
        ExprOrNondet.getTypedVars] at hx
    · cases m with
      | none => simp at hx
      | some m => exact LawfulHasFvars.mem_getFvars_of_typed _ _ _ hx
    · obtain ⟨lp, hlp, hx⟩ := List.mem_flatMap.1 hx
      exact List.mem_flatMap.2 ⟨lp, hlp, LawfulHasFvars.mem_getFvars_of_typed _ _ _ hx⟩
  | .exit l md | .typeDecl t md =>
    simp only [Stmt.nondetElimM, List.singleton_append, Block.fvarTypesWellAnnotated,
      Stmt.fvarTypesWellAnnotated, true_and]
    exact hys Γt hN
  termination_by sizeOf s

/-- The output of `Block.nondetElimM ss σ`, followed by `ys`, passes the annotation check
    against a typing `Γt` that agrees with `Γs` on every name `nondetElim` does not generate,
    when `ss` passes it against `Γs`, reads no generated name, and `ys` passes it against
    every typing. -/
private theorem Block.nondetElimM_fvarTypes [LawfulHasFvars P] (ss : List (Stmt P (Cmd P)))
    (σ : StringGenState)
    (Γs Γt : VarTyping P)
    (hN : ∀ y, ¬ IdentOfStringKind NondetElim.isGeneratedName y → Γt y = Γs y)
    (hreads : ∀ y ∈ Block.getVars ss, ¬ IdentOfStringKind NondetElim.isGeneratedName y)
    (hss : Block.fvarTypesWellAnnotated Γs ss) (ys : List (Stmt P (Cmd P)))
    (hys : ∀ Γ : VarTyping P, Block.fvarTypesWellAnnotated Γ ys) :
    Block.fvarTypesWellAnnotated Γt ((Block.nondetElimM ss σ).1 ++ ys) := by
  match ss with
  | [] =>
    simp only [Block.nondetElimM, List.nil_append]
    exact hys Γt
  | s :: rest =>
    rcases hS : Stmt.nondetElimM s σ with ⟨out, σ₁⟩
    rcases hR : Block.nondetElimM rest σ₁ with ⟨out', σ₂⟩
    simp only [Block.nondetElimM, hS, hR, List.append_assoc]
    simp only [Block.getVars, List.mem_append] at hreads
    simp only [Block.fvarTypesWellAnnotated] at hss
    have h := Stmt.nondetElimM_fvarTypes s σ Γs Γt hN (fun y hy => hreads y (.inl hy)) hss.1
      (out' ++ ys) fun Γt' hN' => by
        have hr := Block.nondetElimM_fvarTypes rest σ₁ _ Γt' hN'
          (fun y hy => hreads y (.inr hy)) hss.2 ys hys
        rwa [hR] at hr
    rwa [hS] at h
  termination_by sizeOf ss
end

end NondetElimAnnotations

open NondetElimTrace in
/-- `Block.nondetElim` overapproximates its source on event traces. For a
block that never writes or reads an `NondetElim.isGeneratedName` name, every
finite source trace prefix is matched by a target prefix under
`Trace.WithWF (EventArg.ExtendsEnv NdExtra)`.
Generated guard commands are event-silent and the source commands replay
one-for-one, so no event is inserted or dropped on either side.
Terminating and exiting runs preserve their outcome shape and end in an
environment extended only by generated guard registers. -/
theorem NondetElim.Internal.overapproximates_upto_base {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [LawfulHasVal P]
    [HasIdent P] [HasInt P] [HasIntOps P] [DecidableEq P.Ident]
    [HasOps P] [LawfulHasFvar P] [LawfulHasFvars P] [LawfulHasIdent P]
    [HasSubstFvar P]
    (params : InitEnvWFParams P)
    (hprefixes : prefixesDisjoint params.prefixIdents
      NondetElim.isGeneratedName) :
    Specification.Transform.OverapproximatesTracesUptoWhen
      (Trace.WithWF (P := P) (EventArg.ExtendsEnv NondetElimTrace.NdExtra))
      (fun x y => x = y)
      (Env.ExtendsWith (IdentOfStringKind NondetElim.isGeneratedName))
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P)
        ⟨InitEnvWFParams P, BlockInitEnvWF⟩)
      (EventLang.imperativeBlockE P (Cmd P) (EvalCmdE P)
        ⟨InitEnvWFParams P, BlockInitEnvWF⟩)
      (fun ss => some (Block.nondetElim ss))
      (fun ss => SrcNoGenWrites NondetElim.isGeneratedName ss
        ∧ Block.exprsShapeFree NondetElim.isGeneratedName ss)
      (params.extend NondetElim.prefixesReserved) params := by
  intro ss ss' ht hpre ρ₀ ρ₀' hEq hwf
  subst hEq
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨hng, hread⟩ := hpre
  change BlockInitEnvWF (params.extend NondetElim.prefixesReserved)
    ss ρ₀ at hwf
  have hsrc : ∀ x, NdExtra (P := P) x → ρ₀.store x = none := by
    intro ident hident
    obtain ⟨name, hname, heq⟩ := hident
    subst ident
    apply hwf.generatedNamesFresh
    refine ⟨name, ?_, rfl⟩
    rw [NondetElim.isGeneratedName_iff] at hname
    rcases hname with ⟨state, rfl⟩ | ⟨state, rfl⟩
    · exact ⟨NondetElim.prefixIte, by
        simp [InitEnvWFParams.extend, NondetElim.prefixesReserved],
        String.HasGenPrefix.bare_isPrefixOf
          (StringGenState.gen_hasGenPrefix NondetElim.prefixIte state)⟩
    · exact ⟨NondetElim.prefixLoop, by
        simp [InitEnvWFParams.extend, NondetElim.prefixesReserved],
        String.HasGenPrefix.bare_isPrefixOf
          (StringGenState.gen_hasGenPrefix NondetElim.prefixLoop state)⟩
  have hleaf : NdLeaf StringGenState.emp ρ₀ ρ₀ :=
    ⟨Env.ExtendsWith.refl _ _, hsrc,
      fun s hs _ => hsrc (HasIdent.ident (P := P) s) ⟨s, hs, rfl⟩,
      fun x v hx hv => by rw [hsrc x hx] at hv; cases hv⟩
  obtain ⟨σe, hsim₀⟩ : ∃ σe, NdSim none σe (.stmts ss ρ₀) (.stmts (Block.nondetElim ss) ρ₀) :=
    ⟨_, NdSim.stmts_none StringGenState.wf_emp hleaf hng hread⟩
  have hvar : WellFormedSemanticEvalVar (Config.stmts ss ρ₀).getEnv.factory := hwf.var
  have hmono : WellFormedSemanticEvalMono (Config.stmts ss ρ₀).getEnv.factory := hwf.mono
  have hcongr : WellFormedSemanticEvalExprCongr (Config.stmts ss ρ₀).getEnv.factory :=
    hwf.exprCongr
  have hstoreWF : Config.storeWellDefined (Config.stmts ss ρ₀) := hwf.storeWellDefined
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg trace hrun
    obtain ⟨ct', tr', hrun', htr, _⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    exact ⟨ct', tr', hrun', htr⟩
  · intro ρ' trace hrun
    obtain ⟨ct', tr', hrun', htr, hsim⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    cases hsim with
    | terminal hl => exact ⟨_, tr', hrun', hl.ext, htr⟩
  · intro lbl ρ' trace hrun
    obtain ⟨ct', tr', hrun', htr, hsim⟩ := hsim₀.trace hcongr hstoreWF
      hstoreWF hwf.val hwf.val hvar hmono hrun
    cases hsim with
    | exiting hl => exact ⟨_, tr', hrun', hl.ext, htr⟩
  · change BlockInitEnvWF params (Block.nondetElim ss) ρ₀
    have hinits := Block.nondetElim_initsUndefinedAndInhabited ss ρ₀
      (fun ident hident =>
        Option.isNone_iff_eq_none.mp (hwf.defsUndefined ident hident))
      hsrc hwf.initTypesInhabited
    have hdu := Block.nondetElim_defUseWellFormed ss
      (fun ident => (ρ₀.store ident).isSome)
      params.declaredFuncs params.declaredFuncs
      (fun name hname => by rw [hsrc _ ⟨name, hname, rfl⟩]; rfl)
      (fun _ h => h) hwf.defUseOk hng
    exact
      { toWellFormedSemanticEval := hwf.toWellFormedSemanticEval
        storeWellDefined := hwf.storeWellDefined
        readWritesDefined := fun _ htouched hnotDefined =>
          Block.defined_of_mem_touchedVars (fun _ _ h => h) hdu
            htouched hnotDefined
        defsUndefined := fun ident hident =>
          Option.isNone_iff_eq_none.mpr (hinits.1 ident hident)
        definedVarsNotReserved := by
          intro ident hident name heq pfx hpfx
          rcases Block.nondetElimM_initVars_classified
              ss StringGenState.emp ident hident with
            hsource | ⟨generated, hgeneratedIdent, hgenerated⟩
          · exact hwf.definedVarsNotReserved ident hsource name heq pfx
              (by simp [InitEnvWFParams.extend, hpfx])
          · have hnames : generated = name :=
              LawfulHasIdent.ident_inj (hgeneratedIdent.symm.trans heq)
            simpa [hnames] using hprefixes pfx hpfx generated hgenerated
        reservedFresh := by
          intro ident hdefined name heq pfx hpfx
          exact hwf.reservedFresh ident hdefined name heq pfx
            (by simp [InitEnvWFParams.extend, hpfx])
        defUseOk := hdu
        initTypesInhabited := hinits.2
        fvarTypesOk := by
          obtain ⟨Γ, hσ, hw⟩ := hwf.fvarTypesOk
          have hout := Block.nondetElimM_fvarTypes ss StringGenState.emp Γ Γ
            (fun _ _ => rfl) (fun y hy ⟨name, hname, heq⟩ => hread name hname (heq ▸ hy))
            hw [] fun _ => trivial
          rw [List.append_nil] at hout
          exact ⟨Γ, hσ, hout⟩ }

end NondetElimOverapprox

end Imperative

end -- public section

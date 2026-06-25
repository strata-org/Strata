/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.PipelineBridge
public import Strata.DL.Imperative.StmtSemanticsProps

public section

namespace Imperative

open Imperative.Specification
open Imperative.Specification.Transform
open StructuredToUnstructuredCorrect (StepDetCFGStar)

/-! # `CanFail` preservation through the structured-to-unstructured pipeline

`CanFail L s ρ₀` says that *some* reachable configuration of `s` under language `L`
has its cumulative `hasFailure` flag set:

  `∃ cfg, (L.getEnv cfg).hasFailure = true ∧ L.star (L.stmtCfg s ρ₀) cfg`.

The reachable `cfg` may be an *intermediate* configuration — the run is not required
to have reached a terminal or exiting endpoint.  This is the one genuinely net-new
obligation a refinement that tracks "can the source fail?" would add on top of the
existing terminal/exiting `Overapproximates` story.

## What is proven here (`canFail_preserved_when_outcome`)

If the source's failing configuration lies on a run that *does* reach a terminal or
exiting endpoint, `CanFail` is preserved through `pipeline = stmtsToCFG ∘ hoist ∘
nondetElim`.  The proof is a real composition:

  1. *Source monotonicity* (`StepStmtStar_hasFailure_monotone`) lifts the
     intermediate `hasFailure = true` to the endpoint's flag, since the source
     step semantics only ever OR-s failure in and never clears it.
  2. The dual `pipeline_sound` transports that endpoint to a matching CFG endpoint
     (terminal or exiting) carrying the *same* failure flag.  Either output disjunct
     suffices: both yield a reachable CFG configuration with `getFailure = true`, so
     no target-IR determinism principle is needed to select the disjunct.

## What is NOT proven (and why) — the diverging-run obstruction

The *unconditional* statement `CanFail (source) → CanFail (target)` is **not** a
corollary of the pipeline's correctness theorems.  Those theorems are forward
simulations keyed on a terminal or exiting *endpoint*: each `_sound_kind` /
`_sound_kind_exit` lemma consumes a source run reaching `.terminal ρ'` / `.exiting
lbl ρ'` and produces the matching CFG endpoint.  None of them says anything about an
intermediate configuration that a non-terminating run passes through.

A failing configuration need not lie on such a run.  Consider `assert false`
followed by a non-terminating loop, or any failing configuration that then gets
stuck on a guard that does not evaluate to a boolean.  The source records the
failure, but the run never reaches `.terminal`/`.exiting`, so there is no endpoint to
feed the simulation lemmas.  Discharging the `h_outcome` hypothesis below
unconditionally would amount to a source-side progress/termination principle, which
this development does not carry (partial-correctness only).

Closing the unconditional statement would therefore require a *new* per-pass
forward simulation that maps an arbitrary intermediate (possibly non-terminal)
failing source configuration to a reachable failing CFG configuration — strictly
more than the endpoint lemmas supply.  The conditional theorem captures exactly the
fragment the existing machinery proves. -/

/-! ## CFG-side `hasFailure` monotonicity

`updateFailure` only ever OR-s the failure flag in, so the projected `getFailure` of
a `CFGConfig` is monotone along any `StepCFG` run.  (Stated fully generically.) -/

/-- A single `StepCFG` step preserves a set failure flag. -/
theorem stepCFG_getFailure_monotone {P : PureExpr} {l CmdT : Type} [BEq l]
    {EvalCmd : EvalCmdParam P CmdT} {extendEval : ExtendEval P}
    [HasNot P] [HasVarsPure P P.Expr]
    {cfg : CFG l (DetBlock l CmdT P)} {c c' : CFGConfig l CmdT P}
    (hstep : StepCFG P EvalCmd extendEval cfg c c')
    (hf : c.getFailure = true) : c'.getFailure = true := by
  cases hstep with
  | fetch _ => simpa [CFGConfig.getFailure] using hf
  | step_cmd _ => simp [CFGConfig.getFailure]; left; simpa [CFGConfig.getFailure] using hf
  | goto_true _ _ _ => simpa [CFGConfig.getFailure] using hf
  | goto_false _ _ _ => simpa [CFGConfig.getFailure] using hf
  | finish => simpa [CFGConfig.getFailure] using hf
  | exitTo => simpa [CFGConfig.getFailure] using hf

/-- A `StepCFGStar` run preserves a set failure flag. -/
theorem stepCFGStar_getFailure_monotone {P : PureExpr} {l CmdT : Type} [BEq l]
    {EvalCmd : EvalCmdParam P CmdT} {extendEval : ExtendEval P}
    [HasNot P] [HasVarsPure P P.Expr]
    {cfg : CFG l (DetBlock l CmdT P)} {c c' : CFGConfig l CmdT P}
    (hstar : StepCFGStar P EvalCmd extendEval cfg c c')
    (hf : c.getFailure = true) : c'.getFailure = true := by
  induction hstar with
  | refl => exact hf
  | step _ _ _ hstep _ ih => exact ih (stepCFG_getFailure_monotone hstep hf)

variable {P : PureExpr} [HasFvar P] [HasNot P] [HasVal P] [HasBoolVal P]
  [HasIdent P] [HasIntOrder P] [HasVarsPure P P.Expr] [DecidableEq P.Ident] [LawfulHasFvar P]
  [LawfulHasBool P] [LawfulHasIdent P] [LawfulHasIntOrder P] [LawfulHasNot P]
  [HasSubstFvar P] [LawfulHasSubstFvar P]

/-- **Endpoint core.** Given a failing source configuration `c` that is reachable
from `.stmts ss ρ₀`, together with an endpoint witness (the continuation from `c`
reaches `.terminal ρ'` or `.exiting lbl ρ'`), produce a reachable *failing* CFG
configuration of `pipeline ss`.

Source monotonicity carries `c`'s failure to the endpoint `ρ'`; the dual
`pipeline_sound` then transports that endpoint to a matching CFG endpoint with the
same failure flag.  Either output disjunct of `pipeline_sound` works — both expose a
configuration whose `getFailure` is `ρ'.hasFailure = true`. -/
theorem canFail_target_of_source_endpoint
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ ρ' : Env P) (c : Config P (Cmd P))
    (hpre : PipelinePre extendEval ss ρ₀)
    (h_reach_c : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) c)
    (h_c_fail : c.getEnv.hasFailure = true)
    (h_endpoint :
      (∃ ρ'', StepStmtStar P (EvalCmd P) extendEval c (.terminal ρ'') ∧ ρ'' = ρ')
      ∨ (∃ lbl ρ'', StepStmtStar P (EvalCmd P) extendEval c (.exiting lbl ρ'') ∧ ρ'' = ρ')) :
    ∃ d : CFGConfig String (Cmd P) P,
      d.getFailure = true ∧
      StepDetCFGStar extendEval (pipeline ss)
        (.atBlock (pipeline ss).entry ρ₀.store ρ₀.hasFailure) d := by
  have h_run_disj :
      StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ')
      ∨ ∃ lbl, StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ') := by
    rcases h_endpoint with ⟨ρ'', h_to, rfl⟩ | ⟨lbl, ρ'', h_to, rfl⟩
    · exact Or.inl (ReflTrans_Transitive _ _ _ _ h_reach_c h_to)
    · exact Or.inr ⟨lbl, ReflTrans_Transitive _ _ _ _ h_reach_c h_to⟩
  have h_ρ'_fail : ρ'.hasFailure = true := by
    rcases h_endpoint with ⟨ρ'', h_to, rfl⟩ | ⟨lbl, ρ'', h_to, rfl⟩ <;>
    · have := StepStmtStar_hasFailure_monotone (P := P) (EvalCmd := EvalCmd P)
        (extendEval := extendEval) h_to h_c_fail
      simpa [Config.getEnv] using this
  rcases pipeline_sound extendEval ss ρ₀ ρ'
      hpre.hwfb hpre.hwfv hpre.hwfvar' hpre.hwfcongr' hpre.hwfsubst' hpre.hwfdef'
      hpre.h_store_inits hpre.h_store_mints_ndelim hpre.h_store_mints_hoist
      hpre.h_store_mints_s2u hpre.h_nofd hpre.h_lhni hpre.h_nml
      hpre.h_unique hpre.h_fresh hpre.h_disj hpre.h_ndelim_writes hpre.h_ndelim_exprs
      hpre.h_hoist_exprs hpre.h_disj_initVars hpre.h_disj_modVars h_run_disj with
    ⟨σ_cfg, h_run, _⟩ | ⟨lbl, σ_cfg, h_run, _⟩
  · exact ⟨.terminal σ_cfg ρ'.hasFailure, by simpa [CFGConfig.getFailure] using h_ρ'_fail, h_run⟩
  · exact ⟨.exiting lbl σ_cfg ρ'.hasFailure, by simpa [CFGConfig.getFailure] using h_ρ'_fail, h_run⟩

/-- **`CanFail` preservation (conditional on a source endpoint).** If `ss` can fail
from `ρ₀` and *every* failing reachable source configuration lies on a run that
reaches a terminal or exiting endpoint (`h_outcome`), then `pipeline ss` can fail
from `ρ₀` under the CFG language.

The `h_outcome` hypothesis is the exact fragment the pipeline's endpoint correctness
theorems can serve.  It is *not* dischargeable unconditionally: a failing
configuration on a non-terminating (or stuck) run has no endpoint, and the endpoint
simulation lemmas say nothing about such an intermediate configuration.  See the
module header for the full obstruction. -/
theorem canFail_preserved_when_outcome
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P)
    (hpre : PipelinePre extendEval ss ρ₀)
    (h_src : CanFail (Lang.imperativeBlock (EvalCmd P) extendEval (isAtAssert P)) ss ρ₀)
    (h_outcome : ∀ c : Config P (Cmd P),
      StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) c →
      c.getEnv.hasFailure = true →
      (∃ ρ', StepStmtStar P (EvalCmd P) extendEval c (.terminal ρ'))
      ∨ (∃ lbl ρ', StepStmtStar P (EvalCmd P) extendEval c (.exiting lbl ρ'))) :
    CanFail (Lang.cfg extendEval) (pipeline ss) ρ₀ := by
  obtain ⟨c, h_c_fail, h_reach_c⟩ := h_src
  rcases h_outcome c h_reach_c h_c_fail with ⟨ρ', h_to_term⟩ | ⟨lbl, ρ', h_to_exit⟩
  · obtain ⟨d, hd_fail, hd_run⟩ :=
      canFail_target_of_source_endpoint extendEval ss ρ₀ ρ' c hpre h_reach_c h_c_fail
        (Or.inl ⟨ρ', h_to_term, rfl⟩)
    exact ⟨(⟨"", []⟩, d), by simpa [Lang.cfg, CFGConfig.getFailure] using hd_fail,
      by simpa [Lang.cfg] using hd_run⟩
  · obtain ⟨d, hd_fail, hd_run⟩ :=
      canFail_target_of_source_endpoint extendEval ss ρ₀ ρ' c hpre h_reach_c h_c_fail
        (Or.inr ⟨lbl, ρ', h_to_exit, rfl⟩)
    exact ⟨(⟨"", []⟩, d), by simpa [Lang.cfg, CFGConfig.getFailure] using hd_fail,
      by simpa [Lang.cfg] using hd_run⟩

/-! ## Unconditional `CanFail` preservation (modulo the structured-pass bridge)

The conditional theorem above needs `h_outcome`: every failing source config must
lie on a run reaching a terminal/exiting endpoint.  That hypothesis is the price
of the *endpoint*-keyed pipeline simulations.  The S2U failing-config sibling
(`stmtsToBlocks_simulation_to_fail`) removes the endpoint demand for the final
pass; combined into `pipeline_to_fail`, the only remaining gap is the
structured-pass failing-config bridge (`StructuredPassFailingBridge`).  Taking
that bridge as a hypothesis, `CanFail` is preserved with NO `h_outcome` — the
failing run may diverge or get stuck after the failure. -/

/-- **Unconditional `CanFail` preservation (modulo the structured-pass bridge).**
If `ss` can fail from a clean initial environment `ρ₀` (`ρ₀.hasFailure = false`),
then — given the structured-pass failing-config bridge — `pipeline ss` can fail
from `ρ₀` under the CFG language.  No source endpoint hypothesis: this is the
unconditional statement, with the structured-pass bridge as its sole remaining
obligation.

The proof runs `pipeline_to_fail` at `σ_ext := ρ₀.store` (the identity
overapproximation: `StoreAgreement` is reflexive and the `σ_ext`-freshness side
conditions are the `ρ₀`-store freshness facts already bundled in
`PipelinePre`). -/
theorem canFail_pipeline
    (extendEval : ExtendEval P)
    (ss : List (Stmt P (Cmd P))) (ρ₀ : Env P)
    (hpre : PipelinePre extendEval ss ρ₀)
    (h_ρ₀_nofail : ρ₀.hasFailure = false)
    (h_bridge : StructuredPassFailingBridge extendEval ss ρ₀)
    (h_src : CanFail (Lang.imperativeBlock (EvalCmd P) extendEval (isAtAssert P)) ss ρ₀) :
    CanFail (Lang.cfg extendEval) (pipeline ss) ρ₀ := by
  obtain ⟨c, h_c_fail, h_reach_c⟩ := h_src
  obtain ⟨d, hd_run, hd_fail⟩ :=
    pipeline_to_fail extendEval ss ρ₀ c ρ₀.store h_ρ₀_nofail
      hpre.hwfb hpre.hwfv hpre.hwfvar' hpre.hwfcongr' hpre.hwfsubst' hpre.hwfdef'
      hpre.h_store_inits hpre.h_store_mints_ndelim hpre.h_store_mints_hoist
      (StoreAgreement.refl _) hpre.h_store_inits
      hpre.h_store_mints_ndelim hpre.h_store_mints_hoist hpre.h_store_mints_s2u
      hpre.h_nofd hpre.h_lhni hpre.h_nml hpre.h_unique hpre.h_fresh hpre.h_disj
      hpre.h_ndelim_writes hpre.h_ndelim_exprs hpre.h_hoist_exprs
      hpre.h_disj_initVars hpre.h_disj_modVars h_bridge
      (by simpa [Lang.imperativeBlock] using h_reach_c)
      (by simpa [Lang.imperativeBlock] using h_c_fail)
  -- `pipeline_to_fail` starts the CFG at `.atBlock _ ρ₀.store ρ₀.hasFailure`,
  -- which is exactly `Lang.cfg.stmtCfg (pipeline ss) ρ₀`.
  exact ⟨(⟨"", []⟩, d), by simpa [Lang.cfg, CFGConfig.getFailure] using hd_fail,
    by simpa [Lang.cfg] using hd_run⟩

/-! ## Phase 4 — the up-to-relation overapproximation instance

`pipeline_overapproximates_upto` packages the pipeline's correctness as a single
`OverapproximatesUptoWhen` instance, relating source and target *whole
environments* by `PipelineEnvRel` (env-lifted store agreement, source on the
left, with matching failure flag and evaluator).

### The single-relation tension, and how `pre` resolves it

`OverapproximatesUptoWhen` uses *one* relation `R` for both the input (as a
hypothesis: `R ρ₀ ρ₀'`) and the output (under an existential: `R ρ' ρ''`).  These
pull in opposite directions for a variable-*introducing* pipeline:

* the **output** `R ρ' ρ''` must *allow extra variables* — the CFG terminal store
  `σ_cfg` binds the pipeline-minted names that the source store `ρ'.store` never
  defines — so `R` can be no stronger than `StoreAgreement` (source on the left);
* but the target-side compositional theorems run from `ρ₀'` and need, on
  `ρ₀'.store`, that the source `initVars` and the three minted kinds are
  *undefined* — a *freshness* fact that `StoreAgreement ρ₀.store ρ₀'.store` (which
  constrains only the variables `ρ₀.store` *defines*) cannot supply.

A single `R` strong enough for the input freshness would forbid exactly the extra
output variables the pipeline produces.  So the input freshness on `ρ₀'` cannot
come from `R`; it is instead supplied — together with the structured-pass failing
bridge — through the statement-only `pre`, which asserts `PipelinePre` (whose
store-freshness fields pin `ρ₀'.store`) at every clean candidate initial env.
`R` is then free to be the natural output-side `StoreAgreement`.

### Conjuncts

* **terminal/exiting** — from `pipeline_sound_terminal_compositional` /
  `pipeline_sound_exiting_compositional`, run from `ρ₀'`, with the `ρ₀'`-store
  freshness drawn from the `pre`-supplied `PipelinePre ρ₀'`.
* **CanFail** — from `canFail_pipeline` (modulo the structured-pass bridge),
  run from `ρ₀'` (or, when `ρ₀'` already fails, witnessed by the failing start
  config directly).
* **target `initEnvWF`** — trivial, since `Lang.cfg.initEnvWF = fun _ _ _ => True`.
-/

/-- The environment relation `pipeline_overapproximates_upto` runs at:
env-lifted store agreement (source on the left, the natural output-side relation
that *allows the extra variables* the pipeline introduces) with matching failure
flag and evaluator.  Reflexive, so the diagonal `ρ₀ = ρ₀'` is included and the
instance specialises to identity-input pipeline soundness. -/
@[expose] def PipelineEnvRel (ρ₀ ρ₀' : Env P) : Prop :=
  StoreAgreement ρ₀.store ρ₀'.store
  ∧ ρ₀.hasFailure = ρ₀'.hasFailure
  ∧ ρ₀'.eval = ρ₀.eval

theorem PipelineEnvRel.refl (ρ₀ : Env P) : PipelineEnvRel ρ₀ ρ₀ :=
  ⟨StoreAgreement.refl _, rfl, rfl⟩

/-- **Phase 4: pipeline overapproximation up to `PipelineEnvRel` (modulo the
structured-pass failing bridge).**  `fun ss => some (pipeline ss)` overapproximates
the source statement-list language by the unstructured CFG language *up to*
`PipelineEnvRel`.

Because the single relation `R` cannot simultaneously carry the input freshness
and permit the output's extra variables (see the section header), the per-`ρ₀'`
`PipelinePre` — and the structured-pass failing bridge — are threaded through the
statement-only `pre`, instantiated at the actual `R`-related target env.
Everything else (the terminal/exiting compositional simulations and the `CanFail`
assembly) is fully proven; the bridge is the only standing obligation. -/
theorem pipeline_overapproximates_upto (extendEval : ExtendEval P) :
    Specification.Transform.OverapproximatesUptoWhen
      (PipelineEnvRel (P := P))
      (Lang.imperativeBlockSrc extendEval)
      (Lang.cfg extendEval)
      (fun ss => some (pipeline ss))
      (fun ss => ∀ ρ : Env P, PipelinePre extendEval ss ρ ∧
        (ρ.hasFailure = false → StructuredPassFailingBridge extendEval ss ρ))
      () () := by
  intro ss cfg ht hpre_all ρ₀ ρ₀' hR _hwf
  simp only [Option.some.injEq] at ht
  subst ht
  obtain ⟨hR_agree, hR_hf, hR_eval⟩ := hR
  -- `pre` supplies `PipelinePre` (hence the store-freshness) at the target env ρ₀'.
  have hpre' : PipelinePre extendEval ss ρ₀' := (hpre_all ρ₀').1
  -- σ_ext-freshness on ρ₀'.store, directly from `PipelinePre ρ₀'`.
  have h_inits_ext : ∀ x ∈ Block.initVars ss, ρ₀'.store x = none := hpre'.h_store_inits
  have h_ndelim_ext : ∀ s : String, ndelimKind s →
      ρ₀'.store (HasIdent.ident (P := P) s) = none := hpre'.h_store_mints_ndelim
  have h_hoist_ext : ∀ s : String, hoistKind s →
      ρ₀'.store (HasIdent.ident (P := P) s) = none := hpre'.h_store_mints_hoist
  have h_s2u_ext : ∀ s : String, StructuredToUnstructuredCorrect.s2uKind s →
      ρ₀'.store (HasIdent.ident (P := P) s) = none := hpre'.h_store_mints_s2u
  -- The structured passes run from ρ₀; use the source-side preconditions for ρ₀.
  have hpre : PipelinePre extendEval ss ρ₀ := (hpre_all ρ₀).1
  refine ⟨fun ρ' => ⟨fun hstar => ?_, fun lbl hstar => ?_⟩, ?_, ?_⟩
  · -- ===== TERMINAL ARM =====
    have h_term : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.terminal ρ') := by
      simpa [Lang.imperativeBlockSrc, Lang.imperativeBlock] using hstar
    obtain ⟨σ_cfg, h_run, h_agree⟩ :=
      pipeline_sound_terminal_compositional extendEval ss ρ₀ ρ' ρ₀'.store
        hpre.hwfb hpre.hwfv hpre.hwfvar' hpre.hwfcongr' hpre.hwfsubst' hpre.hwfdef'
        hpre.h_store_inits hpre.h_store_mints_ndelim hpre.h_store_mints_hoist
        hR_agree h_inits_ext h_ndelim_ext h_hoist_ext h_s2u_ext
        hpre.h_nofd hpre.h_lhni hpre.h_nml hpre.h_unique hpre.h_fresh hpre.h_disj
        hpre.h_ndelim_writes hpre.h_ndelim_exprs hpre.h_hoist_exprs
        hpre.h_disj_initVars hpre.h_disj_modVars h_term
    refine ⟨{ store := σ_cfg, eval := ρ'.eval, hasFailure := ρ'.hasFailure }, ?_, ?_⟩
    · exact ⟨h_agree, rfl, rfl⟩
    · -- target run: Lang.cfg.star (stmtCfg (pipeline ss) ρ₀') (terminalCfg ρ_t)
      simp only [Lang.cfg]
      rw [← hR_hf]
      exact h_run
  · -- ===== EXITING ARM =====
    have h_exit : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) (.exiting lbl ρ') := by
      simpa [Lang.imperativeBlockSrc, Lang.imperativeBlock] using hstar
    obtain ⟨σ_cfg, h_run, h_agree⟩ :=
      pipeline_sound_exiting_compositional extendEval ss ρ₀ ρ' ρ₀'.store
        hpre.hwfb hpre.hwfv hpre.hwfvar' hpre.hwfcongr' hpre.hwfsubst' hpre.hwfdef'
        hpre.h_store_inits hpre.h_store_mints_ndelim hpre.h_store_mints_hoist
        hR_agree h_inits_ext h_ndelim_ext h_hoist_ext h_s2u_ext
        hpre.h_nofd hpre.h_lhni hpre.h_nml hpre.h_unique hpre.h_fresh hpre.h_disj
        hpre.h_ndelim_writes hpre.h_ndelim_exprs hpre.h_hoist_exprs
        hpre.h_disj_initVars hpre.h_disj_modVars lbl h_exit
    refine ⟨{ store := σ_cfg, eval := ρ'.eval, hasFailure := ρ'.hasFailure }, ?_, ?_⟩
    · exact ⟨h_agree, rfl, rfl⟩
    · simp only [Lang.cfg]
      rw [← hR_hf]
      exact h_run
  · -- ===== CanFail ARM (CanFail L₁ ss ρ₀ → CanFail L₂ (pipeline ss) ρ₀') =====
    -- Source failing run is from ρ₀; target must fail from ρ₀'.  This is exactly
    -- the `pipeline_to_fail` shape (structured passes from ρ₀, S2U from
    -- σ_ext := ρ₀'.store), with the structured-pass bridge taken at ρ₀.
    intro h_src
    by_cases h_ρ₀_fail : ρ₀.hasFailure = true
    · -- ρ₀ already failing ⟹ (hf-eq) ρ₀' failing: the CFG start config from
      -- ρ₀'.store is itself failing, reachable by the reflexive run.
      have h_ρ₀'_fail : ρ₀'.hasFailure = true := hR_hf ▸ h_ρ₀_fail
      refine ⟨(⟨"", []⟩, .atBlock (pipeline ss).entry ρ₀'.store ρ₀'.hasFailure),
        by simpa [Lang.cfg, CFGConfig.getFailure] using h_ρ₀'_fail, ?_⟩
      simp only [Lang.cfg]
      exact ReflTrans.refl _
    · -- ρ₀ clean: bridge at ρ₀ from `pre`, run `pipeline_to_fail` from ρ₀ with
      -- σ_ext := ρ₀'.store.
      have h_ρ₀_nofail : ρ₀.hasFailure = false := by simpa using h_ρ₀_fail
      have h_bridge : StructuredPassFailingBridge extendEval ss ρ₀ :=
        (hpre_all ρ₀).2 h_ρ₀_nofail
      -- Source failing config + run from ρ₀ (`CanFail` reads star/getEnv/stmtCfg,
      -- shared by `imperativeBlockSrc`).
      obtain ⟨cfg_s, h_cfg_fail, h_cfg_reach⟩ := h_src
      have h_reach : StepStmtStar P (EvalCmd P) extendEval (.stmts ss ρ₀) cfg_s := by
        simpa [Lang.imperativeBlockSrc, Lang.imperativeBlock] using h_cfg_reach
      have h_fail : cfg_s.getEnv.hasFailure = true := by
        simpa [Lang.imperativeBlockSrc, Lang.imperativeBlock] using h_cfg_fail
      obtain ⟨d, hd_run, hd_fail⟩ :=
        pipeline_to_fail extendEval ss ρ₀ cfg_s ρ₀'.store h_ρ₀_nofail
          hpre.hwfb hpre.hwfv hpre.hwfvar' hpre.hwfcongr' hpre.hwfsubst' hpre.hwfdef'
          hpre.h_store_inits hpre.h_store_mints_ndelim hpre.h_store_mints_hoist
          hR_agree h_inits_ext h_ndelim_ext h_hoist_ext h_s2u_ext
          hpre.h_nofd hpre.h_lhni hpre.h_nml hpre.h_unique hpre.h_fresh hpre.h_disj
          hpre.h_ndelim_writes hpre.h_ndelim_exprs hpre.h_hoist_exprs
          hpre.h_disj_initVars hpre.h_disj_modVars h_bridge h_reach h_fail
      -- `pipeline_to_fail` starts at `.atBlock _ ρ₀'.store ρ₀.hasFailure`; the CFG
      -- language's `stmtCfg (pipeline ss) ρ₀'` starts at `ρ₀'.hasFailure`.  Match
      -- the start flag via the relation's `ρ₀.hasFailure = ρ₀'.hasFailure`.
      rw [hR_hf] at hd_run
      exact ⟨(⟨"", []⟩, d), by simpa [Lang.cfg, CFGConfig.getFailure] using hd_fail,
        by simpa [Lang.cfg] using hd_run⟩
  · -- ===== target initEnvWF conjunct: `Lang.cfg.initEnvWF = fun _ _ _ => True` =====
    trivial


end Imperative

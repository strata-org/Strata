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

end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCFGComplete
public import Strata.DL.Imperative.InterpreterCFGCallSound
public import Strata.DL.Imperative.InterpreterCallComplete
import all Strata.DL.Imperative.InterpreterCFG
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterCall

/-! # Call-aware completeness of the monadic CFG interpreter

Instantiates the monad-generic CFG completeness (`runInterpCFG_completeE`,
`InterpreterCFGComplete.lean`) with the call-aware store-stepper `cfgStepCmd π`,
discharging its per-command obligation `hCmdC` from the structured call-aware command
completeness (`InterpreterCallComplete.lean`: the command stepper reproduces every
engine-realizable command step `EvalCommandEngAtE π R n`).  The guard steps of the
engine-realizable CFG relation `StepCFGEngE` carry the engine's guard evaluation.

The reference derivation is the *engine-realizable* CFG event closure — the
command relation `EvalCommandEngAtE π R n` records each nondeterministic choice in
the choice record `R`, exactly the "with the choices recorded" sense of
completeness.  Relating a plain `StepCFGExtStarE` derivation to the engine is a
separate realizability argument about the derivation's choices, not about CFG control
flow, so this module does not make it.

Key theorem: `runInterpCFG_callCompleteE`. -/

namespace Imperative

namespace Calls

public section

variable {P : PureExpr} {l : Type} [BEq l]
variable [HasBoolOps P] [HasFvar P] [HasFvars P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CallLangWF P] [HasOldIdent P]
variable {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

omit [CallLangWF P] in
/-- **Call-aware completeness of the monadic CFG interpreter.**  Every derivation of the
    engine-realizable CFG semantics `StepCFGEngStarE (EvalCommandEngAtE π R n)` (commands follow
    the engine-realizable command relation, which reads every nondeterministic choice off the
    choice record `R` and nests calls at most `n` deep) from the semantic image under the factory
    `F` (`ICFGConfig.abs`) of a configuration `start` that denotes at `F` and that ends in a
    terminal config is reproduced by a `runInterpCFG (cfgStepCmd π)` run from `start` at every
    sufficiently large fuel, reaching a configuration that denotes the derivation's end and
    emitting runtime events whose semantic images are exactly its events.  It assumes that the
    observation emits every event and resolves every choice recorded in `R`, and that the bounded
    evaluator is fuel-monotone. -/
theorem runInterpCFG_callCompleteE
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (F : P.Factory) (R : ChoiceRecord P) (n : Nat) (cfgr : obs.Cfg)
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (start : ICFGConfig l (CmdExt P) P) (final : CFGConfig l (CmdExt P) P)
    (evs : List (Event P)) (hden : start.Denoting F)
    (hstar : StepCFGEngStarE P (EvalCommandEngAtE π R n) (start.abs F) evs final)
    (hdone : final.Done) (st : obs.St) :
    ∃ f0 st', ∃ final' : ICFGConfig l (CmdExt P) P, final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runInterpCFG (cfgStepCmd π d) fuel start) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  (runInterpCFG_follows_fam obs cfgr F (fun _ _ => True) (Q := fun _ => True)
    (E := fun f σ c σ' evs _ _ => EvalCommandEngAtE π R n f σ c σ' evs)
    (fun d _ => cfgStepCmd π d)
    (fun σ c σ' emitted _ _ hσ hstep _ st _ =>
      (cfg_stepCmd_store_complete _ π n hemit hchoose hMono σ c σ' emitted st hσ
        hstep).imp fun _ ⟨σi, st', hσi, hdi, h, ht⟩ =>
          ⟨st', σi, hσi, hdi, fun d _ k hd _ hk => h k d hk hd, trivial, ht⟩)
    hMono (y := (final, [])) hden
    (stepCFGEngStarE_toOracle (o := []) hstar) hdone (fun _ _ => trivial) st trivial).imp
    fun _ ⟨st', final', hf, h, _, ht⟩ => ⟨st', final', hf, fun fuel d hf hd => h d _ fuel hd
      (Nat.le_refl _) hf, ht⟩

end -- public section

end Calls

end Imperative

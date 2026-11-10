/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CallAwareSemantics
public import Strata.DL.Imperative.InterpreterCFGSound
public import Strata.DL.Imperative.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterCall
public import Strata.DL.Imperative.CFGSemanticsProps
import all Strata.DL.Imperative.InterpreterCFG

/-! # Call-aware soundness of the monadic CFG interpreter

Instantiates the monad-generic CFG soundness (`runInterpCFG_soundE`,
`InterpreterCFGSound.lean`) with the call-aware command stepper, discharging its
two hypotheses from the structured call-aware machinery:

* the per-command correspondence `hCmd` from the structured call-aware command
  soundness (`InterpreterCallSound.lean`: the executable command stepper
  `Calls.stepCmd π` realizes the reference relation `Calls.EvalCommandET π`); and
* the configuration-invariant preservation `hPres` from the structured facts that a
  command step keeps the store well-formed and typed, lifted to the CFG config
  invariant `CFGCfgInv`.

Key theorem: `runInterpCFG_callSoundE`, relating a successful
`runInterpCFG (cfgStepCmd π)` observation to `StepCFGExtStarE π`, emitting
exactly the run's recorded events. -/

namespace Imperative

namespace Calls

public section

variable {P : PureExpr} {l : Type} [BEq l]
variable [ihbo : HasBoolOps P] [ihf : HasFvar P]
    [ihfs : HasFvars P] [ide : DecidableEq P.Expr] [idi : DecidableEq P.Ident]
    [iil : InterpLang P] [iclwf : CallLangWF P] [ioi : HasOldIdent P]
variable {Hdr : Type} [idh : DecidableEq Hdr] [iih : Inhabited Hdr] [iph : ProcedureHeader P Hdr]
variable {m : Type → Type} [imo : Monad m] [ime : InterpEffects P m]
    [imx : MonadExcept StopReason m]

/-- The call-aware store-stepper for the CFG driver at call-depth budget `d`: run one
    `CmdExt P` to completion with the structured call stepper `Calls.stepCmd π d` (a `.call`
    runs its callee body inside), then project the resulting store. -/
@[expose] def cfgStepCmd (π : String → Option (Procedure P (CmdExt P) Hdr)) (d : Nat) :
    StepCmdStoreM P (CmdExt P) m :=
  StepCmdM.toStore (stepCmd π d)

include iclwf in
/-- At a well-formed factory `F` (`FactoryWF`), from an in-block configuration whose running
    store denotes at `F`, whose environment factory is the runtime image of `F`, and whose
    semantic image satisfies the CFG invariant `CFGCfgInv` at `F` (well-formed and typed running
    store, well-formed call sites, environment factory `F`), a successful run of the call-aware
    store-stepper `cfgStepCmd π` on the next command is a step of the typed call-aware command
    relation `EvalCommandET π` between the semantic images of the stores, emitting the semantic
    images of exactly the events the run recorded, and its result store denotes at `F`. -/
private theorem cfgStepCmd_hCmd [InterpLangBool P]
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (F : P.Factory)
    (hprocs : ProcsOk π) (hfac : FactoryWF (P := P) F) (hEval : BoundedEvalSoundAt P F) (d : Nat) :
    ∀ fuel (g : CFG l (DetBlock l (CmdExt P) P)) t c cs tr (ρ : IEnv P) σ' cfgr st st',
      RStore.Denoting F ρ.store.get → ρ.factory = InterpLang.rfactory F →
      CFGCfgInv π F (.inBlock g t (c :: cs) tr (ρ.abs F)) →
      obs.run (cfgStepCmd π d fuel ρ.factory ρ.store c) cfgr st = (.ok σ', st') →
      ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
        ∧ EvalCommandET π F (InterpLang.absStore F ρ.store.get) c (InterpLang.absStore F σ'.get)
          (revs.map (REvent.abs F))
        ∧ RStore.Denoting F σ'.get := by
  intro _ _ _ _ _ _ _ _ _ _ _ hd hfF hinv hrun
  obtain ⟨hpre, hres, -, -⟩ := hinv
  rw [hfF] at hrun
  exact (cfg_stepCmd_store_sound _ _ hprocs hEval hfac (hres _ (.head _)) hd hpre hrun).imp
    fun _ ⟨hev, _, hd', htr⟩ => ⟨htr, hev, hd'⟩

include iclwf in
/-- **Call-aware soundness of the monadic CFG interpreter.**  A successful observation of
    `runInterpCFG (cfgStepCmd π)` from a config `start` that denotes at a factory `F`
    (`ICFGConfig.Denoting`) and whose semantic image (`ICFGConfig.abs`) satisfies the CFG
    invariant `CFGCfgInv` at `F` (well-formed and typed running store, well-formed call sites,
    environment factory `F`) to `final` is a derivation from the semantic image of `start` to
    that of `final` of the call-aware CFG reference semantics `StepCFGExtStarE π`, emitting the
    semantic images of exactly the run's recorded events; and `final` denotes at `F`.  It
    assumes that every procedure of `π` passes the local well-formedness check `ProcsOk`, that
    the factory is well-formed (`FactoryWF`), that the boolean constants denote
    (`InterpLangBool`), and that at `F` every value the bounded evaluator commits to denotes the
    reference value (`BoundedEvalSoundAt`). -/
theorem runInterpCFG_callSoundE [InterpLangBool P]
    (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (F : P.Factory)
    (hprocs : ProcsOk π)
    (hfac : FactoryWF (P := P) F)
    (hEval : BoundedEvalSoundAt P F)
    (fuel d : Nat) (start final : ICFGConfig l (CmdExt P) P) (cfgr : obs.Cfg)
    (st st' : obs.St)
    (hden : start.Denoting F)
    (hInv : CFGCfgInv π F (start.abs F))
    (hrun : obs.run (runInterpCFG (cfgStepCmd π d) fuel start) cfgr st = (.ok final, st')) :
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGExtStarE π (start.abs F) (revs.map (REvent.abs F)) (final.abs F)
      ∧ final.Denoting F :=
  (runInterpCFG_soundE _ _ _ _ F (cfgStepCmd_hCmd _ _ F hprocs hfac hEval d)
      (fun _ _ _ => cfgCfgInv_stepE _ _) hEval _ _ _ _ _ _ hden hInv hrun).imp
    fun _ => .imp_right (.imp_left (·.imp fun _ _ _ => .imp fun _ _ _ _ _ => And.left))

end -- public section

end Calls

end Imperative

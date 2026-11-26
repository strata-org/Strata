/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCallInterrupt
public import Strata.DL.Imperative.InterpreterSoundGeneric
public import Strata.DL.Imperative.InterpreterSound
public import Strata.DL.Imperative.StmtSemanticsProps
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.InterpreterReplayProps
public import Strata.DL.Imperative.InterpreterCallProps
public import Strata.DL.Imperative.InterpreterSemanticsSpecProps
public import Strata.DL.Imperative.InterpreterCFGSound
public import Strata.DL.Imperative.StmtCFGCallSemanticsProps
import Strata.DL.Imperative.CFGSemanticsProps
import all Strata.DL.Imperative.InterpreterCFG


/-! # Soundness of the call-aware stepper over any command type

`Calls.stepCmdWith view around π` steps the commands of any type `CmdT`, with `view` telling it
what each command is. This module proves its successful steps and runs sound against
`EvalCmdViewE S π` and `BigStepViewE S π` (`StmtCFGCallSemantics.lean`) for a command semantics
`S`. It assumes that `view` agrees with `S` and that each extension command runs as `S.ExtE`
relates it (`Calls.ViewSound`), that the wrapper `around` keeps successful steps
(`Calls.AroundOk`), that every procedure a call can run is well formed (`Calls.ProcsOkV`), and
that the stepper's call mode runs as its contract exactly the callees the reference semantics
does, the opaque ones (`Calls.ModeOk`): always under `CallMode.contract` (`Calls.modeOk_contract`),
and under `CallMode.execute` when no callee has an opaque body that is not abstract.

Key theorems: `stepCmdWith_armSound` (per command), `stepCmdWith_stepSound` (per step),
`stepCmdWith_runInterp_sound` (statement runs) and `runInterpCFG_sound_of_arm` (CFG runs).

It also holds what the proofs share with the replay soundness of `InterpreterCallSound.lean`:
the expression-language facts `CallLangWF`, the per-actual checks `StrictActual` and
`TypedActual`, the store invariant `CallEnvOk`, and the bridges from the executable call helpers
to the relations of the call rule. The `CmdExt` soundness lemmas of `InterpreterCallSound.lean`
are instances of the ones here, at `CmdExt.sem`. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

public section

namespace Calls

/-- The expression-language facts call-aware replay soundness uses (the soundness of the bounded
    evaluator at the run's factory, `BoundedEvalSoundAt`, is an explicit hypothesis of each theorem
    instead: Core's holds only at factories whose evaluators meet `Core.EvalFactoryWF`, so it
    cannot be a field of an instance).
    * the engine's executable value check implies `HasVal.value`;
    * every factory's evaluator is value-well-formed (`WellFormedSemanticEvalVal`);
    * an expression that is a bare free variable `x` has no free variable but `x`;
    * `x` is a free variable of `mkFvar x`;
    * the engine's executable type checks are sound against `HasVal.valueOfTy`
      (`ops_typed`, the content of `InterpLangTyped`);
    * `closedTyped` is a syntactic class of closed actuals whose bounded value is a
      typed value (`closedTyped_sound`).  The reference call rule binds input formals
      to argument values without a type premise, so the typed-store invariant the
      typed `set` rules need is kept across a call only for arguments that are bare
      variables (whose values come from a typed store) or `closedTyped`. -/
class CallLangWF (P : PureExpr) [HasBool P] [HasFvar P] [HasFvars P] [InterpLang P] where
  isValue_sound : ∀ (f : P.Factory) (r : P.Expr) (v : P.Val),
    (InterpLang.ops (P := P)).isValue (InterpLang.rfactory f) r = true →
      InterpLang.Denotes f r v → HasVal.value f v
  evalVal : ∀ f : P.Factory, WellFormedSemanticEvalVal (P := P) f
  getFvars_of_getFvar : ∀ (e : P.Expr) (x : P.Ident), HasFvar.getFvar (P := P) e = some x →
    ∀ y ∈ HasFvars.getFvars (P := P) e, y = x
  mem_getFvars_mkFvar : ∀ x : P.Ident, x ∈ HasFvars.getFvars (P := P) (HasFvar.mkFvar (P := P) x)
  lawfulHasVal : LawfulHasVal P
  ops_typed : (InterpLang.ops (P := P)).TypedSound InterpLang.rfactory InterpLang.denote
  closedTyped : P.Expr → Bool
  closedTyped_sound : ∀ (n : Nat) (f : P.Factory) (σ : RStore P) (e r : P.Expr),
    closedTyped e = true → InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σ e = some r →
    ∃ v ty, InterpLang.Denotes f r v ∧ HasVal.valueOfTy f v ty

instance (priority := low) {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P] [InterpLang P]
    [CallLangWF P] : InterpLangTyped P := ⟨CallLangWF.ops_typed⟩

instance (priority := low) {P : PureExpr} [HasBool P] [HasFvar P] [HasFvars P] [InterpLang P]
    [CallLangWF P] : LawfulHasVal P := CallLangWF.lawfulHasVal

section CallBase

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CallLangWF P]
  [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  [ProcedureTypeInstantiation P Hdr]

/-- Every free variable of every expression in `es` is bound in `σ`.  This is what
    `EvalExpressions` demands of each expression it evaluates and what
    `evalBoundedList` does not check. -/
@[expose] def ExprsDefined (σ : SemanticStore P) (es : List P.Expr) : Prop :=
  ∀ e ∈ es, SemanticStore.varsDefined (· ∈ HasFvars.getFvars e) σ

/-! ## The strictness check on input actuals, and `EvalExpressions` from it

`StrictActual` (a bare variable, or a closed expression) makes a successful bounded evaluation of
the actuals an `EvalExpressions` derivation, definedness included. -/

/-- The per-actual syntactic check: a bare free variable, or a closed expression.
    Anything else is rejected, because `P.eval` is not strict in general
    (`(fun _ => 3) x` evaluates with `x` unbound), so a successful evaluation would not
    witness `EvalExpressions`' definedness premise. -/
@[expose] def StrictActual (e : P.Expr) : Bool :=
  (HasFvar.getFvar (P := P) e).isSome ||
    (HasFvars.getFvars (P := P) e).isEmpty

/-- The per-actual typing check: a bare free variable, or an actual of the language's
    `CallLangWF.closedTyped` class.  Either way its value is typed when the caller's
    store is. -/
@[expose] def TypedActual (e : P.Expr) : Bool :=
  (HasFvar.getFvar (P := P) e).isSome || CallLangWF.closedTyped (P := P) e

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- A strict actual that evaluates has all its free variables bound. -/
private theorem exprDefined_of_strict {f : P.Factory} {σ : SemanticStore P}
    (hvar : WellFormedSemanticEvalVar (P := P) f)
    (hwfs : WellFormedStore σ f) {e : P.Expr} {v : P.Val}
    (hs : StrictActual e = true) (he : P.eval f σ e = some v) :
    SemanticStore.varsDefined (· ∈ HasFvars.getFvars (P := P) e) σ := by
  simp only [StrictActual, Bool.or_eq_true, List.isEmpty_iff] at hs
  grind [SemanticStore.varsDefined, WellFormedSemanticEvalVar, CallLangWF, Option.isSome_iff_exists]

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `evalBoundedList` realizes `EvalExpressions` on actuals that pass the syntactic strictness
    check. -/
private theorem evalExpressions_of_evalBoundedList_strict
    (n : Nat) (f : P.Factory) (hEval : BoundedEvalSoundAt P f) (σ : RStore P)
    (hd : RStore.Denoting f σ)
    (hvar : WellFormedSemanticEvalVar (P := P) f)
    (hwfs : WellFormedStore (InterpLang.absStore f σ) f) :
    ∀ (es rs : List P.Expr), (∀ e ∈ es, StrictActual e = true) →
      evalBoundedList n (InterpLang.rfactory f) σ es = some rs →
      ∃ vs, List.Rel₂ (InterpLang.Denotes f) rs vs ∧
        EvalExpressions f (InterpLang.absStore f σ) es vs := fun es => by
  induction es with
  | nil =>
    rintro _ _ ⟨⟩
    exact ⟨[], .nil, .eval_none⟩
  | cons e es ih =>
    intro rs hs h
    simp only [evalBoundedList] at h
    split at h
    · obtain ⟨rs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨v, hv, hdv⟩ := hEval.atAbs hd ‹_›
      obtain ⟨vs, hrel, hE⟩ := ih rs' (fun e he => hs e (.tail _ he)) h'
      exact ⟨v :: vs, .cons hdv hrel,
        .eval_some (exprDefined_of_strict hvar hwfs (hs e (.head _)) hv) hv hE⟩
    · cases h

/-! ## Definedness of the write-back targets

A successful `.call` step binds every `getLhs args` target in the caller store, as `UpdateStates`
requires. -/

omit [HasBoolOps P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [CallLangWF P] [HasOldIdent P] in
omit [InterpLang P] in
/-- Each `inoutArg` of a call occurs among its input expressions as a variable reference. -/
private theorem mem_getInputExprs_of_mem_getInoutArgs :
    ∀ (args : List (CallArg P)) (y : P.Ident),
      y ∈ CallArg.getInoutArgs args →
      (HasFvar.mkFvar y : P.Expr) ∈ getInputExprs args := by
  simp only [CallArg.getInoutArgs, List.mem_filterMap, getInputExprs, forall_exists_index,
    and_imp]
  grind

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [CallLangWF P] [HasOldIdent P] in
omit [InterpLang P] in
/-- `getLhs` is exactly the `inoutArg` names together with the `outArg` names. -/
private theorem mem_getLhs :
    ∀ (args : List (CallArg P)) (y : P.Ident),
      y ∈ CallArg.getLhs args →
      y ∈ CallArg.getInoutArgs args ∨ y ∈ CallArg.getOutArgs args := by
  simp only [CallArg.getLhs, List.mem_filterMap, CallArg.getInoutArgs, CallArg.getOutArgs,
    forall_exists_index, and_imp]
  grind

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- The write-back targets of a call whose inputs evaluate and whose `out` actuals read are
    bound. -/
private theorem getLhs_defined {f : P.Factory} {σ : SemanticStore P}
    (args : List (CallArg P)) {inputVals outOnlyVals : List P.Val}
    (hin : EvalExpressions f σ (getInputExprs args) inputVals)
    (hout : readVarList σ (CallArg.getOutArgs args) = some outOnlyVals) :
    SemanticStore.varsDefined (· ∈ CallArg.getLhs args) σ := fun y hy =>
  (mem_getLhs _ _ hy).elim
    (fun hio => evalExpressions_defined hin _ (mem_getInputExprs_of_mem_getInoutArgs _ _ hio) y
      (CallLangWF.mem_getFvars_mkFvar y))
    (readVarList_defined σ _ _ hout y)

/-! ## Store typing across a call

The callee frame is typed when the input actuals are `TypedActual` and the caller's store is typed;
the caller's store stays typed across the write-back when the callee's final store is. -/

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- A `TypedActual` evaluated in a typed, value-only store yields a typed value. -/
private theorem typed_of_typedActual
    {n : Nat} {f : P.Factory} (hEval : BoundedEvalSoundAt P f) {σ : RStore P}
    (hd : RStore.Denoting f σ)
    (hvar : WellFormedSemanticEvalVar (P := P) f)
    (hwfs : WellFormedStore (InterpLang.absStore f σ) f)
    (hty : StoreTyped f (InterpLang.absStore f σ)) {e r : P.Expr}
    (ht : TypedActual e = true)
    (he : InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σ e = some r) :
    ∃ v ty, InterpLang.Denotes f r v ∧ HasVal.valueOfTy f v ty := by
  rcases Bool.or_eq_true _ _ ▸ ht with hx | hc
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hx
    obtain ⟨v, hv, hdv⟩ := hEval.atAbs hd he
    obtain ⟨ty, hty⟩ := hty x v ((hvar e x _ hwfs hx).symm.trans hv)
    exact ⟨v, ty, hdv, hty⟩
  · exact CallLangWF.closedTyped_sound n f σ e r hc he

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- `evalBoundedList` of `TypedActual`s in a typed, value-only store yields typed values. -/
private theorem typed_of_evalBoundedList
    (n : Nat) (f : P.Factory) (hEval : BoundedEvalSoundAt P f) (σ : RStore P)
    (hd : RStore.Denoting f σ)
    (hvar : WellFormedSemanticEvalVar (P := P) f)
    (hwfs : WellFormedStore (InterpLang.absStore f σ) f)
    (hty : StoreTyped f (InterpLang.absStore f σ)) :
    ∀ (es rs : List P.Expr), (∀ e ∈ es, TypedActual e = true) →
      evalBoundedList n (InterpLang.rfactory f) σ es = some rs →
      ∃ vs, List.Rel₂ (InterpLang.Denotes f) rs vs ∧ ∀ v ∈ vs, ∃ ty, HasVal.valueOfTy f v ty :=
  fun es => by
  induction es with
  | nil =>
    rintro _ _ ⟨⟩
    exact ⟨[], .nil, nofun⟩
  | cons e es ih =>
    intro rs hs h
    simp only [evalBoundedList] at h
    split at h
    · obtain ⟨rs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨v, ty, hdv, hty⟩ :=
        typed_of_typedActual hEval hd hvar hwfs hty (hs e (.head _)) ‹_›
      obtain ⟨vs, hrel, hvs⟩ := ih rs' (fun e he => hs e (.tail _ he)) h'
      refine ⟨v :: vs, .cons hdv hrel, ?_⟩
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨ty, hty⟩, hvs⟩
    · cases h

/-! ## The call helpers over runtime stores, through the semantic image -/

omit [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- On a denoting runtime store with a typed image, a passed typed write-back check
    (`writeBackTyped`) of denoting values against the values the targets hold gives each
    written-back value the type of its target's value in the image (the typed write-back
    premise of `CallExit`). -/
private theorem storedTy_of_writeBackTyped {F : P.Factory} {σ : RStore P}
    (hd : RStore.Denoting F σ) (hty : StoreTyped F (InterpLang.absStore F σ)) :
    ∀ (xs : List P.Ident) (olds ws : List P.Expr) (vs : List P.Val),
      readVarList σ xs = some olds → xs.length = vs.length →
      List.Rel₂ (InterpLang.Denotes F) ws vs →
      writeBackTyped InterpLang.ops (InterpLang.rfactory F) olds ws = true →
      List.Rel₂ (HasVal.valueOfStoredTy (P := P) F (InterpLang.absStore F σ)) xs vs
  | [], _, _, [], _, _, _, _ => .nil
  | x :: xs, olds, _, _, hr, hl, .cons hw hrel, hwb => by
    simp only [readVarList] at hr
    split at hr
    · rename_i old hold
      obtain ⟨olds', hr', rfl⟩ := Option.map_eq_some_iff.1 hr
      simp only [writeBackTyped, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hwb
      obtain ⟨⟨hv, hs⟩, hwb⟩ := hwb
      obtain ⟨vo, hdo⟩ := hd x old hold
      have habs : InterpLang.absStore F σ x = some vo := by
        simpa [InterpLang.absStore, hold, InterpLang.Denotes] using hdo
      obtain ⟨v', hv', hst⟩ := CallLangWF.ops_typed.storedTy hty habs hdo hv hs
      cases Option.some.inj (hv'.symm.trans hw)
      exact .cons hst (storedTy_of_writeBackTyped hd hty xs olds' _ _ hr'
        (Nat.succ.inj hl) hrel hwb)
    · cases hr

/-- The store invariant a call-aware run carries, at a fixed factory: a well-formed (value-only)
    store and a typed store. -/
@[expose] def CallEnvOk (fac : P.Factory) (σ : SemanticStore P) : Prop :=
  WellFormedStore σ fac ∧ StoreTyped fac σ

omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [CallLangWF P] [HasOldIdent P] [ProcedureHeader P Hdr] [ProcedureTypeInstantiation P Hdr] in
omit [InterpLang P] in
/-- `CallEnvOk` (well-formed store, typed store) is preserved by projecting a store onto a
    parent store (`projectStore`), as at a block exit. -/
theorem callEnvOk_projectStore (fac : P.Factory) (σp σ : SemanticStore P)
    (h : CallEnvOk (P := P) fac σ) : CallEnvOk (P := P) fac (projectStore σp σ) := by
  obtain ⟨hwf, hty⟩ := h
  exact ⟨fun x v => by grind [projectStore, hwf x v], hty.projectStore⟩

end CallBase

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CallLangWF P]
  [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
  {CmdT : Type} [CmdDefs P CmdT]

/-- The per-call-site check on the arguments of a call: every input actual is `StrictActual` and
    `TypedActual`, and the write-back targets are distinct, as `CmdCallOk` checks them. -/
@[expose] def ArgsOk (args : List (CallArg P)) : Bool :=
  (getInputExprs args).all StrictActual && (getInputExprs args).all TypedActual &&
    decide (CallArg.getLhs args).Nodup

/-- The per-command check: a call, by its kind under `S`, passes `ArgsOk`; every other command
    passes. -/
@[expose] def CmdOk (S : CmdSem P CmdT Hdr) (c : CmdT) : Bool :=
  match S.kind c with
  | .call _ args _ _ => ArgsOk args
  | _ => true

/-- Shallow check on one procedure, as `ProcOk`: distinct frame formals, and a structured body
    that is exit-covered with all commands `CmdOk`, or a CFG body with all commands `CmdOk`. -/
@[expose] def ProcOkV (S : CmdSem P CmdT Hdr) (p : Procedure P CmdT Hdr) : Prop :=
  (ProcedureHeader.inputParams (P := P) p.header ++ outputOnlyParams (P := P) p.header).Nodup ∧
  (∀ ss opq, p.body = .structured ss opq →
    Block.exitsCoveredByBlocks (P := P) (CmdT := CmdT) [] ss ∧
    Block.allCmds (P := P) (CmdOk S) ss = true) ∧
  ∀ g opq, p.body = .cfg g opq → g.allCmds (CmdOk S)

/-- `p` is a procedure a call can run: the instantiation `inst` of a call's callee `π n`, for a
    call that is a command of kind `.call` or the outcome of an extension command under `S`. -/
@[expose] def CallRuns (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr))
    (p : Procedure P CmdT Hdr) : Prop :=
  ∃ n p₀ inst, π n = some p₀ ∧ inst p₀ = some p ∧
    ((∃ c args md, S.kind c = .call n args md inst) ∨
      (∃ f σ c σ' args md evs, S.ExtE f σ c (.call σ' n args md inst) evs))

/-- Every procedure a call can run (`CallRuns`) passes `ProcOkV`: the callee hypothesis of the
    soundness theorems, as `ProcsOk` is for `CmdExt`. -/
@[expose] def ProcsOkV (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr)) :
    Prop :=
  ∀ p, CallRuns S π p → ProcOkV S p

/-- The call mode `mode` runs as its contract (`CallMode.runsContract`) exactly the procedures a
    call can run (`CallRuns`) that the reference semantics runs as their contract, the opaque ones
    (`Body.isOpaque`). It holds under `CallMode.contract` (`modeOk_contract`). Under
    `CallMode.execute`, which runs the contract of an abstract callee only, it says that no
    procedure a call can run has an opaque body that is not abstract. -/
@[expose] def ModeOk (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr))
    (mode : CallMode) : Prop :=
  ∀ p, CallRuns S π p → mode.runsContract p.body = p.body.isOpaque

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [CallLangWF P] [HasOldIdent P] [ProcedureHeader P Hdr] [CmdDefs P CmdT] in
/-- `CallMode.contract` runs as its contract exactly the opaque callees. -/
theorem modeOk_contract (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr)) :
    ModeOk S π .contract :=
  fun _ _ => rfl

/-- The configuration invariant of a statement run, as `CfgInv`: a value-only store, all commands
    `CmdOk`, and typed stores. -/
@[expose] def CfgInvV (S : CmdSem P CmdT Hdr) (c : Config P CmdT) : Prop :=
  Config.storeWellDefined (P := P) c ∧
  Config.allCmds (P := P) (CmdOk S) c ∧
  Config.storeTyped (P := P) c

/-- `EvalCmdViewE S π` restricted to steps that keep a value-only store value-only and a typed
    store typed, and define only the names `CmdDefs` allows: the relation the engine's steps
    are shown to follow, so that the invariants transport along them. -/
@[expose] def EvalCommandVT (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr)) :
    EvalCmdParamE P CmdT (Event P) :=
  fun f σ c σ' evs => EvalCmdViewE S π f σ c σ' evs ∧
    (WellFormedStore σ f → WellFormedStore σ' f) ∧ (StoreTyped f σ → StoreTyped f σ') ∧
    DefinesWithin σ σ' (CmdDefs.defs (P := P) c)

/-- The invariant of a CFG run at the factory `fac`, as `CFGCfgInv`: a value-only, typed store,
    every command of the CFG (and the residual commands of a block) `CmdOk`, and the factory
    `fac`. -/
@[expose] def CFGCfgInvV {l : Type} [BEq l] (S : CmdSem P CmdT Hdr) (fac : P.Factory) :
    CFGConfig l CmdT P → Prop
  | .atBlock g _ ρ => CallEnvOk fac ρ.store ∧ g.allCmds (CmdOk S) ∧ ρ.factory = fac
  | .inBlock g _ cs _ ρ =>
    CallEnvOk fac ρ.store ∧ (∀ c ∈ cs, CmdOk S c = true) ∧ g.allCmds (CmdOk S) ∧ ρ.factory = fac
  | .terminal ρ => CallEnvOk fac ρ.store ∧ ρ.factory = fac

/-- What an extension command's run must establish, for its runtime outcome and the events `evs`
    it emitted, from the environment `env` at the factory `F`. For `.done σ'`: `S.ExtE` relates
    the command to the image of `σ'`, which is value-only, typed and denoting, and defines only
    the names `CmdDefs` allows. For `.call env' n args md inst`: the factory is unchanged, `S.ExtE`
    relates the command to that call from the image of `env'`'s store, which is value-only, typed
    and denoting, the arguments pass `ArgsOk`, and the store defines only the names `CmdDefs`
    allows. -/
@[expose] def ExtStepOk (S : CmdSem P CmdT Hdr) (F : P.Factory) (env : IEnv P) (c : CmdT) :
    ExtStep P CmdT Hdr → Trace P → Prop
  | .done σ', evs =>
    S.ExtE F (InterpLang.absStore F env.store.get) c (.done (InterpLang.absStore F σ'.get)) evs ∧
    CallEnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get ∧
    DefinesWithin (InterpLang.absStore F env.store.get) (InterpLang.absStore F σ'.get)
      (CmdDefs.defs (P := P) c)
  | .call env' n args md inst, evs =>
    env'.factory = env.factory ∧
    S.ExtE F (InterpLang.absStore F env.store.get) c
      (.call (InterpLang.absStore F env'.store.get) n args md inst) evs ∧
    CallEnvOk F (InterpLang.absStore F env'.store.get) ∧ RStore.Denoting F env'.store.get ∧
    ArgsOk args = true ∧
    DefinesWithin (InterpLang.absStore F env.store.get) (InterpLang.absStore F env'.store.get)
      (CmdDefs.defs (P := P) c)

variable {m : Type → Type} [Monad m] [InterpEffects P m]
  [MonadExcept StopReason m]

/-- The view `view` agrees with the command semantics `S`, observed through `obs`: a base command
    or a call of the view has that kind under `S` (a base command with the definitions of its
    `Cmd`), an extension command of the view has kind `.ext`, and every successful run of an
    extension command, from a denoting, value-only, typed store at a sound, well-formed factory,
    meets `ExtStepOk` for the events it emitted. This is the obligation of a new instance of the
    call-aware stepper. -/
structure ViewSound (obs : InterpObs P m) (view : CmdT → CmdView P CmdT Hdr m)
    (S : CmdSem P CmdT Hdr) :
    Prop where
  /-- A base command of the view is a base command of `S`, with the same definitions. -/
  base : ∀ c b, view c = .base b →
    S.kind c = .base b ∧ CmdDefs.defs (P := P) c = CmdDefs.defs (P := P) b
  /-- A call of the view is the same call under `S`. -/
  call : ∀ c n args md inst, view c = .call n args md inst → S.kind c = .call n args md inst
  /-- An extension command of the view is an extension command of `S`. -/
  ext_kind : ∀ c run, view c = .ext run → S.kind c = .ext
  /-- A successful run of an extension command meets `ExtStepOk`. -/
  ext : ∀ (F : P.Factory) (fuel : Nat) (c : CmdT) (run : Nat → IEnv P → m (ExtStep P CmdT Hdr))
    (env : IEnv P) (r : ExtStep P CmdT Hdr) (cfgr : obs.Cfg) (st st' : obs.St),
    view c = .ext run → obs.run (run fuel env) cfgr st = (.ok r, st') →
    FactoryWF (P := P) F → BoundedEvalSoundAt P F → RStore.Denoting F env.store.get →
    env.factory = InterpLang.rfactory F → CallEnvOk F (InterpLang.absStore F env.store.get) →
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st ∧
      ExtStepOk S F env c r (revs.map (REvent.abs F))

/-- The per-command obligation of the soundness theorems for the stepper `step` at the factory
    `F`: every successful step of a command from a configuration that denotes at `F` and meets
    `CfgInvV S` is one reference step over `EvalCommandVT S π` that emits exactly the recorded
    events, to a configuration that denotes at `F`. -/
@[expose] def ArmSound (obs : InterpObs P m) (step : StepCmdM P CmdT m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (F : P.Factory) : Prop :=
  ∀ (fuel : Nat) (cmd : CmdT) (env : IEnv P) (cfg' : IConfig P CmdT) (cfgr : obs.Cfg)
    (st st' : obs.St),
    obs.run (step fuel env cmd) cfgr st = (.ok cfg', st') →
    FactoryWF (P := P) F → RStore.Denoting F env.store.get →
    env.factory = InterpLang.rfactory F → CfgInvV S (.stmt (.cmd cmd) (env.abs F)) →
    ∃ revs : List (IEvent P), StepStmtE P (EvalCommandVT S π)
      (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
      ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [CallLangWF P] [HasOldIdent P] in
/-- `DefinesWithin` composes with a step that defines no new name. -/
private theorem definesWithin_trans {σ₁ σ₂ σ₃ : SemanticStore P} {L : List P.Ident}
    (h₁ : DefinesWithin σ₁ σ₂ L) (h₂ : DefinesWithin σ₂ σ₃ []) : DefinesWithin σ₁ σ₃ L :=
  fun x hx => (h₂ x hx).elim (h₁ x) (fun h => absurd h List.not_mem_nil)

omit [DecidableEq P.Expr] [InterpLang P] [CallLangWF P] in
/-- A run over `EvalCommandVT S π` is a run over `EvalCmdViewE S π`. -/
private theorem stepStarVT_toE (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr))
    {c c' : Config P CmdT} {evs : Trace P}
    (h : StepStmtStarE P (EvalCommandVT S π) c evs c') :
    StepStmtStarE P (EvalCmdViewE S π) c evs c' :=
  ReflTransTrace.imp (fun _ _ _ h' => StepStmtE.imp (fun _ _ _ _ _ => And.left) h') h

omit [DecidableEq P.Expr] [InterpLang P] [CallLangWF P] in
/-- A CFG run over `EvalCommandVT S π` is a CFG run over `EvalCmdViewE S π`. -/
private theorem stepCFGStarVT_toE {l : Type} [BEq l] (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr))
    {c c' : CFGConfig l CmdT P} {evs : Trace P}
    (h : StepCFGStarE P (EvalCommandVT S π) c evs c') :
    StepCFGStarE P (EvalCmdViewE S π) c evs c' :=
  ReflTransTrace.imp (fun _ _ _ h' => StepCFGE.imp (fun _ _ _ _ _ => And.left) h') h

omit [DecidableEq P.Expr] [InterpLang P] [CallLangWF P] in
/-- A step of `EvalCommandVT S π` defines only the names `CmdDefs` allows. -/
private theorem evalCommandVT_cmdDefsSound (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) : CmdDefsSound (EvalCommandVT S π) :=
  fun _ _ _ _ _ h => h.2.2.2

omit [DecidableEq P.Expr] in
/-- `CfgInvV S` is preserved by one reference step over `EvalCommandVT S π`. -/
private theorem cfgInvV_stepE (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr))
    {c c' : Config P CmdT} {evs : Trace P}
    (h : StepStmtE P (EvalCommandVT S π) c evs c') (hinv : CfgInvV S c) : CfgInvV S c' :=
  let ⟨hstore, hall, htyped⟩ := hinv
  ⟨Config.storeWellDefined_stepE_of (fun h => h.2.1) h hstore,
    stepStmtE_preserves_allCmds _ h hall,
    Config.storeTyped_stepE (fun h => h.2.2.1) h htyped⟩

omit [DecidableEq P.Expr] in
/-- `CfgInvV S` is preserved along a reference run over `EvalCommandVT S π`. -/
private theorem cfgInvV_stepStarE (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr))
    {c c' : Config P CmdT} {evs : Trace P}
    (h : StepStmtStarE P (EvalCommandVT S π) c evs c') (hinv : CfgInvV S c) : CfgInvV S c' := by
  induction h <;> grind [cfgInvV_stepE]

omit [DecidableEq P.Expr] in
/-- `CFGCfgInvV S fac` is preserved by one reference CFG step over `EvalCommandVT S π`. -/
theorem cfgCfgInvV_stepE {l : Type} [BEq l] (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (fac : P.Factory)
    {a : CFGConfig l CmdT P} {emitted : Trace P} {b : CFGConfig l CmdT P}
    (h : StepCFGE P (EvalCommandVT S π) a emitted b)
    (hinv : CFGCfgInvV S fac a) : CFGCfgInvV S fac b := by
  cases h <;> grind [CFGCfgInvV, CallEnvOk, CFG.allCmds, EvalCommandVT]

omit [DecidableEq P.Expr] in
/-- `CFGCfgInvV S fac` is preserved along a reference CFG run over `EvalCommandVT S π`. -/
private theorem cfgCfgInvV_starE {l : Type} [BEq l] (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (fac : P.Factory)
    {a : CFGConfig l CmdT P} {emitted : Trace P} {b : CFGConfig l CmdT P}
    (h : StepCFGStarE P (EvalCommandVT S π) a emitted b)
    (hinv : CFGCfgInvV S fac a) : CFGCfgInvV S fac b := by
  induction h <;> grind [cfgCfgInvV_stepE]

omit [DecidableEq P.Expr] [HasOldIdent P] [CmdDefs P CmdT] [ProcedureHeader P Hdr] in
/-- `CfgInvV S` projects into the inner configuration of a `.seq`. -/
theorem cfgInvV_seq (S : CmdSem P CmdT Hdr) (inner : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (h : CfgInvV S (.seq inner ss)) : CfgInvV S inner :=
  let ⟨hstore, hall, htyped⟩ := h
  ⟨hstore, hall.1, htyped⟩

omit [DecidableEq P.Expr] [HasOldIdent P] [CmdDefs P CmdT] [ProcedureHeader P Hdr] in
/-- `CfgInvV S` projects into the inner configuration of a `.block`. -/
theorem cfgInvV_block (S : CmdSem P CmdT Hdr) (l : Option String) (σ : SemanticStore P)
    (inner : Config P CmdT) (h : CfgInvV S (.block l σ inner)) : CfgInvV S inner :=
  let ⟨hstore, hall, htyped⟩ := h
  ⟨hstore.2, hall, htyped.2⟩

omit [DecidableEq P.Expr] in
/-- A call whose arguments pass `ArgsOk` and whose marshalling succeeded, from a value-only,
    typed store that denotes at a well-formed factory, meets `CallEntry` at the denoted input and
    `out` values, for a callee with distinct frame formals; its entry frame is value-only and typed,
    and denotes. -/
theorem callEntry_okV
    {args : List (CallArg P)} {F : P.Factory} {env : IEnv P}
    {C : Type} {p : Procedure P C Hdr} {k : Nat} {i o : List P.Expr}
    (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (henv : CallEnvOk F (InterpLang.absStore F env.store.get)) (hargs : ArgsOk args = true)
    (hnd : (ProcedureHeader.inputParams (P := P) p.header ++
      outputOnlyParams (P := P) p.header).Nodup)
    (hi : evalBoundedList k env.factory env.store.get (getInputExprs args) = some i)
    (hil : ¬i.length ≠ (ProcedureHeader.inputParams (P := P) p.header).length)
    (ho : readVarList env.store.get (CallArg.getOutArgs args) = some o)
    (hol : ¬o.length ≠ (outputOnlyParams (P := P) p.header).length) :
    ∃ vi vo, List.Rel₂ (InterpLang.Denotes F) i vi ∧ List.Rel₂ (InterpLang.Denotes F) o vo ∧
    CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo) ∧
    CallEnvOk F (callEntryStore p vi vo) ∧ RStore.Denoting F (callEntryStore p i o) ∧
    InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo := by
  obtain ⟨hstore, htyped⟩ := henv
  simp only [ArgsOk, Bool.and_eq_true, List.all_eq_true] at hargs
  rw [hrf] at hi
  have hvar := hfac.2.1
  obtain ⟨vi, hreli, hE⟩ :=
    evalExpressions_of_evalBoundedList_strict _ _ hEval _ hden hvar hstore _ _ hargs.1.1 hi
  obtain ⟨vi', hreli', htyi⟩ :=
    typed_of_evalBoundedList _ _ hEval _ hden hvar hstore htyped _ _ hargs.1.2 hi
  obtain rfl :=
    List.Rel₂.unique (fun _ _ _ h1 h2 => Option.some.inj (h1.symm.trans h2)) hreli' hreli
  obtain ⟨vo, hrelo, hro⟩ := readVarList_absStore_of_denoting hden _ _ ho
  obtain ⟨habs, hd⟩ := callEntryStore_abs p hreli hrelo
  refine ⟨vi', vo, hreli, hrelo, ⟨vi', vo, hE, readValues_of_readVarList _ _ hstore _ _ hro,
      initCallFrame_callEntryStore p vi' vo (by grind [List.Rel₂.length_eq])
        (by grind [List.Rel₂.length_eq]) hnd⟩,
    ⟨wellFormedStore_callEntryStore p vi' vo
      (evalExpressions_values (CallLangWF.evalVal _) hstore hE)
      (values_of_readVarList hstore _ _ hro),
    storeTyped_callEntryStore p vi' vo htyi (typed_of_readVarList htyped _ _ hro)⟩, hd, habs⟩

/-- Per-step soundness of the statement engine over `step` at the single factory `F₀`, from an
    `ArmSound` command arm at `F₀`: the invariant carries that the configuration's factory is
    `F₀`. -/
theorem stepSoundV_at [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (step : StepCmdM P CmdT m) {F₀ : P.Factory}
    (harm : ArmSound obs step S π F₀) :
    StepInterpSoundGeneric obs step (EvalCommandVT S π)
      (fun c => CfgInvV S c ∧ c.getEnv.factory = F₀) :=
  stepInterpSoundGeneric_of_arms obs _ _ _ (fun _ _ h => ⟨cfgInvV_seq S _ _ h.1, h.2⟩)
    (fun _ _ _ h => ⟨cfgInvV_block S _ _ _ h.1, h.2⟩)
    (fun _ fuel cmd env cfg' cfgr st st' h hf _ ⟨hd, hrf⟩ ⟨hi, hF⟩ => by
      subst hF
      obtain ⟨revs, hs, ht, hd'⟩ := harm fuel cmd env cfg' cfgr st st' h hf hd hrf hi
      exact ⟨⟨revs, hs, ht⟩, hd'⟩)
    (fun _ _ _ hs hi => ⟨cfgInvV_stepE S π hs hi.1,
      (stepE_preserves_factory (StepStmtE.imp (fun _ _ _ _ _ => And.left) hs)).symm.trans hi.2⟩)
    (evalCommandVT_cmdDefsSound S π)

/-- Per-step soundness of the statement engine over `step`, from an `ArmSound` command arm at
    every factory at which the bounded evaluator is sound. -/
private theorem stepSoundV [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (step : StepCmdM P CmdT m)
    (harm : ∀ F, BoundedEvalSoundAt P F → ArmSound obs step S π F) :
    StepInterpSoundGeneric obs step (EvalCommandVT S π) (CfgInvV S) :=
  stepInterpSoundGeneric_of_arms obs _ _ _ (cfgInvV_seq S) (cfgInvV_block S)
    (fun F fuel cmd env cfg' cfgr st st' h hf hE ⟨hd, hrf⟩ hi =>
      let ⟨revs, hs, ht, hd'⟩ := harm F hE fuel cmd env cfg' cfgr st st' h hf hd hrf hi
      ⟨⟨revs, hs, ht⟩, hd'⟩)
    (fun _ _ _ => cfgInvV_stepE S π) (evalCommandVT_cmdDefsSound S π)

/-- A successful run of a structured callee body (as `.block "" ss`) over a stepper meeting
    `ArmSound`, for a procedure passing `ProcOkV`, ends in a terminal configuration at the caller's
    factory that meets `CfgInvV S`, and is a reference run over `EvalCommandVT S π` emitting
    exactly the recorded events. -/
theorem callee_run_okV [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr))
    (hEval : BoundedEvalSoundAt P F) (step : StepCmdM P CmdT m)
    {p : Procedure P CmdT Hdr} {ss : List (Stmt P CmdT)} {k : Nat}
    {E : IEnv P} {fc : IConfig P CmdT} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ArmSound obs step S π F)
    (hp : ProcOkV S p) (hb : p.body = .structured ss opq)
    (hI : CfgInvV S (.stmt (.block "" ss #[]) (E.abs F))) (hfE : FactoryWF (P := P) F)
    (hdE : RStore.Denoting F E.store.get) (hrE : E.factory = InterpLang.rfactory F)
    (h : obs.run (runInterp step k (.stmt (.block "" ss #[]) E)) cfgr st = (.ok fc, st')) :
    ∃ σ', fc = .terminal ⟨σ', E.factory⟩ ∧ fc.Denoting F ∧ CfgInvV S (fc.abs F) ∧
      ∃ revs : List (IEvent P), StepStmtStarE P (EvalCommandVT S π)
        (.stmt (.block "" ss #[]) (E.abs F)) (revs.map (REvent.abs F)) (fc.abs F) ∧
          obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨revs, R, hdf, -, htr⟩ := runInterp_sound_tracked obs _ _ _
    (stepSoundV_at obs S π step IH) F k _ fc cfgr st st' h hfE hEval ⟨hdE, hrE⟩
    ⟨hI, rfl⟩ trivial
  obtain ⟨⟨σ', f⟩, rfl⟩ := (obs_runInterp_ok_final obs _ _ _ _ _ _ _ h).resolve_right
    fun ⟨_, _, hfc⟩ => absurd (hfc ▸ R) (exitsCoveredByBlocks_noEscapeE _ (.block "" ss #[])
      ((exitsCoveredByBlocks_weaken [] [""] nofun).2 ss (hp.2.1 ss _ hb).1) _ _ _)
  obtain rfl : f = E.factory := hdf.2.trans hrE.symm
  exact ⟨_, rfl, hdf, cfgInvV_stepStarE S π R hI, revs, R, htr⟩

/-- A successful step of a `CmdOk` command, projected to its store, from a value-only, typed store
    that denotes at a well-formed factory, is a step of `EvalCommandVT S π` emitting exactly the
    recorded events, to a value-only, typed store that denotes, for a stepper meeting `ArmSound`. -/
theorem store_sound_of_armV (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (step : StepCmdM P CmdT m) {k : Nat}
    (IH : ArmSound obs step S π F)
    {σ σ' : IStore P} {cmd : CmdT} {cfgr : obs.Cfg} {st st' : obs.St}
    (hfac : FactoryWF (P := P) F) (hok : CmdOk S cmd = true) (hd : RStore.Denoting F σ.get)
    (henv : CallEnvOk F (InterpLang.absStore F σ.get))
    (h : obs.run (StepCmdM.toStore step k (InterpLang.rfactory F) σ cmd) cfgr st =
        (.ok σ', st')) :
    ∃ revs : List (IEvent P), EvalCommandVT S π F (InterpLang.absStore F σ.get) cmd
        (InterpLang.absStore F σ'.get) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σ'.get) ∧ RStore.Denoting F σ'.get
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  rw [obs.run_bind] at h
  split at h <;>
    simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i c s hrun
  obtain ⟨revs, hs, ht, hdc⟩ := IH k cmd ⟨σ, InterpLang.rfactory F⟩ c cfgr st s hrun hfac hd rfl
    ⟨henv.1, by simp [Config.allCmds, Stmt.allCmds, hok], henv.2⟩
  obtain ⟨ρ', hρ'⟩ := hs.cmd_terminal
  obtain ⟨e, rfl, -⟩ := (IConfig.abs_eq_terminal _ _ _).1 hρ'
  simp only [IConfig.abs, IEnv.abs] at hs
  cases hs
  rename_i hev
  exact ⟨revs, hev, ⟨hev.2.1 henv.1, hev.2.2.1 henv.2⟩, hdc.1, ht⟩

/-- A successful `runInterpCFG` run over a stepper meeting `ArmSound`, from a configuration that
    denotes at a well-formed factory `F` and meets `CFGCfgInvV S F`, is a reference CFG run over
    `EvalCommandVT S π` emitting exactly the recorded events, to a configuration that denotes. -/
theorem cfg_run_soundV [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr)) (hEval : BoundedEvalSoundAt P F)
    (step : StepCmdM P CmdT m)
    (IH : ArmSound obs step S π F)
    (hfac : FactoryWF (P := P) F) {n : Nat} {c c' : ICFGConfig String CmdT P}
    {cfgr : obs.Cfg} {st st' : obs.St} (hd : c.Denoting F) (hinv : CFGCfgInvV S F (c.abs F))
    (h : obs.run (runInterpCFG step.toStore n c) cfgr st = (.ok c', st')) :
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGStarE P (EvalCommandVT S π) (c.abs F) (revs.map (REvent.abs F)) (c'.abs F)
      ∧ c'.Denoting F :=
  runInterpCFG_soundE obs (EvalCommandVT S π) _ (CFGCfgInvV S F) F
    (fun fuel _ _ _ _ _ _ _ _ _ _ hdρ hrf ⟨he, hr, _, _⟩ hc =>
      (store_sound_of_armV obs S π step (k := fuel) IH hfac (hr _ (.head _)) hdρ he (hrf ▸ hc)).imp
        fun _ ⟨hev, _, hd', ht⟩ => ⟨ht, hev, hd'⟩)
    (fun _ _ _ => cfgCfgInvV_stepE S π F) hEval _ _ _ _ _ _ hd hinv h

/-- A successful callee body run (`runCallee`), structured or CFG, over a stepper meeting
    `ArmSound`, for a procedure passing `ProcOkV`, from a value-only, typed entry frame that
    denotes, is a `BigStepViewE S π` body run emitting exactly the recorded events, to a value-only,
    typed final store that denotes. -/
theorem runCallee_okV [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr))
    (hEval : BoundedEvalSoundAt P F) (step : StepCmdM P CmdT m)
    {n : String} {p : Procedure P CmdT Hdr} {k : Nat}
    {σ σf : RStore P} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ArmSound obs step S π F)
    (hp : ProcOkV S p) (hfac : FactoryWF (P := P) F) (hd : RStore.Denoting F σ)
    (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runCallee step n p.body (InterpLang.rfactory F) k σ) cfgr st = (.ok σf, st')) :
    ∃ revs : List (IEvent P), BigStepViewE S π p.body ⟨InterpLang.absStore F σ, F⟩
        (InterpLang.absStore F σf) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σf) ∧ RStore.Denoting F σf
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨-, hS, hC⟩ := id hp
  have hE : IEnv.abs F (⟨.ofStore σ, InterpLang.rfactory F⟩ : IEnv P) =
      ⟨InterpLang.absStore F σ, F⟩ := by simp [IEnv.abs]
  revert h
  cases hb : p.body with
  | structured ss =>
    intro h
    simp only [runCallee, obs.run_bind] at h
    split at h
    · rename_i fc s hrun
      obtain ⟨σ', rfl, hdf, ⟨hwf, -, hty⟩, revs, R, htr⟩ :=
        callee_run_okV obs S π hEval step (E := ⟨.ofStore σ, InterpLang.rfactory F⟩) IH hp
          hb (hE ▸ ⟨henv.1, by simpa [Config.allCmds, Stmt.allCmds] using (hS ss _ hb).2,
            henv.2⟩)
          hfac (by simpa using hd) rfl hrun
      simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨revs, .structured (hE ▸ stepStarVT_toE S π R), ⟨hwf, hty⟩, hdf.1, htr⟩
    · simp at h
  | cfg g =>
    intro h
    simp only [runCallee, obs.run_bind] at h
    split at h
    · rename_i fc s hrun
      have hA : ICFGConfig.abs F (.atBlock g g.entry ⟨.ofStore σ, InterpLang.rfactory F⟩ :
          ICFGConfig _ CmdT P) = .atBlock g g.entry ⟨InterpLang.absStore F σ, F⟩ := by
        simp [ICFGConfig.abs, IEnv.abs]
      have hInv : CFGCfgInvV S F
          (ICFGConfig.abs F (.atBlock g g.entry ⟨.ofStore σ, InterpLang.rfactory F⟩)) :=
        hA ▸ ⟨henv, hC g _ hb, rfl⟩
      obtain ⟨revs, htr, R, hdf⟩ := cfg_run_soundV obs S π hEval step IH hfac
        ⟨by simpa [ICFGConfig.env] using hd, rfl⟩ hInv hrun
      have hfin := cfgCfgInvV_starE S π F R hInv
      rw [hA] at R
      split at h
      · simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rename_i ρEnd
        refine ⟨revs, ?_, ?_, hdf.1.project _, htr⟩
        · rw [InterpLang.absStore_project _ hd]
          exact .cfg (stepCFGStarVT_toE S π R)
        · rw [InterpLang.absStore_project _ hd]
          exact callEnvOk_projectStore _ _ _ hfin.1
      · simp [obs.run_throw] at h
    · simp at h
  | abstract => intro h; simp [runCallee, obs.run_throw] at h

omit [HasOldIdent P] in
/-- A successful `havocVarList` run over the names `xs`, at a well-formed factory (`FactoryWF`),
    from a store that denotes a well-formed, typed store (`CallEnvOk`), is a reference
    `HavocVars` of `xs` between the stores' images, records no event, and ends in a store that
    again denotes a well-formed, typed store. -/
theorem havocVarList_sound (obs : InterpObs P m) (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) (fuel : Nat) :
    ∀ (xs : List P.Ident) (st st' : IStore P) (cfgr : obs.Cfg) (s s' : obs.St),
      obs.run (havocVarList fuel (InterpLang.rfactory F) xs st) cfgr s = (.ok st', s') →
      RStore.Denoting F st.get → CallEnvOk F (InterpLang.absStore F st.get) →
      HavocVars F (InterpLang.absStore F st.get) xs (InterpLang.absStore F st'.get) ∧
        RStore.Denoting F st'.get ∧ CallEnvOk F (InterpLang.absStore F st'.get) ∧
        obs.trace s' = obs.trace s
  | [], _, _, _, _, _, h, hd, henv => by
    simp only [havocVarList, InterpObs.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.update_none, hd, henv, rfl⟩
  | x :: xs, st, st', cfgr, s, s', h, hd, henv => by
    simp only [havocVarList, InterpObs.run_bind] at h
    split at h
    · rename_i st1 s1 h1
      obtain ⟨revs, hstep, hd1, t1⟩ :=
        obs_stepBaseCmdStore_sound obs _ _ hEval _ _ _ _ _ _ hfac.2.1 hd henv.2 h1
      have henv1 : CallEnvOk F (InterpLang.absStore F st1.get) :=
        ⟨evalCmdE_storeWellDefined (CallLangWF.evalVal _) hstep henv.1,
          evalCmdE_storeTyped hstep henv.2⟩
      obtain ⟨H, hd', henv', t⟩ := havocVarList_sound obs hEval hfac fuel xs st1 st' cfgr s1 s'
        h hd1 henv1
      generalize hR : revs.map (REvent.abs F) = R at hstep
      cases hstep with
      | eval_set_nondet hupd hty _ =>
        refine ⟨.update_some hupd hty H, hd', henv', ?_⟩
        rw [t, t1, List.map_eq_nil_iff.1 hR]
        rfl
    · simp at h

omit [HasOldIdent P] in
/-- A successful contract run of an opaque callee (`runAbstractCallee`) over the output formals
    `xs`, at a well-formed factory (`FactoryWF`), from an entry frame that denotes a well-formed,
    typed store (`CallEnvOk`), havocs `xs` in the reference sense (`HavocVars`), records exactly
    the assumption events of `post` at the returned frame, and returns a store that denotes a
    well-formed, typed store. -/
theorem runAbstractCallee_sound (obs : InterpObs P m) (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) {fuel : Nat} {xs : List P.Ident}
    {post : ListMap String (Check P)} {σ σf : RStore P} {cfgr : obs.Cfg} {st st' : obs.St}
    (hd : RStore.Denoting F σ) (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runAbstractCallee fuel (InterpLang.rfactory F) xs post σ) cfgr st =
      (.ok σf, st')) :
    HavocVars F (InterpLang.absStore F σ) xs (InterpLang.absStore F σf) ∧
      RStore.Denoting F σf ∧ CallEnvOk F (InterpLang.absStore F σf) ∧
      obs.trace st' = (rAssumeEvents (InterpLang.rfactory F) σf post).reverse ++ obs.trace st := by
  simp only [runAbstractCallee, obs.run_bind] at h
  split at h
  · rename_i σO s1 h1
    split at h
    · rename_i s2 h2
      simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨H, hd', henv', t⟩ := havocVarList_sound obs hEval hfac _ _ _ _ _ _ _ h1
        (by simpa using hd) (by simpa using henv)
      simp only [IStore.get_ofStore] at H
      exact ⟨H, hd', henv', by rw [obs_forM_emit obs _ _ _ _ _ h2, t]⟩
    · simp at h
  · simp at h

omit [DecidableEq P.Expr] [HasOldIdent P] in
/-- The write-back of a successful call: from a value-only, typed caller store that denotes, whose
    write-back targets are bound, distinct, as many as the output formals, and read `olds`, and a
    value-only, typed callee store `σE` that denotes and in which the output formals read `w`, a
    passed typed write-back check (`writeBackTyped`) gives a store `store'`, the caller store with
    the outputs written back, that denotes, is value-only and typed, defines no new name, and is
    reached by `CallExit`. -/
private theorem writeBack_okV {F : P.Factory} {env : IEnv P} {C : Type} {p : Procedure P C Hdr}
    {args : List (CallArg P)} {σE : RStore P} {w olds : List P.Expr}
    (hden : RStore.Denoting F env.store.get)
    (henv : CallEnvOk F (InterpLang.absStore F env.store.get))
    (hdef : SemanticStore.varsDefined (· ∈ CallArg.getLhs args)
      (InterpLang.absStore F env.store.get))
    (hlhs : (CallArg.getLhs args).Nodup)
    (hlen : (CallArg.getLhs args).length = (ProcedureHeader.outputParams (P := P) p.header).length)
    (holds : readVarList env.store.get (CallArg.getLhs args) = some olds)
    (hwb : writeBackTyped (InterpLang.ops (P := P)) (InterpLang.rfactory F) olds w = true)
    (hE : CallEnvOk F (InterpLang.absStore F σE)) (hdf : RStore.Denoting F σE)
    (hw : readVarList σE (ProcedureHeader.outputParams (P := P) p.header) = some w) :
    ∃ store' : IStore P, store' = env.store.bindPositional (CallArg.getLhs args) w ∧
      RStore.Denoting F store'.get ∧ CallEnvOk F (InterpLang.absStore F store'.get) ∧
      DefinesWithin (InterpLang.absStore F env.store.get) (InterpLang.absStore F store'.get) [] ∧
      CallExit F (InterpLang.absStore F env.store.get) p args (InterpLang.absStore F σE)
        (InterpLang.absStore F store'.get) := by
  obtain ⟨vw, hrelw, hrw⟩ := readVarList_absStore_of_denoting hdf _ _ hw
  have M := readValues_of_readVarList _ _ hE.1 _ _ hrw
  have hlw : (CallArg.getLhs args).length = vw.length := hlen.trans (ReadValuesLength M)
  have hwt := storedTy_of_writeBackTyped hden henv.2 _ _ _ _ holds hlw hrelw hwb
  have habsW := absStore_bindPositional env.store.get (CallArg.getLhs args) hrelw
  have hup := updateStates_bindPositional _ _ _ hlw hdef
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa [IStore.get_bindPositional] using denoting_bindPositional _ hden hrelw
  · simp only [IStore.get_bindPositional, habsW]
    exact ⟨wellFormedStore_updateStates hup (readValues_values M) henv.1,
      storeTyped_bindPositional _ _ _ henv.2 (typed_of_readVarList hE.2 _ _ hrw)⟩
  · simp only [IStore.get_bindPositional, habsW]
    exact fun x hx => .inl (UpdateStatesDefMonotone' (vs := [x])
      (fun _ hv => List.mem_singleton.1 hv ▸ hx) hup x (List.mem_singleton_self x))
  · simp only [IStore.get_bindPositional, habsW]
    exact ⟨hlhs, vw, M, hup, hwt⟩

/-- What a successful call of `p` with arguments `args` and metadata `md` from the caller store
    `σ` to the store `σ'`, emitting `evs`, establishes: `CallEntry` to an entry frame `σAO`,
    `CallExit` from a callee store `σf`, and between them, for a callee that is not opaque, a body
    run `BigStepViewE` with the precondition, body and postcondition events, or, for an opaque
    callee, a `HavocVars` of the output formals with the precondition and postcondition
    assumption events, as the call rules of `EvalCmdViewE` require. -/
@[expose] def CallOutcome (S : CmdSem P CmdT Hdr) (π : String → Option (Procedure P CmdT Hdr))
    (F : P.Factory) (σ : SemanticStore P) (p : Procedure P CmdT Hdr) (args : List (CallArg P))
    (md : MetaData P) (σ' : SemanticStore P) (evs : Trace P) : Prop :=
  ∃ σAO σf, CallEntry F σ p args σAO ∧ CallExit F σ p args σf σ' ∧
    ((p.body.isOpaque = false ∧ ∃ bodyEvs, BigStepViewE S π p.body ⟨σAO, F⟩ σf bodyEvs ∧
        evs = defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++ bodyEvs ++
          defaultAssertEvents F σf p.spec.postconditions) ∨
      (p.body.isOpaque = true ∧
        HavocVars F σAO (ProcedureHeader.outputParams (P := P) p.header) σf ∧
        evs = defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++
          assumeEvents F σf p.spec.postconditions))

/-- A successful run of the call protocol `callBody` in mode `mode` of a call whose arguments pass
    `ArgsOk`, to a procedure passing `ProcOkV` that `mode` runs as its contract exactly when it is
    opaque, over a stepper meeting `ArmSound`, from a value-only, typed store that denotes, ends in
    the caller's environment with a store that denotes, is value-only and typed, defines no new
    name, and is reached as `CallOutcome` describes, emitting exactly the recorded events. -/
private theorem callBody_okV [InterpLangBool P] (obs : InterpObs P m) (S : CmdSem P CmdT Hdr)
    (π : String → Option (Procedure P CmdT Hdr))
    (hEval : BoundedEvalSoundAt P F) (mode : CallMode) (step : StepCmdM P CmdT m) (k : Nat)
    (IH : ArmSound obs step S π F)
    {n : String} {args : List (CallArg P)} {md : MetaData P} {p : Procedure P CmdT Hdr}
    (hp : ProcOkV S p) (hmode : mode.runsContract p.body = p.body.isOpaque) {env : IEnv P}
    {cfg' : IConfig P CmdT} {cfgr : obs.Cfg} {st st' : obs.St}
    (hrun : obs.run (callBody mode step (k + 1) k p env n args md) cfgr st = (.ok cfg', st'))
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (henv : CallEnvOk F (InterpLang.absStore F env.store.get)) (hargs : ArgsOk args = true) :
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st ∧
      ∃ store' : IStore P, cfg' = .terminal { env with store := store' } ∧
        RStore.Denoting F store'.get ∧ CallEnvOk F (InterpLang.absStore F store'.get) ∧
        DefinesWithin (InterpLang.absStore F env.store.get) (InterpLang.absStore F store'.get) [] ∧
        CallOutcome S π F (InterpLang.absStore F env.store.get) p args md
          (InterpLang.absStore F store'.get) (revs.map (REvent.abs F)) := by
  have hlhs : (CallArg.getLhs args).Nodup := by
    simp only [ArgsOk, Bool.and_eq_true, decide_eq_true_eq] at hargs
    exact hargs.2
  simp only [callBody, ne_eq, List.forM_eq_forM, ite_not] at hrun
  repeat' (first
    | split at hrun
    | simp only [InterpObs.run_bind,
        InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
        false_and] at hrun)
  all_goals obtain ⟨rfl, rfl⟩ := hrun
  · rename_i i hi hil _ o ho hol hab hlen _ olds holds _ _ _ hpre _ σf _ hbody _ w hw hwb
    rw [hrf] at hbody hpre hwb
    obtain ⟨vi, vo, hreli, hrelo, hE, hen, hdEntry, habsEntry⟩ :=
      callEntry_okV hEval hfac hden hrf henv hargs hp.1 hi (· hil) ho (· hol)
    obtain ⟨_, _, hargsE, hread, hinit⟩ := hE
    obtain ⟨vo', -, hro⟩ := readVarList_absStore_of_denoting hden _ _ ho
    obtain ⟨H, hdf, hEf, t⟩ :=
      runAbstractCallee_sound obs hEval hfac hdEntry (habsEntry ▸ hen) hbody
    rw [habsEntry] at H
    obtain ⟨_, rfl, hdS, hcall, hdefs, hexit⟩ := writeBack_okV hden henv
      (getLhs_defined args hargsE hro) hlhs hlen holds (by simpa using hwb) hEf hdf hw
    refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions) ++
        rAssumeEvents (InterpLang.rfactory F) σf p.spec.postconditions,
      by simp [t, obs_forM_emit obs _ _ _ _ _ hpre], _, rfl, hdS, hcall, hdefs,
      _, _, ⟨_, _, hargsE, hread, hinit⟩, hexit, .inr ⟨hmode.symm.trans hab, H, ?_⟩⟩
    simp only [List.map_append, rDefaultAssertEvents_abs, rAssumeEvents_abs, habsEntry]
  · rename_i i hi hil _ o ho hol hab hlen _ olds holds _ _ _ hpre _ σf _ hbody _ _ _ hpost _ w
      hw hwb
    rw [hrf] at hbody hpre hpost hwb
    obtain ⟨vi, vo, hreli, hrelo, hE, hen, hdEntry, habsEntry⟩ :=
      callEntry_okV hEval hfac hden hrf henv hargs hp.1 hi (· hil) ho (· hol)
    obtain ⟨_, _, hargsE, hread, hinit⟩ := hE
    obtain ⟨vo', -, hro⟩ := readVarList_absStore_of_denoting hden _ _ ho
    obtain ⟨bevs, B, hEf, hdf, t⟩ :=
      runCallee_okV obs S π hEval step IH hp hfac hdEntry (habsEntry ▸ hen) hbody
    rw [habsEntry] at B
    obtain ⟨_, rfl, hdS, hcall, hdefs, hexit⟩ := writeBack_okV hden henv
      (getLhs_defined args hargsE hro) hlhs hlen holds (by simpa using hwb) hEf hdf hw
    refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions) ++ bevs ++
        rDefaultAssertEvents (InterpLang.rfactory F) σf p.spec.postconditions,
      by simp [obs_forM_emit obs _ _ _ _ _ hpost, t, obs_forM_emit obs _ _ _ _ _ hpre], _, rfl,
      hdS, hcall, hdefs, _, _, ⟨_, _, hargsE, hread, hinit⟩, hexit,
      .inl ⟨hmode.symm.trans (Bool.of_not_eq_true hab), _, B, ?_⟩⟩
    simp only [List.map_append, rDefaultAssertEvents_abs, habsEntry]

/-- The wrapper `w` keeps successful runs: a successful run of `w c x` is a successful run of `x`,
    with the same result and final state. The `around` wrapper of `stepCmdWith` and Cortex's
    `locatedAt` are such wrappers. -/
@[expose] def AroundOk (obs : InterpObs P m) {α : Type} (w : CmdT → m α → m α) : Prop :=
  ∀ (c : CmdT) (x : m α) (cfgr : obs.Cfg) (st st' : obs.St) (r : α),
    obs.run (w c x) cfgr st = (.ok r, st') → obs.run x cfgr st = (.ok r, st')

/-- A stepper whose steps are wrapped by an `AroundOk` wrapper meets `ArmSound` when the unwrapped
    stepper does. -/
theorem armSound_wrap (obs : InterpObs P m) {S : CmdSem P CmdT Hdr}
    {π : String → Option (Procedure P CmdT Hdr)} {step : StepCmdM P CmdT m}
    {w : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (hw : AroundOk obs w)
    (h : ArmSound obs step S π F) : ArmSound obs (fun f e c => w c (step f e c)) S π F :=
  fun fuel cmd env cfg' cfgr st st' hrun => h fuel cmd env cfg' cfgr st st' (hw _ _ _ _ _ _ hrun)

omit [HasFvars P] [CallLangWF P] in
/-- A successful `dispatchCall` run had fuel and call-depth budget left, found the callee `p₀` and
    its instantiation `p`, and is a successful run of `callBody` for `p`. -/
private theorem dispatchCall_ok (obs : InterpObs P m)
    (π : String → Option (Procedure P CmdT Hdr)) {mode : CallMode} {k d : Nat}
    {step : (d' k' : Nat) → k' < k → StepCmdM P CmdT m} {env : IEnv P} {n : String}
    {args : List (CallArg P)} {md : MetaData P}
    {inst : Procedure P CmdT Hdr → Option (Procedure P CmdT Hdr)} {cfg' : IConfig P CmdT}
    {cfgr : obs.Cfg} {st st' : obs.St}
    (h : obs.run (dispatchCall π mode k d step env n args md inst) cfgr st = (.ok cfg', st')) :
    ∃ k' d' p₀ p, ∃ hk : k = k' + 1, d = d' + 1 ∧ π n = some p₀ ∧ inst p₀ = some p ∧
      obs.run (callBody mode (step d' k' (hk ▸ Nat.lt_succ_self k')) (k' + 1) k' p env n args
        md) cfgr st = (.ok cfg', st') := by
  cases k with
  | zero => simp [dispatchCall, obs.run_throw] at h
  | succ k' =>
    cases d with
    | zero => simp [dispatchCall, obs.run_throw] at h
    | succ d' =>
      cases hπ : π n with
      | none => simp [dispatchCall, hπ, obs.run_throw] at h
      | some p₀ =>
        cases hinst : inst p₀ with
        | none => simp [dispatchCall, hπ, hinst, obs.run_throw] at h
        | some p =>
          simp only [dispatchCall, hπ, hinst] at h
          exact ⟨k', d', p₀, p, rfl, rfl, rfl, hinst, h⟩

/-- The call path shared by a call and by an extension command that resolves to one: a successful
    `dispatchCall` run in mode `mode`, at fuel `k` and budget `d`, of a call that some command or
    extension outcome of `S` makes (so its callee passes `ProcOkV`, and `ModeOk` applies to it),
    from a value-only, typed store that denotes, found the callee and its instantiation and ran
    `callBody` as `callBody_okV` describes, given `ArmSound` at the decremented fuel and budget. -/
private theorem dispatchCall_okV [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr}
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (hEval : BoundedEvalSoundAt P F) {k d : Nat}
    (IH : ∀ k' d', k = k' + 1 → d = d' + 1 →
      ArmSound obs (fun _ e c => stepCmdWith view around π mode d' k' e c) S π F)
    {env : IEnv P} {n : String} {args : List (CallArg P)} {md : MetaData P}
    {inst : Procedure P CmdT Hdr → Option (Procedure P CmdT Hdr)} {cfg' : IConfig P CmdT}
    {cfgr : obs.Cfg} {st st' : obs.St}
    (hrun : obs.run (dispatchCall π mode k d
      (fun d k _ _ e c => around c (stepCmdWith view around π mode d k e c)) env n args md inst)
      cfgr st = (.ok cfg', st'))
    (hruns : (∃ c args md, S.kind c = .call n args md inst) ∨
      (∃ f σ c σ' args md evs, S.ExtE f σ c (.call σ' n args md inst) evs))
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (henv : CallEnvOk F (InterpLang.absStore F env.store.get)) (hargs : ArgsOk args = true) :
    ∃ p₀ p, π n = some p₀ ∧ inst p₀ = some p ∧
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st ∧
      ∃ store' : IStore P, cfg' = .terminal { env with store := store' } ∧
        RStore.Denoting F store'.get ∧ CallEnvOk F (InterpLang.absStore F store'.get) ∧
        DefinesWithin (InterpLang.absStore F env.store.get) (InterpLang.absStore F store'.get) [] ∧
        CallOutcome S π F (InterpLang.absStore F env.store.get) p args md
          (InterpLang.absStore F store'.get) (revs.map (REvent.abs F)) := by
  obtain ⟨k', d', p₀, p, rfl, rfl, hπ, hinst, hrun⟩ := dispatchCall_ok obs π hrun
  have hr : CallRuns S π p := ⟨n, p₀, inst, hπ, hinst, hruns⟩
  exact ⟨p₀, p, hπ, hinst, callBody_okV obs S π hEval mode _ k'
    (armSound_wrap obs haround (IH k' d' rfl rfl)) (hprocs p hr) (hmode p hr) hrun hfac hden hrf
    henv hargs⟩

/-- The inductive step of per-command soundness: `stepCmdWith` in mode `mode` at fuel `k` and
    budget `d` meets `ArmSound` when it does at every smaller fuel and budget its calls run the
    callee at. -/
private theorem stepCmdWith_arm_step [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr} (hv : ViewSound obs view S)
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (hEval : BoundedEvalSoundAt P F) (k d : Nat)
    (IH : ∀ k' d', k = k' + 1 → d = d' + 1 →
      ArmSound obs (fun _ e c => stepCmdWith view around π mode d' k' e c) S π F) :
    ArmSound obs (fun _ e c => stepCmdWith view around π mode d k e c) S π F := by
  intro _ cmd env cfg' cfgr st st' hrun hfac hden hrf hinv
  have henv : CallEnvOk F (InterpLang.absStore F env.store.get) := ⟨hinv.1, hinv.2.2⟩
  dsimp only at hrun
  rw [stepCmdWith] at hrun
  cases hvc : view cmd with
  | base b =>
    simp only [hvc, obs.run_bind, obs.run_pure] at hrun
    split at hrun <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    rename_i hb
    rw [hrf] at hb
    obtain ⟨hk, hdefs⟩ := hv.base cmd b hvc
    obtain ⟨revs, hstep, hd', htr⟩ :=
      obs_stepBaseCmdStore_sound obs _ _ hEval _ _ _ _ _ _ hfac.2.1 hden hinv.2.2 hb
    refine ⟨revs, .step_cmd ⟨.base_sem hk hstep,
      evalCmdE_storeWellDefined (CallLangWF.evalVal _) hstep, evalCmdE_storeTyped hstep, ?_⟩,
      htr, hd', hrf⟩
    rw [hdefs]
    exact evalCmdE_cmdDefsSound _ _ _ _ _ hstep
  | call n args md inst =>
    simp only [hvc] at hrun
    have hk := hv.call cmd n args md inst hvc
    have hargs : ArgsOk args = true := by
      have h := hinv.2.1
      simpa [Config.allCmds, Stmt.allCmds, CmdOk, hk] using h
    obtain ⟨p₀, p, hπ, hinst, revs, htr, store', rfl, hdS, hcall, hdefs, σAO, σf, hentry,
        hexit, hout⟩ :=
      dispatchCall_okV obs haround π mode hprocs hmode hEval IH hrun (.inl ⟨cmd, args, md, hk⟩)
        hfac hden hrf henv hargs
    refine ⟨revs, ?_, htr, hdS, hrf⟩
    have hE : EvalCmdViewE S π F (InterpLang.absStore F env.store.get) cmd
        (InterpLang.absStore F store'.get) (revs.map (REvent.abs F)) := by
      rcases hout with ⟨hno, bevs, hbody, hevs⟩ | ⟨ho, hhavoc, hevs⟩
      · rw [hevs]; exact .call_sem hk hπ hinst hno hentry hbody hexit
      · rw [hevs]; exact .call_contract_sem hk hπ hinst ho hentry hhavoc hexit
    exact .step_cmd ⟨hE, fun _ => hcall.1, fun _ => hcall.2,
      fun x hx => (hdefs x hx).elim .inl (absurd · List.not_mem_nil)⟩
  | ext run =>
    have hk := hv.ext_kind cmd run hvc
    simp only [hvc, obs.run_bind] at hrun
    split at hrun
    · rename_i r s1 hr
      obtain ⟨revs1, htr1, hok⟩ := hv.ext F _ cmd run env r cfgr st s1 hvc hr hfac hEval hden hrf
        henv
      cases r with
      | done σ' =>
        simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨hE, hcall, hdσ, hdefs⟩ := hok
        exact ⟨revs1, .step_cmd ⟨.ext_sem hk hE, fun _ => hcall.1, fun _ => hcall.2, hdefs⟩, htr1,
          hdσ, hrf⟩
      | call env' n args md inst =>
        obtain ⟨hfac', hE, henv', hden', hargs, hdefs1⟩ := hok
        obtain ⟨p₀, p, hπ, hinst, revs2, htr2, store', rfl, hdS, hcall, hdefs2, σAO, σf,
            hentry, hexit, hout⟩ :=
          dispatchCall_okV obs haround π mode hprocs hmode hEval IH hrun
            (.inr ⟨_, _, _, _, _, _, _, hE⟩) hfac hden' (hfac'.trans hrf) henv' hargs
        refine ⟨revs1 ++ revs2, ?_, by simp [htr1, htr2], hdS, hfac'.trans hrf⟩
        have hX : EvalCmdViewE S π F (InterpLang.absStore F env.store.get) cmd
            (InterpLang.absStore F store'.get)
            ((revs1 ++ revs2).map (REvent.abs F)) := by
          rw [List.map_append]
          rcases hout with ⟨hno, bevs, hbody, hevs⟩ | ⟨ho, hhavoc, hevs⟩
          · have h := EvalCmdViewE.ext_call_sem hk hE hπ hinst hno hentry hbody hexit
            rw [hevs]
            simp only [List.append_assoc] at h ⊢
            exact h
          · have h := EvalCmdViewE.ext_call_contract_sem hk hE hπ hinst ho hentry hhavoc hexit
            rw [hevs]
            simp only [List.append_assoc] at h ⊢
            exact h
        exact .step_cmd ⟨hX, fun _ => hcall.1, fun _ => hcall.2, definesWithin_trans hdefs1 hdefs2⟩
    · simp at hrun

/-- Per-command soundness of `stepCmdWith` at every fuel and call-depth budget, with the step's
    fuel argument ignored: `ArmSound` under the hypotheses of `stepCmdWith_armSound`. -/
theorem stepCmdWith_arm [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr} (hv : ViewSound obs view S)
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (hEval : BoundedEvalSoundAt P F) :
    ∀ k d, ArmSound obs (fun _ e c => stepCmdWith view around π mode d k e c) S π F := by
  intro k
  induction k with
  | zero =>
    exact fun d => stepCmdWith_arm_step obs hv haround π mode hprocs hmode hEval 0 d nofun
  | succ k ih =>
    exact fun d => stepCmdWith_arm_step obs hv haround π mode hprocs hmode hEval (k + 1) d
      fun _ d' hk hd => by cases hk; exact ih d'

/-- **Per-command soundness of the call-aware stepper.** For a view that agrees with `S`
    (`ViewSound`), an `AroundOk` wrapper `around`, a callee table every runnable procedure of
    which passes `ProcOkV` (`ProcsOkV`), and a call mode `mode` that runs as its contract exactly
    the opaque callees (`ModeOk`), `stepCmdWith view around π mode d` meets `ArmSound` at every
    factory at which the bounded evaluator is sound. -/
theorem stepCmdWith_armSound [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr} (hv : ViewSound obs view S)
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (hEval : BoundedEvalSoundAt P F) (d : Nat) :
    ArmSound obs (stepCmdWith view around π mode d) S π F :=
  fun fuel => stepCmdWith_arm obs hv haround π mode hprocs hmode hEval fuel d fuel

/-- **Per-step soundness of the statement engine over `stepCmdWith`**, under the hypotheses of
    `stepCmdWith_armSound`: every successful `stepInterp` step is one reference step over
    `EvalCommandVT S π` and keeps `CfgInvV S` (`StepInterpSoundGeneric`). -/
theorem stepCmdWith_stepSound [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr} (hv : ViewSound obs view S)
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (d : Nat) :
    StepInterpSoundGeneric obs (stepCmdWith view around π mode d) (EvalCommandVT S π)
      (CfgInvV S) :=
  stepSoundV obs S π _ fun _ hEval =>
    stepCmdWith_armSound obs hv haround π mode hprocs hmode hEval d

/-- **Whole-run soundness of the statement engine over `stepCmdWith`**, under the hypotheses of
    `stepCmdWith_armSound`: a successful `runInterp` run is a reference run over
    `EvalCmdViewE S π` emitting exactly the recorded events (`RunInterpSound`). -/
theorem stepCmdWith_runInterp_sound [InterpLangBool P] (obs : InterpObs P m)
    {view : CmdT → CmdView P CmdT Hdr m} {S : CmdSem P CmdT Hdr} (hv : ViewSound obs view S)
    {around : CmdT → m (IConfig P CmdT) → m (IConfig P CmdT)} (haround : AroundOk obs around)
    (π : String → Option (Procedure P CmdT Hdr)) (mode : CallMode) (hprocs : ProcsOkV S π)
    (hmode : ModeOk S π mode) (d : Nat) :
    RunInterpSound P m obs (stepCmdWith view around π mode d) (EvalCmdViewE S π) (CfgInvV S) :=
  fun _ _ _ _ _ _ _ _ hD hrun hf hE hi =>
    (runInterp_sound_generic obs _ _ _ (stepCmdWith_stepSound obs hv haround π mode hprocs hmode d)
      _ _ _ _ _ _ _ _ hD hrun hf hE hi).imp fun _ => .imp fun _ => .imp fun _ =>
        .imp_left (stepStarVT_toE S π)

/-- **Whole-run soundness of the CFG driver.** For a stepper meeting `ArmSound` at a well-formed
    factory `F` at which the bounded evaluator is sound, a successful `runInterpCFG` run from a
    configuration that denotes at `F` and meets `CFGCfgInvV S F` is a reference CFG run over
    `EvalCmdViewE S π`, emitting exactly the recorded events, to a configuration that denotes at
    `F`. -/
theorem runInterpCFG_sound_of_arm [InterpLangBool P] (obs : InterpObs P m)
    {S : CmdSem P CmdT Hdr} (π : String → Option (Procedure P CmdT Hdr))
    {step : StepCmdM P CmdT m} (harm : ArmSound obs step S π F)
    (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F) (n : Nat)
    {c c' : ICFGConfig String CmdT P} {cfgr : obs.Cfg} {st st' : obs.St}
    (hd : c.Denoting F) (hinv : CFGCfgInvV S F (c.abs F))
    (h : obs.run (runInterpCFG (StepCmdM.toStore step) n c) cfgr st = (.ok c', st')) :
    ∃ revs : List (IEvent P), obs.trace st' = revs.reverse ++ obs.trace st
      ∧ StepCFGStarE P (EvalCmdViewE S π) (c.abs F) (revs.map (REvent.abs F)) (c'.abs F)
      ∧ c'.Denoting F :=
  (cfg_run_soundV obs S π hEval _ harm hfac hd hinv h).imp fun _ ⟨ht, R, hd'⟩ =>
    ⟨ht, stepCFGStarVT_toE S π R, hd'⟩

end Calls

end -- public section

end Imperative

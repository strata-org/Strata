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

/-! # Call-aware replay soundness against the reference event semantics

The engine's `.call` arm (`Calls.stepCmd`) computes its callee frame, its argument
values and its write-back with *executable* functions; the reference rule
`Calls.EvalCmdExtE.call_sem` states the same things *relationally*
(`EvalExpressions`, `ReadValues`, `InitCallFrame` / `CallEntry`, `UpdateStates` /
`CallExit`).  The bridges from each executable function to its relation are in
`InterpreterCallProps.lean`.  This module proves the per-step and whole-run soundness of the
call-aware driver `runCallInterp`, certifies the events of interrupted runs, and proves replay
soundness against `StepStmtExtStarE`, generically in the expression language `P`.  A callee
runs its structured body as a statement run (`runCallee`), sound against the structured
`BigStepE` rule; a callee with a CFG body is refused.

Key definitions:
* `CallLangWF P`: the expression-language facts the proofs use;
* `ProcsOk π` (every procedure is well-formed) and `CfgInv π` (the configuration invariant):
  the side conditions of the soundness theorems;
* `EvalCommandET`: the reference call-aware command relation restricted to steps that keep a
  typed store typed;
* `CallEnvOk`: the store invariant of a call-aware run (well-formed and typed store);
* `InterruptedSound`: a certificate for the events of a run that may stop inside a call;
* `TargetNotInProcs π target`: the target assertion occurs in no procedure of `π`, and every
  procedure of `π` has a structured body;
* `ReplaySound`, `ReplaySoundFeasible`: the replay-soundness statements.

Key theorems:
* `callStepInterpSound`, `call_cmd_arm`: per-step soundness of the call-aware stepper;
* `call_runInterp_sound`, `call_replayRun_sound`: whole-run soundness of successful runs;
* `call_replayRun_interruptedSound`: the events of every replay run, throwing ones included,
  are certified by `InterruptedSound`;
* `interruptedSound_flatPrefix_of_targetReached`: under `TargetNotInProcs`, a certified event
  that reaches the target lies in a flat reference run;
* replay soundness: `call_replaySound_of_ok`, `call_replaySound_general`, `call_replaySound`,
  `call_replaySound_feasible`, `call_replaySound_interruptOn`.

Each bridge needs a side condition, because on that axis the relation demands
strictly more than the function checks:

* `EvalExpressions` carries `SemanticStore.varsDefined (· ∈ getFvars e) σ` per argument expression;
  `evalBoundedList` only requires the expression to reduce to a value.
* `ReadValues` requires each value read to be a value in the factory
  (`HasVal.value`); `readVarList` returns whatever the store holds.
* `InitCallFrame` is a fold of `InitState`, each step of which requires its target
  slot *unbound*; `bindPositional` overwrites blindly, so the callee's formal names
  must be pairwise distinct.
* `CallExit`'s `UpdateStates` is a fold of `UpdateState`, each step of which
  requires its target slot *already bound*; `bindPositional` does not check. -/

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

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CallLangWF P]
  [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- **Soundness of call-aware replay**: if the replay at call-depth limit `maxCallDepth` classifies
    the counterexample `genuine`, some run of the reference relation `StepStmtExtStarE π` from its
    configuration records an event failing the target assertion (`assertFailureHalt`). -/
@[expose] def ReplaySound (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (F : P.Factory) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuine π target fuel cex maxCallDepth →
    ∃ (revs : List (IEvent P)) (final : Config P (CmdExt P)),
      StepStmtExtStarE π (cex.cfg.abs F) (revs.map (REvent.abs F)) final ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true

/-- **Feasibility-aware soundness**: if the replay classifies the counterexample
    `genuineEnforced` (genuine, with every assumption on the path enforced), some reference run
    from its configuration records an event failing the target assertion, and every `.assume`
    event it records evaluates to `tt` (`PathFeasible`). -/
@[expose] def ReplaySoundFeasible (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (F : P.Factory) (cex : CexA P (CmdExt P))
    (maxCallDepth : Nat := defaultMaxCallDepth) : Prop :=
  genuineEnforced π target fuel cex maxCallDepth →
    ∃ (revs : List (IEvent P)) (final : Config P (CmdExt P)),
      StepStmtExtStarE π (cex.cfg.abs F) (revs.map (REvent.abs F)) final ∧
      (∃ ev ∈ revs, assertFailureHalt target fuel ev = true) ∧
      PathFeasible fuel revs

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

/-! ## The flat side conditions: per command, per procedure, per program

`CmdCallOk` (one command), `ProcOk` (one procedure), `ProcsOk` (every procedure of `π`), and the
configuration invariant `CfgInv` the `.call` step obligation runs under. -/

/-- Per-command check on a call site: its input actuals are all `StrictActual` and all
    `TypedActual` (the latter keeps the callee frame typed, see `CallLangWF`), and its result
    variables are distinct (as the call rule's write-back `CallExit` requires).  Base commands
    carry no condition.  The output arity (`|getLhs args| = |outputs.keys|`) is not part of the
    check: the engine checks it itself and throws `programCallOutputArityMismatch`, a throw
    certified sound. -/
@[expose] def CmdCallOk (_π : String → Option (Procedure P (CmdExt P) Hdr)) : CmdExt P → Bool
  | .cmd _ => true
  | .call _ args _ =>
    (getInputExprs args).all StrictActual && (getInputExprs args).all TypedActual &&
      decide (CallArg.getLhs args).Nodup

/-- Shallow check on one procedure, mentioning no calls: its frame-binding formals
    are pairwise distinct (what `InitCallFrame` needs), and a structured body is
    exit-covered and has well-formed call sites everywhere. -/
@[expose] def ProcOk (π : String → Option (Procedure P (CmdExt P) Hdr))
    (p : Procedure P (CmdExt P) Hdr) : Prop :=
  (ProcedureHeader.inputParams (P := P) p.header ++ outputOnlyParams (P := P) p.header).Nodup ∧
  ∀ ss, p.body = .structured ss →
    Block.exitsCoveredByBlocks (P := P) (CmdT := CmdExt P) [] ss ∧
    Block.allCmds (P := P) (CmdCallOk π) ss = true

/-- Flat program-level check: every procedure `π` resolves satisfies `ProcOk`.
    No recursion: `ProcOk` says nothing about the *callees* of the calls inside a
    body, only that each such call site is locally well-formed. -/
@[expose] def ProcsOk (π : String → Option (Procedure P (CmdExt P) Hdr)) : Prop :=
  ∀ n p, π n = some p → ProcOk π p

/-- The configuration invariant call-aware replay soundness runs under: a value-only store
    (`Config.storeWellDefined`), well-formed call sites everywhere (`CmdCallOk π`), and typed
    stores (`Config.storeTyped`).

    Exit coverage is deliberately *not* a conjunct.  It is the one condition whose
    label list grows when execution descends into a labeled block, so it does not
    project from a `.block` configuration into its inner one and cannot be part of a
    fixed configuration invariant.  A `.call` step needs it only to know the callee
    body's run did not end `.exiting`, and there it is transported along that run's
    own reference derivation. -/
@[expose] def CfgInv (π : String → Option (Procedure P (CmdExt P) Hdr))
    (c : Config P (CmdExt P)) : Prop :=
  Config.storeWellDefined (P := P) c ∧
  Config.allCmds (P := P) (CmdCallOk π) c ∧
  Config.storeTyped (P := P) c

/-- The call-aware reference command relation restricted to steps that keep a typed
    store typed.  The engine's soundness argument runs against this relation, so
    that `Config.storeTyped` transports along the reference steps it builds: the
    reference `call_sem` writes back values `ReadValues` only knows to be values,
    while the engine's own callee run shows they are typed.  Every derivation of it
    is a derivation of `EvalCmdExtE`. -/
@[expose] def EvalCommandET (π : String → Option (Procedure P (CmdExt P) Hdr))
    : EvalCmdParamE P (CmdExt P) (Event P) :=
  fun f σ c σ' evs => EvalCmdExtE π f σ c σ' evs ∧ (StoreTyped f σ → StoreTyped f σ')

/-- The store invariant a call-aware run carries, at a fixed factory: a well-formed (value-only)
    store and a typed store. -/
@[expose] def CallEnvOk (fac : P.Factory) (σ : SemanticStore P) : Prop :=
  WellFormedStore σ fac ∧ StoreTyped fac σ

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A run of the typed-step relation is a run of `EvalCmdExtE`. -/
private theorem stepStarET_toE (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCommandET π) c evs c') :
    StepStmtStarE P (EvalCmdExtE π) c evs c' := h.imp fun _ _ _ _ _ => And.left

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A step of the typed-step relation is a step of `EvalCmdExtE`. -/
theorem stepET_toE (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtE P (EvalCommandET π) c evs c') :
    StepStmtE P (EvalCmdExtE π) c evs c' := h.imp fun _ _ _ _ _ => And.left

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A reference call-aware command evaluation (`EvalCmdExtE`) defines only the binder of an
    `init`: a call's write-back (`CallExit`) updates already defined slots only. -/
theorem evalCmdExtE_cmdDefsSound (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CmdDefsSound (EvalCmdExtE π) := by
  rintro _ _ _ _ _ (h | ⟨_, _, _, ⟨_, _, _, hup, -⟩⟩) x hx
  · exact evalCmdE_cmdDefsSound _ _ _ _ _ h x hx
  exact .inl (UpdateStatesDefMonotone' (vs := [x]) (fun _ hv => List.mem_singleton.1 hv ▸ hx) hup
    x (List.mem_singleton_self x))

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A typed call-aware command evaluation (`EvalCommandET`) defines only the binder of an
    `init`. -/
private theorem evalCommandET_cmdDefsSound (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CmdDefsSound (EvalCommandET π) := fun _ _ _ _ _ h =>
  evalCmdExtE_cmdDefsSound π _ _ _ _ _ h.1

/-! ## `CfgInv` is preserved along the reference relation -/

omit [DecidableEq P.Expr] in
/-- A reference command step leaves a value-only store (a call's write-back writes exactly
    the values `ReadValues` read out of the callee's final store). -/
private theorem evalCommandE_wellFormedStore
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {emitted : Trace P}
    (h : EvalCmdExtE π fac σ c σ' emitted) (hsv : WellFormedStore σ fac) :
    WellFormedStore σ' fac := by
  cases h <;> grind [CallExit, wellFormedStore_updateStates, readValues_values,
      evalCmdE_storeWellDefined (P := P), CallLangWF.evalVal]

omit [DecidableEq P.Expr] in
/-- `CfgInv` transports along one reference step. -/
private theorem cfgInv_stepE
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtE P (EvalCommandET π) c evs c')
    (hinv : CfgInv π c) : CfgInv π c' :=
  let ⟨hstore, hall, htyped⟩ := hinv
  have hE := stepET_toE π h
  ⟨Config.storeWellDefined_stepE_of (evalCommandE_wellFormedStore π) hE hstore,
    stepStmtE_preserves_allCmds _ hE hall,
    Config.storeTyped_stepE (·.2) h htyped⟩

omit [DecidableEq P.Expr] in
/-- `CfgInv` transports along a whole reference run. -/
private theorem cfgInv_stepStarE
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCommandET π) c evs c')
    (hinv : CfgInv π c) : CfgInv π c' := by induction h <;> grind [cfgInv_stepE]

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- A reference run leaves the factory alone. -/
private theorem stepStarE_factory
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) c evs c') :
    c'.getEnv.factory = c.getEnv.factory := (starE_preserves_factory h).symm

/-! ## The call-aware per-step obligation

`StepInterpSoundGeneric` for the call-aware stepper, from its `.cmd` arm (`callStepSound_of_arm`).
The arm is a hypothesis indexed by `kf : Nat → Nat`, so it applies both to the fuel-baked
callee-body stepper and to the top-level engine. -/

section CallArm

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CfgInv` projects into the inner configuration of a `.seq`. -/
private theorem cfgInv_seq (π : String → Option (Procedure P (CmdExt P) Hdr))
    (inner : Config P (CmdExt P)) (ss : List (Stmt P (CmdExt P)))
    (h : CfgInv π (.seq inner ss)) : CfgInv π inner :=
  let ⟨hstore, hall, htyped⟩ := h
  ⟨hstore, hall.1, htyped⟩

omit [DecidableEq P.Expr] [HasOldIdent P] [ProcedureHeader P Hdr] in
/-- `CfgInv` projects into the inner configuration of a `.block`. -/
private theorem cfgInv_block (π : String → Option (Procedure P (CmdExt P) Hdr))
    (l : Option String) (σ : SemanticStore P) (inner : Config P (CmdExt P))
    (h : CfgInv π (.block l σ inner)) : CfgInv π inner :=
  let ⟨hstore, hall, htyped⟩ := h
  ⟨hstore.2, hall, htyped.2⟩

omit [DecidableEq P.Expr] in
/-- A `.call` whose marshalling succeeded, from a configuration with a well-formed factory
    (`FactoryWF`) satisfying `CfgInv π`, satisfies `CallEntry`, and its entry frame is a
    well-formed, typed store (`CallEnvOk`). -/
private theorem callEntry_ok (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    {n : String} {args : List (CallArg P)} {md : MetaData P} {F : P.Factory} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {k : Nat} {i o : List P.Expr}
    (hEval : BoundedEvalSoundAt P F)
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (hinv : CfgInv π (.stmt (.cmd (CmdExt.call n args md)) (env.abs F))) (hπ : π n = some p)
    (hi : evalBoundedList k env.factory env.store.get (getInputExprs args) = some i)
    (hil : ¬i.length ≠ (ProcedureHeader.inputParams (P := P) p.header).length)
    (ho : readVarList env.store.get (CallArg.getOutArgs args) = some o)
    (hol : ¬o.length ≠ (outputOnlyParams (P := P) p.header).length) :
    ∃ vi vo, List.Rel₂ (InterpLang.Denotes F) i vi ∧ List.Rel₂ (InterpLang.Denotes F) o vo ∧
    CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo) ∧
    CallEnvOk F (callEntryStore p vi vo) ∧ RStore.Denoting F (callEntryStore p i o) ∧
    InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo := by
  obtain ⟨hstore, hall, htyped⟩ := hinv
  obtain ⟨hnd, -⟩ := hprocs n p hπ
  simp only [Config.allCmds, Stmt.allCmds, CmdCallOk, Bool.and_eq_true, List.all_eq_true] at hall
  rw [hrf] at hi
  have hvar := hfac.2.1
  obtain ⟨vi, hreli, hE⟩ :=
    evalExpressions_of_evalBoundedList_strict _ _ hEval _ hden hvar hstore _ _ hall.1.1 hi
  obtain ⟨vi', hreli', htyi⟩ :=
    typed_of_evalBoundedList _ _ hEval _ hden hvar hstore htyped _ _ hall.1.2 hi
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

omit [LawfulMonad m] in
/-- **Per-step soundness of the call-aware engine at call-depth budget `d` and stepper fuel
    `kf fuel`.** Assume every successful command step `stepCmd π d (kf fuel)` from a configuration
    with a well-formed factory (`FactoryWF`) satisfying the invariant `CfgInv π` (the replay
    invariant on the stores and the call sites) is one reference step over `EvalCommandET π`
    recording exactly its events. Then every successful `stepInterp` step over
    `stepCmd π d (kf fuel)` from a non-terminal, non-exiting such configuration is one reference
    `StepStmtE` step over `EvalCommandET π` that records exactly the step's events and reaches a
    configuration satisfying `CfgInv π` (`StepInterpSoundGeneric`). It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callStepSound_of_arm [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (d : Nat) (kf : Nat → Nat)
    (harm : ∀ (F : P.Factory) (fuel : Nat) (cmd : CmdExt P) (env : IEnv P)
        (cfg' : IConfig P (CmdExt P)) (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d (kf fuel) env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → BoundedEvalSoundAt P F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F) :
    StepInterpSoundGeneric obs (fun fuel e c => stepCmd π d (kf fuel) e c)
      (EvalCommandET π) (CfgInv π) :=
  stepInterpSoundGeneric_of_arms obs _ _ _ (cfgInv_seq π) (cfgInv_block π)
    (fun F fuel cmd env cfg' cfgr st st' h hf hE ⟨hd, hrf⟩ hi =>
      let ⟨revs, hs, ht, hd'⟩ := harm F fuel cmd env cfg' cfgr st st' h hf hE hd hrf hi
      ⟨⟨revs, hs, ht⟩, hd'⟩)
    (fun _ _ _ => cfgInv_stepE π) (evalCommandET_cmdDefsSound π)

omit [LawfulMonad m] in
/-- **Per-step soundness of the call-aware engine at one factory.** As `callStepSound_of_arm`, for
    a command arm `harm` known at the single factory `F₀` only: the carried invariant adds that the
    configuration's factory is `F₀` (which every reference step keeps). It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callStepSound_at [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (d : Nat) (kf : Nat → Nat) {F₀ : P.Factory}
    (harm : ∀ (fuel : Nat) (cmd : CmdExt P) (env : IEnv P)
        (cfg' : IConfig P (CmdExt P)) (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d (kf fuel) env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F₀ → RStore.Denoting F₀ env.store.get →
        env.factory = InterpLang.rfactory F₀ → CfgInv π (.stmt (.cmd cmd) (env.abs F₀)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F₀)) (revs.map (REvent.abs F₀)) (cfg'.abs F₀)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F₀) :
    StepInterpSoundGeneric obs (fun fuel e c => stepCmd π d (kf fuel) e c)
      (EvalCommandET π) (fun c => CfgInv π c ∧ c.getEnv.factory = F₀) :=
  stepInterpSoundGeneric_of_arms obs _ _ _ (fun _ _ h => ⟨cfgInv_seq π _ _ h.1, h.2⟩)
    (fun _ _ _ h => ⟨cfgInv_block π _ _ _ h.1, h.2⟩)
    (fun _ fuel cmd env cfg' cfgr st st' h hf _ ⟨hd, hrf⟩ ⟨hi, hF⟩ => by
      subst hF
      obtain ⟨revs, hs, ht, hd'⟩ := harm fuel cmd env cfg' cfgr st st' h hf hd hrf hi
      exact ⟨⟨revs, hs, ht⟩, hd'⟩)
    (fun _ _ _ hs hi => ⟨cfgInv_stepE π hs hi.1,
      (stepE_preserves_factory (stepET_toE π hs)).symm.trans hi.2⟩)
    (evalCommandET_cmdDefsSound π)

omit [LawfulMonad m] in
/-- A successful step `stepCmd π d k` of a base command from a configuration with a well-formed
    factory (`FactoryWF`) satisfying the invariant `CfgInv π` (the replay invariant on the stores
    and the call sites) is one reference `StepStmtE` step over `EvalCommandET π` recording exactly
    the step's events. -/
private theorem call_cmd_arm_base (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hEval : BoundedEvalSoundAt P F)
    (k d : Nat) (base : Cmd P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
    (cfgr : obs.Cfg) (st st' : obs.St)
    (hrun : obs.run (stepCmd π d k env (.cmd base)) cfgr st = (.ok cfg', st'))
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (hinv : CfgInv π (.stmt (.cmd (CmdExt.cmd base)) (env.abs F))) :
    ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd (CmdExt.cmd base)) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F := by
  simp only [stepCmd_cmd, InterpObs.run_bind, InterpObs.run_pure] at hrun
  split at hrun <;> simp only [Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  rename_i hb
  rw [hrf] at hb
  obtain ⟨-, -, htyped⟩ := hinv
  obtain ⟨revs, hstep, hd', htr⟩ :=
    obs_stepBaseCmdStore_sound obs _ _ hEval _ _ _ _ _ _ hfac.2.1 hden htyped hb
  exact ⟨revs, .step_cmd ⟨.cmd_sem hstep, evalCmdE_storeTyped hstep⟩, htr, hd', hrf⟩

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every successful command step
    `stepCmd π d k` from a configuration with a well-formed factory (`FactoryWF`) satisfying the
    invariant `CfgInv π` (the replay invariant on the stores and the call sites) is one reference
    `EvalCommandET π` step recording its events. Then a successful callee-body run of `runInterp` at
    call-depth budget `d` and stepper fuel `k` from a configuration `.stmt (.block "" ss #[]) E`
    satisfying `CfgInv π`, with `E.factory` well-formed, for the structured body `ss` of a procedure
    `π` resolves, ends in a `.terminal` configuration carrying the caller's factory `E.factory`
    whose abstraction (`IConfig.abs`) satisfies `CfgInv π` and is reached by a reference
    `StepStmtStarE` run over `EvalCmdExtE π` that records exactly the run's events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callee_run_ok [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {k d : Nat}
    {E : IEnv P} {fc : IConfig P (CmdExt P)} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (hπ : π n = some p) (hb : p.body = .structured ss)
    (hI : CfgInv π (.stmt (.block "" ss #[]) (E.abs F))) (hfE : FactoryWF (P := P) F)
    (hdE : RStore.Denoting F E.store.get) (hrE : E.factory = InterpLang.rfactory F)
    (h : obs.run (runInterp (fun _ e c => stepCmd π d k e c) k (.stmt (.block "" ss #[]) E)) cfgr st
        = (.ok fc, st')) :
    ∃ σ', fc = .terminal ⟨σ', E.factory⟩ ∧ fc.Denoting F ∧ CfgInv π (fc.abs F) ∧
      ∃ revs : List (IEvent P), StepStmtStarE P (EvalCmdExtE π)
        (.stmt (.block "" ss #[]) (E.abs F)) (revs.map (REvent.abs F)) (fc.abs F) ∧
          obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨revs, R, hdf, -, htr⟩ := runInterp_sound_tracked obs _ _ _
    (callStepSound_at obs π d (fun _ => k) IH) F k _ fc cfgr st st' h hfE hEval ⟨hdE, hrE⟩
    ⟨hI, rfl⟩ trivial
  obtain ⟨⟨σ', f⟩, rfl⟩ := (obs_runInterp_ok_final obs _ _ _ _ _ _ _ h).resolve_right
    fun ⟨_, _, hfc⟩ => absurd (hfc ▸ R) (exitsCoveredByBlocks_noEscapeE _ (.block "" ss #[])
      ((exitsCoveredByBlocks_weaken [] [""] nofun).2 ss ((hprocs n p hπ).2 ss hb).1) _ _ _)
  obtain rfl : f = E.factory := hdf.2.trans hrE.symm
  exact ⟨_, rfl, hdf, cfgInv_stepStarE π R hI, revs, stepStarET_toE π R, htr⟩

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every successful command
    step `stepCmd π d k` from a configuration with a well-formed factory (`FactoryWF`) satisfying
    `CfgInv π` is one reference step over `EvalCommandET π` recording its events (`IH`).  Then a
    successful callee body run `runCallee` of a procedure `π` resolves, over `stepCmd π d k` at
    driver fuel `k`, from a well-formed, typed entry frame `σ` (`CallEnvOk`) at a well-formed
    factory `fac`, is a reference body execution `BigStepE` from `⟨σ, fac⟩` to the
    returned store recording exactly the run's events, and the returned store is well-formed
    and typed. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem runCallee_ok [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {k d : Nat}
    {σ σf : RStore P} {cfgr : obs.Cfg} {st st' : obs.St}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (hπ : π n = some p) (hfac : FactoryWF (P := P) F) (hd : RStore.Denoting F σ)
    (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runCallee (fun _ e c => stepCmd π d k e c) n p.body (InterpLang.rfactory F) k σ)
        cfgr st = (.ok σf, st')) :
    ∃ revs : List (IEvent P), BigStepE π p.body ⟨InterpLang.absStore F σ, F⟩
        (InterpLang.absStore F σf) (revs.map (REvent.abs F)) ∧
      CallEnvOk F (InterpLang.absStore F σf) ∧ RStore.Denoting F σf
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨-, hS⟩ := hprocs n p hπ
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
        callee_run_ok obs π hprocs hEval (E := ⟨.ofStore σ, InterpLang.rfactory F⟩) IH hπ hb
        (hE ▸ ⟨henv.1, by simpa [Config.allCmds, Stmt.allCmds] using (hS ss hb).2, henv.2⟩)
        hfac (by simpa using hd) rfl hrun
      simp only [obs.run_pure, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨revs, .structured (hE ▸ R), ⟨hwf, hty⟩, hdf.1, htr⟩
    · simp at h
  | cfg g =>
    intro h
    simp [runCallee, obs.run_throw] at h

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every successful command step
    `stepCmd π d' k'` from a configuration with a well-formed factory (`FactoryWF`) satisfying the
    invariant `CfgInv π` (the replay invariant on the stores and the call sites) is one reference
    `StepStmtE` step over `EvalCommandET π` recording exactly its events. Then so is a successful
    step `stepCmd π (d' + 1) (k' + 1)` of a `.call` from such a configuration; its callee body runs
    at call-depth budget `d'` and stepper fuel `k'`. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem call_cmd_arm_call [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (k' d' : Nat)
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d' k' env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (n : String) (args : List (CallArg P)) (md : MetaData P)
    (env : IEnv P) (cfg' : IConfig P (CmdExt P))
    (cfgr : obs.Cfg) (st st' : obs.St)
    (hrun : obs.run (stepCmd π (d' + 1) (k' + 1) env (.call n args md)) cfgr st = (.ok cfg', st'))
    (hfac : FactoryWF (P := P) F) (hden : RStore.Denoting F env.store.get)
    (hrf : env.factory = InterpLang.rfactory F)
    (hinv : CfgInv π (.stmt (.cmd (CmdExt.call n args md)) (env.abs F))) :
    ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd (CmdExt.call n args md)) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F := by
  repeat' (first
    | split at hrun
    | simp only [stepCmd, ne_eq, List.forM_eq_forM, ite_not, InterpObs.run_bind,
        InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq,
        false_and] at hrun)
  obtain ⟨rfl, rfl⟩ := hrun
  rename_i _ p hπ _ _ _ _ i hi hil _ o ho hol hlen _ olds holds _ _ _ hpre _ σf _ hbody _ _ _
    hpost _ w hw hwb
  rw [hrf] at hbody hpre hpost hwb
  obtain ⟨vi, vo, hreli, hrelo, hE, hen, hdEntry, habsEntry⟩ :=
    callEntry_ok π hprocs hEval hfac hden hrf hinv hπ hi (· hil) ho (· hol)
  obtain ⟨_, _, hargs, hread, hinit⟩ := hE
  obtain ⟨vo', -, hro⟩ := readVarList_absStore_of_denoting hden _ _ ho
  obtain ⟨bevs, B, ⟨hwf, hty⟩, hdf, t⟩ :=
    runCallee_ok obs π hprocs hEval IH hπ hfac hdEntry (habsEntry ▸ hen) hbody
  rw [habsEntry] at B
  obtain ⟨vw, hrelw, hrw⟩ := readVarList_absStore_of_denoting hdf _ _ hw
  have M := readValues_of_readVarList _ _ hwf _ _ hrw
  have hlw : (CallArg.getLhs args).length = vw.length := hlen.trans (ReadValuesLength M)
  have hlhs : (CallArg.getLhs args).Nodup := by
    have hall := hinv.2.1
    simp only [Config.allCmds, Stmt.allCmds, CmdCallOk, Bool.and_eq_true, decide_eq_true_eq]
      at hall
    exact hall.2
  have hwt := storedTy_of_writeBackTyped hden hinv.2.2 _ _ _ _ holds hlw hrelw
    (by simpa using hwb)
  have habsW := absStore_bindPositional env.store.get (CallArg.getLhs args) hrelw
  simp only [IConfig.abs, IEnv.abs, IConfig.Denoting, IStore.get_bindPositional, habsW]
  refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
      (checksAtCall md p.spec.preconditions) ++ bevs ++
      rDefaultAssertEvents (InterpLang.rfactory F) σf p.spec.postconditions,
    .step_cmd ⟨?_, (storeTyped_bindPositional _ _ _ · (typed_of_readVarList hty _ _ hrw))⟩,
    ?_, denoting_bindPositional _ hden hrelw, hrf⟩
  · simp only [List.map_append, rDefaultAssertEvents_abs, habsEntry]
    exact .call_sem hπ ⟨_, _, hargs, hread, hinit⟩ B ⟨hlhs, vw, M,
      updateStates_bindPositional _ _ _ hlw (getLhs_defined args hargs hro), hwt⟩
  · simp [obs_forM_emit obs _ _ _ _ _ hpost, t, obs_forM_emit obs _ _ _ _ _ hpre]

omit [LawfulMonad m] in
/-- At every stepper fuel `k` and call-depth budget `d`, if every procedure of `π` is well-formed
    (`ProcsOk π`: distinct frame formals, and a structured body that is exit-covered and has only
    well-formed call sites), a successful step `stepCmd π d k` of a command (base command or
    `.call`) from a configuration with a well-formed factory (`FactoryWF`) satisfying the invariant
    `CfgInv π` (the replay invariant on the stores and the call sites) is one reference `StepStmtE`
    step over `EvalCommandET π`, to the configuration the result stands for (`IConfig.abs`),
    recording exactly the step's events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem call_cmd_arm [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F) :
    ∀ (k d : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
      (cfgr : obs.Cfg) (st st' : obs.St),
      obs.run (stepCmd π d k env cmd) cfgr st = (.ok cfg', st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F := fun
  | k, d, .cmd _ => call_cmd_arm_base obs π hEval k d _
  | 0, _, .call .. => by simp [stepCmd]
  | _ + 1, 0, .call .. => by simp [stepCmd]
  | k + 1, d + 1, .call .. =>
    call_cmd_arm_call obs π hprocs hEval k d (fun _ => call_cmd_arm obs π hprocs hEval k d) _ _ _

omit [LawfulMonad m] in
/-- **Per-step soundness of the call-aware engine.** If every procedure of `π` is well-formed
    (`ProcsOk π`), every successful `stepInterp (stepCmd π d)` step, at every call-depth budget
    `d`, from a non-terminal, non-exiting
    configuration with a well-formed factory (`FactoryWF`) satisfying the invariant `CfgInv π`
    (the replay invariant on the stores and the call sites) is one reference `StepStmtE` step over
    `EvalCommandET π` that records exactly the step's events and reaches a configuration
    satisfying `CfgInv π` (`StepInterpSoundGeneric`). It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem callStepInterpSound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π) (d : Nat) :
    StepInterpSoundGeneric obs (stepCmd π d) (EvalCommandET π) (CfgInv π) :=
  callStepSound_of_arm obs π d id fun F k _ _ _ _ _ _ h hf hE =>
    call_cmd_arm obs π hprocs hE (F := F) k d _ _ _ _ _ _ h hf

omit [LawfulMonad m] in
/-- **Whole-run soundness, monad-generically.**  If every procedure of `π` is well-formed
    (`ProcsOk π`) and the start configuration has a well-formed factory (`FactoryWF`) and satisfies
    the invariant `CfgInv π`, a successful `runCallInterp` run, at every call-depth limit `d`, is a
    reference `StepStmtExtStarE` execution emitting exactly the same events. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
theorem call_runInterp_sound [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π) (d : Nat) :
    RunInterpSound P m obs (stepCmd π d) (EvalCmdExtE π) (CfgInv π) :=
  fun _ _ _ _ _ _ _ _ hD hrun hf hE hi =>
    (runInterp_sound_generic obs _ _ _ (callStepInterpSound obs π hprocs d) _ _ _ _ _ _ _
      _ hD hrun hf hE hi).imp fun _ => .imp fun _ => .imp fun _ => .imp_left (stepStarET_toE π)

end CallArm

/-! ## The interrupted-run certificate (`InterruptedSound`)

The reference relation takes a whole call as one `call_sem` step, so a trace that ends inside a call
has no flat `StepStmtStarE` derivation. `InterruptedSound` certifies such a trace recursively:
`clean` covers a completed run of steps, and the other constructors cover a run that stops inside
the call at its tail (in the precondition events, in the callee body, in the postcondition events,
or at the write-back). -/

/-- **The call is the active redex of a config**, stable under the `.seq _ rest` and
    `.block l σ _` evaluation contexts.  A callee body is `.block "" ss` → `.stmts ss`
    → `.seq (.stmt call env) rest`, so a call is almost never at a *bare* config when it
    is stepped; `CallActive C pn args md env` says peeling seq/block wrappers from `C`
    reaches the bare call `.stmt (.cmd (.call pn args md)) env`.  This is what makes
    `InterruptedSound` closed under those wrappers. -/
inductive CallActive :
    Config P (CmdExt P) → String → List (CallArg P) →
      MetaData P → Env P → Prop where
  | here {pn args md env} :
      CallActive (.stmt (.cmd (.call pn args md)) env) pn args md env
  | seq {inner rest pn args md env} :
      CallActive inner pn args md env → CallActive (.seq inner rest) pn args md env
  | block {inner label σ pn args md env} :
      CallActive inner pn args md env → CallActive (.block label σ inner) pn args md env

/-- Certificate that `evs` is the event trace of a reference run from a configuration, possibly
    stopped inside a call: a flat reference run (`clean`), or a flat run to an active call
    followed by a prefix of that call's events.  The call may stop inside its callee body
    (`inCall`), at the write-back after a completed body (`inCallExit`), or while emitting the
    precondition (`preThrow`) or postcondition (`postThrow`) events. -/
inductive InterruptedSound (π : String → Option (Procedure P (CmdExt P) Hdr))
    :
    Config P (CmdExt P) → Trace P → Prop where
  | clean {start : Config P (CmdExt P)} {evs : Trace P} {mid : Config P (CmdExt P)} :
      StepStmtStarE P (EvalCmdExtE π) start evs mid →
      InterruptedSound π start evs
  | inCall {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
        {bodyStmts : List (Stmt P (CmdExt P))}
      {calleeEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .structured bodyStmts →
      CallEntry env.factory env.store p args σAO →
      InterruptedSound π
        (.stmt (.block "" bodyStmts #[]) (⟨σAO, env.factory⟩ : Env P))
        calleeEvs →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (checksAtCall md p.spec.preconditions) ++ calleeEvs)
  /-- A **completed** callee body whose write-back throws
      (`programCallOutputUndefinedOnReturn`): the body ran to a terminal and both the
      pre- and post-condition events emitted in full, but `CallExit` never fired, so this
      is neither `clean` (no `call_sem` step) nor `inCall` (the body is not still running). -/
  | inCallExit {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
        {bodyStmts : List (Stmt P (CmdExt P))}
      {ρ' : Env P} {bodyEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .structured bodyStmts →
      CallEntry env.factory env.store p args σAO →
      StepStmtStarE P (EvalCmdExtE π)
        (.stmt (.block "" bodyStmts #[]) (⟨σAO, env.factory⟩ : Env P))
        bodyEvs (.terminal ρ') →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO
            (checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ defaultAssertEvents ρ'.factory ρ'.store p.spec.postconditions)
  /-- The interrupt fires **mid-precondition** emit (the target id matches a callee
      precondition clause): the trace carries a *prefix* of the precondition events.
      Reachable only when `emit` throws on the target. -/
  | preThrow {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
        {bodyStmts : List (Stmt P (CmdExt P))}
      {preEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .structured bodyStmts →
      CallEntry env.factory env.store p args σAO →
      preEvs <+: defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions) →
      InterruptedSound π start (outerEvs ++ preEvs)
  /-- The interrupt fires **mid-postcondition** emit, after the body completed: the trace
      carries the full pre-events, the full body events, and a *prefix* of the post-events.
      Reachable only when `emit` throws on the target. -/
  | postThrow {start : Config P (CmdExt P)} {outerEvs : Trace P} {C : Config P (CmdExt P)}
      {env : Env P} {pn : String}
      {args : List (CallArg P)} {md : MetaData P}
      {p : Procedure P (CmdExt P) Hdr} {σAO : SemanticStore P}
        {bodyStmts : List (Stmt P (CmdExt P))}
      {ρ' : Env P} {bodyEvs : Trace P}
      {postEvs : Trace P} :
      StepStmtStarE P (EvalCmdExtE π) start outerEvs C →
      CallActive C pn args md env →
      π pn = some p →
      p.body = .structured bodyStmts →
      CallEntry env.factory env.store p args σAO →
      StepStmtStarE P (EvalCmdExtE π)
        (.stmt (.block "" bodyStmts #[]) (⟨σAO, env.factory⟩ : Env P))
        bodyEvs (.terminal ρ') →
      postEvs <+: defaultAssertEvents ρ'.factory ρ'.store p.spec.postconditions →
      InterruptedSound π start
        (outerEvs ++ defaultAssertEvents env.factory σAO (checksAtCall md p.spec.preconditions)
          ++ bodyEvs ++ postEvs)

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **Closure of `InterruptedSound` under prepending one clean step**: a reference step from
    `cfg` to `cfg'` followed by a certified trace from `cfg'` is a certified trace from `cfg`. -/
private theorem interruptedSound_stepThen
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfg : Config P (CmdExt P)) (evs : Trace P) (cfg' : Config P (CmdExt P)) (rest : Trace P)
    (hstep : StepStmtE P (EvalCmdExtE π) cfg evs cfg')
    (hrest : InterruptedSound π cfg' rest) :
    InterruptedSound π cfg (evs ++ rest) := by
  cases hrest <;> (try simp only [← List.append_assoc]) <;>
    open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallExit, postThrow, preThrow]

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **`InterruptedSound` is closed under the `.seq _ rest` evaluation context**: a certified trace
    from `inner` is a certified trace from `.seq inner rest`. -/
private theorem interruptedSound_seq
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (inner : Config P (CmdExt P)) (rest : List (Stmt P (CmdExt P))) (evs : Trace P)
    (h : InterruptedSound π inner evs) :
    InterruptedSound π (.seq inner rest) evs := by
  cases h <;> open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallExit, postThrow, preThrow, clean, seq_inner_starE]

omit [DecidableEq P.Expr] [CallLangWF P] [InterpLang P] in
/-- **`InterruptedSound` is closed under the `.block l σ _` evaluation context**: a certified
    trace from `inner` is a certified trace from `.block l σ inner`. -/
private theorem interruptedSound_block
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (label : Option String) (σp : SemanticStore P)
    (inner : Config P (CmdExt P)) (evs : Trace P)
    (h : InterruptedSound π inner evs) :
    InterruptedSound π (.block label σp inner) evs := by
  cases h <;> open InterruptedSound in
    solve_by_elim (maxDepth := 12) [inCall, inCallExit, postThrow, preThrow, clean,
      block_inner_starE]

/-- If every procedure of `π` is well-formed (`ProcsOk π`), the Boolean literals denote the Boolean
    values (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), and `start` satisfies the invariant `CfgInv π` at a well-formed factory
    `F` (`FactoryWF`), a successful replay run of `runCallInterp π` from a runtime configuration
    `istart` that denotes `start` under `F` (`IConfig.Denotes`) records runtime events whose images
    (`REvent.abs F`) are exactly the events of a reference run from `start` to the image
    (`IConfig.abs F`) of the returned configuration, and the returned configuration denotes. -/
theorem call_replayRun_sound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (start : Config P (CmdExt P))
    (istart : IConfig P (CmdExt P))
    (hstart : istart.Denotes F start) (final : IConfig P (CmdExt P))
    (cfg : ReplayCfg P) (oracle : List P.Expr)
    (st' : ReplayState P) (d : Nat)
    (hrun : runReplayRun (runCallInterp (m := ReplayM P) π fuel istart d) cfg oracle
        = (.ok final, st'))
    (hfac : FactoryWF (P := P) F) (hinv : CfgInv π start) :
    ∃ revs : List (IEvent P), StepStmtStarE (P := P) (EvalCmdExtE π)
             start (revs.map (REvent.abs F)) (final.abs F) ∧ final.Denoting F ∧
             st'.traceRev = revs.reverse := by
  obtain ⟨_, revs, _, hs, ⟨hd, -, rfl⟩, htr, rfl⟩ := call_runInterp_sound obsReplay π hprocs
    d _ _ _ _ _ _ _ _ hstart hrun hfac hEval hinv
  exact ⟨revs, hs, hd, by simpa [obsReplay] using htr⟩

/-! ## The error discharge: `StepInterpErrSoundInto` into `InterruptedSound` -/

section CallErrDischarge

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

omit [CallLangWF P] [HasOldIdent P] [LawfulMonad m] [HasFvar P] [HasFvars P] in
/-- A run of `resolveGuard`, whatever its outcome, leaves the trace unchanged when a throwing
    `choose` does. -/
private theorem obs_resolveGuard_trace (obs : InterpObs P m)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {fuel : Nat} {env : IEnv P} {g : ExprOrNondet P} {cfgr : obs.Cfg} {st st' : obs.St}
    {q : Except StopReason Bool} (h : obs.run (resolveGuard fuel env g) cfgr st = (q, st')) :
    obs.trace st' = obs.trace st := by
  cases g with
  | det c =>
    simp only [resolveGuard] at h
    split at h
    · split at h <;> simp only [InterpObs.run_pure, InterpObs.branch_stuck, Prod.mk.injEq] at h <;>
        rw [← h.2]
    · simp only [InterpObs.run_throw, Prod.mk.injEq] at h
      rw [← h.2]
  | nondet =>
    simp only [resolveGuard, InterpObs.run_bind] at h
    split at h
    · rename_i hc
      have ht := (obs.choose_sound _ _ _ _ _ _ _ hc).2
      split at h <;> simp only [InterpObs.run_pure, InterpObs.run_throw, Prod.mk.injEq] at h <;>
        rw [← h.2, ht]
    · rename_i hc
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact hchooseErr _ _ _ _ _ _ _ hc

omit [CallLangWF P] [HasOldIdent P] [LawfulMonad m] in
/-- **Error soundness of one step, into a certificate.** Fix an invariant `Inv` on
    configurations and a trace certificate `TraceSound`.  Assume a throwing command step from an
    `Inv` configuration recorded events certified by `TraceSound`; `TraceSound` holds of every
    `StepStmtStarE` trace and is closed under the `.seq`/`.block` evaluation contexts; `Inv`
    projects into the inner configuration of a `.seq`/`.block`; and a throwing `choose` leaves
    the trace unchanged.  Then every throwing `stepInterp stepCmd` step from a non-terminal,
    non-exiting tracked configuration whose abstraction satisfies `Inv` recorded events certified
    by `TraceSound` from that abstraction (`StepInterpErrSoundInto`). -/
private theorem stepInterpErrInto_of_arms (obs : InterpObs P m)
    (stepCmd : StepCmdM P (CmdExt P) m)
    (EvalCmd : EvalCmdParamE P (CmdExt P) (Event P))
    (Inv : Config P (CmdExt P) → Prop)
    (TraceSound : Config P (CmdExt P) → List (Event P) → Prop)
    (hclean : ∀ (start : Config P (CmdExt P)) (evs : List (Event P)) (mid : Config P (CmdExt P)),
        StepStmtStarE P EvalCmd start evs mid → TraceSound start evs)
    (hseqInv : ∀ (inner : Config P (CmdExt P)) (ss : List (Stmt P (CmdExt P))),
        Inv (.seq inner ss) → Inv inner)
    (hblkInv : ∀ (l : Option String) (σ : SemanticStore P)
        (inner : Config P (CmdExt P)),
        Inv (.block l σ inner) → Inv inner)
    (hseqClose : ∀ (inner : Config P (CmdExt P)) (rest : List (Stmt P (CmdExt P)))
        (evs : List (Event P)),
        TraceSound inner evs → TraceSound (.seq inner rest) evs)
    (hblkClose : ∀ (l : Option String) (σ : SemanticStore P)
        (inner : Config P (CmdExt P)) (evs : List (Event P)),
        TraceSound inner evs → TraceSound (.block l σ inner) evs)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    (hcmdErr : ∀ (F : P.Factory) (fuel : Nat) (cmd : CmdExt P) (env : IEnv P)
        (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
        obs.run (stepInterp stepCmd fuel (.stmt (.cmd cmd) env)) cfgr st = (.error r, st') →
        FactoryWF (P := P) F → BoundedEvalSoundAt P F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → Inv (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), TraceSound (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
          ∧ obs.trace st' = revs.reverse ++ obs.trace st) :
    StepInterpErrSoundInto obs stepCmd Inv (fun _ => TraceSound) := by
  intro F fuel c cfgr
  have hW : ∀ k c evs, TraceSound c evs → TraceSound (Config.wrapSeqs c k) evs := by
    intro k c evs h
    induction k with | zero => exact h | succ _ ih => exact hseqClose _ _ _ ih
  have hV : ∀ k c, Inv (Config.wrapSeqs c k) → Inv c := by
    intro k c h
    induction k with | zero => exact h | succ _ ih => exact ih (hseqInv _ _ h)
  have hnil : ∀ (c : Config P (CmdExt P)) (st st' : obs.St), obs.trace st' = obs.trace st →
      ∃ revs : List (IEvent P), TraceSound c (revs.map (REvent.abs F)) ∧
        obs.trace st' = revs.reverse ++ obs.trace st :=
    fun c _ _ h => ⟨[], hclean _ _ _ (.refl _), by simpa using h⟩
  induction c with
  | stmt s env =>
    intro st st' r h _ _ hf hE hd hi _
    cases s with
    | cmd cmd => exact hcmdErr F _ _ _ _ _ _ _ h hf hE hd.1 hd.2 hi
    | ite | loop =>
      simp only [stepInterp, InterpObs.run_bind] at h
      split at h
      · simp only [InterpObs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
      · rename_i hrg
        obtain ⟨-, rfl⟩ := Prod.mk.inj h
        exact hnil _ _ _ (obs_resolveGuard_trace obs hchooseErr hrg)
    | _ =>
      simp only [stepInterp, InterpObs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
  | stmts | terminal | exiting =>
    intro st st' r h hnt hne
    first
      | exact absurd rfl (hnt _)
      | exact absurd rfl (hne _ _)
      | (rename_i ss _
         rcases ss with _ | ⟨_, _ | _⟩ <;> simp [stepInterp] at h)
  | seq inner ss ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> simp [stepInterp] at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp_seq_unfold_gen _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
      InterpObs.run_pure] at h
    split at h
    · cases h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd (hseqInv _ _ hi) ht
    exact ⟨revs, hseqClose _ _ _ hs, htr⟩
  | seqs inner k ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l, e, rfl⟩ <;> cases k <;> simp [stepInterp] at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp] at h
    split at h
    · exact absurd rfl (hdone.1 _)
    · exact absurd rfl (hdone.2 _ _)
    simp only [InterpObs.run_bind] at h
    split at h
    · split at h <;> simp at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd (hV (k + 1) _ hi) ht
    exact ⟨revs, hW (k + 1) _ _ hs, htr⟩
  | block l fr inner ih =>
    intro st st' r h _ _ hf hE hd hi ht
    by_cases hdone : (∃ e, inner = .terminal e) ∨ ∃ l e, inner = .exiting l e
    · rcases hdone with ⟨e, rfl⟩ | ⟨l', e, rfl⟩ <;> simp only [stepInterp] at h
      all_goals (try split at h) <;> simp at h
    simp only [not_or, not_exists] at hdone
    simp only [stepInterp_block_unfold_gen _ _ _ _ _ hdone.1 hdone.2, InterpObs.run_bind,
      InterpObs.run_pure] at h
    split at h
    · cases h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h
    obtain ⟨revs, hs, htr⟩ := ih _ _ _ ‹_› hdone.1 hdone.2 hf hE hd.2 (hblkInv _ _ _ hi) ht.2
    exact ⟨revs, hblkClose _ _ _ _ hs, htr⟩

omit [LawfulMonad m] in
omit [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [CallLangWF P]
    [HasOldIdent P] in
/-- A throwing `forM` of `emit`s recorded a prefix of its events. -/
private theorem obs_forM_emit_err (obs : InterpObs P m)
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (cfgr : obs.Cfg) :
    ∀ (evs : List (IEvent P)) (st st' : obs.St) (r : StopReason),
      obs.run (evs.forM (InterpEffects.emit (P := P))) cfgr st = (.error r, st') →
      ∃ pref, pref <+: evs ∧ obs.trace st' = pref.reverse ++ obs.trace st := fun evs => by
  induction evs <;> intro st st' r h <;>
    simp_all only [List.forM_eq_forM, List.forM_nil, InterpObs.run_pure, Prod.mk.injEq,
      reduceCtorEq, false_and, List.forM_cons, InterpObs.run_bind]
  rename_i a l ih
  split at h
  · obtain ⟨w, hw⟩ := ih _ _ _ h
    exact ⟨a :: w, by grind⟩
  exact ⟨[a], by grind⟩

omit [CallLangWF P] [LawfulMonad m] in
/-- A throwing base-command step is certified `clean` by a flat reference derivation. -/
private theorem obs_stepCmd_base_err (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {k d : Nat} {env : IEnv P} {base : Cmd P} {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (h : obs.run (stepCmd π d k env (.cmd base)) cfgr st = (.error r, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (CmdExt.cmd base)) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  rcases base with ⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _ | _ | _
  rotate_left 4
  iterate 3
    simp only [stepCmd_cmd, stepBaseCmdStore, Cmd.rEmittedEvents, List.forM_eq_forM,
      List.forM_cons, List.forM_nil, obs.run_bind, obs.run_pure] at h
    generalize hE : obs.run (InterpEffects.emit (P := P) _) cfgr st = q at h
    rcases q with ⟨_ | _, s⟩ <;> simp only [Prod.mk.injEq, reduceCtorEq, false_and] at h
    obtain ⟨-, rfl⟩ := h
    have hs : (obs.run _ cfgr st).2 = s := congrArg Prod.snd hE
    subst hs
    refine ⟨[?_], ?_, ?_⟩
    all_goals try (rw [hemitStep]; rfl)
    exact .clean (StepStmtStarE.single (StepStmtE.step_cmd (EvalCmdExtE.cmd_sem (by constructor))))
  all_goals
    simp only [stepCmd_cmd, stepBaseCmdStore] at h
    (repeat' first | split at h | simp only [obs.run_bind, obs.run_pure, obs.run_throw] at h)
  all_goals cases h
  all_goals
    refine ⟨[], .clean (.refl _), ?_⟩
    grind [→ obs.choose_sound]

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), and every throwing command step
    `stepCmd π d k` from a configuration with a well-formed factory (`FactoryWF`) satisfying the
    invariant `CfgInv π` (the replay invariant on the stores and the call sites) recorded events
    certified by `InterruptedSound π` (the events of a reference run, possibly stopped inside a
    call), and a throwing `choose` leaves the trace unchanged. Then a throwing callee-body run of
    `runInterp` at call-depth budget `d` and stepper fuel `k` from a configuration
    `.stmt (.block "" ss #[]) E` satisfying `CfgInv π`, at a well-formed factory `E.factory`,
    recorded events certified by `InterruptedSound π` from that configuration. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem callee_run_err [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {k d : Nat} {ss : List (Stmt P (CmdExt P))} {E : IEnv P} {cfgr : obs.Cfg} {st st' : obs.St}
    {r : StopReason}
    (ih : ∀ (cmd : CmdExt P) (env : IEnv P) (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
      obs.run (stepCmd π d k env cmd) cfgr st = (.error r, st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hI : CfgInv π (.stmt (.block "" ss #[]) (E.abs F))) (hfE : FactoryWF (P := P) F)
    (hdE : RStore.Denoting F E.store.get) (hrE : E.factory = InterpLang.rfactory F)
    (h : obs.run (runInterp (fun _ e c => stepCmd π d k e c) k (.stmt (.block "" ss #[]) E)) cfgr st
        = (.error r, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.block "" ss #[]) (E.abs F))
        (revs.map (REvent.abs F))
      ∧ obs.trace st' = revs.reverse ++ obs.trace st :=
  runInterp_traceSound_generic obs _ (EvalCommandET π) _ (fun _ => InterruptedSound π)
    (fun _ _ _ _ hstar => .clean (stepStarET_toE π hstar))
    (fun _ _ _ _ _ hs hr => interruptedSound_stepThen π _ _ _ _ (stepET_toE π hs) hr)
    (callStepSound_at obs π d (fun _ => k) fun _ => call_cmd_arm obs π hprocs hEval k d)
    (stepInterpErrInto_of_arms obs _ (EvalCommandET π) _ _
      (fun _ _ _ hstar => .clean (stepStarET_toE π hstar))
      (fun _ _ h => ⟨cfgInv_seq π _ _ h.1, h.2⟩) (fun _ _ _ h => ⟨cfgInv_block π _ _ _ h.1, h.2⟩)
      (interruptedSound_seq π) (interruptedSound_block π) hchooseErr
      fun _ _ cmd env cfgr st st' r h hf _ hd hrf ⟨hi, hF⟩ => by
        subst hF
        exact ih cmd env cfgr st st' r h hf hd hrf hi)
    F k _ cfgr st st' _ h hfE hEval ⟨hdE, hrE⟩ ⟨hI, rfl⟩ trivial

omit [LawfulMonad m] in
/-- Assume every procedure of `π` is well-formed (`ProcsOk π`), every successful step
    `stepCmd π d k` from a configuration with a well-formed factory satisfying `CfgInv π` is one
    reference step over `EvalCommandET π` (`IH`), every throwing one records events certified by
    `InterruptedSound π` (`IHerr`), and a throwing `choose` leaves the trace unchanged.  Then a
    throwing callee body run `runCallee` of a procedure `π` resolves with the structured body
    `ss`, over `stepCmd π d k` at driver fuel `k`, from a well-formed, typed entry frame `σ` at a
    well-formed factory `F`, recorded events certified by `InterruptedSound π` from the body's
    `.block ""` configuration.  It assumes that the Boolean literals denote the Boolean values
    (`InterpLangBool`). -/
private theorem runCallee_err [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st)
    {n : String} {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {k d : Nat}
    {σ : RStore P} {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason}
    (IH : ∀ (_fuel : Nat) (cmd : CmdExt P) (env : IEnv P) (cfg' : IConfig P (CmdExt P))
        (cfgr : obs.Cfg) (st st' : obs.St),
        obs.run (stepCmd π d k env cmd) cfgr st = (.ok cfg', st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), StepStmtE P (EvalCommandET π)
          (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F)) (cfg'.abs F)
          ∧ obs.trace st' = revs.reverse ++ obs.trace st ∧ cfg'.Denoting F)
    (IHerr : ∀ (cmd : CmdExt P) (env : IEnv P) (cfgr : obs.Cfg) (st st' : obs.St)
        (r : StopReason),
        obs.run (stepCmd π d k env cmd) cfgr st = (.error r, st') →
        FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
        ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    (hπ : π n = some p) (hb : p.body = .structured ss) (hfac : FactoryWF (P := P) F)
    (hd : RStore.Denoting F σ) (henv : CallEnvOk F (InterpLang.absStore F σ))
    (h : obs.run (runCallee (fun _ e c => stepCmd π d k e c) n p.body (InterpLang.rfactory F) k σ)
        cfgr st = (.error r, st')) :
    ∃ revs : List (IEvent P),
      InterruptedSound π (.stmt (.block "" ss #[]) ⟨InterpLang.absStore F σ, F⟩)
        (revs.map (REvent.abs F))
      ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨-, hS⟩ := hprocs n p hπ
  have hE : IEnv.abs F (⟨.ofStore σ, InterpLang.rfactory F⟩ : IEnv P) =
      ⟨InterpLang.absStore F σ, F⟩ := by simp [IEnv.abs]
  have hdE : RStore.Denoting F (IStore.ofStore σ).get := by simpa using hd
  have hI : CfgInv π (.stmt (.block "" ss #[])
      (IEnv.abs F ⟨.ofStore σ, InterpLang.rfactory F⟩)) :=
    hE ▸ ⟨henv.1, by simpa [Config.allCmds, Stmt.allCmds] using (hS ss hb).2, henv.2⟩
  simp only [runCallee, hb, obs.run_bind] at h
  split at h
  · rename_i fc s hrun
    obtain ⟨σ', rfl, -⟩ := callee_run_ok obs π hprocs hEval IH hπ hb hI hfac hdE rfl hrun
    simp only [obs.run_pure, Prod.mk.injEq, reduceCtorEq, false_and] at h
  · rename_i r' s hrun
    obtain ⟨revs, hc, ht⟩ :=
      callee_run_err obs π hprocs hEval hchooseErr IHerr hI hfac hdE rfl hrun
    exact ⟨revs, hE ▸ hc, (Prod.mk.inj h).2 ▸ ht⟩

/-! ### The interrupted `.call` step, by where it stops

Each lemma takes a `.call` step that built the callee frame `callEntryStore p i o` (its image the
reference frame `callEntryStore p vi vo`, `CallEntry` holding) and stopped at one point, and
certifies the recorded events by the matching `InterruptedSound` constructor. -/

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped inside its precondition events: `InterruptedSound.preThrow`. -/
private theorem callErr_pre (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2 = ev :: obs.trace st)
    {n : String} {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {i o : List P.Expr}
    {vi vo : List P.Val} {cfgr : obs.Cfg} {st st' : obs.St} {r : StopReason} (hπ : π n = some p)
    (hb : p.body = .structured ss)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.error r, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (.call n args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  obtain ⟨pref, hq, u⟩ := obs_forM_emit_err obs hemitStep cfgr _ _ _ _ hpre
  have hq' := hq.map (REvent.abs F)
  rw [rDefaultAssertEvents_abs, habs] at hq'
  refine ⟨pref, ?_, u⟩
  simpa using
    InterruptedSound.preThrow (outerEvs := []) (env := env.abs F) (.refl _) .here hπ hb hE hq'

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped inside its structured callee body, given the certificate of the body's events
    (the shape `runCallee_err` returns): `InterruptedSound.inCall`. -/
private theorem callErr_body (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    {n : String} {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {i o : List P.Expr}
    {vi vo : List P.Val}
    {cfgr : obs.Cfg} {st s st' : obs.St} {u : Unit} {crevs : List (IEvent P)} (hπ : π n = some p)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (hb : p.body = .structured ss)
    (hc : InterruptedSound π
      (.stmt (.block "" ss #[]) ⟨InterpLang.absStore F (callEntryStore p i o), F⟩)
      (crevs.map (REvent.abs F)))
    (u' : obs.trace st' = crevs.reverse ++ obs.trace s) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (.call n args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
    (checksAtCall md p.spec.preconditions) ++ crevs, ?_,
    by simp [u', obs_forM_emit obs _ _ _ _ _ hpre]⟩
  rw [habs] at hc
  rw [List.map_append, rDefaultAssertEvents_abs, habs, ← List.nil_append (defaultAssertEvents ..)]
  exact .inCall (env := env.abs F) (.refl _) .here hπ hb hE hc

omit [CallLangWF P] [LawfulMonad m] in
/-- A call stopped after its completed body: inside its postcondition events
    (`InterruptedSound.postThrow`), or after them (`InterruptedSound.inCallExit`). -/
private theorem callErr_post (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2 = ev :: obs.trace st)
    {n : String} {args : List (CallArg P)} {md : MetaData P} {env : IEnv P}
    {p : Procedure P (CmdExt P) Hdr} {ss : List (Stmt P (CmdExt P))} {i o : List P.Expr}
    {vi vo : List P.Val} {σf : RStore P}
    {cfgr : obs.Cfg} {st s s2 st' : obs.St} {u : Unit} {bevs : List (IEvent P)}
    {res : Except StopReason Unit} (hπ : π n = some p) (hb : p.body = .structured ss)
    (hE : CallEntry F (InterpLang.absStore F env.store.get) p args (callEntryStore p vi vo))
    (habs : InterpLang.absStore F (callEntryStore p i o) = callEntryStore p vi vo)
    (hpre : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
        (checksAtCall md p.spec.preconditions)).forM (InterpEffects.emit (P := P))) cfgr st
        = (.ok u, s))
    (B : BigStepE π p.body ⟨callEntryStore p vi vo, F⟩ (InterpLang.absStore F σf)
        (bevs.map (REvent.abs F)))
    (t : obs.trace s2 = bevs.reverse ++ obs.trace s)
    (hpost : obs.run ((rDefaultAssertEvents (InterpLang.rfactory F) σf
        p.spec.postconditions).forM (InterpEffects.emit (P := P))) cfgr s2 = (res, st')) :
    ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd (.call n args md)) (env.abs F))
        (revs.map (REvent.abs F)) ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  have hpa :=
    rDefaultAssertEvents_abs F (callEntryStore p i o) (checksAtCall md p.spec.preconditions)
  rw [habs] at hpa
  have hq := rDefaultAssertEvents_abs F σf p.spec.postconditions
  rw [hb] at B
  obtain ⟨ρ', R, hρs⟩ : ∃ ρ', StepStmtStarE P (EvalCmdExtE π)
      (.stmt (.block "" ss #[]) ⟨callEntryStore p vi vo, F⟩) (bevs.map (REvent.abs F))
      (.terminal ρ') ∧ ρ'.store = InterpLang.absStore F σf := by
    generalize hS : InterpLang.absStore F σf = S at B
    cases B
    exact ⟨_, ‹_›, rfl⟩
  have hρf : ρ'.factory = F := stepStarE_factory π R
  have hpost' : defaultAssertEvents ρ'.factory ρ'.store p.spec.postconditions =
      defaultAssertEvents F (InterpLang.absStore F σf) p.spec.postconditions := by rw [hρf, hρs]
  rcases res with r | u2
  · obtain ⟨pref, hpref, u3⟩ := obs_forM_emit_err obs hemitStep cfgr _ _ _ _ hpost
    have hpref' := hpref.map (REvent.abs F)
    rw [hq] at hpref'
    refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
      (checksAtCall md p.spec.preconditions) ++ bevs ++ pref, ?_,
      by simp [u3, t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
    rw [List.map_append, List.map_append, hpa, ← List.nil_append (defaultAssertEvents ..)]
    exact .postThrow (env := env.abs F) (.refl _) .here hπ hb hE R (hpost' ▸ hpref')
  · refine ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p i o)
      (checksAtCall md p.spec.preconditions) ++ bevs ++
      rDefaultAssertEvents (InterpLang.rfactory F) σf p.spec.postconditions, ?_,
      by simp [obs_forM_emit obs _ _ _ _ _ hpost, t, obs_forM_emit obs _ _ _ _ _ hpre]⟩
    rw [List.map_append, List.map_append, hpa, hq, ← hpost',
      ← List.nil_append (defaultAssertEvents ..)]
    exact .inCallExit (env := env.abs F) (.refl _) .here hπ hb hE R

omit [LawfulMonad m] in
/-- At every stepper fuel `k` and call-depth budget `d`, for an observation whose `emit` always
    records its event and whose throwing `choose` leaves the trace unchanged, and if every procedure
    of `π` is well-formed (`ProcsOk π`): a throwing step `stepCmd π d k` of a command from a
    configuration with a well-formed factory (`FactoryWF`) satisfying the invariant `CfgInv π` (the
    replay invariant on the stores and the call sites) recorded events certified by
    `InterruptedSound π` (the events of a reference run, possibly stopped inside a call) from that
    command's configuration. It assumes
    that the Boolean literals denote the Boolean values (`InterpLangBool`). -/
private theorem call_cmd_errArm [InterpLangBool P] (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (hEval : BoundedEvalSoundAt P F)
    (hemitStep : ∀ (ev : IEvent P) (cfgr : obs.Cfg) (st : obs.St),
        obs.trace (obs.run (InterpEffects.emit (P := P) ev) cfgr st).2
          = ev :: obs.trace st)
    (hchooseErr : ∀ (f : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
        (cfgr : obs.Cfg) (st : obs.St) (e : StopReason) (st' : obs.St),
        obs.run (InterpEffects.choose (P := P) f store ty) cfgr st = (.error e, st') →
        obs.trace st' = obs.trace st) :
    ∀ (k d : Nat) (cmd : CmdExt P) (env : IEnv P)
      (cfgr : obs.Cfg) (st st' : obs.St) (r : StopReason),
      obs.run (stepCmd π d k env cmd) cfgr st = (.error r, st') →
      FactoryWF (P := P) F → RStore.Denoting F env.store.get →
        env.factory = InterpLang.rfactory F → CfgInv π (.stmt (.cmd cmd) (env.abs F)) →
      ∃ revs : List (IEvent P), InterruptedSound π (.stmt (.cmd cmd) (env.abs F)) (revs.map (REvent.abs F))
        ∧ obs.trace st' = revs.reverse ++ obs.trace st := by
  intro k
  induction k with
  | zero =>
    intro _ c _ cfgr _ _ _ h _ _ _ _
    cases c
    · exact obs_stepCmd_base_err (F := F) obs π hemitStep hchooseErr h
    · simp only [stepCmd, obs.run_throw, Prod.mk.injEq] at h
      exact ⟨[], .clean (.refl _), by rw [← h.2]; rfl⟩
  | succ k ih =>
  intro d c env cfgr st st' r h hf hd hrf hi
  cases c
  · exact obs_stepCmd_base_err (F := F) obs π hemitStep hchooseErr h
  cases d
  · simp only [stepCmd, obs.run_throw, Prod.mk.injEq] at h
    exact ⟨[], .clean (.refl _), by rw [← h.2]; rfl⟩
  rename_i n args md d
  have ih := ih d
  have A := fun k => call_cmd_arm obs π hprocs hEval (F := F) k d
  repeat' first
    | rw [obs_run_throw_bind] at h
    | split at h
    | simp only [stepCmd, obs.run_bind, obs.run_pure, obs.run_throw] at h
  all_goals cases h
  all_goals try exact ⟨[], .clean (.refl _), rfl⟩
  all_goals
    obtain ⟨vi, vo, hreli, hrelo, hE, hen, hdEntry, habsEntry⟩ :=
      callEntry_ok π hprocs hEval hf hd hrf hi ‹_› ‹_› ‹_› ‹_› ‹_›
    rw [hrf] at *
    first
      | (obtain ⟨bevs, B, -, -, t⟩ := runCallee_ok obs π hprocs hEval (fun _ => A k) ‹_› hf hdEntry
            (habsEntry ▸ hen) ‹obs.run (runCallee _ _ _ _ _ _) _ _ = (.ok _, _)›
         rw [habsEntry] at B
         exact callErr_post obs π hemitStep ‹_› ‹_› hE habsEntry ‹_› B t ‹_›)
      | (obtain ⟨crevs, hc, u⟩ := runCallee_err obs π hprocs hEval hchooseErr (fun _ => A k) ih ‹_›
            ‹_› hf hdEntry (habsEntry ▸ hen) ‹obs.run (runCallee _ _ _ _ _ _) _ _ = (.error _, _)›
         exact callErr_body obs π ‹_› hE habsEntry ‹_› ‹_› hc u)
      | exact callErr_pre obs π hemitStep ‹_› ‹_› hE habsEntry ‹_›

end CallErrDischarge

/-! ## Replay soundness for `CmdExt P` -/

section CallReplay

/-- Replay soundness for a run that completes: if every procedure of `π` is well-formed
    (`ProcsOk π`: distinct frame formals, and a structured body that is exit-covered, declares no
    function and has only well-formed call sites), the Boolean literals denote the Boolean values
    (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), the counterexample's configuration denotes and is tracked under a
    well-formed factory `F` (`FactoryWF`) and its image satisfies the invariant `CfgInv π`, and the
    strict replay run of `runCallInterp π` at fuel `fuel` from the counterexample's configuration
    returns `.ok`, then a counterexample classified `genuine` has a reference run recording the
    images of runtime events one of which fails the target assertion (`ReplaySound`). -/
theorem call_replaySound_of_ok [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (d : Nat)
    (hok : ∃ final, (runReplayRun (runCallInterp (m := ReplayM P) π fuel cex.cfg d)
          { oracleConfig := .strict }
          cex.oracle).1 = .ok final) :
    ReplaySound π target fuel F cex d := by
  intro hg
  obtain ⟨final, hf⟩ := hok
  obtain ⟨ev, hmem, hhalt⟩ := (genuine_iff ..).1 hg
  obtain ⟨revs, hs, -, htr⟩ := call_replayRun_sound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩ final _ _ _
    d (Prod.ext hf rfl) hfac hinv
  exact ⟨revs, _, hs, ev, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-- An erroring `choose` in `ReplayM` leaves `traceRev` unchanged. -/
private theorem replayRun_choose_err {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : ReplayCfg P) (st : ReplayState P) (e : StopReason)
    (st' : ReplayState P)
    (h : replayRun (InterpEffects.choose (P := P) factory store ty) cfg st
        = (.error e, st')) :
    st'.traceRev = st.traceRev := by eff_inv [] <;> rfl

/-- **Whole-run interrupted soundness.**  If every procedure of `π` is well-formed (`ProcsOk π`),
    the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded evaluator is
    sound up to denotation at `F` (`BoundedEvalSoundAt`), and `start` satisfies the invariant
    `CfgInv π` at a well-formed factory `F` (`FactoryWF`), then for any outcome of a replay run from
    a runtime configuration `istart` that denotes `start` under `F` (`IConfig.Denotes`), including a
    throw inside a callee, the images (`REvent.abs F`) of the recorded events are certified by
    `InterruptedSound` (they are the events of a reference run, possibly stopped inside a call). -/
theorem call_replayRun_interruptedSound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (hprocs : ProcsOk π)
    (fuel : Nat) (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (start : Config P (CmdExt P))
    (istart : IConfig P (CmdExt P))
    (hstart : istart.Denotes F start)
    (cfg : ReplayCfg P) (oracle : List P.Expr)
    (res : Except StopReason (IConfig P (CmdExt P))) (st' : ReplayState P) (d : Nat)
    (hrun : runReplayRun (runCallInterp (m := ReplayM P) π fuel istart d) cfg oracle
        = (res, st'))
    (hfac : FactoryWF (P := P) F) (hinv : CfgInv π start) :
    ∃ revs : List (IEvent P), InterruptedSound π start (revs.map (REvent.abs F)) ∧
      st'.traceRev = revs.reverse := by
  have hclean : ∀ (F : P.Factory) (c : Config P (CmdExt P)) (evs : List (Event P))
      (mid : Config P (CmdExt P)), StepStmtStarE P (EvalCommandET π) c evs mid →
      InterruptedSound π c evs := fun _ _ _ _ hs => .clean (stepStarET_toE π hs)
  obtain ⟨revs, hcert, htr⟩ := runInterp_traceSound_generic obsReplay _ (EvalCommandET π) _
    (fun _ => InterruptedSound π) hclean
    (fun _ _ _ _ _ hs hr => interruptedSound_stepThen π _ _ _ _ (stepET_toE π hs) hr)
    (callStepInterpSound _ π hprocs d)
    (stepInterpErrInto_of_arms _ _ _ _ _ (hclean F) (cfgInv_seq _) (cfgInv_block _)
      (interruptedSound_seq _) (interruptedSound_block _) replayRun_choose_err
      (fun F k _ _ _ _ _ _ h hf hE => call_cmd_errArm _ π hprocs hE
        (fun _ _ _ => congrArg _ (replayRun_emit_state ..)) replayRun_choose_err (F := F) k d
          _ _ _ _ _ _ h hf))
    F _ _ _ _ _ _ hrun hfac hEval hstart.1 (hstart.2.2 ▸ hinv) hstart.2.1
  exact ⟨revs, hstart.2.2 ▸ hcert, by simpa [obsReplay] using htr⟩

/-- **Production replay soundness with prompt stopping.** If every procedure of `π` is well-formed
    (`ProcsOk π`), the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded
    evaluator is sound up to denotation at `F` (`BoundedEvalSoundAt`), and the counterexample's
    configuration denotes and is tracked under a well-formed factory `F` (`FactoryWF`) and its image
    satisfies the invariant `CfgInv π`, then at `interruptOn := targetInterrupt target fuel` (stop
    at the target), the images of the recorded events of a `.genuine` verdict of the replay from the
    counterexample's configuration are certified by `InterruptedSound` (the events of a reference
    run, possibly stopped inside a call), and the recorded events contain one failing the target
    assertion (`assertFailureHalt`); no run-completion premise is needed. -/
theorem call_replaySound_interruptOn [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (fuel d : Nat)
    (hg : (runReplay (runCallInterp (m := ReplayM P) π fuel cex.cfg d)
            { interruptOn := targetInterrupt target fuel,
              oracleConfig := .strict } (assertFailureHalt target fuel) cex.oracle).1 = .genuine) :
    ∃ (revs : List (IEvent P)),
      InterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  obtain ⟨_, hmem, hhalt⟩ := (runReplay_genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  exact ⟨revs, hcert, _, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-! ## Replay soundness without a run-completion premise -/

/-- If every procedure of `π` is well-formed (`ProcsOk π`), the Boolean literals denote the Boolean
    values (`InterpLangBool`), the bounded evaluator is sound up to denotation at `F`
    (`BoundedEvalSoundAt`), and the counterexample's configuration denotes and is tracked under a
    well-formed factory `F` (`FactoryWF`) and its image satisfies the invariant `CfgInv π`, a
    counterexample classified `genuine` has a list of runtime events whose images are certified by
    `InterruptedSound` (the events of a reference run, possibly stopped inside a call) and one of
    which fails the target assertion (`assertFailureHalt target fuel`). -/
theorem call_replaySound_general [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F)) (d : Nat)
    (hg : genuine π target fuel cex d) :
    ∃ (revs : List (IEvent P)),
      InterruptedSound π (cex.cfg.abs F) (revs.map (REvent.abs F)) ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true := by
  obtain ⟨_, hmem, hhalt⟩ := (genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  exact ⟨revs, hcert, _, List.mem_reverse.1 (htr ▸ hmem), hhalt⟩

/-! ### `TargetNotInProcs`: the target id occurs in no procedure of `π`

Under `TargetNotInProcs π target`, no event a callee contributes reaches the target, so a
target-reaching event of an `InterruptedSound` certificate lies in its flat outer prefix. -/

/-- A command that does not *reach* `target` in the sense of `targetReached`:
    it is not an `assert`/`cover` whose label and metadata both equal `target`'s. -/
@[expose] def cmdAvoidsTarget (target : AssertId P) : CmdExt P → Bool
  | .cmd (.assert l _ md) => !(target.label == l && decide (target.md = md))
  | .cmd (.cover l _ md) => !(target.label == l && decide (target.md = md))
  | _ => true

/-- No spec clause of `checks` has both `target`'s label and `target`'s metadata. -/
@[expose] def ChecksAvoidTarget (target : AssertId P)
    (checks : ListMap String (Check P)) : Prop :=
  ∀ lc ∈ checks.toList, ¬ (target.label = lc.1 ∧ target.md = lc.2.md)

/-- **The target id occurs in no procedure of `π`**: for every `p` that `π`
    resolves, no pre- or postcondition clause of `p` has `target`'s label and
    metadata, and no `assert`/`cover` command anywhere in `p`'s structured body
    (nested `block`/`ite`/`loop` bodies included, via `Block.allCmds`) does; and `p`'s body is
    structured, not a CFG (the call-aware interpreter refuses CFG callee bodies with
    `unsupportedCalleeCfgBody`). -/
@[expose] def TargetNotInProcs (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) : Prop :=
  ∀ n p, π n = some p →
    (∀ callMd, ChecksAvoidTarget target (checksAtCall callMd p.spec.preconditions)) ∧
    ChecksAvoidTarget target p.spec.postconditions ∧
    (∀ ss, p.body = .structured ss → Block.allCmds (cmdAvoidsTarget target) ss = true) ∧
    ∀ g, p.body ≠ .cfg g

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P]
    [ProcedureHeader P Hdr] in
omit [InterpLang P] in
/-- The empty procedure table satisfies `TargetNotInProcs` for every target. -/
theorem targetNotInProcs_none (target : AssertId P) :
    TargetNotInProcs (Hdr := Hdr) (fun _ => none) target := nofun

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P] [InterpLang P] in
/-- The assertion events of spec clauses that avoid `target` do not reach `target`. -/
private theorem defaultAssertEvents_avoid (target : AssertId P)
    (fac : P.Factory) (σ : SemanticStore P) (checks : ListMap String (Check P))
    (h : ChecksAvoidTarget target checks) :
    ∀ e ∈ defaultAssertEvents fac σ checks, targetReachedE target e = false := by
  grind [defaultAssertEvents, targetReachedE, ChecksAvoidTarget]

omit [HasFvars P] [CallLangWF P] [HasOldIdent P] [InterpLang P] in
/-- A base command that avoids `target` emits no event reaching `target`. -/
private theorem evalCmdE_avoid (target : AssertId P)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P}
    {evs : Trace P}
    (h : EvalCmdE (P := P) fac σ c σ' evs)
    (hq : cmdAvoidsTarget target (.cmd c) = true) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  cases h <;> unfold cmdAvoidsTarget at hq <;> grind [targetReachedE]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a reference evaluation of a command that avoids the target emits no
    target-reaching event. -/
private theorem evalCommandE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {fac : P.Factory} {σ σ' : SemanticStore P} {c : CmdExt P} {evs : Trace P}
    (h : EvalCmdExtE π fac σ c σ' evs)
    (hq : cmdAvoidsTarget target c = true) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  revert hq
  refine EvalCmdExtE.rec
    (motive_1 := fun b _ _ l _ =>
      (∀ ss, b = .structured ss → Block.allCmds (cmdAvoidsTarget target) ss) →
      (∀ g, b ≠ .cfg g) → l.all (!targetReachedE target ·))
    (motive_3 := fun c l _ _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·))
    (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun c l _ _ =>
      c.allCmds (cmdAvoidsTarget target) → l.all (!targetReachedE target ·))
    (motive_6 := fun _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ h <;>
  grind [Config.allCmds, Stmt.allCmds, evalCmdE_avoid, defaultAssertEvents_avoid,
    stepStmtE_preserves_allCmds, TargetNotInProcs]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, a reference run from a target-avoiding configuration emits no
    target-reaching event. -/
private theorem stepStarE_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {c c' : Config P (CmdExt P)} {evs : Trace P}
    (h : StepStmtStarE P (EvalCmdExtE π) c evs c')
    (hall : c.allCmds (cmdAvoidsTarget target)) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  induction h
  nofun
  rename_i hs hr ih
  have hrest := ih (stepStmtE_preserves_allCmds _ hs hall)
  clear hr
  induction hs <;> grind [Config.allCmds, Stmt.allCmds, evalCommandE_avoid]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, an `InterruptedSound` certificate from a target-avoiding configuration
    has no target-reaching event. -/
private theorem interruptedSound_avoid
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    (hall : start.allCmds (cmdAvoidsTarget target)) :
    ∀ e ∈ evs, targetReachedE target e = false := by
  induction h <;> grind [stepStarE_avoid, defaultAssertEvents_avoid, TargetNotInProcs,
      Config.allCmds, Stmt.allCmds]

omit [CallLangWF P] [InterpLang P] in
/-- **Flattening a certificate at a target-reaching event, with the flat trace a prefix.** If the
    target assertion occurs in no procedure of `π` (`TargetNotInProcs π target`), an event of an
    `InterruptedSound` certificate that reaches the target lies in a flat reference run from `start`
    whose events are a prefix of the certificate's: every event a callee contributes is target-free,
    so the event is in the certificate's flat outer prefix. -/
theorem interruptedSound_flatPrefix_of_targetReached
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    {ev : Event P} (hmem : ev ∈ evs) (hreach : targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE P (EvalCmdExtE π)
        start evs' final ∧ ev ∈ evs' ∧ evs' <+: evs := by
  cases h <;> grind [interruptedSound_avoid, stepStarE_avoid, defaultAssertEvents_avoid,
      TargetNotInProcs, Config.allCmds, Stmt.allCmds]

omit [CallLangWF P] [InterpLang P] in
/-- **Flattening a certificate at a target-reaching event.** If the target assertion occurs in
    no procedure of `π` (`TargetNotInProcs π target`), an
    event of an `InterruptedSound` certificate that reaches the target lies in a flat reference run
    from `start`: every event a callee contributes is target-free, so the event is in the
    certificate's flat outer prefix. -/
private theorem interruptedSound_flat_of_targetReached
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs)
    {ev : Event P} (hmem : ev ∈ evs) (hreach : targetReachedE target ev = true) :
    ∃ evs' final, StepStmtStarE P (EvalCmdExtE π)
        start evs' final ∧ ev ∈ evs' := by
  grind [interruptedSound_flatPrefix_of_targetReached _ _ hπ]

omit [CallLangWF P] [InterpLang P] in
/-- Under `TargetNotInProcs`, the events of an `InterruptedSound` certificate are the events of a
    flat reference run from its start followed by events none of which reaches the target. -/
private theorem interruptedSound_split
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target)
    {start : Config P (CmdExt P)} {evs : Trace P}
    (h : InterruptedSound π start evs) :
    ∃ evs' rest final, StepStmtStarE P (EvalCmdExtE π) start evs' final ∧ evs = evs' ++ rest ∧
      ∀ e ∈ rest, targetReachedE target e = false := by
  have hI := fun s e (h : InterruptedSound π s e) => interruptedSound_avoid π target hπ h
  cases h with
  | clean R => exact ⟨_, [], _, R, (List.append_nil _).symm, nofun⟩
  | inCall R _ hp hb _ hc =>
    have hC := hI _ _ hc (by simpa [Config.allCmds, Stmt.allCmds] using (hπ _ _ hp).2.2.1 _ hb)
    refine ⟨_, _, _, R, List.append_assoc .., ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | inCallExit R _ hp hb _ hB =>
    have hC := stepStarE_avoid π target hπ hB
      (by simpa [Config.allCmds, Stmt.allCmds] using (hπ _ _ hp).2.2.1 _ hb)
    refine ⟨_, _, _, R, by simp only [List.append_assoc]; rfl, ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]
  | preThrow R _ hp _ _ hpre =>
    refine ⟨_, _, _, R, rfl, fun e he => ?_⟩
    exact defaultAssertEvents_avoid _ _ _ _ ((hπ _ _ hp).1 _) e (hpre.subset he)
  | postThrow R _ hp hb _ hB hpost =>
    have hC := stepStarE_avoid π target hπ hB
      (by simpa [Config.allCmds, Stmt.allCmds] using (hπ _ _ hp).2.2.1 _ hb)
    have hQ := fun e he => defaultAssertEvents_avoid _ _ _ _ (hπ _ _ hp).2.1 e (hpost.subset he)
    refine ⟨_, _, _, R, by simp only [List.append_assoc]; rfl, ?_⟩
    grind [defaultAssertEvents_avoid, TargetNotInProcs]

omit [HasBoolOps P] [HasFvar P] [HasFvars P] [CallLangWF P] [HasOldIdent P] in
/-- The semantic image of a runtime event reaches the target exactly when the event does. -/
private theorem targetReachedE_abs (target : AssertId P) (F : P.Factory) (e : IEvent P) :
    targetReachedE target (REvent.abs F e) = targetReached target e := by
  cases e <;> rfl

omit [CallLangWF P] in
/-- Under `TargetNotInProcs`, a certificate of the images of runtime events `revs` containing a
    target-reaching event `ev` has a prefix of `revs` that contains `ev` and whose images are the
    events of a flat reference run from its start. -/
private theorem interruptedSound_flatRuntime
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (hπ : TargetNotInProcs π target) {F : P.Factory}
    {start : Config P (CmdExt P)} {revs : List (IEvent P)}
    (h : InterruptedSound π start (revs.map (REvent.abs F)))
    {ev : IEvent P} (hmem : ev ∈ revs) (hreach : targetReached target ev = true) :
    ∃ pre final, StepStmtStarE P (EvalCmdExtE π) start (pre.map (REvent.abs F)) final ∧
      ev ∈ pre ∧ pre <+: revs := by
  obtain ⟨evs', rest, final, R, heq, hrest⟩ := interruptedSound_split π target hπ h
  have hpre : evs' = (revs.take evs'.length).map (REvent.abs F) := by
    rw [List.map_take, heq, List.take_left]
  have hsuf : rest = (revs.drop evs'.length).map (REvent.abs F) := by
    rw [List.map_drop, heq, List.drop_left]
  refine ⟨_, final, hpre ▸ R, ?_, List.take_prefix _ _⟩
  rw [← List.take_append_drop evs'.length revs, List.mem_append] at hmem
  refine hmem.resolve_right fun hd => ?_
  have hr := hrest _ (hsuf ▸ List.mem_map_of_mem hd)
  rw [targetReachedE_abs, hreach] at hr
  cases hr

/-- **Replay soundness** (`ReplaySound`): if every procedure of `π` is well-formed (`ProcsOk π`:
    distinct frame formals, and a structured body that is exit-covered and has only well-formed call
    sites), the Boolean literals denote the Boolean values (`InterpLangBool`), the bounded evaluator
    is sound up to denotation at `F` (`BoundedEvalSoundAt`), the counterexample's configuration
    denotes and is tracked under a well-formed factory `F` (`FactoryWF`) and its image satisfies the
    invariant `CfgInv π` (the replay invariant on the stores and the call sites), and the target
    assertion occurs in no procedure of `π` (`TargetNotInProcs π target`), then a counterexample
    classified `genuine` has a reference run recording the images of runtime events one of which
    fails the target assertion. -/
theorem call_replaySound [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySound π target fuel F cex d := by
  intro hg
  obtain ⟨revs, hcert, ev, hmem, hhalt⟩ :=
    call_replaySound_general π _ _ _ hprocs F hEval hfac hd ht hinv d hg
  obtain ⟨pre, final, R, hev, -⟩ := interruptedSound_flatRuntime π target htgt hcert hmem
    (targetReached_of_assertFailureHalt _ _ _ hhalt)
  exact ⟨pre, final, R, ev, hev, hhalt⟩

/-- **Feasibility-aware replay soundness** (`ReplaySoundFeasible`): under the hypotheses of replay
    soundness (every procedure of `π` well-formed, `ProcsOk π`; Boolean literals denoting the
    Boolean values, `InterpLangBool`; a bounded evaluator sound up to denotation at `F`,
    `BoundedEvalSoundAt`; the counterexample's configuration denoting and tracked under a
    well-formed factory `F`, `FactoryWF`, with its image satisfying the invariant `CfgInv π`; the
    target assertion in no procedure of `π`, `TargetNotInProcs π target`), a counterexample
    classified `genuineEnforced` has a reference run recording the images of runtime events one of
    which fails the target assertion and whose `.assume` events all evaluate to `tt`
    (`PathFeasible`). -/
theorem call_replaySound_feasible [InterpLangBool P]
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (cex : CexA P (CmdExt P))
    (hprocs : ProcsOk π)
    (F : P.Factory) (hEval : BoundedEvalSoundAt P F) (hfac : FactoryWF (P := P) F)
    (hd : cex.cfg.Denoting F)
    (ht : cex.cfg.Tracked) (hinv : CfgInv π (cex.cfg.abs F))
    (htgt : TargetNotInProcs π target) (d : Nat) :
    ReplaySoundFeasible π target fuel F cex d := by
  intro hg
  obtain ⟨_, hmem, hhalt⟩ := (runReplay_genuine_iff ..).1 hg
  obtain ⟨revs, hcert, htr⟩ := call_replayRun_interruptedSound π hprocs _ F hEval _ _ ⟨hd, ht, rfl⟩
    _ _ _ _ _ rfl hfac hinv
  obtain ⟨pre, final, R, hev, hpre⟩ := interruptedSound_flatRuntime π target htgt hcert
    (List.mem_reverse.1 (htr ▸ hmem)) (targetReached_of_assertFailureHalt _ _ _ hhalt)
  exact ⟨pre, final, R, ⟨_, hev, hhalt⟩,
    pathFeasible_of_subset (fun _ hx => htr ▸ List.mem_reverse.2 (hpre.subset hx))
      (pathFeasible_of_runReplay_genuine_call _ _ _ _ _ _ hg)⟩

end CallReplay

end Calls

end -- public section

end Imperative

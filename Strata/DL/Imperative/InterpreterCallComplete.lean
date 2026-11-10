/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCallSound
public import Strata.DL.Imperative.InterpreterCompleteGeneric
public import Strata.DL.Imperative.InterpreterCompleteObs
import all Strata.DL.Imperative.InterpreterCompleteGeneric
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterSemanticsSpec
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.StmtCFGCallSemantics
import Strata.DL.Imperative.InterpreterReplayTactics
public import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.InterpreterCallProps


/-! # Call-aware replay completeness against the reference event semantics

The completeness direction of call-aware soundness: every reference `.call`
execution is *performed* by the engine (`Calls.stepCmd`), at every sufficiently large
call-depth budget, stepper index and driver fuel, emitting exactly the reference rule's events.

As in the base-command development, the derivation has to be given in the
**engine-realizable** form: `EvalCommandEngAtE` below is the reference `EvalCmdExtE`
with its base-command arm replaced by `EvalCmdEngE` (which carries the engine's
executable value checks), its call arm carrying the engine's argument evaluation
(`CallArgsReach`) and typed write-back check (`WriteBackOK`), and with a **call-nesting
height** index, so that the
`.call` completeness proof recurses on a `Nat` rather than through the nested mutual
derivation.

Key definitions: `EvalCommandEngAtE` and its closure `StepEngAtStarE` (the engine-realizable
relations at a call-nesting height), `CallArgsReach` and `WriteBackOK` (the run-local facts of a
call), `CmdArmComplete` (the per-command completeness obligation)
and `ReplayComplete` (completeness of the replay verdict `genuine`).

Key theorems: `call_cmdArmComplete_all` (every engine-realizable command is performed by
`stepCmd π`, at every call-nesting height), `call_runCallInterp_complete` (every
engine-realizable run ending at a configuration the driver stops at is reproduced by
`runCallInterp π`) and `call_runCallInterp_complete_of_agree` (the same for a reference
`StepStmtExtStarE` run, under `EngineAgreesFrom`).
`stepCmd_call_complete` is the completeness of one `.call` step given its callee body run.
`evalBoundedList_of_reach`, `readVarList_of_storedTy` and `writeBackTyped_of_rel` relate the
engine's runtime call marshalling to the semantic one, and `guardEval_complete` gives the guard
values, literals up to metadata, the engine branches on under `EngineGuardsAgree`.

`RunChoices` is the choice sequence of a reference run: the values its nondeterministic
`.init`/`.set` commands write and the Booleans its `.nondet` guards are read as, in execution
order and inside callee bodies, read off an oracle by the relations `OracleStepE` and
`OracleCmdAt`.  `ProgDeterministic` (with `Config.noNondetGuards`, `CmdExtDeterministic`) is the
syntactic determinism of a call-aware program.  Completeness over choice sequences is in
`InterpreterCallCompleteProps.lean`. -/

namespace Imperative
open scoped C1
attribute [-simp] bind_pure_comp

public section

namespace Calls

variable {P : PureExpr} [HasBoolOps P] [HasFvar P] [HasFvars P]
  [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- **Completeness of call-aware replay**: if a reference run from `cex.cfg` emits an event on
    which the halting predicate fires at fuel `fuel` (an event of the target obligation whose
    condition evaluates to the literal witnessing it), then `cex` replays at `fuel` to the target
    failure (`genuine`). -/
@[expose] def ReplayComplete (π : String → Option (Procedure P (CmdExt P) Hdr))
    (target : AssertId P) (fuel : Nat) (F : P.Factory) (cex : CexA P (CmdExt P)) :
    Prop :=
  (∃ (revs : List (IEvent P)) (final : Config P (CmdExt P)),
      StepStmtExtStarE π (cex.cfg.abs F) (revs.map (REvent.abs F)) final ∧
      ∃ ev ∈ revs, assertFailureHalt target fuel ev = true) →
    genuine π target fuel cex

/-! ## The engine-realizable command relation, indexed by call-nesting height -/

/-- A call-aware command relation: what the `.call` arm's callee body run and the
    statement relation are parameterized by. -/
abbrev CallCmdRel (P : PureExpr) :=
  P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P → Prop

/-- A procedure-body relation: the callee body run of a `.call` arm. -/
abbrev CallBodyRel (P : PureExpr) :=
  Body P (CmdExt P) → Env P → SemanticStore P → Trace P → Prop

/-- The engine reaches the reference value of every input expression of a call (`EngEvalReach`):
    the run-local evaluation fact the engine's argument evaluation (`evalBoundedList`) needs. -/
@[expose] def CallArgsReach (f : P.Factory) (σ : SemanticStore P) (args : List (CallArg P)) :
    Prop :=
  ∀ e ∈ getInputExprs args, EngEvalReach P f σ e

/-- The engine's typed write-back check (`writeBackTyped`) passes on every runtime representation
    of a call's write-back: for every runtime caller store denoting `σ` and every runtime callee
    final store denoting `σf`, the runtime values read from the caller's write-back targets and
    from the callee's output formals pass the check. -/
@[expose] def WriteBackOK (f : P.Factory) (σ : SemanticStore P) (p : Procedure P (CmdExt P) Hdr)
    (args : List (CallArg P)) (σf : SemanticStore P) : Prop :=
  ∀ (σr σfr : RStore P) (olds ms : List P.Expr), StoreDenotes f σr σ → StoreDenotes f σfr σf →
    readVarList σr (CallArg.getLhs args) = some olds →
    readVarList σfr (ProcedureHeader.outputParams (P := P) p.header) = some ms →
    writeBackTyped (InterpLang.ops (P := P)) (InterpLang.rfactory f) olds ms = true

/-- Execution of a structured procedure body whose statements run through the
    engine-realizable statement relation built from the command relation `E`.  Only
    `.structured` bodies have an execution; `.cfg` bodies have none. -/
@[expose] def BodyExecEngOf
    (R : ChoiceRecord P) (E : CallCmdRel P) : CallBodyRel P
  | .structured ss, ρ, σ', emitted =>
      ∃ ρ' : Env P,
        ReflTransTrace (Imperative.StepEngParamE P R E)
          (.stmt (Stmt.block "" ss #[]) ρ) emitted (.terminal ρ')
        ∧ ρ'.store = σ'
  | .cfg _, _, _, _ => False

/-- The base-command arm of the engine-realizable command relation: the
    reference `EvalCmdExtE.cmd_sem` arm with the engine's executable value checks
    (`EvalCmdEngE`). -/
@[expose] def CmdArmEng (R : ChoiceRecord P) : CallCmdRel P :=
  fun fac σ c σ' emitted =>
    ∃ base, c = CmdExt.cmd base ∧ EvalCmdEngE P R fac σ base σ' emitted

/-- The call arm of the engine-realizable command relation, with the callee
    body run supplied as `B`: the reference `EvalCmdExtE.call_sem` arm, plus the two facts the
    engine's `.call` machinery needs of the individual call: the engine reaches the value of
    every input expression (`CallArgsReach`), and its typed write-back check passes
    (`WriteBackOK`). -/
@[expose] def CallArmEng (π : String → Option (Procedure P (CmdExt P) Hdr))
    (B : CallBodyRel P) : CallCmdRel P :=
  fun fac σ c σ' emitted =>
    ∃ nm p callArgs md σAO σ_final bodyEvents,
      c = CmdExt.call nm callArgs md
      ∧ π nm = some p
      ∧ CallEntry fac σ p callArgs σAO
      ∧ B p.body ⟨σAO, fac⟩ σ_final bodyEvents
      ∧ CallExit fac σ p callArgs σ_final σ'
      ∧ emitted = defaultAssertEvents fac σAO (checksAtCall md p.spec.preconditions) ++
          bodyEvents ++ defaultAssertEvents fac σ_final p.spec.postconditions
      ∧ CallArgsReach fac σ callArgs ∧ WriteBackOK fac σ p callArgs σ_final

/-- Engine-realizable command semantics at call-nesting height `n`: base
    commands at every height, and calls whose callee body is itself an
    engine-realizable run at height `n - 1`.  At height `0` only base commands
    are related. -/
@[expose] def EvalCommandEngAtE
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (R : ChoiceRecord P) : Nat → CallCmdRel P
  | 0 => CmdArmEng R
  | n + 1 => fun fac σ c σ' emitted =>
      CmdArmEng R fac σ c σ' emitted
      ∨ CallArmEng π
          (BodyExecEngOf R (EvalCommandEngAtE π R n)) fac σ c σ' emitted

/-- Traced closure of the engine-realizable statement relation at height `n`. -/
abbrev StepEngAtStarE
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (R : ChoiceRecord P) (n : Nat) :=
  ReflTransTrace
    (Imperative.StepEngParamE P R (EvalCommandEngAtE π R n))

/-- The stepper family: `stepCmd π` baked at call-depth budget `i` and index `j`, ignoring the
    fuel the driver threads.  This is the stepper a `.call` runs its callee body with. -/
abbrev callStepOf {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (π : String → Option (Procedure P (CmdExt P) Hdr)) (i j : Nat) :
    StepCmdM P (CmdExt P) m :=
  fun _ env cmd => stepCmd π i j env cmd

/-! ## Runtime call marshalling against its semantic image

The engine's `.call` step evaluates its actuals (`evalBoundedList`) and type-checks its write-back
(`writeBackTyped`) on runtime values; on denoting stores these succeed whenever the reference call
rule's semantic operations do.  The lemmas for `readVarList`, `bindPositional` and
`callEntryStore` are in `InterpreterCallProps.lean`. -/

omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- The write-back targets of a call, each of which holds in the image of a runtime store a value
    of the type of its written value (`valueOfStoredTy`), are read from the runtime store, and
    runtime values denoting the written values pass the engine's typed write-back check. -/
theorem writeBackTyped_of_rel (hWB : WriteBackTypedComplete P) {F : P.Factory}
    {σ : RStore P} :
    ∀ {xs : List P.Ident} {vs : List P.Val} {ms : List P.Expr},
      List.Rel₂ (HasVal.valueOfStoredTy (P := P) F (InterpLang.absStore F σ)) xs vs →
      List.Rel₂ (InterpLang.Denotes F) ms vs →
      ∃ olds, readVarList σ xs = some olds ∧
        writeBackTyped (InterpLang.ops (P := P)) (InterpLang.rfactory F) olds ms = true
  | _, _, _, .nil, .nil => ⟨[], rfl, rfl⟩
  | x :: _, _, _ :: _, .cons ⟨_, ty, hx, hp, hv⟩ hs, .cons hm hms => by
    obtain ⟨olds, ho, hw⟩ := writeBackTyped_of_rel hWB hs hms
    simp only [InterpLang.absStore, Option.bind_eq_some_iff] at hx
    obtain ⟨o, hσ, hdo⟩ := hx
    obtain ⟨h1, h2⟩ := hWB F o _ _ _ ty hdo hm hp hv
    refine ⟨o :: olds, by simp [readVarList, hσ, ho], ?_⟩
    simp only [writeBackTyped, List.zip_cons_cons, List.all_cons, h1, h2, Bool.and_self,
      Bool.true_and]
    exact hw

omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [HasOldIdent P] [DecidableEq P.Ident]  in
/-- When the runtime value checks are complete for typed write-back (`WriteBackTypedComplete`),
    the engine's write-back check passes on every runtime representation of a reference call exit
    (`WriteBackOK`). -/
theorem writeBackOK_of_complete (hWB : WriteBackTypedComplete P) {F : P.Factory}
    {σ σf σ' : SemanticStore P} {p : Procedure P (CmdExt P) Hdr} {args : List (CallArg P)}
    (hexit : CallExit F σ p args σf σ') : WriteBackOK F σ p args σf := by
  intro σr σfr olds ms hσ hσf hold hms
  obtain ⟨-, rfl⟩ := storeDenotes_iff.1 hσ
  obtain ⟨-, rfl⟩ := storeDenotes_iff.1 hσf
  obtain ⟨-, vs, hrd, -, hrel⟩ := hexit
  obtain ⟨ms', hms', hmsrel⟩ := readVarList_absStore σfr _ (readVarList_of_readValues _ _ _ _ hrd)
  obtain ⟨olds', hold', hwb⟩ := writeBackTyped_of_rel hWB hrel hmsrel
  rw [hms'] at hms
  rw [hold'] at hold
  cases hms
  cases hold
  exact hwb

omit [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- If the reference semantics evaluates the expressions `es` to `vs` (`EvalExpressions`) and the
    engine reaches the reference value of each of them (`EngEvalReach`), then `evalBoundedList`
    returns runtime values denoting `vs` at every sufficiently large fuel, on every runtime store
    denoting the store, when the bounded evaluator is fuel-monotone. -/
theorem evalBoundedList_of_reach (hMono : BoundedEvalMono P) {f : P.Factory} {σr : RStore P}
    {σ : SemanticStore P} (hσ : StoreDenotes f σr σ) :
    ∀ {es : List P.Expr} {vs : List P.Val}, EvalExpressions f σ es vs →
      (∀ e ∈ es, EngEvalReach P f σ e) →
      ∃ N rs, List.Rel₂ (InterpLang.Denotes f) rs vs ∧
        ∀ n, N ≤ n → evalBoundedList n (InterpLang.rfactory f) σr es = some rs := by
  intro es vs h
  induction h with
  | eval_none => exact fun _ => ⟨0, [], .nil, fun _ _ => rfl⟩
  | eval_some _ hev _ ih =>
    intro hr
    obtain ⟨a, r, ha, hd⟩ := hr _ (.head _) _ _ hσ hev
    obtain ⟨b, rs, hrs, hb⟩ := ih hσ fun e he => hr e (List.mem_cons_of_mem _ he)
    refine ⟨a + b, r :: rs, .cons hd hrs, fun n hn => ?_⟩
    simp only [evalBoundedList, hMono a n _ _ _ _ (by omega) ha, hb n (by omega), Option.map_some]

omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- The write-back targets of a call, each of which holds in the image of a runtime store a value
    of the type of its written value (`valueOfStoredTy`), are read from the runtime store. -/
theorem readVarList_of_storedTy {F : P.Factory} {σ : RStore P} :
    ∀ {xs : List P.Ident} {vs : List P.Val},
      List.Rel₂ (HasVal.valueOfStoredTy (P := P) F (InterpLang.absStore F σ)) xs vs →
      ∃ olds, readVarList σ xs = some olds
  | _, _, .nil => ⟨[], rfl⟩
  | x :: _, _ :: _, .cons ⟨_, _, hx, _⟩ hs => by
    obtain ⟨olds, ho⟩ := readVarList_of_storedTy hs
    simp only [InterpLang.absStore, Option.bind_eq_some_iff] at hx
    obtain ⟨o, hσ, -⟩ := hx
    exact ⟨o :: olds, by simp [readVarList, hσ, ho]⟩

omit [HasFvar P] [HasFvars P] [DecidableEq P.Expr] [DecidableEq P.Ident] [HasOldIdent P] in
/-- Under guard agreement (`EngineGuardsAgree`), a guard whose reference value is `ttVal F`
    (respectively `ffVal F`) on a store `σ` evaluates, on every runtime store denoting `σ`, to one
    runtime value at every large enough fuel, the literal `tt` (`ff`) up to metadata
    (`InterpLang.boolLit?`), when the bounded evaluator is complete and fuel-monotone. -/
theorem guardEval_complete (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (hGuards : EngineGuardsAgree P) {F : P.Factory} (σr : RStore P) (σ : SemanticStore P)
    (c : P.Expr) (hσ : StoreDenotes F σr σ) :
    (P.eval F σ c = some (HasBool.ttVal F) → ∃ f0 r, InterpLang.boolLit? r = some true ∧
      ∀ fuel, f0 ≤ fuel →
        InterpLang.boundedEval (P := P) fuel (InterpLang.rfactory F) σr c = some r) ∧
    (P.eval F σ c = some (HasBool.ffVal F) → ∃ f0 r, InterpLang.boolLit? r = some false ∧
      ∀ fuel, f0 ≤ fuel →
        InterpLang.boundedEval (P := P) fuel (InterpLang.rfactory F) σr c = some r) := by
  refine ⟨fun he => ?_, fun he => ?_⟩
  all_goals obtain ⟨n, r, hr, -⟩ := hEvalComplete F σr σ c _ hσ he
  · exact ⟨n, r, (hGuards F σ c).1 he σr n r hσ hr, fun k hk => hMono n k _ _ _ _ hk hr⟩
  · exact ⟨n, r, (hGuards F σ c).2 he σr n r hσ hr, fun k hk => hMono n k _ _ _ _ hk hr⟩

/-! ## The per-command completeness obligation, per call-nesting height -/

section CallComplete

variable {m : Type → Type} [Monad m] [LawfulMonad m] [InterpEffects P m]
  [MonadExcept StopReason m]

omit [DecidableEq P.Expr] in
/-- An engine-realizable command evaluation at any call-nesting height defines only the names
    `CmdDefs` lists: a base command only the binder of an `init`, a call nothing new, since its
    write-back (`CallExit`) updates already defined slots only. -/
theorem evalCommandEngAtE_cmdDefsSound
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (R : ChoiceRecord P) (n : Nat) :
    CmdDefsSound (EvalCommandEngAtE π R n) := by
  have hcmd : CmdDefsSound (CmdArmEng (P := P) R) := fun _ _ _ _ _ ⟨_, hc, h⟩ =>
    hc ▸ evalCmdE_cmdDefsSound _ _ _ _ _ h.toEvalCmdE
  rcases n with _ | n
  · exact hcmd
  rintro _ _ _ _ _ (h | ⟨_, _, _, _, _, _, _, rfl, -, -, -, ⟨_, _, _, hup, -⟩, -⟩)
  · exact hcmd _ _ _ _ _ h
  exact fun x hx => .inl (UpdateStatesDefMonotone' (vs := [x])
    (fun _ hv => List.mem_singleton.1 hv ▸ hx) hup x (List.mem_singleton_self x))

omit [LawfulMonad m] in
/-- **A `.call` step, given its callee body run.**  A reference `.call` with entry frame `σAO`
    (`CallEntry`) and write-back from the callee's final store `σf` to `σ'` (`CallExit`), from a
    denoting caller environment `ρ` carrying the runtime factory of `F`, is performed by
    `stepCmd π i j` at every large enough call-depth budget `i` and stepper index `j` from every
    state `st` with `Pend st o`, reaching a denoting store that stands for `σ'`, leaving a state
    with `Pend st' o'` and recording the call's events, given that: emitting runtime events whose
    images satisfy `Q` succeeds, keeps `Pend` and prepends the events (`hemit`); the callee body
    run (`runCallee`) from every denoting runtime frame standing for `σAO` reaches a denoting store
    standing for `σf`, turning `Pend · o` into `Pend · o'` and recording `evB` (`hbody`); the
    call's events satisfy `Q`; the engine reaches the value of every input expression
    (`hargs`); the engine's typed write-back check passes (`hwb`); and the bounded evaluator is
    fuel-monotone. -/
theorem stepCmd_call_complete (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory}
    (hMono : BoundedEvalMono P)
    {Pend : obs.St → List P.Val → Prop} {Q : Event P → Prop}
    (hemit : ∀ (revs : List (IEvent P)) o st, (∀ ev ∈ revs, Q (ev.abs F)) → Pend st o →
      ∃ st', obs.run (revs.forM (InterpEffects.emit (P := P))) cfgr st = (.ok ⟨⟩, st') ∧
        Pend st' o ∧ obs.trace st' = revs.reverse ++ obs.trace st)
    {ρ : IEnv P} (hd : RStore.Denoting F ρ.store.get) (hf : ρ.factory = InterpLang.rfactory F)
    {nm : String} {args : List (CallArg P)} {md : MetaData P} {p : Procedure P (CmdExt P) Hdr}
    {σAO σf σ' : SemanticStore P} {evB : List (Event P)} {o o' : List P.Val}
    (hπ : π nm = some p) (hentry : CallEntry F (InterpLang.absStore F ρ.store.get) p args σAO)
    (hexit : CallExit F (InterpLang.absStore F ρ.store.get) p args σf σ')
    (hargs : CallArgsReach F (InterpLang.absStore F ρ.store.get) args)
    (hwb : WriteBackOK F (InterpLang.absStore F ρ.store.get) p args σf)
    (hbody : ∀ er : RStore P, InterpLang.absStore F er = σAO → RStore.Denoting F er →
      ∀ st, Pend st o → ∃ (fb : Nat) (sf : RStore P) (st' : obs.St),
        InterpLang.absStore F sf = σf ∧ RStore.Denoting F sf ∧
        (∀ i j, fb ≤ i → fb ≤ j → obs.run (runCallee (fun _ e c => stepCmd π i j e c) nm p.body
          (InterpLang.rfactory F) j er) cfgr st = (.ok sf, st')) ∧
        Pend st' o' ∧ obs.TraceExt F st st' evB)
    (hq : ∀ ev ∈ defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++ evB ++
      defaultAssertEvents F σf p.spec.postconditions, Q ev)
    (st : obs.St) (hst : Pend st o) :
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ i j, f0 ≤ i → f0 ≤ j → obs.run (stepCmd π i j ρ (.call nm args md)) cfgr st
        = (.ok (.terminal { ρ with store := σi }), st')) ∧ Pend st' o' ∧
      obs.TraceExt F st st' (defaultAssertEvents F σAO (checksAtCall md p.spec.preconditions) ++
        evB ++ defaultAssertEvents F σf p.spec.postconditions) := by
  obtain ⟨vi, vo, hin, hout, hinit⟩ := hentry
  obtain ⟨-, vs, hrd, hup, hrel⟩ := hexit
  obtain ⟨N, ri, hri, hev⟩ := evalBoundedList_of_reach hMono (storeDenotes_absStore hd) hin hargs
  obtain ⟨ro, hro, hrorel⟩ := readVarList_absStore _ _ (readVarList_of_readValues _ _ _ _ hout)
  obtain ⟨hlin, hlout, rfl⟩ := callEntryStore_of_initCallFrame _ _ _ _ hinit
  obtain ⟨habs, hden⟩ := callEntryStore_abs p hri hrorel
  have hQ : ∀ σr checks, (∀ ev ∈ defaultAssertEvents F (InterpLang.absStore F σr) checks, Q ev) →
      ∀ ev ∈ rDefaultAssertEvents (InterpLang.rfactory F) σr checks, Q (ev.abs F) :=
    fun σr checks h ev hev => h _ (rDefaultAssertEvents_abs F σr checks ▸ List.mem_map_of_mem hev)
  simp only [List.forall_mem_append] at hq
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hq
  obtain ⟨s1, e1, p1, t1⟩ := hemit _ o st (hQ _ _ (habs ▸ hq1)) hst
  obtain ⟨fb, sf, s2, rfl, hdsf, hrun, p2, rb, hrb, t2⟩ := hbody _ habs hden s1 p1
  obtain ⟨s3, e3, p3, t3⟩ := hemit _ o' s2 (hQ _ p.spec.postconditions hq3) p2
  obtain ⟨ms, hms, hmsrel⟩ := readVarList_absStore sf _ (readVarList_of_readValues _ _ _ _ hrd)
  obtain ⟨olds, hold⟩ := readVarList_of_storedTy hrel
  have hwb := hwb _ _ _ _ (storeDenotes_absStore hd) (storeDenotes_absStore hdsf) hold hms
  have hbind := bindPositional_of_updateStates _ _ _ _ hup
  refine ⟨N + fb + 1, ρ.store.bindPositional (CallArg.getLhs args) ms, s3, ?_, ?_,
    fun i j hi hj => ?_, p3, ⟨rDefaultAssertEvents (InterpLang.rfactory F) (callEntryStore p ri ro)
      (checksAtCall md p.spec.preconditions) ++ rb ++
      rDefaultAssertEvents (InterpLang.rfactory F) sf p.spec.postconditions, ?_, ?_⟩⟩
  · rw [IStore.get_bindPositional, absStore_bindPositional _ _ hmsrel, hbind.2]
  · rw [IStore.get_bindPositional]
    exact denoting_bindPositional _ hd hmsrel
  · obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hr := hrun i j (by omega) (by omega)
    obtain ⟨ss, hss⟩ : ∃ ss, p.body = .structured ss := by
      cases hb : p.body
      · exact ⟨_, rfl⟩
      · simp [hb, runCallee, obs.run_throw] at hr
    rw [hss] at hr
    rw [stepCmd]
    simp (disch := omega) [hπ, hss, hf, hev, hro, hlin, hlout, hri.length_eq, hrorel.length_eq,
      e1, hr, e3, hms, hold, hwb, ReadValuesLength hrd, hbind.1, -List.forM_eq_forM]
  · simp only [List.map_append, rDefaultAssertEvents_abs, habs, hrb]
  · simp [t1, t2, t3]

/-- **Completeness of the call-aware command stepper for the command relation `E`**: every
    `E`-related command evaluation, from the store of an environment `ρ` to `σ'` emitting `evs`, is
    performed by one `stepInterp` step over `stepCmd π i j` at every sufficiently large call-depth
    budget `i`, stepper index `j` and driver fuel, landing in `.terminal { ρ with store := σ' }` and
    prepending exactly `evs` to the trace. -/
@[expose] def CmdArmComplete (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) (F : P.Factory)
    (E : CallCmdRel P) : Prop :=
  ∀ (ρ : IEnv P) (cmd : CmdExt P) (σ' : SemanticStore P)
      (evs : Trace P) (st : obs.St), (IConfig.stmt (.cmd cmd) ρ).Denoting F →
    E F (InterpLang.absStore F ρ.store.get) cmd σ' evs →
    ∃ (f0 : Nat) (σi : IStore P) (st' : obs.St), InterpLang.absStore F σi.get = σ' ∧
      RStore.Denoting F σi.get ∧
      (∀ i j fuel, f0 ≤ i → f0 ≤ j → f0 ≤ fuel →
        obs.run (stepInterp (callStepOf (m := m) π i j) fuel (.stmt (.cmd cmd) ρ)) cfgr st
          = (.ok (.terminal { ρ with store := σi }), st'))
      ∧ obs.TraceExt F st st' evs

omit [HasFvars P] in
/-- `CmdArmComplete` holds for the base-command arm `CmdArmEng R` of the engine-realizable command
    relation: every engine-realizable base-command evaluation is performed by `stepCmd π i j`, for
    an observation whose `emit` always succeeds and whose `choose` resolves `R`, when the bounded
    evaluator is fuel-monotone. -/
private theorem call_cmdArmComplete_cmd (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr)) (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P) :
    CmdArmComplete obs π cfgr F (CmdArmEng R) := by
  rintro ρ _ _ _ st ⟨hd, hf⟩ ⟨_, rfl, heval⟩
  obtain ⟨n, σi, s, hσ, hdi, hrun, htrace⟩ :=
    obs_stepBaseCmdStore_complete _ _ hemit hchoose hMono hd heval st
  refine ⟨n, σi, s, hσ, hdi, fun _ j _ _ hj _ => ?_, htrace⟩
  simp [hf, hrun j hj]

/-- `CmdArmComplete` holds for the `.call` arm whose callee body runs at call-nesting height `n`,
    given that every engine-realizable command evaluation at height `n` is performed by
    `stepCmd π i j` at every large enough `i`, `j` and fuel (`ih`): every engine-realizable `.call`
    evaluation is then so performed, for an observation whose `emit` always succeeds and whose
    `choose` resolves `R`, when the bounded evaluator is fuel-monotone.  The call arm carries the
    engine's argument evaluation and write-back facts. -/
private theorem call_cmdArmComplete_call (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (n : Nat) (ih : CmdArmComplete obs π cfgr F (EvalCommandEngAtE π R n)) :
    CmdArmComplete obs π cfgr F
      (CallArmEng π (BodyExecEngOf R (EvalCommandEngAtE π R n))) := by
  rintro ρ _ _ _ st ⟨hd, hf⟩
    ⟨nm, ⟨hdr, spec, body⟩, args, md, σAO, σf, evB, rfl, hπ, hentry, hB, hexit, rfl, hargs, hwb⟩
  refine (stepCmd_call_complete obs π cfgr hMono (Pend := fun _ _ => True)
    (Q := fun _ => True) (o := []) (o' := []) (fun revs _ st _ _ =>
      (obs_forM_emit_complete obs cfgr hemit revs st).imp fun _ ⟨a, b⟩ => ⟨a, trivial, b⟩)
    hd hf hπ hentry hexit hargs hwb (fun er habs hder st _ => ?_) (fun _ _ => trivial) st
    trivial).imp
    fun _ ⟨σi, st', h1, h2, hrun, _, ht⟩ =>
      ⟨σi, st', h1, h2, fun i j _ hi hj _ => hrun i j hi hj, ht⟩
  cases body with
  | structured ss =>
    obtain ⟨ρ', hstar, rfl⟩ := hB
    obtain ⟨f, fin, s', ⟨hfd, -, hfin⟩, hr, ht⟩ := runInterp_complete_fam _ _ _
      (stepInterpCompleteFam_of_arms _ (callStepOf π) _ hchoose hMono ih
        (evalCommandEngAtE_cmdDefsSound π R n))
      (.stmt (.block "" ss #[]) ⟨.ofStore er, InterpLang.rfactory F⟩)
      (.terminal ρ') evB trivial ⟨(by simpa using hder), rfl⟩
      (by simpa [IConfig.abs, IEnv.abs, habs] using hstar) (.inl ⟨_, rfl⟩) st
    obtain ⟨ie, rfl, rfl⟩ := (IConfig.abs_eq_terminal (P := P) _ _ _).1 hfin
    exact ⟨f, ie.store.get, s', rfl, hfd.1, fun i j hi hj => by
      simp [runCallee, hr i j j hi hj hj], trivial, ht⟩
  | cfg g => exact hB.elim

/-- At every call-nesting height `n`, `CmdArmComplete` holds for the engine-realizable command
    relation `EvalCommandEngAtE π R n`: every engine-realizable command evaluation, base command or
    `.call`, is performed by `stepCmd π i j` at every sufficiently large call-depth budget `i`,
    stepper index `j` and driver fuel, for an observation whose `emit` always succeeds and whose
    `choose` resolves `R`, when the bounded evaluator is fuel-monotone. -/
theorem call_cmdArmComplete_all (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P) :
    ∀ n, CmdArmComplete obs π cfgr F (EvalCommandEngAtE π R n) :=
  have hcmd := call_cmdArmComplete_cmd _ π _ hemit hchoose hMono
  fun n => n.rec hcmd fun _ ih _ _ _ _ _ hd h =>
    h.elim (hcmd _ _ _ _ _ hd)
      (call_cmdArmComplete_call _ _ _ hemit hchoose hMono _ ih _ _ _ _ _
        hd)

/-- Per-step completeness of the call-aware engine at call-nesting height `n`: every
    engine-realizable step over `EvalCommandEngAtE π R n` is performed by one
    `stepInterp (stepCmd π d)` step at every sufficiently large call-depth limit `d` and fuel, from
    every state (`StepInterpCompleteFam` of the family `fun d _ => stepCmd π d`), for an
    observation whose `emit` always succeeds and whose `choose` resolves `R`, when the bounded
    evaluator is fuel-monotone. -/
private theorem call_stepInterpCompleteParam (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (n : Nat) :
    StepInterpCompleteFam obs (fun d _ => stepCmd π d) cfgr F R (EvalCommandEngAtE π R n) :=
  fun c _ _ st ht hd h =>
  have ⟨n, c', s, hrun, habs, hdn, htr, htrace⟩ := stepInterpCompleteFam_of_arms _ (callStepOf π) _
    hchoose hMono
    (call_cmdArmComplete_all _ π _ hemit hchoose hMono n)
    (evalCommandEngAtE_cmdDefsSound π R n) _ _ _ st ht hd h
  have hstep : ∀ d f c, stepInterp (callStepOf (m := m) π d f) f c = stepInterp (stepCmd π d) f c :=
    fun _ _ c => by induction c <;> simp [*, stepInterp]
  ⟨n, c', s, fun d _ f hd _ k => hstep d f c ▸ hrun d f f hd k k, habs, hdn, htr, htrace⟩

/-- **Whole-run completeness at call-nesting height `n`:** for an observation whose `emit` always
    succeeds and whose `choose` resolves `R`, when the bounded evaluator is fuel-monotone, every
    engine-realizable run at height `n`
    from the abstraction of a tracked configuration `start`, ending at a configuration `final` the
    monadic interpreter stops at, is reproduced by `runCallInterp π` from `start` to a
    configuration denoting `final` (`IConfig.Denotes`) at every sufficiently large fuel and
    call-depth limit, from every state, emitting runtime events denoting exactly the run's
    events. -/
theorem call_runCallInterp_complete (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (n : Nat) (start : IConfig P (CmdExt P)) (final : Config P (CmdExt P))
    (evs : List (Event P)) (hds : start.Denoting F) (htr : start.Tracked)
    (hrun : StepEngAtStarE π R n (start.abs F) evs final) (hdone : Config.Done final)
    (st : obs.St) :
    ∃ (f0 : Nat) (final' : IConfig P (CmdExt P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterp π fuel start d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  (runInterp_complete_fam _ _ _ (call_stepInterpCompleteParam _ _ _ hemit hchoose hMono n) _ _ _
    htr hds hrun hdone st).imp fun f0 ⟨c, s, hc, a, b⟩ =>
      ⟨c, s, hc, fun fuel d hf hd => a d f0 fuel hd (Nat.le_refl _) hf, b⟩

/-- **Call-aware whole-run completeness against the reference semantics**: for an observation whose
    `emit` always succeeds and whose `choose` resolves `R`, when the bounded evaluator is
    fuel-monotone, a reference run of
    `StepStmtExtStarE π` from `start` ending at a configuration `final` the monadic interpreter
    stops at is reproduced by `runCallInterp π` from an interpreter configuration `istart` denoting
    `start` (`IConfig.Denotes`) to one denoting `final` at every sufficiently large fuel and
    call-depth limit, emitting runtime events denoting exactly the run's events, provided every
    reference step from a configuration reachable from `start` is an engine-realizable step at
    call-nesting height `n` with the same events and successor (`EngineAgreesFrom`). -/
theorem call_runCallInterp_complete_of_agree (obs : InterpObs P m)
    (π : String → Option (Procedure P (CmdExt P) Hdr))
    (cfgr : obs.Cfg) {F : P.Factory} {R : ChoiceRecord P}
    (hemit : EmitTotal obs cfgr) (hchoose : ChooseResolves obs cfgr F R)
    (hMono : BoundedEvalMono P)
    (n : Nat) (start final : Config P (CmdExt P)) (evs : List (Event P))
    (istart : IConfig P (CmdExt P)) (hstart : istart.Denotes F start)
    (hag : EngineAgreesFrom (P := P) R (EvalCmdExtE π) (EvalCommandEngAtE π R n)
      start)
    (hrun : StepStmtExtStarE π start evs final) (hdone : Config.Done final) (st : obs.St) :
    ∃ (f0 : Nat) (final' : IConfig P (CmdExt P)) (st' : obs.St), final'.Denotes F final ∧
      (∀ fuel d, f0 ≤ fuel → f0 ≤ d →
        obs.run (runCallInterp π fuel istart d) cfgr st = (.ok final', st'))
      ∧ obs.TraceExt F st st' evs :=
  call_runCallInterp_complete _ _ _ hemit hchoose hMono n _ _ _ hstart.1
    hstart.2.1 (hstart.2.2 ▸ StepStmtStarE.toStepEngParamStarE hrun hag) hdone st

end CallComplete

/-! ## Reference runs that read their choices off an oracle

A nondeterministic statement or command resolves a *choice*: the value a nondeterministic
`.init`/`.set` writes, or the Boolean a `.nondet` guard is read as (`tt` for the then-branch or
loop entry, `ff` for the else-branch or loop exit).  The relations below pair a configuration
with an oracle and pop each choice off its front, in execution order and inside callee bodies
at any depth, which is the order in which `ReplayM`'s `choose` consumes its oracle. -/

/-- A call-aware command relation that reads choices off an oracle: `E f σ c σ' evs o o'`
    says that `c` runs from store `σ` to `σ'` emitting `evs` and turns the oracle `o` into
    `o'`. -/
abbrev OracleCmdRel (P : PureExpr) :=
  P.Factory → SemanticStore P → CmdExt P → SemanticStore P → Trace P →
    List P.Val → List P.Val → Prop

/-- One reference statement step over the command relation `E`, on a configuration paired with
    an oracle.  A step that resolves no choice and runs no command leaves the oracle alone; a
    `.nondet` guard pops the Boolean it is read as: `tt` for the then-branch or loop entry, `ff`
    for the else-branch or loop exit. -/
inductive OracleStepE (E : OracleCmdRel P) :
    Config P (CmdExt P) × List P.Val → List (Event P) →
      Config P (CmdExt P) × List P.Val → Prop where
  /-- A step that resolves no choice and runs no command. -/
  | step_det {c c' : Config P (CmdExt P)} {evs : List (Event P)} {o : List P.Val} :
      StepEngParamE P (ChoiceRecord.bot P) (fun _ _ _ _ _ => False) c evs c' →
      OracleStepE E (c, o) evs (c', o)
  /-- A nondeterministic `ite` reads `tt` to take the then-branch. -/
  | step_ite_then :
      OracleStepE E (.stmt (.ite .nondet tss ess md) ρ, HasBool.ttVal ρ.factory :: o) []
        (.block .none ρ.store (.stmts tss ρ), o)
  /-- A nondeterministic `ite` reads `ff` to take the else-branch. -/
  | step_ite_else :
      OracleStepE E (.stmt (.ite .nondet tss ess md) ρ, HasBool.ffVal ρ.factory :: o) []
        (.block .none ρ.store (.stmts ess ρ), o)
  /-- A nondeterministic `loop` reads `tt` to enter its body. -/
  | step_loop_enter :
      OracleStepE E (.stmt (.loop .nondet m inv body md) ρ, HasBool.ttVal ρ.factory :: o) []
        (.seq (.block .none ρ.store (.stmts body ρ)) [.loop .nondet m inv body md], o)
  /-- A nondeterministic `loop` reads `ff` to exit. -/
  | step_loop_exit :
      OracleStepE E (.stmt (.loop .nondet m inv body md) ρ, HasBool.ffVal ρ.factory :: o) [] (.terminal ρ, o)
  /-- Execute one command through `E`. -/
  | step_cmd :
      E ρ.factory ρ.store cmd σ' evs o o' →
      OracleStepE E (.stmt (.cmd cmd) ρ, o) evs (.terminal { ρ with store := σ' }, o')
  /-- Lift one inner sequence step. -/
  | step_seq_inner :
      OracleStepE E (inner, o) evs (inner', o') →
      OracleStepE E (.seq inner ss, o) evs (.seq inner' ss, o')
  /-- Lift one inner block step. -/
  | step_block_body :
      OracleStepE E (inner, o) evs (inner', o') →
      OracleStepE E (.block label σp inner, o) evs (.block label σp inner', o')

/-- The base-command arm: an engine-realizable evaluation of a base command (`EvalCmdEngE`, its
    nondeterministic values typed: `ChoiceRecord.typed`).  A deterministic command leaves the
    oracle alone; a nondeterministic `.init`/`.set` of `x` pops the value it writes. -/
@[expose] def OracleCmdBase : OracleCmdRel P := fun f σ c σ' evs o o' =>
  ∃ base, c = .cmd base ∧ EvalCmdEngE P (ChoiceRecord.typed P) f σ base σ' evs ∧
    ((CmdDeterministic base = true ∧ o' = o) ∨
      ∃ x v, o = v :: o' ∧ σ' x = some v ∧
        ((∃ ty md, base = .init x ty .nondet md) ∨ ∃ md, base = .set x .nondet md))

/-- The call arm over the callee-command relation `E`: the reference `call_sem` rule on a
    structured callee, whose body run reads its choices off the oracle, plus the engine's facts
    about the call (`CallArgsReach`, `WriteBackOK`). -/
@[expose] def OracleCallArm (π : String → Option (Procedure P (CmdExt P) Hdr))
    (E : OracleCmdRel P) : OracleCmdRel P := fun f σ c σ' evs o o' =>
  ∃ nm p args md σAO ss ρ' bodyEvs,
    c = .call nm args md ∧ π nm = some p ∧ p.body = .structured ss ∧
    CallEntry f σ p args σAO ∧
    ReflTransTrace (OracleStepE E)
      (.stmt (Stmt.block "" ss #[]) ⟨σAO, f⟩, o) bodyEvs (.terminal ρ', o') ∧
    CallExit f σ p args ρ'.store σ' ∧
    evs = defaultAssertEvents f σAO (checksAtCall md p.spec.preconditions) ++ bodyEvs ++
      defaultAssertEvents f ρ'.store p.spec.postconditions ∧
    CallArgsReach f σ args ∧ WriteBackOK f σ p args ρ'.store

/-- The oracle-reading command relation at call-nesting height `n`: base commands at every
    height, and calls whose callee body runs at height `n - 1`. -/
@[expose] def OracleCmdAt (π : String → Option (Procedure P (CmdExt P) Hdr))
    : Nat → OracleCmdRel P
  | 0 => OracleCmdBase
  | n + 1 => fun f σ c σ' evs o o' =>
      OracleCmdBase f σ c σ' evs o o' ∨ OracleCallArm π (OracleCmdAt π n) f σ c σ' evs o o'

/-- **The choice sequence of a reference run.**  `RunChoices π c evs c' cs`: a run of the
    call-aware reference semantics from `c` to `c'` emitting `evs` resolves its choices, in
    execution order and including those inside callee bodies at any depth, as the values `cs`.
    Read off the front of any oracle `cs ++ rest`, they leave `rest`. -/
@[expose] def RunChoices (π : String → Option (Procedure P (CmdExt P) Hdr))
    (c : Config P (CmdExt P)) (evs : List (Event P))
    (c' : Config P (CmdExt P)) (cs : List P.Val) : Prop :=
  ∃ n, ∀ rest, ReflTransTrace (OracleStepE (OracleCmdAt π n)) (c, cs ++ rest) evs (c', rest)

/-- `Stmt.noNondetGuards` lifted to a configuration: no guard still to be executed in `c` is
    `.nondet`. -/
@[expose] def _root_.Imperative.Config.noNondetGuards {CmdT : Type} :
    Config P CmdT → Bool
  | .stmt s _ => Stmt.noNondetGuards s
  | .stmts ss _ => Block.noNondetGuards ss
  | .terminal _ => true
  | .exiting _ _ => true
  | .block _ _ inner => Config.noNondetGuards inner
  | .seq inner ss => Config.noNondetGuards inner && Block.noNondetGuards ss

/-- A call-aware command that resolves no choice: a deterministic base command, or a call. -/
@[expose] def CmdExtDeterministic : CmdExt P → Bool
  | .cmd c => CmdDeterministic c
  | .call _ _ _ => true

/-- **A deterministic call-aware program**: no `.nondet` guard and no nondeterministic base
    command, in the statements still to be executed in `c` and in every structured callee body
    of `π`. -/
@[expose] def ProgDeterministic (π : String → Option (Procedure P (CmdExt P) Hdr))
    (c : Config P (CmdExt P)) : Prop :=
  (Config.noNondetGuards c = true ∧ Config.allCmds CmdExtDeterministic c) ∧
  ∀ n p ss, π n = some p → p.body = .structured ss →
    Block.noNondetGuards ss = true ∧ Block.allCmds CmdExtDeterministic ss = true

/-! ## The replay configuration of `genuine` -/

section CallReplayComplete

/-- The replay configuration `genuine` runs at: strict oracle. -/
abbrev replayCfgOf (_target : AssertId P) (_fuel : Nat) :
    (obsReplay (P := P)).Cfg :=
  { oracleConfig := .strict }

end CallReplayComplete

end Calls

end -- public section

end Imperative

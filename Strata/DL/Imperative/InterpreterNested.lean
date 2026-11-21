/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterConfig
public import Strata.Util.DecidableEqProps
import Strata.DL.Imperative.InterpreterProps

/-! # Running nested blocks without re-walking the context

A step of `stepInterp` from a configuration under `d` nested contexts walks and rebuilds all `d`
of them, so a run that descends `d` nested blocks, as the replay of a nondeterministic `if` tower
does, takes time quadratic in `d`. `runInterpNested` computes the same run as `runInterp`, but
runs the configuration inside a sequence or block context as a run of that configuration alone,
and then the steps from the context around the configuration it stops at. A block context's frame
is updated by every inner step (`ScopeFrame.record`), so the inner run also returns its frame
(`runInterpFrame`).

`IConfig.samePointN` is computed with its statement lists compared by pointer first
(`IConfig.samePointNPtr`, `IConfig.samePointN_eq_ptr`).

Key definitions: `runInterpFrame`, `runInterpNested`. Key theorems: `runInterp_eq_nested`,
`IConfig.samePointN_eq_ptr`. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type} {m : Type → Type}

/-- `IConfig.samePointN` with its statements and statement lists compared by pointer first
    (`ptrFastEq`). -/
def IConfig.samePointNPtr [InterpLang P] [DecidableEq CmdT] [DecidableEq P.Expr]
    (c c' : IConfig P CmdT) : Bool :=
  match c, c' with
  | .stmt s _, .stmt s' _ => ptrFastEq s s'
  | .stmts ss _, .stmts ss' _ => ptrFastEq ss ss'
  | .terminal _, .terminal _ => true
  | .exiting l _, .exiting l' _ => l == l'
  | .seq i rest, .seq i' rest' => i.samePointNPtr i' && ptrFastEq rest rest'
  | .seqs i k, .seqs i' k' => k == k' && i.samePointNPtr i'
  | .block l _ i, .block l' _ i' => l == l' && i.samePointNPtr i'
  | _, _ => false

/-- `IConfig.samePointN` is `IConfig.samePointNPtr`, which the compiler runs in its place. -/
@[csimp] theorem IConfig.samePointN_eq_ptr :
    @IConfig.samePointN = @IConfig.samePointNPtr := by
  funext P CmdT _ _ _ c c'
  induction c generalizing c' <;> cases c' <;>
    simp_all [IConfig.samePointN, IConfig.samePointNPtr, ptrFastEq_eq_decide]
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- `runInterp`, also returning the fuel left when it stops and the frame `fr` recorded with the
    level command of every step taken (`ScopeFrame.record`): the frame a block context around
    the configuration holds when the configuration stops. -/
@[expose] def runInterpFrame (stepCmd : StepCmdM P CmdT m) :
    Nat → IConfig P CmdT → ScopeFrame P → m (IConfig P CmdT × Nat × ScopeFrame P)
  | fuel, cfg, fr =>
    match cfg with
    | .terminal _ | .exiting _ _ => pure (cfg, fuel, fr)
    | _ =>
      match fuel with
      | 0 => throw .replayFuelExhausted
      | fuel + 1 => do
        let next ← stepInterp stepCmd (fuel + 1) cfg
        runInterpFrame stepCmd fuel next (fr.record cfg.levelCmd?)

/-- Is the configuration a context whose step is the step of one inner configuration `c` that
    has not stopped, rebuilt around the result whatever it is: a sequence context `.seq c rest`, a
    block context `.block l fr c`, or `k + 1` sequence contexts around one of these,
    `.seqs (.seq c rest) k` or `.seqs (.block l fr c) k`. -/
@[expose] def IConfig.nestedInner : IConfig P CmdT → Bool
  | .seq c _ | .block _ _ c | .seqs (.seq c _) _ | .seqs (.block _ _ c) _ => !decide c.Done
  | _ => false

/-- `runInterpFrame`, computed with the run of a context that `IConfig.nestedInner` holds of split
    into the run of its inner configuration on its own (from the frame of a block context, from
    the current frame otherwise), then the run from the context rebuilt around the configuration
    the inner run stops at; `.seqs (.block l fr c) k` is split into the run of the block context.
    Every inner configuration is split again in turn, so `stepInterp` is only applied to a
    configuration `IConfig.nestedInner` does not hold of: a statement, a statement list, a stopped
    configuration, or one context around a stopped configuration, under which each step walks a
    bounded number of contexts. The run from a configuration nested `d` contexts deep then takes
    time linear in the number of steps and in `d`, also when statements follow the contexts. -/
@[expose] def runInterpNested (stepCmd : StepCmdM P CmdT m) :
    Nat → IConfig P CmdT → ScopeFrame P → m (IConfig P CmdT × Nat × ScopeFrame P)
  | fuel, cfg, fr =>
    if hn : cfg.nestedInner then
      match cfg, hn with
      | .seq c rest, _ => do
        let (c', r, fr') ← runInterpNested stepCmd fuel c fr
        if r < fuel then runInterpNested stepCmd r (.seq c' rest) fr'
        else throw .replayFuelExhausted
      | .block l bfr c, _ => do
        let (c', r, bfr') ← runInterpNested stepCmd fuel c bfr
        if r < fuel then runInterpNested stepCmd r (.block l bfr' c') fr
        else throw .replayFuelExhausted
      | .seqs (.seq c rest) k, _ => do
        let (c', r, fr') ← runInterpNested stepCmd fuel c fr
        if r < fuel then runInterpNested stepCmd r (.seqs (.seq c' rest) k) fr'
        else throw .replayFuelExhausted
      | .seqs x k, _ => do
        let (x', r, fr') ← runInterpNested stepCmd fuel x fr
        if r < fuel then runInterpNested stepCmd r (.seqs x' k) fr'
        else throw .replayFuelExhausted
    else
      match cfg with
      | .terminal _ | .exiting _ _ => pure (cfg, fuel, fr)
      | _ =>
        match fuel with
        | 0 => throw .replayFuelExhausted
        | fuel + 1 => do
          let next ← stepInterp stepCmd (fuel + 1) cfg
          runInterpNested stepCmd fuel next (fr.record cfg.levelCmd?)
termination_by fuel cfg => (fuel, sizeOf cfg)
decreasing_by all_goals first | (apply Prod.Lex.right; simp; omega) | (apply Prod.Lex.left; omega)

omit [HasBool P] [DecidableEq P.Expr] in
/-- A frame recorded with no level command is unchanged. -/
private theorem ScopeFrame.record_none (fr : ScopeFrame P) :
    fr.record (CmdT := CmdT) none = fr := by
  cases h : fr.defined <;> simp [ScopeFrame.record, h]

/-- `runInterpFrame` at successor fuel from a configuration that has not stopped takes a step. -/
private theorem runInterpFrame_succ (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (cfg : IConfig P CmdT) (fr : ScopeFrame P) (hc : ¬ cfg.Done) :
    runInterpFrame stepCmd (fuel + 1) cfg fr = (do
      let next ← stepInterp stepCmd (fuel + 1) cfg
      runInterpFrame stepCmd fuel next (fr.record cfg.levelCmd?)) := by
  cases cfg <;> simp_all [runInterpFrame, IConfig.Done]

variable [LawfulMonad m]

/-- A step from sequence contexts around a sequence context whose inner configuration has not
    stopped is the inner configuration's step, under the contexts. -/
private theorem stepInterp_seqs_seq (stepCmd : StepCmdM P CmdT m) (fuel : Nat) (c : IConfig P CmdT)
    (rest : List (Stmt P CmdT)) (k : Nat) (hc : ¬ c.Done) :
    stepInterp stepCmd fuel (.seqs (.seq c rest) k) = (do
      let c' ← stepInterp stepCmd fuel c
      pure (.seqs (.seq c' rest) k)) := by
  cases c <;> simp_all [stepInterp, IConfig.Done]

/-- A step from sequence contexts around a block context is the block context's step, under the
    sequence contexts: a block context steps to a block context or to a stopped configuration. -/
private theorem stepInterp_seqs_blockCtx (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (l : Option String)
    (fr : ScopeFrame P) (c : IConfig P CmdT) (k : Nat) :
    stepInterp stepCmd fuel (.seqs (.block l fr c) k) = (do
      let x' ← stepInterp stepCmd fuel (.block l fr c)
      pure (.seqs x' k)) := by
  cases c <;> simp only [stepInterp] <;> (try split) <;> simp

/-- A continuation bound to `runInterpFrame` only reads results whose fuel is at most the fuel
    the run started with. -/
private theorem runInterpFrame_bind_le {β : Type} (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (c : IConfig P CmdT) (fr : ScopeFrame P) (k k' : IConfig P CmdT × Nat × ScopeFrame P → m β),
    (∀ x, x.2.1 ≤ fuel → k x = k' x) →
    runInterpFrame stepCmd fuel c fr >>= k = runInterpFrame stepCmd fuel c fr >>= k' := by
  induction fuel with
  | zero =>
    intro c fr k k' h
    cases c <;> simp_all [runInterpFrame]
  | succ fuel ih =>
    intro c fr k k' h
    by_cases hc : c.Done
    · cases c <;> simp_all [runInterpFrame, IConfig.Done]
    · rw [runInterpFrame_succ _ _ _ _ hc, bind_assoc, bind_assoc]
      exact bind_congr fun _ => ih _ _ _ _ fun x hx => h x (Nat.le_succ_of_le hx)

/-- A continuation bound to `runInterpFrame` from a configuration that has not stopped only reads
    results whose fuel is below the fuel the run started with. -/
private theorem runInterpFrame_bind_lt {β : Type} (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (c : IConfig P CmdT) (fr : ScopeFrame P) (hc : ¬ c.Done)
    (k k' : IConfig P CmdT × Nat × ScopeFrame P → m β) (h : ∀ x, x.2.1 < fuel → k x = k' x) :
    runInterpFrame stepCmd fuel c fr >>= k = runInterpFrame stepCmd fuel c fr >>= k' := by
  cases fuel with
  | zero => cases c <;> simp_all [runInterpFrame, IConfig.Done]
  | succ fuel =>
    rw [runInterpFrame_succ _ _ _ _ hc, bind_assoc, bind_assoc]
    exact bind_congr fun _ =>
      runInterpFrame_bind_le hthrow _ _ _ _ _ _ fun x hx => h x (Nat.lt_succ_of_le hx)

/-- The run from a sequence context is the run of its inner configuration, then the run from
    the context around the configuration it stops at. -/
private theorem runInterpFrame_seq (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (c : IConfig P CmdT) (rest : List (Stmt P CmdT)) (fr : ScopeFrame P),
    runInterpFrame stepCmd fuel (.seq c rest) fr = (do
      let (c', r, fr') ← runInterpFrame stepCmd fuel c fr
      runInterpFrame stepCmd r (.seq c' rest) fr') := by
  induction fuel with
  | zero =>
    intro c rest fr
    cases c <;> simp_all [runInterpFrame]
  | succ fuel ih =>
    intro c rest fr
    by_cases hc : c.Done
    · cases c <;> simp_all [IConfig.Done, runInterpFrame]
    · rw [runInterpFrame_succ _ _ _ _ (by simp [IConfig.Done]), runInterpFrame_succ _ _ _ _ hc,
        stepInterp_seq_notDone stepCmd _ hc rest]
      simp [ih, IConfig.levelCmd?]

/-- The run from sequence contexts around a sequence context is the run of its inner
    configuration, then the run from the contexts around the configuration it stops at. -/
private theorem runInterpFrame_seqs_seq (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (c : IConfig P CmdT) (rest : List (Stmt P CmdT)) (k : Nat) (fr : ScopeFrame P),
    runInterpFrame stepCmd fuel (.seqs (.seq c rest) k) fr = (do
      let (c', r, fr') ← runInterpFrame stepCmd fuel c fr
      runInterpFrame stepCmd r (.seqs (.seq c' rest) k) fr') := by
  induction fuel with
  | zero =>
    intro c rest k fr
    cases c <;> simp_all [runInterpFrame]
  | succ fuel ih =>
    intro c rest k fr
    by_cases hc : c.Done
    · cases c <;> simp_all [IConfig.Done, runInterpFrame]
    · rw [runInterpFrame_succ _ _ _ _ (by simp [IConfig.Done]), runInterpFrame_succ _ _ _ _ hc,
        stepInterp_seqs_seq stepCmd _ c rest k hc]
      simp [ih, IConfig.levelCmd?]

/-- The run from a block context is the run of its inner configuration from the context's frame,
    then the run from the context around the configuration it stops at, with the frame it
    returns; the outer frame is not changed by the inner run. -/
private theorem runInterpFrame_block (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (l : Option String) (bfr : ScopeFrame P) (c : IConfig P CmdT) (fr : ScopeFrame P),
    runInterpFrame stepCmd fuel (.block l bfr c) fr = (do
      let (c', r, bfr') ← runInterpFrame stepCmd fuel c bfr
      runInterpFrame stepCmd r (.block l bfr' c') fr) := by
  induction fuel with
  | zero =>
    intro l bfr c fr
    cases c <;> simp_all [runInterpFrame]
  | succ fuel ih =>
    intro l bfr c fr
    by_cases hc : c.Done
    · cases c <;> simp_all [IConfig.Done, runInterpFrame]
    · rw [runInterpFrame_succ _ _ _ _ (by simp [IConfig.Done]), runInterpFrame_succ _ _ _ _ hc,
        stepInterp_block_notDone stepCmd _ hc l bfr]
      simp [ih, IConfig.levelCmd?, ScopeFrame.record_none]

/-- The run from sequence contexts around a block context is the run of the block context, then
    the run from the sequence contexts around the configuration it stops at. -/
private theorem runInterpFrame_seqs_blockCtx (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (l : Option String) (bfr : ScopeFrame P) (c : IConfig P CmdT) (k : Nat) (fr : ScopeFrame P),
    runInterpFrame stepCmd fuel (.seqs (.block l bfr c) k) fr = (do
      let (x', r, fr') ← runInterpFrame stepCmd fuel (.block l bfr c) fr
      runInterpFrame stepCmd r (.seqs x' k) fr') := by
  induction fuel with
  | zero => intro l bfr c k fr; simp [runInterpFrame, hthrow]
  | succ fuel ih =>
    intro l bfr c k fr
    rw [runInterpFrame_succ _ _ _ _ (by simp [IConfig.Done]),
      runInterpFrame_succ _ _ _ _ (by simp [IConfig.Done]), stepInterp_seqs_blockCtx]
    by_cases hc : c.Done
    · cases c <;> simp_all [IConfig.Done, runInterpFrame, stepInterp, IConfig.levelCmd?] <;>
        split <;> simp [runInterpFrame]
    · simp [stepInterp_block_notDone _ _ hc, ih, IConfig.levelCmd?, ScopeFrame.record_none]

/-- The nested run gives the same result as the frame-threaded run `runInterpFrame`, at every
    fuel, configuration and frame. -/
private theorem runInterpNested_eq (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m)
    (fuel : Nat) (cfg : IConfig P CmdT) (fr : ScopeFrame P) :
    runInterpNested stepCmd fuel cfg fr = runInterpFrame stepCmd fuel cfg fr := by
  induction fuel, cfg, fr using runInterpNested.induct with
  | case1 _ _ _ _ hn ih ih' | case2 _ _ _ _ _ hn ih ih' | case3 _ _ _ _ _ hn ih ih' =>
    rw [runInterpNested.eq_def]
    simp only [hn, ↓reduceDIte, ih]
    first
      | rw [runInterpFrame_seqs_seq hthrow]
      | rw [runInterpFrame_seq hthrow]
      | rw [runInterpFrame_block hthrow]
    exact runInterpFrame_bind_lt hthrow _ _ _ _ (by simpa [IConfig.nestedInner] using hn) _ _
      fun ⟨c', r, fr'⟩ hx => by
        simp only at hx ⊢
        simp [hx, ih' c' r fr' hx]
  | case4 fuel fr x k hn hx ih ih' =>
    cases x
    case seq c rest => exact (hx c rest hn rfl .rfl).elim
    case block l bfr c =>
      rw [runInterpNested.eq_def]
      simp only [hn, ↓reduceDIte, ih]
      rw [runInterpFrame_seqs_blockCtx hthrow]
      exact runInterpFrame_bind_lt hthrow _ _ _ _ (by simp [IConfig.Done]) _ _
        fun ⟨x', r, fr'⟩ hx => by
          simp only at hx ⊢
          simp [hx, ih' x' r fr' hx]
    all_goals simp [IConfig.nestedInner] at hn
  | case5 | case6 => rw [runInterpNested.eq_def]; simp_all [runInterpFrame, IConfig.nestedInner]
  | case7 cfg _ hn h1 h2 | case8 cfg _ _ hn h1 h2 _ =>
    rw [runInterpNested.eq_def]
    simp only [hn, Bool.false_eq_true, ↓reduceDIte]
    cases cfg
    case terminal => exact (h1 _ hn rfl .rfl).elim
    case exiting => exact (h2 _ _ hn rfl .rfl).elim
    all_goals simp_all [runInterpFrame]

/-- `runInterp` is the configuration `runInterpFrame` stops at, from any frame. -/
private theorem runInterp_eq_frame (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat) :
    ∀ (cfg : IConfig P CmdT) (fr : ScopeFrame P),
    runInterp stepCmd fuel cfg = (·.1) <$> runInterpFrame stepCmd fuel cfg fr := by
  induction fuel with
  | zero => intro cfg fr; cases cfg <;> simp [runInterp, runInterpFrame, ← bind_pure_comp, hthrow]
  | succ fuel ih =>
    intro cfg fr
    cases cfg <;> simp only [runInterp, runInterpFrame, map_bind] <;>
      first | exact bind_congr fun _ => ih _ _ | simp

/-- `runInterp` is the configuration `runInterpNested` stops at, from any frame, in a monad whose
    `throw` ends the computation. -/
theorem runInterp_eq_nested (hthrow : ∀ {α β : Type} (e : StopReason)
    (f : α → m β), (throw e : m α) >>= f = throw e) (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (cfg : IConfig P CmdT) (fr : ScopeFrame P) :
    runInterp stepCmd fuel cfg = (·.1) <$> runInterpNested stepCmd fuel cfg fr := by
  rw [runInterpNested_eq hthrow, runInterp_eq_frame hthrow]

end

end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterSound
public import Strata.DL.Imperative.StmtSemanticsDeterminism

/-! # Monadic-interpreter↔semantics contract

This module defines the two statements that connect a run of the monadic interpreter in any monad
instance to the small-step *reference semantics* `StepStmtStarE`/`EvalCmdE`:
soundness `RunInterpSound` and completeness `RunInterpComplete`. They are stated
monad-generically, over an abstract observation of a run (`InterpObs`), not over any
one instance's concrete state. Lemmas about the definitions of this module are in
`InterpreterSemanticsSpecProps.lean`.

Why generic: the engine (`runInterp`/`stepInterp`/`stepBaseCmdStore`) is
monad-generic and feeds `emit` the *same* `Event`s regardless of instance, so
the run↔semantics link is a property of the observed event trace, not of any one
instance.  Abstracting the observation (below) hands the link to all instances at
once, in particular to the counterexample-replay instance `ReplayM` whose replay
verdict is otherwise disconnected from the semantics.

## The observation abstraction

`InterpObs P m` bundles how to *observe* a run of monad `m`: a `run` that projects
a computation to its `(outcome, state)` pair under a reader config, a `trace`
projection reading the emitted-event list out of the state, and the algebraic
laws these satisfy.  The laws are the "hypotheses on the monad" the contract rests
on, chosen to be satisfiable by both instances:

* `ReplayM P` — `Cfg := ReplayCfg P`, `St := ReplayState P`, records-only `emit`
  (halting is the *post-hoc* `haltOn` scan over the finished trace, not an `emit`
  effect).
* `EvalM` (Core) — `Cfg := Core.EvalOpts` (the eval fuel plus the assert/assume
  policies), `St := EvalState`; its `emit` evaluates the assert and may **throw**.
  On a false assert condition under `AssertPolicy.halt` the event is prepended
  before the throw (`ExceptT` outer of `StateT` ⇒ the state survives the error);
  on a condition that does not reduce to a Boolean literal it throws *without*
  recording, which is why `emit_trace` is guarded by the emit having succeeded.  The
  guarded form suffices: soundness only reads the trace off a step whose run succeeded.

`choose_sound` says any value `choose` resolves to is a valid nondeterministic
value (`isValue ∧ hasType`) and that `choose` emits nothing — this is what lets a
`choose` step be matched to `EvalCmdE`'s nondet constructors in the soundness
direction.

## The engine-realizable relations

The completeness direction cannot be stated against the bare reference relations,
because the engine checks more than they do and stops in fewer places.  The
refinements it is stated against are defined here, next to the contract:

* `Config.Done` — the configurations `runInterp` stops at, hence the only ones a
  run can return.
* `ChoiceRecord P` — which value a nondeterministic choice of type `ty` at factory
  `f` and store `σ` resolves to; a derivation's nondeterministic rules are
  annotated with it.
* `EvalCmdEngE P R` — the reference command relation `EvalCmdE` plus the engine's
  own executable value checks on the deterministic `.init`/`.set` rules, with the
  nondeterministic `.init` value drawn from `R`.
* `StepEngE P R` / `StepEngStarE` — the statement-level relation and
  its traced reflexive-transitive closure.  `StepEngE.toStepStmtE` and
  `StepEngStarE.toStepStmtStarE` (`InterpreterSemanticsSpecProps.lean`) show these are
  sub-relations of the reference semantics, so a completeness statement about them
  is a statement about genuine reference derivations.
* `EngineChecksAgree R` — the engine's value checks read as a side condition on the
  *language*: every deterministic base-command evaluation the reference admits also
  passes them.  Under it, a choice-free reference derivation is a `StepEngE` derivation
  (`StepDetE.toStepEngE`, `InterpreterSemanticsSpecProps.lean`).
* `EngineChecksAgreeAt R c` / `EngineChecksAgreeFrom R c` — the same
  side condition localized to the base command in active position of `c` (`CmdFocus`),
  respectively to those of every configuration reachable from `c` by choice-free
  reference steps.  `EngineChecksAgreeFrom` is the form the bridge lemmas are proved
  against, and `EngineChecksAgree.toFrom` derives it from the global form.
* `EngineAgreesFrom R EvalCmd EvalCmdEng c` — every reference step from a configuration
  reachable from `c` is an engine-realizable step, over any command type; under it a reference
  derivation is an engine-realizable one (`StepStmtStarE.toStepEngParamStarE`).
* `Config.storeFree` — the fragment with no `.init` and no `.set` anywhere in the
  remaining program text, on which `engineChecksAgreeFrom_of_storeFree` discharges
  the localized obligation outright.
* `ValidChoices R` — every value `R` prescribes is one a `choose` may return, i.e.
  the converse constraint that `InterpObs.choose_sound` imposes on any resolvable
  choice record.

## Where the contract is discharged

`RunInterpSound` is proved monad-generically in `InterpreterSoundGeneric.lean`;
`RunInterpComplete` is proved for `ReplayM` in `InterpreterCompleteObs.lean`.
`RunInterpSound` takes the command type, the engine's command stepper and the reference
command relation as parameters, so it covers both the base-command language (`Cmd P`,
`baseStepCmd`, `EvalCmdE`) and Core's `.call`-aware engine (`Core.Command`,
`Core.replayStepCmd π`, `Core.EvalCommandE π`);
`RunInterpComplete` is scoped to the base-command language. A monad instance
connects to the semantics by exhibiting an `InterpObs P m` and proving
`RunInterpSound`/`RunInterpComplete` for it; from `RunInterpSound`, `ReplayM`'s
`.genuine` verdict (target event in the finished trace) entails a real reference
execution reaching the failing assert, and `RunInterpComplete` is the converse. -/

namespace Imperative

public section

universe u

/-! ## Configurations the driver can return -/

/-- The configurations `runInterp` stops at, hence the only ones an engine run can
return.  A derivation whose final configuration is not `Done` is not reproducible
by a run. -/
@[expose] def Config.Done {P : PureExpr} {CmdT : Type} (c : Config P CmdT) : Prop :=
  (∃ e, c = .terminal e) ∨ (∃ l e, c = .exiting l e)

/-! ## The engine-realizable command relation -/

section EngRel

variable (P : PureExpr) [HasBool P] [HasFvar P] [DecidableEq P.Ident] [InterpLang P]

/-- A **choice record**: which semantic value a nondeterministic choice of type `ty` at
factory `f` and store `σ` resolves to.  A derivation's nondeterministic rules are
annotated with it, so that what the monad's `choose` must return can be stated
relative to the derivation. -/
@[expose] def ChoiceRecord (P : PureExpr.{u}) : Type u :=
  P.Factory → SemanticStore P → P.Ty → P.Val → Prop

/-- Every engine evaluation of `e`, at any fuel, from a runtime store denoting `σ` under `f`, that
commits a runtime value `r` satisfies `ok σr r`.  The engine's executable checks act on runtime
values, which a semantic derivation does not name, so the engine-realizable relations state them
of every runtime value the engine can commit. -/
@[expose] def EngEvalOK (f : P.Factory) (σ : SemanticStore P) (e : P.Expr)
    (ok : RStore P → P.Expr → Prop) : Prop :=
  ∀ (σr : RStore P) (n : Nat) (r : P.Expr), StoreDenotes f σr σ →
    InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σr e = some r → ok σr r

/-- The engine reaches the reference value of `e`: on every runtime store denoting `σ` under `f`,
if `P.eval f σ e` is `v`, then the bounded evaluator commits, at some fuel, a runtime value that
denotes `v`.  It is the per-evaluation form of `BoundedEvalComplete`, carried by the
engine-realizable rules that evaluate an expression. -/
@[expose] def EngEvalReach (f : P.Factory) (σ : SemanticStore P) (e : P.Expr) : Prop :=
  ∀ (σr : RStore P) (v : P.Val), StoreDenotes f σr σ → P.eval f σ e = some v →
    ∃ n r, InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σr e = some r ∧
      InterpLang.Denotes f r v

/-- An evaluation of `e` the engine performs: the engine reaches the reference value
(`EngEvalReach`) and every runtime value it can commit satisfies the executable check `ok`
(`EngEvalOK`). -/
@[expose] def EngEval (f : P.Factory) (σ : SemanticStore P) (e : P.Expr)
    (ok : RStore P → P.Expr → Prop) : Prop :=
  EngEvalReach P f σ e ∧ EngEvalOK P f σ e ok

/-- **Engine guard agreement.**  Every runtime value the engine can commit for an expression whose
reference value is `ttVal f` (respectively `ffVal f`) is the literal `HasBool.tt` (`HasBool.ff`) up
to metadata (`InterpLang.boolLit?`), the runtime guard values the engine's branch selection takes
to the then-branch (else-branch).  It is the guard
counterpart of `EngineChecksAgree`: under it a choice-free reference derivation's guard steps are
engine-realizable.  The engine tests guards against runtime literals, and nothing else relates
those literals to the semantic guard value; this hypothesis supplies the relation. -/
@[expose] def EngineGuardsAgree [HasBool P] : Prop :=
  ∀ (f : P.Factory) (σ : SemanticStore P) (e : P.Expr),
    (P.eval f σ e = some (HasBool.ttVal f) →
      EngEvalOK P f σ e (fun _ r => InterpLang.boolLit? r = some true)) ∧
    (P.eval f σ e = some (HasBool.ffVal f) →
      EngEvalOK P f σ e (fun _ r => InterpLang.boolLit? r = some false))

/-- The **engine-realizable** refinement of the reference command relation
`EvalCmdE`: the same rules, with the engine's executable value checks added to
the deterministic `.init`/`.set` rules (the engine reaches the value and every runtime value it
can commit passes the checks, `EngEval`), the resulting store written as the engine's point
update, and the nondeterministic `.init` value drawn from the choice record `R`.  The nondeterministic `.set` value is likewise
drawn from `R`, at the type `InterpLang.typeOf` reads off the variable's current runtime value,
and every runtime value denoting it must pass the same `isValue`/`sameType` checks as a
deterministic `.set`. -/
inductive EvalCmdEngE (R : ChoiceRecord P) :
    P.Factory → SemanticStore P → Cmd P → SemanticStore P → Trace P → Prop where
  /-- Deterministic initializer, with the engine's value and type checks. -/
  | eval_init :
    σ x = none →
    P.eval f σ e = .some v →
    EngEval P f σ e (fun _ r =>
      (InterpLang.ops (P := P)).isValue (InterpLang.rfactory f) r = true ∧
      (InterpLang.ops (P := P)).hasType (InterpLang.rfactory f) r ty = true) →
    HasVal.valueOfTy f v ty →
    WellFormedSemanticEvalVar (P := P) f →
    EvalCmdEngE R f σ (.init x ty (.det e) md) (SemanticStore.update σ x v) []
  /-- Nondeterministic initializer, its value resolved by the choice record. -/
  | eval_init_nondet :
    σ x = none →
    R f σ ty v →
    HasVal.valueOfTy f v ty →
    WellFormedSemanticEvalVar (P := P) f →
    EvalCmdEngE R f σ (.init x ty .nondet md) (SemanticStore.update σ x v) []
  /-- Deterministic assignment, with the engine's value and same-type checks. -/
  | eval_set :
    σ x = .some old →
    P.eval f σ e = .some v →
    EngEval P f σ e (fun σr r => ∀ ro, σr x = some ro →
      (InterpLang.ops (P := P)).isValue (InterpLang.rfactory f) r = true ∧
      (InterpLang.ops (P := P)).sameType (InterpLang.rfactory f) ro r = true) →
    HasVal.valueOfStoredTy (P := P) f σ x v →
    WellFormedSemanticEvalVar (P := P) f →
    EvalCmdEngE R f σ (.set x (.det e) md) (SemanticStore.update σ x v) []
  /-- Nondeterministic assignment: the value is resolved by the choice record at
      the type of the current value, with the deterministic `.set`'s checks. -/
  | eval_set_nondet :
    σ x = .some old →
    (∀ (σr : RStore P) (ro : P.Expr), StoreDenotes f σr σ → σr x = some ro →
      InterpLang.typeOf (P := P) (InterpLang.rfactory f) ro = .some ty) →
    R f σ ty v →
    HasVal.valueOfStoredTy (P := P) f σ x v →
    (∀ (σr : RStore P) (ro r : P.Expr), StoreDenotes f σr σ → σr x = some ro →
      InterpLang.Denotes f r v →
      (InterpLang.ops (P := P)).isValue (InterpLang.rfactory f) r = true ∧
      (InterpLang.ops (P := P)).sameType (InterpLang.rfactory f) ro r = true) →
    WellFormedSemanticEvalVar (P := P) f →
    EvalCmdEngE R f σ (.set x .nondet md) (SemanticStore.update σ x v) []
  /-- Emit the captured assertion condition. -/
  | eval_assert :
    EvalCmdEngE R f σ (.assert label e md) σ
      [.assert { factory := f, store := σ, label := label, expr := e, metadata := md }]
  /-- Emit the captured assumption condition. -/
  | eval_assume :
    EvalCmdEngE R f σ (.assume label e md) σ
      [.assume { factory := f, store := σ, label := label, expr := e, metadata := md }]
  /-- Emit the captured coverage condition. -/
  | eval_cover :
    EvalCmdEngE R f σ (.cover label e md) σ
      [.cover { factory := f, store := σ, label := label, expr := e, metadata := md }]

end EngRel

/-- The choice record of typed choices: a nondeterministic choice of type `ty` may resolve to any
semantic value of type `ty`. -/
@[expose] def ChoiceRecord.typed (P : PureExpr) [HasVal P] : ChoiceRecord P :=
  fun f _ ty v => HasVal.valueOfTy f v ty

/-! ## The engine-realizable statement relation -/

section StepEng

variable (P : PureExpr) [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

open Classical in
/-- The **engine-realizable** statement step relation: the choice-free rules of
`StepDetE`, with the base-command rule delegated to `EvalCmd` (which already
carries the engine's own conditions), the deterministic guard rules with the engine's literal
test (the engine reaches the guard's value, and every runtime guard value it can commit is
`HasBool.tt`, respectively `HasBool.ff`: `EngEval`),
plus the two nondeterministic guard rules,
each recording the guard value it resolved in the choice record `R`.  That value
must be `HasBool.ttVal` or `HasBool.ffVal`, and the `if … then … else …` in those two
rules is the engine's own branch selection (`ttVal` takes the then-branch or enters
the loop, `ffVal` the else-branch or exits it). -/
inductive StepEngParamE {CmdT : Type} (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) :
    Config P CmdT → List (Event P) → Config P CmdT → Prop where
  /-- Execute one base command through the engine-realizable command relation. -/
  | step_cmd :
      EvalCmd ρ.factory ρ.store cmd σ' emitted →
      StepEngParamE R EvalCmd
        (.stmt (.cmd cmd) ρ) emitted (.terminal { ρ with store := σ' })
  /-- Enter a labeled block. -/
  | step_block :
      StepEngParamE R EvalCmd
        (.stmt (.block label ss md) ρ) []
        (.block (.some label) ρ.store (.stmts ss ρ))
  /-- Take the then-branch of an `ite` whose guard evaluates to true. -/
  | step_ite_true :
      P.eval ρ.factory ρ.store c = .some (HasBool.ttVal ρ.factory) →
      EngEval P ρ.factory ρ.store c (fun _ r => InterpLang.boolLit? r = some true) →
      StepEngParamE R EvalCmd
        (.stmt (.ite (.det c) tss ess md) ρ) []
        (.block .none ρ.store (.stmts tss ρ))
  /-- Take the else-branch of an `ite` whose guard evaluates to false. -/
  | step_ite_false :
      P.eval ρ.factory ρ.store c = .some (HasBool.ffVal ρ.factory) →
      EngEval P ρ.factory ρ.store c (fun _ r => InterpLang.boolLit? r = some false) →
      StepEngParamE R EvalCmd
        (.stmt (.ite (.det c) tss ess md) ρ) []
        (.block .none ρ.store (.stmts ess ρ))
  /-- Resolve a nondeterministic `ite` guard through the choice record to `ttVal` (then-branch)
      or `ffVal` (else-branch). -/
  | step_ite_nondet :
      R ρ.factory ρ.store (HasBool.boolTy (P := P)) v →
      (v = HasBool.ttVal ρ.factory ∨ v = HasBool.ffVal ρ.factory) →
      StepEngParamE R EvalCmd
        (.stmt (.ite .nondet tss ess md) ρ) []
        (.block .none ρ.store
          (.stmts (if v = HasBool.ttVal ρ.factory then tss else ess) ρ))
  /-- Enter a loop body whose guard evaluates to true. -/
  | step_loop_enter :
      P.eval ρ.factory ρ.store g = .some (HasBool.ttVal ρ.factory) →
      EngEval P ρ.factory ρ.store g (fun _ r => InterpLang.boolLit? r = some true) →
      StepEngParamE R EvalCmd
        (.stmt (.loop (.det g) m inv body md) ρ) []
        (.seq (.block .none ρ.store (.stmts body ρ))
          [.loop (.det g) m inv body md])
  /-- Exit a loop whose guard evaluates to false. -/
  | step_loop_exit :
      P.eval ρ.factory ρ.store g = .some (HasBool.ffVal ρ.factory) →
      EngEval P ρ.factory ρ.store g (fun _ r => InterpLang.boolLit? r = some false) →
      StepEngParamE R EvalCmd
        (.stmt (.loop (.det g) m inv body md) ρ) [] (.terminal ρ)
  /-- Resolve a nondeterministic `loop` guard through the choice record to `ttVal` (enter the
      body) or `ffVal` (exit). -/
  | step_loop_nondet :
      R ρ.factory ρ.store (HasBool.boolTy (P := P)) v →
      (v = HasBool.ttVal ρ.factory ∨ v = HasBool.ffVal ρ.factory) →
      StepEngParamE R EvalCmd
        (.stmt (.loop .nondet m inv body md) ρ) []
        (if v = HasBool.ttVal ρ.factory then
            .seq (.block .none ρ.store (.stmts body ρ))
              [.loop .nondet m inv body md]
          else .terminal ρ)
  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
      StepEngParamE R EvalCmd (.stmt (.exit label md) ρ) [] (.exiting label ρ)
  /-- A type declaration is a runtime no-op. -/
  | step_typeDecl :
      StepEngParamE R EvalCmd (.stmt (.typeDecl tc md) ρ) [] (.terminal ρ)
  /-- The empty statement list is terminal. -/
  | step_stmts_nil :
      StepEngParamE R EvalCmd (.stmts [] ρ) [] (.terminal ρ)
  /-- Enter a sequence context on a non-empty statement list. -/
  | step_stmts_cons :
      StepEngParamE R EvalCmd (.stmts (s :: ss) ρ) [] (.seq (.stmt s ρ) ss)
  /-- Lift one inner sequence step. -/
  | step_seq_inner :
      StepEngParamE R EvalCmd inner emitted inner' →
      StepEngParamE R EvalCmd (.seq inner ss) emitted (.seq inner' ss)
  /-- Continue with the pending statements once the sequence head terminates. -/
  | step_seq_done :
      StepEngParamE R EvalCmd (.seq (.terminal ρ') ss) [] (.stmts ss ρ')
  /-- Propagate an exit out of a sequence, skipping the pending statements. -/
  | step_seq_exit :
      StepEngParamE R EvalCmd (.seq (.exiting label ρ') ss) [] (.exiting label ρ')
  /-- Lift one inner block step. -/
  | step_block_body :
      StepEngParamE R EvalCmd inner emitted inner' →
      StepEngParamE R EvalCmd
        (.block label σ_parent inner) emitted
        (.block label σ_parent inner')
  /-- Leave a block whose body terminated, projecting store and factory. -/
  | step_block_done :
      StepEngParamE R EvalCmd
        (.block label σ_parent (.terminal ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })
  /-- A block consumes an exit carrying its own label. -/
  | step_block_exit_match :
      label = .some l →
      StepEngParamE R EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })
  /-- A block propagates an exit carrying a different label. -/
  | step_block_exit_mismatch :
      label ≠ .some l →
      StepEngParamE R EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.exiting l { ρ' with store := projectStore σ_parent ρ'.store })

/-- The **engine-realizable** statement step relation for base commands:
`StepEngParamE` with the command relation `EvalCmdEngE R`. -/
abbrev StepEngE (R : ChoiceRecord P) :
    Config P (Cmd P) → List (Event P) → Config P (Cmd P) → Prop :=
  StepEngParamE P R (EvalCmdEngE P R)

/-- Traced reflexive-transitive closure of `StepEngParamE`. -/
abbrev StepEngParamStarE {CmdT : Type} (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P)) :
    Config P CmdT → List (Event P) → Config P CmdT → Prop :=
  ReflTransTrace (StepEngParamE P R EvalCmd)

/-- Traced reflexive-transitive closure of `StepEngE`. -/
abbrev StepEngStarE (R : ChoiceRecord P) :
    Config P (Cmd P) → List (Event P) → Config P (Cmd P) → Prop :=
  ReflTransTrace (StepEngE P R)

end StepEng

/-! ## The two side conditions on a choice record -/

section ChoiceSide

variable {P : PureExpr} [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
  [DecidableEq P.Ident] [InterpLang P]

/-- **Engine-check agreement.**  Every deterministic base-command evaluation the
reference semantics admits also passes the engine's executable value checks.  This
is the residual well-typedness obligation of completeness against the bare
reference relation: it fails exactly when the program declares an `.init`/`.set`
whose right-hand side evaluates to a value of the wrong type. -/
@[expose] def EngineChecksAgree (R : ChoiceRecord P) : Prop :=
  ∀ (f : P.Factory) (σ σ' : SemanticStore P) (cmd : Cmd P) (evs : Trace P),
    EvalCmdE (P := P) f σ cmd σ' evs → CmdDeterministic cmd = true →
    EvalCmdEngE P R f σ cmd σ' evs

/-! ### The sharpened, derivation-relative form

`CmdFocus` names the base-command evaluation a configuration is about to perform;
`EngineChecksAgreeAt` asks for the engine checks only there; `EngineChecksAgreeFrom` asks for
them along the reference derivations from a start configuration. -/

/-- `CmdFocus c ρ cmd`: the configuration `c` has the base command `cmd` in
*active position* under environment `ρ` — that is, if `c`'s next step is a
base-command step, that step evaluates `cmd` at `ρ.factory`/`ρ.store`.  The
active position is reached by descending through the enclosing `.seq` and
`.block` frames, which is exactly how `StepDetE.step_seq_inner` and
`StepDetE.step_block_body` nest a base-command step.  A configuration with no
base command in active position (`.stmts`, `.terminal`, `.exiting`, or a `.stmt`
holding anything other than a `.cmd`) has no focus at all. -/
inductive CmdFocus {P : PureExpr} : Config P (Cmd P) → Env P → Cmd P → Prop where
  /-- The active statement is the base command itself. -/
  | here {cmd : Cmd P} {ρ : Env P} : CmdFocus (.stmt (.cmd cmd) ρ) ρ cmd
  /-- Descend into the head of a sequence. -/
  | seq {inner : Config P (Cmd P)} {ss : List (Stmt P (Cmd P))} {ρ : Env P} {cmd : Cmd P} :
      CmdFocus inner ρ cmd → CmdFocus (.seq inner ss) ρ cmd
  /-- Descend into the body of a block. -/
  | block {inner : Config P (Cmd P)} {label : Option String}
      {σ_parent : SemanticStore P} {ρ : Env P} {cmd : Cmd P} :
      CmdFocus inner ρ cmd → CmdFocus (.block label σ_parent inner) ρ cmd

/-- **Engine-check agreement at one configuration.**  `EngineChecksAgree`
restricted to the single base-command evaluation `c` is about to perform: for the
command in `c`'s active position, at the factory and store `c`'s own environment
carries there, every deterministic reference evaluation also passes the engine's
executable value checks.  Nothing is asked at any other store or command. -/
@[expose] def EngineChecksAgreeAt (R : ChoiceRecord P) (c : Config P (Cmd P)) : Prop :=
  ∀ (ρ : Env P) (cmd : Cmd P) (σ' : SemanticStore P) (evs : Trace P),
    CmdFocus (P := P) c ρ cmd →
    EvalCmdE (P := P) ρ.factory ρ.store cmd σ' evs → CmdDeterministic cmd = true →
    EvalCmdEngE P R ρ.factory ρ.store cmd σ' evs

/-- **Engine-check agreement along the derivations out of `c`.**  The
derivation-relative form of `EngineChecksAgree`: agreement at every configuration the
reference semantics can reach from `c` by choice-free steps.  Because the
reachable configurations carry only the stores an execution from `c` actually
builds, and only the commands `c`'s program text contains, it asks only for the
checks an execution from `c` actually performs.  The global form implies it at every
`c`, so it is never a stronger demand. -/
@[expose] def EngineChecksAgreeFrom (R : ChoiceRecord P)
    (c : Config P (Cmd P)) : Prop :=
  ∀ (evs : List (Event P)) (mid : Config P (Cmd P)),
    StepDetStarE P (@EvalCmdE P _ _) c evs mid → EngineChecksAgreeAt R mid

/-- **Engine/semantics agreement along the reference derivations out of `c`**, for a reference
command relation `EvalCmd` and an engine-realizable command relation `EvalCmdEng`: every reference
step from a configuration that a reference derivation reaches from `c` is an engine-realizable step
under the choice record `R`, with the same events and successor.  The step-level counterpart of
`EngineChecksAgreeFrom`, over any command type. -/
@[expose] def EngineAgreesFrom {CmdT : Type} (R : ChoiceRecord P)
    (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (EvalCmdEng : EvalCmdParamE P CmdT (Event P))
    (c : Config P CmdT) : Prop :=
  ∀ (evs : List (Event P)) (mid : Config P CmdT) (evs' : List (Event P)) (mid' : Config P CmdT),
    StepStmtStarE P EvalCmd c evs mid → StepStmtE P EvalCmd mid evs' mid' →
    StepEngParamE P R EvalCmdEng mid evs' mid'

/-! ### A fragment on which the sharpened obligation is *discharged*

A configuration with no `.init` and no `.set` (`Config.storeFree`) performs none of the
engine's value checks, so `EngineChecksAgreeFrom` holds on it with no hypothesis on the
language, factory or store. -/

/-- A base command needs none of the engine's value checks: it is one of the
store-neutral event emitters, not an `.init` or a `.set`. -/
@[expose] def CmdStoreFree : Cmd P → Bool
  | .init _ _ _ _ => false
  | .set _ _ _ => false
  | .assert _ _ _ => true
  | .assume _ _ _ => true
  | .cover _ _ _ => true

mutual
/-- No `.init` and no `.set` occurs anywhere inside the statement `s`. -/
@[expose] def StmtStoreFree {P : PureExpr} (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd c => CmdStoreFree c
  | .block _ b _ => StmtsStoreFree b
  | .ite _ t e _ => StmtsStoreFree t && StmtsStoreFree e
  | .loop _ _ _ body _ => StmtsStoreFree body
  | .exit _ _ => true
  | .typeDecl _ _ => true

/-- `StmtStoreFree` for every statement of a list. -/
@[expose] def StmtsStoreFree {P : PureExpr} (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest => StmtStoreFree s && StmtsStoreFree rest
end

/-- `StmtStoreFree` lifted to a configuration, exactly as `Config.deterministic`
lifts `StmtDeterministic`: every statement still to be executed — in the active
position, in the pending tail of every enclosing `.seq`, and inside every
enclosing `.block` — contains no `.init` and no `.set`. -/
@[expose] def Config.storeFree : Config P (Cmd P) → Bool
  | .stmt s _ => StmtStoreFree s
  | .stmts ss _ => StmtsStoreFree ss
  | .terminal _ => true
  | .exiting _ _ => true
  | .block _ _ inner => Config.storeFree inner
  | .seq inner ss => Config.storeFree inner && StmtsStoreFree ss

/-- **The choices an observation can resolve.**  Every value the choice record `R`
prescribes is the denotation of a runtime value that passes the engine's executable value and
type checks; a Boolean choice (a guard) is the denotation of a runtime value that is the literal
`HasBool.tt` or `HasBool.ff` up to metadata (`InterpLang.boolLit?`).  These are the only runtime
values `InterpObs.choose_sound` lets a `choose` return, so a record a run follows can prescribe
nothing else. -/
@[expose] def ValidChoices (R : ChoiceRecord P) : Prop :=
  ∀ (f : P.Factory) (σ : SemanticStore P) (ty : P.Ty) (v : P.Val),
    R f σ ty v →
      ∃ r, InterpLang.Denotes f r v
        ∧ (InterpLang.ops (P := P)).isValue (InterpLang.rfactory f) r = true
        ∧ (InterpLang.ops (P := P)).hasType (InterpLang.rfactory f) r ty = true
        ∧ (v = HasBool.ttVal f → InterpLang.boolLit? r = some true)
        ∧ (v = HasBool.ffVal f → InterpLang.boolLit? r = some false)

end ChoiceSide

/-! ## The hypotheses on the language's evaluator

`BoundedEvalSoundAt P F` is the premise of soundness for a run under the factory `F`: a runtime
value the bounded evaluator commits denotes the unbounded `P.eval` value (`BoundedEvalSound` is
its statement at every factory).  `BoundedEvalComplete` and `BoundedEvalMono` turn a
reference `P.eval` premise into an engine-side `boundedEval` premise at every sufficiently large
fuel.  `BoundedEvalMono` is a hypothesis of completeness; `BoundedEvalComplete` is needed only to
turn a bare reference derivation into an engine-realizable one (`BoundedEvalComplete.reach`). -/

/-- The language's evaluator is sound up to denotation: on a runtime store denoting `σ`, a value
the bounded evaluator commits denotes the value of `P.eval` on `σ`. -/
@[expose] def BoundedEvalSound (P : PureExpr) [InterpLang P] : Prop :=
  ∀ (n : Nat) (f : P.Factory) (σr : RStore P) (σ : SemanticStore P) (e r : P.Expr),
    StoreDenotes f σr σ → InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σr e = some r →
      ∃ v, P.eval f σ e = some v ∧ InterpLang.Denotes f r v

/-- `BoundedEvalSound` at one factory `f`: on a runtime store denoting a semantic store under
`f`, every value the language's bounded evaluator commits to at the runtime factory of `f`
denotes the value `P.eval f` gives. -/
@[expose] def BoundedEvalSoundAt (P : PureExpr) [InterpLang P] (f : P.Factory) : Prop :=
  ∀ (n : Nat) (σr : RStore P) (σ : SemanticStore P) (e r : P.Expr),
    StoreDenotes f σr σ → InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σr e = some r →
      ∃ v, P.eval f σ e = some v ∧ InterpLang.Denotes f r v

/-- The language's evaluator reaches every unbounded `P.eval` value at some fuel, up to
denotation — the converse of `BoundedEvalSound`. -/
@[expose] def BoundedEvalComplete (P : PureExpr) [InterpLang P] : Prop :=
  ∀ (f : P.Factory) (σr : RStore P) (σ : SemanticStore P) (e : P.Expr) (v : P.Val),
    StoreDenotes f σr σ → P.eval f σ e = some v →
      ∃ n r, InterpLang.boundedEval (P := P) n (InterpLang.rfactory f) σr e = some r ∧
        InterpLang.Denotes f r v

/-- The runtime value checks are complete for the typed write-back of a call (`CallExit`): a
runtime value `r` denoting a value of the type of the value a variable's runtime value `old` denotes
passes the engine's write-back check (`isValue` and `sameType` against `old`). -/
@[expose] def WriteBackTypedComplete (P : PureExpr) [HasVal P] [InterpLang P] : Prop :=
  ∀ (F : P.Factory) (old r : P.Expr) (vo v : P.Val) (ty : P.Ty),
    InterpLang.Denotes F old vo → InterpLang.Denotes F r v →
    HasVal.valueOfTy F vo ty → HasVal.valueOfTy F v ty →
    (InterpLang.ops (P := P)).isValue (InterpLang.rfactory F) r = true ∧
    (InterpLang.ops (P := P)).sameType (InterpLang.rfactory F) old r = true

/-- The language's evaluator is upward fuel-monotone: a value reached at some fuel is
reached at every larger fuel. -/
@[expose] def BoundedEvalMono (P : PureExpr) [InterpLang P] : Prop :=
  ∀ (a b : Nat) (f : InterpLang.RFactory P) (σ : RStore P) (e v : P.Expr),
    a ≤ b → InterpLang.boundedEval (P := P) a f σ e = some v →
      InterpLang.boundedEval (P := P) b f σ e = some v

variable {P : PureExpr}

/-- How to observe a run of the monadic interpreter in the monad `m`: project a computation to
    its `(outcome, state)` pair under a reader config (`run`), read the emitted runtime
    event trace out of the state (`trace`), plus the algebraic laws relating them.
    An instance is the per-monad data over which the generic soundness and
    completeness contracts (`RunInterpSound`, `RunInterpComplete`) are stated. -/
structure InterpObs (P : PureExpr) [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    (m : Type → Type) [Monad m] [InterpEffects P m] [MonadExcept StopReason m] where
  /-- The reader config a run is parameterized by (`Unit` when there is none). -/
  Cfg : Type
  /-- The threaded monad state. -/
  St : Type
  /-- Run a computation to its outcome-and-state pair, under a config and start state. -/
  run : {α : Type} → m α → Cfg → St → (Except StopReason α × St)
  /-- Read the emitted runtime-event trace (most-recent-first) out of a state. -/
  trace : St → List (IEvent P)
  /-- `pure x` runs to `x` with the state untouched. -/
  run_pure : ∀ {α : Type} (x : α) (cfg : Cfg) (st : St),
    run (pure x : m α) cfg st = (.ok x, st)
  /-- `throw e` runs to the error with the state frozen. -/
  run_throw : ∀ {α : Type} (e : StopReason) (cfg : Cfg) (st : St),
    run (throw e : m α) cfg st = (.error e, st)
  /-- `run` threads the state through a bind, short-circuiting on error. -/
  run_bind : ∀ {α β : Type} (ma : m α) (f : α → m β) (cfg : Cfg) (st : St),
    run (ma >>= f) cfg st
      = (match run ma cfg st with
         | (.ok a, st') => run (f a) cfg st'
         | (.error e, st') => (.error e, st'))
  /-- A **successful** `emit ev` prepends `ev` to the trace; an instance's `emit` may
      throw instead of recording the event. -/
  emit_trace : ∀ (ev : IEvent P) (cfg : Cfg) (st st' : St) (u : Unit),
    run (InterpEffects.emit (P := P) ev) cfg st = (.ok u, st') → trace st' = ev :: trace st
  /-- Whatever `choose` resolves to is a valid nondeterministic runtime value, and `choose`
      emits no event. -/
  choose_sound : ∀ (factory : InterpLang.RFactory P) (store : RStore P) (ty : P.Ty)
    (cfg : Cfg) (st : St) (v : P.Expr) (st' : St),
    run (InterpEffects.choose (P := P) factory store ty) cfg st = (.ok v, st') →
      ((InterpLang.ops (P := P)).isValue factory v = true
        ∧ (InterpLang.ops (P := P)).hasType factory v ty = true)
      ∧ trace st' = trace st
  /-- `branch` (a deterministic guard that evaluated to neither `tt` nor `ff`) is stuck, with
      the state frozen: the reference semantics has no step there. -/
  branch_stuck : ∀ (factory : InterpLang.RFactory P) (store : RStore P) (v : P.Expr)
    (cfg : Cfg) (st : St),
    run (InterpEffects.branch (P := P) factory store v) cfg st
      = (.error .expressionWasNotBoolean, st)

/-- The trace of the state `st'` extends that of `st` by runtime events denoting exactly `evs`
    under `F` (most recent first, as `InterpObs.trace` reads it). -/
@[expose] def InterpObs.TraceExt {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
    (obs : InterpObs P m) (F : P.Factory) (st st' : obs.St) (evs : List (Event P)) : Prop :=
  ∃ revs : List (IEvent P), revs.map (REvent.abs F) = evs ∧
    obs.trace st' = revs.reverse ++ obs.trace st

namespace C1
attribute [scoped simp] InterpObs.run_pure InterpObs.run_throw InterpObs.run_bind
  InterpObs.branch_stuck
attribute [scoped grind =] InterpObs.run_pure InterpObs.run_throw InterpObs.run_bind
  InterpObs.branch_stuck
attribute [scoped grind →] InterpObs.emit_trace InterpObs.choose_sound
end C1

/-- **Monad-generic soundness.**  For any observation `obs : InterpObs P m` and factory `F`: if
    the bounded evaluator is sound up to denotation at `F` (`BoundedEvalSoundAt`), then a run of
    the engine over the command stepper `stepCmd` from an interpreter configuration `istart` that
    denotes a semantic configuration `start` under `F` (`IConfig.Denotes`), where `start`
    satisfies the invariant `Inv` and `F` is well-formed (`FactoryWF`), that reaches `final`, is a reference
    `StepStmtStarE` execution over `EvalCmd` from `start` to a configuration `final` denotes,
    carrying the denotations (`REvent.abs F`) of exactly the runtime events it emitted.

    The command type `CmdT`, the engine's command stepper `stepCmd` and the
    reference command relation `EvalCmd` are parameters, because the driver argument
    never inspects a command, so one proof covers every command language.

    The configuration invariant `Inv` the run carries is a parameter as well.  The
    base-command instance passes `Config.storeTyped`.  A procedure call reads the callee's
    output formals out of the callee's final store, and the reference semantics
    demands each value read be a value in the factory, so a language with calls
    passes an invariant that also carries `Config.storeWellDefined`. -/
def RunInterpSound (P : PureExpr) [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]
    [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] (m : Type → Type) [Monad m]
    [InterpEffects P m]
    [MonadExcept StopReason m] (obs : InterpObs P m) {CmdT : Type} [CmdDefs P CmdT]
    (stepCmd : StepCmdM P CmdT m) (EvalCmd : EvalCmdParamE P CmdT (Event P))
    (Inv : Config P CmdT → Prop) : Prop :=
  ∀ (fuel : Nat) (F : P.Factory) (start : Config P CmdT) (istart final : IConfig P CmdT)
    (cfg : obs.Cfg) (st st' : obs.St),
    istart.Denotes F start →
    obs.run (runInterp stepCmd fuel istart) cfg st = (.ok final, st') →
    FactoryWF (P := P) F → BoundedEvalSoundAt P F → Inv start →
    ∃ (evs : List (Event P)) (revs : List (IEvent P)) (final' : Config P CmdT),
      StepStmtStarE (P := P) EvalCmd start evs final' ∧ final.Denotes F final' ∧
      obs.trace st' = revs.reverse ++ obs.trace st ∧ revs.map (REvent.abs F) = evs

/-- **Monad-generic completeness.**  The converse of `RunInterpSound`: a derivation
    of the reference semantics is *reproduced* by an engine run — there exist a
    start state (the oracle a nondeterministic derivation needs), a reader config, a
    fuel and an end state at which the engine, run from any interpreter configuration `istart`
    denoting `start` under `F`, reaches a configuration denoting `final`, having emitted runtime
    events denoting exactly the derivation's events.

    Four things about this statement are deliberate, and each departs from the
    naive converse of `RunInterpSound`:

    1. **The start state is existential, not universal.**  A nondeterministic
       derivation is reproduced only if the engine's `choose` follows its choices,
       and for `ReplayM` the oracle that decides `choose` lives in the threaded
       *state* (`ReplayState.remaining`), not in the reader config — so no `∃ cfg`
       over a universally quantified start state can supply it.  Existentially
       quantifying the start state is what lets the oracle be constructed from the
       derivation; its runtime values are the runtime values `ValidChoices` provides.
    2. **The start state is required to carry an empty trace** (`obs.trace st = []`),
       and the conclusion then reads `obs.trace st' = revs.reverse` absolutely rather
       than relative to `obs.trace st`.
    3. **`Config.Done final` is required.**  A reference derivation may stop
       anywhere, whereas `runInterp` returns only a `.terminal`/`.exiting` configuration.
    4. **The derivation is given in the engine-realizable form
       `StepEngStarE P R`**, with `EngineChecksAgree R` and `ValidChoices R` as
       explicit premises.

    The engine-realizable rules carry, for each expression they evaluate, that the bounded
    evaluator reaches a value denoting the reference value at some fuel (`EngEval`); the
    language-evaluator hypothesis `BoundedEvalMono` (then every larger fuel does) is the
    completeness side's own hypothesis. -/
def RunInterpComplete (P : PureExpr) [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr]
    [DecidableEq P.Ident] [InterpLang P] (m : Type → Type) [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (obs : InterpObs P m) : Prop :=
  BoundedEvalMono P →
  ∀ (F : P.Factory) (R : ChoiceRecord P) (start final : Config P (Cmd P)) (evs : List (Event P))
    (istart : IConfig P (Cmd P)),
    istart.Denotes F start →
    StepEngStarE P R start evs final →
    EngineChecksAgree (P := P) R →
    ValidChoices (P := P) R →
    Config.Done final →
    ∃ (fuel : Nat) (cfg : obs.Cfg) (st st' : obs.St) (final' : IConfig P (Cmd P))
      (revs : List (IEvent P)),
      obs.trace st = [] ∧
      obs.run (runInterp (baseStepCmd (m := m)) fuel istart) cfg st
        = (.ok final', st') ∧ final'.Denotes F final ∧
      obs.trace st' = revs.reverse ∧ revs.map (REvent.abs F) = evs

end -- public section

end Imperative

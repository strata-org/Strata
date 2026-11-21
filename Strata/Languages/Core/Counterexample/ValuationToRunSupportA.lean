/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.ExceptProps
public import Strata.Languages.Core.Counterexample.ValuationToRunProducer
public import Strata.Languages.Core.Counterexample.Model
public import Strata.Languages.Core.Counterexample.ModelToValuation
public import Strata.Languages.Core.Counterexample.ValuationToRun
public import Strata.Languages.Core.FactoryWF
public import Strata.Languages.Core.ObligationExtraction
public import Strata.DL.Imperative.Counterexample.Run
public import Strata.DL.Imperative.Counterexample.BackLink
public import Strata.DL.Imperative.Counterexample.Valuation
public import Strata.DL.Imperative.EvalContextProps
import all Strata.Languages.Core.Counterexample.ValuationToRunProducer
import all Strata.Languages.Core.Counterexample.Model
import all Strata.Languages.Core.Counterexample.ModelToValuation
import all Strata.Languages.Core.Counterexample.ValuationToRun
import all Strata.Languages.Core.InterpreterEval
import all Strata.Languages.Core.Interpreter
import all Strata.Languages.Core.ObligationExtraction
import Strata.Languages.Core.ObligationExtractionProps
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.Valuation
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Imperative.Counterexample.Tactics
import all Strata.DL.Lambda.LExprEvalFuelProps
import Strata.Languages.Core.InterpreterDomainProps

/-! # Engine-independent support lemmas for the `(b)→(a)` replay, part 1

Facts, not mentioning the replay engine, used to replay a level-`(b)` counterexample on the
source program: the shape of the obligations and back-links `extractLinkedFromStatements` emits,
the environment and oracle `valuationToEnv` builds, evaluation transfer between agreeing stores,
and the bridge from the computable well-scopedness check to `WellScopedObl`.

Key theorems: `extractLinked_assumes_are_path_folded`, `extractGoLinked_events_branch_head`,
`valuationToEnv_oracle_eq`, `eval_transfer_on_defined`.

Key definitions: `RootPc` (root path condition of an extraction), `eventsToOracle` (closed form
of the oracle `valuationToEnv` builds), `store_agrees`, and the accumulator invariants
`LinkEntryOK`, `EventsPrefixOK`, `AssumesPrependOK`. -/


namespace Core

open _root_.Lambda Imperative
open ObligationExtraction

public section

/-- A root path condition for extraction: at most one scope, and no variable
    declaration (every entry is an assumption or a distinctness fact).  The empty path
    condition and the verifier's global scope of axioms and `distinct` declarations
    are root path conditions. -/
@[expose] def RootPc (pc0 : Imperative.RevPathConditions Expression) : Prop :=
  pc0.scopes.length ≤ 1 ∧ ∀ e ∈ pc0.consume.flatten, ∀ n ty v, e ≠ .varDecl n ty v

/-- Invariant: every linked pair in an accumulator has `link.entryStatements`
    equal to the fixed extraction `entry`. -/
def LinkEntryOK (entry : Statements)
    (acc : Array ObligationExtraction.LinkedObligation) : Prop :=
  ∀ (ob : ProofObligation Expression) (lnk : ObligationExtraction.ExtractBackLink),
    (ob, lnk) ∈ acc.toList → lnk.entryStatements = entry

/-- The empty accumulator satisfies `LinkEntryOK`. -/
theorem LinkEntryOK_empty (entry : Statements) : LinkEntryOK entry #[] := nofun

/-- `LinkEntryOK` is preserved by appending accumulators. -/
theorem LinkEntryOK_append {entry : Statements}
    {a b : Array ObligationExtraction.LinkedObligation}
    (ha : LinkEntryOK entry a) (hb : LinkEntryOK entry b) : LinkEntryOK entry (a ++ b) := by
  grind [LinkEntryOK]

/-- `LinkEntryOK` is preserved by pushing a pair whose link has entry statements `entry`. -/
theorem LinkEntryOK_push_some {entry : Statements}
    {a : Array ObligationExtraction.LinkedObligation}
    (ha : LinkEntryOK entry a) (ob : ProofObligation Expression)
    (lnk : ObligationExtraction.ExtractBackLink) (hent : lnk.entryStatements = entry) :
    LinkEntryOK entry (a.push (ob, lnk)) := by grind [LinkEntryOK]

/-- A successful `extractGoLinked` run from accumulator `acc` returns `acc` followed by the
    result of the same run from the empty accumulator. -/
theorem extractGoLinked_acc_append
    (entry : Statements) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements)
      (acc : Array ObligationExtraction.LinkedObligation)
      (arr : Array ObligationExtraction.LinkedObligation),
      ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr →
      ∃ fresh, ObligationExtraction.extractGoLinked entry pc events ss #[] = .ok fresh
             ∧ arr.toList = acc.toList ++ fresh.toList := by
  intro pc events ss acc arr hok
  rcases hfresh : extractGoLinked entry pc events ss #[] with _ | fresh <;>
    rw [extractGoLinked_acc, hfresh] at hok <;> cases hok
  exact ⟨fresh, rfl, Array.toList_append⟩

/-! ## The environment `valuationToEnv` builds -/

/-! ### Default values are canonical and well-typed -/

/-- Any value `defaultCanonicalValue` produces is canonical (`isValue`).
    Its results are literal constants (`.const _ _`), for which `isValue`
    is definitionally `true`. -/
theorem defaultCanonicalValue_isCanonical
    (factory : @Lambda.Factory CoreLParams) (ty : Lambda.LMonoTy) (v : Expression.Expr)
    (h : defaultCanonicalValue ty = some v) :
    Lambda.LExpr.isValue factory v = true := by
  unfold defaultCanonicalValue at h
  split at h <;> cases h <;> exact isValue_const_true ..

/-- Any value `defaultCanonicalValue ty` produces has mono-type `ty`
    (`valueHasMonoType`). -/
private theorem defaultCanonicalValue_hasMonoType
    (F : @Lambda.Factory CoreLParams) (ty : Lambda.LMonoTy) (v : Expression.Expr)
    (h : defaultCanonicalValue ty = some v) :
    valueHasMonoType F v ty = true := by
  unfold defaultCanonicalValue at h
  split at h <;> cases h <;> exact Bool.and_eq_true_iff.2
    ⟨by first | rfl | simp! [LExpr.typeCheckWith, LExpr.opsConsistent, LExpr.typeCheck],
      isGroundTy_iff.2 rfl⟩

/-- Any value `defaultValueIn F ty` produces is canonical in `F`: a primitive default
    is a literal, and a datatype default is kept only when canonical in `F`. -/
theorem defaultValueIn_isCanonical
    (F : @Lambda.Factory CoreLParams) (ty : Lambda.LMonoTy) (v : Expression.Expr)
    (h : defaultValueIn F ty = some v) :
    Lambda.LExpr.isValue F v = true := by
  unfold defaultValueIn at h
  split at h
  · exact Option.some.inj h ▸ defaultCanonicalValue_isCanonical F ty _ ‹_›
  · exact (Bool.and_eq_true_iff.1 (Option.filter_eq_some_iff.1 h).2).1

/-- Any value `defaultValueIn F ty` produces has mono-type `ty`. -/
theorem defaultValueIn_hasMonoType
    (F : @Lambda.Factory CoreLParams) (ty : Lambda.LMonoTy) (v : Expression.Expr)
    (h : defaultValueIn F ty = some v) :
    valueHasMonoType F v ty = true := by
  unfold defaultValueIn at h
  split at h
  · exact Option.some.inj h ▸ defaultCanonicalValue_hasMonoType F ty _ ‹_›
  · exact (Bool.and_eq_true_iff.1 (Option.filter_eq_some_iff.1 h).2).2

/-! ### The two `forIn` loops of `valuationToEnv` -/

/-- **Inputs-loop key preservation.**  The `valuationToEnv` inputs `forIn`, when it
    returns `.ok out`, produces an accumulator whose key list is `acc`'s keys
    followed by the input names. -/
private theorem inputs_forIn_keys
    (factory : @Lambda.Factory CoreLParams) (store : RStore Expression)
    (inputs : List (CoreIdent × Lambda.LMonoTy)) (acc : LExprModel) (out : LExprModel)
    (hok : (forIn (m := Except StopReason) inputs acc
      (fun x r =>
        match store x.fst with
        | some value =>
          if (!Lambda.LExpr.isValue factory value) = true then
            Except.error StopReason.expectedValueChoice
          else if (!valueHasMonoType factory value x.snd) = true then
            Except.error StopReason.illTypedValue
          else Except.ok (ForInStep.yield (r ++ [(x.fst, value)]))
        | none =>
          match defaultValueIn factory x.snd with
          | some value =>
            if (!Lambda.LExpr.isValue factory value) = true then
              Except.error StopReason.expectedValueChoice
            else if (!valueHasMonoType factory value x.snd) = true then
              Except.error StopReason.illTypedValue
            else Except.ok (ForInStep.yield (r ++ [(x.fst, value)]))
          | none => Except.error (StopReason.missingBinding x.fst.name))) = .ok out) :
    out.map Prod.fst = acc.map Prod.fst ++ inputs.map Prod.fst := by
  induction inputs generalizing acc with
  | nil => simp [← Except.ok.inj hok]
  | cons input inputs ih =>
    rw [List.forIn_cons] at hok
    revert hok
    (repeat' split) <;> first
      | (intro h; cases h)
      | (intro hok; simp [ih _ hok])

/-- Inversion of a successful `valuationToEnv`: its inputs loop succeeds with bindings `out`
    whose keys are the input names, its events loop succeeds with the returned `oracle`, and
    `env` is the environment with the given factory, no failure, and the store that looks a
    name up in `out`. -/
theorem cel_vte {factory : @Lambda.Factory CoreLParams} {unit : PassiveUnit}
    {obligation : ProofObligation Expression} {link : ObligationExtraction.ExtractBackLink}
    {store : RStore Expression} {env : IEnv Expression} {oracle : OracleSeed}
    (henv : valuationToEnv factory unit obligation link store = .ok (env, oracle)) :
    ∃ out, (forIn (m := Except StopReason) unit.inputs []
      (fun x r =>
        match store x.fst with
        | some value =>
          if (!Lambda.LExpr.isValue factory value) = true then
            Except.error StopReason.expectedValueChoice
          else if (!valueHasMonoType factory value x.snd) = true then
            Except.error StopReason.illTypedValue
          else Except.ok (ForInStep.yield (r ++ [(x.fst, value)]))
        | none =>
          match defaultValueIn factory x.snd with
          | some value =>
            if (!Lambda.LExpr.isValue factory value) = true then
              Except.error StopReason.expectedValueChoice
            else if (!valueHasMonoType factory value x.snd) = true then
              Except.error StopReason.illTypedValue
            else Except.ok (ForInStep.yield (r ++ [(x.fst, value)]))
          | none => Except.error (StopReason.missingBinding x.fst.name))) = .ok out ∧
    out.map Prod.fst = unit.inputs.map Prod.fst ∧
    (forIn (m := Except StopReason) link.events []
      (fun event r =>
        match event with
        | .branch takeThen =>
          Except.ok (ForInStep.yield (r ++ [if takeThen = true then HasBool.tt else HasBool.ff]))
        | .nondetWrite name expectedType =>
          match store name with
          | some value =>
            if (!Lambda.LExpr.isValue factory value) = true then
              Except.error StopReason.expectedValueChoice
            else
              match expectedType with
              | some ty =>
                if (!valueHasType factory value
                    ty) = true then Except.error StopReason.illTypedValue
                else Except.ok (ForInStep.yield (r ++ [value]))
              | _ => Except.ok (ForInStep.yield (r ++ [value]))
          | none =>
            match (expectedType.bind fun ty => ty.toMonoType?).bind (defaultValueIn factory) with
            | some value =>
              if (!Lambda.LExpr.isValue factory value) = true then
                Except.error StopReason.expectedValueChoice
              else
                match expectedType with
                | some ty =>
                  if (!valueHasType factory value
                      ty) = true then Except.error StopReason.illTypedValue
                  else Except.ok (ForInStep.yield (r ++ [value]))
                | _ => Except.ok (ForInStep.yield (r ++ [value]))
            | none => Except.error (StopReason.missingBinding name.name))) = .ok oracle ∧
    env = { store := .ofStore fun name =>
              (out.find? fun (candidate, _) => candidate == name).map Prod.snd,
            factory := factory } := by
  simp only [valuationToEnv] at henv
  split at henv
  · cases henv
  obtain ⟨-, -, henv⟩ := (Except.bind_is_ok _ _ _).1 henv
  obtain ⟨out, hinputs, henv⟩ := (Except.bind_is_ok _ _ _).1 henv
  obtain ⟨_, hevents, henv⟩ := (Except.bind_is_ok _ _ _).1 henv
  cases henv
  exact ⟨out, hinputs, by simpa using inputs_forIn_keys _ _ _ _ _ hinputs, hevents, rfl⟩

/-- **The operational store defines only input names.**  When `valuationToEnv` succeeds,
    any name defined in the produced `env.store` is an input name of the passive unit:
    `env.store` is a `find?` lookup over the inputs-loop bindings, whose keys are exactly
    the input names. -/
theorem valuationToEnv_inputs_only
    (factory : @Lambda.Factory CoreLParams)
    (unit : PassiveUnit) (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression)
    (env : IEnv Expression) (oracle : OracleSeed)
    (henv : valuationToEnv factory unit obligation link store = .ok (env, oracle)) :
    ∀ x, (env.store.get x).isSome → x ∈ unit.inputs.map (·.1) := by
  obtain ⟨_, -, hkeys, -, rfl⟩ := cel_vte henv
  simp only [IStore.get_ofStore]
  grind

/-! ## Replay reaches the failing assertion

The replay from `.stmts link.entryStatements env`, fed the `oracle` that `valuationToEnv`
builds from `link.events`, walks the extracted path to `link.targetLabel` and returns
`.genuine`.  This part holds the engine-independent ingredients of that fact: the closed form
of the oracle, evaluation transfer between agreeing stores, and the shape of the emitted links
and assumptions. -/

/-! ### The oracle `valuationToEnv` builds -/

open Imperative

/-- The oracle value one replay event contributes: the branch's Boolean for a branch
    choice; for a nondeterministic write, the valuation's value of the written variable,
    or else the default value of its expected type. -/
def eventChoice (factory : @Lambda.Factory CoreLParams) (store : RStore Expression) :
    ObligationExtraction.ExtractReplayEvent → Option Expression.Expr
  | .branch takeThen => some (if takeThen then HasBool.tt else HasBool.ff)
  | .nondetWrite name expectedType =>
    match store name with
    | some value => some value
    | none =>
      (expectedType.bind (fun ty => Lambda.LTy.toMonoType? ty)).bind (defaultValueIn factory)

/-- Closed form of `valuationToEnv`'s events loop: the produced oracle is the
    per-event `eventChoice` fold, when every entry is defaultable. -/
def eventsToOracle (factory : @Lambda.Factory CoreLParams) (store : RStore Expression) :
    List ObligationExtraction.ExtractReplayEvent → Option OracleSeed
  | [] => some []
  | ev :: rest =>
    match eventChoice factory store ev, eventsToOracle factory store rest with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The events `forIn` inside `valuationToEnv`, when it returns `.ok`, produces
    exactly `acc ++ o` where `eventsToOracle factory store events = some o`. -/
private theorem events_forIn_eq_eventsToOracle
    (factory : @Lambda.Factory CoreLParams)
    (store : RStore Expression)
    (events : List ObligationExtraction.ExtractReplayEvent)
    (acc : OracleSeed) (out : OracleSeed)
    (hok : (forIn (m := Except StopReason) events acc
      (fun event r =>
        match event with
        | .branch takeThen =>
          Except.ok (ForInStep.yield (r ++ [if takeThen = true then HasBool.tt else HasBool.ff]))
        | .nondetWrite name expectedType =>
          match store name with
          | some value =>
            if (!Lambda.LExpr.isValue factory value) = true then
              Except.error StopReason.expectedValueChoice
            else
              match expectedType with
              | some ty =>
                if (!valueHasType factory value
                    ty) = true then Except.error StopReason.illTypedValue
                else Except.ok (ForInStep.yield (r ++ [value]))
              | _ => Except.ok (ForInStep.yield (r ++ [value]))
          | none =>
            match (expectedType.bind fun ty => ty.toMonoType?).bind (defaultValueIn factory) with
            | some value =>
              if (!Lambda.LExpr.isValue factory value) = true then
                Except.error StopReason.expectedValueChoice
              else
                match expectedType with
                | some ty =>
                  if (!valueHasType factory value
                      ty) = true then Except.error StopReason.illTypedValue
                  else Except.ok (ForInStep.yield (r ++ [value]))
                | _ => Except.ok (ForInStep.yield (r ++ [value]))
            | none => Except.error (StopReason.missingBinding name.name))) = .ok out) :
    ∃ o, eventsToOracle factory store events = some o ∧ out = acc ++ o := by
  induction events generalizing acc with
  | nil => exact ⟨[], rfl, by simp [← Except.ok.inj hok]⟩
  | cons ev rest ih =>
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.forIn_cons, Except.bind_is_ok] at hok ih
    obtain ⟨_, hstep, hok⟩ := hok
    grind [eventsToOracle, eventChoice]

/-- The oracle `valuationToEnv` returns is exactly the `eventsToOracle` fold of
    `link.events` over the valuation. -/
theorem valuationToEnv_oracle_eq
    (factory : @Lambda.Factory CoreLParams)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (store : RStore Expression)
    (env : IEnv Expression) (oracle : OracleSeed)
    (henv : valuationToEnv factory (PassiveUnit.forObligation link obligation) obligation link store
              = .ok (env, oracle)) :
    eventsToOracle factory store link.events = some oracle := by
  obtain ⟨-, -, -, hevents, -⟩ := cel_vte henv
  exact (events_forIn_eq_eventsToOracle _ _ _ _ _ hevents).elim fun _ ⟨ho, heq⟩ => heq ▸ ho

/-! ### Store agreement and evaluation transfer

Facts about the replay store: evaluation of an expression whose free variables are
defined agrees between agreeing stores, and an update with a factory value keeps a store
well-formed. -/

/-- The replay store `opStore` agrees with the valuation `store` (`StoreAgreement`): every
    variable defined in `opStore` has the same value in `store`. -/
def store_agrees (opStore store : RStore Expression) : Prop :=
  ∀ x v, opStore x = some v → store x = some v

/-- **Evaluation transfer.**  On a well-formed factory, an expression whose free variables
    are all defined in the replay store `opStore` evaluates the same under `opStore` and
    under any well-formed store `declStore` that `opStore` agrees with (a well-formed store
    holds only canonical values). -/
theorem eval_transfer_on_defined
    (factory : @Lambda.Factory CoreLParams)
    (hWF : Lambda.FactoryWF factory)
    (opStore declStore : RStore Expression) (e : Expression.Expr)
    (hdeclWF : RWellFormedStore declStore factory)
    (hAgree : store_agrees opStore declStore)
    (hdef : RStore.isDefined opStore (Lambda.LExpr.freeVars e).unzip.fst) :
    Lambda.LExpr.evalFully factory opStore e = Lambda.LExpr.evalFully factory declStore e := by
  refine evalFully_env_congr (fun a b h => by cases a; cases b; simp_all) factory _ _ hWF
    (fun x v hx => Lambda.isValue_getVars_nil factory v (hdeclWF x v hx)) e fun x hx => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1
    (hdef x (by grind [getVars_eq_freeVars_idents]))
  exact hv.trans (hAgree x v hv).symm

/-- **well-formedness preserved by an update with a factory value.**  Updating a
    well-formed store at `name` with a value that is itself a factory value
    (`HasVal.value`) keeps the store well-formed. -/
theorem wellFormedStore_update
    (factory : @Lambda.Factory CoreLParams)
    (σ : RStore Expression) (name : Expression.Ident) (v : Expression.Expr)
    (hσ : RWellFormedStore σ factory)
    (hv : Lambda.LExpr.isValue factory v = true) :
    RWellFormedStore (RStore.update σ name v) factory := by
  grind [RStore.update, RWellFormedStore]

/-! ### `extractGoLinked` content characterization

The `events` argument of the extraction walk survives verbatim as a prefix of the
`link.events` of every pair the walk emits; the rest of `link.events` holds the branch and
nondeterministic-write choices met between that point and the emitting `assert`/`cover`. -/

/-- Accumulator invariant: every pair already in the accumulator has the current `events`
    argument as a prefix of its `link.events`. -/
def EventsPrefixOK (events : List ObligationExtraction.ExtractReplayEvent)
    (acc : Array ObligationExtraction.LinkedObligation) : Prop :=
  ∀ (ob : ProofObligation Expression) (lnk : ObligationExtraction.ExtractBackLink),
    (ob, lnk) ∈ acc.toList → events <+: lnk.events

/-- The empty accumulator satisfies `EventsPrefixOK`. -/
theorem EventsPrefixOK_empty
    (events : List ObligationExtraction.ExtractReplayEvent) :
    EventsPrefixOK events #[] := nofun

/-- `EventsPrefixOK` is preserved by pushing a pair whose `link.events` extends `events`. -/
private theorem EventsPrefixOK_push_some
    {events : List ObligationExtraction.ExtractReplayEvent}
    {acc : Array ObligationExtraction.LinkedObligation}
    (h : EventsPrefixOK events acc) (ob : ProofObligation Expression)
    (lnk : ObligationExtraction.ExtractBackLink)
    (hlnk : events <+: lnk.events) :
    EventsPrefixOK events (acc.push (ob, lnk)) := by grind [EventsPrefixOK]

/-- `EventsPrefixOK` is preserved by appending accumulators. -/
private theorem EventsPrefixOK_append
    {events : List ObligationExtraction.ExtractReplayEvent}
    {a b : Array ObligationExtraction.LinkedObligation}
    (ha : EventsPrefixOK events a) (hb : EventsPrefixOK events b) :
    EventsPrefixOK events (a ++ b) := by grind [EventsPrefixOK]

/-- **Events prefix (structural).**  If every pair of the starting accumulator `acc` has
    `events` as a prefix of its `link.events` (`EventsPrefixOK`), then so does every pair of
    a successful `extractGoLinked entry pc events ss acc` result. -/
theorem extractGoLinked_events_prefix
    (entry : Statements) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements)
      (acc : Array ObligationExtraction.LinkedObligation)
      (arr : Array ObligationExtraction.LinkedObligation),
      EventsPrefixOK events acc →
      ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr →
      EventsPrefixOK events arr := by
  have hwalk (base pc events ss acc) (hbase : base <+: events) (hacc : EventsPrefixOK base acc) :
      ∀ arr, extractGoLinked entry pc events ss acc = .ok arr → EventsPrefixOK base arr := by
    induction pc, events, ss, acc using extractGoLinked_induct entry <;>
      simp_all only [extractGoLinked_nil, extractGoLinked_assert, extractGoLinked_cover,
        extractGoLinked_assume, extractGoLinked_ite, extractGoLinked_init,
        extractGoLinked_unsupported, bind, Except.bind, Except.ok.injEq, reduceCtorEq,
        forall_eq'] <;>
      grind [EventsPrefixOK_push_some, EventsPrefixOK_append, EventsPrefixOK_empty]
  exact fun _ _ _ _ _ hacc => hwalk _ _ _ _ _ (List.prefix_refl _) hacc _

/-! ### Shape extraction and the scoping bridge

The program-shape check and its predicted fuel, and the relation between the computable
well-scopedness check `Block.readsDefined` and the semantic `WellScopedObl`. -/

/-- **`checkObligationProgram` unfold.**  A successful shape check yields the three Boolean
    shape facts (`Block.nondetIteLast`, `Block.onlyAssertLast`, `Block.readsDefined inputs`) and
    pins the predicted fuel to `Block.stepBudget ss`. -/
theorem checkObligationProgram_some {inputs ss f} :
    checkObligationProgram inputs ss = some f →
      Block.nondetIteLast ss = true ∧ Block.onlyAssertLast ss = true
        ∧ Block.readsDefined inputs ss = true ∧ f = Block.stepBudget ss := by
  grind [checkObligationProgram]

/-- **Syntactic well-scopedness implies semantic well-scopedness.**  If the names defined in
    the store `σ` are exactly those in `defined`, then the computable
    `Block.readsDefined defined ss` check implies `WellScopedObl σ ss` (every statement's
    reads are defined in the store threaded up to it). -/
theorem readsDefined_toWellScopedObl {σ : RStore Expression}
    {defined : List CoreIdent} {ss : Statements} :
    (∀ x ∈ defined, (σ x).isSome) →
    (∀ x, (σ x).isSome → x ∈ defined) →
    Block.readsDefined defined ss = true →
    WellScopedObl σ ss := by
  have hfv (e : Expression.Expr) :
      HasFvars.getFvars (P := Expression) e = (Lambda.LExpr.freeVars e).unzip.fst := by
    simp [HasFvars.getFvars, Lambda.getVars_eq_freeVars_idents]
  induction defined, ss using Block.readsDefined.induct (P := Expression) generalizing σ <;>
    grind [Block.readsDefined, WellScopedObl, RStore.isDefined, RStore.update,
      Option.isSome_iff_ne_none]

/-- Every pair of `acc` has as assumptions the path conditions `pc` with a list of
    entries prepended in program order. -/
def AssumesPrependOK (pc : Imperative.RevPathConditions Expression)
    (acc : Array ObligationExtraction.LinkedObligation) : Prop :=
  ∀ (ob : ProofObligation Expression) (lnk : ObligationExtraction.ExtractBackLink),
    (ob, lnk) ∈ acc.toList →
    ∃ extras : List (Imperative.PathConditionEntry Expression),
      ob.assumptions =
        (extras.foldl Imperative.RevPathConditions.prepend pc).consume

/-- The empty accumulator satisfies `AssumesPrependOK`. -/
private theorem AssumesPrependOK_empty
    (pc : Imperative.RevPathConditions Expression) :
    AssumesPrependOK pc #[] := nofun

/-- **Assumptions extend the path conditions (structural).**  If every pair of the starting
    accumulator `acc` has as assumptions `pc` with a list of entries prepended in program
    order (`AssumesPrependOK pc`), then so does every pair of a successful
    `extractGoLinked entry pc events ss acc` result: for each, some list `extras` gives
    `obligation.assumptions = (extras.foldl RevPathConditions.prepend pc).consume`. -/
private theorem extractGoLinked_assumes_prepend
    (entry : Statements) :
    ∀ (pc : Imperative.RevPathConditions Expression)
      (events : List ObligationExtraction.ExtractReplayEvent) (ss : Statements)
      (acc : Array ObligationExtraction.LinkedObligation)
      (arr : Array ObligationExtraction.LinkedObligation),
      AssumesPrependOK pc acc →
      ObligationExtraction.extractGoLinked entry pc events ss acc = .ok arr →
      AssumesPrependOK pc arr := by
  have hwalk (root pc events ss acc)
      (hroot : ∃ extras : List (PathConditionEntry Expression), pc = extras.foldl .prepend root)
      (hacc : AssumesPrependOK root acc) :
      ∀ arr, extractGoLinked entry pc events ss acc = .ok arr → AssumesPrependOK root arr := by
    induction pc, events, ss, acc using extractGoLinked_induct entry <;>
      simp_all +zetaDelta only [extractGoLinked_nil, extractGoLinked_assert,
        extractGoLinked_cover, extractGoLinked_assume, extractGoLinked_ite, extractGoLinked_init,
        extractGoLinked_unsupported, Except.bind_is_ok, Except.ok.injEq, forall_eq',
        forall_exists_index, and_imp, reduceCtorEq, forall_const]
    case case4 | case6 =>
      rename_i ih
      obtain ⟨extras, rfl⟩ := hroot
      have hnext := ih (extras ++ [_]) (by rw [List.foldl_append]; rfl)
      simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hnext
    all_goals grind [AssumesPrependOK, AssumesPrependOK_empty]
  exact fun _ _ _ _ _ hacc => hwalk _ _ _ _ _ ⟨[], rfl⟩ hacc _

/-- **Assumptions extend the root path conditions (top level).**  Every `(obligation, link)`
    pair a successful `extractLinkedFromStatements pc0 statements` emits has
    `obligation.assumptions = (extras.foldl RevPathConditions.prepend pc0).consume` for some
    program-order list `extras` of path-condition entries. -/
private theorem extractLinked_assumes_are_path
    {pc0 : Imperative.RevPathConditions Expression} (statements : Statements)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (arr : Array ObligationExtraction.LinkedObligation)
    (hok : ObligationExtraction.extractLinkedFromStatements pc0 statements = .ok arr)
    (hmem : (obligation, link) ∈ arr.toList) :
    ∃ extras : List (Imperative.PathConditionEntry Expression),
      obligation.assumptions =
        (extras.foldl Imperative.RevPathConditions.prepend pc0).consume := by
  solve_by_elim [extractGoLinked_assumes_prepend, AssumesPrependOK_empty]

/-! ### Assumes-side per-entry decomposition

The extractor builds path conditions in a reversed representation (`RevPathConditions`).
Moving the fold of `RevPathConditions.prepend` across `consume` presents
`obligation.assumptions` as a program-order fold of `PathConditions.addEntry` over the same
entries, rooted at the consumed root path conditions. -/

/-- **consume commutes with the prepend-fold.**  Folding `RevPathConditions.prepend`
    over a list `extras` and then `consume`-ing equals `consume`-ing first and then
    folding `PathConditions.addEntry` over the *same* `extras` in the *same* order. -/
theorem consume_foldl_prepend
    (extras : List (Imperative.PathConditionEntry Expression)) :
    ∀ (pc : Imperative.RevPathConditions Expression),
      (extras.foldl Imperative.RevPathConditions.prepend pc).consume
        = extras.foldl (fun ps e => Imperative.PathConditions.addEntry ps e) pc.consume := by
  induction extras <;> simp_all [RevPathConditions.consume_prepend]

/-- **Assumptions are a program-order `addEntry` fold (top level).**  Every
    `(obligation, link)` pair a successful `extractLinkedFromStatements pc0 statements` emits
    has `obligation.assumptions = extras.foldl (fun ps e => ps.addEntry e) pc0.consume` for
    some program-order list `extras` of path-condition entries: the assumptions are the root
    path conditions with those entries added one by one. -/
theorem extractLinked_assumes_are_path_folded
    {pc0 : Imperative.RevPathConditions Expression} (statements : Statements)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    (arr : Array ObligationExtraction.LinkedObligation)
    (hok : ObligationExtraction.extractLinkedFromStatements pc0 statements = .ok arr)
    (hmem : (obligation, link) ∈ arr.toList) :
    ∃ extras : List (Imperative.PathConditionEntry Expression),
      obligation.assumptions =
        extras.foldl (fun ps e => Imperative.PathConditions.addEntry ps e)
          pc0.consume :=
  let ⟨extras, h⟩ := extractLinked_assumes_are_path _ _ _ _ hok hmem
  ⟨extras, h.trans (consume_foldl_prepend _ _)⟩

/-! ### Events-side branch-selection inversion for the `.ite` head-case

At a nondeterministic `.ite`, the extraction walk recurses into both branches, with
`events ++ [.branch true]` and `events ++ [.branch false]`.  A pair emitted inside a branch
records which branch it came from: the event after the walk's current `events` in its
`link.events` is `.branch true` for the then-branch and `.branch false` for the
else-branch. -/

/-- **Branch selection.**  If the pair `(obligation, link)` is emitted by the extraction of
    the then-branch `thenSs` (run with `events ++ [.branch true]`) or of the else-branch
    `elseSs` (run with `events ++ [.branch false]`) of a nondeterministic `.ite`, then for the
    branch `b` it came from, the extraction of that branch emits the pair and
    `events ++ [.branch b]` is a prefix of `link.events`. -/
theorem extractGoLinked_events_branch_head
    (entry : Statements) (pc : Imperative.RevPathConditions Expression)
    (events : List ObligationExtraction.ExtractReplayEvent)
    (thenSs elseSs : Statements)
    (obligation : ProofObligation Expression)
    (link : ObligationExtraction.ExtractBackLink)
    -- the target is in a branch, not the post-join continuation
    (hbranch :
      (∃ thenObs,
        ObligationExtraction.extractGoLinked entry pc (events ++ [.branch true]) thenSs #[]
          = .ok thenObs ∧ (obligation, link) ∈ thenObs.toList)
      ∨ (∃ elseObs,
        ObligationExtraction.extractGoLinked entry pc (events ++ [.branch false]) elseSs #[]
          = .ok elseObs ∧ (obligation, link) ∈ elseObs.toList)) :
    ∃ b sub,
      ObligationExtraction.extractGoLinked entry pc (events ++ [.branch b])
          (if b then thenSs else elseSs) #[] = .ok sub
      ∧ (obligation, link) ∈ sub.toList
      ∧ (events ++ [.branch b]) <+: link.events := by
  rcases hbranch with ⟨obs, hrun, hmem⟩ | ⟨obs, hrun, hmem⟩ <;>
    exact ⟨_, obs, hrun, hmem,
      extractGoLinked_events_prefix _ _ _ _ _ _ (EventsPrefixOK_empty _) hrun _ _ hmem⟩

end
end Core

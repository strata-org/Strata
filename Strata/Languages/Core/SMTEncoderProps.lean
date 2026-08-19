/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.Languages.Core.SMTEncoder
import all Strata.DL.Imperative.PathConditionsFold
import all Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.Imperative.PathConditionsFoldProps
public import Strata.Util.OrderedSetProps
import Strata.Util.ExceptProps

/-!
# Proofs about the SMT encoder

Coherence proofs relating the encoder's O(1) index-based lookups to direct
scans, and the faithfulness proof for the shared-prefix obligation encoder.

Key results:

- `SMT.Context.committedFn_eq_any` — `committedFn`'s O(1) `ifs` key-index lookup
  agrees with a linear scan over the interpreted functions, provided the index
  is well-formed.
- `SMT.Datatypes.getType_ofFactory` — the name→datatype hash index built by
  `SMT.Datatypes.ofFactory` returns exactly what a linear scan of the underlying
  `TypeFactory` would.
- `encodeObligationToSMT_eq_reference` — the per-obligation
  faithfulness result and the main building block for the run-level theorem: on
  a state satisfying the `RefFaithful` invariant at a checkpoint `initial`,
  encoding one obligation incrementally (`encodeObligationToSMT`) equals
  encoding it from scratch from `initial` (`encodeObligationToSMT_reference`).
- `encodeRunFrom_eq_reference` — the general run-level statement: from any
  state satisfying `RefFaithful` at the checkpoint `{ ctx }`, the
  incremental run (`encodeRunFrom`) equals the from-scratch run (`encodeRun_reference`).
  Reusable for resuming from a mid-run state.
- `encodeRun_eq_reference` — the fresh-state corollary of the above:
  threading one `SMTEncodeState` through a list of obligations (`encodeRun`)
  produces, as `Except` values, exactly the results of encoding each obligation
  independently from scratch (`encodeRun_reference`). -/

namespace Core
open Strata.SMT
open Strata.Util

/-- `committedFn`'s O(1) index lookup agrees with a linear scan over the
    interpreted functions, provided the `ifs` index is well-formed. -/
public theorem SMT.Context.committedFn_eq_any (ctx : SMT.Context) (uf : UF)
    (h : OrderedKeyedSetWF ctx.ifs) :
    ctx.committedFn uf
      = (ctx.ufs.contains uf || ctx.ifs.toArray.any (fun f => f.toUF == uf)) := by
  simp only [SMT.Context.committedFn, h.containsKey_eq_any]

/-! ### Datatype name-index coherence

`SMT.Datatypes.ofFactory` builds the name→datatype index by folding
`Std.HashMap.insertIfNew` over the factory's datatypes. The helper below
characterizes that fold; the exported theorem then specializes it at the empty
starting map. -/

section Datatypes
open Lambda

/-- Looking up `name` after folding `insertIfNew` (keyed on `.name`) over `l`
    into a starting map `m`: `insertIfNew`'s first-wins semantics means an
    existing binding in `m` takes precedence, and otherwise the result is the
    first list element whose name matches. -/
private theorem getElem?_foldl_insertIfNew
    (l : List (LDatatype CoreLParams.IDMeta)) (name : String)
    (m : Std.HashMap String (LDatatype CoreLParams.IDMeta)) :
    (l.foldl (fun m d => m.insertIfNew d.name d) m)[name]?
      = (m[name]?).or (l.find? (·.name == name)) := by
  induction l generalizing m with
  | nil => simp only [List.foldl_nil, List.find?_nil, Option.or_none]
  | cons d l ih =>
    simp only [List.foldl_cons, List.find?_cons, ih, Std.HashMap.getElem?_insertIfNew]
    by_cases h : d.name = name
    · subst h
      simp only [beq_self_eq_true, true_and, Std.HashMap.mem_iff_isSome_getElem?, Option.or_some]
      cases m[d.name]? with
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true, ↓reduceIte,
          Option.some_or, Option.getD_none]
      | some v =>
        simp only [Option.isSome_some, not_true_eq_false, ↓reduceIte, Option.some_or,
          Option.getD_some]
    · have hne : (d.name == name) = false := beq_false_of_ne h
      simp only [hne, Bool.false_eq_true, false_and, if_false]

/-- `SMT.Datatypes.getType` agrees with `TypeFactory.getType`: the hash index
    computed by `ofFactory` returns exactly what a linear scan of the factory
    would. -/
theorem SMT.Datatypes.getType_ofFactory (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (name : String) :
    (SMT.Datatypes.ofFactory tf).getType name = tf.getType name := by
  simp only [SMT.Datatypes.getType, SMT.Datatypes.ofFactory,
    Lambda.TypeFactory.getType, Std.HashMap.get?_eq_getElem?]
  rw [getElem?_foldl_insertIfNew, Std.HashMap.getElem?_empty, Option.none_or]

end Datatypes


open Std (ToFormat Format format)
open Lambda Strata.SMT Strata.SMT.Encoder
open Imperative (PathConditionEntry ExprOrNondet PathCondition PathConditions)
open Imperative.PathConditions (Fold FoldState refFaithful_init)

public section

/-! ## Faithfulness of the shared-prefix obligation encoder

`encodeObligationToSMT` reuses whichever of an obligation's `assumptions` the
threaded `SMTEncodeState` already encoded for earlier obligations. The
theorems below show the reuse is invisible in the output: each obligation's
`EncodeResult` is exactly what encoding that obligation alone, from scratch,
would produce. The proofs instantiate the fold's faithfulness theorem
(`Imperative.PathConditions.Fold.advance_eq_reference`,
PathConditionsFoldProps.lean) at `smtEncodingFold`.

The per-obligation theorem is conditional on `RefFaithful`
(PathConditionsFoldProps.lean), the run's induction invariant. -/

/-- Reference implementation of `encodeObligationToSMT`: encode the
    obligation's `assumptions` from scratch starting at `initial`, then
    `snapshotObligation` for the goal. -/
def encodeObligationToSMT_reference (factory : @Lambda.Factory CoreLParams) (initial : SMTCheckpoint)
    (ob : Imperative.ProofObligation Expression) (prunedLabels : List String) :
    Except Format (EncodeResult × SMTEncodeState) := do
  let st' ← Fold.reference (smtEncodingFold factory) initial ob.assumptions.reverse
  let r ← snapshotObligation factory st' ob.obligation prunedLabels
  .ok (r, st')

/-- On a state satisfying `RefFaithful` at `initial`, `encodeObligationToSMT`
    equals `encodeObligationToSMT_reference` run from `initial`. -/
theorem encodeObligationToSMT_eq_reference (factory : @Lambda.Factory CoreLParams)
    {st : SMTEncodeState} {initial : SMTCheckpoint}
    (hc : st.RefFaithful (smtEncodingFold factory) initial)
    (ob : Imperative.ProofObligation Expression) (prunedLabels : List String) :
    encodeObligationToSMT factory st ob prunedLabels =
      encodeObligationToSMT_reference factory initial ob prunedLabels := by
  unfold encodeObligationToSMT encodeObligationToSMT_reference
  rw [Fold.advance_eq_reference (smtEncodingFold factory) hc]


/-! ### Run-level faithfulness

The obligation-level corollaries iterated across a whole run. `encodeRun`
threads one shared state through a list of obligations;
`encodeRun_reference` encodes each obligation independently from scratch. The theorem
`encodeRun_eq_reference` says the two agree. -/

/-- Reference encoding of one obligation, seeded with the context `ctx`:
    encode its `assumptions` from scratch, then `snapshotObligation` for the
    goal. Takes no `SMTEncodeState`, so it cannot depend on other
    obligations. -/
def encodeObligation_reference (factory : @Lambda.Factory CoreLParams) (ctx : SMT.Context)
    (ob : Imperative.ProofObligation Expression) (prunedLabels : List String) :
    Except Format EncodeResult := do
  let st ← Fold.reference (smtEncodingFold factory) { ctx } ob.assumptions.reverse
  snapshotObligation factory st ob.obligation prunedLabels

/-- Incremental run: thread one shared state through the obligation list,
    collecting each obligation's result. -/
def encodeRunFrom (factory : @Lambda.Factory CoreLParams) :
    SMTEncodeState → List (Imperative.ProofObligation Expression × List String) →
    Except Format (List EncodeResult)
  | _, [] => .ok []
  | st, (ob, prunedLabels) :: rest => do
      let (result, st') ← encodeObligationToSMT factory st ob prunedLabels
      let results ← encodeRunFrom factory st' rest
      .ok (result :: results)

/-- Incremental run from the initial state built on `ctx`. -/
def encodeRun (factory : @Lambda.Factory CoreLParams) (ctx : SMT.Context)
    (obs : List (Imperative.ProofObligation Expression × List String)) :
    Except Format (List EncodeResult) :=
  encodeRunFrom factory (FoldState.init { ctx }) obs

/-- Reference run: encode every obligation independently from scratch. -/
def encodeRun_reference (factory : @Lambda.Factory CoreLParams) (ctx : SMT.Context) :
    List (Imperative.ProofObligation Expression × List String) →
    Except Format (List EncodeResult)
  | [] => .ok []
  | (ob, prunedLabels) :: rest => do
      let result ← encodeObligation_reference factory ctx ob prunedLabels
      let results ← encodeRun_reference factory ctx rest
      .ok (result :: results)

/-- Run faithfulness: the incremental run equals the reference run, starting
    from any state `st` that satisfies the `RefFaithful` invariant at the
    checkpoint `{ ctx }`. -/
theorem encodeRunFrom_eq_reference (factory : @Lambda.Factory CoreLParams)
    (st : SMTEncodeState) (ctx : SMT.Context)
    (hc : st.RefFaithful (smtEncodingFold factory) { ctx })
    (obs : List (Imperative.ProofObligation Expression × List String)) :
    encodeRunFrom factory st obs = encodeRun_reference factory ctx obs := by
  induction obs generalizing st hc with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨ob, prunedLabels⟩ := head
    -- One incremental step equals fresh encoding of that obligation from
    -- the run's starting checkpoint `{ ctx }`.
    have hStepEq := encodeObligationToSMT_eq_reference factory hc ob prunedLabels
    cases hRef : Fold.reference (smtEncodingFold factory) { ctx } ob.assumptions.reverse with
    | error _ =>
      simp only [encodeRunFrom, encodeRun_reference, encodeObligation_reference,
        encodeObligationToSMT_reference, hStepEq, hRef, Bind.bind, Except.bind]
    | ok st' =>
      -- The `assumptions` fold succeeded; the obligation's own result is
      -- `snapshotObligation`'s outcome.
      cases hSnap : snapshotObligation factory st' ob.obligation prunedLabels with
      | error _ =>
        simp only [encodeRunFrom, encodeRun_reference, encodeObligation_reference,
          encodeObligationToSMT_reference, hStepEq, hRef, hSnap, Bind.bind, Except.bind]
      | ok _ =>
        -- The advanced state st' is a reference-encoding result, so it satisfies
        -- the invariant; the induction hypothesis then covers the rest of the run.
        obtain ⟨hc', -⟩ := Fold.reference_refFaithful (smtEncodingFold factory) hRef
        simp only [encodeRunFrom, encodeRun_reference, encodeObligation_reference,
          encodeObligationToSMT_reference, hStepEq, hRef, hSnap, Bind.bind, Except.bind]
        rw [ih st' hc']

/-- **Run-level faithfulness**: threading one `SMTEncodeState` through a list
    of obligations produces exactly the results of encoding each obligation
    independently from scratch. -/
theorem encodeRun_eq_reference (factory : @Lambda.Factory CoreLParams)
    (ctx : SMT.Context)
    (obs : List (Imperative.ProofObligation Expression × List String)) :
    encodeRun factory ctx obs = encodeRun_reference factory ctx obs :=
  encodeRunFrom_eq_reference factory (FoldState.init { ctx }) ctx
    (refFaithful_init (smtEncodingFold factory) { ctx }) obs

end -- public section

end Core

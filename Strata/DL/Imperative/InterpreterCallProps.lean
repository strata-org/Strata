/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.InterpreterCall
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterReplay
import all Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.InterpreterTypes
public import Strata.DL.Imperative.InterpreterSemanticsSpec
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.InterpreterReplayProps
import Strata.DL.Imperative.InterpreterTypesProps
import Strata.DL.Imperative.InterpreterReplayTactics
import Strata.DL.Imperative.InterpreterConfigProps

/-! # Properties of the call-aware stepper

Lemmas about the definitions of `InterpreterCall.lean`:
* reduction lemmas for `stepCmd` and `runCallInterp` (`stepCmd_cmd`, `runCallInterp_eq`);
* path feasibility (`pathFeasible_of_subset`, `pathFeasible_cons`) and genuineness as a trace
  property (`genuine_iff`);
* the executable call helpers against the reference store relations
  (`readVarList_of_readValues`, `readValues_of_readVarList`, `readVarList_defined`,
  `bindPositional_of_updateStates`, `updateStates_bindPositional`,
  `callEntryStore_of_initCallFrame`, `initCallFrame_callEntryStore`,
  `evalBoundedList_of_evalExpressions`);
* value-only and typed stores across the call helpers (`values_of_readVarList`,
  `typed_of_readVarList`, `storeTyped_bindPositional`, `wellFormedStore_callEntryStore`,
  `storeTyped_callEntryStore`);
* the runtime call marshalling against its semantic image (`readVarList_absStore`,
  `readVarList_absStore_of_denoting`, `absStore_bindPositional`, `denoting_bindPositional`,
  `absStore_withOldSnapshotsV`, `callEntryStore_abs`, `rDefaultAssertEvents_abs`);
* `targetReached_of_assertFailureHalt`: the halting predicate fires only on target-id matches. -/

/-! ## Stepper reductions -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr}
section Stepper
variable [DecidableEq P.Ident] [HasOldIdent P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P] [HasFvar P]

/-- The call-aware stepper on a base command runs `stepBaseCmdStore` and returns a `.terminal`
    configuration carrying the new store. -/
@[simp] theorem stepCmd_cmd {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (π : String → Option (Procedure P (CmdExt P) Hdr)) (depth : Nat)
    (fuel : Nat) (env : IEnv P) (base : Cmd P) :
    stepCmd (m := m) π depth fuel env (.cmd base)
      = (stepBaseCmdStore fuel env.factory env.store base >>=
          fun store => pure (.terminal { env with store := store })) := by rw [stepCmd]

/-- The call-aware driver `runCallInterp` is `runInterp` over the stepper `stepCmd π d`. -/
@[simp] theorem runCallInterp_eq {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (π : String → Option (Procedure P (CmdExt P) Hdr)) (fuel : Nat)
    (cfg : IConfig P (CmdExt P)) (d : Nat) :
    runCallInterp (m := m) π fuel cfg d = runInterp (stepCmd π d) fuel cfg := rfl

end Stepper
end Calls
end
end Imperative

/-! ## Path feasibility and genuineness -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]

omit [DecidableEq P.Expr] in
/-- Path-feasibility (every `.assume` event evaluates to `tt` under the bounded evaluator) is
    inherited by any sub-trace (`evs' ⊆ evs`). -/
theorem pathFeasible_of_subset {fuel : Nat} {evs evs' : List (IEvent P)}
    (hsub : evs' ⊆ evs) (h : PathFeasible fuel evs) : PathFeasible fuel evs' :=
  fun _ => h _ ∘ @hsub _

omit [DecidableEq P.Expr] in
/-- `e :: evs` is path-feasible (every `.assume` event evaluates under the bounded evaluator to
    `tt` up to metadata) iff `e`, if an `.assume`, evaluates to `tt` up to metadata and `evs` is
    path-feasible. -/
theorem pathFeasible_cons {fuel : Nat} {e : IEvent P} {evs : List (IEvent P)} :
    PathFeasible fuel (e :: evs) ↔
      (∀ arg, e = REvent.assume arg →
        (InterpLang.boundedEval (P := P) fuel arg.factory arg.store arg.expr).bind
          InterpLang.boolLit? = some true)
      ∧ PathFeasible fuel evs :=
  ⟨fun h => ⟨fun a he => h a (he ▸ .head _), fun a ha => h a (.tail _ ha)⟩,
    fun ⟨h1, h2⟩ a ha => (List.mem_cons.1 ha).elim (fun he => h1 a he.symm) (h2 a)⟩

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
variable [DecidableEq P.Ident] [HasOldIdent P] [HasFvar P]
  {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- A counterexample is genuine (its strict call-aware replay returns the `.genuine` verdict) iff
    the replay's trace contains an event on which the halting predicate `assertFailureHalt`
    fires. -/
theorem genuine_iff (π : String → Option (Procedure P (CmdExt P) Hdr)) (target : AssertId P)
    (fuel : Nat) (cex : CexA P (CmdExt P)) (d : Nat) :
    genuine π target fuel cex d ↔
        ∃ ev ∈ (runReplayRun (runCallInterp (m := ReplayM P) π fuel cex.cfg d)
                  { oracleConfig := .strict }
                  cex.oracle).2.traceRev,
          assertFailureHalt target fuel ev = true := runReplay_genuine_iff ..

end Calls
end
end Imperative

/-! ## Executable call helpers against the reference store relations -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- If the reference relation `ReadValues` reads the values `vs` of the variables `xs` from `σ`,
    then `readVarList σ xs` returns exactly `vs`. -/
theorem readVarList_of_readValues (f : P.Factory) (σ : SemanticStore P) :
    ∀ (xs : List P.Ident) (vs : List P.Val),
      ReadValues (P := P) f σ xs vs → readVarList σ xs = some vs := fun _ _ h => by
        induction h <;> grind [readVarList]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [DecidableEq P.Ident] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- If initializing `names` one by one to `vals` from `σ` (the reference fold `InitStates`)
    yields `σ'`, then the two lists have equal length and `σ'` is `bindPositional σ names vals`. -/
private theorem bindPositional_of_initStates :
    ∀ (σ σ' : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      InitStates (P := P) σ names vals σ' →
        names.length = vals.length ∧ σ' = bindPositional σ names vals := fun _ _ _ _ h => by
          induction h <;> grind [bindPositional, storeUpdate_eq_update, InitState.eq_update]

/-- If assigning `names` one by one to `vals` in `σ` (the reference fold `UpdateStates`) yields
    `σ'`, then the two lists have equal length and `σ'` is `bindPositional σ names vals`. -/
theorem bindPositional_of_updateStates :
    ∀ (σ σ' : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      UpdateStates (P := P) σ names vals σ' →
        names.length = vals.length ∧ σ' = bindPositional σ names vals := fun _ _ _ _ h => by
          induction h <;> grind [bindPositional, storeUpdate_eq_update, UpdateState.eq_update]

end Calls
end
end Imperative

namespace Imperative
public section

variable {P : PureExpr} [InterpLang P] [DecidableEq P.Ident]

/-- Positionally binding names to values in an interpreter store stands for positionally binding
    them in the store it stands for. -/
theorem IStore.get_bindPositional : ∀ (s : IStore P) (names : List P.Ident) (vals : List P.Expr),
    (s.bindPositional names vals).get = Calls.bindPositional s.get names vals
  | s, n :: ns, v :: vs => by
    rw [IStore.bindPositional, Calls.bindPositional, IStore.get_bindPositional, IStore.get_update]
    rfl
  | _, [], _ | _, _ :: _, [] => rfl

end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type} [DecidableEq Hdr]
    [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- If the reference relation `InitCallFrame` builds the callee frame `σAO` from the input and
    output-only values, then `σAO` is `callEntryStore` of them, and the input and output-only
    formals are as many as their values. -/
theorem callEntryStore_of_initCallFrame (p : Procedure P (CmdExt P) Hdr)
    (inputVals outOnlyVals : List P.Val) (σAO : SemanticStore P)
    (h : InitCallFrame p inputVals outOnlyVals σAO) :
    (ProcedureHeader.inputParams (P := P) p.header).length = inputVals.length
    ∧ (outputOnlyParams (P := P) p.header).length = outOnlyVals.length
    ∧ σAO = callEntryStore p inputVals outOnlyVals := by
  obtain ⟨_, _, hInit, hOut, hσ⟩ := h
  simp only [bindPositional_of_initStates _ _ _ _ hInit,
    bindPositional_of_initStates _ _ _ _ hOut, hσ, true_and]
  rfl

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasFvars P] [InterpLang P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- If the reference semantics evaluates the expressions `es` to `vs` (`EvalExpressions`), then
    `evalBoundedList` returns `vs` at every sufficiently large fuel, provided the bounded evaluator
    reaches every reference value at some fuel and keeps it at every larger fuel. -/
theorem evalBoundedList_of_evalExpressions
    (hEvalComplete : BoundedEvalComplete P) (hMono : BoundedEvalMono P)
    (f : P.Factory) (σr : RStore P) (σ : SemanticStore P) (hσ : StoreDenotes f σr σ) :
    ∀ (es : List P.Expr) (vs : List P.Val), EvalExpressions f σ es vs →
      ∃ N rs, List.Rel₂ (InterpLang.Denotes f) rs vs ∧
        ∀ n, N ≤ n → evalBoundedList n (InterpLang.rfactory f) σr es = some rs := fun _ _ h => by
  induction h with
  | eval_none => exact ⟨0, [], .nil, fun _ _ => rfl⟩
  | eval_some _ hev _ ih =>
    obtain ⟨a, r, ha, hr⟩ := hEvalComplete _ _ _ _ _ hσ hev
    obtain ⟨b, rs, hrs, hb⟩ := ih hσ
    refine ⟨a + b, r :: rs, .cons hr hrs, fun n hn => ?_⟩
    simp only [evalBoundedList, hMono a n _ _ _ _ (by omega) ha, hb n (by omega), Option.map_some]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [DecidableEq P.Ident] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- `bindPositional` leaves a name outside the bound list alone. -/
private theorem bindPositional_not_mem (σ : SemanticStore P)
    (names : List P.Ident) (vals : List P.Val) (y : P.Ident)
    (hy : y ∉ names) : bindPositional σ names vals y = σ y := by
  fun_induction bindPositional σ names vals <;> grind [SemanticStore.update, storeUpdate]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- On a store whose every entry is a value of the factory (`WellFormedStore`), a successful
    `readVarList` is a reference `ReadValues` derivation reading the same values. -/
theorem readValues_of_readVarList (f : P.Factory) (σ : SemanticStore P)
    (hv : WellFormedStore σ f) :
    ∀ (xs : List P.Ident) (vs : List P.Val),
      readVarList σ xs = some vs → ReadValues (P := P) f σ xs vs := fun xs => by
        induction xs <;> grind [readVarList, ReadValues, WellFormedStore, Option.map_eq_some_iff]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [DecidableEq P.Ident] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- When the names are pairwise distinct, unbound in `σ` and as many as the values,
    `bindPositional` is the reference fold initializing them one by one (`InitStates`). -/
private theorem initStates_bindPositional :
    ∀ (σ : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      names.length = vals.length → names.Nodup → SemanticStore.varsUndefined (· ∈ names) σ →
      InitStates (P := P) σ names vals (bindPositional σ names vals) := fun σ ns vs => by
        fun_induction bindPositional σ ns vs <;> (try simp only [storeUpdate_eq_update] at *) <;> grind [InitStates, SemanticStore.varsUndefined,
            InitState.of_update, SemanticStore.update, storeUpdate, cases List]

/-- When every name is bound in `σ` and the names are as many as the values, `bindPositional` is
    the reference fold assigning them one by one (`UpdateStates`). -/
theorem updateStates_bindPositional :
    ∀ (σ : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      names.length = vals.length → SemanticStore.varsDefined (· ∈ names) σ →
      UpdateStates (P := P) σ names vals (bindPositional σ names vals) := fun σ ns vs => by
        fun_induction bindPositional σ ns vs <;> (try simp only [storeUpdate_eq_update] at *) <;>
            (try simp_all only [SemanticStore.varsDefined, Option.isSome_iff_exists, List.length_cons,
              Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp, and_imp,
              forall_exists_index, imp_false]) <;>
            grind [UpdateStates, cases List, SemanticStore.update, storeUpdate,
              UpdateState.of_update]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type} [DecidableEq Hdr]
    [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- When the input and output-only formals are pairwise distinct and as many as their values, the
    engine's callee frame `callEntryStore` is a frame the reference relation `InitCallFrame`
    builds. -/
theorem initCallFrame_callEntryStore (p : Procedure P (CmdExt P) Hdr)
    (inputVals outOnlyVals : List P.Val)
    (hin : (ProcedureHeader.inputParams (P := P) p.header).length = inputVals.length)
    (hout : (outputOnlyParams (P := P) p.header).length = outOnlyVals.length)
    (hnd : (ProcedureHeader.inputParams (P := P) p.header ++
            outputOnlyParams (P := P) p.header).Nodup) :
    InitCallFrame p inputVals outOnlyVals (callEntryStore p inputVals outOnlyVals) := by
  obtain ⟨hndIn, hndOut, hdisj⟩ := List.nodup_append.1 hnd
  exact ⟨_, _, initStates_bindPositional _ _ _ hin hndIn fun _ _ => rfl,
    initStates_bindPositional _ _ _ hout hndOut
      fun y hy => bindPositional_not_mem _ _ _ y (hdisj y · y hy rfl), rfl⟩

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- A successful `readVarList` means every name it read is bound. -/
theorem readVarList_defined (σ : SemanticStore P) :
    ∀ (xs : List P.Ident) (vs : List P.Val),
      readVarList σ xs = some vs → SemanticStore.varsDefined (· ∈ xs) σ := fun xs => by
        induction xs <;> grind [readVarList, SemanticStore.varsDefined, Option.map_eq_some_iff]

end Calls
end
end Imperative

/-! ## Value-only and typed stores -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] {Hdr : Type} [DecidableEq Hdr]
    [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- A positional bind of values keeps a store value-only (every entry a value of the factory). -/
private theorem wellFormedStore_bindPositional {f : P.Factory} :
    ∀ (σ : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      WellFormedStore σ f → (∀ v ∈ vals, HasVal.value f v) →
      WellFormedStore (bindPositional σ names vals) f := fun σ ns vs => by
        fun_induction bindPositional σ ns vs <;> (try simp only [storeUpdate_eq_update] at *) <;> grind [WellFormedStore, SemanticStore.update]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type}
    [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- `withOldSnapshots` keeps a store value-only (every entry a value of the factory). -/
private theorem wellFormedStore_withOldSnapshots {f : P.Factory}
    (snapshot : List P.Ident) (σ : SemanticStore P) (hsv : WellFormedStore σ f) :
    WellFormedStore (withOldSnapshots snapshot σ) f := fun z w => by
      unfold withOldSnapshots
      split <;> apply hsv

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- On a store whose every entry is a value of the factory, a successful `readVarList` returns
    values. -/
theorem values_of_readVarList {f : P.Factory} {σ : SemanticStore P}
    (hsv : WellFormedStore σ f) :
    ∀ (xs : List P.Ident) (vs : List P.Val),
      readVarList σ xs = some vs → ∀ v ∈ vs, HasVal.value f v := fun xs => by
        induction xs <;> grind [readVarList, WellFormedStore, Option.map_eq_some_iff]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type}
    [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- The callee frame `callEntryStore` built from values is value-only (every entry a value of the
    factory). -/
theorem wellFormedStore_callEntryStore {f : P.Factory} (p : Procedure P (CmdExt P) Hdr)
    (inputVals outOnlyVals : List P.Val)
    (hin : ∀ v ∈ inputVals, HasVal.value f v)
    (hout : ∀ v ∈ outOnlyVals, HasVal.value f v) :
    WellFormedStore (callEntryStore p inputVals outOnlyVals) f := by
  exact wellFormedStore_withOldSnapshots _ _ (wellFormedStore_bindPositional _ _ _
    (wellFormedStore_bindPositional _ _ _ nofun hin) hout)

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] {Hdr : Type} [DecidableEq Hdr]
    [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- A positional bind of typed values keeps a store typed (every entry is a value of some
    type, `StoreTyped`). -/
theorem storeTyped_bindPositional {f : P.Factory} :
    ∀ (σ : SemanticStore P) (names : List P.Ident) (vals : List P.Val),
      StoreTyped f σ → (∀ v ∈ vals, ∃ ty, HasVal.valueOfTy f v ty) →
      StoreTyped f (bindPositional σ names vals) := fun σ n v => by
        fun_induction bindPositional σ n v <;> (try simp only [storeUpdate_eq_update] at *) <;>
          grind [StoreTyped, SemanticStore.update]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type}
    [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- `withOldSnapshots` only copies existing bindings, so it keeps a store typed (every entry is a
    value of some type). -/
private theorem storeTyped_withOldSnapshots {f : P.Factory}
    (snapshot : List P.Ident) (σ : SemanticStore P) (hsv : StoreTyped f σ) :
    StoreTyped f (withOldSnapshots snapshot σ) := by grind [StoreTyped, withOldSnapshots]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr]
    [ProcedureHeader P Hdr]

/-- On a typed store (every entry a value of some type), every value a successful `readVarList`
    returns is a value of some type. -/
theorem typed_of_readVarList {f : P.Factory} {σ : SemanticStore P}
    (hsv : StoreTyped f σ) :
    ∀ (xs : List P.Ident) (vs : List P.Val),
      readVarList σ xs = some vs → ∀ v ∈ vs, ∃ ty, HasVal.valueOfTy f v ty := fun xs => by
        fun_induction readVarList σ xs <;>
          simp_all only [Option.some.injEq, List.nil_eq, List.not_mem_nil, false_implies,
            implies_true, Option.map_eq_some_iff, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂, List.mem_cons, forall_eq_or_imp, and_true, reduceCtorEq]
        grind [StoreTyped]

end Calls
end
end Imperative

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBoolOps P] [DecidableEq P.Ident] [HasOldIdent P] {Hdr : Type}
    [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- The callee frame `callEntryStore` is typed (every entry is a value of some type) when its
    input and output-only values are. -/
theorem storeTyped_callEntryStore {f : P.Factory} (p : Procedure P (CmdExt P) Hdr)
    (inputVals outOnlyVals : List P.Val)
    (hin : ∀ v ∈ inputVals, ∃ ty, HasVal.valueOfTy f v ty)
    (hout : ∀ v ∈ outOnlyVals, ∃ ty, HasVal.valueOfTy f v ty) :
    StoreTyped f (callEntryStore p inputVals outOnlyVals) := by
  grind [callEntryStore, withOldSnapshotsV_eq, storeTyped_withOldSnapshots,
    storeTyped_bindPositional, StoreTyped]

end Calls
end
end Imperative

/-! ## Runtime call marshalling against its semantic image

The engine's `.call` step marshals runtime values (`readVarList`, `bindPositional`,
`callEntryStore`, `rDefaultAssertEvents`); on denoting stores each of these stands for the
semantic operation the reference call rule uses. -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [InterpLang P]

/-- The runtime assert events of the non-free clauses of `checks` at a runtime snapshot stand
    for the semantic ones at its image. -/
theorem rDefaultAssertEvents_abs (F : P.Factory) (σ : RStore P)
    (checks : ListMap String (Check P)) :
    (rDefaultAssertEvents (InterpLang.rfactory F) σ checks).map (REvent.abs F) =
      defaultAssertEvents F (InterpLang.absStore F σ) checks := by
  simp only [rDefaultAssertEvents, defaultAssertEvents, List.map_filterMap]
  congr
  funext ⟨_, _⟩
  split <;> rfl

/-- A successful read of names in the image of a runtime store reads runtime values that denote
    the values read. -/
theorem readVarList_absStore {F : P.Factory} (σ : RStore P) :
    ∀ (xs : List P.Ident) {vs : List P.Val},
      readVarList (InterpLang.absStore F σ) xs = some vs →
      ∃ rs, readVarList σ xs = some rs ∧ List.Rel₂ (InterpLang.Denotes F) rs vs
  | [], _, h => ⟨[], rfl, by cases h; exact .nil⟩
  | x :: xs, _, h => by
    simp only [readVarList, InterpLang.absStore] at h
    rcases hx : σ x with _ | r
    · simp [hx] at h
    rcases hd : InterpLang.denote F r with _ | v
    · simp [hx, hd] at h
    simp only [hx, hd, Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨vs, hvs, rfl⟩ := h
    obtain ⟨rs, hrs, hrel⟩ := readVarList_absStore σ xs hvs
    exact ⟨r :: rs, by simp [readVarList, hx, hrs], .cons hd hrel⟩

/-- The converse of `readVarList_absStore` on a denoting runtime store: the values a successful
    `readVarList` reads from the store denote the values `readVarList` reads from its image. -/
theorem readVarList_absStore_of_denoting {F : P.Factory} {σ : RStore P}
    (hd : RStore.Denoting F σ) :
    ∀ (xs : List P.Ident) (rs : List P.Expr), readVarList σ xs = some rs →
      ∃ vs, List.Rel₂ (InterpLang.Denotes F) rs vs ∧
        readVarList (InterpLang.absStore F σ) xs = some vs
  | [], _, h => by
    cases h
    exact ⟨[], .nil, rfl⟩
  | x :: xs, rs, h => by
    simp only [readVarList] at h
    split at h
    · rename_i r hr
      obtain ⟨rs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨v, hv⟩ := hd x r hr
      obtain ⟨vs, hrel, hvs⟩ := readVarList_absStore_of_denoting hd xs rs' h'
      have hx : InterpLang.absStore F σ x = some v := by
        simpa [InterpLang.absStore, hr, InterpLang.Denotes] using hv
      exact ⟨v :: vs, .cons hv hrel, by simp only [readVarList, hx, hvs, Option.map_some]⟩
    · cases h

variable [DecidableEq P.Ident]

/-- Positionally binding runtime values that denote `vs` stands for binding `vs`. -/
theorem absStore_bindPositional {F : P.Factory} :
    ∀ (σ : RStore P) (xs : List P.Ident) {rs : List P.Expr} {vs : List P.Val},
      List.Rel₂ (InterpLang.Denotes F) rs vs →
      InterpLang.absStore F (bindPositional σ xs rs) =
        bindPositional (InterpLang.absStore F σ) xs vs
  | _, [], _, _, .nil | _, [], _, _, .cons _ _ | _, _ :: _, _, _, .nil => rfl
  | σ, x :: xs, _, _, .cons hr h => by
    rw [bindPositional, bindPositional, absStore_bindPositional _ xs h]
    exact congrArg (bindPositional · xs _) (InterpLang.absStore_update σ x hr)

/-- Positionally binding denoting runtime values keeps a store denoting. -/
theorem denoting_bindPositional {F : P.Factory} :
    ∀ {σ : RStore P} (xs : List P.Ident) {rs : List P.Expr} {vs : List P.Val},
      RStore.Denoting F σ → List.Rel₂ (InterpLang.Denotes F) rs vs →
      RStore.Denoting F (bindPositional σ xs rs)
  | _, [], _, _, h, _ | _, _ :: _, _, _, h, .nil => h
  | _, x :: xs, _, _, h, .cons hr hs => denoting_bindPositional xs (h.update x hr) hs

variable [HasOldIdent P]

/-- The `old` snapshots of a runtime store stand for those of its image. -/
theorem absStore_withOldSnapshotsV {F : P.Factory} (s : List P.Ident) (σ : RStore P) :
    InterpLang.absStore F (withOldSnapshotsV s σ) =
      withOldSnapshotsV s (InterpLang.absStore F σ) := by
  funext x
  simp only [InterpLang.absStore, withOldSnapshotsV]
  split <;> rfl

/-- The callee frame built from runtime values that denote the input and output-only values
    stands for the frame built from those values, and denotes. -/
theorem callEntryStore_abs {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    {F : P.Factory} (p : Procedure P (CmdExt P) Hdr)
    {rs ros : List P.Expr} {vs vos : List P.Val} (h1 : List.Rel₂ (InterpLang.Denotes F) rs vs)
    (h2 : List.Rel₂ (InterpLang.Denotes F) ros vos) :
    InterpLang.absStore F (callEntryStore p rs ros) = callEntryStore p vs vos ∧
      RStore.Denoting F (callEntryStore p rs ros) := by
  refine ⟨?_, fun x r h => ?_⟩
  · rw [callEntryStore, absStore_withOldSnapshotsV, absStore_bindPositional _ _ h2,
      absStore_bindPositional _ _ h1]
    rfl
  · simp only [callEntryStore, withOldSnapshotsV] at h
    have h0 : RStore.Denoting F (fun _ : P.Ident => none) := fun _ _ h => by cases h
    have hd := denoting_bindPositional (outputOnlyParams (P := P) p.header)
      (denoting_bindPositional (ProcedureHeader.inputParams (P := P) p.header) h0 h1) h2
    split at h <;> exact hd _ _ h

end Calls
end
end Imperative

/-! ## Assertion-failure events -/

namespace Imperative
public section
namespace Calls
variable {P : PureExpr} [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]

/-- The halting predicate `assertFailureHalt` (the target assertion failing or the target cover
    reached) fires only on events matching the target's label and metadata
    (`targetReached`). -/
theorem targetReached_of_assertFailureHalt (target : AssertId P) (fuel : Nat)
    (ev : IEvent P) (h : assertFailureHalt target fuel ev = true) :
    targetReached target ev = true := by cases ev <;> simp_all!

end Calls
end
end Imperative

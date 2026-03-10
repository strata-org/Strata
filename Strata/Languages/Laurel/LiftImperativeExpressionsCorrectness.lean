/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Correctness of LiftImperativeExpressions — Phases 2 & 3

Bottom-up correctness proof for the lifting pass.
See `docs/designs/design-correctness-theorem-for-liftimperativeexpre.md`.

## Phase 2: Single Assignment in PrimitiveOp
## Phase 3: General PrimitiveOp with Multiple Assignments

## Design Reference

Option C (Phased bottom-up proof), Phases 2–3.
-/

namespace Strata.Laurel

/-! ## Phase 2: Single Assignment -/

theorem lift_single_assign_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old v_new result : LaurelValue)
    (hx_def : σ x = some v_old)
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_ext : ∀ σ', (∀ y, y ≠ snap → σ' y = σ y) →
      EvalLaurelStmt δ π h σ' e h σ' (.normal v_new))
    (hop : evalPrimOp op [v_old, v_new] = some result) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h σ_block (.normal result) := by
  let σ_snap : LaurelStore := fun y => if y == snap then some v_old else σ y
  let σ_final : LaurelStore := fun y => if y == x then some v_new else σ_snap y
  have h_snap_self : σ_snap snap = some v_old := by simp [σ_snap]
  have h_snap_x : σ_snap x = some v_old := by
    simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne, hx_def]
  have h_final_snap : σ_final snap = some v_old := by
    simp only [σ_final]; simp [beq_iff_eq, hne, h_snap_self]
  have h_final_x : σ_final x = some v_new := by simp [σ_final]
  have he_snap : EvalLaurelStmt δ π h σ_snap e h σ_snap (.normal v_new) := by
    apply he_ext; intro y hne'; simp only [σ_snap]; simp [beq_iff_eq, hne']
  have h_init : InitStore σ snap v_old σ_snap :=
    .init hfresh h_snap_self (fun y hne' => by
      simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne'])
  have h_upd : UpdateStore σ_snap x v_new σ_final :=
    .update (v' := v_old) h_snap_x h_final_x (fun y hne' => by
      simp only [σ_final]; simp [beq_iff_eq, Ne.symm hne'])
  exact ⟨σ_final, .cons_normal
    (.local_var_init (.identifier hx_def) hfresh h_init)
    (by simp)
    (.cons_normal
      (.assign_single he_snap h_snap_x h_upd)
      (by simp)
      (.last_normal
        (.prim_op
          (.cons (.identifier h_final_snap) (.cons (.identifier h_final_x) .nil))
          hop)))⟩

set_option maxHeartbeats 800000 in
theorem lift_single_assign_from_eval
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (h' : LaurelHeap) (σ' : LaurelStore) (result : LaurelValue)
    (v_new : LaurelValue)
    (heval : EvalLaurelStmt δ π h σ
      ⟨.PrimitiveOp op [⟨.Identifier x, md⟩,
                         ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩], md⟩
      h' σ' (.normal result))
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_pure : EvalLaurelStmt δ π h σ e h σ (.normal v_new))
    (he_ext : ∀ σ₀, (∀ y, y ≠ snap → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal v_new)) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h' σ_block (.normal result) := by
  cases heval with
  | prim_op hargs hop_eq =>
    cases hargs with
    | cons harg1 hrest =>
      cases hrest with
      | cons harg2 hnil =>
        cases hnil
        cases harg1 with
        | identifier hlookup =>
          cases harg2 with
          | assign_single heval_e _hexists hupdate =>
            have ⟨hh_eq, hσ_eq, hv_eq⟩ := EvalLaurelStmt_deterministic heval_e he_pure
            cases hv_eq; rw [hh_eq] at *; rw [hσ_eq] at *
            exact lift_single_assign_correct δ π _ _ op x snap e ty md tmd
              _ _ result hlookup hfresh hne he_ext hop_eq

/-! ## Phase 3: General PrimitiveOp with Multiple Assignments -/

/-- Specification of a single argument in a PrimitiveOp call. -/
inductive ArgSpec where
  | pure (ref : StmtExprMd) (val : LaurelValue)
  | assign (x snap : Identifier) (e : StmtExprMd) (ty : HighTypeMd) (val : LaurelValue)

def ArgSpec.value : ArgSpec → LaurelValue
  | .pure _ v => v
  | .assign _ _ _ _ v => v

def ArgSpec.cleanedArg (md : Imperative.MetaData Core.Expression) : ArgSpec → StmtExprMd
  | .pure ref _ => ref
  | .assign x _ _ _ _ => ⟨.Identifier x, md⟩

def ArgSpec.prepends (md tmd : Imperative.MetaData Core.Expression) : ArgSpec → List StmtExprMd
  | .pure _ _ => []
  | .assign x snap e ty _ =>
    [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
      ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩ ]

def allPrepends (md tmd : Imperative.MetaData Core.Expression) : List ArgSpec → List StmtExprMd
  | [] => []
  | a :: as => allPrepends md tmd as ++ a.prepends md tmd

def cleanedArgs (md : Imperative.MetaData Core.Expression) : List ArgSpec → List StmtExprMd
  | [] => []
  | a :: as => a.cleanedArg md :: cleanedArgs md as

def argValues : List ArgSpec → List LaurelValue
  | [] => []
  | a :: as => a.value :: argValues as

/-! ### Store Effect Model -/

def applyArgEffect (σ : LaurelStore) : ArgSpec → LaurelStore
  | .pure _ _ => σ
  | .assign x snap _ _ val =>
    fun y => if y == x then some val
             else if y == snap then σ x
             else σ y

/-- Thread store effects right-to-left: for `[a₁, ..., aₙ]`, apply aₙ first,
then aₙ₋₁, ..., then a₁. This matches the execution order of `allPrepends`. -/
def threadEffectsRL (σ : LaurelStore) : List ArgSpec → LaurelStore
  | [] => σ
  | a :: as => applyArgEffect (threadEffectsRL σ as) a

/-! ### Freshness Through Threading -/

theorem threadEffectsRL_preserves_none
    {σ : LaurelStore} {name : Identifier}
    (hfresh : σ name = none)
    (hne : ∀ spec ∈ specs, match spec with
      | .assign x snap _ _ _ => name ≠ x ∧ name ≠ snap
      | .pure _ _ => True) :
    threadEffectsRL σ specs name = none := by
  match specs with
  | [] => exact hfresh
  | (.pure _ _) :: rest =>
    simp only [threadEffectsRL, applyArgEffect]
    -- threadEffectsRL σ (pure :: rest) = applyArgEffect (threadEffectsRL σ rest) pure
    -- = threadEffectsRL σ rest (since pure is identity)
    exact threadEffectsRL_preserves_none hfresh
      (fun s hs => hne s (List.mem_cons_of_mem _ hs))
  | (.assign x snap e₀ ty₀ val₀) :: rest =>
    -- threadEffectsRL σ (assign :: rest) = applyArgEffect (threadEffectsRL σ rest) assign
    simp only [threadEffectsRL, applyArgEffect]
    have h_spec := hne (.assign x snap e₀ ty₀ val₀) List.mem_cons_self
    have hne_x := h_spec.1
    have hne_snap := h_spec.2
    simp [beq_iff_eq, hne_x, hne_snap]
    -- Now need: threadEffectsRL σ rest name = none
    -- But the goal after simp should be about (threadEffectsRL σ rest) x, not name
    -- Actually after simp [beq_iff_eq, hne_x, hne_snap], the if-then-else reduces
    -- and we need threadEffectsRL σ rest name = none
    exact threadEffectsRL_preserves_none hfresh
      (fun s hs => hne s (List.mem_cons_of_mem _ hs))

/-! ### Single Assignment Prepend Evaluation -/

theorem assign_prepends_eval
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (x snap : Identifier) (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old val : LaurelValue)
    (hx_def : σ x = some v_old)
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_eval : ∀ σ₀, (∀ y, y ≠ snap → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal val)) :
    EvalLaurelBlock δ π h σ
      (ArgSpec.prepends md tmd (ArgSpec.assign x snap e ty val))
      h (applyArgEffect σ (ArgSpec.assign x snap e ty val)) (.normal val) := by
  simp only [ArgSpec.prepends, applyArgEffect]
  -- The snapshot store: snap gets v_old (= σ x), everything else unchanged
  let σ_snap : LaurelStore := fun y => if y == snap then some v_old else σ y
  have h_snap_x : σ_snap x = some v_old := by
    simp [σ_snap, beq_iff_eq, Ne.symm hne, hx_def]
  have he_snap : EvalLaurelStmt δ π h σ_snap e h σ_snap (.normal val) :=
    he_eval σ_snap (fun y hne' => by simp [σ_snap, beq_iff_eq, hne'])
  have h_init : InitStore σ snap v_old σ_snap :=
    .init hfresh (by simp [σ_snap]) (fun y hne' => by
      simp [σ_snap, beq_iff_eq, Ne.symm hne'])
  -- The final store after assignment
  let σ_final : LaurelStore :=
    fun y => if y == x then some val else σ_snap y
  have hσ_final_x : σ_final x = some val := by simp [σ_final]
  have h_upd : UpdateStore σ_snap x val σ_final :=
    .update (v' := v_old) h_snap_x hσ_final_x
      (fun y hne' => by simp [σ_final, beq_iff_eq, Ne.symm hne'])
  -- σ_final = applyArgEffect result (the nested if-then-else)
  suffices h_eq : σ_final = fun y => if y == x then some val
      else if y == snap then σ x else σ y by
    rw [h_eq] at h_upd
    exact .cons_normal
      (.local_var_init (.identifier hx_def) hfresh h_init)
      (by simp)
      (.last_normal (.assign_single he_snap h_snap_x h_upd))
  funext y; simp only [σ_final, σ_snap]
  split
  · rfl
  · split
    · simp_all
    · rfl

/-! ### General Prepend Evaluation

Proof by structural recursion on the spec list. For `spec :: rest`:
1. Recursively evaluate prepends for `rest` (these execute first)
2. Evaluate prepends for `spec` in the resulting store
3. Compose via `EvalLaurelBlock_append` -/

/-- Inductive witness that a spec list is well-formed and each assignment
evaluates correctly. This avoids indexing and BEq issues. -/
inductive SpecsOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    Imperative.MetaData Core.Expression → Imperative.MetaData Core.Expression →
    List ArgSpec → Prop where
  | nil : SpecsOK δ π h σ md tmd []
  | cons_pure :
    SpecsOK δ π h σ md tmd rest →
    SpecsOK δ π h σ md tmd (ArgSpec.pure ref val :: rest)
  | cons_assign :
    SpecsOK δ π h σ md tmd rest →
    -- snap is fresh in σ and not affected by any spec in rest
    (σ snap = none) →
    (∀ spec ∈ rest, match spec with
      | .assign x' snap' _ _ _ => snap ≠ x' ∧ snap ≠ snap'
      | .pure _ _ => True) →
    (snap ≠ x) →
    -- target is defined after threading rest
    ((threadEffectsRL σ rest x).isSome) →
    -- e evaluates purely in the store after threading rest
    (∀ σ₀, (∀ y, y ≠ snap → σ₀ y = threadEffectsRL σ rest y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal val)) →
    SpecsOK δ π h σ md tmd (ArgSpec.assign x snap e ty val :: rest)

theorem allPrepends_eval
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {md tmd : Imperative.MetaData Core.Expression}
    {specs : List ArgSpec}
    (hok : SpecsOK δ π h σ md tmd specs) :
    ∃ v, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs)
      h (threadEffectsRL σ specs) (.normal v) := by
  match hok with
  | .nil => exact ⟨.vVoid, .nil⟩
  | .cons_pure hrest =>
    simp only [allPrepends, ArgSpec.prepends, List.append_nil, threadEffectsRL, applyArgEffect]
    exact allPrepends_eval hrest
  | .cons_assign (rest := rest) (x := x) (snap := snap) (e := e) (ty := ty) (val := val)
      hrest hfresh_σ hfresh_rest hne htarget_def he_eval =>
    -- Recursively evaluate prepends for rest
    have ⟨v_rest, hrest_eval⟩ := allPrepends_eval hrest
    simp only [allPrepends, threadEffectsRL]
    let σ_rest := threadEffectsRL σ rest
    -- snap is fresh in σ_rest
    have hsnap_fresh : σ_rest snap = none := by
      apply threadEffectsRL_preserves_none hfresh_σ
      intro spec hmem
      exact hfresh_rest spec hmem
    -- target is defined in σ_rest
    obtain ⟨v_old, hx_def⟩ := Option.isSome_iff_exists.mp htarget_def
    -- Evaluate the assignment prepends
    have hassign := assign_prepends_eval δ π h σ_rest x snap e ty md tmd
      v_old val hx_def hsnap_fresh hne he_eval
    -- Compose
    exact ⟨_, EvalLaurelBlock_append hrest_eval (by simp [ArgSpec.prepends]) hassign⟩

/-! ### Main Phase 3 Theorem -/

/-- General Phase 3 theorem: the lifted block (prepended statements followed
by the cleaned PrimitiveOp) evaluates to the same result as the original. -/
theorem lift_multi_assign_correct
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {op : Operation} {specs : List ArgSpec}
    {md tmd : Imperative.MetaData Core.Expression}
    {result : LaurelValue}
    (hok : SpecsOK δ π h σ md tmd specs)
    -- The cleaned args evaluate to the right values in the final store
    (hargs_eval : EvalStmtArgs δ π h (threadEffectsRL σ specs)
      (cleanedArgs md specs) h (threadEffectsRL σ specs) (argValues specs))
    (hop : evalPrimOp op (argValues specs) = some result) :
    ∃ σ_final, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs ++ [⟨.PrimitiveOp op (cleanedArgs md specs), md⟩])
      h σ_final (.normal result) := by
  have ⟨_, hprep⟩ := allPrepends_eval hok
  exact ⟨threadEffectsRL σ specs,
    EvalLaurelBlock_append_singleton hprep (.prim_op hargs_eval hop)⟩

end Strata.Laurel

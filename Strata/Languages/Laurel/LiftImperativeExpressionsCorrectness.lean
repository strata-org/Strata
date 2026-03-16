/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Correctness of LiftImperativeExpressions — Phases 2–4

Bottom-up correctness proof for the lifting pass.
See `docs/designs/design-correctness-theorem-for-liftimperativeexpre.md`.

## Phase 2: Single Assignment in PrimitiveOp
## Phase 3: General PrimitiveOp with Multiple Assignments
## Phase 4: Statement-level transformStmt

## Design Reference

Option C (Phased bottom-up proof), Phases 2–4.
-/

namespace Strata.Laurel

/-! ## Phase 2: Single Assignment -/

theorem lift_single_assign_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old v_new result : LaurelValue)
    (hx_def : σ x.text = some v_old)
    (hfresh : σ snap.text = none)
    (hne : snap.text ≠ x.text)
    (he_ext : ∀ σ', (∀ y, y ≠ snap.text → σ' y = σ y) →
      EvalLaurelStmt δ π h σ' e h σ' (.normal v_new))
    (hop : evalPrimOp op [v_old, v_new] = some result) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h σ_block (.normal result) := by
  let σ_snap : LaurelStore := fun y => if y == snap.text then some v_old else σ y
  let σ_final : LaurelStore := fun y => if y == x.text then some v_new else σ_snap y
  have h_snap_self : σ_snap snap.text = some v_old := by simp [σ_snap]
  have h_snap_x : σ_snap x.text = some v_old := by
    simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne, hx_def]
  have h_final_snap : σ_final snap.text = some v_old := by
    simp only [σ_final]; simp [beq_iff_eq, hne, h_snap_self]
  have h_final_x : σ_final x.text = some v_new := by simp [σ_final]
  have he_snap : EvalLaurelStmt δ π h σ_snap e h σ_snap (.normal v_new) := by
    apply he_ext; intro y hne'; simp only [σ_snap]; simp [beq_iff_eq, hne']
  have h_init : InitStore σ snap.text v_old σ_snap :=
    .init hfresh h_snap_self (fun y hne' => by
      simp only [σ_snap]; simp [beq_iff_eq, Ne.symm hne'])
  have h_upd : UpdateStore σ_snap x.text v_new σ_final :=
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
    (hfresh : σ snap.text = none)
    (hne : snap.text ≠ x.text)
    (he_pure : EvalLaurelStmt δ π h σ e h σ (.normal v_new))
    (he_ext : ∀ σ₀, (∀ y, y ≠ snap.text → σ₀ y = σ y) →
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
    fun y => if y == x.text then some val
             else if y == snap.text then σ x.text
             else σ y

/-- Thread store effects right-to-left: for `[a₁, ..., aₙ]`, apply aₙ first,
then aₙ₋₁, ..., then a₁. This matches the execution order of `allPrepends`. -/
def threadEffectsRL (σ : LaurelStore) : List ArgSpec → LaurelStore
  | [] => σ
  | a :: as => applyArgEffect (threadEffectsRL σ as) a

/-! ### Freshness Through Threading -/

theorem threadEffectsRL_preserves_none
    {σ : LaurelStore} {name : Identifier}
    (hfresh : σ name.text = none)
    (hne : ∀ spec ∈ specs, match spec with
      | .assign x snap _ _ _ => name.text ≠ x.text ∧ name.text ≠ snap.text
      | .pure _ _ => True) :
    threadEffectsRL σ specs name.text = none := by
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
    (hx_def : σ x.text = some v_old)
    (hfresh : σ snap.text = none)
    (hne : snap.text ≠ x.text)
    (he_eval : ∀ σ₀, (∀ y, y ≠ snap.text → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal val)) :
    EvalLaurelBlock δ π h σ
      (ArgSpec.prepends md tmd (ArgSpec.assign x snap e ty val))
      h (applyArgEffect σ (ArgSpec.assign x snap e ty val)) (.normal val) := by
  simp only [ArgSpec.prepends, applyArgEffect]
  -- The snapshot store: snap gets v_old (= σ x), everything else unchanged
  let σ_snap : LaurelStore := fun y => if y == snap.text then some v_old else σ y
  have h_snap_x : σ_snap x.text = some v_old := by
    simp [σ_snap, hne, hx_def]
  have he_snap : EvalLaurelStmt δ π h σ_snap e h σ_snap (.normal val) :=
    he_eval σ_snap (fun y hne' => by simp [σ_snap, beq_iff_eq, hne'])
  have h_init : InitStore σ snap.text v_old σ_snap :=
    .init hfresh (by simp [σ_snap]) (fun y hne' => by
      simp [σ_snap, beq_iff_eq, Ne.symm hne'])
  -- The final store after assignment
  let σ_final : LaurelStore :=
    fun y => if y == x.text then some val else σ_snap y
  have hσ_final_x : σ_final x.text = some val := by simp [σ_final]
  have h_upd : UpdateStore σ_snap x.text val σ_final :=
    .update (v' := v_old) h_snap_x hσ_final_x
      (fun y hne' => by simp [σ_final, beq_iff_eq, Ne.symm hne'])
  -- σ_final = applyArgEffect result (the nested if-then-else)
  suffices h_eq : σ_final = fun y => if y == x.text then some val
      else if y == snap.text then σ x.text else σ y by
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
    (σ snap.text = none) →
    (∀ spec ∈ rest, match spec with
      | .assign x' snap' _ _ _ => snap.text ≠ x'.text ∧ snap.text ≠ snap'.text
      | .pure _ _ => True) →
    (snap.text ≠ x.text) →
    -- target is defined after threading rest
    ((threadEffectsRL σ rest x.text).isSome) →
    -- e evaluates purely in the store after threading rest
    (∀ σ₀, (∀ y, y ≠ snap.text → σ₀ y = threadEffectsRL σ rest y) →
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
    have hsnap_fresh : σ_rest snap.text = none := by
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

/-! ## Phase 4: Statement-level transformStmt

These theorems show that `transformStmt` preserves semantics for each
statement construct. The approach: if the original statement evaluates
to some result, and the transformation output is `prepends ++ [s']`,
then the output block evaluates to the same result (modulo store
extension with snapshot variables).

### 4.1 Identity cases

For statements where `transformStmt` returns `[stmt]` unchanged
(Return, Exit, Assert, Assume, literals, etc.), preservation is immediate.
-/

/-- A singleton block `[s]` evaluates to the same result as `s`. -/
theorem stmt_to_block
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o) :
    EvalLaurelBlock δ π h σ [s] h' σ' o := by
  cases o with
  | normal v => exact .last_normal heval
  | exit l => exact .cons_exit heval
  | ret rv => exact .cons_return heval

/-- Identity-case correctness: for statements where `transformStmt` returns
`[stmt]` unchanged (Return, Exit, Assert, Assume, and other pass-through
cases in the `| _ => return [stmt]` branch), the transformed singleton
block evaluates to the same result as the original statement. -/
theorem transformStmt_identity_correct
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o) :
    EvalLaurelBlock δ π h σ [s] h' σ' o :=
  stmt_to_block heval

/-! ### 4.2 Prepend composition for statements

When `transformStmt` produces `prepends ++ [s']`, the prepends come from
`transformExpr` on sub-expressions. If the prepends evaluate normally
(setting up the store for the cleaned expression), and the cleaned
statement evaluates in the resulting store, the whole block evaluates
correctly.

This is a direct application of `EvalLaurelBlock_append_singleton`.

Note: These theorems are structural composition lemmas — they show that
`prepends ++ [s']` evaluates correctly given that prepends evaluate normally
and `s'` evaluates in the resulting store. They do *not* connect to the
actual monadic output of `transformStmt`; that connection is deferred to
the end-to-end correctness theorem. In particular, they hold for any
`prepends` that evaluate normally, regardless of whether those prepends
are semantically related to the original expression.
-/

/-- Generic prepend composition: if prepends evaluate normally and the
statement evaluates in the resulting store, then `prepends ++ [s]`
evaluates correctly. The per-statement theorems below are specializations. -/
theorem transformStmt_prepend_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {prepends : List StmtExprMd} {s : StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hstmt : EvalLaurelStmt δ π h₁ σ₁ s h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (prepends ++ [s]) h₂ σ₂ o :=
  EvalLaurelBlock_append_singleton hprep hstmt

/-- Assign correctness: specialization of `transformStmt_prepend_correct`. -/
abbrev transformStmt_assign_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {prepends : List StmtExprMd}
    {targets : List StmtExprMd} {seqValue : StmtExprMd}
    {md : Imperative.MetaData Core.Expression}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hassign : EvalLaurelStmt δ π h₁ σ₁ ⟨.Assign targets seqValue, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (prepends ++ [⟨.Assign targets seqValue, md⟩]) h₂ σ₂ o :=
  transformStmt_prepend_correct hprep hassign

/-- LocalVariable correctness: specialization of `transformStmt_prepend_correct`. -/
abbrev transformStmt_local_var_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {prepends : List StmtExprMd}
    {name : Identifier} {ty : HighTypeMd} {seqInit : StmtExprMd}
    {md : Imperative.MetaData Core.Expression}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hlocal : EvalLaurelStmt δ π h₁ σ₁ ⟨.LocalVariable name ty (some seqInit), md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (prepends ++ [⟨.LocalVariable name ty (some seqInit), md⟩]) h₂ σ₂ o :=
  transformStmt_prepend_correct hprep hlocal

/-! ### 4.3 IfThenElse correctness

`transformStmt` on `IfThenElse cond thenBr elseBr` produces:
  `condPrepends ++ [IfThenElse seqCond seqThen seqElse]`

where `condPrepends` come from `transformExpr cond`, and `seqThen`/`seqElse`
are blocks wrapping the recursively transformed branches.
-/

/-- IfThenElse correctness: specialization of `transformStmt_prepend_correct`. -/
abbrev transformStmt_ite_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {condPrepends : List StmtExprMd}
    {seqCond seqThen : StmtExprMd} {seqElse : Option StmtExprMd}
    {md : Imperative.MetaData Core.Expression}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ condPrepends h₁ σ₁ (.normal v₁))
    (hite : EvalLaurelStmt δ π h₁ σ₁ ⟨.IfThenElse seqCond seqThen seqElse, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (condPrepends ++ [⟨.IfThenElse seqCond seqThen seqElse, md⟩]) h₂ σ₂ o :=
  transformStmt_prepend_correct hprep hite

/-! ### 4.4 While correctness

`transformStmt` on `While cond invs dec body` produces:
  `condPrepends ++ [While seqCond invs dec seqBody]`

Note: This is a structural composition lemma. It does *not* claim that
`seqCond` is semantically equivalent to the original `cond` on each loop
iteration. The condition prepends are evaluated once before the loop,
while the `while_true` rule re-evaluates `seqCond` on each iteration.
This is correct for the lifting pass (which only lifts pure snapshot
operations whose values don't change across iterations), but the
distinction is subtle — callers must ensure that the prepends only
capture values that are loop-invariant.
-/

/-- While correctness: specialization of `transformStmt_prepend_correct`. -/
abbrev transformStmt_while_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {condPrepends : List StmtExprMd}
    {seqCond : StmtExprMd} {invs : List StmtExprMd}
    {dec : Option StmtExprMd} {seqBody : StmtExprMd}
    {md : Imperative.MetaData Core.Expression}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ condPrepends h₁ σ₁ (.normal v₁))
    (hwhile : EvalLaurelStmt δ π h₁ σ₁ ⟨.While seqCond invs dec seqBody, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (condPrepends ++ [⟨.While seqCond invs dec seqBody, md⟩]) h₂ σ₂ o :=
  transformStmt_prepend_correct hprep hwhile

/-! ### 4.5 StaticCall correctness

`transformStmt` on `StaticCall name args` produces:
  `prepends ++ [StaticCall name seqArgs]`
-/

/-- StaticCall correctness: specialization of `transformStmt_prepend_correct`. -/
abbrev transformStmt_static_call_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {prepends : List StmtExprMd}
    {name : Identifier} {seqArgs : List StmtExprMd}
    {md : Imperative.MetaData Core.Expression}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hcall : EvalLaurelStmt δ π h₁ σ₁ ⟨.StaticCall name seqArgs, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (prepends ++ [⟨.StaticCall name seqArgs, md⟩]) h₂ σ₂ o :=
  transformStmt_prepend_correct hprep hcall

/-! ### 4.6 Block correctness

`transformStmt` on `Block stmts label` maps `transformStmt` over each
statement and wraps the result in a new Block. The proof uses induction
on the statement list.
-/

/-- Block correctness: if the original block evaluates to some result,
and the transformed block (with each statement mapped through transformStmt)
evaluates to the same result, then the Block wrapper preserves semantics.

The key insight: `transformStmt` on a Block produces
`[Block (stmts.mapM transformStmt).flatten label]`. The Block wrapper
applies `catchExit`, which is preserved since the inner block evaluates
to the same outcome. -/
theorem transformStmt_block_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {stmts_flat : List StmtExprMd}
    {label : Option String}
    {md : Imperative.MetaData Core.Expression}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (hinner : EvalLaurelBlock δ π h σ stmts_flat h' σ' o)
    (hcatch : catchExit label o = o') :
    EvalLaurelBlock δ π h σ
      [⟨.Block stmts_flat label, md⟩] h' σ' o' := by
  exact stmt_to_block (.block_sem hinner hcatch)

/-! ### 4.7 Composing block evaluation from per-statement results

This is the inductive core of the block case: if we have a list of
statements where each `sᵢ` has been transformed into `stmtsᵢ`, and
the original block `[s₁, ..., sₙ]` evaluates to some result, then
the flattened block `stmts₁ ++ ... ++ stmtsₙ` evaluates to the same
result (modulo store extension).

We prove this by showing that if each transformed sub-block preserves
the semantics of its source statement, then the concatenation preserves
the semantics of the whole block.
-/

/-- Cons composition for transformed blocks: if the first statement's
transformation evaluates correctly (producing normal outcome), and the
rest of the transformed block evaluates correctly, then the concatenation
evaluates correctly. -/
theorem transformed_block_cons_normal
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h₁ σ₁ (.normal v₁))
    (hne : stmts_rest ≠ [])
    (hrest : EvalLaurelBlock δ π h₁ σ₁ stmts_rest h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h₂ σ₂ o :=
  EvalLaurelBlock_append hfirst hne hrest

/-- Cons composition for transformed blocks with exit outcome:
if the first statement's transformation produces an exit, the rest
is skipped. -/
theorem transformed_block_cons_exit
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {label : String}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h' σ' (.exit label)) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h' σ' (.exit label) := by
  match hfirst with
  | .cons_exit hs => exact .cons_exit hs
  | .cons_normal hs hne hrest =>
    simp only [List.cons_append]
    exact .cons_normal hs (by simp [List.append_eq_nil_iff, hne])
      (transformed_block_cons_exit hrest)

/-- Cons composition for transformed blocks with return outcome:
if the first statement's transformation produces a return, the rest
is skipped. -/
theorem transformed_block_cons_return
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {rv : Option LaurelValue}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h' σ' (.ret rv)) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h' σ' (.ret rv) := by
  match hfirst with
  | .cons_return hs => exact .cons_return hs
  | .cons_normal hs hne hrest =>
    simp only [List.cons_append]
    exact .cons_normal hs (by simp [List.append_eq_nil_iff, hne])
      (transformed_block_cons_return hrest)

/-! ### 4.8 General composition theorem

The main Phase 4 composition: given a list of (source statement, transformed
statements) pairs where each transformation preserves semantics, the
concatenation of all transformed statements preserves the semantics of
the original block.
-/

/-- Inductive witness that a list of statement transformations preserves
semantics. Each entry says: "if the source statement evaluates to some
result in the given state, then the transformed statements evaluate to
the same result (modulo store extension)."

Key invariant: `stmts_rest` is always non-empty when `rest` is non-empty,
because each statement transforms to at least one statement.

TODO: In `cons_normal`, the source produces `_v` and the target produces
`_v'` — these are independent. This means `TransformOK` does not require
intermediate normal values to agree, only that the final (heap, store,
outcome) match. This is sufficient for `TransformOK_eval` (since
`EvalLaurelBlock_append` only needs *some* normal value), but it weakens
`TransformOK` as a specification of semantic preservation. A stronger
version could require `_v = _v'` in `cons_normal`. -/
inductive TransformOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → List StmtExprMd →
    LaurelHeap → LaurelStore → Outcome → Prop where
  /-- Empty block: both source and target are empty. -/
  | nil :
    TransformOK δ π h σ [] [] h σ (.normal .vVoid)
  /-- Last statement (normal): source `[s]` transforms to `stmts₁` with
  the same final state and outcome. -/
  | last_normal :
    EvalLaurelStmt δ π h σ s h' σ' (.normal v) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.normal v) →
    TransformOK δ π h σ [s] stmts₁ h' σ' (.normal v)
  /-- Last statement (exit): singleton source exits, target block exits. -/
  | last_exit :
    EvalLaurelStmt δ π h σ s h' σ' (.exit label) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.exit label) →
    TransformOK δ π h σ [s] stmts₁ h' σ' (.exit label)
  /-- Last statement (return): singleton source returns, target block returns. -/
  | last_return :
    EvalLaurelStmt δ π h σ s h' σ' (.ret rv) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.ret rv) →
    TransformOK δ π h σ [s] stmts₁ h' σ' (.ret rv)
  /-- Cons (normal): first statement evaluates normally, rest follows.
  Requires `stmts_rest ≠ []` to ensure well-formed append. -/
  | cons_normal :
    EvalLaurelStmt δ π h σ s h₁ σ₁ (.normal _v) →
    EvalLaurelBlock δ π h σ stmts₁ h₁ σ₁ (.normal _v') →
    rest ≠ [] →
    stmts_rest ≠ [] →
    TransformOK δ π h₁ σ₁ rest stmts_rest h₂ σ₂ o →
    TransformOK δ π h σ (s :: rest) (stmts₁ ++ stmts_rest) h₂ σ₂ o
  /-- Cons (exit): first statement exits, rest is skipped. -/
  | cons_exit :
    EvalLaurelStmt δ π h σ s h' σ' (.exit label) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.exit label) →
    TransformOK δ π h σ (s :: _rest) (stmts₁ ++ _stmts_rest) h' σ' (.exit label)
  /-- Cons (return): first statement returns, rest is skipped. -/
  | cons_return :
    EvalLaurelStmt δ π h σ s h' σ' (.ret rv) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.ret rv) →
    TransformOK δ π h σ (s :: _rest) (stmts₁ ++ _stmts_rest) h' σ' (.ret rv)

/-- If `TransformOK` holds, the target block evaluates correctly. -/
theorem TransformOK_eval
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {src tgt : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (htok : TransformOK δ π h σ src tgt h' σ' o) :
    EvalLaurelBlock δ π h σ tgt h' σ' o := by
  match htok with
  | .nil => exact .nil
  | .last_normal _ htgt => exact htgt
  | .last_exit _ htgt => exact htgt
  | .last_return _ htgt => exact htgt
  | .cons_normal _ hfirst _ hne_rest hrest =>
    exact EvalLaurelBlock_append hfirst hne_rest (TransformOK_eval hrest)
  | .cons_exit _ hfirst => exact transformed_block_cons_exit hfirst
  | .cons_return _ hfirst => exact transformed_block_cons_return hfirst

end Strata.Laurel

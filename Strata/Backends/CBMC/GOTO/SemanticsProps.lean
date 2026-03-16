/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Semantics

/-!
# Properties of GOTO Semantics

Determinism, store properties, and structural lemmas for the GOTO
operational semantics defined in `Semantics.lean`.

## Status

### Completed
- Store operation lemmas (update idempotence, commutativity, etc.)
- Determinism of `StepInstr` for deterministic evaluators (excluding `assign_nondet`)
- Additional reachability lemmas

### TODO
- [ ] Determinism of `ExecProg` (requires induction on derivation depth)
- [ ] Progress: well-formed programs always step or are at END_FUNCTION
- [ ] Store monotonicity: DECL only adds, DEAD only removes
-/

namespace CProverGOTO.Semantics

/-! ## Store Operation Lemmas -/

@[simp] theorem Store.update_same (σ : Store) (name : String) (v : Value) :
    (σ.update name v) name = some v := by
  simp [Store.update]

theorem Store.update_other (σ : Store) (name name' : String) (v : Value)
    (h : name' ≠ name) :
    (σ.update name v) name' = σ name' := by
  simp [Store.update]
  intro heq; exact absurd heq h

@[simp] theorem Store.declare_same (σ : Store) (name : String) :
    (σ.declare name) name = some .vEmpty := by
  simp [Store.declare]

theorem Store.declare_other (σ : Store) (name name' : String)
    (h : name' ≠ name) :
    (σ.declare name) name' = σ name' := by
  simp [Store.declare]
  intro heq; exact absurd heq h

@[simp] theorem Store.kill_same (σ : Store) (name : String) :
    (σ.kill name) name = none := by
  simp [Store.kill]

theorem Store.kill_other (σ : Store) (name name' : String)
    (h : name' ≠ name) :
    (σ.kill name) name' = σ name' := by
  simp [Store.kill]
  intro heq; exact absurd heq h

@[simp] theorem Store.update_update (σ : Store) (name : String) (v₁ v₂ : Value) :
    (σ.update name v₁).update name v₂ = σ.update name v₂ := by
  funext x; simp [Store.update]; split <;> simp_all

/-! ## Determinism -/

/-- A deterministic expression evaluator. -/
def DeterministicEval (eval : ExprEval) : Prop :=
  ∀ σ e v₁ v₂, eval σ e = some v₁ → eval σ e = some v₂ → v₁ = v₂

/-- A deterministic call relation. -/
def DeterministicCall (callResult : CallResultRel) : Prop :=
  ∀ eval fenv name σ σ₁ σ₂ r₁ r₂,
    callResult eval fenv name σ σ₁ r₁ →
    callResult eval fenv name σ σ₂ r₂ →
    σ₁ = σ₂ ∧ r₁ = r₂

/-- `StepInstr` is deterministic for deterministic evaluators, when
    `assign_nondet` is not present (no havoc instructions).

    Programs produced by Strata's translation use `assign_nondet` only for
    `havoc` commands; for programs without `havoc`, this gives full determinism. -/
theorem StepInstr_deterministic_no_nondet
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc₁ pc₂ : Nat} {σ σ₁ σ₂ : Store}
    (_heval : DeterministicEval eval)
    (hcall : DeterministicCall callResult)
    (hno_nondet : ∀ rhs, (instrCode prog pc).bind getAssignRhs = some rhs →
                          rhs.id ≠ .side_effect .Nondet) :
    StepInstr callResult eval fenv prog pc σ pc₁ σ₁ →
    StepInstr callResult eval fenv prog pc σ pc₂ σ₂ →
    pc₁ = pc₂ ∧ σ₁ = σ₂ := by
  intro h1 h2
  cases h1 <;> cases h2 <;> simp_all
  -- After simp_all: only function_call × function_call remains.
  -- The context has two callResult hypotheses with unified callee names.
  next _ hcr1 hσ1 _ _ hcr2 hσ2 =>
    have ⟨hσeq, hreq⟩ := hcall _ _ _ _ _ _ _ _ hcr1 hcr2
    subst hσeq; subst hreq; simp_all

/-! ## Reachability Lemmas -/

/-- A single step is reachable. -/
theorem reachable_single
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    Reachable callResult eval fenv prog pc σ pc' σ' :=
  fun h => .step h .refl

/-- If a program is safe and we can reach `pc, σ`, then the assertion
    at `pc` (if any) does not fail. -/
theorem safe_no_assert_fail
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {σ₀ σ : Store} {pc : Nat} :
    ProgramSafe callResult eval fenv prog σ₀ →
    Reachable callResult eval fenv prog 0 σ₀ pc σ →
    ¬ AssertFails eval prog pc σ :=
  fun hsafe hreach => hsafe pc σ hreach

/-! ## ExecProg Properties -/

/-- An empty program (no instructions) halts immediately. -/
theorem exec_empty_prog
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {σ : Store} :
    ExecProg callResult eval fenv { instructions := #[] } 0 σ σ none :=
  .out_of_bounds (by simp)

end CProverGOTO.Semantics

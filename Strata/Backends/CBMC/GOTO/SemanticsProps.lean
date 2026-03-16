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
- Determinism of `ExecProg` for nondet-free programs (`ExecProg_deterministic`)
- Per-instruction-type progress lemmas (`progress_skip`, `progress_assign`, etc.)
- Composite well-formed program progress (`progress_wellformed`)
- Additional reachability lemmas

### TODO
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

/-- If `instrType` returns `some`, the PC is in bounds. -/
theorem instrType_some_lt {prog : Program} {pc : Nat} {ty : InstructionType} :
    instrType prog pc = some ty → pc < prog.instructions.size := by
  simp only [instrType]
  intro h
  exact Decidable.byContradiction fun hge => by
    simp only [Nat.not_lt] at hge
    simp [Array.getElem?_eq_none hge] at h

/-- ExecProg determinism for programs without nondet, given deterministic
    eval and call relations. -/
def NoNondet (prog : Program) : Prop :=
  ∀ pc, ∀ rhs, (instrCode prog pc).bind getAssignRhs = some rhs →
               rhs.id ≠ .side_effect .Nondet

theorem ExecProg_deterministic
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ σ₁ σ₂ : Store}
    {r₁ r₂ : Option Value}
    (_heval : DeterministicEval eval)
    (hcall : DeterministicCall callResult)
    (hnn : NoNondet prog) :
    ExecProg callResult eval fenv prog pc σ σ₁ r₁ →
    ExecProg callResult eval fenv prog pc σ σ₂ r₂ →
    σ₁ = σ₂ ∧ r₁ = r₂ := by
  intro h1 h2
  induction h1 generalizing σ₂ r₂ with
  | out_of_bounds hge =>
    cases h2 with
    | out_of_bounds => exact ⟨rfl, rfl⟩
    | end_function hty => have := instrType_some_lt hty; omega
    | set_return_value hty => have := instrType_some_lt hty; omega
    | step hstep => cases hstep <;> (simp_all [instrType]; try (split at * <;> simp_all <;> omega))
  | end_function hty =>
    cases h2 with
    | out_of_bounds hge => have := instrType_some_lt hty; omega
    | end_function => exact ⟨rfl, rfl⟩
    | set_return_value hty2 => simp_all
    | step hstep => cases hstep <;> simp_all
  | set_return_value hty hcode hev hcont ih =>
    cases h2 with
    | out_of_bounds hge => have := instrType_some_lt hty; omega
    | end_function hty2 => simp_all
    | set_return_value hty2 hcode2 hev2 hcont2 =>
      have heq := Option.some.inj (hcode.symm.trans hcode2)
      subst heq
      have ⟨hσ, hr⟩ := ih hcont2
      exact ⟨hσ, by simp_all⟩
    | step hstep => cases hstep <;> simp_all
  | step hstep1 _hcont1 ih =>
    cases h2 with
    | out_of_bounds hge => cases hstep1 <;> (simp_all [instrType]; try (split at * <;> simp_all <;> omega))
    | end_function hty2 => cases hstep1 <;> simp_all
    | set_return_value hty2 => cases hstep1 <;> simp_all
    | step hstep2 hcont2 =>
      have ⟨hpc, hσ⟩ := StepInstr_deterministic_no_nondet _heval hcall (hnn _) hstep1 hstep2
      subst hpc; subst hσ; exact ih hcont2

/-! ## Progress -/

/-- An instruction at `pc` is a terminator (END_FUNCTION or SET_RETURN_VALUE). -/
def IsTerminator (prog : Program) (pc : Nat) : Prop :=
  instrType prog pc = some .END_FUNCTION ∨
  instrType prog pc = some .SET_RETURN_VALUE

/-- An ASSUME instruction at `pc` blocks (guard is false). -/
def AssumeBlocks (eval : ExprEval) (prog : Program) (pc : Nat) (σ : Store) : Prop :=
  instrType prog pc = some .ASSUME ∧
  (instrGuard prog pc).bind (eval σ ·) = some (.vBool false)

/-- The instruction types that Strata's translation produces. -/
def IsSupportedInstrType (ty : InstructionType) : Prop :=
  ty = .SKIP ∨ ty = .LOCATION ∨ ty = .ASSIGN ∨ ty = .DECL ∨ ty = .DEAD ∨
  ty = .GOTO ∨ ty = .ASSUME ∨ ty = .ASSERT ∨ ty = .FUNCTION_CALL ∨
  ty = .END_FUNCTION ∨ ty = .SET_RETURN_VALUE

/-- Progress for SKIP and LOCATION: always step. -/
theorem progress_skip
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .SKIP) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' :=
  ⟨pc + 1, σ, .skip hty⟩

theorem progress_location
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .LOCATION) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' :=
  ⟨pc + 1, σ, .location hty⟩

/-- Progress for DECL: always steps if the code has a symbol name. -/
theorem progress_decl
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .DECL)
    (hcode : ∃ name, (instrCode prog pc).bind getSymbolName = some name) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hcode
  exact ⟨pc + 1, σ.declare name, .decl hty hname⟩

/-- Progress for DEAD: always steps if the code has a symbol name. -/
theorem progress_dead
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .DEAD)
    (hcode : ∃ name, (instrCode prog pc).bind getSymbolName = some name) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hcode
  exact ⟨pc + 1, σ.kill name, .dead hty hname⟩

/-- Progress for ASSIGN: steps if the rhs evaluates (or is nondet). -/
theorem progress_assign
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .ASSIGN)
    (hlhs : ∃ name, (instrCode prog pc).bind getAssignLhs = some name)
    (hrhs : ∃ rhs, (instrCode prog pc).bind getAssignRhs = some rhs)
    -- Either rhs evaluates or is nondet
    (heval_or_nondet : ∀ rhs, (instrCode prog pc).bind getAssignRhs = some rhs →
      (∃ v, eval σ rhs = some v) ∨ rhs.id = .side_effect .Nondet) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hlhs
  obtain ⟨rhs, hrhs_eq⟩ := hrhs
  cases heval_or_nondet rhs hrhs_eq with
  | inl hev =>
    obtain ⟨v, hv⟩ := hev
    exact ⟨pc + 1, σ.update name v, .assign hty hname hrhs_eq hv⟩
  | inr hnd =>
    exact ⟨pc + 1, σ.update name .vEmpty, .assign_nondet hty hname hrhs_eq hnd⟩

/-- Progress for ASSERT: always steps (pass or fail) if guard evaluates to bool. -/
theorem progress_assert
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .ASSERT)
    (hguard : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b)) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨b, hb⟩ := hguard
  cases b with
  | true => exact ⟨pc + 1, σ, .assert_pass hty hb⟩
  | false => exact ⟨pc + 1, σ, .assert_fail hty hb⟩

/-- Progress for ASSUME: steps if guard is true, blocks if false. -/
theorem progress_assume
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .ASSUME)
    (hguard : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b)) :
    (∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ') ∨
    AssumeBlocks eval prog pc σ := by
  obtain ⟨b, hb⟩ := hguard
  cases b with
  | true => left; exact ⟨pc + 1, σ, .assume_pass hty hb⟩
  | false => right; exact ⟨hty, hb⟩

/-- Progress for GOTO: steps if guard evaluates to bool and target resolves. -/
theorem progress_goto
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .GOTO)
    (hguard : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b))
    -- Well-formed GOTO has a target
    (htgt_exists : ∃ tgt, instrTarget prog pc = some (some tgt))
    (htgt_resolves : ∀ tgt, instrTarget prog pc = some (some tgt) →
            ∃ idx, findLocIdx prog.instructions tgt = some idx) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨b, hb⟩ := hguard
  cases b with
  | false => exact ⟨pc + 1, σ, .goto_not_taken hty hb⟩
  | true =>
    obtain ⟨tgt, htgt⟩ := htgt_exists
    obtain ⟨idx, hidx⟩ := htgt_resolves tgt htgt
    exact ⟨idx, σ, .goto_taken hty htgt hb hidx⟩

/-- Progress for FUNCTION_CALL: steps if callee resolves. -/
theorem progress_function_call
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .FUNCTION_CALL)
    (hcallee : ∃ name, (instrCode prog pc).bind getCallCallee = some name)
    (hcall : ∀ name, (instrCode prog pc).bind getCallCallee = some name →
             ∃ σ' rv, callResult eval fenv name σ σ' rv) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hcallee
  obtain ⟨σ', rv, hcr⟩ := hcall name hname
  exact ⟨pc + 1, _, .function_call hty hname hcr rfl⟩

/-- Well-formed program progress: if the PC is in bounds and the instruction
    is not a terminator, then either execution steps or ASSUME blocks.

    A program is "well-formed" if:
    - Guards evaluate to booleans
    - ASSIGN has valid lhs/rhs
    - DECL/DEAD have symbol names
    - GOTO targets resolve
    - Function calls resolve

    This composes the per-instruction progress lemmas above. -/
theorem progress_wellformed
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hbound : pc < prog.instructions.size)
    (hnot_term : ¬ IsTerminator prog pc)
    -- Well-formedness: the instruction type is supported
    (hty : ∃ ty, instrType prog pc = some ty ∧ IsSupportedInstrType ty)
    -- Guards evaluate to booleans (in bind form)
    (hguard_bool : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b))
    -- ASSIGN has valid lhs/rhs and rhs evaluates or is nondet
    (hassign : instrType prog pc = some .ASSIGN →
      (∃ name, (instrCode prog pc).bind getAssignLhs = some name) ∧
      (∃ rhs, (instrCode prog pc).bind getAssignRhs = some rhs) ∧
      (∀ rhs, (instrCode prog pc).bind getAssignRhs = some rhs →
        (∃ v, eval σ rhs = some v) ∨ rhs.id = .side_effect .Nondet))
    -- DECL/DEAD have symbol names
    (hdecl : instrType prog pc = some .DECL →
      ∃ name, (instrCode prog pc).bind getSymbolName = some name)
    (hdead : instrType prog pc = some .DEAD →
      ∃ name, (instrCode prog pc).bind getSymbolName = some name)
    -- GOTO targets exist and resolve
    (hgoto : instrType prog pc = some .GOTO →
      ∃ tgt, instrTarget prog pc = some (some tgt))
    (hgoto_resolve : ∀ tgt, instrTarget prog pc = some (some tgt) →
      ∃ idx, findLocIdx prog.instructions tgt = some idx)
    -- Function calls resolve
    (hfcall : instrType prog pc = some .FUNCTION_CALL →
      (∃ name, (instrCode prog pc).bind getCallCallee = some name) ∧
      (∀ name, (instrCode prog pc).bind getCallCallee = some name →
        ∃ σ' rv, callResult eval fenv name σ σ' rv)) :
    (∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ') ∨
    AssumeBlocks eval prog pc σ := by
  obtain ⟨ty, hty_eq, hsupp⟩ := hty
  -- Dispatch on the instruction type
  rcases hsupp with h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · left; exact progress_skip hty_eq
  · left; exact progress_location hty_eq
  · left; obtain ⟨hl, hr, hev⟩ := hassign hty_eq
    exact progress_assign hty_eq hl hr hev
  · left; exact progress_decl hty_eq (hdecl hty_eq)
  · left; exact progress_dead hty_eq (hdead hty_eq)
  · left
    exact progress_goto hty_eq hguard_bool (hgoto hty_eq) hgoto_resolve
  · exact progress_assume hty_eq hguard_bool
  · left; exact progress_assert hty_eq hguard_bool
  · left; obtain ⟨hcallee, hcall⟩ := hfcall hty_eq
    exact progress_function_call hty_eq hcallee hcall
  · exact absurd (.inl hty_eq) hnot_term
  · exact absurd (.inr hty_eq) hnot_term

end CProverGOTO.Semantics

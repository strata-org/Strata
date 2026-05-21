/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.SemanticsTautschnig

public section

/-! # Properties of Tautschnig-style GOTO Semantics

Phase-0 port of `tautschnig/goto-semantics`'s `SemanticsProps.lean`.
Lives in `CProverGOTO.SemanticsTautschnig`. -/

namespace CProverGOTO.SemanticsTautschnig

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
  next _ hcr1 hσ1 _ _ hcr2 hσ2 =>
    have ⟨hσeq, hreq⟩ := hcall _ _ _ _ _ _ _ _ hcr1 hcr2
    subst hσeq; subst hreq; simp_all

/-! ## Reachability Lemmas -/

theorem reachable_single
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    Reachable callResult eval fenv prog pc σ pc' σ' :=
  fun h => .step h .refl

theorem safe_no_assert_fail
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {σ₀ σ : Store} {pc : Nat} :
    ProgramSafe callResult eval fenv prog σ₀ →
    Reachable callResult eval fenv prog 0 σ₀ pc σ →
    ¬ AssertFails eval prog pc σ :=
  fun hsafe hreach => hsafe pc σ hreach

/-! ## ExecProg Properties -/

theorem exec_empty_prog
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {σ : Store} :
    ExecProg callResult eval fenv { instructions := #[] } 0 σ σ none :=
  .out_of_bounds (by simp)

theorem instrType_some_lt {prog : Program} {pc : Nat} {ty : InstructionType} :
    instrType prog pc = some ty → pc < prog.instructions.size := by
  simp only [instrType]
  intro h
  exact Decidable.byContradiction fun hge => by
    simp only [Nat.not_lt] at hge
    simp [Array.getElem?_eq_none hge] at h

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

def IsTerminator (prog : Program) (pc : Nat) : Prop :=
  instrType prog pc = some .END_FUNCTION ∨
  instrType prog pc = some .SET_RETURN_VALUE

def AssumeBlocks (eval : ExprEval) (prog : Program) (pc : Nat) (σ : Store) : Prop :=
  instrType prog pc = some .ASSUME ∧
  (instrGuard prog pc).bind (eval σ ·) = some (.vBool false)

def IsSupportedInstrType (ty : InstructionType) : Prop :=
  ty = .SKIP ∨ ty = .LOCATION ∨ ty = .ASSIGN ∨ ty = .DECL ∨ ty = .DEAD ∨
  ty = .GOTO ∨ ty = .ASSUME ∨ ty = .ASSERT ∨ ty = .FUNCTION_CALL ∨
  ty = .END_FUNCTION ∨ ty = .SET_RETURN_VALUE

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

theorem progress_decl
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .DECL)
    (hcode : ∃ name, (instrCode prog pc).bind getSymbolName = some name) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hcode
  exact ⟨pc + 1, σ.declare name, .decl hty hname⟩

theorem progress_dead
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .DEAD)
    (hcode : ∃ name, (instrCode prog pc).bind getSymbolName = some name) :
    ∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ' := by
  obtain ⟨name, hname⟩ := hcode
  exact ⟨pc + 1, σ.kill name, .dead hty hname⟩

theorem progress_assign
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .ASSIGN)
    (hlhs : ∃ name, (instrCode prog pc).bind getAssignLhs = some name)
    (hrhs : ∃ rhs, (instrCode prog pc).bind getAssignRhs = some rhs)
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

theorem progress_goto
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (hty : instrType prog pc = some .GOTO)
    (hguard : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b))
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

theorem progress_wellformed
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store}
    (_hbound : pc < prog.instructions.size)
    (hnot_term : ¬ IsTerminator prog pc)
    (hty : ∃ ty, instrType prog pc = some ty ∧ IsSupportedInstrType ty)
    (hguard_bool : ∃ b, (instrGuard prog pc).bind (eval σ ·) = some (.vBool b))
    (hassign : instrType prog pc = some .ASSIGN →
      (∃ name, (instrCode prog pc).bind getAssignLhs = some name) ∧
      (∃ rhs, (instrCode prog pc).bind getAssignRhs = some rhs) ∧
      (∀ rhs, (instrCode prog pc).bind getAssignRhs = some rhs →
        (∃ v, eval σ rhs = some v) ∨ rhs.id = .side_effect .Nondet))
    (hdecl : instrType prog pc = some .DECL →
      ∃ name, (instrCode prog pc).bind getSymbolName = some name)
    (hdead : instrType prog pc = some .DEAD →
      ∃ name, (instrCode prog pc).bind getSymbolName = some name)
    (hgoto : instrType prog pc = some .GOTO →
      ∃ tgt, instrTarget prog pc = some (some tgt))
    (hgoto_resolve : ∀ tgt, instrTarget prog pc = some (some tgt) →
      ∃ idx, findLocIdx prog.instructions tgt = some idx)
    (hfcall : instrType prog pc = some .FUNCTION_CALL →
      (∃ name, (instrCode prog pc).bind getCallCallee = some name) ∧
      (∀ name, (instrCode prog pc).bind getCallCallee = some name →
        ∃ σ' rv, callResult eval fenv name σ σ' rv)) :
    (∃ pc' σ', StepInstr callResult eval fenv prog pc σ pc' σ') ∨
    AssumeBlocks eval prog pc σ := by
  obtain ⟨ty, hty_eq, hsupp⟩ := hty
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

end CProverGOTO.SemanticsTautschnig

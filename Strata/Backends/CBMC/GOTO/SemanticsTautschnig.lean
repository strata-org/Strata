/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Program

public section

/-! # Tautschnig-style operational semantics for the CBMC GOTO language

This module is a port of the operational semantics from the
`tautschnig/goto-semantics` branch, namespaced as
`CProverGOTO.SemanticsTautschnig` so it coexists with this branch's
`CProverGOTO.StepGoto` (defined in `Semantics.lean`).

It is brought in by Phase 0 of the GOTO-semantics-expansion plan
(`docs/superpowers/specs/2026-05-20-goto-semantics-expansion-design.md`)
to support the Phase-0 bisimulation bridge between the two step
relations. If/when Phase 5 (convergence) ever fires, these dual-namespace
files go away.

The semantics covers a wider set of GOTO instructions than `StepGoto`
does today (`SKIP`, `DEAD`, `FUNCTION_CALL`, `SET_RETURN_VALUE` in
addition to the seven shared types), uses a concrete `Value` /
`Store` rather than an abstract `Imperative.SemanticStore`, and
exposes per-instruction accessors plus determinism / progress
infrastructure (proven in `SemanticsPropsTautschnig.lean`). -/

namespace CProverGOTO.SemanticsTautschnig

open CProverGOTO

/-! ## Values -/

/-- Runtime values for GOTO programs.
    Mirrors the types supported by the GOTO type system (`Ty`). -/
inductive Value where
  | vBool   : Bool → Value
  | vInt    : Int → Value
  | vBV     : (width : Nat) → Int → Value
  | vReal   : Int → Int → Value
  | vString : String → Value
  | vArray  : List Value → Value
  | vStruct : List (String × Value) → Value
  | vEmpty  : Value
  deriving Repr, BEq, Inhabited

/-! ## Store -/

/-- Variable store: maps symbol names to optional values.
    A variable is "declared" when it maps to `some v`, and
    "undeclared" / "dead" when it maps to `none`. -/
abbrev Store := String → Option Value

@[expose] def Store.empty : Store := fun _ => none

/-- Update a variable in the store. -/
@[expose] def Store.update (σ : Store) (name : String) (v : Value) : Store :=
  fun x => if x == name then some v else σ x

/-- Declare a variable with a default value (`.vEmpty` sentinel). -/
@[expose] def Store.declare (σ : Store) (name : String) : Store :=
  fun x => if x == name then some .vEmpty else σ x

/-- Mark a variable as dead. -/
@[expose] def Store.kill (σ : Store) (name : String) : Store :=
  fun x => if x == name then none else σ x

/-! ## Expression Evaluator (abstract) -/

/-- Abstract expression evaluator. -/
abbrev ExprEval := Store → Expr → Option Value

/-- Two-state expression evaluator for postconditions with `old()`. -/
abbrev ExprEval₂ := Store → Store → Expr → Option Value

/-- Lift a single-state evaluator to a two-state evaluator that handles `old()`. -/
def ExprEval.withOld (eval : ExprEval) : ExprEval₂ := fun σ_old σ_cur e =>
  match e.id, e.operands with
  | .unary .Old, [inner] => eval σ_old inner
  | _, _ => eval σ_cur e

/-! ## Function Environment -/

/-- Maps function names to their GOTO programs. -/
abbrev FuncEnv := String → Option Program

/-! ## Instruction Accessors -/

@[expose] def instrType (prog : Program) (pc : Nat) : Option InstructionType :=
  (prog.instructions[pc]?).map Instruction.type

@[expose] def instrGuard (prog : Program) (pc : Nat) : Option Expr :=
  (prog.instructions[pc]?).map Instruction.guard

@[expose] def instrTarget (prog : Program) (pc : Nat) : Option (Option Target) :=
  (prog.instructions[pc]?).map Instruction.target

@[expose] def instrCode (prog : Program) (pc : Nat) : Option Code :=
  (prog.instructions[pc]?).map Instruction.code

/-- Extract the symbol name from a DECL/DEAD code operand. -/
@[expose] def getSymbolName (c : Code) : Option String :=
  match c.operands with
  | [e] => match e.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Extract lhs name from an ASSIGN code. -/
@[expose] def getAssignLhs (c : Code) : Option String :=
  match c.operands with
  | [lhs, _rhs] => match lhs.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Extract rhs expression from an ASSIGN code. -/
@[expose] def getAssignRhs (c : Code) : Option Expr :=
  match c.operands with
  | [_lhs, rhs] => some rhs
  | _ => none

/-- Extract the return value expression from a SET_RETURN_VALUE code. -/
@[expose] def getReturnValue (c : Code) : Option Expr :=
  match c.operands with
  | [e] => some e
  | _ => none

/-- Extract function call lhs name. -/
@[expose] def getCallLhs (c : Code) : Option String :=
  match c.operands with
  | [lhs, _, _] => match lhs.id with
    | .nullary (.symbol name) => if name == "" then none else some name
    | _ => none
  | _ => none

/-- Extract function call callee name. -/
@[expose] def getCallCallee (c : Code) : Option String :=
  match c.operands with
  | [_, callee, _] => match callee.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Find the array index of an instruction with a given locationNum. -/
@[expose] def findLocIdx (instrs : Array Instruction) (loc : Nat) : Option Nat :=
  go instrs.toList 0
where
  go : List Instruction → Nat → Option Nat
    | [], _ => none
    | i :: rest, idx => if i.locationNum == loc then some idx else go rest (idx + 1)

/-! ## Abstract Callee Result -/

/-- Abstract relation for function call results. -/
abbrev CallResultRel := ExprEval → FuncEnv → String → Store → Store → Option Value → Prop

/-! ## Single-Step Semantics -/

/-- Single-step execution of one GOTO instruction. -/
inductive StepInstr (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) :
    Nat → Store → Nat → Store → Prop where

  | skip :
    instrType prog pc = some .SKIP →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | location :
    instrType prog pc = some .LOCATION →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | assign :
    instrType prog pc = some .ASSIGN →
    (instrCode prog pc).bind getAssignLhs = some name →
    (instrCode prog pc).bind getAssignRhs = some rhs →
    eval σ rhs = some v →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.update name v)

  | assign_nondet :
    instrType prog pc = some .ASSIGN →
    (instrCode prog pc).bind getAssignLhs = some name →
    (instrCode prog pc).bind getAssignRhs = some rhs →
    rhs.id = .side_effect .Nondet →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.update name v)

  | decl :
    instrType prog pc = some .DECL →
    (instrCode prog pc).bind getSymbolName = some name →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.declare name)

  | dead :
    instrType prog pc = some .DEAD →
    (instrCode prog pc).bind getSymbolName = some name →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.kill name)

  | goto_taken :
    instrType prog pc = some .GOTO →
    instrTarget prog pc = some (some tgt) →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    findLocIdx prog.instructions tgt = some tgtIdx →
    StepInstr callResult eval fenv prog pc σ tgtIdx σ

  | goto_not_taken :
    instrType prog pc = some .GOTO →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool false) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | assume_pass :
    instrType prog pc = some .ASSUME →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | assert_pass :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | assert_fail :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool false) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  | function_call :
    instrType prog pc = some .FUNCTION_CALL →
    (instrCode prog pc).bind getCallCallee = some calleeName →
    callResult eval fenv calleeName σ σ' retVal →
    σ'' = (match (instrCode prog pc).bind getCallLhs, retVal with
           | some name, some v => σ'.update name v
           | _, _ => σ') →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ''

/-! ## Multi-Step Execution -/

/-- Execute a GOTO program from a given PC to completion. -/
inductive ExecProg (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) :
    Nat → Store → Store → Option Value → Prop where

  | out_of_bounds :
    pc ≥ prog.instructions.size →
    ExecProg callResult eval fenv prog pc σ σ none

  | end_function :
    instrType prog pc = some .END_FUNCTION →
    ExecProg callResult eval fenv prog pc σ σ none

  | set_return_value :
    instrType prog pc = some .SET_RETURN_VALUE →
    (instrCode prog pc).bind getReturnValue = some retExpr →
    eval σ retExpr = some v →
    ExecProg callResult eval fenv prog (pc + 1) σ σ' retVal →
    ExecProg callResult eval fenv prog pc σ σ' (retVal <|> some v)

  | step :
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    ExecProg callResult eval fenv prog pc' σ' σ'' retVal →
    ExecProg callResult eval fenv prog pc σ σ'' retVal

/-! ## Program-Level Execution -/

/-- Execute a complete GOTO program starting from PC 0. -/
def execProgram (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (σ₀ σ' : Store) (retVal : Option Value) : Prop :=
  ExecProg callResult eval fenv prog 0 σ₀ σ' retVal

/-! ## Assertion Safety -/

/-- An assertion fails at `pc` in store `σ`. -/
@[expose] def AssertFails (eval : ExprEval) (prog : Program) (pc : Nat) (σ : Store) : Prop :=
  instrType prog pc = some .ASSERT ∧
  (instrGuard prog pc).bind (eval σ ·) = some (.vBool false)

/-- Reachability via zero or more steps. -/
inductive Reachable (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) :
    Nat → Store → Nat → Store → Prop where
  | refl :
    Reachable callResult eval fenv prog pc σ pc σ
  | step :
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    Reachable callResult eval fenv prog pc' σ' pc'' σ'' →
    Reachable callResult eval fenv prog pc σ pc'' σ''

/-- A program is safe if no reachable state has a failing assertion. -/
@[expose] def ProgramSafe (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (σ₀ : Store) : Prop :=
  ∀ pc σ,
    Reachable callResult eval fenv prog 0 σ₀ pc σ →
    ¬ AssertFails eval prog pc σ

/-! ## Basic Properties -/

theorem assume_preserves_store
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    instrType prog pc = some .ASSUME →
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    σ' = σ := by
  intro htype hstep
  cases hstep <;> simp_all

theorem assert_preserves_store
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    instrType prog pc = some .ASSERT →
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    σ' = σ := by
  intro htype hstep
  cases hstep <;> simp_all

theorem reachable_trans
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc₁ pc₂ pc₃ : Nat} {σ₁ σ₂ σ₃ : Store} :
    Reachable callResult eval fenv prog pc₁ σ₁ pc₂ σ₂ →
    Reachable callResult eval fenv prog pc₂ σ₂ pc₃ σ₃ →
    Reachable callResult eval fenv prog pc₁ σ₁ pc₃ σ₃ := by
  intro h1 h2
  induction h1 with
  | refl => exact h2
  | step hstep _hreach ih => exact .step hstep (ih h2)

end CProverGOTO.SemanticsTautschnig

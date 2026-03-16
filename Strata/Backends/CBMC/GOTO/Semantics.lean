/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program

/-!
# Formal Semantics for CBMC's GOTO Intermediate Language

This file defines a big-step operational semantics for the GOTO intermediate
representation used by CBMC, as modeled by the Strata `CProverGOTO` AST.

## Design

The semantics is defined as an inductive relation over GOTO programs (flat
instruction arrays with a program counter). The judgment form is:

  `eval, fenv, prog, pc, σ ⊢ σ', retVal`

where:
- `eval` is an abstract expression evaluator
- `fenv` is a function environment mapping function names to GOTO programs
- `prog` is the current GOTO program (instruction array)
- `pc` is the current program counter (index into the instruction array)
- `σ` is the variable store
- `σ'` is the resulting store
- `retVal` is the optional return value

## Scope

This semantics covers the subset of GOTO instructions that Strata's
Core-to-GOTO translation (`CoreToCProverGOTO.lean`, `ToCProverGOTO.lean`)
produces:

### Fully modeled instructions
- **ASSIGN** — `lhs := rhs` assignment (including nondet side effects)
- **DECL** — local variable declaration (introduces a symbol)
- **DEAD** — end of variable lifetime (removes from store)
- **GOTO** — conditional/unconditional branch (guarded by `guard`, jumps to `target`)
- **ASSUME** — constrain execution (block if `guard` is false)
- **ASSERT** — verification obligation (flag error if `guard` is false)
- **SKIP** — no-op, advance PC
- **LOCATION** — semantically identical to SKIP (used for labels)
- **END_FUNCTION** — marks function exit, halts execution of current function
- **SET_RETURN_VALUE** — sets the return value (used for pure function bodies)
- **FUNCTION_CALL** — invoke a function with arguments, assign return value

### Intentionally omitted instructions
- **START_THREAD / END_THREAD** — concurrency (not produced by Strata)
- **ATOMIC_BEGIN / ATOMIC_END** — atomicity blocks (not produced by Strata)
- **THROW / CATCH** — exception handling (not produced by Strata)
- **OTHER** — miscellaneous (array_set, printf, etc.; not produced by Strata)
- **INCOMPLETE_GOTO** — placeholder (should not appear in final programs)
- **NO_INSTRUCTION_TYPE** — invalid (should not appear)

### Expression evaluation
Expression evaluation is abstracted via a parameter `eval : Store → Expr → Option Value`.
This keeps the semantics modular: the expression evaluator can be instantiated
with different interpretations (concrete, symbolic, etc.) without changing the
instruction-level rules.

### Known limitations
- **Pointers and memory**: The store is a flat map from variable names to values.
  Pointer arithmetic, address-of, and dereference are not modeled.
- **Struct/array values**: Values include structured forms, but field access and
  indexing are delegated to the expression evaluator.
- **Non-determinism in GOTO targets**: Exactly one target is required for GOTO
  instructions (multiple targets are deprecated in CBMC).
- **Function calls**: Modeled via a separate `CallResult` relation that
  abstracts callee execution.
- **Assertion semantics**: CBMC records assertion failures but continues
  execution. We model this by having `assert_fail` advance the PC normally.
  A separate `ProgramSafe` predicate captures the property that no assertion
  fails.

## Relationship to CBMC's interpreter

The semantics is informed by CBMC's concrete interpreter
(`src/goto-programs/interpreter.cpp`), but abstracts away:
- The flat memory model (replaced by a named variable store)
- The symbol table (replaced by the function environment)
- Trace recording (not modeled; we only track state transitions)

## TODO
- [x] Prove determinism of the single-step relation (for deterministic `eval`)
      → See `SemanticsProps.lean`: `StepInstr_deterministic_no_nondet`
- [x] Prove determinism of `ExecProg`
      → See `SemanticsProps.lean`: `ExecProg_deterministic`
- [x] Prove that well-formed programs (from Strata's translation) always make
      progress or terminate
      → See `SemanticsProps.lean`: `progress_wellformed`
- [x] Formalize expression evaluation for the concrete GOTO expression language
      → See `SemanticsEval.lean`: `concreteEval`
- [x] Connect to Strata Core semantics: prove that the Core-to-GOTO translation
      preserves the semantics (simulation relation)
      → See `SemanticsSim.lean`: all command-level simulation lemmas proved
        (`sim_assert`, `sim_assume`, `sim_set`, `sim_init`, `sim_havoc`,
         `sim_cmd`), plus if-then-else guard simulation
- [x] Add support for `old()` expressions in postconditions
      → See `Semantics.lean`: `ExprEval₂`, `ExprEval.withOld`
      → See `SemanticsEval.lean`: `concreteEval₂`
- [x] Statement-level simulation for block and loop
      → See `SemanticsSim.lean`: `sim_block`, `ExecLoop`, `sim_loop`
- [ ] End-to-end theorem: `EvalBlock` implies `ExecProg` on translated program
      (requires connecting `ExecRange` composition to `ExecProg`)
- [x] Loop evaluation rules added to Imperative `EvalStmt`
      → See `StmtSemantics.lean`: `loop_false_sem`, `loop_true_sem`
      (3 sorry's introduced in `DetToNondetCorrect.lean` — the DetToNondet
       correctness proof needs restructuring for derivation-based induction)
- [x] Progress theorems (per-instruction-type)
      → See `SemanticsProps.lean`: `progress_skip`, `progress_assign`, etc.
-/

namespace CProverGOTO.Semantics

open CProverGOTO

/-! ## Values -/

/-- Runtime values for GOTO programs.
    Mirrors the types supported by the GOTO type system (`Ty`). -/
inductive Value where
  | vBool   : Bool → Value
  | vInt    : Int → Value
  | vBV     : (width : Nat) → Int → Value
  | vReal   : Int → Int → Value  -- numerator / denominator
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

def Store.empty : Store := fun _ => none

/-- Update a variable in the store. -/
def Store.update (σ : Store) (name : String) (v : Value) : Store :=
  fun x => if x == name then some v else σ x

/-- Declare a variable with a default value. -/
def Store.declare (σ : Store) (name : String) : Store :=
  fun x => if x == name then some .vEmpty else σ x

/-- Mark a variable as dead. -/
def Store.kill (σ : Store) (name : String) : Store :=
  fun x => if x == name then none else σ x

/-! ## Expression Evaluator (abstract) -/

/-- Abstract expression evaluator. -/
abbrev ExprEval := Store → Expr → Option Value

/-- Two-state expression evaluator for postconditions with `old()`.
    Takes both the pre-state (at procedure entry) and the current state. -/
abbrev ExprEval₂ := Store → Store → Expr → Option Value

/-- Lift a single-state evaluator to a two-state evaluator that handles `old()`.
    `old(e)` evaluates `e` in the pre-state; all other expressions use the
    current state. -/
def ExprEval.withOld (eval : ExprEval) : ExprEval₂ := fun σ_old σ_cur e =>
  match e.id, e.operands with
  | .unary .Old, [inner] => eval σ_old inner
  | _, _ => eval σ_cur e

/-! ## Function Environment -/

/-- Maps function names to their GOTO programs. -/
abbrev FuncEnv := String → Option Program

/-! ## Instruction Accessors -/

/-- Get instruction type at a given PC, or `none` if out of bounds. -/
def instrType (prog : Program) (pc : Nat) : Option InstructionType :=
  (prog.instructions[pc]?).map Instruction.type

/-- Get instruction guard at a given PC. -/
def instrGuard (prog : Program) (pc : Nat) : Option Expr :=
  (prog.instructions[pc]?).map Instruction.guard

/-- Get instruction target at a given PC. -/
def instrTarget (prog : Program) (pc : Nat) : Option (Option Target) :=
  (prog.instructions[pc]?).map Instruction.target

/-- Get instruction code at a given PC. -/
def instrCode (prog : Program) (pc : Nat) : Option Code :=
  (prog.instructions[pc]?).map Instruction.code

/-- Extract the symbol name from a DECL/DEAD code operand. -/
def getSymbolName (c : Code) : Option String :=
  match c.operands with
  | [e] => match e.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Extract lhs name and rhs expression from an ASSIGN code. -/
def getAssignLhs (c : Code) : Option String :=
  match c.operands with
  | [lhs, _rhs] => match lhs.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Extract rhs expression from an ASSIGN code. -/
def getAssignRhs (c : Code) : Option Expr :=
  match c.operands with
  | [_lhs, rhs] => some rhs
  | _ => none

/-- Extract the return value expression from a SET_RETURN_VALUE code. -/
def getReturnValue (c : Code) : Option Expr :=
  match c.operands with
  | [e] => some e
  | _ => none

/-- Extract function call lhs name. -/
def getCallLhs (c : Code) : Option String :=
  match c.operands with
  | [lhs, _, _] => match lhs.id with
    | .nullary (.symbol name) => if name == "" then none else some name
    | _ => none
  | _ => none

/-- Extract function call callee name. -/
def getCallCallee (c : Code) : Option String :=
  match c.operands with
  | [_, callee, _] => match callee.id with
    | .nullary (.symbol name) => some name
    | _ => none
  | _ => none

/-- Find the array index of an instruction with a given locationNum. -/
def findLocIdx (instrs : Array Instruction) (loc : Nat) : Option Nat :=
  go instrs.toList 0
where
  go : List Instruction → Nat → Option Nat
    | [], _ => none
    | i :: rest, idx => if i.locationNum == loc then some idx else go rest (idx + 1)

/-! ## Abstract Callee Result -/

/-- Abstract relation for function call results.
    `CallResult eval fenv calleeName σ σ' retVal` means: calling function
    `calleeName` with store `σ` produces final store `σ'` and optional
    return value `retVal`.

    This is left as a parameter to break the mutual recursion between
    single-step and multi-step execution. -/
abbrev CallResultRel := ExprEval → FuncEnv → String → Store → Store → Option Value → Prop

/-! ## Single-Step Semantics -/

/-- Single-step execution of one GOTO instruction.

The judgment `StepInstr callResult eval fenv prog pc σ pc' σ'` means:
executing the instruction at index `pc` in `prog` with store `σ`
transitions to program counter `pc'` and store `σ'`.
-/
inductive StepInstr (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) :
    Nat → Store → Nat → Store → Prop where

  /-- **SKIP**: Advance PC, no state change. -/
  | skip :
    instrType prog pc = some .SKIP →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **LOCATION**: Semantically identical to SKIP. -/
  | location :
    instrType prog pc = some .LOCATION →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSIGN**: Evaluate rhs, update lhs in store. -/
  | assign :
    instrType prog pc = some .ASSIGN →
    (instrCode prog pc).bind getAssignLhs = some name →
    (instrCode prog pc).bind getAssignRhs = some rhs →
    eval σ rhs = some v →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.update name v)

  /-- **ASSIGN with nondet**: rhs is a nondeterministic side effect.
      The variable gets an arbitrary value `v`. -/
  | assign_nondet :
    instrType prog pc = some .ASSIGN →
    (instrCode prog pc).bind getAssignLhs = some name →
    (instrCode prog pc).bind getAssignRhs = some rhs →
    rhs.id = .side_effect .Nondet →
    -- `v` is universally quantified (any value is a valid result)
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.update name v)

  /-- **DECL**: Declare a local variable. -/
  | decl :
    instrType prog pc = some .DECL →
    (instrCode prog pc).bind getSymbolName = some name →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.declare name)

  /-- **DEAD**: End lifetime of a local variable. -/
  | dead :
    instrType prog pc = some .DEAD →
    (instrCode prog pc).bind getSymbolName = some name →
    StepInstr callResult eval fenv prog pc σ (pc + 1) (σ.kill name)

  /-- **GOTO (taken)**: Guard is true, jump to target. -/
  | goto_taken :
    instrType prog pc = some .GOTO →
    instrTarget prog pc = some (some tgt) →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    findLocIdx prog.instructions tgt = some tgtIdx →
    StepInstr callResult eval fenv prog pc σ tgtIdx σ

  /-- **GOTO (not taken)**: Guard is false, fall through. -/
  | goto_not_taken :
    instrType prog pc = some .GOTO →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool false) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSUME (pass)**: Guard is true, advance.
      When the guard is false, there is no derivation — the execution path
      is infeasible (CBMC models this as a non-failing guarded self-loop). -/
  | assume_pass :
    instrType prog pc = some .ASSUME →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSERT (pass)**: Guard is true, advance normally. -/
  | assert_pass :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSERT (fail)**: Guard is false, advance (CBMC continues after failures).
      The assertion failure is observable via `AssertFails` below. -/
  | assert_fail :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.vBool false) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **FUNCTION_CALL**: Call a function, assign return value to lhs. -/
  | function_call :
    instrType prog pc = some .FUNCTION_CALL →
    (instrCode prog pc).bind getCallCallee = some calleeName →
    callResult eval fenv calleeName σ σ' retVal →
    σ'' = (match (instrCode prog pc).bind getCallLhs, retVal with
           | some name, some v => σ'.update name v
           | _, _ => σ') →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ''

/-! ## Multi-Step Execution -/

/-- Execute a GOTO program from a given PC to completion.
    Terminates when END_FUNCTION is reached or PC goes out of bounds. -/
inductive ExecProg (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) :
    Nat → Store → Store → Option Value → Prop where

  /-- PC out of bounds: implicit halt. -/
  | out_of_bounds :
    pc ≥ prog.instructions.size →
    ExecProg callResult eval fenv prog pc σ σ none

  /-- END_FUNCTION reached: halt. -/
  | end_function :
    instrType prog pc = some .END_FUNCTION →
    ExecProg callResult eval fenv prog pc σ σ none

  /-- SET_RETURN_VALUE: evaluate return expression, then continue. -/
  | set_return_value :
    instrType prog pc = some .SET_RETURN_VALUE →
    (instrCode prog pc).bind getReturnValue = some retExpr →
    eval σ retExpr = some v →
    ExecProg callResult eval fenv prog (pc + 1) σ σ' retVal →
    ExecProg callResult eval fenv prog pc σ σ' (retVal <|> some v)

  /-- Normal step: execute one instruction, then continue. -/
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
def AssertFails (eval : ExprEval) (prog : Program) (pc : Nat) (σ : Store) : Prop :=
  instrType prog pc = some .ASSERT ∧
  (instrGuard prog pc).bind (eval σ ·) = some (.vBool false)

/-- Reachability: `(pc', σ')` is reachable from `(pc, σ)` by zero or more steps. -/
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
def ProgramSafe (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (σ₀ : Store) : Prop :=
  ∀ pc σ,
    Reachable callResult eval fenv prog 0 σ₀ pc σ →
    ¬ AssertFails eval prog pc σ

/-! ## Basic Properties -/

/-- ASSUME does not modify the store. -/
theorem assume_preserves_store
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    instrType prog pc = some .ASSUME →
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    σ' = σ := by
  intro htype hstep
  cases hstep <;> simp_all

/-- ASSERT does not modify the store. -/
theorem assert_preserves_store
    {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc pc' : Nat} {σ σ' : Store} :
    instrType prog pc = some .ASSERT →
    StepInstr callResult eval fenv prog pc σ pc' σ' →
    σ' = σ := by
  intro htype hstep
  cases hstep <;> simp_all

/-- Reachability is transitive. -/
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

end CProverGOTO.Semantics

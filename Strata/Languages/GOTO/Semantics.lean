/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.GOTO.Program
public import Strata.DL.Util.Relations
import Strata.Util.Tactics

/-!
# Formal Semantics for CBMC's GOTO Intermediate Language

This file defines a small-step operational semantics for the GOTO intermediate
representation used by CBMC, as modeled by the Strata `CProverGOTO` AST.

## Design

The semantics is small-step: `StepInstr` is a single-instruction transition
relation, `ExecProg` is its multi-step closure to a function's exit, and
`Reachable` is the reflexive-transitive closure used for safety. It is defined
as an inductive relation over GOTO programs (flat instruction arrays with a
program counter). The single-step judgment form is:

  `eval, fenv, prog, pc, σ ↪ σ', retVal`

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

The exact set of modeled instructions is the constructors of the `StepInstr`
relation (plus the `ExecProg` terminators `END_FUNCTION`/`SET_RETURN_VALUE`)
below, which are the source of truth. Concurrency (`START_THREAD`/`END_THREAD`,
`ATOMIC_*`), exceptions (`THROW`/`CATCH`), `OTHER`, and the `INCOMPLETE_GOTO`/
`NO_INSTRUCTION_TYPE` placeholders are not produced by Strata and are not
modeled.

### Expression evaluation
Expression evaluation is abstracted via a parameter `eval : Store → Expr → Option Value`.
This keeps the semantics modular: the expression evaluator can be instantiated
with different interpretations (concrete, symbolic, etc.) without changing the
instruction-level rules.

### Known limitations
- **Pointers and memory**: The store is a flat map from variable names to values.
  Pointer arithmetic, address-of, and dereference are not modeled. A byte-level
  flat memory (e.g. `Array UInt8`) is straightforward to model in Lean; the
  deferred difficulty is CBMC's memory-*object* model layered on top — object
  identity/bounds, alignment and padding, type-punning between a value and its
  byte representation, and pointer provenance — which the named-variable store
  side-steps for the instruction subset Strata currently emits.
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
- Trace recording: CBMC's interpreter records a full execution trace — the
  ordered list of assignments, guard directions, and assertion outcomes — which
  it later reports as a counterexample. We model only the input/output state
  relation (`σ ↪ σ'`, with `AssertFails`/`ProgramSafe` capturing assertion
  status), not the step-indexed trace, since the meta-theory here concerns
  determinism, progress, and safety rather than counterexample reconstruction.

## Scope note

Deferred to a follow-up (Phase 2, stacked on this change): the Core/Imperative
⟹ GOTO **simulation** (`sim_cmd`, `sim_block`, `sim_loop`, `sim_end_to_end`),
re-derived against the current small-step Imperative semantics. (The upstream
PR's big-step Imperative "loop rules" base layer is dropped, since the
small-step Imperative semantics already models loops.)
-/

namespace CProverGOTO.Semantics

open CProverGOTO

public section

/-! ## Values -/

/-- Runtime values for GOTO programs.
    Mirrors the types supported by the GOTO type system (`Ty`). -/
inductive Value where
  | bool   : Bool → Value
  | int    : Int → Value
  | bv     : (width : Nat) → Int → Value
  | rational   : Int → Int → Value  -- numerator / denominator
  | string : String → Value
  | array  : List Value → Value
  | struct : List (String × Value) → Value
  | undefined  : Value
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

/-- Declare a variable with a default value.
    Note: In CBMC, DECL introduces a symbol but the value is undefined until
    assigned. We use `.undefined` as a sentinel. The translation pipeline always
    follows DECL with an ASSIGN (for `init x ty (some e)`) or with a nondet
    ASSIGN (for `havoc`), so `.undefined` is never observed in well-formed
    translated programs. For `init x ty none` (unconstrained init), the
    Imperative semantics uses `InitState` with an arbitrary value, which
    corresponds to the DECL + nondet ASSIGN pattern in GOTO. -/
def Store.declare (σ : Store) (name : String) : Store :=
  fun x => if x == name then some .undefined else σ x

/-- Mark a variable as dead. -/
def Store.kill (σ : Store) (name : String) : Store :=
  fun x => if x == name then none else σ x

/-! ## Expression Evaluator (abstract) -/

/-- Abstract expression evaluator. -/
abbrev ExprEval := Store → Expr → Option Value

/-- Two-state expression evaluator for postconditions with `old()`.
    Takes both the pre-state (at procedure entry) and the current state. -/
abbrev ExprEval₂ := Store → Store → Expr → Option Value

/-- Remove every `old(...)` wrapper from an expression. Inside an `old(...)`
    context all sub-expressions already refer to the pre-state, so a nested
    `old` is transparent and can simply be dropped. -/
def Expr.stripOld (e : Expr) : Expr :=
  match e.id, _: e.operands with
  | .unary .Old, [inner] => Expr.stripOld inner
  | _, _ => { e with operands := e.operands.map Expr.stripOld }
  termination_by (SizeOf.sizeOf e)
  decreasing_by all_goals (cases e; term_by_mem)

/-- Rewrite `e`, replacing each *maximal* `old(inner)` subterm with a fresh
    symbol (named `#old<n>`), and collecting a binding from that fresh name to
    the old-stripped `inner` (which must be evaluated in the pre-state). The
    `next` counter guarantees the generated names are distinct. Returns the
    rewritten expression, the collected bindings (in left-to-right order), and
    the next unused counter value. -/
def Expr.rewriteOld (e : Expr) (next : Nat) :
    Expr × List (String × Expr) × Nat :=
  match e.id, _: e.operands with
  | .unary .Old, [inner] =>
    let name := s!"#old{next}"
    let sym : Expr := { id := .nullary (.symbol name), type := e.type }
    (sym, [(name, Expr.stripOld inner)], next + 1)
  | _, _ =>
    let (opsRev, binds, next') :=
      e.operands.foldl
        (fun acc op =>
          let (op', b, n') := Expr.rewriteOld op acc.2.2
          (op' :: acc.1, acc.2.1 ++ b, n'))
        (([] : List Expr), ([] : List (String × Expr)), next)
    ({ e with operands := opsRev.reverse }, binds, next')
  termination_by (SizeOf.sizeOf e)
  decreasing_by all_goals (cases e; term_by_mem)

/-- Lift a single-state evaluator to a two-state evaluator that handles `old()`
    at ANY nesting depth (not just at the top level).

    Each *maximal* `old(inner)` subterm is evaluated in the pre-state `σ_old`
    and bound to a fresh symbol; the remainder of the expression (which now
    references those fresh symbols and otherwise reads the current state) is
    evaluated in `σ_cur` extended with those bindings.

    This assumes `eval` interprets symbol expressions via its store argument
    (as `concreteEval` does), which is the intended contract for a single-state
    evaluator being lifted. -/
def ExprEval.withOld (eval : ExprEval) : ExprEval₂ := fun σ_old σ_cur e =>
  let (e', binds, _) := Expr.rewriteOld e 0
  match binds.foldlM
      (fun σ (nv : String × Expr) => (eval σ_old nv.2).map (σ.update nv.1)) σ_cur with
  | some σ' => eval σ' e'
  | none => none

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

The configuration-level relation `Config → Config → Prop` over `(pc, store)`
pairs is `StepConfig` (below); its `ReflTrans` closure is `StepInstrStar`, which
is what closure-level properties use. `StepInstr` itself is kept in the spread
`pc σ pc' σ'` form because its constructors are naturally per-`(pc, instruction)`.
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
    (instrGuard prog pc).bind (eval σ ·) = some (.bool true) →
    findLocIdx prog.instructions tgt = some tgtIdx →
    StepInstr callResult eval fenv prog pc σ tgtIdx σ

  /-- **GOTO (not taken)**: Guard is false, fall through. -/
  | goto_not_taken :
    instrType prog pc = some .GOTO →
    (instrGuard prog pc).bind (eval σ ·) = some (.bool false) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSUME (pass)**: Guard is true, advance.
      When the guard is false, there is no derivation — the execution path
      is infeasible (CBMC models this as a non-failing guarded self-loop). -/
  | assume_pass :
    instrType prog pc = some .ASSUME →
    (instrGuard prog pc).bind (eval σ ·) = some (.bool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSERT (pass)**: Guard is true, advance normally. -/
  | assert_pass :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.bool true) →
    StepInstr callResult eval fenv prog pc σ (pc + 1) σ

  /-- **ASSERT (fail)**: Guard is false, advance (CBMC continues after failures).
      The assertion failure is observable via `AssertFails` below. -/
  | assert_fail :
    instrType prog pc = some .ASSERT →
    (instrGuard prog pc).bind (eval σ ·) = some (.bool false) →
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

/-! ## Step Closures -/

/-- A GOTO configuration: program counter paired with the variable store. -/
abbrev Config := Nat × Store

/-- Single-instruction transition on configurations — `StepInstr` on the paired
    `(pc, store)` state, so it can be closed under `ReflTrans`. -/
def StepConfig (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (c c' : Config) : Prop :=
  StepInstr callResult eval fenv prog c.1 c.2 c'.1 c'.2

/-- Multi-step execution: the reflexive-transitive closure of single
    instruction steps. It is often more convenient to state closure-level
    properties (progress/preservation chains, and the Phase-2 simulation) over
    `StepInstrStar` than to unfold `ExecProg`/`Reachable`. -/
def StepInstrStar (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) : Config → Config → Prop :=
  ReflTrans (StepConfig callResult eval fenv prog)

/-! ## Assertion Safety -/

/-- An assertion fails at `pc` in store `σ`. -/
def AssertFails (eval : ExprEval) (prog : Program) (pc : Nat) (σ : Store) : Prop :=
  instrType prog pc = some .ASSERT ∧
  (instrGuard prog pc).bind (eval σ ·) = some (.bool false)

/-- One reachability step: either a genuine `StepInstr`, or advancing one past a
    `SET_RETURN_VALUE` (which `StepInstr` has no rule for — it is handled at the
    `ExecProg` level) leaving the store unchanged. Reachability is the closure of
    this relation. -/
def ReachStep (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (c c' : Config) : Prop :=
  StepInstr callResult eval fenv prog c.1 c.2 c'.1 c'.2 ∨
  (instrType prog c.1 = some .SET_RETURN_VALUE ∧ c' = (c.1 + 1, c.2))

/-- Reachability: `(pc', σ')` is reachable from `(pc, σ)` by zero or more steps
    — the reflexive-transitive closure of `ReachStep`. -/
def Reachable (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (pc : Nat) (σ : Store) (pc' : Nat) (σ' : Store) : Prop :=
  ReflTrans (ReachStep callResult eval fenv prog) (pc, σ) (pc', σ')

/-- Reflexivity of `Reachable` (constructor-style wrapper over `ReflTrans.refl`). -/
theorem Reachable.refl {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store} :
    Reachable callResult eval fenv prog pc σ pc σ :=
  ReflTrans.refl _

/-- Prepend a genuine instruction step to a reachability path. -/
theorem Reachable.step {callResult : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {pc : Nat} {σ : Store} {pc' : Nat} {σ' : Store}
    {pc'' : Nat} {σ'' : Store}
    (h : StepInstr callResult eval fenv prog pc σ pc' σ')
    (r : Reachable callResult eval fenv prog pc' σ' pc'' σ'') :
    Reachable callResult eval fenv prog pc σ pc'' σ'' :=
  ReflTrans.step _ _ _ (Or.inl h) r

/-- Prepend a `SET_RETURN_VALUE` advance (store unchanged) to a reachability path. -/
theorem Reachable.step_set_return_value {callResult : CallResultRel} {eval : ExprEval}
    {fenv : FuncEnv} {prog : Program} {pc : Nat} {σ : Store} {pc'' : Nat} {σ'' : Store}
    (htype : instrType prog pc = some .SET_RETURN_VALUE)
    (r : Reachable callResult eval fenv prog (pc + 1) σ pc'' σ'') :
    Reachable callResult eval fenv prog pc σ pc'' σ'' :=
  ReflTrans.step _ _ _ (Or.inr ⟨htype, rfl⟩) r

/-- A program is safe if no reachable state has a failing assertion. -/
def ProgramSafe (callResult : CallResultRel) (eval : ExprEval) (fenv : FuncEnv)
    (prog : Program) (σ₀ : Store) : Prop :=
  ∀ pc σ,
    Reachable callResult eval fenv prog 0 σ₀ pc σ →
    ¬ AssertFails eval prog pc σ

end -- public section

end CProverGOTO.Semantics

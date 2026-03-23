/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
public import Strata.DL.Imperative.StmtSemantics
public import Strata.DL.Util.Relations

---------------------------------------------------------------------

namespace Imperative

public section

/-! ## Program Counter

A `ProgramCounter` is a stack of natural-number indices that locates a
sub-statement inside a (possibly nested) statement list.

The list is stored in *innermost-first* order: the head is the index of
the current statement within its immediately enclosing list, and the tail
records the positions of the enclosing scopes outward.

- `[]` — no position information (e.g., a bare statement with no list context).
- `[i]` — the `i`-th statement in a single (non-nested) list.
- `[j, i]` — the `j`-th statement inside a block that is itself the
  `i`-th statement of the outer list.

For example, given a block `{ s0; s1; { t0; t1; t2 }; s3 }`:
- `[1]` refers to `s1`
- `[0, 2]` refers to `t0` (the first statement inside the block at
  outer index 2)

This convention makes the common operations cheap:
- *Advance to next sibling*: increment the head.
- *Enter a nested scope*: push `0` onto the front.
- *Leave a scope*: pop the head.
-/

/-- A program counter: a stack of indices into nested statement lists,
    innermost-first. -/
abbrev ProgramCounter := List Nat

/-- Helper: look up a sub-statement given a path in outermost-first order.
    This is the natural recursive form; `resolve` below reverses the
    innermost-first PC before calling this.

    For `ite` nodes the path consumes *two* indices: the first selects the
    `ite` statement in the enclosing list, and the second selects the branch
    (`0` = then, `1` = else).  The remaining path then indexes into the
    chosen branch's statement list. -/
private def ProgramCounter.resolveAux {P : PureExpr} {CmdT : Type}
    (path : List Nat) (ss : List (Stmt P CmdT)) : Option (Stmt P CmdT) :=
  match path with
  | [] => none
  | [i] => ss[i]?
  | i :: rest =>
    match ss[i]? with
    | some (.block _ body _) => resolveAux rest body
    | some (.ite _ thenb elseb _) =>
      -- `rest` starts with a branch selector: 0 = then, 1 = else
      match rest with
      | 0 :: rest' => resolveAux rest' thenb
      | 1 :: rest' => resolveAux rest' elseb
      | _ => none
    | some (.loop _ _ _ body _) => resolveAux rest body
    | _ => none

/-- Look up the sub-statement at a given program counter within a statement
    list. The PC is stored innermost-first, so we reverse it to get the
    outermost-first traversal order.  Returns `none` if any index is out
    of bounds or the path tries to descend into a non-block statement. -/
def ProgramCounter.resolve {P : PureExpr} {CmdT : Type}
    (pc : ProgramCounter) (ss : List (Stmt P CmdT)) : Option (Stmt P CmdT) :=
  resolveAux pc.reverse ss

/-- Look up the sub-statement at a given program counter starting from
    a single statement. `[]` refers to the statement itself.
    For `ite` nodes, the first element of the (reversed) path selects the
    branch (`0` = then, `1` = else), matching the convention in `resolveAux`. -/
def ProgramCounter.resolveStmt {P : PureExpr} {CmdT : Type}
    (pc : ProgramCounter) (s : Stmt P CmdT) : Option (Stmt P CmdT) :=
  match pc with
  | [] => some s
  | _ =>
    match s with
    | .block _ inner _ => resolve pc inner
    | .ite _ thenb elseb _ =>
      -- The reversed PC's head is the branch selector (0=then, 1=else),
      -- tail indexes into the chosen branch.
      match pc.reverse with
      | 0 :: rest => resolveAux rest thenb
      | 1 :: rest => resolveAux rest elseb
      | _ => none
    | .loop _ _ _ body _ => resolve pc body
    | _ => none

/-! ## Small-Step Operational Semantics for Statements

This module defines small-step operational semantics for the Imperative
dialect's statement constructs.

Key design decisions:
- `Config.seq` enables truly small-step processing of statement lists.
  Without it, `step_stmt_cons` required the first statement to reach
  terminal in a single step, which prevented blocks (multi-step) from
  being processed inside statement lists.
- `Config.block` holds an inner `Config` (not a statement list + store),
  allowing blocks to observe the execution state of their body at each step.
- `assert` is a skip in the operational semantics (`eval_assert` has no
  precondition). Assertion checking is handled by the verification framework,
  not by execution.
- Each `stmt` and `stmts` configuration carries a `ProgramCounter` that
  records the position of the current statement within the overall program.
  The PC is observational — it does not affect execution, but allows
  external analyses (e.g., `isAtAssert`) to identify program locations.
  The PC is stored innermost-first (head = current index in enclosing list).
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of:
- The current statement (or list of statements) being executed
- The current store
- The current expression evaluator (threaded to support funcDecl)
- A program counter recording the position in the overall program
  (innermost-first stack of indices)
-/
inductive Config (P : PureExpr) (CmdT : Type) : Type where
  /-- A single statement to execute next, with its program counter. -/
  | stmt : Stmt P CmdT → SemanticStore P → SemanticEval P → ProgramCounter → Config P CmdT
  /-- A list of statements to execute next, in order.
      The PC records the position of the list head. -/
  | stmts : List (Stmt P CmdT) → SemanticStore P → SemanticEval P → ProgramCounter → Config P CmdT
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : SemanticStore P → SemanticEval P → Config P CmdT
  /-- An exiting configuration, indicating that an exit statement was encountered.
      The optional label identifies which block to exit to. -/
  | exiting : Option String → SemanticStore P → SemanticEval P → Config P CmdT
  /-- A block context: execute the inner config, then consume matching exits.
      The string is the block label. -/
  | block : String → Config P CmdT → Config P CmdT
  /-- A sequence context: execute the first statement (as a sub-config), then
      continue with the remaining statements. Carries the PC that the
      remaining tail should use when it becomes the active `stmts`. -/
  | seq : Config P CmdT → List (Stmt P CmdT) → ProgramCounter → Config P CmdT


/--
Small-step operational semantics for statements. The relation `StepStmt`
defines a single execution step from one configuration to another.
The expression evaluator is part of the configuration and can be extended
by funcDecl statements.

### Program-counter update rules

The PC is a stack (innermost-first).  The step rules maintain it as follows:

- **`step_stmts_cons`**: splitting `s :: ss` at PC `i :: ctx`.
  The head `s` inherits `i :: ctx`.  The tail `ss` gets `(i+1) :: ctx`.
- **`step_block`**: entering a block body pushes a new scope:
  `0 :: pc` (start at index 0 inside the block).
- **`step_ite_true`**: entering the then branch pushes two levels:
  `0 :: 0 :: pc` (stmt-index 0, branch-selector 0 = then).
- **`step_ite_false`**: entering the else branch pushes two levels:
  `0 :: 1 :: pc` (stmt-index 0, branch-selector 1 = else).
- **`step_loop_enter`**: entering the unrolled body pushes a new scope:
  `0 :: pc`.
- **`step_seq_done`**: the tail resumes with its stored `tailPc`.
- All other rules either preserve or discard the PC (terminal/exiting
  configurations carry no PC).
-/
inductive StepStmt
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P] :
  Config P CmdT → Config P CmdT → Prop where

  /-- A command steps to terminal configuration if it evaluates successfully.
      Commands preserve the evaluator (δ' = δ). -/
  | step_cmd :
    EvalCmd δ σ c σ' →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.cmd c) σ δ pc)
      (.terminal σ' δ)

  /-- A labeled block steps to a block context that wraps its body as `.stmts`.
      Entering the block body pushes a new scope: the body starts at index 0
      inside the block, so the new PC is `0 :: pc`. -/
  | step_block :
    StepStmt P EvalCmd extendEval
      (.stmt (.block label ss _) σ δ pc)
      (.block label (.stmts ss σ δ (0 :: pc)))

  /-- If the condition of an `ite` statement evaluates to true, step to the
      then branch.  Entering the then branch pushes two levels onto the PC:
      `0 :: 0 :: pc` — the first `0` is the statement index within the branch,
      and the second `0` is the branch selector (0 = then). -/
  | step_ite_true :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.ite c tss ess _) σ δ pc)
      (.stmts tss σ δ (0 :: 0 :: pc))

  /-- If the condition of an `ite` statement evaluates to false, step to the
      else branch.  Entering the else branch pushes two levels onto the PC:
      `0 :: 1 :: pc` — the first `0` is the statement index within the branch,
      and the `1` is the branch selector (1 = else). -/
  | step_ite_false :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.ite c tss ess _) σ δ pc)
      (.stmts ess σ δ (0 :: 1 :: pc))

  /-- If a loop guard is true, execute the body (followed by the loop again).
      Entering the unrolled body pushes a new scope: `0 :: pc`. -/
  | step_loop_enter :
    δ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.loop g m inv body md) σ δ pc)
      (.stmts (body ++ [.loop g m inv body md]) σ δ (0 :: pc))

  /-- If a loop guard is false, terminate the loop. -/
  | step_loop_exit :
    δ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    StepStmt P EvalCmd extendEval
      (.stmt (.loop g m inv body _) σ δ pc)
      (.terminal σ δ)

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
    StepStmt P EvalCmd extendEval
      (.stmt (.exit label _) σ δ pc)
      (.exiting label σ δ)

  /-- A function declaration extends the evaluator with the new function. -/
  | step_funcDecl [HasSubstFvar P] [HasVarsPure P P.Expr] :
    StepStmt P EvalCmd extendEval
      (.stmt (.funcDecl decl md) σ δ pc)
      (.terminal σ (extendEval δ σ decl))

  /-- A type declaration is a no-op at runtime. -/
  | step_typeDecl :
    StepStmt P EvalCmd extendEval
      (.stmt (.typeDecl _tc _md) σ δ pc)
      (.terminal σ δ)

  /-- An empty list of statements steps to `.terminal` with no state changes. -/
  | step_stmts_nil :
    StepStmt P EvalCmd extendEval
      (.stmts [] σ δ pc)
      (.terminal σ δ)

  /-- To evaluate a non-empty sequence, enter a seq context that processes
      the first statement while remembering the remaining statements.
      The head statement inherits the current PC `pc`.
      The tail gets `tailPc` where the head index is incremented:
      if `pc = i :: ctx` then `tailPc = (i+1) :: ctx`;
      if `pc = []` then `tailPc = []` (no position info). -/
  | step_stmts_cons :
    pc' = (match pc with | i :: ctx => (i + 1) :: ctx | [] => []) →
    ----
    StepStmt P EvalCmd extendEval
      (.stmts (s :: ss) σ δ pc)
      (.seq (.stmt s σ δ pc) ss pc')

  /-- A seq context steps its inner config forward. -/
  | step_seq_inner :
    StepStmt P EvalCmd extendEval inner inner' →
    ----
    StepStmt P EvalCmd extendEval
      (.seq inner ss tailPc)
      (.seq inner' ss tailPc)

  /-- When the inner config of a seq reaches terminal, continue with the
      remaining statements using the tail PC. -/
  | step_seq_done :
    StepStmt P EvalCmd extendEval
      (.seq (.terminal σ' δ') ss tailPc)
      (.stmts ss σ' δ' tailPc)

  /-- When the inner config of a seq exits, propagate the exit
      (skip remaining statements). -/
  | step_seq_exit :
    StepStmt P EvalCmd extendEval
      (.seq (.exiting label σ' δ') ss _tailPc)
      (.exiting label σ' δ')

  /-- A block context steps its inner body one step forward.
      The inner body can be any config (stmts, seq, etc.). -/
  | step_block_body :
    StepStmt P EvalCmd extendEval inner inner' →
    ----
    StepStmt P EvalCmd extendEval
      (.block label inner)
      (.block label inner')

  /-- When a block's inner body reaches terminal, the block terminates. -/
  | step_block_done :
    StepStmt P EvalCmd extendEval
      (.block label (.terminal σ' δ'))
      (.terminal σ' δ')

  /-- When a block's inner body exits with no label, the block consumes the exit. -/
  | step_block_exit_none :
    StepStmt P EvalCmd extendEval
      (.block label (.exiting .none σ' δ'))
      (.terminal σ' δ')

  /-- When a block's inner body exits with a matching label, the block consumes it. -/
  | step_block_exit_match :
    l = label →
    ----
    StepStmt P EvalCmd extendEval
      (.block label (.exiting (.some l) σ' δ'))
      (.terminal σ' δ')

  /-- When a block's inner body exits with a non-matching label, the exit propagates. -/
  | step_block_exit_mismatch :
    l ≠ label →
    ----
    StepStmt P EvalCmd extendEval
      (.block label (.exiting (.some l) σ' δ'))
      (.exiting (.some l) σ' δ')


/-! ## Multi-step execution: reflexive transitive closure of single steps. -/

section

variable
  {CmdT : Type}
  (P : PureExpr)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P CmdT))]
  [HasVarsImp P CmdT] [HasFvar P] [HasVal P]
  [HasBool P] [HasNot P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)

abbrev StepStmtStar :
    Config P CmdT → Config P CmdT → Prop :=
  ReflTrans (StepStmt P EvalCmd extendEval)

/-- A statement evaluates successfully if it can step from *some* initial PC
    to a terminal configuration. -/
def EvalStmtSmall
    (δ : SemanticEval P) (σ : SemanticStore P) (s : Stmt P CmdT)
    (σ' : SemanticStore P) (δ' : SemanticEval P) : Prop :=
  ∃ pc : ProgramCounter,
    StepStmtStar P EvalCmd extendEval (.stmt s σ δ pc) (.terminal σ' δ')

/-- A list of statements evaluates successfully if it can step from *some*
    initial PC to a terminal configuration. -/
def EvalStmtsSmall
    (δ : SemanticEval P) (σ : SemanticStore P) (ss : List (Stmt P CmdT))
    (σ' : SemanticStore P) (δ' : SemanticEval P) : Prop :=
  ∃ pc : ProgramCounter,
    StepStmtStar P EvalCmd extendEval (.stmts ss σ δ pc) (.terminal σ' δ')

---------------------------------------------------------------------

/-! ## Basic Properties and Theorems -/

/-- Empty statement list evaluation. -/
theorem evalStmtsSmallNil
    (δ : SemanticEval P) (σ : SemanticStore P) :
    EvalStmtsSmall P EvalCmd extendEval δ σ [] σ δ := by
  unfold EvalStmtsSmall
  exact ⟨[], .step _ _ _ StepStmt.step_stmts_nil (.refl _)⟩

/-- Configuration is terminal if no further steps are possible. -/
def IsTerminal
    (c : Config P CmdT) : Prop :=
  ∀ c', ¬ StepStmt P EvalCmd extendEval c c'

/-- Terminal configurations are indeed terminal. -/
theorem terminalIsTerminal
    (σ : SemanticStore P) (δ : SemanticEval P) :
    IsTerminal P EvalCmd extendEval (.terminal σ δ) := by
  unfold IsTerminal
  intro c' h
  cases h

/-!
### Stepping through a statement list

When executing `.stmts (s :: ss) σ δ pc`, the semantics first enters a
`.seq` context (via `step_stmts_cons`), executes `s` to terminal, then
resumes with `.stmts ss σ' δ' pc'` where `pc'` has its head index
incremented by one.

The proof proceeds in two parts:
1. A helper lemma (`seq_inner_star`) showing that multi-step execution of
   the inner config lifts to multi-step execution of the enclosing `.seq`.
2. The main theorem (`stmts_cons_step`) composing the pieces.
-/

/-- Transitivity of `ReflTrans`: if `r* x y` and `r* y z` then `r* x z`.
    This is a local helper that avoids the opaque `Transitive` wrapper
    from `Relations.lean` (which becomes opaque across module boundaries). -/
private theorem reflTrans_trans {r : Relation A}
    {x y z : A} (h1 : ReflTrans r x y) (h2 : ReflTrans r y z) :
    ReflTrans r x z := by
  induction h1 with
  | refl => exact h2
  | step _ mid _ hstep _ ih => exact .step _ mid _ hstep (ih h2)

/-- Helper: if the inner config of a `.seq` takes multiple steps, the
    enclosing `.seq` takes the same number of steps.
    Proved by induction on the multi-step derivation. -/
theorem seq_inner_star
    (inner inner' : Config P CmdT)
    (ss : List (Stmt P CmdT))
    (tailPc : ProgramCounter)
    (h : StepStmtStar P EvalCmd extendEval inner inner') :
    StepStmtStar P EvalCmd extendEval
      (.seq inner ss tailPc)
      (.seq inner' ss tailPc) := by
  induction h with
  | refl => exact .refl _
  | step _ mid _ hstep _ ih =>
    exact .step _ _ _ (.step_seq_inner hstep) ih

/-- When executing `.stmts (s :: ss) σ δ pc`, if the head statement `s`
    multi-steps to `.terminal σ' δ'`, then the whole list multi-steps to
    `.stmts ss σ' δ' pc'` where `pc'` is `pc` with its head index
    incremented by one:
    - if `pc = i :: ctx` then `pc' = (i + 1) :: ctx`
    - if `pc = []` then `pc' = []`

    This captures the fundamental sequencing behaviour of statement lists
    in the small-step semantics. -/
theorem stmts_cons_step
    (s : Stmt P CmdT) (ss : List (Stmt P CmdT))
    (σ σ' : SemanticStore P) (δ δ' : SemanticEval P)
    (pc : ProgramCounter)
    (hstmt : StepStmtStar P EvalCmd extendEval
      (.stmt s σ δ pc) (.terminal σ' δ')) :
    let pc' := match pc with | i :: ctx => (i + 1) :: ctx | [] => []
    StepStmtStar P EvalCmd extendEval
      (.stmts (s :: ss) σ δ pc)
      (.stmts ss σ' δ' pc') := by
  intro pc'
  -- Step 1: .stmts (s :: ss) σ δ pc  →  .seq (.stmt s σ δ pc) ss pc'
  --         via step_stmts_cons
  apply ReflTrans.step _ (.seq (.stmt s σ δ pc) ss pc')
  · exact .step_stmts_cons (by cases pc <;> rfl)
  -- Step 2: .seq (.stmt s σ δ pc) ss pc'  →*  .seq (.terminal σ' δ') ss pc'
  --         by lifting hstmt through the seq context
  have h2 := seq_inner_star P EvalCmd extendEval _ _ ss pc' hstmt
  -- Step 3: .seq (.terminal σ' δ') ss pc'  →  .stmts ss σ' δ' pc'
  --         via step_seq_done, then chain with h2 by induction
  suffices h3 : StepStmtStar P EvalCmd extendEval
      (.seq (.terminal σ' δ') ss pc') (.stmts ss σ' δ' pc') from
    reflTrans_trans h2 h3
  exact .step _ _ _ .step_seq_done (.refl _)

end -- section

end -- public section
end Imperative

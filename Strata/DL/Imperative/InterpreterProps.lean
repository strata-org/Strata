/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.Interpreter

/-! # Monadic interpreter: single-step reduction lemmas

Monad-generic equation lemmas for the engine of `Interpreter.lean` (`runInterp`,
`stepInterp`, `stepBaseCmdStore`), so proofs can reason about a run one step at a time
without unfolding the driver by hand. Key theorems: `runInterp_terminal`,
`runInterp_exiting` and `runInterp_succ_nonterminal` (the driver at a stopping
configuration and at successor fuel), `runInterp_zero_stmt` and `runInterp_succ_stmt` (the driver
on a `.stmt` configuration at zero and successor fuel), the `stepInterp_*` equations for each
configuration shape, and the `stepBaseCmdStore_*` equations for each base command. -/

namespace Imperative

public section

variable {P : PureExpr} {CmdT : Type} {m : Type → Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- `runInterp` halts on a terminal configuration. -/
@[simp] theorem runInterp_terminal (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (env : IEnv P) : runInterp stepCmd fuel (.terminal env) = pure (.terminal env) := by
  rw [runInterp]

/-- `runInterp` halts on an exiting configuration. -/
@[simp] theorem runInterp_exiting (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : String) (env : IEnv P) :
    runInterp stepCmd fuel (.exiting label env) = pure (.exiting label env) := by rw [runInterp]

/-- `runInterp` out of fuel on a non-terminal configuration throws. -/
theorem runInterp_zero_stmt (stepCmd : StepCmdM P CmdT m)
    (stmt : Stmt P CmdT) (env : IEnv P) :
    runInterp stepCmd 0 (.stmt stmt env) = throw .replayFuelExhausted := (rfl)

/-- One driver step on a `.stmt` config at successor fuel: step once, then recurse. -/
theorem runInterp_succ_stmt (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (stmt : Stmt P CmdT) (env : IEnv P) :
    runInterp stepCmd (fuel + 1) (.stmt stmt env)
      = stepInterp stepCmd (fuel + 1) (.stmt stmt env) >>= runInterp stepCmd fuel := (rfl)

/-- `stepInterp` on a base-`cmd` statement delegates to the command stepper. -/
@[simp] theorem stepInterp_stmt_cmd (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (cmd : CmdT) (env : IEnv P) :
    stepInterp stepCmd fuel (.stmt (.cmd cmd) env) = stepCmd fuel env cmd := (rfl)

/-- `stepInterp` on a statement list of at least two statements opens a `.seq`. -/
@[simp] theorem stepInterp_stmts_cons (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (stmt next : Stmt P CmdT) (rest : List (Stmt P CmdT)) (env : IEnv P) :
    stepInterp stepCmd fuel (.stmts (stmt :: next :: rest) env)
      = pure (.seq (.stmt stmt env) (next :: rest)) := (rfl)

/-- `stepInterp` on a one-statement list opens a sequence tower of height one. -/
@[simp] theorem stepInterp_stmts_single (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (stmt : Stmt P CmdT) (env : IEnv P) :
    stepInterp stepCmd fuel (.stmts [stmt] env) = pure (.seqs (.stmt stmt env) 0) := (rfl)

/-- `stepInterp` on an empty statement list terminates. -/
@[simp] theorem stepInterp_stmts_nil (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (env : IEnv P) :
    stepInterp stepCmd fuel (.stmts [] env) = pure (.terminal env) := (rfl)

/-- `stepInterp` on a `.seq` whose head is terminal advances to the tail list. -/
@[simp] theorem stepInterp_seq_terminal (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (env : IEnv P) (rest : List (Stmt P CmdT)) :
    stepInterp stepCmd fuel (.seq (.terminal env) rest) = pure (.stmts rest env) := (rfl)

/-- `stepInterp` on a `.seq` whose head is a `.stmt` steps the head, keeping the tail. -/
@[simp] theorem stepInterp_seq_stmt (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (stmt : Stmt P CmdT) (env : IEnv P) (rest : List (Stmt P CmdT)) :
    stepInterp stepCmd fuel (.seq (.stmt stmt env) rest)
      = stepInterp stepCmd fuel (.stmt stmt env) >>= fun i => pure (.seq i rest) := (rfl)

/-- `stepInterp` on a `.stmt (.block …)` opens the block scope. -/
@[simp] theorem stepInterp_stmt_block (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : String) (body : List (Stmt P CmdT)) (md) (env : IEnv P) :
    stepInterp stepCmd fuel (.stmt (.block label body md) env)
      = pure (.block (some label) (.opened env.store) (.stmts body env)) := (rfl)

/-- `stepInterp` on a `.block` whose inner is terminal exits the block through its frame. -/
@[simp] theorem stepInterp_block_terminal (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : Option String) (frame : ScopeFrame P)
    (env : IEnv P) :
    stepInterp stepCmd fuel (.block label frame (.terminal env))
      = pure (.terminal { env with store := frame.exit env.store }) := (rfl)

/-- `stepInterp` on a `.block` whose inner is a `.stmt` steps the inner, recording the step in the
    frame. -/
@[simp] theorem stepInterp_block_stmt (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : Option String) (frame : ScopeFrame P)
    (stmt : Stmt P CmdT) (env : IEnv P) :
    stepInterp stepCmd fuel (.block label frame (.stmt stmt env))
      = stepInterp stepCmd fuel (.stmt stmt env) >>= fun i =>
          pure (.block label (frame.record (IConfig.stmt stmt env).levelCmd?) i) := (rfl)

/-- `stepBaseCmdStore` on an `assert` emits its events and leaves the store unchanged. -/
@[simp] theorem stepBaseCmdStore_assert (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (label : String) (e : P.Expr) (md) :
    stepBaseCmdStore (m := m) fuel factory store (.assert label e md)
      = (do
          (Cmd.rEmittedEvents (P := P) (.assert label e md) factory store.get).forM
            (InterpEffects.emit (P := P))
          pure store) := (rfl)

/-- `stepBaseCmdStore` on an `assume` emits its events and leaves the store unchanged. -/
@[simp] theorem stepBaseCmdStore_assume (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (label : String) (e : P.Expr) (md) :
    stepBaseCmdStore (m := m) fuel factory store (.assume label e md)
      = (do
          (Cmd.rEmittedEvents (P := P) (.assume label e md) factory store.get).forM
            (InterpEffects.emit (P := P))
          pure store) := (rfl)

/-- `stepBaseCmdStore` on a `cover` emits its events and leaves the store unchanged. -/
@[simp] theorem stepBaseCmdStore_cover (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (label : String) (e : P.Expr) (md) :
    stepBaseCmdStore (m := m) fuel factory store (.cover label e md)
      = (do
          (Cmd.rEmittedEvents (P := P) (.cover label e md) factory store.get).forM
            (InterpEffects.emit (P := P))
          pure store) := (rfl)

/-- `stepBaseCmdStore` on a successful deterministic `init` (target undefined, RHS
    evaluates to a well-typed value) updates the store at that variable. -/
theorem stepBaseCmdStore_init_det [LawfulMonad m] (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (name : P.Ident) (ty : P.Ty) (e : P.Expr) (md) (v : P.Expr)
    (hu : store.get name = none)
    (he : InterpLang.boundedEval (P := P) fuel factory store.get e = some v)
    (ht : ((InterpLang.ops (P := P)).isValue factory v
            && (InterpLang.ops (P := P)).hasType factory v ty) = true) :
    stepBaseCmdStore (m := m) fuel factory store (.init name ty (.det e) md)
      = pure (store.update name v) := by grind [stepBaseCmdStore]

/-- `stepBaseCmdStore` on a successful deterministic `set` (target defined, RHS
    evaluates to a same-typed value) updates the store at that variable. -/
theorem stepBaseCmdStore_set_det [LawfulMonad m] (fuel : Nat) (factory : InterpLang.RFactory P)
    (store : IStore P) (name : P.Ident) (e : P.Expr) (md) (old v : P.Expr)
    (hd : store.get name = some old)
    (he : InterpLang.boundedEval (P := P) fuel factory store.get e = some v)
    (ht : ((InterpLang.ops (P := P)).isValue factory v
            && (InterpLang.ops (P := P)).sameType factory old v) = true) :
    stepBaseCmdStore (m := m) fuel factory store (.set name (.det e) md)
      = pure (store.update name v) := by grind [stepBaseCmdStore]

end -- public section

end Imperative

namespace Imperative
attribute [-simp] bind_pure_comp
open Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [DecidableEq P.Ident] [InterpLang P] [CmdDefs P CmdT]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]

/-- At successor fuel, `runInterp` on a non-terminal, non-exiting configuration is one step bound
    into the tail. -/
theorem runInterp_succ_nonterminal {m : Type → Type} [Monad m] [InterpEffects P m]
    [MonadExcept StopReason m] (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (cfg : IConfig P CmdT) (hnt : ∀ e, cfg ≠ .terminal e) (hex : ∀ l e, cfg ≠ .exiting l e) :
    runInterp stepCmd (fuel + 1) cfg
      = (stepInterp stepCmd (fuel + 1) cfg >>= runInterp stepCmd fuel) := by cases cfg <;> simp_all!

end
end Imperative

namespace Imperative
attribute [-simp] bind_pure_comp
open Imperative
public section
variable {P : PureExpr} {CmdT : Type}
variable [HasBool P] [DecidableEq P.Expr] [InterpLang P]
    [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable {m : Type → Type} [Monad m] [InterpEffects P m] [MonadExcept StopReason m]
variable [HasBoolOps P] [HasFvar P] [DecidableEq P.Ident]
section StepGeneric
variable {P : PureExpr} {m : Type → Type} {CmdT : Type}
variable [HasBool P] [HasBoolOps P] [HasFvar P] [DecidableEq P.Expr] [DecidableEq P.Ident]
    [InterpLang P] [CmdDefs P CmdT] [Monad m] [LawfulMonad m] [InterpEffects P m]
    [MonadExcept StopReason m]

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- `stepInterp` on a `.seq` whose head is neither terminal nor exiting steps the head, keeping
    the tail. -/
theorem stepInterp_seq_unfold_gen (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (inner : IConfig P CmdT) (rest : List (Stmt P CmdT))
    (hnt : ∀ e, inner ≠ IConfig.terminal e) (hex : ∀ l e, inner ≠ IConfig.exiting l e) :
    stepInterp stepCmd fuel (.seq inner rest)
      = (stepInterp stepCmd fuel inner >>= fun i => pure (.seq i rest)) := by
  cases inner <;> simp_all!

omit [HasBoolOps P] [HasFvar P] [LawfulMonad m] in
/-- `stepInterp` on a `.block` whose inner configuration is neither terminal nor exiting steps
    the inner configuration, recording the step in the frame. -/
theorem stepInterp_block_unfold_gen (stepCmd : StepCmdM P CmdT m) (fuel : Nat)
    (label : Option String) (frame : ScopeFrame P) (inner : IConfig P CmdT)
    (hnt : ∀ e, inner ≠ IConfig.terminal e) (hex : ∀ l e, inner ≠ IConfig.exiting l e) :
    stepInterp stepCmd fuel (.block label frame inner)
      = (stepInterp stepCmd fuel inner >>= fun i =>
          pure (.block label (frame.record inner.levelCmd?) i)) := by
  cases inner <;> simp_all!

end StepGeneric
end
end Imperative

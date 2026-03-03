/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Tests for Laurel Operational Semantics

Concrete evaluation tests using `example` proofs to demonstrate that the
semantic rules produce expected results for each major construct.
-/

namespace Strata.Laurel.Test

open Strata.Laurel

/-! ## Test Helpers -/

abbrev emd : Imperative.MetaData Core.Expression := .empty

def mk (s : StmtExpr) : StmtExprMd := ⟨s, emd⟩

def emptyStore : LaurelStore := fun _ => none
def emptyHeap : LaurelHeap := fun _ => none
def emptyProc : ProcEnv := fun _ => none

def trivialEval : LaurelEval := fun σ e =>
  match e with
  | .Identifier name => σ name
  | .LiteralInt i => some (.vInt i)
  | .LiteralBool b => some (.vBool b)
  | .LiteralString s => some (.vString s)
  | _ => none

def singleStore (name : Identifier) (v : LaurelValue) : LaurelStore :=
  fun x => if x == name then some v else none

/-! ## Literal Tests -/

example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.LiteralInt 42)) emptyHeap emptyStore (.normal (.vInt 42)) :=
  .literal_int

example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.LiteralBool true)) emptyHeap emptyStore (.normal (.vBool true)) :=
  .literal_bool

example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.LiteralString "hello")) emptyHeap emptyStore (.normal (.vString "hello")) :=
  .literal_string

/-! ## Identifier Test -/

example : EvalLaurelStmt trivialEval emptyProc emptyHeap (singleStore "x" (.vInt 7))
    (mk (.Identifier "x")) emptyHeap (singleStore "x" (.vInt 7)) (.normal (.vInt 7)) :=
  .identifier (by simp [singleStore])

/-! ## PrimitiveOp Tests -/

-- 2 + 3 = 5
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.PrimitiveOp .Add [mk (.LiteralInt 2), mk (.LiteralInt 3)]))
    emptyHeap emptyStore (.normal (.vInt 5)) :=
  .prim_op (.cons (by rfl) (.cons (by rfl) .nil)) (by rfl)

-- true && false = false
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.PrimitiveOp .And [mk (.LiteralBool true), mk (.LiteralBool false)]))
    emptyHeap emptyStore (.normal (.vBool false)) :=
  .prim_op (.cons (by rfl) (.cons (by rfl) .nil)) (by rfl)

-- !true = false
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.PrimitiveOp .Not [mk (.LiteralBool true)]))
    emptyHeap emptyStore (.normal (.vBool false)) :=
  .prim_op (.cons (by rfl) .nil) (by rfl)

-- 5 < 10 = true
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.PrimitiveOp .Lt [mk (.LiteralInt 5), mk (.LiteralInt 10)]))
    emptyHeap emptyStore (.normal (.vBool true)) :=
  .prim_op (.cons (by rfl) (.cons (by rfl) .nil)) (by rfl)

-- "a" ++ "b" = "ab"
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.PrimitiveOp .StrConcat [mk (.LiteralString "a"), mk (.LiteralString "b")]))
    emptyHeap emptyStore (.normal (.vString "ab")) :=
  .prim_op (.cons (by rfl) (.cons (by rfl) .nil)) (by rfl)

/-! ## Block Tests -/

-- Empty block evaluates to void
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [] none)) emptyHeap emptyStore (.normal .vVoid) :=
  .block_sem .nil (by rfl)

-- Singleton block returns its value
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.LiteralInt 99)] none)) emptyHeap emptyStore (.normal (.vInt 99)) :=
  .block_sem (.last_normal .literal_int) (by rfl)

-- Block with two statements: value is the last one
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.LiteralInt 1), mk (.LiteralInt 2)] none))
    emptyHeap emptyStore (.normal (.vInt 2)) :=
  .block_sem (.cons_normal .literal_int (.last_normal .literal_int)) (by rfl)

/-! ## IfThenElse Tests -/

-- if true then 1 else 2 => 1
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.IfThenElse (mk (.LiteralBool true)) (mk (.LiteralInt 1)) (some (mk (.LiteralInt 2)))))
    emptyHeap emptyStore (.normal (.vInt 1)) :=
  .ite_true .literal_bool .literal_int

-- if false then 1 else 2 => 2
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.IfThenElse (mk (.LiteralBool false)) (mk (.LiteralInt 1)) (some (mk (.LiteralInt 2)))))
    emptyHeap emptyStore (.normal (.vInt 2)) :=
  .ite_false .literal_bool .literal_int

-- if false then 1 => void (no else branch)
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.IfThenElse (mk (.LiteralBool false)) (mk (.LiteralInt 1)) none))
    emptyHeap emptyStore (.normal .vVoid) :=
  .ite_false_no_else .literal_bool

/-! ## Exit Tests -/

-- Exit propagates through block
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.Exit "L"), mk (.LiteralInt 99)] none))
    emptyHeap emptyStore (.exit "L") :=
  .block_sem (.cons_exit .exit_sem) (by rfl)

-- Labeled block catches matching exit
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.Exit "L")] (some "L")))
    emptyHeap emptyStore (.normal .vVoid) :=
  .block_sem (.cons_exit .exit_sem) (by rfl)

-- Labeled block does NOT catch non-matching exit
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.Exit "other")] (some "L")))
    emptyHeap emptyStore (.exit "other") :=
  .block_sem (.cons_exit .exit_sem) (by decide)

/-! ## Return Tests -/

-- Return with value
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Return (some (mk (.LiteralInt 42)))))
    emptyHeap emptyStore (.ret (some (.vInt 42))) :=
  .return_some .literal_int

-- Return without value
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Return none))
    emptyHeap emptyStore (.ret none) :=
  .return_none

-- Return short-circuits block
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [mk (.Return (some (mk (.LiteralInt 1)))), mk (.LiteralInt 99)] none))
    emptyHeap emptyStore (.ret (some (.vInt 1))) :=
  .block_sem (.cons_return (.return_some .literal_int)) (by rfl)

/-! ## LocalVariable Tests -/

-- Declare and initialize a local variable
example : let σ' := singleStore "x" (.vInt 10)
    EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.LocalVariable "x" ⟨.TInt, emd⟩ (some (mk (.LiteralInt 10)))))
    emptyHeap σ' (.normal .vVoid) :=
  .local_var_init .literal_int (by simp [emptyStore])
    (.init (by simp [emptyStore])
           (by simp [singleStore])
           (by intro y hne; simp [singleStore, emptyStore]; intro h; exact absurd h.symm hne))

-- Declare without initializer
example : let σ' := singleStore "y" .vVoid
    EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.LocalVariable "y" ⟨.TBool, emd⟩ none))
    emptyHeap σ' (.normal .vVoid) :=
  .local_var_uninit (by simp [emptyStore])
    (.init (by simp [emptyStore])
           (by simp [singleStore])
           (by intro y hne; simp [singleStore, emptyStore]; intro h; exact absurd h.symm hne))

/-! ## Assert/Assume Tests -/

-- Assert true succeeds
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Assert (mk (.LiteralBool true))))
    emptyHeap emptyStore (.normal .vVoid) :=
  .assert_true .literal_bool

-- Assume true succeeds
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Assume (mk (.LiteralBool true))))
    emptyHeap emptyStore (.normal .vVoid) :=
  .assume_true .literal_bool

/-! ## ProveBy Test -/

-- ProveBy evaluates to the value of its first argument
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.ProveBy (mk (.LiteralInt 5)) (mk (.LiteralBool true))))
    emptyHeap emptyStore (.normal (.vInt 5)) :=
  .prove_by .literal_int

/-! ## Nested Control Flow Tests -/

-- Nested blocks with exit: inner exit propagates to outer labeled block
example : EvalLaurelStmt trivialEval emptyProc emptyHeap emptyStore
    (mk (.Block [
      mk (.Block [mk (.Exit "outer"), mk (.LiteralInt 99)] none),
      mk (.LiteralInt 88)
    ] (some "outer")))
    emptyHeap emptyStore (.normal .vVoid) :=
  .block_sem
    (.cons_exit (.block_sem (.cons_exit .exit_sem) (by rfl)))
    (by rfl)

/-! ## Property Tests -/

-- catchExit preserves normal outcomes
example : catchExit (some "L") (.normal (.vInt 1)) = .normal (.vInt 1) := by rfl

-- catchExit preserves return outcomes
example : catchExit (some "L") (.ret (some (.vInt 1))) = .ret (some (.vInt 1)) := by rfl

-- catchExit catches matching exit
example : catchExit (some "L") (.exit "L") = .normal .vVoid := by rfl

-- catchExit passes through non-matching exit
example : catchExit (some "L") (.exit "M") = .exit "M" := by decide

-- evalPrimOp: integer addition
example : evalPrimOp .Add [.vInt 3, .vInt 4] = some (.vInt 7) := by rfl

-- evalPrimOp: boolean negation
example : evalPrimOp .Not [.vBool false] = some (.vBool true) := by rfl

-- evalPrimOp: division by zero returns none
example : evalPrimOp .Div [.vInt 5, .vInt 0] = none := by rfl

-- evalPrimOp: type mismatch returns none
example : evalPrimOp .Add [.vBool true, .vInt 1] = none := by rfl

-- Empty block is void
example : EvalLaurelBlock trivialEval emptyProc emptyHeap emptyStore
    [] emptyHeap emptyStore (.normal .vVoid) :=
  .nil

end Strata.Laurel.Test

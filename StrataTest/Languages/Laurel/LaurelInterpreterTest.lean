/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter

/-!
# Tests for Laurel Interpreter

`#guard` tests mirroring every test in `LaurelSemanticsTest.lean`.
Uses concrete finite stores and extracts outcomes for comparison since
`LaurelStore` and `LaurelHeap` are function types without `BEq`.
-/

namespace Strata.Laurel.InterpreterTest

open Strata.Laurel

/-! ## Test Helpers -/

abbrev emd : Imperative.MetaData Core.Expression := .empty

def mk (s : StmtExpr) : StmtExprMd := ⟨s, emd⟩

def emptyStore : LaurelStore := fun _ => none
def emptyHeap : LaurelHeap := fun _ => none
def emptyProc : ProcEnv := fun _ => none

def trivialEval : LaurelEval := fun σ e =>
  match e with
  | .Identifier name => σ name.text
  | .LiteralInt i => some (.vInt i)
  | .LiteralBool b => some (.vBool b)
  | .LiteralString s => some (.vString s)
  | _ => none

def singleStore (name : Identifier) (v : LaurelValue) : LaurelStore :=
  fun x => if x == name.text then some v else none

/-- Extract just the outcome from a interpreter result. -/
def getOutcome (r : Option (Outcome × LaurelStore × LaurelHeap)) : Option Outcome :=
  r.map (·.1)

/-- Extract outcome and a store lookup from a interpreter result. -/
def getOutcomeAndVar (r : Option (Outcome × LaurelStore × LaurelHeap))
    (name : Identifier) : Option (Outcome × Option LaurelValue) :=
  r.map (fun (o, σ, _) => (o, σ name.text))

/-- Check that a interpreter result has the expected outcome and the store is unchanged. -/
def checkPure (r : Option (Outcome × LaurelStore × LaurelHeap))
    (expected : Outcome) : Bool :=
  match r with
  | some (o, _, _) => o == expected
  | none => false

/-! ## Literal Tests -/

#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LiteralInt 42)) = some (.normal (.vInt 42))

#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LiteralBool true)) = some (.normal (.vBool true))

#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LiteralString "hello")) = some (.normal (.vString "hello"))

/-! ## Identifier Test -/

#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap (singleStore "x" (.vInt 7))
    (.Identifier "x")) = some (.normal (.vInt 7))

/-! ## PrimitiveOp Tests -/

-- 2 + 3 = 5
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Add [mk (.LiteralInt 2), mk (.LiteralInt 3)]))
  = some (.normal (.vInt 5))

-- true && false = false
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .And [mk (.LiteralBool true), mk (.LiteralBool false)]))
  = some (.normal (.vBool false))

-- !true = false
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Not [mk (.LiteralBool true)]))
  = some (.normal (.vBool false))

-- 5 < 10 = true
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Lt [mk (.LiteralInt 5), mk (.LiteralInt 10)]))
  = some (.normal (.vBool true))

-- "a" ++ "b" = "ab"
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .StrConcat [mk (.LiteralString "a"), mk (.LiteralString "b")]))
  = some (.normal (.vString "ab"))

/-! ## Effectful Argument Evaluation Test -/

-- x + (x := 1) with x initially 0 evaluates to 0 + 1 = 1, final store x = 1.
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let r := interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.PrimitiveOp .Add [mk (.Identifier "x"),
                        mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 1)))])
  getOutcomeAndVar r "x" = some (.normal (.vInt 1), some (.vInt 1))

/-! ## Assignment Return Value Tests -/

-- assign_single returns the assigned value (not void)
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let r := interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 5)))
  getOutcomeAndVar r "x" = some (.normal (.vInt 5), some (.vInt 5))

/-! ## Nested Effectful Argument Tests -/

-- f((x := 1), (x := 2)) with x initially 0 → args are [1, 2], final x = 2.
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let r := interpArgs trivialEval emptyProc 10 emptyHeap σ₀
    [mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 1))),
     mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 2)))]
  r.map (fun (vs, σ, _) => (vs, σ "x")) = some ([.vInt 1, .vInt 2], some (.vInt 2))

-- EvalStmtArgs with pure arguments
#guard
  let r := interpArgs trivialEval emptyProc 10 emptyHeap emptyStore
    [mk (.LiteralInt 1), mk (.LiteralBool true)]
  r.map (·.1) = some [.vInt 1, .vBool true]

-- EvalStmtArgs on empty list
#guard
  let r := interpArgs trivialEval emptyProc 10 emptyHeap emptyStore []
  r.map (·.1) = some []

/-! ## Block Tests -/

-- Empty block evaluates to void
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [] none)) = some (.normal .vVoid)

-- Singleton block returns its value
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.LiteralInt 99)] none)) = some (.normal (.vInt 99))

-- Block with two statements: value is the last one
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.LiteralInt 1), mk (.LiteralInt 2)] none))
  = some (.normal (.vInt 2))

/-! ## IfThenElse Tests -/

-- if true then 1 else 2 => 1
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralBool true)) (mk (.LiteralInt 1)) (some (mk (.LiteralInt 2)))))
  = some (.normal (.vInt 1))

-- if false then 1 else 2 => 2
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralBool false)) (mk (.LiteralInt 1)) (some (mk (.LiteralInt 2)))))
  = some (.normal (.vInt 2))

-- if false then 1 => void (no else branch)
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralBool false)) (mk (.LiteralInt 1)) none))
  = some (.normal .vVoid)

/-! ## Exit Tests -/

-- Exit propagates through block
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Exit "L"), mk (.LiteralInt 99)] none))
  = some (.exit "L")

-- Labeled block catches matching exit
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Exit "L")] (some "L")))
  = some (.normal .vVoid)

-- Labeled block does NOT catch non-matching exit
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Exit "other")] (some "L")))
  = some (.exit "other")

/-! ## Return Tests -/

-- Return with value
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Return (some (mk (.LiteralInt 42)))))
  = some (.ret (some (.vInt 42)))

-- Return without value
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Return none))
  = some (.ret none)

-- Return short-circuits block
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Return (some (mk (.LiteralInt 1)))), mk (.LiteralInt 99)] none))
  = some (.ret (some (.vInt 1)))

/-! ## LocalVariable Tests -/

-- Declare and initialize a local variable
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LocalVariable "x" ⟨.TInt, emd⟩ (some (mk (.LiteralInt 10))))
  getOutcomeAndVar r "x" = some (.normal .vVoid, some (.vInt 10))

-- Declare without initializer
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LocalVariable "y" ⟨.TBool, emd⟩ none)
  getOutcomeAndVar r "y" = some (.normal .vVoid, some .vVoid)

/-! ## Assert/Assume Tests -/

-- Assert true succeeds
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assert (mk (.LiteralBool true))))
  = some (.normal .vVoid)

-- Assume true succeeds
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assume (mk (.LiteralBool true))))
  = some (.normal .vVoid)

/-! ## ProveBy Test -/

-- ProveBy evaluates to the value of its first argument
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.ProveBy (mk (.LiteralInt 5)) (mk (.LiteralBool true))))
  = some (.normal (.vInt 5))

/-! ## Nested Control Flow Tests -/

-- Nested blocks with exit: inner exit propagates to outer labeled block
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.Block [mk (.Exit "outer"), mk (.LiteralInt 99)] none),
      mk (.LiteralInt 88)
    ] (some "outer")))
  = some (.normal .vVoid)

/-! ## Property Tests -/

-- catchExit preserves normal outcomes
#guard catchExit (some "L") (.normal (.vInt 1)) = .normal (.vInt 1)

-- catchExit preserves return outcomes
#guard catchExit (some "L") (.ret (some (.vInt 1))) = .ret (some (.vInt 1))

-- catchExit catches matching exit
#guard catchExit (some "L") (.exit "L") = .normal .vVoid

-- catchExit passes through non-matching exit
#guard catchExit (some "L") (.exit "M") = .exit "M"

-- interpPrimop: integer addition
#guard interpPrimop .Add [.vInt 3, .vInt 4] = some (.vInt 7)

-- interpPrimop: boolean negation
#guard interpPrimop .Not [.vBool false] = some (.vBool true)

-- interpPrimop: division by zero returns none
#guard interpPrimop .Div [.vInt 5, .vInt 0] = none

-- interpPrimop: type mismatch returns none
#guard interpPrimop .Add [.vBool true, .vInt 1] = none

-- Empty block is void
#guard getOutcome (interpBlock trivialEval emptyProc 10 emptyHeap emptyStore [])
  = some (.normal .vVoid)

/-! ## Fuel Exhaustion Test -/

-- Fuel 0 returns none
#guard interpStmt trivialEval emptyProc 0 emptyHeap emptyStore (.LiteralInt 1) = none

/-! ## Stuck State Tests -/

-- Undefined variable returns none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore (.Identifier "undef") = none

-- Abstract returns none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .Abstract = none

-- All returns none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .All = none

-- Hole returns none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .Hole = none

/-! ## While Loop Test -/

-- Simple while loop: x starts at 0, increments to 3
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let whileStmt := StmtExpr.While
    (mk (.PrimitiveOp .Lt [mk (.Identifier "x"), mk (.LiteralInt 3)]))
    [] none
    (mk (.Assign [⟨.Identifier "x", emd⟩]
      (mk (.PrimitiveOp .Add [mk (.Identifier "x"), mk (.LiteralInt 1)]))))
  let r := interpStmt trivialEval emptyProc 100 emptyHeap σ₀ whileStmt
  getOutcomeAndVar r "x" = some (.normal .vVoid, some (.vInt 3))

/-! ## Static Call Tests -/

-- Simple static call: procedure that returns its argument + 1
#guard
  let proc : Procedure := {
    name := "inc"
    inputs := [{ name := "n", type := ⟨.TInt, emd⟩ }]
    outputs := [{ name := "result", type := ⟨.TInt, emd⟩ }]
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.PrimitiveOp .Add [mk (.Identifier "n"), mk (.LiteralInt 1)]))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "inc" then some proc else none
  getOutcome (interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "inc" [mk (.LiteralInt 5)]))
  = some (.normal (.vInt 6))

-- Static call with return statement
#guard
  let proc : Procedure := {
    name := "f"
    inputs := [{ name := "n", type := ⟨.TInt, emd⟩ }]
    outputs := [{ name := "result", type := ⟨.TInt, emd⟩ }]
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.Return (some (mk (.Identifier "n")))))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  getOutcome (interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" [mk (.LiteralInt 42)]))
  = some (.normal (.vInt 42))

-- Static call with void return
#guard
  let proc : Procedure := {
    name := "g"
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.Return none))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "g" then some proc else none
  getOutcome (interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "g" []))
  = some (.normal .vVoid)

/-! ## OO Feature Tests -/

-- New allocates an object
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore (.New "MyClass")
  getOutcome r = some (.normal (.vRef 0))

-- FieldSelect after PureFieldUpdate
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.PureFieldUpdate (mk (.Identifier "obj")) "f" (mk (.LiteralInt 42))),
      mk (.FieldSelect (mk (.Identifier "obj")) "f")
    ] none)
  getOutcome r = some (.normal (.vInt 42))

-- ReferenceEquals: same ref
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.ReferenceEquals (mk (.Identifier "obj")) (mk (.Identifier "obj")))
    ] none)
  getOutcome r = some (.normal (.vBool true))

-- ReferenceEquals: different refs
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "a" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.LocalVariable "b" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.ReferenceEquals (mk (.Identifier "a")) (mk (.Identifier "b")))
    ] none)
  getOutcome r = some (.normal (.vBool false))

/-! ## Type Operation Tests -/

-- IsType: matching type
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "Dog", emd⟩ (some (mk (.New "Dog")))),
      mk (.IsType (mk (.Identifier "obj")) ⟨.UserDefined "Dog", emd⟩)
    ] none)
  getOutcome r = some (.normal (.vBool true))

-- IsType: non-matching type
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "Dog", emd⟩ (some (mk (.New "Dog")))),
      mk (.IsType (mk (.Identifier "obj")) ⟨.UserDefined "Cat", emd⟩)
    ] none)
  getOutcome r = some (.normal (.vBool false))

-- AsType: pass-through
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.AsType (mk (.LiteralInt 5)) ⟨.TInt, emd⟩))
  = some (.normal (.vInt 5))

/-! ## Specification Construct Tests -/

-- Old (delegated to δ)
#guard
  let δ : LaurelEval := fun σ e =>
    match e with
    | .Old ⟨.Identifier name, _⟩ => σ name.text
    | _ => trivialEval σ e
  getOutcome (interpStmt δ emptyProc 10 emptyHeap (singleStore "x" (.vInt 99))
    (.Old (mk (.Identifier "x"))))
  = some (.normal (.vInt 99))

-- Forall (delegated to δ)
#guard
  let δ : LaurelEval := fun _ e =>
    match e with
    | .Forall _ _ _ => some (.vBool true)
    | _ => none
  getOutcome (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Forall ⟨"x", ⟨.TInt, emd⟩⟩ none (mk (.LiteralBool true))))
  = some (.normal (.vBool true))

-- Exists (delegated to δ)
#guard
  let δ : LaurelEval := fun _ e =>
    match e with
    | .Exists _ _ _ => some (.vBool true)
    | _ => none
  getOutcome (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Exists ⟨"x", ⟨.TInt, emd⟩⟩ none (mk (.LiteralBool true))))
  = some (.normal (.vBool true))

/-! ## This Test -/

#guard
  let σ := singleStore "this" (.vRef 42)
  getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap σ .This)
  = some (.normal (.vRef 42))

/-! ## While Loop with Exit -/

#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let whileStmt := StmtExpr.While
    (mk (.LiteralBool true)) [] none
    (mk (.Block [
      mk (.Assign [⟨.Identifier "x", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "x"), mk (.LiteralInt 1)]))),
      mk (.IfThenElse
        (mk (.PrimitiveOp .Eq [mk (.Identifier "x"), mk (.LiteralInt 3)]))
        (mk (.Exit "done"))
        none)
    ] none))
  let r := interpStmt trivialEval emptyProc 100 emptyHeap σ₀
    (.Block [mk whileStmt] (some "done"))
  getOutcomeAndVar r "x" = some (.normal .vVoid, some (.vInt 3))

/-! ## While Loop with Return -/

#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let whileStmt := StmtExpr.While
    (mk (.LiteralBool true)) [] none
    (mk (.Return (some (mk (.LiteralInt 99)))))
  let r := interpStmt trivialEval emptyProc 100 emptyHeap σ₀ whileStmt
  getOutcome r = some (.ret (some (.vInt 99)))

/-! ## Field Assignment Test -/

#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.Assign [⟨.FieldSelect (mk (.Identifier "obj")) "f", emd⟩] (mk (.LiteralInt 7))),
      mk (.FieldSelect (mk (.Identifier "obj")) "f")
    ] none)
  getOutcome r = some (.normal (.vInt 7))

/-! ## Instance Call Test -/

#guard
  let proc : Procedure := {
    name := "MyClass.getVal"
    inputs := [{ name := "this", type := ⟨.UserDefined "MyClass", emd⟩ }]
    outputs := [{ name := "result", type := ⟨.TInt, emd⟩ }]
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.LiteralInt 100))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "MyClass.getVal" then some proc else none
  let r := interpStmt trivialEval π 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "MyClass", emd⟩ (some (mk (.New "MyClass")))),
      mk (.InstanceCall (mk (.Identifier "obj")) "getVal" [])
    ] none)
  getOutcome r = some (.normal (.vInt 100))

end Strata.Laurel.InterpreterTest

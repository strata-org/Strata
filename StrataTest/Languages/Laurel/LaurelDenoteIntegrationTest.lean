/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelDenote

/-!
# Integration Scenario Tests for Laurel Denotational Interpreter

Multi-feature scenario tests exercising realistic Laurel programs through
the denotational interpreter. Tests combine multiple language features to
validate that semantics composes correctly.
-/

namespace Strata.Laurel.DenoteIntegrationTest

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

def singleStore (name : String) (v : LaurelValue) : LaurelStore :=
  fun x => if x == name then some v else none

def multiStore (bindings : List (String × LaurelValue)) : LaurelStore :=
  fun x => bindings.find? (·.1 == x) |>.map (·.2)

def getOutcome (r : Option (Outcome × LaurelStore × LaurelHeap)) : Option Outcome :=
  r.map (·.1)

def getOutcomeAndVar (r : Option (Outcome × LaurelStore × LaurelHeap))
    (name : String) : Option (Outcome × Option LaurelValue) :=
  r.map (fun (o, σ, _) => (o, σ name))

def getVar (r : Option (Outcome × LaurelStore × LaurelHeap))
    (name : String) : Option LaurelValue :=
  r.bind (fun (_, σ, _) => σ name)

/-- Make a simple procedure with a body expression. -/
def mkProc (name : String) (inputs : List (String × HighType))
    (body : StmtExpr) : Procedure :=
  { name := name
    inputs := inputs.map fun (n, t) => { name := n, type := ⟨t, emd⟩ }
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk body)
    md := emd }

/-! ## 1. Recursive Procedures -/

-- Factorial: fact(n) = if n <= 0 then 1 else n * fact(n-1)
#guard
  let factBody := StmtExpr.IfThenElse
    (mk (.PrimitiveOp .Leq [mk (.Identifier "n"), mk (.LiteralInt 0)]))
    (mk (.Return (some (mk (.LiteralInt 1)))))
    (some (mk (.Return (some (mk (.PrimitiveOp .Mul
      [mk (.Identifier "n"),
       mk (.StaticCall "fact" [mk (.PrimitiveOp .Sub
         [mk (.Identifier "n"), mk (.LiteralInt 1)])])]))))))
  let factProc := mkProc "fact" [("n", .TInt)] factBody
  let π : ProcEnv := fun name => if name == "fact" then some factProc else none
  -- fact(5) = 120
  getOutcome (denoteStmt trivialEval π 1000 emptyHeap emptyStore
    (.StaticCall "fact" [mk (.LiteralInt 5)]))
  = some (.normal (.vInt 120))

-- Fibonacci via two procedures: fib calls fibHelper
-- fib(n) = if n <= 1 then n else fib(n-1) + fib(n-2)
#guard
  let fibBody := StmtExpr.IfThenElse
    (mk (.PrimitiveOp .Leq [mk (.Identifier "n"), mk (.LiteralInt 1)]))
    (mk (.Return (some (mk (.Identifier "n")))))
    (some (mk (.Return (some (mk (.PrimitiveOp .Add
      [mk (.StaticCall "fib" [mk (.PrimitiveOp .Sub
         [mk (.Identifier "n"), mk (.LiteralInt 1)])]),
       mk (.StaticCall "fib" [mk (.PrimitiveOp .Sub
         [mk (.Identifier "n"), mk (.LiteralInt 2)])])]))))))
  let fibProc := mkProc "fib" [("n", .TInt)] fibBody
  let π : ProcEnv := fun name => if name == "fib" then some fibProc else none
  -- fib(6) = 8
  getOutcome (denoteStmt trivialEval π 1000 emptyHeap emptyStore
    (.StaticCall "fib" [mk (.LiteralInt 6)]))
  = some (.normal (.vInt 8))

/-! ## 2. Nested Control Flow -/

-- Nested while loops: outer counts i 0..2, inner counts j 0..2, accumulate sum
-- Note: j is pre-declared since initStore fails on re-declaration
#guard
  let σ₀ := multiStore [("i", .vInt 0), ("j", .vInt 0), ("sum", .vInt 0)]
  let outerLoop := StmtExpr.While
    (mk (.PrimitiveOp .Lt [mk (.Identifier "i"), mk (.LiteralInt 3)]))
    [] none
    (mk (.Block [
      mk (.Assign [⟨.Identifier "j", emd⟩] (mk (.LiteralInt 0))),
      mk (.While
        (mk (.PrimitiveOp .Lt [mk (.Identifier "j"), mk (.LiteralInt 3)]))
        [] none
        (mk (.Block [
          mk (.Assign [⟨.Identifier "sum", emd⟩]
            (mk (.PrimitiveOp .Add [mk (.Identifier "sum"), mk (.LiteralInt 1)]))),
          mk (.Assign [⟨.Identifier "j", emd⟩]
            (mk (.PrimitiveOp .Add [mk (.Identifier "j"), mk (.LiteralInt 1)])))
        ] none))),
      mk (.Assign [⟨.Identifier "i", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "i"), mk (.LiteralInt 1)])))
    ] none))
  let r := denoteStmt trivialEval emptyProc 1000 emptyHeap σ₀ outerLoop
  -- 3 outer × 3 inner = 9
  getVar r "sum" = some (.vInt 9)

-- Return inside if inside while — early termination
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let body := StmtExpr.While
    (mk (.LiteralBool true)) [] none
    (mk (.Block [
      mk (.Assign [⟨.Identifier "x", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "x"), mk (.LiteralInt 1)]))),
      mk (.IfThenElse
        (mk (.PrimitiveOp .Eq [mk (.Identifier "x"), mk (.LiteralInt 5)]))
        (mk (.Return (some (mk (.Identifier "x")))))
        none)
    ] none))
  getOutcome (denoteStmt trivialEval emptyProc 1000 emptyHeap σ₀ body)
  = some (.ret (some (.vInt 5)))

-- Exit from deeply nested blocks (3+ levels)
#guard
  let prog := StmtExpr.Block [
    mk (.Block [
      mk (.Block [
        mk (.Exit "outer")
      ] none)
    ] none),
    mk (.LiteralInt 999)  -- should not be reached
  ] (some "outer")
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal .vVoid)

-- While loop with if-then-else containing exit to labeled outer block
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let prog := StmtExpr.Block [
    mk (.While
      (mk (.LiteralBool true)) [] none
      (mk (.Block [
        mk (.Assign [⟨.Identifier "x", emd⟩]
          (mk (.PrimitiveOp .Add [mk (.Identifier "x"), mk (.LiteralInt 1)]))),
        mk (.IfThenElse
          (mk (.PrimitiveOp .Geq [mk (.Identifier "x"), mk (.LiteralInt 4)]))
          (mk (.Exit "done"))
          (some (mk (.LiteralBool true))))
      ] none)))
  ] (some "done")
  getOutcomeAndVar (denoteStmt trivialEval emptyProc 1000 emptyHeap σ₀ prog) "x"
  = some (.normal .vVoid, some (.vInt 4))

-- Block with multiple labeled sub-blocks and targeted exits
#guard
  let σ₀ := multiStore [("r", .vInt 0)]
  let prog := StmtExpr.Block [
    mk (.Block [
      mk (.Assign [⟨.Identifier "r", emd⟩] (mk (.LiteralInt 1))),
      mk (.Exit "b1")
    ] (some "b1")),
    mk (.Block [
      mk (.Assign [⟨.Identifier "r", emd⟩] (mk (.LiteralInt 2))),
      mk (.Exit "b2")
    ] (some "b2")),
    mk (.Assign [⟨.Identifier "r", emd⟩] (mk (.LiteralInt 3)))
  ] none
  getVar (denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog) "r"
  = some (.vInt 3)

/-! ## 3. Effectful Expressions in Complex Positions -/

-- Assignment in if-condition: if (x := 5) > 3 then 1 else 0
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let prog := StmtExpr.IfThenElse
    (mk (.PrimitiveOp .Gt
      [mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 5))),
       mk (.LiteralInt 3)]))
    (mk (.LiteralInt 1))
    (some (mk (.LiteralInt 0)))
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getOutcome r = some (.normal (.vInt 1))

-- Assignment in while-condition: while (x := x + 1) < 5 do skip
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let prog := StmtExpr.While
    (mk (.PrimitiveOp .Lt
      [mk (.Assign [⟨.Identifier "x", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "x"), mk (.LiteralInt 1)]))),
       mk (.LiteralInt 5)]))
    [] none
    (mk (.Block [] none))
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getVar r "x" = some (.vInt 5)

-- Nested assignments in arguments: (x := 1) + (y := 2) = 3
#guard
  let σ₀ := multiStore [("x", .vInt 0), ("y", .vInt 0)]
  let prog := StmtExpr.PrimitiveOp .Add
    [mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 1))),
     mk (.Assign [⟨.Identifier "y", emd⟩] (mk (.LiteralInt 2)))]
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getOutcome r = some (.normal (.vInt 3))

-- Assignment in both branches of if-then-else
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let prog := StmtExpr.IfThenElse
    (mk (.LiteralBool false))
    (mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 10))))
    (some (mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 20)))))
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getOutcomeAndVar r "x" = some (.normal (.vInt 20), some (.vInt 20))

/-! ## 4. Object-Oriented Programs -/

-- Create object, set multiple fields, read them back
#guard
  let prog := StmtExpr.Block [
    mk (.LocalVariable "obj" ⟨.UserDefined "Pt", emd⟩ (some (mk (.New "Pt")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "obj")) "x", emd⟩] (mk (.LiteralInt 10))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "obj")) "y", emd⟩] (mk (.LiteralInt 20))),
    mk (.PrimitiveOp .Add [
      mk (.FieldSelect (mk (.Identifier "obj")) "x"),
      mk (.FieldSelect (mk (.Identifier "obj")) "y")])
  ] none
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 30))

-- Method call that modifies object fields via heap
#guard
  let setXProc : Procedure := {
    name := "Obj.setX"
    inputs := [{ name := "this", type := ⟨.UserDefined "Obj", emd⟩ },
               { name := "v", type := ⟨.TInt, emd⟩ }]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.Assign [⟨.FieldSelect (mk (.Identifier "this")) "x", emd⟩]
      (mk (.Identifier "v"))))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "Obj.setX" then some setXProc else none
  let prog := StmtExpr.Block [
    mk (.LocalVariable "o" ⟨.UserDefined "Obj", emd⟩ (some (mk (.New "Obj")))),
    mk (.InstanceCall (mk (.Identifier "o")) "setX" [mk (.LiteralInt 42)]),
    mk (.FieldSelect (mk (.Identifier "o")) "x")
  ] none
  getOutcome (denoteStmt trivialEval π 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 42))

-- Multiple objects with independent field stores
#guard
  let prog := StmtExpr.Block [
    mk (.LocalVariable "a" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
    mk (.LocalVariable "b" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "a")) "v", emd⟩] (mk (.LiteralInt 1))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "b")) "v", emd⟩] (mk (.LiteralInt 2))),
    mk (.FieldSelect (mk (.Identifier "a")) "v")
  ] none
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 1))

-- Chain: new → field update → method call → field select
#guard
  let getF : Procedure := {
    name := "C.getF"
    inputs := [{ name := "this", type := ⟨.UserDefined "C", emd⟩ }]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.Return (some (mk (.FieldSelect (mk (.Identifier "this")) "f")))))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "C.getF" then some getF else none
  let prog := StmtExpr.Block [
    mk (.LocalVariable "c" ⟨.UserDefined "C", emd⟩ (some (mk (.New "C")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "c")) "f", emd⟩] (mk (.LiteralInt 77))),
    mk (.InstanceCall (mk (.Identifier "c")) "getF" [])
  ] none
  getOutcome (denoteStmt trivialEval π 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 77))

-- ReferenceEquals after aliasing
#guard
  let prog := StmtExpr.Block [
    mk (.LocalVariable "a" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
    mk (.LocalVariable "b" ⟨.UserDefined "T", emd⟩ (some (mk (.Identifier "a")))),
    mk (.ReferenceEquals (mk (.Identifier "a")) (mk (.Identifier "b")))
  ] none
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal (.vBool true))

/-! ## 5. Procedure Interaction Patterns -/

-- Procedure A calls procedure B (non-recursive call chain)
#guard
  let double := mkProc "double" [("n", .TInt)]
    (.Return (some (mk (.PrimitiveOp .Mul [mk (.Identifier "n"), mk (.LiteralInt 2)]))))
  let quadruple := mkProc "quadruple" [("n", .TInt)]
    (.Return (some (mk (.StaticCall "double"
      [mk (.StaticCall "double" [mk (.Identifier "n")])]))))
  let π : ProcEnv := fun name =>
    if name == "double" then some double
    else if name == "quadruple" then some quadruple
    else none
  getOutcome (denoteStmt trivialEval π 100 emptyHeap emptyStore
    (.StaticCall "quadruple" [mk (.LiteralInt 3)]))
  = some (.normal (.vInt 12))

-- Procedure with precondition (assert in body)
#guard
  let safeDiv := mkProc "safeDiv" [("a", .TInt), ("b", .TInt)]
    (.Block [
      mk (.Assert (mk (.PrimitiveOp .Neq [mk (.Identifier "b"), mk (.LiteralInt 0)]))),
      mk (.Return (some (mk (.PrimitiveOp .Div [mk (.Identifier "a"), mk (.Identifier "b")]))))
    ] none)
  let π : ProcEnv := fun name => if name == "safeDiv" then some safeDiv else none
  -- safeDiv(10, 2) = 5
  getOutcome (denoteStmt trivialEval π 100 emptyHeap emptyStore
    (.StaticCall "safeDiv" [mk (.LiteralInt 10), mk (.LiteralInt 2)]))
  = some (.normal (.vInt 5))

-- Procedure that returns early via Return in the middle of a block
#guard
  let earlyRet := mkProc "earlyRet" [("n", .TInt)]
    (.Block [
      mk (.IfThenElse
        (mk (.PrimitiveOp .Lt [mk (.Identifier "n"), mk (.LiteralInt 0)]))
        (mk (.Return (some (mk (.LiteralInt (-1))))))
        none),
      mk (.Return (some (mk (.Identifier "n"))))
    ] none)
  let π : ProcEnv := fun name => if name == "earlyRet" then some earlyRet else none
  -- earlyRet(-5) = -1
  getOutcome (denoteStmt trivialEval π 100 emptyHeap emptyStore
    (.StaticCall "earlyRet" [mk (.LiteralInt (-5))]))
  = some (.normal (.vInt (-1)))

-- Procedure with local variables that shadow caller's variables
#guard
  let σ₀ := singleStore "x" (.vInt 100)
  let setX := mkProc "setX" []
    (.Block [
      mk (.LocalVariable "x" ⟨.TInt, emd⟩ (some (mk (.LiteralInt 999)))),
      mk (.Return (some (mk (.Identifier "x"))))
    ] none)
  let π : ProcEnv := fun name => if name == "setX" then some setX else none
  let r := denoteStmt trivialEval π 100 emptyHeap σ₀
    (.StaticCall "setX" [])
  -- Procedure returns 999 (its local x), caller's x unchanged
  getOutcome r = some (.normal (.vInt 999)) &&
  getVar r "x" = some (.vInt 100)

/-! ## 6. Store Threading Correctness -/

-- Sequence of assignments verifying left-to-right store threading
#guard
  let σ₀ := multiStore [("a", .vInt 0), ("b", .vInt 0), ("c", .vInt 0)]
  let prog := StmtExpr.Block [
    mk (.Assign [⟨.Identifier "a", emd⟩] (mk (.LiteralInt 1))),
    mk (.Assign [⟨.Identifier "b", emd⟩] (mk (.PrimitiveOp .Add [mk (.Identifier "a"), mk (.LiteralInt 1)]))),
    mk (.Assign [⟨.Identifier "c", emd⟩] (mk (.PrimitiveOp .Add [mk (.Identifier "b"), mk (.LiteralInt 1)])))
  ] none
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getVar r "a" = some (.vInt 1) &&
  getVar r "b" = some (.vInt 2) &&
  getVar r "c" = some (.vInt 3)

-- While loop accumulator pattern (sum 1..5)
#guard
  let σ₀ := multiStore [("i", .vInt 1), ("sum", .vInt 0)]
  let prog := StmtExpr.While
    (mk (.PrimitiveOp .Leq [mk (.Identifier "i"), mk (.LiteralInt 5)]))
    [] none
    (mk (.Block [
      mk (.Assign [⟨.Identifier "sum", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "sum"), mk (.Identifier "i")]))),
      mk (.Assign [⟨.Identifier "i", emd⟩]
        (mk (.PrimitiveOp .Add [mk (.Identifier "i"), mk (.LiteralInt 1)])))
    ] none))
  let r := denoteStmt trivialEval emptyProc 1000 emptyHeap σ₀ prog
  getVar r "sum" = some (.vInt 15)

-- Swap pattern: t := x; x := y; y := t
#guard
  let σ₀ := multiStore [("x", .vInt 10), ("y", .vInt 20)]
  let prog := StmtExpr.Block [
    mk (.LocalVariable "t" ⟨.TInt, emd⟩ (some (mk (.Identifier "x")))),
    mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.Identifier "y"))),
    mk (.Assign [⟨.Identifier "y", emd⟩] (mk (.Identifier "t")))
  ] none
  let r := denoteStmt trivialEval emptyProc 100 emptyHeap σ₀ prog
  getVar r "x" = some (.vInt 20) &&
  getVar r "y" = some (.vInt 10)

/-! ## 7. Edge Cases -/

-- Deeply nested blocks (10+ levels) — verify no stack issues with fuel
#guard
  let rec nestBlocks : Nat → StmtExpr → StmtExpr
    | 0, inner => inner
    | n + 1, inner => .Block [mk (nestBlocks n inner)] none
  let prog := nestBlocks 15 (.LiteralInt 42)
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 42))

-- Empty program (empty block)
#guard
  getOutcome (denoteStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [] none))
  = some (.normal .vVoid)

-- Program that exhausts fuel (infinite loop with limited fuel → none)
#guard
  denoteStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.While (mk (.LiteralBool true)) [] none (mk (.Block [] none)))
  = none

-- Large number of sequential assignments
#guard
  let stmts : List StmtExprMd := List.range 20 |>.map fun i =>
    mk (.LocalVariable (s!"v{i}") ⟨.TInt, emd⟩ (some (mk (.LiteralInt (Int.ofNat i)))))
  let prog := StmtExpr.Block (stmts ++ [mk (.Identifier "v19")]) none
  getOutcome (denoteStmt trivialEval emptyProc 100 emptyHeap emptyStore prog)
  = some (.normal (.vInt 19))

end Strata.Laurel.DenoteIntegrationTest

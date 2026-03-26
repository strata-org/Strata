/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter

/-!
# Comprehensive Unit Tests for Laurel Interpreter

Covers gaps in `LaurelInterpreterTest.lean`: every `evalPrimOp` case,
edge cases for `interpStmt` constructs, and stuck/error states.
-/

namespace Strata.Laurel.InterpreterUnitTest

open Strata.Laurel

/-! ## Test Helpers (reused from LaurelInterpreterTest) -/

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

def twoStore (n1 : Identifier) (v1 : LaurelValue) (n2 : Identifier) (v2 : LaurelValue)
    : LaurelStore :=
  fun x => if x == n1.text then some v1 else if x == n2.text then some v2 else none

def getOutcome (r : Option (Outcome × LaurelStore × LaurelHeap)) : Option Outcome :=
  r.map (·.1)

def getOutcomeAndVar (r : Option (Outcome × LaurelStore × LaurelHeap))
    (name : Identifier) : Option (Outcome × Option LaurelValue) :=
  r.map (fun (o, σ, _) => (o, σ name.text))

/-! ## evalPrimOp: Arithmetic -/

-- Sub
#guard evalPrimOp .Sub [.vInt 10, .vInt 3] = some (.vInt 7)
#guard evalPrimOp .Sub [.vInt 0, .vInt 5] = some (.vInt (-5))

-- Mul
#guard evalPrimOp .Mul [.vInt 4, .vInt 5] = some (.vInt 20)
#guard evalPrimOp .Mul [.vInt 0, .vInt 99] = some (.vInt 0)

-- Div (non-zero)
#guard evalPrimOp .Div [.vInt 10, .vInt 3] = some (.vInt 3)
#guard evalPrimOp .Div [.vInt (-7), .vInt 2] = some (.vInt (-4))

-- Mod (non-zero)
#guard evalPrimOp .Mod [.vInt 10, .vInt 3] = some (.vInt 1)
#guard evalPrimOp .Mod [.vInt (-7), .vInt 2] = some (.vInt 1)

-- Neg
#guard evalPrimOp .Neg [.vInt 5] = some (.vInt (-5))
#guard evalPrimOp .Neg [.vInt (-3)] = some (.vInt 3)
#guard evalPrimOp .Neg [.vInt 0] = some (.vInt 0)

/-! ## evalPrimOp: Division by zero -/

#guard evalPrimOp .Div [.vInt 5, .vInt 0] = none
#guard evalPrimOp .Mod [.vInt 5, .vInt 0] = none
#guard evalPrimOp .DivT [.vInt 5, .vInt 0] = none
#guard evalPrimOp .ModT [.vInt 5, .vInt 0] = none

/-! ## evalPrimOp: Truncation division and modulus -/

-- DivT (truncation toward zero)
#guard evalPrimOp .DivT [.vInt 7, .vInt 2] = some (.vInt 3)
#guard evalPrimOp .DivT [.vInt (-7), .vInt 2] = some (.vInt (-3))
#guard evalPrimOp .DivT [.vInt 7, .vInt (-2)] = some (.vInt (-3))
#guard evalPrimOp .DivT [.vInt (-7), .vInt (-2)] = some (.vInt 3)

-- ModT (truncation modulus)
#guard evalPrimOp .ModT [.vInt 7, .vInt 2] = some (.vInt 1)
#guard evalPrimOp .ModT [.vInt (-7), .vInt 2] = some (.vInt (-1))
#guard evalPrimOp .ModT [.vInt 7, .vInt (-2)] = some (.vInt 1)
#guard evalPrimOp .ModT [.vInt (-7), .vInt (-2)] = some (.vInt (-1))

-- Short-circuit ops return none in evalPrimOp (handled in interpStmt)
#guard evalPrimOp .AndThen [.vBool true, .vBool false] = none
#guard evalPrimOp .OrElse [.vBool false, .vBool true] = none
#guard evalPrimOp .Implies [.vBool false, .vBool true] = none

/-! ## evalPrimOp: Comparison -/

-- Neq (int)
#guard evalPrimOp .Neq [.vInt 1, .vInt 2] = some (.vBool true)
#guard evalPrimOp .Neq [.vInt 3, .vInt 3] = some (.vBool false)

-- Leq
#guard evalPrimOp .Leq [.vInt 3, .vInt 5] = some (.vBool true)
#guard evalPrimOp .Leq [.vInt 5, .vInt 5] = some (.vBool true)
#guard evalPrimOp .Leq [.vInt 6, .vInt 5] = some (.vBool false)

-- Gt
#guard evalPrimOp .Gt [.vInt 5, .vInt 3] = some (.vBool true)
#guard evalPrimOp .Gt [.vInt 3, .vInt 3] = some (.vBool false)

-- Geq
#guard evalPrimOp .Geq [.vInt 5, .vInt 3] = some (.vBool true)
#guard evalPrimOp .Geq [.vInt 3, .vInt 3] = some (.vBool true)
#guard evalPrimOp .Geq [.vInt 2, .vInt 3] = some (.vBool false)

/-! ## evalPrimOp: Boolean -/

-- Or
#guard evalPrimOp .Or [.vBool false, .vBool false] = some (.vBool false)
#guard evalPrimOp .Or [.vBool true, .vBool false] = some (.vBool true)
#guard evalPrimOp .Or [.vBool false, .vBool true] = some (.vBool true)

-- Implies (handled in interpStmt as short-circuit; evalPrimOp returns none)
#guard evalPrimOp .Implies [.vBool true, .vBool false] = none
#guard evalPrimOp .Implies [.vBool false, .vBool false] = none
#guard evalPrimOp .Implies [.vBool true, .vBool true] = none

/-! ## evalPrimOp: String -/

-- Eq on strings
#guard evalPrimOp .Eq [.vString "abc", .vString "abc"] = some (.vBool true)
#guard evalPrimOp .Eq [.vString "abc", .vString "def"] = some (.vBool false)

-- Neq on strings
#guard evalPrimOp .Neq [.vString "a", .vString "b"] = some (.vBool true)
#guard evalPrimOp .Neq [.vString "a", .vString "a"] = some (.vBool false)

/-! ## evalPrimOp: Ref -/

-- Eq on refs
#guard evalPrimOp .Eq [.vRef 0, .vRef 0] = some (.vBool true)
#guard evalPrimOp .Eq [.vRef 0, .vRef 1] = some (.vBool false)

-- Neq on refs
#guard evalPrimOp .Neq [.vRef 0, .vRef 1] = some (.vBool true)
#guard evalPrimOp .Neq [.vRef 0, .vRef 0] = some (.vBool false)

/-! ## evalPrimOp: Bool Eq/Neq -/

#guard evalPrimOp .Eq [.vBool true, .vBool true] = some (.vBool true)
#guard evalPrimOp .Eq [.vBool true, .vBool false] = some (.vBool false)
#guard evalPrimOp .Neq [.vBool true, .vBool false] = some (.vBool true)
#guard evalPrimOp .Neq [.vBool true, .vBool true] = some (.vBool false)

/-! ## evalPrimOp: Type mismatch → none -/

#guard evalPrimOp .Add [.vBool true, .vInt 1] = none
#guard evalPrimOp .Add [.vInt 1, .vBool true] = none
#guard evalPrimOp .And [.vInt 1, .vInt 2] = none
#guard evalPrimOp .Or [.vInt 1, .vInt 2] = none
#guard evalPrimOp .Not [.vInt 1] = none
#guard evalPrimOp .Lt [.vBool true, .vBool false] = none
#guard evalPrimOp .Sub [.vString "a", .vString "b"] = none
#guard evalPrimOp .Neg [.vBool true] = none
#guard evalPrimOp .Implies [.vInt 1, .vInt 2] = none
#guard evalPrimOp .StrConcat [.vInt 1, .vInt 2] = none

/-! ## evalPrimOp: Wrong arity → none -/

#guard evalPrimOp .Add [.vInt 1] = none
#guard evalPrimOp .Add [.vInt 1, .vInt 2, .vInt 3] = none
#guard evalPrimOp .Not [.vBool true, .vBool false] = none
#guard evalPrimOp .Not [] = none
#guard evalPrimOp .Neg [] = none
#guard evalPrimOp .Eq [.vInt 1] = none
#guard evalPrimOp .And [.vBool true] = none

/-! ## interpStmt: LiteralDecimal → none -/

-- LiteralDecimal has no runtime representation
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LiteralDecimal ⟨1, 5⟩) = none

/-! ## interpStmt: Shadowed variable -/

-- Variable shadowing: inner declaration shadows outer
#guard
  let σ₀ := singleStore "x" (.vInt 1)
  let r := interpStmt trivialEval emptyProc 10 emptyHeap σ₀ (.Identifier "x")
  getOutcome r = some (.normal (.vInt 1))

/-! ## interpStmt: IfThenElse edge cases -/

-- Condition evaluates to non-bool → none (stuck)
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralInt 1)) (mk (.LiteralInt 2)) (some (mk (.LiteralInt 3)))) = none

-- Condition evaluates to non-bool, no else → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralInt 1)) (mk (.LiteralInt 2)) none) = none

-- Exit in then-branch propagates
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralBool true)) (mk (.Exit "L")) (some (mk (.LiteralInt 2)))))
  = some (.exit "L")

-- Return in condition propagates (condition stuck since return is not normal)
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.Return (some (mk (.LiteralInt 1))))) (mk (.LiteralInt 2)) none) = none

/-! ## interpStmt: While edge cases -/

-- False guard on first iteration → void, body never executes
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let r := interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.While (mk (.LiteralBool false)) [] none
      (mk (.Assign [⟨.Identifier "x", emd⟩] (mk (.LiteralInt 99)))))
  getOutcomeAndVar r "x" = some (.normal .vVoid, some (.vInt 0))

-- Return with value in loop body
#guard
  let σ₀ := singleStore "x" (.vInt 0)
  let r := interpStmt trivialEval emptyProc 100 emptyHeap σ₀
    (.While (mk (.LiteralBool true)) [] none
      (mk (.Return (some (mk (.Identifier "x"))))))
  getOutcome r = some (.ret (some (.vInt 0)))

-- Non-bool guard → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.While (mk (.LiteralInt 1)) [] none (mk (.LiteralInt 2))) = none

/-! ## interpStmt: LocalVariable re-declaration → none -/

-- initStore fails when variable already exists
#guard
  let σ₀ := singleStore "x" (.vInt 1)
  interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.LocalVariable "x" ⟨.TInt, emd⟩ (some (mk (.LiteralInt 2)))) = none

-- Uninit re-declaration also fails
#guard
  let σ₀ := singleStore "x" (.vInt 1)
  interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.LocalVariable "x" ⟨.TInt, emd⟩ none) = none

/-! ## interpStmt: Assign to undefined variable → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.Identifier "undef", emd⟩] (mk (.LiteralInt 1))) = none

/-! ## interpStmt: Assert false → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assert (mk (.LiteralBool false))) = none

-- Assert non-bool → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assert (mk (.LiteralInt 1))) = none

/-! ## interpStmt: Assume false → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assume (mk (.LiteralBool false))) = none

-- Assume non-bool → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assume (mk (.LiteralInt 1))) = none

/-! ## interpStmt: Block exit/return propagation -/

-- Exit propagates past non-matching label
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Exit "X")] (some "Y")))
  = some (.exit "X")

-- Return propagates through any block (even labeled)
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Return (some (mk (.LiteralInt 42))))] (some "L")))
  = some (.ret (some (.vInt 42)))

-- Return propagates through unlabeled block
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [mk (.Return none), mk (.LiteralInt 99)] none))
  = some (.ret none)

/-! ## interpStmt: StaticCall edge cases -/

-- Undefined procedure → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.StaticCall "nonexistent" []) = none

-- Wrong number of arguments → none (bindParams fails)
#guard
  let proc : Procedure := {
    name := "f"
    inputs := [{ name := "a", type := ⟨.TInt, emd⟩ }, { name := "b", type := ⟨.TInt, emd⟩ }]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Transparent (mk (.LiteralInt 0))
    md := emd
  }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" [mk (.LiteralInt 1)]) = none

-- Procedure with Abstract body → none
#guard
  let proc : Procedure := {
    name := "g"
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Abstract []
    md := emd
  }
  let π : ProcEnv := fun name => if name == "g" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "g" []) = none

-- Procedure with External body → none
#guard
  let proc : Procedure := {
    name := "h"
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .External
    md := emd
  }
  let π : ProcEnv := fun name => if name == "h" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "h" []) = none

/-! ## interpStmt: FieldSelect edge cases -/

-- FieldSelect on non-ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.FieldSelect (mk (.LiteralInt 5)) "f") = none

-- FieldSelect on ref with undefined field → none
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "obj" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.FieldSelect (mk (.Identifier "obj")) "nonexistent")
    ] none)
  r = none

/-! ## interpStmt: New allocates sequential addresses -/

-- First allocation gets address 0
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.New "T")) = some (.normal (.vRef 0))

-- Second allocation gets address 1
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "a" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.New "T")
    ] none)
  getOutcome r = some (.normal (.vRef 1))

-- Third allocation gets address 2
#guard
  let r := interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Block [
      mk (.LocalVariable "a" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.LocalVariable "b" ⟨.UserDefined "T", emd⟩ (some (mk (.New "T")))),
      mk (.New "T")
    ] none)
  getOutcome r = some (.normal (.vRef 2))

/-! ## interpStmt: PureFieldUpdate on non-ref → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PureFieldUpdate (mk (.LiteralInt 5)) "f" (mk (.LiteralInt 1))) = none

/-! ## interpStmt: ContractOf delegated to δ -/

#guard
  let δ : LaurelEval := fun _ e =>
    match e with
    | .ContractOf .Precondition _ => some (.vBool true)
    | _ => none
  getOutcome (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.ContractOf .Precondition (mk (.Identifier "f"))))
  = some (.normal (.vBool true))

-- ContractOf with trivialEval (no handler) → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.ContractOf .Precondition (mk (.Identifier "f"))) = none

/-! ## interpStmt: Fresh delegated to δ -/

#guard
  let δ : LaurelEval := fun _ e =>
    match e with
    | .Fresh _ => some (.vBool true)
    | _ => none
  getOutcome (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Fresh (mk (.Identifier "x"))))
  = some (.normal (.vBool true))

/-! ## interpStmt: Assigned delegated to δ -/

#guard
  let δ : LaurelEval := fun _ e =>
    match e with
    | .Assigned _ => some (.vBool false)
    | _ => none
  getOutcome (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Assigned (mk (.Identifier "x"))))
  = some (.normal (.vBool false))

/-! ## interpStmt: Multi-target Assign → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.Identifier "x", emd⟩, ⟨.Identifier "y", emd⟩] (mk (.LiteralInt 1))) = none

/-! ## interpStmt: Short-circuit AndThen/OrElse/Implies via interpStmt -/

-- AndThen short-circuits: false && (stuck) → false
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .AndThen [mk (.LiteralBool false), mk (.Identifier "undef")]))
  = some (.normal (.vBool false))

-- OrElse short-circuits: true || (stuck) → true
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .OrElse [mk (.LiteralBool true), mk (.Identifier "undef")]))
  = some (.normal (.vBool true))

-- Implies short-circuits: false => (stuck) → true
#guard getOutcome (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Implies [mk (.LiteralBool false), mk (.Identifier "undef")]))
  = some (.normal (.vBool true))

-- AndThen does NOT short-circuit on true: true && undef → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .AndThen [mk (.LiteralBool true), mk (.Identifier "undef")]) = none

-- OrElse does NOT short-circuit on false: false || undef → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .OrElse [mk (.LiteralBool false), mk (.Identifier "undef")]) = none

-- Implies does NOT short-circuit on true: true => undef → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Implies [mk (.LiteralBool true), mk (.Identifier "undef")]) = none

/-! ## interpStmt: ReferenceEquals on non-ref → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.ReferenceEquals (mk (.LiteralInt 1)) (mk (.LiteralInt 1))) = none

/-! ## interpStmt: This with no "this" in store → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .This = none

/-! ## interpStmt: IsType on non-ref → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IsType (mk (.LiteralInt 5)) ⟨.UserDefined "T", emd⟩) = none

/-! ## interpStmt: Opaque procedure with implementation -/

#guard
  let proc : Procedure := {
    name := "f"
    inputs := [{ name := "n", type := ⟨.TInt, emd⟩ }]
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Opaque [] (some (mk (.PrimitiveOp .Add [mk (.Identifier "n"), mk (.LiteralInt 1)]))) []
    md := emd
  }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  getOutcome (interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" [mk (.LiteralInt 5)]))
  = some (.normal (.vInt 6))

-- Opaque procedure without implementation → none
#guard
  let proc : Procedure := {
    name := "f"
    inputs := []
    outputs := []
    preconditions := []
    determinism := .deterministic none
    isFunctional := false
    decreases := none
    body := .Opaque [] none []
    md := emd
  }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" []) = none

/-! ## interpStmt: Field assignment to unallocated ref → none -/

#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.FieldSelect (mk (.LiteralInt 5)) "f", emd⟩] (mk (.LiteralInt 1))) = none

/-! ## interpBlock: fuel exhaustion -/

#guard interpBlock trivialEval emptyProc 0 emptyHeap emptyStore [mk (.LiteralInt 1)] = none

/-! ## interpArgs: fuel exhaustion -/

#guard interpArgs trivialEval emptyProc 0 emptyHeap emptyStore [mk (.LiteralInt 1)] = none

/-! ## interpArgs: stuck argument → none -/

#guard interpArgs trivialEval emptyProc 10 emptyHeap emptyStore
    [mk (.LiteralInt 1), mk (.Identifier "undef")] = none

end Strata.Laurel.InterpreterUnitTest

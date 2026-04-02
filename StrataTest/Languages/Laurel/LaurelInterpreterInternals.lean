/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter
import StrataTest.Languages.Laurel.ConcreteEval.TestHelper

/-!
# Interpreter Internals Tests

Tests for internal APIs that cannot be exercised through parsed Laurel source:
- `interpPrimop` exhaustive coverage (all ops, type mismatches, wrong arity)
- Stuck/error states (malformed AST the parser would reject)
- `δ` delegation (Forall, Exists, Old, Fresh, Assigned, ContractOf)
- Fuel exhaustion
- Programmatic AST tests for `interpProgram` (opaque procs, instance methods, static fields)
-/

namespace Strata.Laurel.InterpreterInternals

open Strata.Laurel
open Strata.Laurel.ConcreteEval.TestHelper

/-! ## Test Helpers -/

def emptyStore : LaurelStore := fun _ => none
def emptyHeap : LaurelHeap := fun _ => none
def emptyProc : ProcEnv := fun _ => none

def trivialEval : LaurelEval := fun st expr =>
  match expr with
  | .Identifier name => st name.text
  | .LiteralInt i => some (.vInt i)
  | .LiteralBool b => some (.vBool b)
  | .LiteralString s => some (.vString s)
  | _ => none

def singleStore (name : Identifier) (v : LaurelValue) : LaurelStore :=
  fun x => if x == name.text then some v else none

def getOutcomeRaw (r : Option (Outcome × LaurelStore × LaurelHeap)) : Option Outcome :=
  r.map (·.1)

/-! ## interpPrimop: Arithmetic -/

#guard interpPrimop .Add [.vInt 3, .vInt 4] = some (.vInt 7)
#guard interpPrimop .Sub [.vInt 10, .vInt 3] = some (.vInt 7)
#guard interpPrimop .Sub [.vInt 0, .vInt 5] = some (.vInt (-5))
#guard interpPrimop .Mul [.vInt 4, .vInt 5] = some (.vInt 20)
#guard interpPrimop .Mul [.vInt 0, .vInt 99] = some (.vInt 0)
#guard interpPrimop .Div [.vInt 10, .vInt 3] = some (.vInt 3)
#guard interpPrimop .Div [.vInt (-7), .vInt 2] = some (.vInt (-4))
#guard interpPrimop .Mod [.vInt 10, .vInt 3] = some (.vInt 1)
#guard interpPrimop .Mod [.vInt (-7), .vInt 2] = some (.vInt 1)
#guard interpPrimop .Neg [.vInt 5] = some (.vInt (-5))
#guard interpPrimop .Neg [.vInt (-3)] = some (.vInt 3)
#guard interpPrimop .Neg [.vInt 0] = some (.vInt 0)

/-! ## interpPrimop: Division by zero -/

#guard interpPrimop .Div [.vInt 5, .vInt 0] = none
#guard interpPrimop .Mod [.vInt 5, .vInt 0] = none
#guard interpPrimop .DivT [.vInt 5, .vInt 0] = none
#guard interpPrimop .ModT [.vInt 5, .vInt 0] = none

/-! ## interpPrimop: Truncation division and modulus -/

#guard interpPrimop .DivT [.vInt 7, .vInt 2] = some (.vInt 3)
#guard interpPrimop .DivT [.vInt (-7), .vInt 2] = some (.vInt (-3))
#guard interpPrimop .DivT [.vInt 7, .vInt (-2)] = some (.vInt (-3))
#guard interpPrimop .DivT [.vInt (-7), .vInt (-2)] = some (.vInt 3)
#guard interpPrimop .ModT [.vInt 7, .vInt 2] = some (.vInt 1)
#guard interpPrimop .ModT [.vInt (-7), .vInt 2] = some (.vInt (-1))
#guard interpPrimop .ModT [.vInt 7, .vInt (-2)] = some (.vInt 1)
#guard interpPrimop .ModT [.vInt (-7), .vInt (-2)] = some (.vInt (-1))

-- Short-circuit ops return none in interpPrimop (handled in interpStmt)
#guard interpPrimop .AndThen [.vBool true, .vBool false] = none
#guard interpPrimop .OrElse [.vBool false, .vBool true] = none
#guard interpPrimop .Implies [.vBool false, .vBool true] = none

/-! ## interpPrimop: Comparison -/

#guard interpPrimop .Neq [.vInt 1, .vInt 2] = some (.vBool true)
#guard interpPrimop .Neq [.vInt 3, .vInt 3] = some (.vBool false)
#guard interpPrimop .Leq [.vInt 3, .vInt 5] = some (.vBool true)
#guard interpPrimop .Leq [.vInt 5, .vInt 5] = some (.vBool true)
#guard interpPrimop .Leq [.vInt 6, .vInt 5] = some (.vBool false)
#guard interpPrimop .Gt [.vInt 5, .vInt 3] = some (.vBool true)
#guard interpPrimop .Gt [.vInt 3, .vInt 3] = some (.vBool false)
#guard interpPrimop .Geq [.vInt 5, .vInt 3] = some (.vBool true)
#guard interpPrimop .Geq [.vInt 3, .vInt 3] = some (.vBool true)
#guard interpPrimop .Geq [.vInt 2, .vInt 3] = some (.vBool false)

/-! ## interpPrimop: Boolean -/

#guard interpPrimop .And [.vBool true, .vBool false] = some (.vBool false)
#guard interpPrimop .Or [.vBool false, .vBool false] = some (.vBool false)
#guard interpPrimop .Or [.vBool true, .vBool false] = some (.vBool true)
#guard interpPrimop .Or [.vBool false, .vBool true] = some (.vBool true)
#guard interpPrimop .Not [.vBool true] = some (.vBool false)
#guard interpPrimop .Not [.vBool false] = some (.vBool true)
-- Implies is short-circuit, handled in interpStmt; interpPrimop returns none
#guard interpPrimop .Implies [.vBool true, .vBool false] = none

/-! ## interpPrimop: String -/

#guard interpPrimop .Eq [.vString "abc", .vString "abc"] = some (.vBool true)
#guard interpPrimop .Eq [.vString "abc", .vString "def"] = some (.vBool false)
#guard interpPrimop .Neq [.vString "a", .vString "b"] = some (.vBool true)
#guard interpPrimop .Neq [.vString "a", .vString "a"] = some (.vBool false)
#guard interpPrimop .StrConcat [.vString "a", .vString "b"] = some (.vString "ab")

/-! ## interpPrimop: Ref and Bool Eq/Neq -/

#guard interpPrimop .Eq [.vRef 0, .vRef 0] = some (.vBool true)
#guard interpPrimop .Eq [.vRef 0, .vRef 1] = some (.vBool false)
#guard interpPrimop .Neq [.vRef 0, .vRef 1] = some (.vBool true)
#guard interpPrimop .Eq [.vBool true, .vBool true] = some (.vBool true)
#guard interpPrimop .Eq [.vBool true, .vBool false] = some (.vBool false)
#guard interpPrimop .Neq [.vBool true, .vBool false] = some (.vBool true)

/-! ## interpPrimop: Type mismatch → none -/

#guard interpPrimop .Add [.vBool true, .vInt 1] = none
#guard interpPrimop .Add [.vInt 1, .vBool true] = none
#guard interpPrimop .And [.vInt 1, .vInt 2] = none
#guard interpPrimop .Or [.vInt 1, .vInt 2] = none
#guard interpPrimop .Not [.vInt 1] = none
#guard interpPrimop .Lt [.vBool true, .vBool false] = none
#guard interpPrimop .Sub [.vString "a", .vString "b"] = none
#guard interpPrimop .Neg [.vBool true] = none
#guard interpPrimop .Implies [.vInt 1, .vInt 2] = none
#guard interpPrimop .StrConcat [.vInt 1, .vInt 2] = none

/-! ## interpPrimop: Wrong arity → none -/

#guard interpPrimop .Add [.vInt 1] = none
#guard interpPrimop .Add [.vInt 1, .vInt 2, .vInt 3] = none
#guard interpPrimop .Not [.vBool true, .vBool false] = none
#guard interpPrimop .Not [] = none
#guard interpPrimop .Neg [] = none
#guard interpPrimop .Eq [.vInt 1] = none
#guard interpPrimop .And [.vBool true] = none

/-! ## Stuck states (malformed AST the parser would reject) -/

-- LiteralDecimal has no runtime representation
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.LiteralDecimal ⟨1, 5⟩) = none

-- Undefined variable
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore (.Identifier "undef") = none

-- Abstract / All / Hole
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .Abstract = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .All = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .Hole = none

-- Non-bool condition in if → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IfThenElse (mk (.LiteralInt 1)) (mk (.LiteralInt 2)) (some (mk (.LiteralInt 3)))) = none

-- Non-bool guard in while → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.While (mk (.LiteralInt 1)) [] none (mk (.LiteralInt 2))) = none

-- Re-declaration of existing variable → none
#guard (let σ₀ := singleStore "x" (.vInt 1)
  interpStmt trivialEval emptyProc 10 emptyHeap σ₀
    (.LocalVariable "x" ⟨.TInt, emd⟩ (some (mk (.LiteralInt 2))))) = none

-- Assign to undefined variable → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.Identifier "undef", emd⟩] (mk (.LiteralInt 1))) = none

-- Multi-target assign → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.Identifier "x", emd⟩, ⟨.Identifier "y", emd⟩] (mk (.LiteralInt 1))) = none

-- Assert/Assume false → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assert (mk (.LiteralBool false))) = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assert (mk (.LiteralInt 1))) = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assume (mk (.LiteralBool false))) = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assume (mk (.LiteralInt 1))) = none

-- Undefined procedure → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.StaticCall "nonexistent" []) = none

-- Wrong arg count → none
#guard (let proc : Procedure := {
    name := "f"
    inputs := [{ name := "a", type := ⟨.TInt, emd⟩ }, { name := "b", type := ⟨.TInt, emd⟩ }]
    outputs := [], preconditions := [], determinism := .deterministic none,
    isFunctional := false, decreases := none,
    body := .Transparent (mk (.LiteralInt 0)), md := emd }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" [mk (.LiteralInt 1)])) = none

-- Abstract/External body → none
#guard (let proc : Procedure := {
    name := "g", inputs := [], outputs := [], preconditions := [],
    determinism := .deterministic none, isFunctional := false, decreases := none,
    body := .Abstract [], md := emd }
  let π : ProcEnv := fun name => if name == "g" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore (.StaticCall "g" [])) = none

#guard (let proc : Procedure := {
    name := "h", inputs := [], outputs := [], preconditions := [],
    determinism := .deterministic none, isFunctional := false, decreases := none,
    body := .External, md := emd }
  let π : ProcEnv := fun name => if name == "h" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore (.StaticCall "h" [])) = none

-- Opaque with/without implementation
#guard (let proc : Procedure := {
    name := "f", inputs := [{ name := "n", type := ⟨.TInt, emd⟩ }], outputs := [],
    preconditions := [], determinism := .deterministic none, isFunctional := false,
    decreases := none,
    body := .Opaque [] (some (mk (.PrimitiveOp .Add [mk (.Identifier "n"), mk (.LiteralInt 1)]))) [],
    md := emd }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  getOutcomeRaw (interpStmt trivialEval π 10 emptyHeap emptyStore
    (.StaticCall "f" [mk (.LiteralInt 5)]))) = some (.normal (.vInt 6))

#guard (let proc : Procedure := {
    name := "f", inputs := [], outputs := [], preconditions := [],
    determinism := .deterministic none, isFunctional := false, decreases := none,
    body := .Opaque [] none [], md := emd }
  let π : ProcEnv := fun name => if name == "f" then some proc else none
  interpStmt trivialEval π 10 emptyHeap emptyStore (.StaticCall "f" [])) = none

-- FieldSelect on non-ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.FieldSelect (mk (.LiteralInt 5)) "f") = none

-- PureFieldUpdate on non-ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PureFieldUpdate (mk (.LiteralInt 5)) "f" (mk (.LiteralInt 1))) = none

-- ReferenceEquals on non-ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.ReferenceEquals (mk (.LiteralInt 1)) (mk (.LiteralInt 1))) = none

-- This with no "this" in store → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore .This = none

-- IsType on non-ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.IsType (mk (.LiteralInt 5)) ⟨.UserDefined "T", emd⟩) = none

-- Field assignment to unallocated ref → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.Assign [⟨.FieldSelect (mk (.LiteralInt 5)) "f", emd⟩] (mk (.LiteralInt 1))) = none

/-! ## Short-circuit semantics -/

-- AndThen short-circuits: false && (stuck) → false
#guard getOutcomeRaw (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .AndThen [mk (.LiteralBool false), mk (.Identifier "undef")]))
  = some (.normal (.vBool false))

-- OrElse short-circuits: true || (stuck) → true
#guard getOutcomeRaw (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .OrElse [mk (.LiteralBool true), mk (.Identifier "undef")]))
  = some (.normal (.vBool true))

-- Implies short-circuits: false => (stuck) → true
#guard getOutcomeRaw (interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Implies [mk (.LiteralBool false), mk (.Identifier "undef")]))
  = some (.normal (.vBool true))

-- Non-short-circuit cases → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .AndThen [mk (.LiteralBool true), mk (.Identifier "undef")]) = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .OrElse [mk (.LiteralBool false), mk (.Identifier "undef")]) = none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.PrimitiveOp .Implies [mk (.LiteralBool true), mk (.Identifier "undef")]) = none

/-! ## Fuel exhaustion -/

#guard interpStmt trivialEval emptyProc 0 emptyHeap emptyStore (.LiteralInt 1) = none
#guard interpBlock trivialEval emptyProc 0 emptyHeap emptyStore [mk (.LiteralInt 1)] = none
#guard interpArgs trivialEval emptyProc 0 emptyHeap emptyStore [mk (.LiteralInt 1)] = none
#guard interpArgs trivialEval emptyProc 10 emptyHeap emptyStore
    [mk (.LiteralInt 1), mk (.Identifier "undef")] = none

/-! ## δ delegation (specification constructs) -/

-- Forall
#guard (let δ : LaurelEval := fun _ expr =>
    match expr with | .Forall _ _ _ => some (.vBool true) | _ => none
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Forall ⟨"x", ⟨.TInt, emd⟩⟩ none (mk (.LiteralBool true)))))
  = some (.normal (.vBool true))

-- Exists
#guard (let δ : LaurelEval := fun _ expr =>
    match expr with | .Exists _ _ _ => some (.vBool true) | _ => none
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Exists ⟨"x", ⟨.TInt, emd⟩⟩ none (mk (.LiteralBool true)))))
  = some (.normal (.vBool true))

-- Old
#guard (let δ : LaurelEval := fun st expr =>
    match expr with | .Old ⟨.Identifier name, _⟩ => st name.text | _ => trivialEval st expr
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap (singleStore "x" (.vInt 99))
    (.Old (mk (.Identifier "x")))))
  = some (.normal (.vInt 99))

-- Fresh
#guard (let δ : LaurelEval := fun _ expr =>
    match expr with | .Fresh _ => some (.vBool true) | _ => none
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Fresh (mk (.Identifier "x")))))
  = some (.normal (.vBool true))

-- Assigned
#guard (let δ : LaurelEval := fun _ expr =>
    match expr with | .Assigned _ => some (.vBool false) | _ => none
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.Assigned (mk (.Identifier "x")))))
  = some (.normal (.vBool false))

-- ContractOf
#guard (let δ : LaurelEval := fun _ expr =>
    match expr with | .ContractOf .Precondition _ => some (.vBool true) | _ => none
  getOutcomeRaw (interpStmt δ emptyProc 10 emptyHeap emptyStore
    (.ContractOf .Precondition (mk (.Identifier "f")))))
  = some (.normal (.vBool true))

-- ContractOf with no handler → none
#guard interpStmt trivialEval emptyProc 10 emptyHeap emptyStore
    (.ContractOf .Precondition (mk (.Identifier "f"))) = none

/-! ## Programmatic AST tests for interpProgram -/

-- Success classification
#guard match interpProgram (mkProgram [mkProc "main" [] (.LiteralInt 42)]) with
  | .success (.vInt 42) _ _ => true | _ => false

-- Returned classification
#guard match interpProgram (mkProgram [mkProc "main" [] (.Return (some (mk (.LiteralInt 99))))]) with
  | .returned (some (.vInt 99)) _ _ => true | _ => false

-- Opaque procedure with no body → noBody
#guard
  let mainProc : Procedure := {
    name := "main", inputs := [], outputs := [],
    preconditions := [], determinism := .deterministic none, isFunctional := false,
    decreases := none, body := .Opaque [] none [], md := emd }
  match interpProgram (mkProgram [mainProc]) with
  | .noBody => true | _ => false

-- Instance method call via buildProcEnv
#guard
  let getXProc : Procedure := {
    name := "getX"
    inputs := [⟨"this", ⟨.UserDefined "Point", emd⟩⟩]
    outputs := [], preconditions := [], determinism := .deterministic none,
    isFunctional := false, decreases := none,
    body := .Transparent (mk (.Return (some (mk (.FieldSelect (mk (.This)) "x"))))),
    md := emd }
  let pointType : TypeDefinition := .Composite {
    name := "Point", extending := [],
    fields := [{ name := "x", isMutable := true, type := ⟨.TInt, emd⟩ }],
    instanceProcedures := [getXProc] }
  let body := StmtExpr.Block [
    mk (.LocalVariable "p" ⟨.UserDefined "Point", emd⟩ (some (mk (.New "Point")))),
    mk (.Assign [⟨.FieldSelect (mk (.Identifier "p")) "x", emd⟩] (mk (.LiteralInt 7))),
    mk (.Return (some (mk (.InstanceCall (mk (.Identifier "p")) "getX" []))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body], staticFields := [],
    types := [pointType], constants := [] }
  getOutcome (interpProgram prog) = some (.vInt 7)

-- Static fields initialized to vVoid
#guard
  let body := StmtExpr.Block [
    mk (.Assign [⟨.Identifier "counter", emd⟩] (mk (.LiteralInt 10))),
    mk (.Return (some (mk (.Identifier "counter"))))
  ] none
  let prog : Program := {
    staticProcedures := [mkProc "main" [] body],
    staticFields := [{ name := "counter", isMutable := true, type := ⟨.TInt, emd⟩ }],
    types := [], constants := [] }
  getOutcome (interpProgram prog) = some (.vInt 10)

end Strata.Laurel.InterpreterInternals

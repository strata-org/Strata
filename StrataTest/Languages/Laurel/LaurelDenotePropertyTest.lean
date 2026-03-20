/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelDenote
import Plausible

/-!
# Property-Based Tests for Laurel Denotational Interpreter

Plausible-based property tests validating structural invariants of the
Laurel denotational interpreter across randomly generated inputs.
-/

namespace Strata.Laurel.DenotePropertyTest

open Strata.Laurel
open Plausible

/-! ## Test Infrastructure -/

abbrev emd : Imperative.MetaData Core.Expression := .empty
def mk (s : StmtExpr) : StmtExprMd := ⟨s, emd⟩
def mkTy (t : HighType) : HighTypeMd := ⟨t, emd⟩

def emptyStore : LaurelStore := fun _ => none
def emptyHeap : LaurelHeap := fun _ => none
def emptyProc : ProcEnv := fun _ => none
def trivialEval : LaurelEval := fun _ _ => none

def idNames : List String := ["x", "y", "z", "a", "b"]

/-- Check if two results agree on outcome and a specific variable.
    TODO: This ignores the heap component — a counterexample differing only in
    heap state would be missed. Consider comparing the full result triple. -/
def resultAgrees (r1 r2 : Option (Outcome × LaurelStore × LaurelHeap))
    (vars : List String) : Bool :=
  match r1, r2 with
  | some (o1, σ1, _), some (o2, σ2, _) =>
    o1 == o2 && vars.all (fun v => σ1 v == σ2 v)
  | none, none => true
  | _, _ => false

/-! ## Repr / Shrinkable / Arbitrary for LaurelValue -/

instance : Shrinkable LaurelValue where
  shrink
    | .vInt i => (Shrinkable.shrink i).map .vInt
    | .vBool _ => []
    | .vString s => (Shrinkable.shrink s).map .vString
    | .vVoid => []
    | .vRef n => (Shrinkable.shrink n).map .vRef

instance : Arbitrary LaurelValue where
  arbitrary := do
    let tag ← Gen.choose Nat 0 4 (by omega)
    match tag.val with
    | 0 => return .vInt (← Arbitrary.arbitrary)
    | 1 => return .vBool (← Arbitrary.arbitrary)
    | 2 => return .vString (← Arbitrary.arbitrary)
    | 3 => return .vVoid
    | _ => return .vRef (← Gen.choose Nat 0 9 (by omega))

/-! ## Simplified Test Expression -/

/-- A simplified expression type for property testing. -/
inductive TestExpr where
  | litInt (i : Int)
  | litBool (b : Bool)
  | litStr (s : String)
  | ident (name : String)
  | primOp (op : Operation) (args : List TestExpr)
  | ite (c t e : TestExpr)
  | block (stmts : List TestExpr)
  | assign (name : String) (val : TestExpr)
  | localVar (name : String) (init : TestExpr)
  | exit_ (label : String)
  deriving Repr

def TestExpr.inferType : TestExpr → HighType
  | .litBool _ => .TBool
  | .litStr _ => .TString
  | _ => .TInt

def TestExpr.toStmtExpr : TestExpr → StmtExpr
  | .litInt i => .LiteralInt i
  | .litBool b => .LiteralBool b
  | .litStr s => .LiteralString s
  | .ident n => .Identifier (mkId n)
  | .primOp op args => .PrimitiveOp op (args.map (mk ·.toStmtExpr))
  | .ite c t e => .IfThenElse (mk c.toStmtExpr) (mk t.toStmtExpr) (some (mk e.toStmtExpr))
  | .block ss => .Block (ss.map (mk ·.toStmtExpr)) none
  | .assign n v => .Assign [mk (.Identifier (mkId n))] (mk v.toStmtExpr)
  | .localVar n init => .LocalVariable (mkId n) (mkTy init.inferType) (some (mk init.toStmtExpr))
  | .exit_ l => .Exit l

/-! ## Generators -/

instance : Inhabited Operation where
  default := .Add

instance : Arbitrary Operation where
  arbitrary := do
    let ops := #[Operation.Eq, .Neq, .And, .Or, .Not, .Implies, .Neg,
                 .Add, .Sub, .Mul, .Div, .Mod, .DivT, .ModT,
                 .Lt, .Leq, .Gt, .Geq, .StrConcat]
    let i ← Gen.choose Nat 0 (ops.size - 1) (by omega)
    return ops[i.val]!

instance : Shrinkable Operation where
  shrink _ := []

/-- Depth-bounded generator for TestExpr. -/
partial def genTestExpr (depth : Nat) : Gen TestExpr := do
  match depth with
  | 0 =>
    let tag ← Gen.choose Nat 0 3 (by omega)
    match tag.val with
    | 0 => return .litInt (← Arbitrary.arbitrary)
    | 1 => return .litBool (← Arbitrary.arbitrary)
    | 2 => return .litStr (← Arbitrary.arbitrary)
    | _ =>
      let i ← Gen.choose Nat 0 (idNames.length - 1) (by omega)
      return .ident idNames[i.val]!
  | d + 1 =>
    let tag ← Gen.choose Nat 0 7 (by omega)
    match tag.val with
    | 0 => return .litInt (← Arbitrary.arbitrary)
    | 1 => return .litBool (← Arbitrary.arbitrary)
    | 2 =>
      let a ← genTestExpr d; let b ← genTestExpr d
      return .primOp .Add [a, b]
    | 3 =>
      let a ← genTestExpr d; let b ← genTestExpr d
      return .primOp .Lt [a, b]
    | 4 =>
      let c ← genTestExpr d; let t ← genTestExpr d; let e ← genTestExpr d
      return .ite c t e
    | 5 =>
      let len ← Gen.choose Nat 1 3 (by omega)
      let stmts ← List.range len.val |>.mapM (fun _ => genTestExpr d)
      return .block stmts
    | 6 =>
      let i ← Gen.choose Nat 0 (idNames.length - 1) (by omega)
      let v ← genTestExpr d
      return .assign idNames[i.val]! v
    | _ =>
      let i ← Gen.choose Nat 0 (idNames.length - 1) (by omega)
      let v ← genTestExpr d
      return .localVar idNames[i.val]! v

instance : Shrinkable TestExpr where
  shrink
    | .litInt i => (Shrinkable.shrink i).map .litInt
    | .litBool _ => []
    | .litStr s => (Shrinkable.shrink s).map .litStr
    | .ident _ => []
    | .primOp _ args => args
    | .ite c t e => [c, t, e]
    | .block ss => ss
    | .assign _ v => [v]
    | .localVar _ v => [v]
    | .exit_ _ => []

instance : Arbitrary TestExpr where
  arbitrary := genTestExpr 2

/-! ## Store Generator -/

/-- Wrapper for store generation in Plausible. -/
structure TestStore where
  store : LaurelStore
  vars : List String  -- track which vars are set for comparison

instance : Repr TestStore where
  reprPrec _ _ := "⟨TestStore⟩"

instance : Shrinkable TestStore where
  shrink _ := []

instance : Arbitrary TestStore where
  arbitrary := do
    let mut σ : LaurelStore := fun _ => none
    let mut vs : List String := []
    for name in idNames do
      let include_ ← Arbitrary.arbitrary (α := Bool)
      if include_ then
        let v ← Arbitrary.arbitrary (α := LaurelValue)
        σ := fun x => if x == name then some v else σ x
        vs := name :: vs
    return ⟨σ, vs⟩

/-! ## 1. Fuel Monotonicity -/

/-- If denoteStmt succeeds with fuel₁, it gives the same result with fuel₁ + k. -/
def fuelMonoProp (e : TestExpr) (ts : TestStore) (fuel₁ : Fin 20) (k : Fin 20) : Bool :=
  let s := e.toStmtExpr
  let f1 := fuel₁.val + 1
  let f2 := f1 + k.val
  let r1 := denoteStmt trivialEval emptyProc f1 emptyHeap ts.store s
  let r2 := denoteStmt trivialEval emptyProc f2 emptyHeap ts.store s
  match r1 with
  | some _ => resultAgrees r1 r2 ts.vars
  | none => true

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ e : TestExpr, ∀ ts : TestStore, ∀ f1 : Fin 20, ∀ k : Fin 20,
    fuelMonoProp e ts f1 k)

/-! ## 2. Determinism: Unused Store Entries Don't Affect Literals -/

/-- Adding an unused variable to the store doesn't change literal evaluation. -/
def unusedStoreIrrelevantProp (i : Int) (extraVal : LaurelValue) : Bool :=
  let σ1 : LaurelStore := emptyStore
  let σ2 : LaurelStore := fun x => if x == "__unused__" then some extraVal else none
  let r1 := denoteStmt trivialEval emptyProc 5 emptyHeap σ1 (.LiteralInt i)
  let r2 := denoteStmt trivialEval emptyProc 5 emptyHeap σ2 (.LiteralInt i)
  match r1, r2 with
  | some (o1, _, _), some (o2, _, _) => o1 == o2
  | none, none => true
  | _, _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ i : Int, ∀ v : LaurelValue, unusedStoreIrrelevantProp i v)

/-! ## 3. Literal Stability -/

/-- Literals return the corresponding value and don't modify the store. -/
def litIntStable (i : Int) : Bool :=
  let σ : LaurelStore := fun x => if x == "x" then some (.vInt 42) else none
  match denoteStmt trivialEval emptyProc 5 emptyHeap σ (.LiteralInt i) with
  | some (.normal (.vInt j), σ', _) => i == j && σ' "x" == some (.vInt 42)
  | _ => false

def litBoolStable (b : Bool) : Bool :=
  let σ : LaurelStore := fun x => if x == "x" then some (.vInt 42) else none
  match denoteStmt trivialEval emptyProc 5 emptyHeap σ (.LiteralBool b) with
  | some (.normal (.vBool b'), σ', _) => b == b' && σ' "x" == some (.vInt 42)
  | _ => false

def litStrStable (s : String) : Bool :=
  let σ : LaurelStore := fun x => if x == "x" then some (.vInt 42) else none
  match denoteStmt trivialEval emptyProc 5 emptyHeap σ (.LiteralString s) with
  | some (.normal (.vString s'), σ', _) => s == s' && σ' "x" == some (.vInt 42)
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ i : Int, litIntStable i)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ b : Bool, litBoolStable b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ s : String, litStrStable s)

/-! ## 4. evalPrimOp Totality on Well-Typed Inputs -/

/-- Arithmetic ops on ints return some (except div/mod by zero). -/
def arithTotalProp (a b : Int) : Bool :=
  (evalPrimOp .Add [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Sub [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Mul [.vInt a, .vInt b]).isSome &&
  (b == 0 || (evalPrimOp .Div [.vInt a, .vInt b]).isSome) &&
  (b == 0 || (evalPrimOp .Mod [.vInt a, .vInt b]).isSome) &&
  (evalPrimOp .Neg [.vInt a]).isSome

/-- Boolean ops on bools return some. -/
def boolTotalProp (a b : Bool) : Bool :=
  (evalPrimOp .And [.vBool a, .vBool b]).isSome &&
  (evalPrimOp .Or [.vBool a, .vBool b]).isSome &&
  (evalPrimOp .Not [.vBool a]).isSome &&
  (evalPrimOp .Implies [.vBool a, .vBool b]).isSome

/-- Comparison ops on ints return some. -/
def cmpTotalProp (a b : Int) : Bool :=
  (evalPrimOp .Lt [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Leq [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Gt [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Geq [.vInt a, .vInt b]).isSome

/-- Equality ops on same-typed values return some. -/
def eqTotalProp (a b : Int) (c d : Bool) (s t : String) : Bool :=
  (evalPrimOp .Eq [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Neq [.vInt a, .vInt b]).isSome &&
  (evalPrimOp .Eq [.vBool c, .vBool d]).isSome &&
  (evalPrimOp .Neq [.vBool c, .vBool d]).isSome &&
  (evalPrimOp .Eq [.vString s, .vString t]).isSome &&
  (evalPrimOp .Neq [.vString s, .vString t]).isSome

/-- String concat on strings returns some. -/
def strConcatTotalProp (a b : String) : Bool :=
  (evalPrimOp .StrConcat [.vString a, .vString b]).isSome

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, arithTotalProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Bool, boolTotalProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, cmpTotalProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, ∀ c d : Bool, ∀ s t : String, eqTotalProp a b c d s t)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : String, strConcatTotalProp a b)

/-! ## 5. evalPrimOp Type Preservation -/

def isVInt : LaurelValue → Bool
  | .vInt _ => true
  | _ => false

def isVBool : LaurelValue → Bool
  | .vBool _ => true
  | _ => false

def isVString : LaurelValue → Bool
  | .vString _ => true
  | _ => false

/-- Arithmetic ops on ints return int. -/
def arithTypePresProp (a b : Int) : Bool :=
  let chk := fun r => match r with | some v => isVInt v | none => true
  chk (evalPrimOp .Add [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Sub [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Mul [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Neg [.vInt a]) &&
  chk (evalPrimOp .Div [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Mod [.vInt a, .vInt b]) &&
  chk (evalPrimOp .DivT [.vInt a, .vInt b]) &&
  chk (evalPrimOp .ModT [.vInt a, .vInt b])

/-- Boolean ops on bools return bool. -/
def boolTypePresProp (a b : Bool) : Bool :=
  let chk := fun r => match r with | some v => isVBool v | none => true
  chk (evalPrimOp .And [.vBool a, .vBool b]) &&
  chk (evalPrimOp .Or [.vBool a, .vBool b]) &&
  chk (evalPrimOp .Not [.vBool a]) &&
  chk (evalPrimOp .Implies [.vBool a, .vBool b])

/-- Comparison ops return bool. -/
def cmpTypePresProp (a b : Int) : Bool :=
  let chk := fun r => match r with | some v => isVBool v | none => true
  chk (evalPrimOp .Lt [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Leq [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Gt [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Geq [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Eq [.vInt a, .vInt b]) &&
  chk (evalPrimOp .Neq [.vInt a, .vInt b])

/-- String concat returns string. -/
def strConcatTypePresProp (a b : String) : Bool :=
  match evalPrimOp .StrConcat [.vString a, .vString b] with
  | some v => isVString v
  | none => true

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, arithTypePresProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Bool, boolTypePresProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, cmpTypePresProp a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : String, strConcatTypePresProp a b)

/-! ## 6. Block Value Is Last Statement's Value -/

/-- A block of int literals returns the value of the last literal. -/
def blockLastValueProp2 (a b : Int) : Bool :=
  let stmts := [mk (.LiteralInt a), mk (.LiteralInt b)]
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore stmts with
  | some (.normal (.vInt v), _, _) => v == b
  | _ => false

def blockLastValueProp3 (a b c : Int) : Bool :=
  let stmts := [mk (.LiteralInt a), mk (.LiteralInt b), mk (.LiteralInt c)]
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore stmts with
  | some (.normal (.vInt v), _, _) => v == c
  | _ => false

def blockSingletonProp (a : Int) : Bool :=
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore [mk (.LiteralInt a)] with
  | some (.normal (.vInt v), _, _) => v == a
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b : Int, blockLastValueProp2 a b)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a b c : Int, blockLastValueProp3 a b c)

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ a : Int, blockSingletonProp a)

/-! ## 7. Exit Propagation -/

/-- If a block contains an Exit, the block produces .exit regardless of
    statements after it. -/
def exitPropagationProp (i : Int) (label : String) (j : Int) : Bool :=
  let stmts := [mk (.LiteralInt i), mk (.Exit label), mk (.LiteralInt j)]
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore stmts with
  | some (.exit l, _, _) => l == label
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ i : Int, ∀ label : String, ∀ j : Int, exitPropagationProp i label j)

/-- Exit at the first position also propagates. -/
def exitFirstProp (label : String) (i : Int) : Bool :=
  let stmts := [mk (.Exit label), mk (.LiteralInt i)]
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore stmts with
  | some (.exit l, _, _) => l == label
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ label : String, ∀ i : Int, exitFirstProp label i)

/-! ## 8. Store Threading in Blocks -/

/-- LocalVariable followed by Identifier lookup returns the initialized value. -/
def storeThreadingIntProp (v : Int) : Bool :=
  let name := mkId "fresh_var"
  let localDecl := mk (.LocalVariable name (mkTy .TInt) (some (mk (.LiteralInt v))))
  let lookup := mk (.Identifier name)
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore [localDecl, lookup] with
  | some (.normal (.vInt v'), _, _) => v == v'
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ v : Int, storeThreadingIntProp v)

/-- LocalVariable with bool value followed by lookup. -/
def storeThreadingBoolProp (b : Bool) : Bool :=
  let name := mkId "fresh_var"
  let localDecl := mk (.LocalVariable name (mkTy .TBool) (some (mk (.LiteralBool b))))
  let lookup := mk (.Identifier name)
  match denoteBlock trivialEval emptyProc 20 emptyHeap emptyStore [localDecl, lookup] with
  | some (.normal (.vBool b'), _, _) => b == b'
  | _ => false

#eval Testable.check (cfg := { numInst := 300, quiet := true })
  (∀ b : Bool, storeThreadingBoolProp b)

end Strata.Laurel.DenotePropertyTest

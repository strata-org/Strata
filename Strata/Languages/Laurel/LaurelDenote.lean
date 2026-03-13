/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelSemantics

/-!
# Fuel-Based Denotational Interpreter for Laurel IR

A computable interpreter mirroring the relational semantics in
`LaurelSemantics.lean` (Option A from the design document
`docs/designs/denotational-semantics-for-laurel-as-an-interprete.md`).

## Design

Three mutually recursive functions with a `fuel : Nat` parameter
decremented on every recursive call. Returns `none` on fuel exhaustion
or stuck states. Reuses existing `Outcome`, `LaurelValue`, `LaurelStore`,
`LaurelHeap` types unchanged.

## Intentionally Omitted Constructs

`Abstract`, `All`, `Hole` return `none`, matching the relational semantics
(which gets stuck on these).
-/

namespace Strata.Laurel

/-! ## Computable Store/Heap Helpers -/

/-- Update an existing variable in the store. Returns `none` if the variable is not present. -/
def updateStore (σ : LaurelStore) (x : Identifier) (v : LaurelValue) : Option LaurelStore :=
  match σ x with
  | some _ => some (fun y => if y == x then some v else σ y)
  | none => none

/-- Initialize a new variable in the store. Returns `none` if the variable already exists. -/
def initStore (σ : LaurelStore) (x : Identifier) (v : LaurelValue) : Option LaurelStore :=
  match σ x with
  | none => some (fun y => if y == x then some v else σ y)
  | some _ => none

/-- Find the smallest free address in the heap, searching up to `bound` addresses from `n`. -/
def findSmallestFree (h : LaurelHeap) (n : Nat) (bound : Nat := 10000) : Nat :=
  match bound with
  | 0 => n
  | bound + 1 =>
    match h n with
    | some _ => findSmallestFree h (n + 1) bound
    | none => n

/-- Allocate a new object on the heap with the given type name. -/
def allocHeap (h : LaurelHeap) (typeName : Identifier) : Option (Nat × LaurelHeap) :=
  let addr := findSmallestFree h 0
  some (addr, fun a => if a == addr then some (typeName, fun _ => none) else h a)

/-- Write a value to a field of a heap object. Returns `none` if the address is not allocated. -/
def heapFieldWrite' (h : LaurelHeap) (addr : Nat) (field : Identifier) (v : LaurelValue)
    : Option LaurelHeap :=
  match h addr with
  | some (tag, fields) =>
      some (fun a => if a == addr then some (tag, fun f => if f == field then some v else fields f) else h a)
  | none => none

/-! ## Denotational Interpreter -/

mutual
/-- Evaluate a single statement/expression. -/
def denoteStmt (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (h : LaurelHeap) (σ : LaurelStore) (stmt : StmtExpr)
    : Option (Outcome × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stmt with
    -- Literals
    | .LiteralInt i => some (.normal (.vInt i), σ, h)
    | .LiteralBool b => some (.normal (.vBool b), σ, h)
    | .LiteralString s => some (.normal (.vString s), σ, h)

    -- Variables
    | .Identifier name =>
      match σ name with
      | some v => some (.normal v, σ, h)
      | none => none

    -- Primitive Operations
    | .PrimitiveOp op args =>
      match denoteArgs δ π fuel h σ args with
      | some (vals, σ', h') =>
        match evalPrimOp op vals with
        | some result => some (.normal result, σ', h')
        | none => none
      | none => none

    -- Control Flow
    | .IfThenElse c thenBr (some elseBr) =>
      match denoteStmt δ π fuel h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) => denoteStmt δ π fuel h₁ σ₁ thenBr.val
      | some (.normal (.vBool false), σ₁, h₁) => denoteStmt δ π fuel h₁ σ₁ elseBr.val
      | _ => none

    | .IfThenElse c thenBr none =>
      match denoteStmt δ π fuel h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) => denoteStmt δ π fuel h₁ σ₁ thenBr.val
      | some (.normal (.vBool false), σ₁, h₁) => some (.normal .vVoid, σ₁, h₁)
      | _ => none

    | .Block stmts label =>
      match denoteBlock δ π fuel h σ stmts with
      | some (outcome, σ', h') => some (catchExit label outcome, σ', h')
      | none => none

    | .Exit target => some (.exit target, σ, h)

    | .Return (some val) =>
      match denoteStmt δ π fuel h σ val.val with
      | some (.normal v, σ', h') => some (.ret (some v), σ', h')
      | _ => none

    | .Return none => some (.ret none, σ, h)

    -- While Loop
    | .While c invs dec body =>
      match denoteStmt δ π fuel h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        match denoteStmt δ π fuel h₁ σ₁ body.val with
        | some (.normal _, σ₂, h₂) =>
          denoteStmt δ π fuel h₂ σ₂ (.While c invs dec body)
        | some (.exit label, σ₂, h₂) => some (.exit label, σ₂, h₂)
        | some (.ret rv, σ₂, h₂) => some (.ret rv, σ₂, h₂)
        | none => none
      | some (.normal (.vBool false), σ₁, h₁) => some (.normal .vVoid, σ₁, h₁)
      | _ => none

    -- Assignments
    | .Assign [⟨.Identifier name, _⟩] value =>
      match denoteStmt δ π fuel h σ value.val with
      | some (.normal v, σ₁, h₁) =>
        match σ₁ name with
        | some _ =>
          match updateStore σ₁ name v with
          | some σ₂ => some (.normal v, σ₂, h₁)
          | none => none
        | none => none
      | _ => none

    -- Field Assignment
    | .Assign [⟨.FieldSelect target fieldName, _⟩] value =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match denoteStmt δ π fuel h₁ σ₁ value.val with
        | some (.normal v, σ₂, h₂) =>
          match heapFieldWrite' h₂ addr fieldName v with
          | some h₃ => some (.normal v, σ₂, h₃)
          | none => none
        | _ => none
      | _ => none

    | .Assign _ _ => none  -- multi-target not supported

    | .LocalVariable name _ty (some init) =>
      match denoteStmt δ π fuel h σ init.val with
      | some (.normal v, σ₁, h₁) =>
        match initStore σ₁ name v with
        | some σ₂ => some (.normal .vVoid, σ₂, h₁)
        | none => none
      | _ => none

    | .LocalVariable name _ty none =>
      match initStore σ name .vVoid with
      | some σ' => some (.normal .vVoid, σ', h)
      | none => none

    -- Verification Constructs
    -- The relational semantics requires assert/assume conditions to be pure
    -- (no side effects). We evaluate the condition and check it's true,
    -- but return the original store/heap since conditions must be pure.
    | .Assert c =>
      match denoteStmt δ π fuel h σ c.val with
      | some (.normal (.vBool true), _, _) => some (.normal .vVoid, σ, h)
      | _ => none

    | .Assume c =>
      match denoteStmt δ π fuel h σ c.val with
      | some (.normal (.vBool true), _, _) => some (.normal .vVoid, σ, h)
      | _ => none

    -- Static Calls
    | .StaticCall callee args =>
      match π callee with
      | some proc =>
        match denoteArgs δ π fuel h σ args with
        | some (vals, σ₁, h₁) =>
          match bindParams proc.inputs vals with
          | some σBound =>
            match getBody proc with
            | some body =>
              match denoteStmt δ π fuel h₁ σBound body.val with
              | some (.normal v, _, h') => some (.normal v, σ₁, h')
              | some (.ret (some v), _, h') => some (.normal v, σ₁, h')
              | some (.ret none, _, h') => some (.normal .vVoid, σ₁, h')
              | _ => none
            | none => none
          | none => none
        | none => none
      | none => none

    -- OO Features
    | .New typeName =>
      match allocHeap h typeName with
      | some (addr, h') => some (.normal (.vRef addr), σ, h')
      | none => none

    | .FieldSelect target fieldName =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match heapFieldRead h₁ addr fieldName with
        | some v => some (.normal v, σ₁, h₁)
        | none => none
      | _ => none

    | .PureFieldUpdate target fieldName newVal =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match denoteStmt δ π fuel h₁ σ₁ newVal.val with
        | some (.normal v, σ₂, h₂) =>
          match heapFieldWrite' h₂ addr fieldName v with
          | some h₃ => some (.normal (.vRef addr), σ₂, h₃)
          | none => none
        | _ => none
      | _ => none

    | .ReferenceEquals lhs rhs =>
      match denoteStmt δ π fuel h σ lhs.val with
      | some (.normal (.vRef a), σ₁, h₁) =>
        match denoteStmt δ π fuel h₁ σ₁ rhs.val with
        | some (.normal (.vRef b), σ₂, h₂) =>
          some (.normal (.vBool (a == b)), σ₂, h₂)
        | _ => none
      | _ => none

    | .InstanceCall target callee args =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match h₁ addr with
        | some (typeName, _) =>
          match π (typeName ++ "." ++ callee) with
          | some proc =>
            match denoteArgs δ π fuel h₁ σ₁ args with
            | some (vals, σ₂, h₂) =>
              match bindParams proc.inputs ((.vRef addr) :: vals) with
              | some σBound =>
                match getBody proc with
                | some body =>
                  match denoteStmt δ π fuel h₂ σBound body.val with
                  | some (.normal v, _, h₃) => some (.normal v, σ₂, h₃)
                  | some (.ret (some v), _, h₃) => some (.normal v, σ₂, h₃)
                  | some (.ret none, _, h₃) => some (.normal .vVoid, σ₂, h₃)
                  | _ => none
                | none => none
              | none => none
            | none => none
          | none => none
        | none => none
      | _ => none

    | .This =>
      match σ "this" with
      | some v => some (.normal v, σ, h)
      | none => none

    -- Type Operations
    | .IsType target ty =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match h₁ addr with
        | some (actualType, _) =>
          some (.normal (.vBool (actualType == ty.val.typeName)), σ₁, h₁)
        | none => none
      | _ => none

    | .AsType target _ty =>
      match denoteStmt δ π fuel h σ target.val with
      | some (.normal v, σ₁, h₁) => some (.normal v, σ₁, h₁)
      | _ => none

    -- Quantifiers (delegated to δ)
    | .Forall name ty body =>
      match δ σ (.Forall name ty body) with
      | some v => some (.normal v, σ, h)
      | none => none

    | .Exists name ty body =>
      match δ σ (.Exists name ty body) with
      | some v => some (.normal v, σ, h)
      | none => none

    -- Specification Constructs (delegated to δ)
    | .Old val =>
      match δ σ (.Old val) with
      | some v => some (.normal v, σ, h)
      | none => none

    | .Fresh val =>
      match δ σ (.Fresh val) with
      | some v => some (.normal v, σ, h)
      | none => none

    | .Assigned name =>
      match δ σ (.Assigned name) with
      | some v => some (.normal v, σ, h)
      | none => none

    | .ProveBy value _proof =>
      denoteStmt δ π fuel h σ value.val

    | .ContractOf ct func =>
      match δ σ (.ContractOf ct func) with
      | some v => some (.normal v, σ, h)
      | none => none

    -- Intentionally omitted
    | .Abstract => none
    | .All => none
    | .Hole => none

/-- Evaluate a block (list of statements). -/
def denoteBlock (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (h : LaurelHeap) (σ : LaurelStore) (stmts : List StmtExprMd)
    : Option (Outcome × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stmts with
    | [] => some (.normal .vVoid, σ, h)
    | [s] =>
      denoteStmt δ π fuel h σ s.val
    | s :: rest =>
      match denoteStmt δ π fuel h σ s.val with
      | some (.normal _, σ₁, h₁) => denoteBlock δ π fuel h₁ σ₁ rest
      | some (.exit label, σ₁, h₁) => some (.exit label, σ₁, h₁)
      | some (.ret rv, σ₁, h₁) => some (.ret rv, σ₁, h₁)
      | none => none

/-- Evaluate a list of arguments left-to-right, threading heap and store. -/
def denoteArgs (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (h : LaurelHeap) (σ : LaurelStore) (args : List StmtExprMd)
    : Option (List LaurelValue × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match args with
    | [] => some ([], σ, h)
    | e :: es =>
      match denoteStmt δ π fuel h σ e.val with
      | some (.normal v, σ₁, h₁) =>
        match denoteArgs δ π fuel h₁ σ₁ es with
        | some (vs, σ₂, h₂) => some (v :: vs, σ₂, h₂)
        | none => none
      | _ => none
end

end Strata.Laurel

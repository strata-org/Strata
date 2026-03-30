/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelSemantics

/-!
# Fuel-Based Interpreter for Laurel IR

A computable interpreter mirroring the relational semantics in
`LaurelSemantics.lean` (Option A from the design document
`docs/designs/denotational-semantics-for-laurel-as-an-interprete.md`).

## Design

Three mutually recursive functions with a `fuel : Nat` parameter
decremented on every recursive call. Returns `none` on fuel exhaustion
or stuck states. Reuses existing `Outcome`, `LaurelValue`, `LaurelStore`,
`LaurelHeap` types unchanged.

## Delegation via `δ : LaurelEval`

The `δ` parameter is a callback that lets callers plug in custom handling
for constructs the interpreter cannot evaluate natively (quantifiers,
specification constructs like `Old`, `Fresh`, `Assigned`, `ContractOf`).
The default `δ` (`defaultEval` in `LaurelConcreteEval.lean`) returns `none`
for all of these, which is equivalent to "stuck / not implemented".
Test harnesses can provide richer `δ` implementations.

## Intentionally Omitted Constructs

`Abstract`, `All`, `Hole` return `none`, matching the relational semantics
(which gets stuck on these).
-/

namespace Strata.Laurel

/-! ## Computable Store/Heap Helpers -/

/-- Update an existing variable in the store. Returns `none` if the variable is not present. -/
def updateStore (store : LaurelStore) (x : Identifier) (v : LaurelValue) : Option LaurelStore :=
  match store x.text with
  | some _ => some (fun y => if y == x.text then some v else store y)
  | none => none

/-- Initialize a new variable in the store. Returns `none` if the variable already exists. -/
def initStore (store : LaurelStore) (x : Identifier) (v : LaurelValue) : Option LaurelStore :=
  match store x.text with
  | none => some (fun y => if y == x.text then some v else store y)
  | some _ => none

/-- Upper bound on the address range searched by `findSmallestFree` and `allocHeap`. -/
def heapSearchBound : Nat := 10000

/-- Find the smallest free address in the heap, searching up to `bound` addresses from `n`. -/
def findSmallestFree (heap : LaurelHeap) (n : Nat) (bound : Nat := heapSearchBound) : Nat :=
  match bound with
  | 0 => n
  | bound + 1 =>
    match heap n with
    | some _ => findSmallestFree heap (n + 1) bound
    | none => n

/-- Allocate a new object on the heap with the given type name.
Returns `none` when the heap is full (all addresses in the search range are occupied). -/
def allocHeap (heap : LaurelHeap) (typeName : String) : Option (Nat × LaurelHeap) :=
  let addr := findSmallestFree heap 0
  match heap addr with
  | none => some (addr, fun a => if a == addr then some (typeName, fun _ => none) else heap a)
  | some _ => none

/-- Write a value to a field of a heap object. Returns `none` if the address is not allocated. -/
def heapFieldWrite' (heap : LaurelHeap) (addr : Nat) (field : String) (v : LaurelValue)
    : Option LaurelHeap :=
  match heap addr with
  | some (tag, fields) =>
      some (fun a => if a == addr then some (tag, fun f => if f == field then some v else fields f) else heap a)
  | none => none

/-! ## Interpreter -/

mutual
/-- Evaluate a single statement/expression. -/
def interpStmt (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (heap : LaurelHeap) (store : LaurelStore) (stmt : StmtExpr)
    : Option (Outcome × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stmt with
    -- Literals
    | .LiteralInt i => some (.normal (.vInt i), store, heap)
    | .LiteralBool b => some (.normal (.vBool b), store, heap)
    | .LiteralString s => some (.normal (.vString s), store, heap)
    | .LiteralDecimal _ => none  -- no runtime representation for decimals

    -- Variables
    | .Identifier name =>
      match store name.text with
      | some v => some (.normal v, store, heap)
      | none => none

    -- Short-circuit Primitive Operations
    | .PrimitiveOp .AndThen [a, b] =>
      match interpStmt δ π fuel heap store a.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        interpStmt δ π fuel h₁ σ₁ b.val
      | some (.normal (.vBool false), σ₁, h₁) =>
        some (.normal (.vBool false), σ₁, h₁)
      | _ => none

    | .PrimitiveOp .OrElse [a, b] =>
      match interpStmt δ π fuel heap store a.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        some (.normal (.vBool true), σ₁, h₁)
      | some (.normal (.vBool false), σ₁, h₁) =>
        interpStmt δ π fuel h₁ σ₁ b.val
      | _ => none

    | .PrimitiveOp .Implies [a, b] =>
      match interpStmt δ π fuel heap store a.val with
      | some (.normal (.vBool false), σ₁, h₁) =>
        some (.normal (.vBool true), σ₁, h₁)
      | some (.normal (.vBool true), σ₁, h₁) =>
        interpStmt δ π fuel h₁ σ₁ b.val
      | _ => none

    -- Eager Primitive Operations
    | .PrimitiveOp op args =>
      match interpArgs δ π fuel heap store args with
      | some (vals, store', h') =>
        match interpPrimop op vals with
        | some result => some (.normal result, store', h')
        | none => none
      | none => none

    -- Control Flow
    | .IfThenElse c thenBr (some elseBr) =>
      match interpStmt δ π fuel heap store c.val with
      | some (.normal (.vBool true), σ₁, h₁) => interpStmt δ π fuel h₁ σ₁ thenBr.val
      | some (.normal (.vBool false), σ₁, h₁) => interpStmt δ π fuel h₁ σ₁ elseBr.val
      | _ => none

    | .IfThenElse c thenBr none =>
      match interpStmt δ π fuel heap store c.val with
      | some (.normal (.vBool true), σ₁, h₁) => interpStmt δ π fuel h₁ σ₁ thenBr.val
      | some (.normal (.vBool false), σ₁, h₁) => some (.normal .vVoid, σ₁, h₁)
      | _ => none

    | .Block stmts label =>
      match interpBlock δ π fuel heap store stmts with
      | some (outcome, store', h') => some (catchExit label outcome, store', h')
      | none => none

    | .Exit target => some (.exit target, store, heap)

    | .Return (some val) =>
      match interpStmt δ π fuel heap store val.val with
      | some (.normal v, store', h') => some (.ret (some v), store', h')
      | _ => none

    | .Return none => some (.ret none, store, heap)

    -- While Loop
    | .While c invs dec body =>
      match interpStmt δ π fuel heap store c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        match interpStmt δ π fuel h₁ σ₁ body.val with
        | some (.normal _, σ₂, h₂) =>
          interpStmt δ π fuel h₂ σ₂ (.While c invs dec body)
        | some (.exit label, σ₂, h₂) => some (.exit label, σ₂, h₂)
        | some (.ret rv, σ₂, h₂) => some (.ret rv, σ₂, h₂)
        | none => none
      | some (.normal (.vBool false), σ₁, h₁) => some (.normal .vVoid, σ₁, h₁)
      | _ => none

    -- Assignments
    | .Assign [⟨.Identifier name, _⟩] value =>
      match interpStmt δ π fuel heap store value.val with
      | some (.normal v, σ₁, h₁) =>
        match σ₁ name.text with
        | some _ =>
          match updateStore σ₁ name v with
          | some σ₂ => some (.normal v, σ₂, h₁)
          | none => none
        | none => none
      | _ => none

    -- Field Assignment
    | .Assign [⟨.FieldSelect target fieldName, _⟩] value =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match interpStmt δ π fuel h₁ σ₁ value.val with
        | some (.normal v, σ₂, h₂) =>
          match heapFieldWrite' h₂ addr fieldName.text v with
          | some h₃ => some (.normal v, σ₂, h₃)
          | none => none
        | _ => none
      | _ => none

    | .Assign _ _ => none  -- multi-target not supported

    | .LocalVariable name _ty (some init) =>
      match interpStmt δ π fuel heap store init.val with
      | some (.normal v, σ₁, h₁) =>
        match initStore σ₁ name v with
        | some σ₂ => some (.normal .vVoid, σ₂, h₁)
        | none => none
      | _ => none

    | .LocalVariable name _ty none =>
      match initStore store name .vVoid with
      | some store' => some (.normal .vVoid, store', heap)
      | none => none

    -- Verification Constructs
    -- Assert/assume conditions must be pure (no side effects on store or heap).
    -- Runtime compilation may erase these constructs, so their bodies must not
    -- have observable effects. We enforce this by discarding the post-condition
    -- store/heap and returning the originals. A condition with side effects will
    -- appear to have no effect, which is the correct semantics for erasable
    -- constructs. The relational semantics separately requires purity as a
    -- well-formedness condition on programs.
    -- TODO: Enriching Outcome with DiagnosticModel would allow reporting
    -- which assertion failed and where, rather than just returning none.
    -- TODO: To implement `Old`, thread a pre-state snapshot captured at
    -- procedure entry through the interpreter.
    | .Assert c =>
      match interpStmt δ π fuel heap store c.val with
      | some (.normal (.vBool true), _, _) => some (.normal .vVoid, store, heap)
      | _ => none

    | .Assume c =>
      match interpStmt δ π fuel heap store c.val with
      | some (.normal (.vBool true), _, _) => some (.normal .vVoid, store, heap)
      | _ => none

    -- Static Calls
    | .StaticCall callee args =>
      match π callee with
      | some proc =>
        match interpArgs δ π fuel heap store args with
        | some (vals, σ₁, h₁) =>
          match bindParams proc.inputs vals with
          | some σBound =>
            match getBody proc with
            | some body =>
              match interpStmt δ π fuel h₁ σBound body.val with
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
      match allocHeap heap typeName.text with
      | some (addr, h') => some (.normal (.vRef addr), store, h')
      | none => none

    | .FieldSelect target fieldName =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match heapFieldRead h₁ addr fieldName.text with
        | some v => some (.normal v, σ₁, h₁)
        | none => none
      | _ => none

    | .PureFieldUpdate target fieldName newVal =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match interpStmt δ π fuel h₁ σ₁ newVal.val with
        | some (.normal v, σ₂, h₂) =>
          match heapFieldWrite' h₂ addr fieldName.text v with
          | some h₃ => some (.normal (.vRef addr), σ₂, h₃)
          | none => none
        | _ => none
      | _ => none

    | .ReferenceEquals lhs rhs =>
      match interpStmt δ π fuel heap store lhs.val with
      | some (.normal (.vRef a), σ₁, h₁) =>
        match interpStmt δ π fuel h₁ σ₁ rhs.val with
        | some (.normal (.vRef b), σ₂, h₂) =>
          some (.normal (.vBool (a == b)), σ₂, h₂)
        | _ => none
      | _ => none

    | .InstanceCall target callee args =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match h₁ addr with
        | some (typeName, _) =>
          match π (↑(typeName ++ "." ++ callee.text)) with
          | some proc =>
            match interpArgs δ π fuel h₁ σ₁ args with
            | some (vals, σ₂, h₂) =>
              match bindParams proc.inputs ((.vRef addr) :: vals) with
              | some σBound =>
                match getBody proc with
                | some body =>
                  match interpStmt δ π fuel h₂ σBound body.val with
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
      match store "this" with
      | some v => some (.normal v, store, heap)
      | none => none

    -- Type Operations
    | .IsType target ty =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        match h₁ addr with
        | some (actualType, _) =>
          some (.normal (.vBool (actualType == ty.val.typeName)), σ₁, h₁)
        | none => none
      | _ => none

    | .AsType target _ty =>
      match interpStmt δ π fuel heap store target.val with
      | some (.normal v, σ₁, h₁) => some (.normal v, σ₁, h₁)
      | _ => none

    -- Quantifiers (delegated to δ)
    -- TODO: Consider adding a `typeValues : LaurelType → Option (List LaurelValue)`
    -- field to δ that enumerates values for finite types (bool, bounded ints),
    -- enabling concrete evaluation of Forall/Exists over enumerable domains.
    | .Forall name ty body =>
      match δ store (.Forall name ty body) with
      | some v => some (.normal v, store, heap)
      | none => none

    | .Exists name ty body =>
      match δ store (.Exists name ty body) with
      | some v => some (.normal v, store, heap)
      | none => none

    -- Specification Constructs (delegated to δ)
    -- TODO: Implementing Old requires threading a pre-state snapshot
    -- (store + heap) captured at procedure entry through the interpreter.
    | .Old val =>
      match δ store (.Old val) with
      | some v => some (.normal v, store, heap)
      | none => none

    | .Fresh val =>
      match δ store (.Fresh val) with
      | some v => some (.normal v, store, heap)
      | none => none

    | .Assigned name =>
      match δ store (.Assigned name) with
      | some v => some (.normal v, store, heap)
      | none => none

    | .ProveBy value _proof =>
      interpStmt δ π fuel heap store value.val

    | .ContractOf ct func =>
      match δ store (.ContractOf ct func) with
      | some v => some (.normal v, store, heap)
      | none => none

    -- Intentionally omitted
    | .Abstract => none
    | .All => none
    | .Hole _ _ => none

/-- Evaluate a block (list of statements). -/
def interpBlock (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (heap : LaurelHeap) (store : LaurelStore) (stmts : List StmtExprMd)
    : Option (Outcome × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match stmts with
    | [] => some (.normal .vVoid, store, heap)
    | [s] =>
      interpStmt δ π fuel heap store s.val
    | s :: rest =>
      match interpStmt δ π fuel heap store s.val with
      | some (.normal _, σ₁, h₁) => interpBlock δ π fuel h₁ σ₁ rest
      | some (.exit label, σ₁, h₁) => some (.exit label, σ₁, h₁)
      | some (.ret rv, σ₁, h₁) => some (.ret rv, σ₁, h₁)
      | none => none

/-- Evaluate a list of arguments left-to-right, threading heap and store. -/
def interpArgs (δ : LaurelEval) (π : ProcEnv) (fuel : Nat)
    (heap : LaurelHeap) (store : LaurelStore) (args : List StmtExprMd)
    : Option (List LaurelValue × LaurelStore × LaurelHeap) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match args with
    | [] => some ([], store, heap)
    | e :: es =>
      match interpStmt δ π fuel heap store e.val with
      | some (.normal v, σ₁, h₁) =>
        match interpArgs δ π fuel h₁ σ₁ es with
        | some (vs, σ₂, h₂) => some (v :: vs, σ₂, h₂)
        | none => none
      | _ => none
end

/-! ## Program-Level Interpreter -/

/-- Build a `ProcEnv` from a list of procedures. Earlier entries shadow later ones. -/
def listToProcEnv (procs : List Procedure) : ProcEnv :=
  fun name => procs.find? (fun p => p.name == name)

/-- Build a `ProcEnv` from a `Program`, including static procedures and
    instance procedures keyed as `"TypeName.methodName"`. -/
def buildProcEnv (prog : Program) : ProcEnv :=
  let statics := prog.staticProcedures
  let instanceProcs := prog.types.foldl (fun acc td =>
    match td with
    | .Composite ct =>
      ct.instanceProcedures.map (fun p =>
        { p with name := mkId (ct.name.text ++ "." ++ p.name.text) }) ++ acc
    | _ => acc) []
  listToProcEnv (instanceProcs ++ statics)

/-- Build an initial store from static fields, all initialized to `vVoid`. -/
def buildInitialStore (prog : Program) : LaurelStore :=
  let fields := prog.staticFields
  fields.foldl (fun σ f => fun x => if x == f.name.text then some .vVoid else σ x)
    (fun _ => none)

/-- A `LaurelEval` that handles identifiers and literals.
    Specification constructs return `none`. -/
def defaultEval : LaurelEval := fun σ e =>
  match e with
  | .Identifier name => σ name.text
  | .LiteralInt i => some (.vInt i)
  | .LiteralBool b => some (.vBool b)
  | .LiteralString s => some (.vString s)
  | _ => none

/-- The interpreter environment for a Laurel program: procedure environment,
    initial store, and initial heap. -/
structure ProgramEnv where
  /-- Procedure environment mapping names to procedure definitions. -/
  π : ProcEnv
  /-- Initial variable store (from static fields). -/
  σ₀ : LaurelStore
  /-- Initial heap (empty). -/
  h₀ : LaurelHeap

/-- Construct the semantic environment for a Laurel program.
    Builds the `ProcEnv` from static and instance procedures,
    the initial store from static fields, and sets the heap to empty. -/
def buildProgramSemantics (prog : Program) : ProgramEnv :=
  { π := buildProcEnv prog
    σ₀ := buildInitialStore prog
    h₀ := fun _ => none }


/-! ## User-Friendly Result Type -/

inductive InterpResult where
  | success (value : LaurelValue) (store : LaurelStore) (heap : LaurelHeap)
  | returned (value : Option LaurelValue) (store : LaurelStore) (heap : LaurelHeap)
  | noMain
  | noBody
  | stuck (msg : String)
  | fuelExhausted
  deriving Inhabited


instance : ToString InterpResult where
  toString
    | .success v _ _ => s!"success: {v}"
    | .returned (some v) _ _ => s!"returned: {v}"
    | .returned none _ _ => "returned: void"
    | .noMain => "error: no 'main' procedure found"
    | .noBody => "error: 'main' has no body"
    | .stuck msg => s!"stuck: {msg}"
    | .fuelExhausted => "error: fuel exhausted"

/-- Evaluate a `Procedure` with name `procName` from a `Program`.
    Returns `none` if there is no procedure with this name. -/
def interpProcedureByName (procName : String) (prog : Program) (fuel : Nat := 10000)
    : InterpResult :=
  let sem := buildProgramSemantics prog
  match prog.staticProcedures.find? (fun p => p.name.text == procName) with
  | none => .noMain
  | some mainProc =>
    match getBody mainProc with
    | none => .noBody
    | some body =>
      match interpStmt defaultEval sem.π fuel sem.h₀ sem.σ₀ body.val with
      | some (.normal v, st, hp) => .success v st hp
      | some (.ret rv, st, hp) => .returned rv st hp
      | some (.exit label, _, _) => .stuck s!"uncaught exit '{label}'"
      | none => .fuelExhausted

/-! ## Utilities -/

/-- Run a program starting from "main". -/
def interpProgram (prog : Program) (fuel : Nat := 10000) : InterpResult :=
  interpProcedureByName "main" prog fuel

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

/-!
# Direct Operational Semantics for Laurel IR

This file defines a standalone big-step operational semantics for Laurel's
`StmtExpr` AST, independent of Core semantics (Option A from the design
document `docs/designs/design-formal-semantics-for-laurel-ir.md`).

## Design

- **LaurelValue**: runtime values (int, bool, string, void, ref)
- **LaurelStore**: variable store (`Identifier → Option LaurelValue`)
- **LaurelHeap**: object heap (`Nat → Option (Identifier × (Identifier → Option LaurelValue))`)
- **Outcome**: non-local control flow (normal, exit, return)
- **EvalLaurelStmt / EvalLaurelBlock**: mutually inductive big-step relations

The judgment form is: `δ, π, heap, σ, stmt ⊢ heap', σ', outcome`

## Intentionally Omitted Constructs

The following `StmtExpr` constructors have no evaluation rules and will get stuck:
- **`Abstract`**: Specification-level marker for abstract contracts. Not executable.
- **`All`**: Specification-level reference to all heap objects (reads/modifies clauses).
- **`Hole`**: Represents incomplete programs. Not executable by design.

## Known Limitations

- **Multi-target `Assign`**: Only single-target assignment (identifier or field) is
  handled. Multi-target assignment (for procedures with multiple outputs) is not yet
  supported. -- TODO: Add multi-target assign rules.
- **Argument evaluation**: Call arguments are evaluated via the pure evaluator `δ`
  rather than `EvalLaurelStmt`, so arguments with side effects will get stuck.
  This is a workaround for Lean 4 mutual inductive limitations.
-/

namespace Strata.Laurel

/-! ## Values -/

inductive LaurelValue where
  | vInt    : Int → LaurelValue
  | vBool   : Bool → LaurelValue
  | vString : String → LaurelValue
  | vVoid   : LaurelValue
  | vRef    : Nat → LaurelValue
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Store and Heap -/

abbrev LaurelStore := Identifier → Option LaurelValue
abbrev LaurelHeap := Nat → Option (Identifier × (Identifier → Option LaurelValue))
abbrev LaurelEval := LaurelStore → StmtExpr → Option LaurelValue
abbrev ProcEnv := Identifier → Option Procedure

/-! ## Outcomes -/

inductive Outcome where
  | normal : LaurelValue → Outcome
  | exit   : Identifier → Outcome
  | ret    : Option LaurelValue → Outcome
  deriving Repr, BEq, Inhabited

/-! ## Store Operations -/

inductive UpdateStore : LaurelStore → Identifier → LaurelValue → LaurelStore → Prop where
  | update :
    σ x = .some v' →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    UpdateStore σ x v σ'

inductive InitStore : LaurelStore → Identifier → LaurelValue → LaurelStore → Prop where
  | init :
    σ x = none →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    InitStore σ x v σ'

/-! ## Heap Operations -/

/-- Heap allocation using a bump-allocator (smallest-free-address) model.
The `alloc` constructor requires `addr` to be the smallest free address:
all addresses below `addr` must be occupied (`(h a).isSome`).
This invariant makes allocation deterministic but precludes heap deallocation.
If Laurel ever needs a `free` operation, this must be relaxed to a free-list
model, which would invalidate `AllocHeap_deterministic` and downstream proofs. -/
inductive AllocHeap : LaurelHeap → Identifier → Nat → LaurelHeap → Prop where
  | alloc :
    h addr = none →
    (∀ a, a < addr → (h a).isSome) →
    h' addr = .some (typeName, fun _ => none) →
    (∀ a, addr ≠ a → h' a = h a) →
    AllocHeap h typeName addr h'

def heapFieldRead (h : LaurelHeap) (addr : Nat) (field : Identifier) : Option LaurelValue :=
  match h addr with
  | some (_, fields) => fields field
  | none => none

inductive HeapFieldWrite : LaurelHeap → Nat → Identifier → LaurelValue → LaurelHeap → Prop where
  | write :
    h addr = .some (tag, fields) →
    h' addr = .some (tag, fun f => if f == field then some v else fields f) →
    (∀ a, addr ≠ a → h' a = h a) →
    HeapFieldWrite h addr field v h'

/-! ## Helpers -/

def catchExit : Option Identifier → Outcome → Outcome
  | some l, .exit l' => if l == l' then .normal .vVoid else .exit l'
  | _, o => o

def evalPrimOp (op : Operation) (args : List LaurelValue) : Option LaurelValue :=
  match op, args with
  | .And,     [.vBool a, .vBool b] => some (.vBool (a && b))
  | .Or,      [.vBool a, .vBool b] => some (.vBool (a || b))
  | .Not,     [.vBool a]           => some (.vBool (!a))
  | .Implies, [.vBool a, .vBool b] => some (.vBool (!a || b))
  | .Add, [.vInt a, .vInt b] => some (.vInt (a + b))
  | .Sub, [.vInt a, .vInt b] => some (.vInt (a - b))
  | .Mul, [.vInt a, .vInt b] => some (.vInt (a * b))
  | .Neg, [.vInt a]          => some (.vInt (-a))
  | .Div, [.vInt a, .vInt b] => if b != 0 then some (.vInt (a / b)) else none
  | .Mod, [.vInt a, .vInt b] => if b != 0 then some (.vInt (a % b)) else none
  | .Eq,  [.vInt a, .vInt b] => some (.vBool (a == b))
  | .Neq, [.vInt a, .vInt b] => some (.vBool (a != b))
  | .Lt,  [.vInt a, .vInt b] => some (.vBool (a < b))
  | .Leq, [.vInt a, .vInt b] => some (.vBool (a ≤ b))
  | .Gt,  [.vInt a, .vInt b] => some (.vBool (a > b))
  | .Geq, [.vInt a, .vInt b] => some (.vBool (a ≥ b))
  | .Eq,  [.vBool a, .vBool b] => some (.vBool (a == b))
  | .Neq, [.vBool a, .vBool b] => some (.vBool (a != b))
  | .Eq,       [.vString a, .vString b] => some (.vBool (a == b))
  | .Neq,      [.vString a, .vString b] => some (.vBool (a != b))
  | .StrConcat, [.vString a, .vString b] => some (.vString (a ++ b))
  | .Eq,  [.vRef a, .vRef b] => some (.vBool (a == b))
  | .Neq, [.vRef a, .vRef b] => some (.vBool (a != b))
  | _, _ => none

def getBody : Procedure → Option StmtExprMd
  | { body := .Transparent b, .. } => some b
  | { body := .Opaque _ (some b) _, .. } => some b
  | _ => none

/-- Bind parameters to values starting from an empty store (lexical scoping). -/
def bindParams (params : List Parameter) (vals : List LaurelValue)
    : Option LaurelStore :=
  go (fun _ => none) params vals
where
  go (σ : LaurelStore) : List Parameter → List LaurelValue → Option LaurelStore
    | [], [] => some σ
    | p :: ps, v :: vs =>
      if σ p.name = none then
        go (fun x => if x == p.name then some v else σ x) ps vs
      else none
    | _, _ => none

def HighType.typeName : HighType → Identifier
  | .UserDefined name => name
  | _ => ""

/-- Non-mutual argument evaluation using the expression evaluator δ. -/
inductive EvalArgs : LaurelEval → LaurelStore → List StmtExprMd → List LaurelValue → Prop where
  | nil  : EvalArgs δ σ [] []
  | cons : δ σ e.val = some v → EvalArgs δ σ es vs → EvalArgs δ σ (e :: es) (v :: vs)

/-! ## Main Semantic Relations -/

mutual
inductive EvalLaurelStmt :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    StmtExprMd → LaurelHeap → LaurelStore → Outcome → Prop where

  -- Literals

  | literal_int :
    EvalLaurelStmt δ π h σ ⟨.LiteralInt i, md⟩ h σ (.normal (.vInt i))

  | literal_bool :
    EvalLaurelStmt δ π h σ ⟨.LiteralBool b, md⟩ h σ (.normal (.vBool b))

  | literal_string :
    EvalLaurelStmt δ π h σ ⟨.LiteralString s, md⟩ h σ (.normal (.vString s))

  -- Variables

  | identifier :
    σ name = some v →
    EvalLaurelStmt δ π h σ ⟨.Identifier name, md⟩ h σ (.normal v)

  -- Primitive Operations (uses non-mutual EvalArgs)

  | prim_op :
    EvalArgs δ σ args vals →
    evalPrimOp op vals = some result →
    EvalLaurelStmt δ π h σ ⟨.PrimitiveOp op args, md⟩ h σ (.normal result)

  -- Control Flow

  | ite_true :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h₁ σ₁ thenBr h₂ σ₂ outcome →
    EvalLaurelStmt δ π h σ ⟨.IfThenElse c thenBr (some elseBr), md⟩ h₂ σ₂ outcome

  | ite_false :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool false)) →
    EvalLaurelStmt δ π h₁ σ₁ elseBr h₂ σ₂ outcome →
    EvalLaurelStmt δ π h σ ⟨.IfThenElse c thenBr (some elseBr), md⟩ h₂ σ₂ outcome

  | ite_true_no_else :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h₁ σ₁ thenBr h₂ σ₂ outcome →
    EvalLaurelStmt δ π h σ ⟨.IfThenElse c thenBr none, md⟩ h₂ σ₂ outcome

  | ite_false_no_else :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool false)) →
    EvalLaurelStmt δ π h σ ⟨.IfThenElse c thenBr none, md⟩ h₁ σ₁ (.normal .vVoid)

  | block_sem :
    EvalLaurelBlock δ π h σ stmts h' σ' outcome →
    catchExit label outcome = outcome' →
    EvalLaurelStmt δ π h σ ⟨.Block stmts (label.map (λ x => x.text)), md⟩ h' σ' outcome'

  | exit_sem :
    EvalLaurelStmt δ π h σ ⟨.Exit target, md⟩ h σ (.exit target)

  | return_some :
    EvalLaurelStmt δ π h σ val h' σ' (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.Return (some val), md⟩ h' σ' (.ret (some v))

  | return_none :
    EvalLaurelStmt δ π h σ ⟨.Return none, md⟩ h σ (.ret none)

  -- While Loop

  | while_true :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h₁ σ₁ body h₂ σ₂ (.normal _) →
    EvalLaurelStmt δ π h₂ σ₂ ⟨.While c invs dec body, md⟩ h₃ σ₃ outcome →
    EvalLaurelStmt δ π h σ ⟨.While c invs dec body, md⟩ h₃ σ₃ outcome

  | while_false :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool false)) →
    EvalLaurelStmt δ π h σ ⟨.While c invs dec body, md⟩ h₁ σ₁ (.normal .vVoid)

  | while_exit :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h₁ σ₁ body h₂ σ₂ (.exit label) →
    EvalLaurelStmt δ π h σ ⟨.While c invs dec body, md⟩ h₂ σ₂ (.exit label)

  | while_return :
    EvalLaurelStmt δ π h σ c h₁ σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h₁ σ₁ body h₂ σ₂ (.ret rv) →
    EvalLaurelStmt δ π h σ ⟨.While c invs dec body, md⟩ h₂ σ₂ (.ret rv)

  -- Assignments

  | assign_single :
    EvalLaurelStmt δ π h σ value h₁ σ₁ (.normal v) →
    σ₁ name = some _ →
    UpdateStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.Assign [⟨.Identifier name, tmd⟩] value, md⟩ h₁ σ₂ (.normal .vVoid)

  | local_var_init :
    EvalLaurelStmt δ π h σ init h₁ σ₁ (.normal v) →
    σ₁ name = none →
    InitStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.LocalVariable name ty (some init), md⟩ h₁ σ₂ (.normal .vVoid)

  | local_var_uninit :
    σ name = none →
    InitStore σ name .vVoid σ' →
    EvalLaurelStmt δ π h σ ⟨.LocalVariable name ty none, md⟩ h σ' (.normal .vVoid)

  -- Verification Constructs
  -- Note: assert_true and assume_true require the condition to be pure
  -- (no side effects on heap or store). Conditions with side effects have
  -- no derivation. This is intentional — assert/assume conditions should
  -- be specification-level expressions, not effectful computations.

  | assert_true :
    EvalLaurelStmt δ π h σ c h σ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h σ ⟨.Assert c, md⟩ h σ (.normal .vVoid)

  | assume_true :
    EvalLaurelStmt δ π h σ c h σ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h σ ⟨.Assume c, md⟩ h σ (.normal .vVoid)

  -- Static Calls (arguments evaluated via δ for simplicity)
  -- Note: Arguments are evaluated via the pure evaluator δ rather than
  -- EvalLaurelStmt due to Lean 4 mutual inductive limitations. This means
  -- call arguments cannot have side effects (e.g., f(g(x)) where g modifies
  -- the store will get stuck). See commit message for details.

  | static_call :
    π callee = some proc →
    EvalArgs δ σ args vals →
    bindParams proc.inputs vals = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h σBound body h' σ' (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.StaticCall callee args, md⟩ h' σ (.normal v)

  | static_call_return :
    π callee = some proc →
    EvalArgs δ σ args vals →
    bindParams proc.inputs vals = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h σBound body h' σ' (.ret (some v)) →
    EvalLaurelStmt δ π h σ ⟨.StaticCall callee args, md⟩ h' σ (.normal v)

  | static_call_return_void :
    π callee = some proc →
    EvalArgs δ σ args vals →
    bindParams proc.inputs vals = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h σBound body h' σ' (.ret none) →
    EvalLaurelStmt δ π h σ ⟨.StaticCall callee args, md⟩ h' σ (.normal .vVoid)

  -- OO Features

  | new_obj :
    AllocHeap h typeName addr h' →
    EvalLaurelStmt δ π h σ ⟨.New typeName, md⟩ h' σ (.normal (.vRef addr))

  | field_select :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    heapFieldRead h₁ addr fieldName = some v →
    EvalLaurelStmt δ π h σ ⟨.FieldSelect target fieldName, md⟩ h₁ σ₁ (.normal v)

  | pure_field_update :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    EvalLaurelStmt δ π h₁ σ₁ newVal h₂ σ₂ (.normal v) →
    HeapFieldWrite h₂ addr fieldName v h₃ →
    EvalLaurelStmt δ π h σ ⟨.PureFieldUpdate target fieldName newVal, md⟩ h₃ σ₂ (.normal (.vRef addr))

  | reference_equals :
    EvalLaurelStmt δ π h σ lhs h₁ σ₁ (.normal (.vRef a)) →
    EvalLaurelStmt δ π h₁ σ₁ rhs h₂ σ₂ (.normal (.vRef b)) →
    EvalLaurelStmt δ π h σ ⟨.ReferenceEquals lhs rhs, md⟩ h₂ σ₂ (.normal (.vBool (a == b)))

  | instance_call :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    h₁ addr = some (typeName, _) →
    π {text:= (typeName.text ++ "." ++ callee)} = some proc →
    EvalArgs δ σ₁ args vals →
    bindParams proc.inputs ((.vRef addr) :: vals) = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h₁ σBound body h₂ σ₂ (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.InstanceCall target callee args, md⟩ h₂ σ₁ (.normal v)

  | instance_call_return :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    h₁ addr = some (typeName, _) →
    π {text:= (typeName.text ++ "." ++ callee)} = some proc →
    EvalArgs δ σ₁ args vals →
    bindParams proc.inputs ((.vRef addr) :: vals) = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h₁ σBound body h₂ σ₂ (.ret (some v)) →
    EvalLaurelStmt δ π h σ ⟨.InstanceCall target callee args, md⟩ h₂ σ₁ (.normal v)

  | instance_call_return_void :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    h₁ addr = some (typeName, _) →
    π {text:= (typeName.text ++ "." ++ callee)} = some proc →
    EvalArgs δ σ₁ args vals →
    bindParams proc.inputs ((.vRef addr) :: vals) = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h₁ σBound body h₂ σ₂ (.ret none) →
    EvalLaurelStmt δ π h σ ⟨.InstanceCall target callee args, md⟩ h₂ σ₁ (.normal .vVoid)

  | this_sem :
    σ "this" = some v →
    EvalLaurelStmt δ π h σ ⟨.This, md⟩ h σ (.normal v)

  -- Type Operations

  | is_type :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    h₁ addr = some (actualType, _) →
    EvalLaurelStmt δ π h σ ⟨.IsType target ty, md⟩ h₁ σ₁
      (.normal (.vBool (actualType == ty.val.typeName)))

  | as_type :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.AsType target ty, md⟩ h₁ σ₁ (.normal v)

  -- Quantifiers (specification-only, delegated to δ)

  -- Specification Constructs (delegated to δ)

  | old_sem :
    δ σ (.Old val) = some v →
    EvalLaurelStmt δ π h σ ⟨.Old val, md⟩ h σ (.normal v)

  | fresh_sem :
    δ σ (.Fresh val) = some v →
    EvalLaurelStmt δ π h σ ⟨.Fresh val, md⟩ h σ (.normal v)

  | assigned_sem :
    δ σ (.Assigned name) = some v →
    EvalLaurelStmt δ π h σ ⟨.Assigned name, md⟩ h σ (.normal v)

  | prove_by :
    EvalLaurelStmt δ π h σ value h' σ' outcome →
    EvalLaurelStmt δ π h σ ⟨.ProveBy value proof, md⟩ h' σ' outcome

  | contract_of :
    δ σ (.ContractOf ct func) = some v →
    EvalLaurelStmt δ π h σ ⟨.ContractOf ct func, md⟩ h σ (.normal v)

  -- Field Assignment

  | assign_field :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    EvalLaurelStmt δ π h₁ σ₁ value h₂ σ₂ (.normal v) →
    HeapFieldWrite h₂ addr fieldName v h₃ →
    EvalLaurelStmt δ π h σ
      ⟨.Assign [⟨.FieldSelect target fieldName, tmd⟩] value, md⟩ h₃ σ₂ (.normal .vVoid)

inductive EvalLaurelBlock :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → LaurelHeap → LaurelStore → Outcome → Prop where

  | nil :
    EvalLaurelBlock δ π h σ [] h σ (.normal .vVoid)

  | last_normal :
    EvalLaurelStmt δ π h σ s h' σ' (.normal v) →
    EvalLaurelBlock δ π h σ [s] h' σ' (.normal v)

  | cons_normal :
    EvalLaurelStmt δ π h σ s h₁ σ₁ (.normal _v) →
    rest ≠ [] →
    EvalLaurelBlock δ π h₁ σ₁ rest h₂ σ₂ outcome →
    EvalLaurelBlock δ π h σ (s :: rest) h₂ σ₂ outcome

  | cons_exit :
    EvalLaurelStmt δ π h σ s h' σ' (.exit label) →
    EvalLaurelBlock δ π h σ (s :: _rest) h' σ' (.exit label)

  | cons_return :
    EvalLaurelStmt δ π h σ s h' σ' (.ret rv) →
    EvalLaurelBlock δ π h σ (s :: _rest) h' σ' (.ret rv)

end

end Strata.Laurel

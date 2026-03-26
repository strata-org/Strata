/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

/-!
# Laurel Semantic Types and Helpers

Shared type definitions (values, stores, heaps, outcomes) and helper
functions used by the interpreter (`LaurelInterpreter.lean`) and
concrete evaluator (`LaurelConcreteEval.lean`).

## Module Layering

- `LaurelSemantics` — types and pure helpers (this file)
- `LaurelInterpreter` — fuel-based recursive interpreter over `StmtExpr`
- `LaurelConcreteEval` — bridges interpreter to `Laurel.Program` (builds
  `ProcEnv`, initial store, runs `main`)
-/
namespace Strata.Laurel

/-- Structural `DecidableEq` for `Identifier` comparing both `text` and `uniqueId`.
    Note: the `BEq` instance in `Laurel.lean` only compares `.text` (temporary hack).
    Proofs that rely on `BEq` agreeing with `DecidableEq` should use `Identifier.beq_eq`
    or work with `BEq` directly. -/
instance : DecidableEq Identifier := fun a b =>
  match decEq a.text b.text, decEq a.uniqueId b.uniqueId with
  | .isTrue ht, .isTrue hu =>
    .isTrue (by cases a; cases b; simp at ht hu; simp [ht, hu])
  | .isFalse ht, _ =>
    .isFalse (by intro heq; cases heq; exact ht rfl)
  | _, .isFalse hu =>
    .isFalse (by intro heq; cases heq; exact hu rfl)

/-! ## Values -/

inductive LaurelValue where
  | vInt    : Int → LaurelValue
  | vBool   : Bool → LaurelValue
  | vString : String → LaurelValue
  | vVoid   : LaurelValue
  | vRef    : Nat → LaurelValue
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Store and Heap -/

/-- Variable store keyed by `String` (the `.text` of an `Identifier`).
    Using `String` ensures `BEq` and `DecidableEq` agree, which is required
    by the bridging proofs between relational and interpreter semantics. -/
abbrev LaurelStore := String → Option LaurelValue
abbrev LaurelHeap := Nat → Option (String × (String → Option LaurelValue))
abbrev LaurelEval := LaurelStore → StmtExpr → Option LaurelValue
abbrev ProcEnv := Identifier → Option Procedure

/-! ## Outcomes -/

inductive Outcome where
  | normal : LaurelValue → Outcome
  | exit   : String → Outcome
  | ret    : Option LaurelValue → Outcome
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Store Operations -/

inductive UpdateStore : LaurelStore → String → LaurelValue → LaurelStore → Prop where
  | update :
    σ x = .some v' →
    σ' x = .some v →
    (∀ y, x ≠ y → σ' y = σ y) →
    UpdateStore σ x v σ'

inductive InitStore : LaurelStore → String → LaurelValue → LaurelStore → Prop where
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
inductive AllocHeap : LaurelHeap → String → Nat → LaurelHeap → Prop where
  | alloc :
    h addr = none →
    (∀ a, a < addr → (h a).isSome) →
    h' addr = .some (typeName, fun _ => none) →
    (∀ a, addr ≠ a → h' a = h a) →
    AllocHeap h typeName addr h'

def heapFieldRead (h : LaurelHeap) (addr : Nat) (field : String) : Option LaurelValue :=
  match h addr with
  | some (_, fields) => fields field
  | none => none

inductive HeapFieldWrite : LaurelHeap → Nat → String → LaurelValue → LaurelHeap → Prop where
  | write :
    h addr = .some (tag, fields) →
    h' addr = .some (tag, fun f => if f == field then some v else fields f) →
    (∀ a, addr ≠ a → h' a = h a) →
    HeapFieldWrite h addr field v h'

/-! ## Helpers -/

def catchExit : Option String → Outcome → Outcome
  | some l, .exit l' => if l == l' then .normal .vVoid else .exit l'
  | _, o => o

def evalPrimOp (op : Operation) (args : List LaurelValue) : Option LaurelValue :=
  match op, args with
  -- `And`/`Or` are eager boolean operators: both operands are fully evaluated.
  -- `AndThen`/`OrElse`/`Implies` are short-circuit operators handled in `interpStmt`
  -- (they return `none` here because evalPrimOp only handles eager evaluation).
  | .And,     [.vBool a, .vBool b] => some (.vBool (a && b))
  | .Or,      [.vBool a, .vBool b] => some (.vBool (a || b))
  | .Not,     [.vBool a]           => some (.vBool (!a))
  | .Add, [.vInt a, .vInt b] => some (.vInt (a + b))
  | .Sub, [.vInt a, .vInt b] => some (.vInt (a - b))
  | .Mul, [.vInt a, .vInt b] => some (.vInt (a * b))
  | .Neg, [.vInt a]          => some (.vInt (-a))
  | .Div,  [.vInt a, .vInt b] => if b != 0 then some (.vInt (a / b)) else none
  | .Mod,  [.vInt a, .vInt b] => if b != 0 then some (.vInt (a % b)) else none
  | .DivT, [.vInt a, .vInt b] => if b != 0 then some (.vInt (a.tdiv b)) else none
  | .ModT, [.vInt a, .vInt b] => if b != 0 then some (.vInt (a.tmod b)) else none
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
  -- Arity/type mismatches for each operation (no wildcard catch-all):
  | .And, _ => none
  | .Or, _ => none
  | .Not, _ => none
  | .Implies, _ => none
  | .AndThen, _ => none
  | .OrElse, _ => none
  | .Neg, _ => none
  | .Add, _ => none
  | .Sub, _ => none
  | .Mul, _ => none
  | .Div, _ => none
  | .Mod, _ => none
  | .DivT, _ => none
  | .ModT, _ => none
  | .Eq, _ => none
  | .Neq, _ => none
  | .Lt, _ => none
  | .Leq, _ => none
  | .Gt, _ => none
  | .Geq, _ => none
  | .StrConcat, _ => none

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
      if σ p.name.text = none then
        go (fun x => if x == p.name.text then some v else σ x) ps vs
      else none
    | _, _ => none

def HighType.typeName : HighType → String
  | .UserDefined name => name.text
  | _ => ""

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-!
# A Lean Model of SMT-LIB Arrays

This module provides a shallow Lean model of the SMT-LIB `ArraysEx` theory,
defining an `SmtArray α β` as the total function space `α → β` and giving
function-based implementations of `select`, `store`, and constant arrays.

The standard SMT-LIB array axioms
(<https://smt-lib.org/theories-ArraysEx.shtml>) are proved as theorems against
this model:

- `select_const`       — reading any index of a constant array returns the
                         constant value.
- `select_store_self`  — reading the index just written returns the stored
                         value (read-over-write, same index).
- `select_store_of_ne` — reading a different index than the one just written
                         returns the original array's value at that index
                         (read-over-write, distinct indices).
- `ext`                — two arrays that agree pointwise are equal
                         (extensionality).

This model is intended as a semantic reference and a source of rewrite lemmas
for reasoning about SMT array operations inside Lean.
-/

public section

/-- An SMT-LIB array from indices of type `α` to values of type `β`,
modeled as the total function `α → β`. -/
structure SmtArray (α : Type u) (β : Type v) where
  private mk ::
  private toFun : α → β

namespace SmtArray

variable {α : Type u} {β : Type v}

/-- The constant array that maps every index to `v`. -/
def const (v : β) : SmtArray α β :=
  { toFun := fun _ => v }

/-- Read the value stored at index `i` in array `a`. -/
def select (a : SmtArray α β) (i : α) : β :=
  a.toFun i

/-- Return a new array that agrees with `a` everywhere except at index `i`,
where it stores value `v`. -/
def store [DecidableEq α] (a : SmtArray α β) (i : α) (v : β) : SmtArray α β :=
  { toFun := fun j => if j = i then v else a.toFun j }

/-- Selecting any index from a constant array yields the constant value. -/
@[grind =]
theorem select_const (v : β) (i : α) : (const v).select i = v := by
  simp [select, const]

/-- Read-over-write at the same index: reading the index just written returns
the stored value. -/
@[grind =]
theorem select_store_self [DecidableEq α] (a : SmtArray α β) (i : α) (v : β) :
    (a.store i v).select i = v := by
  simp [select, store]

/-- Read-over-write at distinct indices: reading an index other than the one
just written returns the original array's value at that index. -/
@[grind =]
theorem select_store_of_ne [DecidableEq α] (a : SmtArray α β) (i j : α) (v : β)
    (hij : j ≠ i) : (a.store i v).select j = a.select j := by
  simp [select, store, hij]

/-- Extensionality: two arrays that agree on every index are equal. -/
@[ext, grind ext]
theorem ext (a b : SmtArray α β) (h : ∀ i, a.select i = b.select i) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  congr
  funext i
  exact h i

end SmtArray

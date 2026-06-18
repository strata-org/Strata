/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement

/-!
# Core-implicit heap commands

These commands model heap operations with an ambient (implicit) heap.
They extend Core's existing `CmdExt` with heap-specific constructors
whose semantics reference the ambient heap state directly, rather than
through an explicit parameter.

The ambient heap exists in the operational semantics (the machine state
carries it), not in the syntax (no named variable). This is what
distinguishes Core-implicit from Core-explicit and enables the
bisimulation between the two representations.
-/

namespace Core.Implicit

public section

open Core

/--
A heap-specific command operating on the ambient heap.

- `heapRead`: Read a field from an object on the heap into a local variable.
- `heapWrite`: Write a value to a field of an object on the heap.
- `heapAlloc`: Allocate a fresh object of the given type on the heap.
-/
inductive HeapCmd where
  /-- `heapRead lhs := obj.field`
      Read the value at `(obj, field)` in the ambient heap into `lhs`.
      The `ty` records the declared type of `lhs`. -/
  | heapRead (lhs : Expression.Ident) (obj : Expression.Expr)
             (field : Expression.Expr) (ty : Expression.Ty)
  /-- `heapWrite obj.field := rhs`
      Update the ambient heap at `(obj, field)` to `rhs`. -/
  | heapWrite (obj : Expression.Expr) (field : Expression.Expr)
              (rhs : Expression.Expr)
  /-- `heapAlloc lhs := new(typeName)`
      Allocate a fresh object of type `typeName` on the ambient heap.
      The result is a fresh `Composite` reference with the correct TypeTag.
      `typeName` is the class name (e.g., `"BankAccount"`). -/
  | heapAlloc (lhs : Expression.Ident) (typeName : String)
  deriving Repr, Inhabited

/--
Core-implicit's command type: either a standard Core command (including
procedure calls) or a heap-specific command.

This reuses `Core.CmdExt` for all non-heap operations and extends it
with `HeapCmd` for heap-specific operations.
-/
inductive ImplicitCmd where
  /-- A standard Core command (init, set, assert, assume, cover, call). -/
  | core (c : Core.Command)
  /-- A heap-specific command (read, write, alloc). -/
  | heap (c : HeapCmd)
  deriving Inhabited

end

end Core.Implicit

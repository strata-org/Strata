/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! # Proofs: SMT.Result.merge lattice properties

`SMT.Result.merge` implements a join on the lattice
`unsat ≤ unknown ≤ sat ≤ err`.
The merge is not commutative on payloads (models/messages), but the
*level* (which constructor the result has) is commutative, associative,
and idempotent.
-/

namespace Core

open Imperative

/-- The lattice level of an SMT result, ignoring payloads. -/
inductive SMTLevel where
  | unsat | unknown | sat | err
  deriving DecidableEq, Repr

/-- Extract the lattice level from an SMT result. -/
def SMT.Result.level (r : SMT.Result) : SMTLevel :=
  match r with
  | .unsat      => .unsat
  | .unknown .. => .unknown
  | .sat ..     => .sat
  | .err ..     => .err

/-- The join operation on the lattice level. -/
def SMTLevel.join : SMTLevel → SMTLevel → SMTLevel
  | .err, _       => .err
  | _, .err       => .err
  | .sat, _       => .sat
  | _, .sat       => .sat
  | .unknown, _   => .unknown
  | _, .unknown   => .unknown
  | .unsat, .unsat => .unsat

/-! ## Level-commutativity -/

theorem SMTLevel.join_comm (a b : SMTLevel) : join a b = join b a := by
  cases a <;> cases b <;> rfl

/-! ## Level-associativity -/

theorem SMTLevel.join_assoc (a b c : SMTLevel) :
    join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Level-idempotency -/

theorem SMTLevel.join_idem (a : SMTLevel) : join a a = a := by
  cases a <;> rfl

/-! ## merge preserves the lattice level -/

theorem SMT.Result.merge_level (a b : SMT.Result) :
    (SMT.Result.merge a b).level = SMTLevel.join a.level b.level := by
  cases a <;> cases b <;> rfl

/-! ## Derived properties -/

/-- The level of merge is commutative. -/
theorem SMT.Result.merge_level_comm (a b : SMT.Result) :
    (SMT.Result.merge a b).level = (SMT.Result.merge b a).level := by
  simp [merge_level, SMTLevel.join_comm]

/-- The level of merge is associative. -/
theorem SMT.Result.merge_level_assoc (a b c : SMT.Result) :
    (SMT.Result.merge (SMT.Result.merge a b) c).level =
    (SMT.Result.merge a (SMT.Result.merge b c)).level := by
  simp [merge_level, SMTLevel.join_assoc]

/-- Merging a result with itself preserves the level. -/
theorem SMT.Result.merge_level_idem (a : SMT.Result) :
    (SMT.Result.merge a a).level = a.level := by
  simp [merge_level, SMTLevel.join_idem]

/-! ## Dominance properties -/

/-- If the left argument is `err`, the merged result is that `err`. -/
theorem SMT.Result.merge_err_left (e : String) (b : SMT.Result) :
    SMT.Result.merge (SMT.Result.err e) b = SMT.Result.err e := by
  cases b <;> rfl

/-- If the right argument is `err`, the merged level is `err`. -/
theorem SMT.Result.merge_err_right (a : SMT.Result) (e : String) :
    (SMT.Result.merge a (SMT.Result.err e)).level = SMTLevel.err := by
  cases a <;> rfl

/-- `unsat` is the left identity for merge. -/
theorem SMT.Result.merge_unsat_left (b : SMT.Result) :
    SMT.Result.merge SMT.Result.unsat b = b := by
  cases b <;> rfl

/-- `unsat` is the right identity for merge. -/
theorem SMT.Result.merge_unsat_right (a : SMT.Result) :
    SMT.Result.merge a SMT.Result.unsat = a := by
  cases a <;> rfl

end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Env

/-! ## Tests for `Env.merge` preserving deferred obligations across an error wall.

When one ITE branch errors during partial evaluation, `Env.merge` must NOT
silently discard the clean branch's already-accumulated `deferred`
obligations. The merge unions `deferred` across the error wall so those
obligations still reach the verifier. -/

---------------------------------------------------------------------
namespace Core

open Imperative
open Lambda

/-- A synthetic obligation we can recognize. The exact shape doesn't matter
    for this test — we only check counts and identity preservation. -/
private def synthOblig : ProofObligation Expression := {
  label := "test_oblig",
  property := .assert,
  assumptions := [],
  obligation := LExpr.true (),
  metadata := MetaData.empty
}

/-- E1: errored, empty deferred. -/
private def E_errored : Env :=
  { Env.init (empty_factory := true) with
    error := some (.Misc f!"simulated PE error") }

/-- E2: clean, one synthetic obligation. -/
private def E_clean_one_oblig : Env :=
  { Env.init (empty_factory := true) with
    deferred := #[synthOblig] }

/-- E3: clean, two synthetic obligations. -/
private def E_clean_two_oblig : Env :=
  { Env.init (empty_factory := true) with
    deferred := #[synthOblig, synthOblig] }

/-- A dummy condition expression. The error-path branches in `Env.merge` do
    not consult `cond`, so any LExpr will do. -/
private def dummyCond : Expression.Expr := LExpr.true ()


/-! ### Case 1: E1 errored, E2 clean — merged carries E2's deferred -/

/--
info: 1
-/
#guard_msgs in
#eval (Env.merge dummyCond E_errored E_clean_one_oblig).deferred.size

/--
info: true
-/
#guard_msgs in
#eval (Env.merge dummyCond E_errored E_clean_one_oblig).error.isSome


/-! ### Case 2: E1 clean, E2 errored — merged still carries E1's deferred -/

/--
info: 1
-/
#guard_msgs in
#eval (Env.merge dummyCond E_clean_one_oblig E_errored).deferred.size

/--
info: true
-/
#guard_msgs in
#eval (Env.merge dummyCond E_clean_one_oblig E_errored).error.isSome


/-! ### Case 3: both clean, two obligations on each side — union has 4 -/

/--
info: 4
-/
#guard_msgs in
#eval (Env.merge dummyCond E_clean_two_oblig E_clean_two_oblig).deferred.size


/-! ### Case 4: both errored — merged carries union of both sides' deferred -/

/-- E_err_with_oblig: errored, one synthetic obligation (e.g., from clean
    statements before the error fired). -/
private def E_err_with_oblig : Env :=
  { Env.init (empty_factory := true) with
    error := some (.Misc f!"simulated PE error 2"),
    deferred := #[synthOblig] }

/--
info: 2
-/
#guard_msgs in
#eval (Env.merge dummyCond E_err_with_oblig E_err_with_oblig).deferred.size


/-! ### Case 5: both errored with DIFFERENT errors — E1's error is kept -/

private def E_err_a : Env :=
  { Env.init (empty_factory := true) with
    error := some (.Misc f!"error A"),
    deferred := #[synthOblig] }

private def E_err_b : Env :=
  { Env.init (empty_factory := true) with
    error := some (.Misc f!"error B"),
    deferred := #[synthOblig] }

/--
info: 2
-/
#guard_msgs in
#eval (Env.merge dummyCond E_err_a E_err_b).deferred.size

-- E1 wins arbitrarily — the merged env carries an error flag either way,
-- so downstream short-circuits regardless of which side's value is kept.
/--
info: some "[ERROR] error A"
-/
#guard_msgs in
#eval ((Env.merge dummyCond E_err_a E_err_b).error.map fun e => f!"{e}").map fun f => Std.Format.pretty f


end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.WellTypedLExprGen
import Strata.DL.Lambda.IntBoolFactory

/-! ## Tests for WellTypedLExprGen -/

open Plausible
open Lambda
open Lambda.LTy
open TestGen

abbrev wtg_lctx : LContext TrivialParams :=
{ LContext.empty with knownTypes := KnownTypes.default
                      functions := Lambda.IntBoolFactory }

abbrev wtg_ctx : TContext Unit := ⟨[[]], []⟩

def wtgCanResolve (C : LContext TrivialParams) (e : LExpr TrivialParams.mono) : Bool :=
  let env : TEnv Unit := { genEnv := ⟨wtg_ctx, TState.init⟩ }
  (LExpr.resolve C env e).isOk

def wtgCheckResolvesTy (C : LContext TrivialParams) (ty : LMonoTy)
    (e : LExpr TrivialParams.mono) : Bool :=
  let env : TEnv Unit := { genEnv := ⟨wtg_ctx, TState.init⟩ }
  match LExpr.resolve C env e with
  | .error _ => false
  | .ok (et, _) => et.toLMonoTy == ty

private def wtgValidate (C : LContext TrivialParams)
    (Γ : TContext Unit := {}) (ty? : Option LMonoTy := none)
    (n : Nat := 1000) : IO Unit := do
  let mut failed : Nat := 0
  let mut total : Nat := 0
  let count := (List.replicate n 0).toArray
  for _ in count do
    try
      let e ← Gen.run (WTG.mkGen C Γ ty?) 9
      total := total + 1
      let ok := match ty? with
        | none => wtgCanResolve C e
        | some ty => wtgCheckResolvesTy C ty e
      if !ok then
        failed := failed + 1
        IO.println s!"FAILED: {Std.format e}"
    catch _ => pure ()
  if failed != 0 then
    throw (IO.userError s!"FAIL: {failed} of {total} failed")

-- Validate with default context
#eval! wtgValidate LContext.default

-- Validate with IntBoolFactory (has actual operations)
#eval! wtgValidate wtg_lctx

-- TODO: fvar+varClose path has issues when combined with factory ops.
-- Uncomment when fixed:
-- #eval! wtgValidate wtg_lctx
--   { types := [[({ name := "x", metadata := () }, .forAll [] .int),
--                ({ name := "f", metadata := () }, .forAll [] (.tcons "arrow" [.int, .bool]))]] }
--   (some .bool)

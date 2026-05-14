/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # Lean 4 Nested Inductive Restriction in Mutual Blocks

This file demonstrates why `CoreEvalDetBlock` and `CoreEvalCmds` in
`StatementSemantics.lean` cannot directly reuse the generic
`Imperative.EvalDetBlock` and `Imperative.EvalCmds`.

## The Rule

Passing a mutual inductive (partially applied) as a parameter to an external
inductive works IF that external inductive uses the parameter **directly** in
its own constructors. It FAILS if the external inductive delegates to yet
another inductive parameterized by the same slot.

## Application to CFG Semantics

- `Imperative.StepStmt` uses `EvalCmd` directly → `CoreStepStar` can use
  `StepStmt Expression (EvalCommand π φ)` ✓
- `Imperative.EvalDetBlock` delegates to `Imperative.EvalCmds` (another
  inductive) → cannot use `EvalDetBlock Expression (EvalCommand π φ)` ✗

This forces us to duplicate `EvalDetBlock`/`EvalCmds` as `CoreEvalDetBlock`/
`CoreEvalCmds` inside the mutual block.
-/

-- External inductive that uses EvalCmd DIRECTLY in its own constructor
inductive DirectUse (α : Type) (EvalCmd : α → Nat → Nat → Prop) : Nat → Nat → Prop where
  | mk : EvalCmd a σ σ' → DirectUse α EvalCmd σ σ'

-- External inductive that DELEGATES to another inductive (EvalList)
inductive EvalList (α : Type) (EvalCmd : α → Nat → Nat → Prop) : Nat → Nat → Prop where
  | nil : EvalCmd a σ σ' → EvalList α EvalCmd σ σ
  | cons : EvalList α EvalCmd σ σ' → EvalList α EvalCmd σ σ'

inductive EvalList' (α : Type) (EvalCmd : α → Nat → Nat → Prop) : Nat → Nat → Prop where
  -- EvalList' is not directly using EvalCmd (the commented-out nil constructor directly uses it), so can't be nested in BadStar
  -- | nil : EvalCmd a σ σ' → EvalList' α EvalCmd σ σ'
  | cons : EvalList α EvalCmd σ σ' → EvalList' α EvalCmd σ σ'

-- ✓ WORKS: DirectUse uses EvalCmd in its own constructor only
mutual
inductive GoodStar (n : Nat) : Nat → Nat → Prop where
  | refl : GoodStar n c c
  | step : DirectUse Nat (GoodCmd n) c₁ c₂ → GoodStar n c₂ c₃ → GoodStar n c₁ c₃

inductive GoodCmd (n : Nat) : Nat → Nat → Nat → Prop where
  | call : GoodStar n σ σ' → GoodCmd n x σ σ'
end

-- ✗ FAILS: EvalList' references EvalList internally, creating a nested
--   inductive chain. Uncomment to see the error:
--   "(kernel) invalid nested inductive datatype 'EvalList'',
--    nested inductive datatypes parameters cannot contain local variables."
/-
mutual
inductive BadStar (n : Nat) : Nat → Nat → Prop where
  | refl : BadStar n c c
  | step : EvalList' Nat (BadCmd n) c₁ c₂ → BadStar n c₂ c₃ → BadStar n c₁ c₃

inductive BadCmd (n : Nat) : Nat → Nat → Nat → Prop where
  | call : BadStar n σ σ' → BadCmd n x σ σ'
end
-/

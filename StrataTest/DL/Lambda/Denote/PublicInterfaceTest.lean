/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprDenote

/-!
## The public interface of `LExprDenote`

A module that builds on the denotation, for example an interpreter that
evaluates expressions with `LExpr.denote`, needs these declarations without
`import all`: decidable equality on `LSort` must compute, and the recursion
principles `LSort.rec'` and `LSort.ind` and the `denote` unfolding lemmas must
be nameable. This file uses a plain import only, so it fails to build if any of
them stops being public.
-/

namespace Lambda

-- `DecidableEq LSort` computes in the kernel.
example : LSort.tcons "int" [] ≠ LSort.bitvec 32 := by decide
example : (LSort.tcons "arrow" [.int, .bitvec 32] : LSort) = .tcons "arrow" [.int, .bitvec 32] := by
  decide

-- The recursion principles and the unfolding lemmas can be named.
example := @LSort.rec'
example := @LSort.ind
example := @denote_fvar
example := @denote_bvar
example := @denote_abs
example := @denote_eq_false
example := @denote_quant_all_false
example := @denote_quant_exist_true
example := @denote_quant_exist_false

end Lambda

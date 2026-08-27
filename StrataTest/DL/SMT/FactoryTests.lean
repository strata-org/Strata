/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all Strata.DL.SMT.Factory

/-! ## Unit tests for `Strata.SMT.Factory` smart constructors

These pin the *structural* behavior of the smart constructors — complementing the semantic-preservation
theorems in `FactoryCorrect.lean`, which prove denotation equivalence but do not characterize which
rewrite branch fires.
-/

meta section
namespace Strata.SMT.Factory

/-! ### `Factory.quant` — nested-quantifier coalescing -/

private def xVar : TermVar := ⟨"x", .int⟩
private def yVar : TermVar := ⟨"y", .int⟩
private def body : Term := .app .eq [.var xVar, .var yVar] .bool

-- Coalescing fires: same kind, outer trigger empty. Inner trigger `[[.var yVar]]` survives
-- as the coalesced binder's trigger.
#guard
  Factory.quant .all "x" .int [] (.quant .all [yVar] [[.var yVar]] body)
    == .quant .all [xVar, yVar] [[.var yVar]] body

-- Coalescing fires with an empty inner trigger too (both empty → merged binder has no trigger).
#guard
  Factory.quant .all "x" .int [] (.quant .all [yVar] [] body)
    == .quant .all [xVar, yVar] [] body

-- Coalescing suppressed: outer trigger is non-empty. Outer binder wraps the inner untouched;
-- the outer's trigger is preserved.
#guard
  Factory.quant .all "x" .int [[.var xVar]] (.quant .all [yVar] [] body)
    == .quant .all [xVar] [[.var xVar]] (.quant .all [yVar] [] body)

-- Coalescing suppressed: mismatched quantifier kinds. The naive single-binder wrapper is used.
#guard
  Factory.quant .all "x" .int [] (.quant .exist [yVar] [] body)
    == .quant .all [xVar] [] (.quant .exist [yVar] [] body)

-- Non-quantifier body: naive single-binder wrapper (coalescing only inspects `.quant` bodies).
#guard
  Factory.quant .all "x" .int [] body
    == .quant .all [xVar] [] body

end Strata.SMT.Factory
end

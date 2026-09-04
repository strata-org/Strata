/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.CollectSound
import all Strata.Languages.Core.VerifiedSMTGen.CollectSound
public import Strata.Languages.Core.VerifiedSMTGen.TranslateSound
import all Strata.Languages.Core.VerifiedSMTGen.TranslateSound

/-!
# Refactored SMT encoder — end-to-end soundness (ProofObligation ⟶ SMTQuery)

The headline theorem `obligation_valid_of_unsatWithNegObl`, composing the two phase-soundness results:
collect (`collect_WF` / `collect_valid`, from `CollectSound`) with translate (`translateQuery_WF`
/ `query_valid_of_unsatWithNegObl`, from `TranslateSound`). Stated against the runtime entry point
`encodeObligationRun`.

Its dual `obligation_unsat_of_unsatWithObl` (`UnsatWithObl ⟹ ProofObligation.Unsat`) composes the
`collect_unsat` / `query_unsat_of_unsatWithObl` duals the same way — the goal is asserted positively
rather than negated, so a solver `unsat` means the obligation can never hold.
-/

open Core Lambda Imperative Strata.SMT Std
open Strata.SMT.DenoteTyped

namespace Core.Refactor

/-- **End-to-end.** If `encodeObligationRun` emits a query for a well-formed obligation and that query is
    `UnsatWithNegObl` (its SMT-LIB rendering refutes the negated goal), the obligation is denotationally
    valid. -/
theorem obligation_valid_of_unsatWithNegObl
    -- ── source side ──
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    -- ── target side ──
    {q : SMTQuery}
    -- ── correspondence ──
    {uAT : Bool}
    (henc : encodeObligationRun uAT F tf karities d = .ok q)
    (hprove : SMTQuery.UnsatWithNegObl q
      (translateQuery_WF (collect_WF hpwf hsimp).1 (collect_WF hpwf hsimp).2 henc)) :
    ProofObligation.Valid F d hpwf hsimp :=
  collect_valid hpwf hsimp
    (query_valid_of_unsatWithNegObl (collect_WF hpwf hsimp).1 henc
      (collect_WF hpwf hsimp).2 hprove)

/-- **End-to-end, dual.** If `encodeObligationRun` emits a query for a well-formed obligation and that
    query is `UnsatWithObl` (its SMT-LIB rendering refutes the goal asserted positively), the obligation
    is denotationally unsatisfiable — the path conditions entail `¬goal`. -/
theorem obligation_unsat_of_unsatWithObl
    -- ── source side ──
    {F : Lambda.Factory CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {karities : KnownTypeArities} {d : Imperative.ProofObligation Expression}
    (hpwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf)
    -- ── target side ──
    {q : SMTQuery}
    -- ── correspondence ──
    {uAT : Bool}
    (henc : encodeObligationRun uAT F tf karities d = .ok q)
    (hrefute : SMTQuery.UnsatWithObl q
      (translateQuery_WF (collect_WF hpwf hsimp).1 (collect_WF hpwf hsimp).2 henc)) :
    ProofObligation.Unsat F d hpwf hsimp :=
  collect_unsat hpwf hsimp
    (query_unsat_of_unsatWithObl (collect_WF hpwf hsimp).1 henc
      (collect_WF hpwf hsimp).2 hrefute)

end Core.Refactor

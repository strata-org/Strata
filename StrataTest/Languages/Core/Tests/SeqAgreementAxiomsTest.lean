/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.Factory

/-! # The agreement axiom of `Sequence.select` and `Sequence.select!`

`Sequence.select` carries one axiom: `Sequence.select!` equals it wherever its
precondition holds. The axiom is written out in the factory, so these checks state
that its guard is the declared precondition: changing a bound on one side without the
other fails here. -/

namespace Strata.SeqAgreementAxiomsTest

open Lambda Core

/-- Strip the leading universal binders of `ax`, opening each as the free variable
of the given name and type, outermost binder first. -/
private def openBinders :
    List (String × LMonoTy) → LExpr CoreLParams.mono → Option (LExpr CoreLParams.mono)
  | [], e => some e
  | (x, ty) :: rest, .quant _ .all _ _ _ body =>
    (openBinders rest body).map (·.varOpen rest.length (⟨x, ()⟩, some ty))
  | _, _ => none

/-- The guard of the agreement axiom `∀ args. {trigger} if guard then … else true`,
the last axiom of `checked`, with its binders named as the inputs of `checked`. -/
private def agreementGuard (checked : WFLFunc CoreLParams) :
    List (LExpr CoreLParams.mono) :=
  match openBinders (checked.func.inputs.map (fun (n, t) => (n.name, t)))
      checked.func.axioms.getLast! with
  | some (.ite _ g _ _) => [g]
  | _ => []

/-- The preconditions `checked` declares. -/
private def preconds (checked : WFLFunc CoreLParams) : List (LExpr CoreLParams.mono) :=
  checked.func.preconditions.map (·.expr)

#guard agreementGuard seqSelectFunc =ₘ preconds seqSelectFunc

-- The check tells bounds apart: `select`'s `i < length(s)` is not `take`'s `n <= length(s)`.
#guard !(agreementGuard seqSelectFunc =ₘ preconds seqTakeFunc)

-- `Sequence.select` has exactly the agreement axiom, and `Sequence.select!` none, so a
-- query that uses `select` receives one extra axiom and pulls in nothing else.
#guard seqSelectFunc.func.axioms.length == 1
#guard seqSelectUnsafeFunc.func.axioms.isEmpty

end Strata.SeqAgreementAxiomsTest

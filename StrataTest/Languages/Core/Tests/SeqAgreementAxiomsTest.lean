/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.Factory

/-! # The agreement axioms of the checked sequence operations

Each checked sequence operation (`Sequence.select`, `update`, `take`, `drop`) carries,
as its last axiom, `∀ args. twin(args) == checked(args)` for its total twin, at every
argument: no guard, so the two agree out of range too. The axioms are written out in
the factory, so these checks state their shape: a guard added back, or a twin or an
argument swapped, fails here. -/

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

/-- The operator and the free-variable arguments of a call, if `e` is one. -/
private def callOf (e : LExpr CoreLParams.mono) : Option (String × List String) :=
  match getLFuncCall e with
  | (.op _ o _, args) =>
    (args.mapM fun (a : LExpr CoreLParams.mono) => match a with
      | .fvar _ x _ => some x.name
      | _ => none).map (o.name, ·)
  | _ => none

/-- The two sides of the last axiom of `checked`, `∀ args. lhs == rhs`, each as the
operator it calls and the names of its arguments, with the binders named as the inputs
of `checked`. -/
private def agreementSides (checked : WFLFunc CoreLParams) :
    Option ((String × List String) × (String × List String)) :=
  match openBinders (checked.func.inputs.map (fun (n, t) => (n.name, t)))
      checked.func.axioms.getLast! with
  | some (.eq _ l r) => do pure (← callOf l, ← callOf r)
  | _ => none

/-- The agreement `twin(args) == checked(args)`, over the inputs of `checked`. -/
private def expected (checked twin : WFLFunc CoreLParams) :
    Option ((String × List String) × (String × List String)) :=
  let args := checked.func.inputs.map (·.1.name)
  some ((twin.name.name, args), (checked.name.name, args))

#guard agreementSides seqSelectFunc == expected seqSelectFunc seqSelectUnsafeFunc
#guard agreementSides seqUpdateFunc == expected seqUpdateFunc seqUpdateUnsafeFunc
#guard agreementSides seqTakeFunc == expected seqTakeFunc seqTakeUnsafeFunc
#guard agreementSides seqDropFunc == expected seqDropFunc seqDropUnsafeFunc

-- The check tells the operations apart: `take`'s agreement is not `drop`'s.
#guard agreementSides seqTakeFunc != expected seqDropFunc seqDropUnsafeFunc

-- `Sequence.select` has exactly the agreement axiom, and `Sequence.select!` none, so a
-- query that uses `select` receives one extra axiom and pulls in nothing else.
#guard seqSelectFunc.func.axioms.length == 1
#guard seqSelectUnsafeFunc.func.axioms.isEmpty

-- Each other twin states the axioms of its checked form but the agreement.
#guard seqUpdateUnsafeFunc.func.axioms.length + 1 == seqUpdateFunc.func.axioms.length
#guard seqTakeUnsafeFunc.func.axioms.length + 1 == seqTakeFunc.func.axioms.length
#guard seqDropUnsafeFunc.func.axioms.length + 1 == seqDropFunc.func.axioms.length

end Strata.SeqAgreementAxiomsTest

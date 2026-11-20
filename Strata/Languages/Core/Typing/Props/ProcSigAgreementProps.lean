/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.ProcSigAgreement

/-! ## Properties of procedure-signature agreement

Agreement on a list of procedure names also holds on any sublist:
`ProcedureCallsRel.subset`, and its instances
`ProcedureCallsRel.append_left` and `ProcedureCallsRel.append_right`, which
`ProcedureCallAgreement.append_left` and `ProcedureCallAgreement.append_right`
state for signature agreement.
-/

namespace Core

open Lambda

public section

/-- If every procedure of `P1` named in `ns'` has a procedure of its name in
    `P2` related to it by `R`, the same holds for the names in any subset `ns`
    of `ns'`. -/
theorem ProcedureCallsRel.subset {R : Procedure → Procedure → Prop}
    {P1 P2 : Program} {ns ns' : List String} (hsub : ns ⊆ ns')
    (h : ProcedureCallsRel R P1 P2 ns') : ProcedureCallsRel R P1 P2 ns :=
  fun x hx q1 hq1 => h x (hsub hx) q1 hq1

/-- A relation between the procedures of two programs for the names in `ns ++ ms` holds for
    those named in `ns`. -/
theorem ProcedureCallsRel.append_left {R : Procedure → Procedure → Prop}
    {P1 P2 : Program} {ns ms : List String}
    (h : ProcedureCallsRel R P1 P2 (ns ++ ms)) : ProcedureCallsRel R P1 P2 ns :=
  ProcedureCallsRel.subset (List.subset_append_left ns ms) h

/-- A relation between the procedures of two programs for the names in `ns ++ ms` holds for
    those named in `ms`. -/
theorem ProcedureCallsRel.append_right {R : Procedure → Procedure → Prop}
    {P1 P2 : Program} {ns ms : List String}
    (h : ProcedureCallsRel R P1 P2 (ns ++ ms)) : ProcedureCallsRel R P1 P2 ms :=
  ProcedureCallsRel.subset (List.subset_append_right ns ms) h

/-- Signature agreement for the procedures named in `ns ++ ms` implies
    agreement for those named in `ns`. -/
theorem ProcedureCallAgreement.append_left {A : List TypeAlias}
    {P1 P2 : Program} {ns ms : List String}
    (h : ProcedureCallAgreement A P1 P2 (ns ++ ms)) :
    ProcedureCallAgreement A P1 P2 ns :=
  ProcedureCallsRel.append_left h

/-- Signature agreement for the procedures named in `ns ++ ms` implies
    agreement for those named in `ms`. -/
theorem ProcedureCallAgreement.append_right {A : List TypeAlias}
    {P1 P2 : Program} {ns ms : List String}
    (h : ProcedureCallAgreement A P1 P2 (ns ++ ms)) :
    ProcedureCallAgreement A P1 P2 ms :=
  ProcedureCallsRel.append_right h

end -- public section

end Core

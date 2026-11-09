/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program

/-! ## Agreement of procedure signatures between two programs

`ProcSigAgree`: two procedures have the same parameter names and
alias-equivalent parameter types. `ProcedureCallsRel` and
`ProcedureCallAgreement`: every named procedure of one program has a related
procedure of the same name in another. -/

namespace Core

open Lambda

public section

/-- Two procedures have agreeing signatures up to type aliases `A`: identical
    parameter names, and pointwise alias-equivalent parameter types. -/
structure ProcSigAgree (A : List TypeAlias) (q1 q2 : Procedure) : Prop where
  inputsKeys : q1.header.inputs.keys = q2.header.inputs.keys
  outputsKeys : q1.header.outputs.keys = q2.header.outputs.keys
  inputsVals :
    AliasEquivList A q1.header.inputs.values q2.header.inputs.values
  outputsVals :
    AliasEquivList A q1.header.outputs.values q2.header.outputs.values

/-- Every procedure of `P1` named in `names` has a procedure of its name in
    `P2` related to it by `R`. -/
abbrev ProcedureCallsRel (R : Procedure → Procedure → Prop) (P1 P2 : Program)
    (names : List String) : Prop :=
  ∀ x ∈ names, ∀ q1, Program.Procedure.find? P1 x = some q1 →
    ∃ q2, Program.Procedure.find? P2 x = some q2 ∧ R q1 q2

/-- Every named procedure of `P1` has a procedure of its name in `P2` with an
    alias-equivalent signature. -/
abbrev ProcedureCallAgreement (A : List TypeAlias) (P1 P2 : Program)
    (names : List String) : Prop :=
  ProcedureCallsRel (ProcSigAgree A) P1 P2 names

end -- public section

end Core

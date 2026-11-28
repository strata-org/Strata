/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement

/-! # The verification unit of a procedure

A procedure's *unit* is the statement list a counterexample of one of its obligations is
judged on: its contract-wrapped body (`procPassive`).  The same list is what symbolic
evaluation and the WP pass translate.  `Program.ContractFree` describes the programs whose
procedures all have an empty contract, as obligation programs do. -/

namespace Core
namespace WPObl

public section

/-- The passive statement list of a procedure as symbolic evaluation sees it
    (`Procedure.eval`): precondition assumes, the body, postcondition asserts (a free
    postcondition becomes `assume true`, keeping its expression in the metadata). -/
@[expose] def procPassive (p : Procedure) (body : Statements) : Statements :=
  let pre := p.spec.preconditions.map fun (label, check) =>
    Statement.assume label check.expr check.md
  let post := p.spec.postconditions.map fun (label, check) =>
    match check.attr with
    | .Free =>
      Statement.assume label Imperative.HasBool.tt
        ((Imperative.MetaData.pushElem (Imperative.MetaData.pushElem #[] (.label label)
          (.expr check.expr)) (.label label) (.msg "FreePostCondition")))
    | _ => Statement.assert label check.expr check.md
  pre ++ body ++ post

/-- `procPassive`, returning the body itself for a procedure without a contract, so that the
    unit of such a procedure shares the body's cells. -/
def procPassiveShared (p : Procedure) (body : Statements) : Statements :=
  match p.spec.preconditions, p.spec.postconditions with
  | [], [] => body
  | _, _ => procPassive p body

/-- `procPassive` is `procPassiveShared`, which the compiler runs in its place. -/
@[csimp] theorem procPassive_eq_shared : @procPassive = @procPassiveShared := by
  funext p body
  simp only [procPassiveShared]
  split
  · rename_i h1 h2
    simp [procPassive, h1, h2]
  · rfl

/-- Every procedure of the program has an empty contract (as every procedure of an
    obligation program does: its contract checks are explicit statements of its body). -/
@[expose] def _root_.Core.Program.ContractFree (p : Program) : Prop :=
  ∀ q md, Decl.proc q md ∈ p.decls → q.spec.preconditions = [] ∧ q.spec.postconditions = []

end -- public section

end WPObl
end Core

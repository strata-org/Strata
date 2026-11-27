/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureUnit
import all Strata.Util.ListMap

/-! # Properties of the verification unit of a procedure

Key theorems: `procPassive_emptySpec` — a procedure with no preconditions and no
postconditions has its body as its unit; `procPassive_eq_contractWrapped` — the unit is
`Procedure.contractWrapped`; `Program.contractFree_iff` — `Program.ContractFree` is
`Program.noProcedureContracts`.  Key definition: `WPObl.procPassive`, a
procedure's unit (precondition assumes, the body, postcondition asserts). -/

namespace Core
namespace WPObl

public section

/-- A procedure with no preconditions and no postconditions has its body as its unit:
    `procPassive` adds no statement around the body. -/
theorem procPassive_emptySpec (p : Procedure) (body : Statements)
    (hpre : p.spec.preconditions = []) (hpost : p.spec.postconditions = []) :
    procPassive p body = body := by simp [procPassive, hpre, hpost]

/-- A procedure's unit is its contract-wrapped body as `Procedure.eval` builds it
    (`Procedure.contractWrapped`). -/
theorem procPassive_eq_contractWrapped (p : Procedure) (body : Statements) :
    procPassive p body = p.contractWrapped body := by
  simp only [procPassive, Imperative.Procedure.contractWrapped, Imperative.Check.assumes,
    Imperative.Check.asserts, List.map_map]
  congr 2
  funext ⟨l, c⟩
  simp only [Function.comp_apply]
  cases c.attr <;> rfl

/-- A program is contract-free (`Program.ContractFree`) exactly when the executable check
    `Program.noProcedureContracts` accepts it. -/
theorem _root_.Core.Program.contractFree_iff (p : Program) :
    p.ContractFree ↔ p.noProcedureContracts = true := by
  have he {α β : Type} : ∀ m : ListMap α β, m.isEmpty = true ↔ m = []
    | [] => ⟨fun _ => rfl, fun _ => rfl⟩
    | _ :: _ => ⟨nofun, nofun⟩
  simp only [Program.ContractFree, Program.noProcedureContracts, List.all_eq_true]
  refine ⟨fun h d hd => ?_, fun h q md hq => by simpa [he] using h _ hq⟩
  cases d <;> simp only [Bool.and_eq_true, he] <;> first | rfl | exact h _ _ hd

end -- public section

end WPObl
end Core

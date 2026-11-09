/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import all Strata.Languages.Core.Program

/-! # Properties of Core programs

Facts about declaration-order views of a `Program` and the expression factories
constructed from them.

Key results:
- `Program.factoryBeforeProcedure_eq_core_of_noFunctions` — when no user
  functions precede a procedure, its visible factory is `Core.Factory`.
-/

public section

namespace Core

/-- If no user functions precede `procName`, its visible factory is exactly
    `Core.Factory`. -/
theorem Program.factoryBeforeProcedure_eq_core_of_noFunctions
    {p : Program} {procName : String}
    (h : (p.declsBeforeProcedure procName).all fun d =>
      match d with
      | .func _ _ | .recFuncBlock _ _ => false
      | _ => true) :
    p.factoryBeforeProcedure procName = Core.Factory := by
  simp only [List.all_eq_true] at h
  unfold Program.factoryBeforeProcedure
  have go : ∀ decls : List Decl,
      (∀ d ∈ decls,
        (match d with
         | .func _ _ | .recFuncBlock _ _ => false
         | _ => true) = true) →
      decls.foldl Decl.addFunctionsToFactory Core.Factory = Core.Factory := by
    intro decls hdecls
    induction decls with
    | nil => rfl
    | cons d ds ih =>
        rw [List.foldl_cons]
        have hd := hdecls d (List.mem_cons_self)
        have hds : ∀ d ∈ ds,
            (match d with
             | .func _ _ | .recFuncBlock _ _ => false
             | _ => true) = true :=
          fun d hdmem => hdecls d (List.mem_cons_of_mem _ hdmem)
        cases d <;> simp at hd
        all_goals simpa [Decl.addFunctionsToFactory] using ih hds
  exact go (p.declsBeforeProcedure procName) h

end Core

end -- public section

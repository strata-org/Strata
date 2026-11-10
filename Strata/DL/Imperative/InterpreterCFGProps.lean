/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterCFG

/-! # Properties of the monadic CFG interpreter's definitions

* `CFG.allCmds_of_mem`: a CFG each of whose listed blocks has only commands passing a check `q`
  satisfies `CFG.allCmds q`. -/

namespace Imperative

public section

/-- A CFG each of whose listed blocks has only commands passing `q` satisfies `CFG.allCmds q`. -/
theorem CFG.allCmds_of_mem {l CmdT : Type} {P : PureExpr} [BEq l] [LawfulBEq l]
    {q : CmdT → Bool} {g : CFG l (DetBlock l CmdT P)}
    (h : ∀ lb ∈ g.blocks, lb.2.cmds.all q = true) : g.allCmds q := fun _ _ hb => by
  obtain ⟨_, _, he, -⟩ := List.lookup_eq_some_iff.1 hb
  exact h _ (he ▸ List.mem_append_right _ List.mem_cons_self)

end

end Imperative

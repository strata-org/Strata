/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.FoldAxiomsCorrect
public import Strata.Transform.CoreSpecification
public import Strata.Languages.Core.ProgramProps

/-! # The axiom premises from a procedure's entry environment

The phase theorems of axiom folding and equality simplification take as premise that the
axioms declared before a procedure `q` evaluate to `true` in a store (`AxiomsHold`). The
entry semantics states the same of `q`'s initial environment, over the declarations
`declsBeforeProcedure` gives (`Core.Specification.AxiomsBeforeProcedureDecl`). This file
connects the two, so that a client starting from the entry environment can discharge the
premise.

Key theorems: `axiomsHold_of_axiomsBeforeProcedureDecl`, `axiomsHold_of_entry`. -/

namespace Core
namespace FoldAxioms

public section

/-- **The entry environment satisfies the axioms before the procedure.** Where `ρ₀`
    satisfies the axioms and distincts declared before `n`, every axiom of
    `p.declsBeforeProcedure n` without bound variables evaluates to `true` in its store. -/
theorem axiomsHold_of_axiomsBeforeProcedureDecl {p : Program} {n : String}
    {ρ₀ : Imperative.Env Expression}
    (h : Core.Specification.AxiomsBeforeProcedureDecl n p ρ₀) :
    AxiomsHold ρ₀.factory (p.declsBeforeProcedure n) ρ₀.store := by
  unfold Core.Specification.AxiomsBeforeProcedureDecl at h
  generalize p.declsBeforeProcedure n = ds at h ⊢
  intro a md ha _
  induction ds with
  | nil => cases ha
  | cons d ds ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · exact h.1
    · cases d <;> simp only [List.foldr_cons] at h <;> first | exact ih h.2 hm | exact ih h hm

/-- **The axiom premise of the phase theorems, from the entry environment.** Let `q` be
    declared after `pre` in `p`, with no earlier procedure of its name. Where `ρ₀` satisfies
    the axioms and distincts declared before `q`, the axioms of `pre` without bound variables
    evaluate to `true` in its store. -/
theorem axiomsHold_of_entry {p : Program} {pre post : List Decl} {q : Procedure}
    {md : Imperative.MetaData Expression} (hd : p.decls = pre ++ Decl.proc q md :: post)
    (hfirst : ∀ q' md', Decl.proc q' md' ∈ pre → q'.header.name.name ≠ q.header.name.name)
    {ρ₀ : Imperative.Env Expression}
    (h : Core.Specification.AxiomsBeforeProcedureDecl q.header.name.name p ρ₀) :
    AxiomsHold ρ₀.factory pre ρ₀.store := by
  rw [← Program.declsBeforeProcedure_eq hd hfirst]
  exact axiomsHold_of_axiomsBeforeProcedureDecl h

end -- public section

end FoldAxioms
end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.IrrelevantAxioms
import all Strata.Transform.IrrelevantAxioms
import Strata.Languages.Core.ProgramProps

/-! # Properties of `removeIrrelevantAxioms`

Key results:

* `irrelevantAxiomsTransform_run` — a successful run keeps the procedures in order and drops
  only other declarations, which is what the phase's contract follows from. -/

namespace Core

public section

/-- A successful run of `irrelevantAxiomsTransform` drops some declarations, all of them other
    than procedures. -/
private theorem irrelevantAxiomsTransform_filter {functions : List String} {p : Program}
    {s : Transform.CoreTransformState} {b : Bool} {p' : Program}
    {s' : Transform.CoreTransformState}
    (h : (irrelevantAxiomsTransform functions p).run s = (.ok (b, p'), s')) :
    ∃ q : Decl → Bool, (∀ d ∈ p.decls, d.kind = .proc → q d = true) ∧
      p' = { p with decls := p.decls.filter q } := by
  simp only [irrelevantAxiomsTransform, IrrelevantAxioms.run, ExceptT.run, bind, ExceptT.bind,
    ExceptT.mk, pure, ExceptT.pure, StateT.bind, StateT.pure, ExceptT.bindCont] at h
  injection h with hok _
  injection hok with hbp
  injection hbp with _ hp'
  refine ⟨_, fun d _ hk => ?_, hp'.symm⟩
  cases d <;> simp_all [Decl.kind]

/-- A successful run of `irrelevantAxiomsTransform` keeps the procedures in order, and every
    declaration it keeps is one of its input's. -/
theorem irrelevantAxiomsTransform_run {functions : List String} {p : Program}
    {s : Transform.CoreTransformState} {b : Bool} {p' : Program}
    {s' : Transform.CoreTransformState}
    (h : (irrelevantAxiomsTransform functions p).run s = (.ok (b, p'), s')) :
    p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc ∧ ∀ d ∈ p'.decls, d ∈ p.decls := by
  obtain ⟨q, hq, rfl⟩ := irrelevantAxiomsTransform_filter h
  exact ⟨Decl.filter_isProc_filter hq, fun d hd => (List.mem_filter.mp hd).1⟩

end -- public section

end Core

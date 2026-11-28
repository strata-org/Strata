/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.RecursiveFunctionAxioms
public import Strata.Transform.CoreTransformProps
import all Strata.Transform.RecursiveFunctionAxioms
import all Strata.Transform.CoreTransform
import Strata.Util.ExceptProps
import Strata.Languages.Core.ProgramProps

/-! # Properties of `recursiveAxioms`

Key results:

* `recursiveAxioms_run` — a successful run keeps the procedures in order, and changes only the
  `axioms` of the functions of recursive blocks. -/

namespace Core

public section

open Transform

/-- `f'` is `f` with its axioms replaced. -/
private def AxiomsOnly (f f' : Function) : Prop := f' = { f with axioms := f'.axioms }

/-- `d'` is `d`, or the recursive block `d` with the axioms of its functions replaced. -/
private def AxiomsOnlyDecl (d d' : Decl) : Prop :=
  d' = d ∨ ∃ fs fs' md, d = .recFuncBlock fs md ∧ d' = .recFuncBlock fs' md ∧
    ∀ f' ∈ fs', ∃ f ∈ fs, AxiomsOnly f f'

/-- `withRecursiveAxioms` changes only a function's axioms. -/
private theorem withRecursiveAxioms_ok {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {pe : Expression.Expr → Expression.Expr} {f f' : Function}
    (h : RecursiveAxioms.withRecursiveAxioms tf pe f = .ok f') : AxiomsOnly f f' := by
  unfold RecursiveAxioms.withRecursiveAxioms at h
  cases hg : generateRecursiveAxioms tf pe f.toLFunc with
  | error e => rw [hg] at h; cases h
  | ok lf =>
    rw [hg] at h
    cases h
    rfl

/-- **`recursiveAxioms` changes only the axioms of recursive blocks**: the procedures of its
    output are its input's, in order, and every declaration of its output is one of its
    input's, or a recursive block of its input with the functions' axioms replaced. -/
private theorem recursiveAxioms_post (options : VerifyOptions) (p : Program) :
    Post (RecursiveAxioms.run options p) fun (_, p') =>
      p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc ∧
      ∀ d' ∈ p'.decls, ∃ d ∈ p.decls, AxiomsOnlyDecl d d' := by
  unfold RecursiveAxioms.run
  split
  · exact Post.pure ⟨rfl, fun d hd => ⟨d, hd, .inl rfl⟩⟩
  · refine Post.bind (Post.true _) fun _ _ => ?_
    refine Post.bind (Post.forIn (I := fun rest (b : Bool × Array Decl) =>
        ∃ pre, pre ++ rest = p.decls ∧ b.2.toList.filter Decl.isProc = pre.filter Decl.isProc ∧
          ∀ d' ∈ b.2.toList, ∃ d ∈ p.decls, AxiomsOnlyDecl d d')
      (Q := fun (b : Bool × Array Decl) =>
        b.2.toList.filter Decl.isProc = p.decls.filter Decl.isProc ∧
          ∀ d' ∈ b.2.toList, ∃ d ∈ p.decls, AxiomsOnlyDecl d d')
      (fun b ⟨pre, hpre, hprocs, hall⟩ => ⟨by simpa [← hpre] using hprocs, hall⟩)
      ?_ p.decls (false, #[]) ⟨[], by simp, by simp, by simp⟩) ?_
    · rintro d rest ⟨changed, acc⟩ ⟨pre, hpre, hprocs, hall⟩
      have hd : d ∈ p.decls := by rw [← hpre]; simp
      have hpre' : (pre ++ [d]) ++ rest = p.decls := by simpa using hpre
      split
      · rename_i fs md
        refine Post.bind Post.liftDiag fun fs' hfs' => ?_
        have hm : ∀ f' ∈ fs', ∃ f ∈ fs, AxiomsOnly f f' := fun f' hf' =>
          (mapM_except_mem_right _ fs fs' hfs' f' hf').imp fun _ ⟨hf, h⟩ =>
            ⟨hf, withRecursiveAxioms_ok h⟩
        have hstep : ∀ c : Bool, (fun rest b => ∃ pre, pre ++ rest = p.decls ∧
            b.2.toList.filter Decl.isProc = pre.filter Decl.isProc ∧
            ∀ d' ∈ b.2.toList, ∃ d ∈ p.decls, AxiomsOnlyDecl d d') rest
            ((c, acc.push (.recFuncBlock fs' md)) : Bool × Array Decl) :=
          fun c => ⟨pre ++ [.recFuncBlock fs md], hpre', by
            simp [List.filter_append, hprocs, Decl.isProc, Decl.kind], fun d' hd' => by
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd'
            rcases hd' with hd' | rfl
            · exact hall d' hd'
            · exact ⟨_, hd, .inr ⟨fs, fs', md, rfl, rfl, hm⟩⟩⟩
        split
        · exact Post.pure (hstep true)
        · exact Post.pure (hstep _)
      · rename_i other _
        exact Post.pure ⟨pre ++ [d], hpre', by simp [List.filter_append, hprocs],
          fun d' hd' => by
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hd'
            rcases hd' with hd' | rfl
            · exact hall d' hd'
            · exact ⟨_, hd, .inl rfl⟩⟩
    · rintro ⟨changed, acc⟩ ⟨hprocs, hall⟩
      exact Post.pure ⟨hprocs, hall⟩

/-- Every function `recursiveAxioms` outputs is one of its input's with its axioms replaced, so
    it agrees with that function on any check that ignores axioms. -/
private theorem recursiveAxioms_funcs {p p' : Program}
    (hall : ∀ d' ∈ p'.decls, ∃ d ∈ p.decls, AxiomsOnlyDecl d d') {c : Function → Bool}
    (hc : ∀ f ax, c { f with axioms := ax } = c f) :
    ∀ d' ∈ p'.decls, ∀ f' ∈ d'.funcs, c f' = true ∨ ∃ d ∈ p.decls, ∃ f ∈ d.funcs, c f' = c f := by
  intro d' hd' f' hf'
  obtain ⟨d, hd, hdd⟩ := hall d' hd'
  rcases hdd with rfl | ⟨fs, fs', md, rfl, rfl, hm⟩
  · exact .inr ⟨d', hd, f', hf', rfl⟩
  · obtain ⟨f, hf, h⟩ := hm f' hf'
    exact .inr ⟨_, hd, f, hf, by rw [h, hc]⟩

/-- **`recursiveAxioms` changes only the axioms of recursive blocks**: the procedures of its
    output are its input's, in order, and every function of its output agrees with a function
    of its input on any check that ignores axioms. -/
theorem recursiveAxioms_run {options : VerifyOptions} {p p' : Program}
    {s s' : CoreTransformState} {b : Bool}
    (hrun : (RecursiveAxioms.run options p).run s = (.ok (b, p'), s')) :
    p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc ∧
      ∀ c : Function → Bool, (∀ f ax, c { f with axioms := ax } = c f) →
        ∀ d' ∈ p'.decls, ∀ f' ∈ d'.funcs,
          c f' = true ∨ ∃ d ∈ p.decls, ∃ f ∈ d.funcs, c f' = c f :=
  let ⟨hprocs, hall⟩ := recursiveAxioms_post options p s (b, p') s' hrun
  ⟨hprocs, fun _ hc => recursiveAxioms_funcs hall hc⟩

end -- public section

end Core

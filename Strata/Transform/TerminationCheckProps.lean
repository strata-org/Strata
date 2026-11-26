/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.TerminationCheck
public import Strata.Transform.CoreTransformProps
import all Strata.Transform.TerminationCheck
import all Strata.DL.Lambda.AdtRankAxioms
import Strata.Util.ListUtilsProps
import Strata.Languages.Core.ProgramProps

/-! # Properties of `termCheck`

Key results:

* `termCheck_post` — `termCheck` keeps the procedures of its input in order, and keeps
  `noPrecondsFromFuncs`.
* `termCheckDecls_post` (private) — the declaration loop keeps the procedures of its input in
  order, and every function it outputs is one of the input's, or a rank function without
  preconditions, or a member of one of the input's recursive blocks with its lemma list
  extended. -/

namespace Core

public section

open Transform

/-- What the declaration loop of `termCheck` may put in its output, given its input `decls`. -/
private def TermCheck.FromInput (decls : List Decl) : Decl → Prop
  | .func f _ => (∃ md, Decl.func f md ∈ decls) ∨ f.preconditions = []
  | .recFuncBlock fs _ => ∀ f ∈ fs, ∃ gs md, Decl.recFuncBlock gs md ∈ decls ∧
      ∃ g ∈ gs, f = { g with lemmas := f.lemmas }
  | _ => True

/-- A rank declaration `mkAdtRankDecls` makes is a function without preconditions. -/
private theorem mkAdtRankDecls_func (a : String) (tf : @Lambda.TypeFactory Unit)
    (md : Imperative.MetaData Expression) :
    ∀ x ∈ (TermCheck.mkAdtRankDecls a tf md).namedDecls,
      ∃ f, x.2 = Decl.func f md ∧ f.preconditions = [] := by
  unfold TermCheck.mkAdtRankDecls
  split
  · simp
  · simp only [List.mem_map]
    rintro _ ⟨dt, -, rfl⟩
    exact ⟨_, rfl, rfl⟩

/-- When `termCheck`'s declaration loop replaces a recursive block by rank functions `R`,
    lemmas `L` and the block with members `fs'`, the output so far followed by the remaining
    declarations still has the input's procedures in order, every declaration of the output so
    far is one `TermCheck.FromInput` admits, and every remaining declaration is the input's:
    provided each of `R` is a function without preconditions and each of `fs'` is a member of the
    block with its lemma list changed. -/
private theorem rankStep_inv {decls : List Decl} {acc : Array Decl} {rest : List Decl}
    {funcs : List Function} {md : Imperative.MetaData Expression}
    (R : List Decl) (L : List Lemma) (fs' : List Function)
    (hR : ∀ x ∈ R, ∃ f, x = Decl.func f md ∧ f.preconditions = [])
    (hfs : ∀ f ∈ fs', ∃ g ∈ funcs, f = { g with lemmas := f.lemmas })
    (hd : Decl.recFuncBlock funcs md ∈ decls)
    (hprocs : (acc.toList ++ Decl.recFuncBlock funcs md :: rest).filter Decl.isProc =
      decls.filter Decl.isProc)
    (hacc : ∀ d ∈ acc.toList, TermCheck.FromInput decls d) (hrest : ∀ e ∈ rest, e ∈ decls) :
    (((acc ++ R.toArray ++ (L.map (Decl.lemma · md)).toArray).push
        (Decl.recFuncBlock fs' md)).toList ++ rest).filter Decl.isProc = decls.filter Decl.isProc ∧
    (∀ e ∈ ((acc ++ R.toArray ++ (L.map (Decl.lemma · md)).toArray).push
        (Decl.recFuncBlock fs' md)).toList, TermCheck.FromInput decls e) ∧
    ∀ e ∈ rest, e ∈ decls := by
  have hRp : R.filter Decl.isProc = [] := Decl.filter_isProc_eq_nil fun x hx => by
    obtain ⟨f, rfl, -⟩ := hR x hx; simp [Decl.isProc, Decl.kind]
  refine ⟨?_, ?_, hrest⟩
  · rw [← hprocs]
    simp [List.filter_append, hRp, Decl.isProc, Decl.kind, List.filter_map,
      Function.comp_def]
  · intro e he
    simp only [Array.toList_push, Array.toList_append, List.mem_append,
      List.mem_map, List.mem_singleton] at he
    rcases he with ((he | he) | ⟨l, -, rfl⟩) | rfl
    · exact hacc e he
    · obtain ⟨f, rfl, hf⟩ := hR e he; exact .inr hf
    · trivial
    · intro f hf
      obtain ⟨g, hg, hfg⟩ := hfs f hf
      exact ⟨funcs, md, hd, g, hg, hfg⟩

/-- **The declaration loop of `termCheck` keeps the procedures of its input in order**, and
    every declaration it outputs is one `TermCheck.FromInput` admits: a function of the input or
    one without preconditions, or a recursive block whose members are the input's with their
    lemma lists extended. -/
private theorem termCheckDecls_post (taken : Std.HashSet String) (decls : List Decl)
    (tf : @Lambda.TypeFactory Unit) (emitted : Std.HashSet String) :
    Post (TermCheck.termCheckDecls taken decls tf emitted) fun (_, out) =>
      out.filter Decl.isProc = decls.filter Decl.isProc ∧
      ∀ d ∈ out, TermCheck.FromInput decls d := by
  unfold TermCheck.termCheckDecls
  refine Post.bind (Q₁ := fun (b : Array Decl × Bool × List Decl × @Lambda.TypeFactory Unit ×
      Std.HashSet String × Std.HashSet String) =>
      b.1.toList.filter Decl.isProc = decls.filter Decl.isProc ∧
      ∀ d ∈ b.1.toList, TermCheck.FromInput decls d)
    (Post.loop (fun b => b.2.2.1.length) (I := fun b =>
      (b.1.toList ++ b.2.2.1).filter Decl.isProc = decls.filter Decl.isProc ∧
      (∀ d ∈ b.1.toList, TermCheck.FromInput decls d) ∧ (∀ d ∈ b.2.2.1, d ∈ decls)) ?_ _
      ⟨by simp, by simp, fun _ h => h⟩) ?_
  · rintro ⟨acc, changed, remaining, tf', em, tk⟩ ⟨hprocs, hacc, hrem⟩
    dsimp only at hprocs hacc hrem ⊢
    cases remaining with
    | nil =>
      simp only [ne_eq, not_true_eq_false, dite_false]
      exact Post.pure ⟨by simpa using hprocs, hacc⟩
    | cons d rest =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, List.head_cons,
        List.tail_cons]
      have hd : d ∈ decls := hrem d List.mem_cons_self
      have hrest : ∀ e ∈ rest, e ∈ decls := fun e he => hrem e (List.mem_cons_of_mem _ he)
      -- Pushing `d` itself keeps the invariant, for any `d` of the input but a recursive block.
      have hpush : TermCheck.FromInput decls d →
          ((acc.push d).toList ++ rest).filter Decl.isProc = decls.filter Decl.isProc ∧
          (∀ e ∈ (acc.push d).toList, TermCheck.FromInput decls e) ∧ ∀ e ∈ rest, e ∈ decls :=
        fun hf => ⟨by simpa using hprocs, fun e he => by
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hacc e he
          · exact hf, hrest⟩
      cases d with
      | recFuncBlock funcs md =>
        repeat' first
          | exact Post.bind Post.throw fun _ h => (h : False).elim
          | (refine Post.bind (Post.true _) fun _ _ => ?_)
          | split
        · -- The block is kept as it is.
          refine Post.pure ⟨⟨?_, ?_, hrest⟩, by simp⟩
          · rw [← hprocs]; simp [List.filter_append, Decl.isProc, Decl.kind]
          · intro e he
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at he
            rcases he with he | rfl
            · exact hacc e he
            · intro f hf
              exact ⟨funcs, md, hd, f, hf, by cases f; rfl⟩
        · -- Rank functions and lemmas are spliced before the block.
          refine Post.pure ⟨rankStep_inv _ _ _ ?_ ?_ hd hprocs hacc hrest, by simp⟩
          · intro x hx
            simp only [List.mem_filterMap, List.mem_flatMap] at hx
            obtain ⟨y, ⟨r, hr, hy⟩, hx⟩ := hx
            split at hx
            · cases hx
            · cases hx
              obtain ⟨a, rfl⟩ := List.foldl_snd_forall
                (P := fun r => ∃ a, r = TermCheck.mkAdtRankDecls a tf' md) _
                (fun x n hx r hr => by
                  split at hr
                  · exact hx r hr
                  · rcases List.mem_cons.mp hr with rfl | hr
                    · exact ⟨n, rfl⟩
                    · exact hx r hr)
                _ _ (by simp) r (List.mem_reverse.mp hr)
              exact mkAdtRankDecls_func a tf' md y hy
          · intro f hf
            simp only [List.mem_map] at hf
            obtain ⟨⟨g, l⟩, hmem, rfl⟩ := hf
            exact ⟨g, (List.of_mem_zip hmem).1, rfl⟩
      | func f md =>
        exact Post.pure ⟨hpush (.inl ⟨md, hd⟩), by simp⟩
      | type t md =>
        cases t <;> exact Post.pure ⟨hpush trivial, by simp⟩
      | _ => exact Post.pure ⟨hpush trivial, by simp⟩
  · rintro ⟨acc, changed, remaining, tf', em, tk⟩ ⟨hprocs, hacc⟩
    exact Post.pure ⟨hprocs, hacc⟩


/-- Every function `termCheck`'s declaration loop outputs is a function of its input, a
    function without preconditions, or a member of one of its input's recursive blocks with its
    lemma list changed. -/
private theorem FromInput.funcs {decls : List Decl} {d : Decl}
    (h : TermCheck.FromInput decls d) {c : Function → Bool}
    (hc : ∀ f ls, c { f with lemmas := ls } = c f) :
    ∀ f ∈ d.funcs, f.preconditions = [] ∨ ∃ e ∈ decls, ∃ g ∈ e.funcs, c f = c g := by
  intro f hf
  cases d with
  | func f' md =>
    simp only [Decl.funcs, List.mem_singleton] at hf
    subst hf
    rcases h with ⟨md', hm⟩ | h
    · exact .inr ⟨_, hm, f, by simp [Decl.funcs], rfl⟩
    · exact .inl h
  | recFuncBlock fs md =>
    obtain ⟨gs, md', hgs, g, hg, hfg⟩ := h f hf
    exact .inr ⟨_, hgs, g, hg, by rw [hfg, hc]⟩
  | _ => simp [Decl.funcs] at hf

/-- `termCheck` keeps the procedures of its input in order, and keeps `noPrecondsFromFuncs`. -/
theorem termCheck_post (p : Program) :
    Post (TermCheck.termCheck p) fun (_, p') =>
      p'.decls.filter Decl.isProc = p.decls.filter Decl.isProc ∧
      (p.noFuncPreconditions = true → p'.noFuncPreconditions = true) := by
  unfold TermCheck.termCheck
  refine Post.bind (termCheckDecls_post _ _ _ _) ?_
  rintro ⟨changed, D⟩ ⟨hprocs, hfrom⟩
  refine Post.pure ⟨hprocs, fun hpre => ?_⟩
  rw [Program.noFuncPreconditions_eq_funcsAll] at hpre ⊢
  exact Program.funcsAll_of_funcs (fun d hd f hf =>
    (FromInput.funcs (hfrom d hd) (c := (·.preconditions.isEmpty)) (fun _ _ => rfl) f hf).imp
      (by simp) id) hpre

end -- public section

end Core

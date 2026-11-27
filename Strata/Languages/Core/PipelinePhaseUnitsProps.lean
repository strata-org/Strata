/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.ExceptProps
import Strata.Transform.CoreTransformProps
public import Strata.Languages.Core.PipelinePhaseUnits
public import Strata.Languages.Core.PipelineUnitChainProps
public import Strata.Transform.TerminationCheckPhase
import all Strata.Languages.Core.PipelineUnitChain
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.TerminationCheck
import all Strata.Transform.TerminationCheckPhase
import all Strata.Transform.NondetElim
import all Strata.Transform.FilterProcedures
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Phases act procedure by procedure

The program-level transform of several phases maps the body (`Program.bodyOf`) and the
unit (`Program.unitBodyOf`, the contract-wrapped body) of a procedure by a fixed map, so a
back-link stated at that map applies at the procedure's units.  Each result is about a
successful run of the phase (`PipelinePhase.Produces`).

Key theorems:

* `termCheckPhase_bodyOf`, `termCheckPhase_unitBodyOf` — `termCheck` leaves the body and
  the unit of every procedure unchanged (it adds lemmas, not procedures);
* `nondetElimPhase_bodyOf`, `nondetElimPhase_unitBodyOf` — `nondetElim` maps every body and
  every unit by `Block.nondetElim`;
* `filterProceduresPhase_bodyOf`, `filterProceduresPhase_unitBodyOf` — `filterProcedures`
  keeps the body and the unit of every procedure it keeps;
* `assertFactPhase_output` — an `assertFactPhase` returns its input program. -/

namespace Core

open Imperative Transform
open Decl Program Block TermCheck

public section

/-! ## Bodies depend only on the procedures of their name -/

/-- Two programs with the same procedures named `n`, in the same order, have the same body
    of `n` (`Program.bodyOf`). -/
private theorem Program.bodyOf_eq_of_filter {p p' : Program} {n : String}
    (h : p'.decls.filter (Decl.isProcNamed n) = p.decls.filter (Decl.isProcNamed n)) :
    p'.bodyOf n = p.bodyOf n := by
  have hfs := List.findSome?_filter (bodyNamed n) (isProcNamed n)
    (fun x h => by cases x <;> grind [isProcNamed, bodyNamed])
  rw [bodyOf, bodyOf, ← hfs, h, hfs]

/-- Two programs with the same procedures named `n`, in the same order, have the same unit
    of `n` (`Program.unitBodyOf`). -/
private theorem Program.unitBodyOf_eq_of_filter {p p' : Program} {n : String}
    (h : p'.decls.filter (Decl.isProcNamed n) = p.decls.filter (Decl.isProcNamed n)) :
    p'.unitBodyOf n = p.unitBodyOf n := by
  have hfs := List.findSome?_filter (unitNamed n) (isProcNamed n)
    (fun x h => by cases x <;> grind [isProcNamed, unitNamed])
  rw [unitBodyOf, unitBodyOf, ← hfs, h, hfs]

/-! ## `termCheck` -/

/-- Filtering by `Decl.isProc` and then by `Decl.isProcNamed n` is filtering by
    `Decl.isProcNamed n`. -/
private theorem filter_isProc_isProcNamed (n : String) (l : List Decl) :
    (l.filter Decl.isProc).filter (Decl.isProcNamed n) = l.filter (Decl.isProcNamed n) := by
  rw [List.filter_filter]
  congr 1
  funext d
  cases d <;> simp [Decl.isProcNamed, Decl.isProc, Decl.kind]

/-- A successful run of `termCheck` returns declarations with the same procedures named `n`,
    in the same order, as its input (from `termCheck_post`). -/
private theorem termCheck_filter (p : Program) {n : String} :
    Post (TermCheck.termCheck p)
      (fun r => r.2.decls.filter (Decl.isProcNamed n) = p.decls.filter (Decl.isProcNamed n)) :=
  (termCheck_post p).mono fun _ h => by
    rw [← filter_isProc_isProcNamed, h.1, filter_isProc_isProcNamed]

/-- **`termCheck` leaves every procedure unchanged**: for every name `n`, the body of `n`
    after a successful run is the body before. -/
private theorem termCheck_bodyOf_ok (p : Program) {n : String} :
    Post (TermCheck.termCheck p) (fun r => r.2.bodyOf n = p.bodyOf n) :=
  (termCheck_filter p).mono fun _ h => Program.bodyOf_eq_of_filter h

/-- For every name `n`, the unit of `n` (its contract-wrapped body) after a successful run
    of `termCheck` is the unit before. -/
private theorem termCheck_unitBodyOf_ok (p : Program) {n : String} :
    Post (TermCheck.termCheck p) (fun r => r.2.unitBodyOf n = p.unitBodyOf n) :=
  (termCheck_filter p).mono fun _ h => Program.unitBodyOf_eq_of_filter h

/-! ## `nondetElim` -/

/-- If `ys` is related to `xs` elementwise by `R`, and `R x y` makes `g y` the image of
    `g x` under `k`, the first `some` result of `g` over `ys` is the image under `k` of the
    first over `xs`. -/
private theorem findSome?_forall₂_map {α γ : Type} {R : α → α → Prop} (g : α → Option γ) (k : γ → γ)
    (hR : ∀ x y, R x y → g y = (g x).map k) :
    ∀ {xs ys : List α}, List.Rel₂ R xs ys → ys.findSome? g = (xs.findSome? g).map k
  := fun h => by induction h <;> grind

/-- If every successful `f x` is related to `x` by `R` on its first component, a
    successful `xs.mapM f` is related to `xs` elementwise on the first components. -/
private theorem mapM_ok_listRel {α β ε : Type} {f : α → Except ε (α × β)} {R : α → α → Prop}
    (hf : ∀ x y, f x = .ok y → R x y.1) :
    ∀ {xs : List α} {ys}, xs.mapM f = .ok ys → List.Rel₂ R xs (ys.map Prod.fst) :=
  fun h => (mapM_except_rel₂ _ _ _ h).map_right Prod.fst hf

/-- A successful run of `nondetElim` returns the first components of a successful
    `nondetElimDecl` over the declarations. -/
private theorem nondetElim_ok {p : Program} {Q : Program → Prop}
    (h : ∀ ys, p.decls.mapM NondetElim.nondetElimDecl = .ok ys →
      Q { decls := ys.map Prod.fst }) :
    Post (NondetElim.nondetElim p) (fun r => Q r.2) := fun s r s' hrun => by
  cases hmap : p.decls.mapM NondetElim.nondetElimDecl with
  | error => simp only [NondetElim.nondetElim, hmap, liftExcept] at hrun; cases hrun
  | ok ys =>
    simp only [NondetElim.nondetElim, hmap, liftExcept] at hrun
    cases hrun
    exact h ys hmap

/-- **`nondetElim` maps every body by `Block.nondetElim`**: after a successful run, the body
    of every procedure name is `Block.nondetElim` of its body before. -/
private theorem nondetElim_bodyOf_ok (p : Program) :
    Post (NondetElim.nondetElim p)
      (fun r => ∀ n, r.2.bodyOf n = Block.nondetElim (p.bodyOf n)) := by
  refine nondetElim_ok (Q := fun q => ∀ n, q.bodyOf n = Block.nondetElim (p.bodyOf n))
    fun ys hys n => ?_
  have hrel := mapM_ok_listRel (R := fun d a => ∀ n, Decl.bodyNamed n a =
    (Decl.bodyNamed n d).map Block.nondetElim) (fun d y hy => ?_) hys
  · simp only [Program.bodyOf]
    rw [findSome?_forall₂_map _ _ (fun x y h => h n) hrel]
    cases (p.decls.findSome? _) <;> simp [Block.nondetElim, Block.nondetElimM]
  · rcases d with _ | _ | _ | _ | ⟨⟨_, _, _ | _⟩⟩ | _ <;>
      simp only [NondetElim.nondetElimDecl] at hy <;> cases hy <;> simp!

/-- `nondetElim` leaves a prefix of commands in place. -/
private theorem nondetElimM_cmds_append (cs : List Statement) (hcs : ∀ s ∈ cs, ∃ c, s = .cmd c)
    (rest : List Statement) (σ : StringGenState) :
    Block.nondetElimM (cs ++ rest) σ =
      (cs ++ (Block.nondetElimM rest σ).1, (Block.nondetElimM rest σ).2) := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    obtain ⟨c, rfl⟩ := hcs s (.head _)
    simp [Block.nondetElimM, Stmt.nondetElimM, ih fun s h => hcs s (.tail _ h)]

/-- A list prepended inside a pattern match on a statement-list result can be moved out of
    the match, past a suffix appended afterwards. -/
private theorem pair_append_match (x : List Statement × StringGenState) (a cs : List Statement) :
    (a ++ (x.1 ++ cs), x.2) =
      ((match x with | (r, σ2) => (a ++ r, σ2)).1 ++ cs,
        (match x with | (r, σ2) => (a ++ r, σ2)).2) := by simp

/-- `nondetElim` leaves a suffix of commands in place. -/
private theorem nondetElimM_append_cmds (cs : List Statement) (hcs : ∀ s ∈ cs, ∃ c, s = .cmd c) :
    ∀ (body : List Statement) (σ : StringGenState),
    Block.nondetElimM (body ++ cs) σ =
      ((Block.nondetElimM body σ).1 ++ cs, (Block.nondetElimM body σ).2)
  := fun body => by
  induction body with
  | nil => intro σ; simpa [Block.nondetElimM] using nondetElimM_cmds_append _ hcs [] σ
  | cons s b ih =>
    intro σ
    simp only [List.cons_append, Block.nondetElimM, ih]
    exact pair_append_match _ _ _

/-- **`nondetElim` commutes with the contract wrapping**: the assumed preconditions and
    the asserted postconditions are commands, which it leaves in place. -/
private theorem nondetElim_procPassive (q : Procedure) (ss : List Statement) :
    Block.nondetElim (WPObl.procPassive q ss) = WPObl.procPassive q (Block.nondetElim ss) := by
  grind [Block.nondetElim, WPObl.procPassive, nondetElimM_cmds_append, nondetElimM_append_cmds]

/-- **`nondetElim` maps every unit by `Block.nondetElim`**: after a successful run, the unit
    (contract-wrapped body) of every procedure name is `Block.nondetElim` of its unit
    before. -/
private theorem nondetElim_unitBodyOf_ok (p : Program) :
    Post (NondetElim.nondetElim p)
      (fun r => ∀ n, r.2.unitBodyOf n = Block.nondetElim (p.unitBodyOf n)) := by
  refine nondetElim_ok
    (Q := fun q => ∀ n, q.unitBodyOf n = Block.nondetElim (p.unitBodyOf n)) fun ys hys n => ?_
  have hrel := mapM_ok_listRel (R := fun d a => ∀ n, Decl.unitNamed n a =
    (Decl.unitNamed n d).map Block.nondetElim) (fun d y hy => ?_) hys
  · simp only [Program.unitBodyOf]
    rw [findSome?_forall₂_map _ _ (fun x y h => h n) hrel]
    cases (p.decls.findSome? _) <;> simp [Block.nondetElim, Block.nondetElimM]
  · rcases d with _ | _ | _ | _ | ⟨⟨_, _, _ | _⟩⟩ | _ <;>
      simp only [NondetElim.nondetElimDecl] at hy <;> cases hy <;>
      simp! [nondetElim_procPassive] <;> try (intro; rfl)

/-! ## `filterProcedures` -/

/-- A successful `FilterProcedures.run` returns a program whose declarations are a filter
    of the input's. -/
private theorem filterProceduresPhase_run_ok' (p : Program) (procs : List String)
    (respectNoFilter : Bool) :
    Post (FilterProcedures.run p procs respectNoFilter)
      (fun r => ∃ keep : Decl → Bool, r.2.decls = p.decls.filter keep) := by
  repeat refine .bind (Post.true _) fun _ _ => ?_
  exact .pure ⟨_, rfl⟩

/-- **Filtering the declarations keeps the body of a procedure it keeps**: if the
    declarations of `p'` are a filter of those of `p`, `p` has at most one procedure named
    `n`, and `p'` still has one, the body of `n` in `p'` is its body in `p`. -/
private theorem bodyOf_of_filter {p p' : Program} {keep : Decl → Bool}
    (h : p'.decls = p.decls.filter keep)
    {n : String} (huniq : (p.decls.filter (Decl.isProcNamed n)).length ≤ 1)
    (hmem : ∃ d ∈ p'.decls, Decl.isProcNamed n d = true) : p'.bodyOf n = p.bodyOf n := by
  have ⟨_, hd, hn⟩ := hmem
  rw [h] at hd
  apply Program.bodyOf_eq_of_filter
  rw [h]
  exact (List.filter_sublist.filter _).eq_of_length_le
    (Nat.le_trans huniq (List.length_pos_of_mem (List.mem_filter.2 ⟨hd, hn⟩)))

/-- **Filtering the declarations keeps the unit of a procedure it keeps**: if the
    declarations of `p'` are a filter of those of `p`, `p` has at most one procedure named
    `n`, and `p'` still has one, the unit (contract-wrapped body) of `n` in `p'` is its unit
    in `p`. -/
private theorem unitBodyOf_of_filter {p p' : Program} {keep : Decl → Bool}
    (h : p'.decls = p.decls.filter keep)
    {n : String} (huniq : (p.decls.filter (Decl.isProcNamed n)).length ≤ 1)
    (hmem : ∃ d ∈ p'.decls, Decl.isProcNamed n d = true) : p'.unitBodyOf n = p.unitBodyOf n := by
  have ⟨_, hd, hn⟩ := hmem
  rw [h] at hd
  apply Program.unitBodyOf_eq_of_filter
  rw [h]
  exact (List.filter_sublist.filter _).eq_of_length_le
    (Nat.le_trans huniq (List.length_pos_of_mem (List.mem_filter.2 ⟨hd, hn⟩)))

/-! ## Phase-level statements -/

/-- A property `Q` that every successful run of a phase's transform on `p` gives its output
    program holds of every program the phase produces from `p` (`PipelinePhase.Produces`). -/
private theorem PipelinePhase.Produces.of_post {pp : PipelinePhase} {p p' : Program}
    {Q : Program → Prop}
    (h : Post (pp.transform p) (fun r => Q r.2)) (hp : pp.Produces p p') : Q p' := by
  have ⟨s, s', hp⟩ := hp
  refine Post.bind h ?_ s p' s' hp
  exact fun ⟨_, _⟩ c => .pure c

/-- If `termCheck` produces `p'` from `p` (`PipelinePhase.Produces`), it leaves the body of
    every procedure unchanged. -/
theorem termCheckPhase_bodyOf {p p' : Program} (hp : termCheckPipelinePhase.Produces p p')
    {n : String} : p'.bodyOf n = p.bodyOf n :=
  hp.of_post (Q := (·.bodyOf n = _)) (termCheck_bodyOf_ok p)

/-- If `nondetElim` produces `p'` from `p` (`PipelinePhase.Produces`), it maps the body of
    every procedure by `Block.nondetElim`. -/
theorem nondetElimPhase_bodyOf {p p' : Program}
    (hp : NondetElim.nondetElimPipelinePhase.Produces p p')
    (n : String) : p'.bodyOf n = Block.nondetElim (p.bodyOf n) :=
  hp.of_post (Q := (·.bodyOf n = _)) ((nondetElim_bodyOf_ok p).mono fun _ h => h n)

/-- If `filterProcedures` produces `p'` from `p` (`PipelinePhase.Produces`), the
    declarations of `p'` are a filter of those of `p`. -/
private theorem filterProceduresPhase_decls {procs : List String} {respectNoFilter : Bool}
    {p p' : Program}
    (hp : (filterProceduresPipelinePhase procs respectNoFilter).Produces p p') :
    ∃ keep : Decl → Bool, p'.decls = p.decls.filter keep :=
  hp.of_post (Q := fun q => ∃ k : Decl → Bool, q.decls = p.decls.filter k)
    (.bind (filterProceduresPhase_run_ok' p _ _) fun ⟨_, _⟩ h => .pure h)

/-- If `filterProcedures` produces `p'` from `p` (`PipelinePhase.Produces`), it keeps the
    body of a procedure it keeps, when `p` has at most one procedure of that name. -/
theorem filterProceduresPhase_bodyOf {procs : List String} {respectNoFilter : Bool}
    {p p' : Program}
    (hp : (filterProceduresPipelinePhase procs respectNoFilter).Produces p p') {n : String}
    (huniq : (p.decls.filter (Decl.isProcNamed n)).length ≤ 1)
    (hmem : ∃ d ∈ p'.decls, Decl.isProcNamed n d = true) : p'.bodyOf n = p.bodyOf n :=
  (filterProceduresPhase_decls hp).elim fun _ hk => bodyOf_of_filter hk huniq hmem

/-- If `termCheck` produces `p'` from `p` (`PipelinePhase.Produces`), it leaves the unit
    (contract-wrapped body) of every procedure unchanged. -/
theorem termCheckPhase_unitBodyOf {p p' : Program} (hp : termCheckPipelinePhase.Produces p p')
    {n : String} : p'.unitBodyOf n = p.unitBodyOf n :=
  hp.of_post (Q := (·.unitBodyOf n = _)) (termCheck_unitBodyOf_ok p)

/-- If `nondetElim` produces `p'` from `p` (`PipelinePhase.Produces`), it maps the unit
    (contract-wrapped body) of every procedure by `Block.nondetElim`. -/
theorem nondetElimPhase_unitBodyOf {p p' : Program}
    (hp : NondetElim.nondetElimPipelinePhase.Produces p p')
    (n : String) : p'.unitBodyOf n = Block.nondetElim (p.unitBodyOf n) :=
  hp.of_post (Q := (·.unitBodyOf n = _)) ((nondetElim_unitBodyOf_ok p).mono fun _ h => h n)

/-- If `filterProcedures` produces `p'` from `p` (`PipelinePhase.Produces`), it keeps the
    unit (contract-wrapped body) of a procedure it keeps, when `p` has at most one procedure
    of that name. -/
theorem filterProceduresPhase_unitBodyOf {procs : List String} {respectNoFilter : Bool}
    {p p' : Program}
    (hp : (filterProceduresPipelinePhase procs respectNoFilter).Produces p p') {n : String}
    (huniq : (p.decls.filter (Decl.isProcNamed n)).length ≤ 1)
    (hmem : ∃ d ∈ p'.decls, Decl.isProcNamed n d = true) : p'.unitBodyOf n = p.unitBodyOf n :=
  (filterProceduresPhase_decls hp).elim fun _ hk => unitBodyOf_of_filter hk huniq hmem

/-- If an `assertFactPhase` produces `p'` from `p` (`PipelinePhase.Produces`), then
    `p' = p`. -/
theorem assertFactPhase_output {f : ProgramFact}
    {hc : f.check?.isSome = true} {p p' : Program}
    (hp : (assertFactPhase f hc).Produces p p') : p' = p :=
  hp.of_post (Q := (· = p)) (by
    dsimp only [assertFactPhase, assertFact]
    split
    · exact .pure rfl
    · exact .throw)

/-- An `assertFactPhase`'s recorded link (the identity lift) is valid at a pair of equal
    units (`LinkPreservesAt`: read as a targeted link, it preserves counterexample validity
    along the forward map sending exactly that unit to itself). -/
theorem assertFactPhase_linkPreservesAt {f : ProgramFact}
    {hc : f.check?.isSome = true} (π : String → Option Procedure) (input output : Program)
    (a : List Statement) :
    LinkPreservesAt π (((assertFactPhase f hc).buildBackLink input output).withPrograms
      input output) a a :=
  (linkPreservesAt_withPrograms _ _ _ _ _ _).2
    (linkPreservesAt_linked_id _ _ _ fun _ _ _ h _ ho => by grind [unitStep])

end -- public section
end Core

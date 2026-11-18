/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Trav

/-!
# Program relations for node-local rewrites

`prog_trav` says that applying a node rewrite `g` to every term of a program with
`mapLaurelProgramStmtExprM` gives a program related to the input by
`ProgRel (TE (fun _ e => g e) P)`. It needs `g` to satisfy `TravOK`, the program to satisfy
`ProgOK (Hered P)`, and `g` to keep literal values. The `Reserved` instance must have no return
label and no valued return, and leave its hooks trivial.

* `ProcOK`, `TypeOK`, `ProgOK Q p`: every term in the program satisfies `Q`, and no
  procedure is a coroutine or uses reserved parameter names.
* `TravOK g`: `g` leaves field accesses unchanged, does not create them, and keeps
  `isWildcard`. `travOK_mk` builds it from a node-level case split (`NodeRw`).
* `proc_trav`: one procedure and its rewritten version are related by `ProcRel`.
* `prog_trav_ix`: `prog_trav` with a given `Reserved.ixX` fact about the indices.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

section
variable [Reserved] {σ : Type} (g : StmtExprMd → StateM σ StmtExprMd) (Q : StmtExprMd → Prop)

def ProcOK (P : Procedure) : Prop :=
  (∀ c ∈ P.preconditions, Q c.condition) ∧ (∀ b, P.body.implementation = some b → Q b) ∧
    (∀ c ∈ P.body.postconditions, Q c.condition) ∧ P.is_coroutine = false ∧
    (∀ x ∈ P.outputs, ¬ Reserved.res x.name.text) ∧ (∀ x ∈ P.inputs, ¬ Reserved.res x.name.text) ∧
    ∀ g ∈ bodyModifies P.body, (∀ t ∈ g.targets, Q t) ∧ ∀ e, g.guard = some e → Q e

def TypeOK : TypeDefinition → Prop
  | .Composite ct => (∀ P ∈ ct.instanceProcedures, ProcOK Q P) ∧ (∀ f ∈ ct.fields, ∀ e, f.initializer = some e → Q e)
  | .Constrained c => Q c.constraint ∧ Q c.witness ∧ ¬ Reserved.res c.valueName.text
  | _ => True

def ProgOK (p : LaurelProgram) : Prop :=
  (∀ P ∈ p.staticProcedures, ProcOK Q P) ∧ (∀ t ∈ p.types, TypeOK Q t) ∧
    (∀ f ∈ p.staticFields, ∀ e, f.initializer = some e → Q e) ∧ (∀ P ∈ p.staticFunctions, ProcOK Q P) ∧
    (∀ c ∈ p.constants, ∀ e, c.initializer = some e → Q e)

end

section
variable [Reserved] {σ : Type} {g : StmtExprMd → StateM σ StmtExprMd} {P : StmtExprMd → Prop}

omit [Reserved] in
theorem mapM_rel_mem {R : α → β → Prop} (l : List α) (h : α → StateM σ β)
    (hh : ∀ x ∈ l, ∀ st, R x ((h x).run st).1) (st : σ) :
    L2 R l ((l.mapM h).run st).1 := by
  induction l generalizing st with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, run_bind1]
    exact .cons (hh x (List.mem_cons_self ..) st) (ih (fun y hy => hh y (List.mem_cons_of_mem _ hy)) _)

omit [Reserved] in
theorem L2.map_eq_key {k : α → γ} {k' : β → γ} {l : List α} {l' : List β}
    (h : L2 (fun a b => k a = k' b) l l') : l.map k = l'.map k' := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.map_cons, hab, ih]

structure TravOK (g : StmtExprMd → StateM σ StmtExprMd) : Prop where
  var : ∀ r st, (∃ o fn, r.val = .Var (.Field o fn)) → ((g r).run st).1 = r
  nf : ∀ r st, (∀ o fn, r.val ≠ .Var (.Field o fn)) → ∀ o fn, ((g r).run st).1.val ≠ .Var (.Field o fn)
  wild : ∀ r st, ((g r).run st).1.isWildcard = r.isWildcard

def NodeRw (r r' : StmtExprMd) : Prop :=
  (∀ o fn, r.val ≠ .Var (.Field o fn)) ∧ r.isWildcard = false ∧ (∀ o fn, r'.val ≠ .Var (.Field o fn)) ∧
    r'.isWildcard = false

omit [Reserved] in
/-- A node rewrite `g` satisfies `TravOK` if, for every term `r` and state, it either returns `r`
unchanged or rewrites it as `NodeRw` allows: neither `r` nor the result is a field access or a
wildcard. -/
theorem travOK_mk (hc : ∀ r st, ((g r).run st).1 = r ∨ NodeRw r ((g r).run st).1) : TravOK g where
  var := fun r st ⟨o, fn, h⟩ => (hc r st).resolve_right (fun h' => h'.1 o fn h)
  nf := fun r st h => by
    rcases hc r st with he | ⟨-, -, h', -⟩
    · rw [he]; exact h
    · exact h'
  wild := fun r st => by
    rcases hc r st with he | ⟨-, h1, -, h2⟩
    · rw [he]
    · rw [h1, h2]

omit [Reserved] in
theorem expr_trav {e : StmtExprMd} (he : Hered P e) (st : σ) :
    TE (fun _ e => g e) P e ((mapStmtExprM g e).run st).1 :=
  ⟨⟨false, st, rfl⟩, he⟩

omit [Reserved] in
theorem L2.map_rel {R R' : α → β → Prop} {l : List α} {l' : List β} (h : L2 R l l')
    (hf : ∀ a b, R a b → R' a b) : L2 R' l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hf _ _ hab) ih

omit [Reserved] in
theorem L2.any_eq {l : List α} {l' : List β} {p : α → Bool} {q : β → Bool}
    (h : L2 (fun a b => p a = q b) l l') : l.any p = l'.any q := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [List.any_cons, hab, ih]

omit [Reserved] in
theorem run_pure1 {α : Type} (x : α) (st : σ) : (pure x : StateM σ α).run st = (x, st) := rfl

theorem condMapM_rel (hvk : ∀ E a b, Reserved.vok E a b) (cs : List Condition) (hcs : ∀ c ∈ cs, Hered P c.condition) (st : σ) :
    L2 (CondRel (TE (fun _ e => g e) P)) cs
      ((cs.mapM (fun x => Condition.mapM (mapStmtExprM g) x)).run st).1 := by
  refine mapM_rel_mem _ _ (fun c hc st => ?_) st
  simp only [Condition.mapM, run_bind1, run_pure1]
  exact ⟨rfl, expr_trav (hcs c hc) st, hvk _ _ _⟩

structure SameSig (Pr Pr' : Procedure) : Prop where
  name : Pr.name = Pr'.name
  inputs : Pr.inputs = Pr'.inputs
  outputs : Pr.outputs = Pr'.outputs
  writes : Pr.writesGlobals = Pr'.writesGlobals
  throws : Pr.throwsType = Pr'.throwsType

/-- Rewriting the targets and guards of a list of modifies groups with `mapStmtExprM g` gives groups
related to the originals by `GroupRel (TE (fun _ e => g e) P)`, after dropping the wildcard groups
on both sides. The hypotheses: `g` satisfies `TravOK`, the pass has no valued return and trivial
hooks (`nodeOK`, `vok`), and every target and guard satisfies `Hered P`. -/
theorem frames_trav (hT : TravOK g) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e)
    (hvk : ∀ E a b, Reserved.vok E a b) (mods : List ModifiesGroup)
    (hm : ∀ g ∈ mods, (∀ t ∈ g.targets, Hered P t) ∧ ∀ e, g.guard = some e → Hered P e) (st : σ) :
    L2 (GroupRel (TE (fun _ e => g e) P)) (mods.filter fun g => !hasModifiesWildcard g.targets)
      (((mods.mapM fun (g_1 : ModifiesGroup) => do
          let targets' ← List.mapM (mapStmtExprM g) g_1.targets
          let guard' ← Option.mapM (mapStmtExprM g) g_1.guard
          pure ({ targets := targets', guard := guard', summary := g_1.summary } : ModifiesGroup)).run st).1.filter
        fun g => !hasModifiesWildcard g.targets) := by
  induction mods generalizing st with
  | nil => exact .nil
  | cons g1 gs ih =>
    simp only [List.mapM_cons, run_bind1, run_pure1]
    have hg1 := hm g1 (List.mem_cons_self ..)
    have hw : hasModifiesWildcard ((g1.targets.mapM (mapStmtExprM g)).run st).1 = hasModifiesWildcard g1.targets := by
      unfold hasModifiesWildcard
      refine (L2.any_eq ?_).symm
      exact mapM_rel_mem (R := fun (a b : StmtExprMd) => a.isWildcard = b.isWildcard) _ _
        (fun t _ st => (trav_wild (f := fun _ e => g e) (fun _ r st => hT.wild r st) false t st).symm) st
    simp only [List.filter_cons, hw]
    have ihs := ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))
    split
    · refine .cons ⟨?_, fun _ _ _ _ => hvk _ _ _, fun e _ => ovOK_none hvn _ _ hk, ?_⟩ (ihs _)
      · cases hgd : g1.guard with
        | none => simp only [Option.mapM, run_pure1, ORel]
        | some e => simp only [Option.mapM]; exact expr_trav (hg1.2 e hgd) _
      · exact mapM_rel_mem _ _ (fun t ht st => targ_trav
          (fun _ r st h => hT.var r st h) (fun _ r st h => hT.nf r st h) (fun e _ => ovOK_none hvn _ _ hk)
          (fun _ _ => hvk _ _ _) (hg1.1 t ht) false st) _
    · exact ihs _

/-- Rewriting the bodies of a procedure `Pr` (implementation, postconditions and modifies frames) with
`mapStmtExprM g` keeps its signature, preconditions and contracts, relates the old and new bodies by
`BodyRel` and the frames by `GroupRel`, all over `TE (fun _ e => g e) P`. The hypotheses: `g`
satisfies `TravOK`, the pass has no return label, no valued return and trivial hooks, and every term
in the body satisfies `Hered P`. -/
theorem bodies_trav (hT : TravOK g) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e)
    (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) {Pr : Procedure} (himpl : ∀ b, Pr.body.implementation = some b → Hered P b)
    (hpost : ∀ c ∈ Pr.body.postconditions, Hered P c.condition)
    (hmods : ∀ g ∈ bodyModifies Pr.body, (∀ t ∈ g.targets, Hered P t) ∧ ∀ e, g.guard = some e → Hered P e) (st : σ) :
    let Pr' := ((mapProcedureBodiesM (mapStmtExprM g) Pr).run st).1
    SameSig Pr Pr' ∧ Pr'.preconditions = Pr.preconditions ∧ Pr'.contracts = Pr.contracts ∧
      BodyRel (TE (fun _ e => g e) P) Pr.outputs Pr.body Pr'.body ∧
      L2 (GroupRel (TE (fun _ e => g e) P)) (procFrames Pr) (procFrames Pr') := by
  intro Pr'
  cases hb : Pr.body with
  | Transparent b =>
    simp only [Pr', mapProcedureBodiesM, hb, run_bind1, run_pure1, procFrames]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by trivial, by trivial, .transparent (.plain hret (expr_trav (himpl b (by simp [hb, Body.implementation])) st)), .nil⟩
  | Opaque posts impl mods =>
    simp only [Pr', mapProcedureBodiesM, hb, run_bind1, run_pure1, procFrames]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by trivial, by trivial, .opq ?_ ?_ ?_, ?_⟩
    rotate_left 3
    · cases impl with
      | none => exact .nil
      | some b =>
        exact frames_trav hT hvn hk hvk mods (fun gr hgr => hmods gr (by simp [hb, bodyModifies, hgr])) _
    · exact condMapM_rel hvk _ (fun c hc => hpost c (by simp [hb, Body.postconditions, hc])) st
    · cases impl with
      | none => trivial
      | some b => exact .plain hret (expr_trav (himpl b (by simp [hb, Body.implementation])) _)
    · have hm := fun (st : σ) => mapM_rel_mem (R := fun (a b : ModifiesGroup) => a.targets.isEmpty = b.targets.isEmpty) mods
        (fun g_1 => do
          let targets' ← List.mapM (mapStmtExprM g) g_1.targets
          let guard' ← Option.mapM (mapStmtExprM g) g_1.guard
          pure ({ targets := targets', guard := guard', summary := g_1.summary } : ModifiesGroup))
        (fun x _ st => by
          simp only [run_bind1, run_pure1]
          exact (mapM_rel_mem (R := fun _ _ => True) x.targets (mapStmtExprM g) (fun _ _ _ => trivial) st
            |>.isEmpty_eq)) st
      refine L2.any_eq ?_
      exact (hm _).map_rel (fun a b hab => by simp only [hab])
  | Abstract posts =>
    simp only [Pr', mapProcedureBodiesM, hb, run_bind1, run_pure1, procFrames]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by trivial, by trivial, .abs (condMapM_rel hvk _ (fun c hc => hpost c (by simp [hb, Body.postconditions, hc])) st), .nil⟩
  | External =>
    simp only [Pr', mapProcedureBodiesM, hb, run_pure1, procFrames]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by trivial, by trivial, .external, .nil⟩

/-- Rewriting the specifications of a procedure `Pr` with `mapStmtExprM g` keeps its signature, body
and coroutine flag, and relates the old and new preconditions by `CondRel (TE (fun _ e => g e) P)`,
provided every precondition satisfies `Hered P` and the pass's `vok` hook is trivial. -/
theorem specs_trav (hvk : ∀ E a b, Reserved.vok E a b) {Pr : Procedure} (hpre : ∀ c ∈ Pr.preconditions, Hered P c.condition) (st : σ) :
    let Pr' := ((mapProcedureSpecificationsM (mapStmtExprM g) Pr).run st).1
    SameSig Pr Pr' ∧ Pr'.body = Pr.body ∧ L2 (CondRel (TE (fun _ e => g e) P)) Pr.preconditions Pr'.preconditions ∧
      Pr'.is_coroutine = Pr.is_coroutine := by
  intro Pr'
  simp only [Pr', mapProcedureSpecificationsM, mapProcedureSpecificationsWithM, run_bind1, run_pure1]
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by trivial, condMapM_rel hvk _ hpre st, ?_⟩
  simp only [Procedure.is_coroutine, Procedure.kind]
  cases Pr.contracts <;> rfl

/-- Rewriting every term of a procedure `Pr` with `mapProcedureM (mapStmtExprM g)` gives a procedure
related to `Pr` by `ProcRel (TE (fun _ e => g e) P)`. The hypotheses: `g` satisfies `TravOK`, the
pass has no return label, no valued return and trivial hooks, `Pr` satisfies `ProcOK (Hered P)`,
and every output that is also an input passes the pass's `inoutOK` check. -/
theorem proc_trav [TyEqC] (hT : TravOK g) (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e) {Pr : Procedure} (hP : ProcOK (Hered P) Pr) (st : σ)
    (hio : ∀ o ∈ Pr.outputs, Pr.inputs.any (·.name.text == o.name.text) = true → Reserved.inoutOK o.name.text := by
      intros; trivial) :
    ProcRel (TE (fun _ e => g e) P) Pr ((mapProcedureM (mapStmtExprM g) Pr).run st).1 := by
  have hte : TyEq := TyEqC.ok
  obtain ⟨hpre, himpl, hpost, hco, hout, hin, hmods⟩ := hP
  simp only [mapProcedureM, run_bind1]
  obtain ⟨hs1, hp1, hc1, hb1, hf1⟩ := bodies_trav (g := g) hT hvn hk hvk hret himpl hpost hmods st
  generalize ((mapProcedureBodiesM (mapStmtExprM g) Pr).run st) = r at hs1 hp1 hc1 hb1 hf1
  obtain ⟨hs2, hb2, hp2, hco2⟩ := specs_trav hvk (g := g) (Pr := r.1)
    (fun c hc => hpre c (by rw [← hp1]; exact hc)) r.2
  generalize ((mapProcedureSpecificationsM (mapStmtExprM g) r.1).run r.2).1 = q at hs2 hb2 hp2 hco2
  have hcoR : r.1.is_coroutine = false := by
    simp only [Procedure.is_coroutine, Procedure.kind, hc1] at hco ⊢; exact hco
  exact {
    name := .inl (hs1.name.trans hs2.name)
    inputs := by rw [← hs1.inputs.trans hs2.inputs]; exact ParamR.list hte _
    outputs := by rw [← hs1.outputs.trans hs2.outputs]; exact ParamR.list hte _
    pre := by rw [← hp1]; exact hp2
    coro := hco
    coro' := by rw [hco2]; exact hcoR
    body := by rw [hb2]; exact hb1
    writes := hs1.writes.trans hs2.writes
    throws := hs1.throws.trans hs2.throws
    throwsTy := fun _ _ => hte.refl _
    outNames := hout
    inNames := hin
    inV := fun _ _ => notV_none hvn _
    outV := fun _ _ => .inl (notV_none hvn _)
    preOK := fun _ _ => ovOK_none hvn _ _ hk
    postOK := fun _ _ => ovOK_none hvn _ _ hk
    bodyOK := fun _ _ => ovOK_none hvn _ _ hk
    nc := fun h => by rw [valued_none hvn] at h; cases h
    frames := by unfold procFrames; rw [hb2]; exact hf1
    inouts := hio }

theorem proc_trav_name (hT : TravOK g) (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e) {Pr : Procedure} (hP : ProcOK (Hered P) Pr) (st : σ) :
    Pr.name.text = ((mapProcedureM (mapStmtExprM g) Pr).run st).1.name.text := by
  obtain ⟨hpre, himpl, hpost, hco, hout, hin, hmods⟩ := hP
  simp only [mapProcedureM, run_bind1]
  obtain ⟨hs1, hp1, hc1, hb1, hf1⟩ := bodies_trav (g := g) hT hvn hk hvk hret himpl hpost hmods st
  generalize ((mapProcedureBodiesM (mapStmtExprM g) Pr).run st) = r at hs1 hp1 hc1 hb1 hf1
  obtain ⟨hs2, hb2, hp2, hco2⟩ := specs_trav hvk (g := g) (Pr := r.1)
    (fun c hc => hpre c (by rw [← hp1]; exact hc)) r.2
  generalize ((mapProcedureSpecificationsM (mapStmtExprM g) r.1).run r.2).1 = q at hs2 hb2 hp2 hco2
  rw [hs1.name.trans hs2.name]

theorem proc_trav_inputs (hT : TravOK g) (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e) {Pr : Procedure} (hP : ProcOK (Hered P) Pr) (st : σ) :
    Pr.inputs = ((mapProcedureM (mapStmtExprM g) Pr).run st).1.inputs := by
  obtain ⟨hpre, himpl, hpost, hco, hout, hin, hmods⟩ := hP
  simp only [mapProcedureM, run_bind1]
  obtain ⟨hs1, hp1, hc1, hb1, hf1⟩ := bodies_trav (g := g) hT hvn hk hvk hret himpl hpost hmods st
  generalize ((mapProcedureBodiesM (mapStmtExprM g) Pr).run st) = r at hs1 hp1 hc1 hb1 hf1
  obtain ⟨hs2, hb2, hp2, hco2⟩ := specs_trav hvk (g := g) (Pr := r.1)
    (fun c hc => hpre c (by rw [← hp1]; exact hc)) r.2
  generalize ((mapProcedureSpecificationsM (mapStmtExprM g) r.1).run r.2).1 = q at hs2 hb2 hp2 hco2
  rw [hs1.inputs.trans hs2.inputs]

def Phase1 (E : StmtExprMd → StmtExprMd → Prop) (t t1 : TypeDefinition) : Prop :=
  match t, t1 with
  | .Composite ct, .Composite ct1 =>
    ct1.name = ct.name ∧ ct1.extending = ct.extending ∧ ct1.fields = ct.fields ∧
      L2 (fun P P' => ProcRel E P P' ∧ P.name.text = P'.name.text ∧ P.inputs = P'.inputs)
        ct.instanceProcedures ct1.instanceProcedures
  | .Composite _, _ => False
  | t, t1 => t1 = t

omit [Reserved] in
theorem L2.mapM_compose {R1 : α → β → Prop} {R : α → γ → Prop} {l : List α} {l1 : List β}
    (h : L2 R1 l l1) (f : β → StateM σ γ) (hf : ∀ a b, R1 a b → ∀ st, R a ((f b).run st).1) (st : σ) :
    L2 R l ((l1.mapM f).run st).1 := by
  induction h generalizing st with
  | nil => exact .nil
  | cons hab _ ih =>
    simp only [List.mapM_cons, run_bind1, run_pure1]
    exact .cons (hf _ _ hab st) (ih _)

def IOK (Pr : Procedure) : Prop :=
  ∀ o ∈ Pr.outputs, Pr.inputs.any (·.name.text == o.name.text) = true → Reserved.inoutOK o.name.text

def InoutsOK (p : LaurelProgram) : Prop :=
  (∀ Pr ∈ p.staticProcedures, IOK Pr) ∧ (∀ Pr ∈ p.staticFunctions, IOK Pr) ∧
    ∀ ct, TypeDefinition.Composite ct ∈ p.types → ∀ Pr ∈ ct.instanceProcedures, IOK Pr

/-- Rewriting every term of a program with `mapLaurelProgramStmtExprM g` gives a program related to the
input by `ProgRel (TE (fun _ e => g e) P)`, given the pass's `Reserved.ixX` fact about the two
program indices. The other hypotheses: `g` satisfies `TravOK` and keeps literal values, the pass has
no return label, no valued return, trivial hooks and does not set `noGlobals`, types are related
only when equal (`TyEqC`), renamings point at procedures of `p` (`RenOK`), the program satisfies
`ProgOK (Hered P)`, and its in-out parameters are allowed (`InoutsOK`). -/
theorem prog_trav_ix {st : σ} (hT : TravOK g) (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e)
    (hng : ¬ Reserved.noGlobals)
    [TyEqC]
    {p : LaurelProgram} (hrok : RenOK p) (hp : ProgOK (Hered P) p)
    (hix : Reserved.ixX (TE (fun _ e => g e) P) (buildIndex p) (buildIndex ((mapLaurelProgramStmtExprM g p).run st).1))
    (hlit : ∀ w st, Hered P w → literalValue? ((mapStmtExprM g w).run st).1.val = literalValue? w.val)
    (hio : InoutsOK p := by exact ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial⟩) :
    ProgRel (TE (fun _ e => g e) P) p ((mapLaurelProgramStmtExprM g p).run st).1 := by
  obtain ⟨hprocs, htypes, hfields, hfuns, hcons⟩ := hp
  simp only [mapLaurelProgramStmtExprM, mapLaurelProgramProceduresM, run_bind1, run_pure1]
  simp only [mapLaurelProgramStmtExprM, mapLaurelProgramProceduresM, run_bind1, run_pure1] at hix
  refine ⟨?_, ?_, L2.nonAlias ?ht, fun h => absurd h hng, hrok,
    mapM_rel_mem _ _ (fun Pr hPr st => proc_trav hT hvk hret hvn hk (hfuns Pr hPr) st (hio.2.1 Pr hPr)) _, hix,
    (fun o h => by rw [hvn] at h; cases h), ?_, aliasOK_of TyEqC.ok ?ht, ?hf, fun _ _ => TyEqC.ok.refl _⟩
  case hf =>
    unfold HeapKeys
    exact (L2.map_eq_key (mapM_rel_mem (R := fun (a b : HeapField) => (a.name.text, a.location.text, a.type.val) = (b.name.text, b.location.text, b.type.val)) _ _
      (fun f _ st => by simp only [run_bind1, run_pure1]) _)).symm
  · exact ⟨_, [], (List.append_nil _).symm, mapM_rel_mem _ _ (fun Pr hPr st => proc_trav hT hvk hret hvn hk (hprocs Pr hPr) st (hio.1 Pr hPr)) _,
      fun _ h => by simp at h⟩
  · refine mapM_rel_mem _ _ (fun f hf st => ?_) _
    simp only [run_bind1, run_pure1]
    refine ⟨by trivial, TyEqC.ok.refl _, ?_, fun x _ => finP_none hvn x hk, fun _ _ _ _ => hvk _ _ _⟩
    cases hi : f.initializer with
    | none => simp only [Option.mapM, run_pure1]; trivial
    | some e => exact expr_trav (hfields f hf e hi) _
  case ht =>
    have h1 := fun st => mapM_rel_mem (R := fun t t1 => Phase1 (TE (fun _ e => g e) P) t t1 ∧ TypeOK (Hered P) t) p.types
      (fun td => match td with
        | .Composite ct => do
          let ps ← ct.instanceProcedures.mapM (mapProcedureM (mapStmtExprM g))
          pure (TypeDefinition.Composite { ct with instanceProcedures := ps })
        | other => pure other)
      (fun t ht st => by
        cases t with
        | Composite ct =>
          simp only [run_bind1, run_pure1, Phase1]
          exact ⟨⟨by trivial, by trivial, by trivial,
            mapM_rel_mem _ _ (fun Pr hPr st => ⟨proc_trav hT hvk hret hvn hk ((htypes _ ht).1 Pr hPr) st (hio.2.2 ct ht Pr hPr),
              proc_trav_name hT hvk hret hvn hk ((htypes _ ht).1 Pr hPr) st,
              proc_trav_inputs hT hvk hret hvn hk ((htypes _ ht).1 Pr hPr) st⟩) _⟩, htypes _ ht⟩
        | _ => simp only [run_pure1, Phase1]; exact ⟨trivial, htypes _ ht⟩) st
    refine L2.mapM_compose (h1 _) _ (fun a b ⟨hab, hok⟩ st => ?_) _
    rcases a with ct | c | dt | o | al <;> rcases b with ct1 | c1 | dt1 | o1 | al1 <;>
      simp only [Phase1, reduceCtorEq, TypeDefinition.Constrained.injEq, TypeDefinition.Datatype.injEq,
        TypeDefinition.Opaque.injEq, TypeDefinition.Alias.injEq] at hab
    · obtain ⟨hn, hx, hfl, hps⟩ := hab
      simp only [run_bind1, run_pure1]
      refine .composite ⟨hn.symm, hx.symm, ?_, fun _ => hps⟩
      rw [← hfl]
      refine mapM_rel_mem _ _ (fun f hf st => ?_) _
      simp only [run_bind1, run_pure1]
      refine ⟨by trivial, TyEqC.ok.refl _, ?_, fun x _ => finP_none hvn x hk, fun _ _ _ _ => hvk _ _ _⟩
      cases hi : f.initializer with
      | none => simp only [Option.mapM, run_pure1]; trivial
      | some e => exact expr_trav (hok.2 f (by rw [← hfl]; exact hf) e hi) _
    · subst hab
      simp only [run_bind1, run_pure1]
      exact .constrained ⟨rfl, TyEqC.ok.refl _, rfl, expr_trav hok.1 _, expr_trav hok.2.1 _, (hlit _ _ hok.2.1).symm, hok.2.2,
        notV_none hvn _, finP_none hvn _ hk, finP_none hvn _ hk, hvk _ _ _, hvk _ _ _⟩
    · subst hab; simp only [run_pure1]; exact .datatype (DtRel.refl TyEqC.ok _)
    · subst hab; simp only [run_pure1]; exact .opaque_ _
    · subst hab; simp only [run_pure1]; exact .alias _
  · refine ⟨_, [], (List.append_nil _).symm, mapM_rel_mem _ _ (fun c hc st => ?_) _, fun _ h => by simp at h⟩
    simp only [run_bind1, run_pure1]
    refine ⟨trivial, ?_, fun e _ => ovOK_none hvn _ _ hk, fun _ _ _ _ => hvk _ _ _⟩
    cases hi : c.initializer with
    | none => simp only [Option.mapM, run_pure1]; trivial
    | some e => exact expr_trav (hcons c hc e hi) _


/-- Rewriting every term of a program with `mapLaurelProgramStmtExprM g` gives a program related to the
input by `ProgRel (TE (fun _ e => g e) P)`. The hypotheses: `g` satisfies `TravOK` and keeps literal
values, the pass has no return label, no valued return, trivial hooks, an `ixX` relation that always
holds, and does not set `noGlobals`, types are related only when equal (`TyEqC`), renamings point at
procedures of `p` (`RenOK`), the program satisfies `ProgOK (Hered P)`, and its in-out parameters are
allowed (`InoutsOK`). -/
theorem prog_trav (hT : TravOK g) (hvk : ∀ E a b, Reserved.vok E a b) (hret : Reserved.retLabel = none) (hvn : Reserved.vret = none) (hk : ∀ G e, Reserved.nodeOK G e)
    (hix : ∀ E ix ix', Reserved.ixX E ix ix') (hng : ¬ Reserved.noGlobals)
    [TyEqC]
    {p : LaurelProgram} (hrok : RenOK p) (hp : ProgOK (Hered P) p)
    (hlit : ∀ w st, Hered P w → literalValue? ((mapStmtExprM g w).run st).1.val = literalValue? w.val)
    (st : σ)
    (hio : InoutsOK p := by exact ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial⟩) :
    ProgRel (TE (fun _ e => g e) P) p ((mapLaurelProgramStmtExprM g p).run st).1 :=
  prog_trav_ix hT hvk hret hvn hk hng hrok hp (hix _ _ _) hlit hio

end

end Strata.Laurel.PassSemantics

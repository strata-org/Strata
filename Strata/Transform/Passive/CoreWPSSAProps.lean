/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.CoreWPSSA
public import Strata.Transform.Passive.CoreProgramProps
public import Strata.Transform.WP.WPCoreProgramProps
public import Strata.Transform.SSA.SSACoreProgramProps
import all Strata.Transform.Passive.CoreProgramProps
import all Strata.Transform.WP.WPCoreProgramProps
import all Strata.Transform.SSA.SSACoreProgramProps
import Strata.Util.ExceptProps
import Strata.Languages.Core.ProcedureProps
import all Strata.Util.ListMap

/-! # Properties of the WP and SSA phases in sequence on Core procedures and programs

Key theorems: `wpSSAProgramWith_contractFree` (every procedure of the obligation program has an
empty contract), `wpSSALoopFree_ok` (what a successful run of both phases on one loop-free list
computes), `wpSSAProgramWith_lemma` (each lemma of a program has the obligation unit of its
obligation in the obligation program), `wpSSALoopFree_hal` (with the values of `old x` in place,
the entry aliases hold the values of the names they alias), `wpSSALoopFree_checks` (a
successful run discharges the syntactic hypotheses on the loop-free list). -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP

public section

/-! ## Fresh names and the entry renaming -/

/-- The current name of `x` under `ρ` is `x` itself, `x` being renamed by no pair of `ρ`, or
    it is the target of a pair of `ρ` renaming `x`. -/
private theorem ren_get_cases (ρ : Ren Expression) (x : Expression.Ident) :
    (ρ.get x = x ∧ x ∉ ρ.map Prod.fst) ∨ ∃ q ∈ ρ, q.1 = x ∧ ρ.get x = q.2 := by
  induction ρ <;> grind [Ren.get]

/-- **A successful run of both phases on a loop-free list** `ss` of `p`: the WP phase succeeds
    (`wpLoopFree`, after `checkLoopFree`) with `w`, and the SSA phase on its guarded program
    (`ssaLoopFree`) with the entry renaming `ρ0` and the output `so`. -/
theorem wpSSALoopFree_ok {Gw Gs : IdSet Expression} {p : Procedure} {ss : Statements}
    {w : WOut Expression} {ρ0 : Ren Expression} {so : SOut Expression}
    (h : wpSSALoopFree Gw Gs p ss = .ok (w, ρ0, so)) :
    wpLoopFree Gw p ss = .ok w ∧ checkLoopFree p ss = .ok () ∧
      ssaLoopFree Gs p w.lay = .ok (ρ0, so) := by
  grind [wpSSALoopFree, wpLoopFree, Except.bind_is_ok, Except.pure_is_ok]

/-! ## Aliasing at entry from the values of `old x`

The entry renaming gives distinct names to distinct variables, except that `old x` of an in-out
parameter `x` shares the name of `x`.  So two variables with the same entry name hold the same
value when, in the procedure's store, `old x` holds the value of `x` for each in-out
parameter `x`. -/

/-- The current name of `w` after renaming `x` to `y` is `y` when `w` is `x`, and its current
    name before otherwise. -/
private theorem get_set (ρ : Ren Expression) (x y w : Expression.Ident) :
    (ρ.set x y).get w = if w = x then y else ρ.get w := by
  grind [Ren.set, Ren.get]

/-- Renaming each `a` of `al` to the entry name of its `x`, for each `(a, x)` of `al` (each `x`
    in the class `D` and `a` holding its value in `σ`), keeps the property that two variables of
    `D` with the same entry name hold the same value. -/
private theorem aliasFold_val {σ : SemanticStore Expression} (D : Expression.Ident → Prop) :
    ∀ (al : List (Expression.Ident × Expression.Ident)), (∀ q ∈ al, D q.2 ∧ σ q.1 = σ q.2) →
      ∀ ρ : Ren Expression, (∀ x y, D x → D y → ρ.get x = ρ.get y → σ x = σ y) →
      ∀ x y, D x → D y →
        (al.foldl (fun (ρ : Ren Expression) (q : Expression.Ident × Expression.Ident) =>
          Ren.set ρ q.1 (Ren.get ρ q.2)) ρ).get x =
          (al.foldl (fun (ρ : Ren Expression) (q : Expression.Ident × Expression.Ident) =>
            Ren.set ρ q.1 (Ren.get ρ q.2)) ρ).get y →
        σ x = σ y
  | [], _, _, hρ => hρ
  | (a, z) :: l, hl, ρ, hρ => aliasFold_val D l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _
    fun x y hx hy he => by grind [get_set, hl (a, z) List.mem_cons_self]

/-- Renaming each variable of `l` to a fresh name (`f`, from the counter `n`, not satisfying the
    avoidance predicate `Av`) keeps the renaming injective on the variables it renames and on
    those avoided or not of the form of an introduced name, and renames every variable of `l`. -/
private theorem freshFold_inj {τ : Type} (Av : Expression.Ident → Prop) (c : τ → Nat)
    (I : τ → Prop) (f : Ren Expression × τ → Expression.Ident → Ren Expression × τ)
    (hf : ∀ ρ s x, I s → ∃ k, c s ≤ k ∧ (f (ρ, s) x).1 = Ren.set ρ x (freshName x.name k) ∧
      c (f (ρ, s) x).2 = k + 1 ∧ I (f (ρ, s) x).2 ∧ ¬Av (freshName x.name k)) :
    ∀ (l : List Expression.Ident) (ρ : Ren Expression) (s : τ), I s →
      (∀ q ∈ ρ, ∃ b j, j < c s ∧ q.2 = freshName b j ∧ ¬Av q.2) →
      (∀ x y, ((Av x ∨ ∀ b n, x ≠ freshName b n) ∨ x ∈ ρ.map Prod.fst) →
        ((Av y ∨ ∀ b n, y ≠ freshName b n) ∨ y ∈ ρ.map Prod.fst) →
        ρ.get x = ρ.get y → x = y) →
      (∀ x y, ((Av x ∨ ∀ b n, x ≠ freshName b n) ∨
          x ∈ (l.foldl f (ρ, s)).1.map Prod.fst) →
        ((Av y ∨ ∀ b n, y ≠ freshName b n) ∨
          y ∈ (l.foldl f (ρ, s)).1.map Prod.fst) →
        (l.foldl f (ρ, s)).1.get x = (l.foldl f (ρ, s)).1.get y → x = y) ∧
        ∀ x, x ∈ l ∨ x ∈ ρ.map Prod.fst → x ∈ (l.foldl f (ρ, s)).1.map Prod.fst
  | [], _, _, _, _, hinj => ⟨hinj, fun _ hx => hx.resolve_left nofun⟩
  | z :: l, ρ, s, hs, hρ, hinj => by
    obtain ⟨j, hj, he, hc, hI, hav⟩ := hf ρ s z hs
    have hne : ∀ w, ((Av w ∨ ∀ b n, w ≠ freshName b n) ∨ w ∈ ρ.map Prod.fst) →
        w ≠ z → ρ.get w ≠ freshName z.name j := fun w hw _ hw' => by
      rcases ren_get_cases ρ w with ⟨hg, hn⟩ | ⟨q, hq, -, hg⟩
      · grind
      · obtain ⟨b, j', hj', hq2, -⟩ := hρ q hq
        exact absurd (freshName_counter_inj (P := Expression) (hq2 ▸ hg ▸ hw').symm) (by omega)
    obtain ⟨ih1, ih2⟩ := freshFold_inj Av c I f hf l (f (ρ, s) z).1 (f (ρ, s) z).2 hI
      (by grind [Ren.set]) fun x y hx hy he => by grind [get_set, Ren.set]
    exact ⟨ih1, fun x hx => ih2 x (by grind [Ren.set])⟩

/-- **The aliasing hypothesis from the values of `old x`.**  When `wpSSALoopFree Gw Gs p ss`
    succeeds with entry renaming `ρ0`, `σ` gives `old x` the value of `x` for each in-out
    parameter `x` of `p`, and every in-scope variable of `S` of the form of an introduced name is
    a parameter, two variables of `S` that `ρ0` maps to the same name hold the same value in `σ`. -/
theorem wpSSALoopFree_hal {Gw Gs : IdSet Expression} {p : Procedure}
    {ss : Statements} {w : WOut Expression} {ρ0 : Ren Expression} {so : SOut Expression}
    (h : wpSSALoopFree Gw Gs p ss = .ok (w, ρ0, so))
    {S V : List Expression.Ident}
    (hSI : ∀ x ∈ S, ∀ b n, x = freshName b n → x ∈ p.paramTys.map (·.1))
    {σ : SemanticStore Expression}
    (hold : ∀ x ∈ p.header.getInoutParams.map (·.1), σ (CoreIdent.mkOld x.name) = σ x) :
    ∀ x ∈ S, x ∈ V → ∀ y ∈ S, y ∈ V → ρ0.get x = ρ0.get y → σ x = σ y := by
  obtain ⟨rfl, -⟩ := ssaEntry_ok (wpSSALoopFree_ok h).2.2
  have hD : ∀ x ∈ S, ((inputAvoid Gs p.paramTys w.lay).contains x = true ∨
      ∀ b n, x ≠ freshName b n) := fun x hx => by
    grind [inputAvoid, AvoidSet.contains, IdSet.ofList, hSI x hx]
  intro x hx _ y hy _ he
  obtain ⟨hinj, hdom⟩ := freshFold_inj (fun x => (inputAvoid Gs p.paramTys w.lay).contains x)
    id (fun _ => True) (fun (r : Ren Expression × Nat) (x : Expression.Ident) =>
      let f := freshIn (inputAvoid Gs p.paramTys w.lay) (WPOps.name x) r.2
      (Ren.set r.1 x f.1, f.2))
    (fun ρ n x _ => (freshIn_spec (P := Expression) _ _ n).imp fun _ ⟨he, hk, hA⟩ => ⟨hk,
      congrArg (Ren.set ρ x ·.1) he, congrArg (·.2) he, trivial, Bool.eq_false_iff.1 hA⟩) _ [] 0
    trivial nofun fun x y _ _ h => by simpa [Ren.get] using h
  exact aliasFold_val _ p.oldAliases (fun q hq => ⟨.inr (hdom q.2 (.inl
      (Procedure.oldAliases_mem p q hq))), by grind [Procedure.oldAliases]⟩) _
    (fun x y hx hy he => congrArg σ (hinj x y hx hy he)) x y (.inl (hD x hx)) (.inl (hD y hy)) he

/-! ## Syntactic hypotheses from a successful run

Both phases succeed only on loop-free lists that pass `checkLoopFree`, so with the variables of
`p.entryScope` (the parameters and `old x` of the in-out parameters) in scope and the assigned
variables of the list as locals, the list is well scoped (`Block.WellScoped`) and reads only
variables in scope. -/

/-- **What a successful run guarantees of its input.**  When `wpSSALoopFree Gw Gs p ss`
    succeeds, `ss` is well scoped from `p.entryScope` with its assigned variables as locals
    (`Block.WellScoped`) and reads only variables of `p.entryScope`. -/
theorem wpSSALoopFree_checks {Gw Gs : IdSet Expression} {p : Procedure}
    {ss : Statements} {w : WOut Expression} {ρ0 : Ren Expression} {so : SOut Expression}
    (h : wpSSALoopFree Gw Gs p ss = .ok (w, ρ0, so)) :
    Block.WellScoped (Block.assignedVars ss) p.entryScope ss ∧
      ∀ x ∈ Block.freeVars ss, x ∈ p.entryScope :=
  let ⟨hfv, hwfl, _⟩ := checkLoopFree_ok (wpSSALoopFree_ok h).2.1
  ⟨hwfl, hfv⟩

/-! ## Programs

What a successful run of the program-level phases contains: one obligation unit per lemma
(`declObligationsProgramWith`), kept by the WP phase (`wpProcsProgram`), then one obligation
procedure per procedure (`ssaProc`, same name). -/

/-- **The obligation program is contract-free**: every procedure of the SSA phase's output is
    an obligation procedure, with an empty contract, so its loop-free statement list is its body
    (`contractWrapped_emptySpec`). -/
theorem wpSSAProgramWith_contractFree {reserved : List Expression.Ident}
    {declProgram program out : Program}
    {lemmaObls : List (Imperative.ProofObligation Expression)}
    (h : wpSSAProgramWith reserved declProgram lemmaObls program = .ok out) :
    Program.noProcedureContracts out = true := by
  simp only [wpSSAProgramWith, ssaProgram, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨mid, -, decls, hm, rfl⟩ := h
  refine List.all_eq_true.2 fun d' hd' => ?_
  suffices ∀ q md, d' = .proc q md → q.spec.preconditions = [] ∧ q.spec.postconditions = [] by
    cases d' <;> simp_all [ListMap.isEmpty]
  rintro q md rfl
  obtain ⟨d, -, hd⟩ := mapM_except_mem_right _ _ _ hm _ hd'
  split at hd <;> grind [ssaProc, Decl.obligationProc, Except.bind_is_ok, Except.pure_is_ok,
    Except.throw_is_ok]

/-! ## Lemmas

The SSA phase keeps the obligation unit of each lemma: it has no parameter, and its obligation
reads no renamed name. -/

/-- **Each lemma keeps its obligation.**  Let `wpSSAProgramWith reserved declProgram lemmaObls
    program` succeed with `out`, and let `l` be a lemma of `program`.  Then `out` contains the
    obligation unit (`lemmaUnit`) of an obligation of `lemmaObls` labelled with `l`'s name. -/
theorem wpSSAProgramWith_lemma {reserved : List Expression.Ident}
    {declProgram program out : Program}
    {lemmaObls : List (Imperative.ProofObligation Expression)}
    (h : wpSSAProgramWith reserved declProgram lemmaObls program = .ok out)
    {l : Lemma} {md : Imperative.MetaData Expression} (hl : Decl.lemma l md ∈ program.decls) :
    ∃ ob ∈ lemmaObls, ob.label = l.name ∧ lemmaUnit l.name ob ∈ out.decls := by
  obtain ⟨mid, hm, hs⟩ := (Except.bind_is_ok _ _ _).1 h
  obtain ⟨dp, hd, hw⟩ := (Except.bind_is_ok _ _ _).1 hm
  obtain ⟨ob, hob, hlb, hu⟩ := declObligationsProgramWith_lemma hd l md hl
  have hu' := wpProcsProgram_unit hw _ _ hu
    (by unfold ProofObligation.toCheckCmd; split <;> simp [isObligationUnit])
  obtain ⟨d, hd, hdo⟩ := ssaProgram_mem hs _ _ hu'
  exact ⟨ob, hob, hlb, Except.ok.inj ((ssaProc_lemmaUnit _ _ _ rfl).symm.trans hd) ▸ hdo⟩

end -- public section
end WP
end Core

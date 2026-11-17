/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.ProgTrav
import StrataLaurel.Implementation.EliminateDoWhile
import StrataLaurel.PassSemantics.EntryAt
import StrataLaurel.PassSemantics.Landing

/-!
# Correctness of `EliminateDoWhile`

This file proves that `eliminateDoWhilePass` preserves the meaning of programs. The pass
replaces each post-test loop `do body while c` by a block labelled `L` that contains
`while true { body; if !c then exit L }`. The proof instantiates `PassRel` with `K = 6`
(`dw_rel`) and applies `entry_sim` and `procAt_all`.

* `eliminateDoWhilePass_correct`: for a whole-program run, running the pass's output with
  6 times the fuel ends with the same outcome and the same number of failed checks as
  running the input, unless the input gets stuck. The interpreter runs without a step
  budget (`limitSteps = false`).
* `eliminateDoWhilePass_procAt`: the same for a run that starts at any static procedure of
  the input, compared with the corresponding procedure of the output.
* `PDW`: what every term of the input must satisfy: `Basic`, no exit to a label starting
  with `$dowhile_exit_`, and every post-test loop body is a block.
* `E`, `Rw`, `target`: the term relation, the rewrite step and the rewritten loop.
* `hext_default`: the default backend satisfies the hypothesis on `externalTruthy`.
-/

namespace Strata.Laurel.PassSemantics.DoWhileSim

open Strata.Laurel
open Strata.Laurel.Interpreter

local instance : Reserved := Reserved.none (fun l => "$dowhile_exit_".isPrefixOf l)

variable {G : StackFrame} {ol : List String}
open EliminateDoWhile

def Gl (l : String) : Prop := ¬ "$dowhile_exit_".isPrefixOf l

def BlockBody (e : StmtExprMd) : Prop :=
  ∀ c invs dec body, e.val = .While c invs dec body true → ∃ ss lab, body.val = .Block ss lab [] none

def PDW (e : StmtExprMd) : Prop := Basic e ∧ ExitOK Gl e ∧ BlockBody e

abbrev fDW : Bool → StmtExprMd → ElimM StmtExprMd := fun _ e => rewriteNode e

abbrev E : StmtExprMd → StmtExprMd → Prop := TE fDW PDW

def notC (c : StmtExprMd) (src : FileRange) : StmtExprMd :=
  ⟨.Call none (mkId Operation.Not.procName) [c] [], src⟩
def exitL (src : FileRange) (L : String) : StmtExprMd := ⟨.Goto L .blockEnd, src⟩
def guard (c : StmtExprMd) (src : FileRange) (L : String) : StmtExprMd :=
  ⟨.IfThenElse (notC c src) (exitL src L) none, src⟩
def trueE (src : FileRange) : StmtExprMd := ⟨.LiteralBool true, src⟩
def loopBody (c body : StmtExprMd) (src : FileRange) (L : String) : StmtExprMd :=
  ⟨.Block [body, guard c src L] none [] none, src⟩
def loopW (c : StmtExprMd) (invs : List StmtExprMd) (dec : Option StmtExprMd) (body : StmtExprMd)
    (src : FileRange) (L : String) : StmtExprMd :=
  ⟨.While (trueE src) invs dec (loopBody c body src L) false, src⟩
def target (c : StmtExprMd) (invs : List StmtExprMd) (dec : Option StmtExprMd) (body : StmtExprMd)
    (src : FileRange) (L : String) : StmtExprMd :=
  ⟨.Block [loopW c invs dec body src L] (some L) [] none, src⟩

private theorem rewriteNode_while (c : StmtExprMd) (invs : List StmtExprMd) (dec : Option StmtExprMd)
    (body : StmtExprMd) (src : FileRange) (st : ElimState) :
    ((rewriteNode ⟨.While c invs dec body true, src⟩).run st).1 =
      target c invs dec body src s!"$dowhile_exit_{st.freshCounter}" := rfl

def Rw (s t : StmtExprMd) : Prop :=
  ∃ c invs dec body src c' invs' dec' body' src' L,
    s = ⟨.While c invs dec body true, src⟩ ∧ t = target c' invs' dec' body' src' L ∧
    E c c' ∧ L2 E invs invs' ∧ E body body' ∧ "$dowhile_exit_".isPrefixOf L ∧
    (∃ ss lab, body.val = .Block ss lab [] none) ∧ (∃ ss lab, body'.val = .Block ss lab [] none)

private theorem rewriteNode_notYield (u : Bool) (r : StmtExprMd) (st : ElimState) (h : NotYield r) :
    NotYield ((fDW u r).run st).1 := by
  unfold fDW rewriteNode
  split
  · simp [NotYield, StateT.run, bind, StateT.bind, freshExitLabel, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure]
  · exact h

private theorem sl_while (c : StmtExprMd) (invs : List StmtExprMd) (dec : Option StmtExprMd) (body : StmtExprMd)
    (pt : Bool) (src : FileRange) : statementLabels ⟨.While c invs dec body pt, src⟩ = [] :=
  statementLabels_other _ _ (by intros; nofun) (by intros; nofun)

private theorem target_labels (c : StmtExprMd) (invs : List StmtExprMd) (dec : Option StmtExprMd) (body : StmtExprMd)
    (src : FileRange) (L : String) : statementLabels (target c invs dec body src L) = [L] := by
  simp [target, loopW, statementLabels_block, sl_while]

private theorem rewriteNode_other (r : StmtExprMd) (st : ElimState)
    (h : ∀ c invs dec body, r.val ≠ .While c invs dec body true) : ((rewriteNode r).run st).1 = r := by
  unfold rewriteNode
  split
  · rename_i c invs dec body heq
    exact absurd heq (h c invs dec body)
  · rfl

private theorem rewriteNode_labels (u : Bool) (r : StmtExprMd) (st : ElimState) (l : String)
    (hl : ¬ "$dowhile_exit_".isPrefixOf l) :
    (l ∈ statementLabels ((fDW u r).run st).1 ↔ l ∈ statementLabels r) := by
  show l ∈ statementLabels ((rewriteNode r).run st).1 ↔ _
  by_cases hw : ∃ c invs dec body, r.val = .While c invs dec body true
  · obtain ⟨c, invs, dec, body, hv⟩ := hw
    rcases r with ⟨v, src⟩
    dsimp only at hv
    subst hv
    rw [rewriteNode_while, target_labels, sl_while]
    simp only [List.mem_singleton, List.not_mem_nil, iff_false]
    rintro rfl
    exact hl (by
      simp only [String.isPrefixOf, Nat.toString_eq_repr, String.startsWith_string_iff, String.reduceToList,
        String.toList_append, Nat.toList_repr, ↓Char.isValue]
      exact List.prefix_append _ _)
  · rw [rewriteNode_other _ _ (fun c invs dec body h => hw ⟨c, invs, dec, body, h⟩)]

private theorem shape_while_true {s r : StmtExprMd} (h : Shape E s r) {c invs dec body}
    (hr : r.val = .While c invs dec body true) : ∃ c invs dec body, s.val = .While c invs dec body true := by
  cases h <;> simp_all [Unsup]

/-- The traversal keeps a do-while body a block: if `body` is related to `body'` by `E` and `body` is a
block with no invariants and no decreases clause, then so is `body'`. -/
private theorem block_out {body body' : StmtExprMd} (h : E body body') (hb : ∃ ss lab, body.val = .Block ss lab [] none) :
    ∃ ss lab, body'.val = .Block ss lab [] none := by
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape (f := fDW) (fun e he => he.1) (fun e _ => namesOK_none e) rewriteNode_notYield u body st hs
  rw [heq]
  obtain ⟨ss, lab, hv⟩ := hb
  rcases body with ⟨v, src⟩
  dsimp only at hv
  subst hv
  cases hsh with
  | block _ =>
    rw [rewriteNode_other _ _ (fun _ _ _ _ h => by cases h)]
    exact ⟨_, _, rfl⟩
  | unsup hu _ => simp [Unsup] at hu

/-- The term relation `E` of `EliminateDoWhile` is closed under `NR E Rw Gl`: a term and its traversal
result either have the same shape with allowed exits and related value children, or the term is a
post-test loop and the result is its rewrite (`Rw`). -/
private theorem closed (s t : StmtExprMd) (h : E s t) : NR E Rw Gl s t := by
  have h0 := h
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape (f := fDW) (fun e he => he.1) (fun e _ => namesOK_none e) rewriteNode_notYield u s st hs
  rw [heq]
  by_cases hw : ∃ c invs dec body, s.val = .While c invs dec body true
  · obtain ⟨c, invs, dec, body, hv⟩ := hw
    rcases s with ⟨v, src⟩
    dsimp only at hv
    subst hv
    have hbb := hs.here.2.2 c invs dec body rfl
    cases hsh with
    | @while_ _ c' _ b' _ is' _ d' _ _ src' hc his hb =>
      right
      refine ⟨c, invs, dec, body, src, c', is', d', b', src', _, rfl, rewriteNode_while _ _ _ _ _ _,
        hc, his, hb, ?_, hbb, block_out hb hbb⟩
      simp only [String.isPrefixOf, Nat.toString_eq_repr, String.startsWith_string_iff, String.reduceToList, String.toList_append, Nat.toList_repr, ↓Char.isValue]
      exact List.prefix_append _ _
    | unsup hu _ => simp [Unsup] at hu
  · left
    rw [rewriteNode_other _ _ (fun c invs dec body hr => hw (shape_while_true hsh hr))]
    exact ⟨hsh, hs.here.2.1, valKids_triv (fun _ _ => trivial) (fun _ _ => trivial) hsh⟩


/-- Every pair of terms related by `E` holds the same statement-position labels that are not reserved. -/
private theorem labE (s t : StmtExprMd) (h : E s t) (l : String) (hl : ¬ "$dowhile_exit_".isPrefixOf l) :
    (l ∈ statementLabels s ↔ l ∈ statementLabels t) := by
  obtain ⟨⟨u, st, rfl⟩, hs⟩ := h
  exact (trav_labels (f := fDW) (P := PDW) (fun e he => he.1) (fun e _ => namesOK_none e) rewriteNode_notYield
    (fun u r st l hl => rewriteNode_labels u r st l hl) (fun l hl a ts h => h.elim) l hl s u st hs).symm

/-- A rewrite step of `EliminateDoWhile` holds only reserved labels and neither side is a stack annotation. -/
private theorem rwLab (s t : StmtExprMd) (hrw : Rw s t) :
    (∀ l, ¬ "$dowhile_exit_".isPrefixOf l → l ∉ statementLabels s ∧ l ∉ statementLabels t) ∧
      (stackAnnotation? s).isNone = true ∧ (stackAnnotation? t).isNone = true := by
  obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, -, -, -, hL, -⟩ := hrw
  refine ⟨fun l hl => ⟨by simp [sl_while], ?_⟩, by simp [stackAnnotation?], by simp [target, stackAnnotation?]⟩
  rw [target_labels]
  simp only [List.mem_singleton]
  rintro rfl
  exact hl hL

/-- For a term `w` with `Hered PDW w`, the traversal's result is a term `r` with `Shape E w r`, or the
rewritten loop `target c invs dec body src L` when `r` is a post-test loop
`While c invs dec body true`. -/
private theorem trav_out {u : Bool} {w : StmtExprMd} {st : ElimState} (hw : Hered PDW w) :
    ∃ r, Shape E w r ∧ (((mapStmtExprUsedM fDW u w).run st).1 = r ∨
      ∃ c invs dec body src L, r.val = .While c invs dec body true ∧
        ((mapStmtExprUsedM fDW u w).run st).1 = target c invs dec body src L) := by
  obtain ⟨r, st1, heq, hsh⟩ := trav_shape (f := fDW) (fun e he => he.1) (fun e _ => namesOK_none e) rewriteNode_notYield u w st hw
  refine ⟨r, hsh, ?_⟩
  rw [heq]
  by_cases hr : ∃ c invs dec body, r.val = .While c invs dec body true
  · obtain ⟨c, invs, dec, body, hv⟩ := hr
    right
    rcases r with ⟨v, src⟩
    dsimp only at hv
    subst hv
    exact ⟨c, invs, dec, body, src, _, rfl, rewriteNode_while _ _ _ _ _ _⟩
  · left
    exact rewriteNode_other _ _ (fun c invs dec body h => hr ⟨c, invs, dec, body, h⟩)

private theorem trav_lit_iff {a a' : StmtExprMd} (h : E a a') :
    (∀ n, a.val = .LiteralInt n ↔ a'.val = .LiteralInt n) ∧
      (∀ d, a.val = .LiteralDecimal d ↔ a'.val = .LiteralDecimal d) := by
  obtain ⟨⟨u, st, rfl⟩, hw⟩ := h
  obtain ⟨r, hsh, hout | ⟨c, invs, dec, body, src, L, hv, hout⟩⟩ := trav_out (u := u) (st := st) hw
  · rw [hout]
    cases hsh
    case unsup hu hu' =>
      exact ⟨fun n => ⟨fun h => by dsimp only at h; subst h; simp [Unsup] at hu,
          fun h => by dsimp only at h; subst h; simp [Unsup] at hu'⟩,
        fun d => ⟨fun h => by dsimp only at h; subst h; simp [Unsup] at hu,
          fun h => by dsimp only at h; subst h; simp [Unsup] at hu'⟩⟩
    all_goals simp_all
  · rw [hout]
    cases hsh
    case unsup hu hu' => dsimp only at hv; subst hv; simp [Unsup] at hu'
    all_goals simp_all [target]

/-- `EliminateDoWhile` keeps literal values: for every term `w` with `Hered PDW w`, the rewritten term has
the same `literalValue?` as `w`. -/
private theorem dw_lit (w : StmtExprMd) (st : ElimState) (hw : Hered PDW w) :
    literalValue? ((mapStmtExprM rewriteNode w).run st).1.val = literalValue? w.val := by
  obtain ⟨r, hsh, hout | ⟨c, invs, dec, body, src, L, hv, hout⟩⟩ := trav_out (u := false) (st := st) hw
  · show literalValue? ((mapStmtExprUsedM fDW false w).run st).1.val = _
    rw [hout]
    cases hsh with
    | @call f f' as as' ta ta' _ _ has hta hcr =>
      obtain ⟨rfl, -⟩ := hcr.resolve_right (fun h => h)
      rcases has with _ | ⟨ha, _ | ⟨hb, hr⟩⟩
      · rfl
      · rename_i a a'
        have ⟨hi, hd⟩ := trav_lit_iff ha
        rcases a with ⟨av, asrc⟩
        rcases a' with ⟨av', asrc'⟩
        dsimp only at hi hd
        cases av <;> cases av' <;> first
          | rfl
          | (have e := (hi _).mp rfl; simp only [StmtExpr.LiteralInt.injEq] at e; subst e; rfl)
          | (have e := (hd _).mp rfl; simp only [StmtExpr.LiteralDecimal.injEq] at e; subst e; rfl)
          | simp_all
      · simp only [literalValue_two]
    | unsup hu hu' => rename_i v v' _ _; cases v <;> simp [Unsup] at hu <;> cases v' <;> simp [Unsup] at hu' <;> rfl
    | _ => rfl
  · show literalValue? ((mapStmtExprUsedM fDW false w).run st).1.val = _
    rw [hout]
    cases hsh
    case unsup hu hu' => dsimp only at hv; subst hv; simp [Unsup] at hu'
    all_goals simp_all [literalValue?, target]


section Catch
variable {h : Control → EvalM PM Unit} (hh : ∀ c, CtlOK Gl G c → h c = throw c)
include hh

omit hh in
private theorem run_tryCatch_bind' (a : EvalM PM α) (f : α → EvalM PM Unit) (σ : EvalState) (τ : Trace) :
    run (tryCatch (a >>= f) h) σ τ = match run a σ τ with
      | .error e => .error e
      | .ok ((.error c, σ1), τ1) => run (h c) σ1 τ1
      | .ok ((.ok v, σ1), τ1) => run (tryCatch (f v) h) σ1 τ1 := by
  rw [run_tryCatch, run_bind]
  rcases run a σ τ with e | ⟨⟨c | v, σ1⟩, τ1⟩
  · rfl
  · rfl
  · exact (run_tryCatch _ _ _ _).symm

private theorem fsc_bind {x a : EvalM PM α} {g f : α → EvalM PM Unit} (hx : FS (SmO E Gl G ol) Eq x a)
    (hg : ∀ v, FS (SmO E Gl G ol) Eq (g v) (tryCatch (f v) h)) :
    FS (SmO E Gl G ol) Eq (x >>= g) (tryCatch (a >>= f) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht (not_oof_bind hn)
  rw [run_tryCatch_bind']
  rw [run_bind] at hn ⊢
  rcases r : run x σ τ with e | ⟨⟨c | v, σ1⟩, τ1⟩ <;>
    rcases r' : run a σ' τ' with e' | ⟨⟨c' | v', σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;> rw [r] at hn <;>
    simp only [RR, ExRel, false_and] at h0
  all_goals try (first | exact h0 | exact RR.ofStuck h0 _)
  · obtain ⟨hsg, ht1⟩ := h0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (fun v => SmO.noWin (not_free_none rfl _) v)
    rcases CtlR.eq hcr with rfl | ⟨_, _, rfl, rfl⟩
    · dsimp only
      rw [hh c hok, run_throw]
      exact ⟨.inl ⟨.inl rfl, hok, hs1⟩, ht1⟩
    · dsimp only
      rw [hh (.refused _) trivial, run_throw]
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, hs1⟩, ht1⟩
  · obtain ⟨rfl, hs1, ht1⟩ := h0
    exact (hg v).sim σ1 σ1' τ1 τ1' hs1 ht1 hn

private theorem fsc_lift {x y : EvalM PM Unit} (hx : FS (SmO E Gl G ol) Eq x y) :
    FS (SmO E Gl G ol) Eq x (tryCatch y h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have h0 := hx.sim σ σ' τ τ' hs ht hn
  rw [run_tryCatch]
  rcases r : run x σ τ with e | ⟨⟨c | v, σ1⟩, τ1⟩ <;>
    rcases r' : run y σ' τ' with e' | ⟨⟨c' | v', σ1'⟩, τ1'⟩ <;> rw [r, r'] at h0 <;>
    simp only [RR, ExRel, false_and] at h0
  all_goals try (first | exact h0 | exact RR.ofStuck h0 _)
  · obtain ⟨hsg, ht1⟩ := h0
    obtain ⟨hcr, hok, hs1⟩ := hsg.same (fun v => SmO.noWin (not_free_none rfl _) v)
    rcases CtlR.eq hcr with rfl | ⟨_, _, rfl, rfl⟩
    · dsimp only
      rw [hh c hok, run_throw]
      exact ⟨.inl ⟨.inl rfl, hok, hs1⟩, ht1⟩
    · dsimp only
      rw [hh (.refused _) trivial, run_throw]
      exact ⟨.inl ⟨.inr (.inr ⟨_, _, rfl, rfl⟩), hok, hs1⟩, ht1⟩
  · dsimp only
    exact ⟨by cases v; cases v'; rfl, h0.2⟩

omit hh in
private theorem fsc_get_r {x : EvalM PM Unit} {f : EvalState → EvalM PM Unit}
    (hf : ∀ s, s.coroSelf = none → s.steps = none → FS (SmO E Gl G ol) Eq x (tryCatch (f s) h)) :
    FS (SmO E Gl G ol) Eq x (tryCatch (get >>= f) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_tryCatch_bind', run_get]
  exact (hf σ' hs'.coroSelf' hs'.steps').sim σ σ' τ τ' hs ht hn

omit hh in
private theorem fsc_modify_r {x : EvalM PM Unit} {g : EvalState → EvalState} {f : PUnit → EvalM PM Unit}
    (hg : ∀ σ σ', (SmO E Gl G ol).st σ σ' → (SmO E Gl G ol).st σ (g σ'))
    (hf : FS (SmO E Gl G ol) Eq x (tryCatch (f ()) h)) :
    FS (SmO E Gl G ol) Eq x (tryCatch (modify g >>= f) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_tryCatch_bind', run_modify]
  exact hf.sim σ (g σ') τ τ' (hg σ σ' hs) ht hn

omit hh in
private theorem fsc_wow_r {x : EvalM PM Unit} {t : StmtExprMd} {y : EvalM PM β} {f : β → EvalM PM Unit}
    (hf : FS (SmO E Gl G ol) Eq x (tryCatch (y >>= f) h)) :
    FS (SmO E Gl G ol) Eq x (tryCatch (withOperandWindow t y >>= f) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_tryCatch_bind', run_wow_nil hs'.ops', ← run_tryCatch_bind']
  exact hf.sim σ σ' τ τ' hs ht hn

omit hh in
private theorem fsc_pure_r {x : EvalM PM Unit} {a : α} {f : α → EvalM PM Unit}
    (hf : FS (SmO E Gl G ol) Eq x (tryCatch (f a) h)) :
    FS (SmO E Gl G ol) Eq x (tryCatch (pure a >>= f) h) := by
  simpa only [pure_bind] using hf

end Catch

private theorem fs_get_l {g : EvalState → EvalM PM α} {y : EvalM PM α}
    (hg : ∀ s, s.coroSelf = none → s.steps = none → s.seek = none → FS (SmO E Gl G ol) Eq (g s) y) :
    FS (SmO E Gl G ol) Eq (get >>= g) y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_bind, run_get] at hn ⊢
  exact (hg σ hs'.coroSelf hs'.steps hs'.seek).sim σ σ' τ τ' hs ht hn

private theorem fs_charge_l {b : StmtExprMd} {g : Unit → EvalM PM α} {y : EvalM PM α}
    (hg : FS (SmO E Gl G ol) Eq (g ()) y) : FS (SmO E Gl G ol) Eq (chargeIteration b >>= g) y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_bind, run_chargeIteration b hs'.steps] at hn ⊢
  exact hg.sim σ σ' τ τ' hs ht hn



private theorem not_coro : ((mkId Operation.Not.procName).text == coroCompletionName) = false := by decide

private theorem of_not : opOf? (mkId Operation.Not.procName).text = some .Not := rfl

section Loop
variable {cfg : ExternalBackendM PM} (hc : CfgB cfg)
  (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg))
  {n : Nat} (ihs : ∀ k ≤ n, FundAt cfg E Rw 6 Gl k)
  {h : Control → EvalM PM Unit} (hh : ∀ c, CtlOK Gl G c → h c = throw c)

omit hc hext ihs hh in
private theorem loop_step {c' body' : StmtExprMd} {src : FileRange} {L : String}
    {ci' : EvalM PM Unit} (j : Nat) :
    evalWhileIter cfg (trueE src) (loopBody c' body' src L) false ci' (pure ()) (j + 3) =
      (ci' >>= fun _ => evalScopedStmt cfg (j + 2) (loopBody c' body' src L) >>= fun _ =>
        evalWhileIter cfg (trueE src) (loopBody c' body' src L) false ci' (pure ()) (j + 2)) := by
  conv => lhs; rw [evalWhileIter]
  simp only [Bool.false_eq_true, ite_false]
  show (pure () >>= fun _ => pure () >>= fun _ => evalExprMd cfg (j + 2) (trueE src) >>= fun c =>
    ci' >>= fun _ => liftM (Interpreter.isTrue cfg c) >>= fun b => if b = true then
      (pure () >>= fun _ => evalScopedStmt cfg (j + 2) (loopBody c' body' src L) >>= fun _ =>
        evalWhileIter cfg (trueE src) (loopBody c' body' src L) false ci' (pure ()) (j + 2)) else pure ()) = _
  have h1 : evalExprMd cfg (j + 2) (trueE src) = pure (.bool ⟨true⟩) := rfl
  have h2 : (liftM (Interpreter.isTrue cfg (.bool ⟨true⟩)) : EvalM PM Bool) = pure true := rfl
  simp only [h1, h2, pure_bind, ite_true]

omit hc ihs hh in
include hext in
private theorem isTrue_not_fails {v : Value} (hv : ¬ ∃ b, v = .bool ⟨b⟩) (τ τ' : Trace) :
    ∃ e e', Interpreter.isTrue cfg v τ = .error e ∧ opCall cfg .Not [v] τ' = .error e' ∧ (Stuck e' → Stuck e) := by
  cases v with
  | external e =>
    obtain ⟨m, hm⟩ := hext e
    exact ⟨_, _, hm τ, rfl, fun _ => .mk m⟩
  | bool b => exact absurd ⟨b.b, rfl⟩ hv
  | _ => exact ⟨_, _, rfl, rfl, fun _ => .mk _⟩

omit hc hext ihs in
private theorem fsc_fail_both {X : PM α} {Y : PM β} {g : α → EvalM PM Unit} {f : β → EvalM PM Unit}
    (hXY : ∀ τ τ', ∃ e e', X τ = .error e ∧ Y τ' = .error e' ∧ (Stuck e' → Stuck e)) :
    FS (SmO E Gl G ol) Eq (liftM X >>= g) (tryCatch (liftM Y >>= f) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_tryCatch_bind', run_bind, run_lift, run_lift]
  obtain ⟨e, e', he, he', hs⟩ := hXY τ τ'
  rw [he, he']
  exact hs

omit hc hext ihs hh in
private theorem fsc_exit {L : String} {src : FileRange} {j : Nat} (hL0 : L ∈ ol) {rest : Unit → EvalM PM Unit}
    (hexit : ∀ σ τ, ∃ σ'', run (h (.exit_ L)) σ τ = .ok ((.ok (), σ''), τ) ∧
      ∀ s, (SmO E Gl G ol).st s σ → (SmO E Gl G ol).st s σ'') :
    FS (SmO E Gl G ol) Eq (pure ()) (tryCatch (evalScopedStmt cfg (j + 2) (exitL src L) >>= rest) h) := by
  refine ⟨fun σ σ' τ τ' hs ht _ => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  have e1 : (evalScopedStmt cfg (j + 2) (exitL src L) : EvalM PM Unit) =
      withOperandWindow (exitL src L) (evalStmt cfg (j + 1) (exitL src L)) := by
    show withBlockScope [exitL src L] (withOperandWindow (exitL src L) (evalStmt cfg (j + 1) (exitL src L))) = _
    exact withBlockScope_nil rfl _
  have hco : σ'.openLabels.contains L = true := by
    rw [hs.2]
    exact List.contains_iff_mem.mpr hL0
  have e2 : run (withOperandWindow (exitL src L) (evalStmt cfg (j + 1) (exitL src L))) σ' τ' =
      .ok ((.error (.exit_ L), σ'), τ') := by
    rw [run_wow_nil hs'.ops']
    simp only [exitL, evalStmt, run_bind, run_get, hco, ite_true]
    rfl
  rw [e1, run_tryCatch_bind', e2]
  dsimp only
  obtain ⟨σ'', he, hst⟩ := hexit σ' τ'
  rw [he, run_pure]
  exact ⟨rfl, hst σ hs, ht⟩

omit hc hext ihs hh in
private theorem scoped_block {body : StmtExprMd} (hb : ∃ ss lab, body.val = .Block ss lab [] none) (k : Nat) :
    evalScopedStmt cfg (k + 1) body = evalStmt cfg k body := by
  obtain ⟨ss, lab, hv⟩ := hb
  rcases body with ⟨v, s⟩
  dsimp only at hv
  subst hv
  rfl

omit hc hext ihs hh in
private theorem wbs_nil {l : List StmtExprMd} (hl : blockDeclarations l = []) (x : EvalM PM α) :
    withBlockScope l x = x := by
  unfold withBlockScope
  simp only [hl, List.isEmpty_nil, ite_true]

omit hc hext ihs hh in
private theorem decl_block {body : StmtExprMd} (hb : ∃ ss lab, body.val = .Block ss lab [] none) (rest : List StmtExprMd) :
    blockDeclarations (body :: rest) = blockDeclarations rest := by
  obtain ⟨ss, lab, hv⟩ := hb
  simp [blockDeclarations, hv]

omit hext ihs hh in
include hc in
/-- Negating a condition is an operator call: it lets no `jump_` out, so the boundary of the expression
evaluation around it changes nothing. -/
private theorem exprMd_notC (k : Nat) (c : StmtExprMd) (src : FileRange) :
    evalExprMd cfg (k + 2) (notC c src) =
      ((modify fun (s : EvalState) => { s with callSite := src }) >>= fun _ =>
        evalExpr cfg (k + 1) (.Call none (mkId Operation.Not.procName) [c] [])) := by
  rw [evalExprMd]
  simp only [notC]
  refine jumpBoundary_noJ (NoJ.bind (NoJ.modify _) (fun _ => ?_))
  simp only [evalExpr, not_coro, of_not, Bool.false_eq_true, ite_false, List.mapM_cons, List.mapM_nil, hc.strict,
    isPartialOp, bind_assoc]
  repeat' (first
    | exact noJ_evalExprMd cfg _ _
    | with_unfolding_none exact NoJ.liftM _
    | with_unfolding_none exact NoJ.pure _
    | with_unfolding_none exact NoJ.get
    | with_reducible apply NoJ.bind
    | refine fun _ => ?_)

omit hc hext ihs hh in
/-- The exit `exitL src L` run with `L` open leaves `L`: it returns no `jump_`. -/
private theorem exitL_noJ {m : Nat} {src : FileRange} {L : String} {σ : EvalState} (hL : L ∈ σ.openLabels) :
    NoJAt (evalStmt cfg m (exitL src L)) σ := by
  cases m with
  | zero => rw [evalStmt]; exact NoJAt.ofNoJ (NoJ.throw (fun _ _ h => by cases h))
  | succ m =>
    simp only [exitL, evalStmt]
    refine NoJAt.bind (NoJAt.ofNoJ NoJ.get) (fun τ a σ1 τ1 h => ?_)
    rw [run_get] at h
    cases h
    have hco : σ.openLabels.contains L = true := List.contains_iff_mem.mpr hL
    simp only [hco, ite_true]
    exact NoJAt.ofNoJ (NoJ.throw (fun _ _ h => by cases h))

omit hc hext ihs hh in
/-- The guard `guard c' src L` run outside a coroutine body with `L` open returns no `jump_`: its condition is
an expression, which lets none out, and its exit leaves the open block `L`. -/
private theorem guard_noJ {m : Nat} {c' : StmtExprMd} {src : FileRange} {L : String} {σ : EvalState}
    (hco : σ.coroSelf = none) (hL : L ∈ σ.openLabels) : NoJAt (evalStmt cfg m (guard c' src L)) σ := by
  cases m with
  | zero => rw [evalStmt]; exact NoJAt.ofNoJ (NoJ.throw (fun _ _ h => by cases h))
  | succ m =>
    simp only [guard]
    rw [evalStmt]
    refine NoJAt.bind (NoJAt.ofNoJ NoJ.get) (fun τ a σ1 τ1 h => ?_)
    rw [run_get] at h
    cases h
    simp only [hco, Option.isNone_none, ite_true]
    refine NoJAt.bind (NoJAt.ofNoJ (noJ_evalExprMd cfg m _)) (fun τ v σ3 τ3 h3 => ?_)
    have hol3 : σ3.openLabels = σ.openLabels := ((keepsAt cfg m).exprMd _ σ.openLabels).keep _ _ _ _ _ rfl h3
    refine NoJAt.bind (NoJAt.ofNoJ (NoJ.liftM _)) (fun τ b σ4 τ4 h4 => ?_)
    have e4 : σ4 = σ3 := by
      rw [run_lift] at h4
      split at h4
      · cases h4
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h4
        exact h4.1.2.symm
    subst e4
    split
    · cases m with
      | zero => exact NoJAt.ofNoJ (NoJ.throw (fun _ _ h => by cases h))
      | succ m =>
        show NoJAt (withBlockScope [exitL src L] (withOperandWindow (exitL src L) (evalStmt cfg m (exitL src L)))) σ4
        rw [wbs_nil rfl]
        exact NoJAt.withOperandWindow (fun σ' hol _ => exitL_noJ (by rw [hol, hol3]; exact hL))
    · exact NoJAt.ofNoJ (NoJ.pure _)

omit hc hext ihs hh in
/-- Running the statements `[body', guard c' src L]` of the rewritten loop's body one after the other, outside a
coroutine body with `L` open, returns no `jump_` to a label they hold: the body's own statement list lands those,
and the guard returns no `jump_`. -/
private theorem loopBody_noLand {m : Nat} {body' c' : StmtExprMd} {src : FileRange} {L : String}
    (hB' : ∃ ss lab, body'.val = .Block ss lab [] none) {σ : EvalState} (hco : σ.coroSelf = none)
    (hL : L ∈ σ.openLabels) (τ : Trace) (l : String) (d : GotoDestination) (σ1 : EvalState) (τ1 : Trace)
    (h : run ([body', guard c' src L].forM fun s => do
        modify fun (st : EvalState) => { st with stmtSite := s.source }
        if (stackAnnotation? s).isNone then withOperandWindow s (evalStmt cfg (m + 1) s)) σ τ =
          .ok ((.error (.jump_ l d), σ1), τ1)) : l ∉ flatLabels [body', guard c' src L] := by
  obtain ⟨ss, lab, hv⟩ := hB'
  rcases body' with ⟨bv, bs⟩
  dsimp only at hv
  subst hv
  have hgl : statementLabels (guard c' src L) = [] := by
    simp only [guard]
    rw [statementLabels_ite]
    simp [exitL, statementLabels_other]
  have hfl : flatLabels [⟨.Block ss lab [] none, bs⟩, guard c' src L] = statementLabels ⟨.Block ss lab [] none, bs⟩ := by
    simp [flatLabels, hgl]
  rw [hfl]
  have hab : (stackAnnotation? (⟨.Block ss lab [] none, bs⟩ : StmtExprMd)).isNone = true := by simp [stackAnnotation?]
  have hag : (stackAnnotation? (guard c' src L)).isNone = true := by simp [guard, stackAnnotation?]
  have hcn := cnAt cfg (m + 1)
  have hkp := keepsAt cfg (m + 1)
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, hab, hag, ite_true, bind_assoc] at h
  rw [run_bind, run_modify] at h
  dsimp only at h
  rw [run_bind] at h
  rcases hr : run (withOperandWindow ⟨.Block ss lab [] none, bs⟩ (evalStmt cfg (m + 1) ⟨.Block ss lab [] none, bs⟩))
    { σ with stmtSite := bs } τ with e | ⟨⟨c | u, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact LandFree.withOperandWindow (landFree_block cfg m ss lab bs) (hcn.stmt _) { σ with stmtSite := bs }
      _ _ _ _ _ hco hr
  · have hco2 : σ2.coroSelf = none :=
      (CN.withOperandWindow (hcn.stmt _)).keep { σ with stmtSite := bs } _ _ σ2 _ hco hr
    have hol2 : σ2.openLabels = σ.openLabels :=
      (OLKeep.withOperandWindow (hkp.stmt _ σ.openLabels)).keep { σ with stmtSite := bs } _ _ σ2 _ rfl hr
    dsimp only at h
    rw [run_bind, run_modify] at h
    dsimp only at h
    rw [run_bind] at h
    exfalso
    rcases hg : run (withOperandWindow (guard c' src L) (evalStmt cfg (m + 1) (guard c' src L)))
      { σ2 with stmtSite := (guard c' src L).source } τ2 with e | ⟨⟨c | u, σ3⟩, τ3⟩ <;> rw [hg] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact NoJAt.withOperandWindow (σ := { σ2 with stmtSite := (guard c' src L).source })
        (fun σ' hol hc' => guard_noJ (hc'.trans hco2) (by rw [hol]; show L ∈ σ2.openLabels; rw [hol2]; exact hL))
        _ _ _ _ _ hg
    · dsimp only at h
      rw [run_pure] at h
      cases h

omit hc hext ihs hh in
private theorem fsc_list_eq {X : EvalM PM Unit} {Y Y' : EvalM PM α} {R : α → EvalM PM Unit}
    (heq : ∀ σ σ' τ', (SmO E Gl G ol).st σ σ' → run Y σ' τ' = run Y' σ' τ')
    (hf : FS (SmO E Gl G ol) Eq X (tryCatch (Y' >>= R) h)) : FS (SmO E Gl G ol) Eq X (tryCatch (Y >>= R) h) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_tryCatch_bind', heq σ σ' τ' hs, ← run_tryCatch_bind']
  exact hf.sim σ σ' τ τ' hs ht hn

include hc hext ihs hh in
/-- The iterations of a source post-test loop are simulated by the iterations of the target's
`while true` loop inside a `tryCatch` handler `h`. If the condition and body are related by `E`,
both bodies are blocks, `h` rethrows every signal that may escape and turns `exit L` into a normal
exit with related states, and the invariant checks `ci` and `ci'` simulate, then running `ci`, the
body and the remaining loop with fuel `fb ≤ n` is simulated by the target loop with fuel `j + 1`
for every `j ≥ 6 * fb + 2`. It needs `FundAt` for every fuel up to `n`, a backend satisfying
`CfgB`, and an `externalTruthy` that always gets stuck. -/
private theorem loop {c c' body body' : StmtExprMd} {src : FileRange} {L : String}
    (hcc : E c c') (hbb : E body body') (hB : ∃ ss lab, body.val = .Block ss lab [] none)
    (hB' : ∃ ss lab, body'.val = .Block ss lab [] none)
    (hL0 : L ∈ ol) (hexit : ∀ σ τ, ∃ σ'', run (h (.exit_ L)) σ τ = .ok ((.ok (), σ''), τ) ∧
      ∀ s, (SmO E Gl G ol).st s σ → (SmO E Gl G ol).st s σ'')
    {ci ci' : EvalM PM Unit} (hci : FS (SmO E Gl G ol) Eq ci ci') (rest : Unit → EvalM PM Unit) (fb j : Nat)
    (hfb : fb ≤ n) (hj : 6 * fb + 2 ≤ j) :
    FS (SmO E Gl G ol) Eq
      (ci >>= fun _ => evalScopedStmt cfg fb body >>= fun _ => evalWhileIter cfg c body true ci (pure ()) fb)
      (tryCatch (evalWhileIter cfg (trueE src) (loopBody c' body' src L) false ci' (pure ()) (j + 1) >>= rest)
        h) := by
  induction fb generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
    rw [loop_step]
    simp only [bind_assoc]
    exact fsc_bind hh hci (fun _ => fs_vac rfl)
  | succ fb ih =>
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  rw [loop_step]
  simp only [bind_assoc]
  refine fsc_bind hh hci (fun _ => ?_)
  rw [scoped_block hB, scoped_block ⟨_, _, rfl⟩]
  simp only [loopBody, evalStmt]
  rw [wbs_nil (by rw [decl_block hB']; rfl)]
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 4 := ⟨j - 4, by omega⟩
  unfold chargeStep
  simp only [bind_assoc]
  refine fsc_get_r (fun s _ hst => ?_)
  simp only [hst, pure_bind]
  refine fsc_list_eq (fun σ σ' τ' hs => run_evalStmtList_noLand cfg hs.1.coroSelf'
    (loopBody_noLand hB' hs.1.coroSelf' (by rw [hs.2]; exact hL0) τ')) ?_
  have hab' : (stackAnnotation? body').isNone = true := by
    obtain ⟨ss, lab, hv⟩ := hB'
    simp [stackAnnotation?, hv]
  have hag : (stackAnnotation? (guard c' src L)).isNone = true := by simp [guard, stackAnnotation?]
  simp only [List.forM_eq_forM, List.forM_cons, List.forM_nil, bind_assoc, pure_bind, hab', hag, ite_true]
  refine fsc_modify_r (fun σ σ' hs => ?_) ?_
  · exact ⟨by strel hs.1, hs.2⟩
  refine fsc_wow_r ?_
  refine fsc_bind hh (FSH.toO ((keepsAt cfg _).stmt _) ol
    ((ihs fb (by omega)).stmt _ _ (closed _ _ hbb) (ovOK_none rfl _ _) _ (by omega))) (fun _ => ?_)
  refine fsc_modify_r (fun σ σ' hs => ?_) ?_
  · exact ⟨by strel hs.1, hs.2⟩
  refine fsc_wow_r ?_
  conv => lhs; rw [evalWhileIter]
  simp only [guard, evalStmt, bind_assoc]
  refine fs_charge_l ?_
  refine fsc_get_r (fun s hco _ => ?_)
  simp only [pure_bind, hco, Option.isNone_none, ite_true, exprMd_notC hc]
  simp only [evalExpr, bind_assoc, not_coro, of_not, Bool.false_eq_true, ite_false,
    isPartialOp, List.mapM_cons, List.mapM_nil, hc.strict]
  refine fsc_modify_r (fun σ σ' hs => ?_) ?_
  · exact ⟨by strel hs.1, hs.2⟩
  refine fsc_get_r (fun _ _ _ => ?_)
  refine fsc_bind hh (FSH.toO ((keepsAt cfg _).exprMd _) ol
    ((ihs fb (by omega)).exprMdT (fun _ _ => trivial) _ _ (closed _ _ hcc) (ovOK_none rfl _ _) _ (by omega))) (fun v => ?_)
  by_cases hv : ∃ b, v = .bool ⟨b⟩
  · obtain ⟨b, rfl⟩ := hv
    have e1 : (liftM (Interpreter.isTrue cfg (.bool ⟨b⟩)) : EvalM PM Bool) = pure b := rfl
    have e2 : (liftM (opCall cfg Operation.Not [.bool ⟨b⟩]) : EvalM PM Value) = pure (.bool ⟨!b⟩) := rfl
    have e3 : (liftM (Interpreter.isTrue cfg (.bool ⟨!b⟩)) : EvalM PM Bool) = pure (!b) := rfl
    simp only [e1, e2, e3, pure_bind]
    cases b
    · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      exact fsc_exit hL0 hexit
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true, pure_bind]
      exact ih (j + 5) (by omega) (by omega)
  · exact fsc_fail_both (X := Interpreter.isTrue cfg v) (Y := opCall cfg .Not [v])
      (fun τ τ' => isTrue_not_fails hext hv τ τ')

omit hc hext ihs hh in
private theorem fs_target_eq {x y y' : EvalM PM α} {g : EvalState → EvalState}
    (heq : ∀ σ' τ', σ'.coroSelf = none → σ'.seek = none → run y σ' τ' = run y' (g σ') τ')
    (hg : ∀ σ σ', (SmO E Gl G ol).st σ σ' → (SmO E Gl G ol).st σ (g σ')) (h : FS (SmO E Gl G ol) Eq x y') :
    FS (SmO E Gl G ol) Eq x y := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [heq σ' τ' hs'.coroSelf' hs'.seek']
  exact h.sim σ (g σ') τ τ' (hg σ σ' hs) ht hn

omit hc hext ihs in
private theorem fsc_stmtList1 {X : EvalM PM Unit} (x : StmtExprMd) (m : Nat) (k : Value → EvalM PM Unit)
    (hlab : statementLabels x = []) (hann : (stackAnnotation? x).isNone = true)
    (hf : FS (SmO E Gl G ol) Eq X (tryCatch (evalStmt cfg m x >>= fun _ => k default) h)) :
    FS (SmO E Gl G ol) Eq X (tryCatch (evalStmtList cfg (m + 1) [x] false >>= k) h) := by
  rw [evalStmtList_plain (fun t ht => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    exact hlab)]
  simp only [bind_assoc]
  refine fsc_get_r (fun s hco _ => ?_)
  simp only [hco, Option.isNone_none, ite_true, List.forM_eq_forM,
    List.forM_cons, List.forM_nil, bind_assoc, pure_bind, hann]
  refine fsc_modify_r (fun σ σ' hs => ?_) (fsc_wow_r hf)
  exact ⟨by strel hs.1, hs.2⟩

omit hc hext ihs in
private theorem fsc_loopW {X : EvalM PM Unit} {c' : StmtExprMd} {invs' : List StmtExprMd}
    {dec' : Option StmtExprMd} {body' : StmtExprMd} {src : FileRange} {L : String} (m : Nat)
    (k : Unit → EvalM PM Unit)
    (hf : FS (SmO E Gl G ol) Eq X (tryCatch (evalWhileIter cfg (trueE src) (loopBody c' body' src L) false
      (do
        forIn invs' PUnit.unit fun inv _ => do
          evalStmt cfg m ⟨.Assert inv none, inv.source⟩
          pure (ForInStep.yield PUnit.unit)
        pure PUnit.unit) (pure ()) m >>= k) h)) :
    FS (SmO E Gl G ol) Eq X (tryCatch (evalStmt cfg (m + 1) (loopW c' invs' dec' body' src L) >>= k) h) := by
  simp only [loopW, evalStmt, bind_assoc]
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_tryCatch_bind', run_get]
  simp only [hs'.coroSelf', hs'.seek', Option.isSome_none, Bool.false_eq_true, ite_false, Bool.false_and,
    pure_bind]
  exact hf.sim σ σ' τ τ' hs ht hn

omit hc hext ihs hh in
private theorem fs_get_rS {x : EvalM PM α} {f : EvalState → EvalM PM α} (hf : ∀ s, FS (Sm E Gl G) Eq x (f s)) :
    FS (Sm E Gl G) Eq x (get >>= f) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  rw [run_bind, run_get]
  exact (hf σ').sim σ σ' τ τ' hs ht hn

omit hc hext ihs hh in
private theorem fs_get_r {x : EvalM PM α} {f : EvalState → EvalM PM α}
    (hf : ∀ s, s.coroSelf = none → s.seek = none → FS (SmO E Gl G ol) Eq x (f s)) :
    FS (SmO E Gl G ol) Eq x (get >>= f) := by
  refine ⟨fun σ σ' τ τ' hs ht hn => ?_⟩
  have hs' : StRel G (IxRel E) σ σ' := hs.1
  rw [run_bind, run_get]
  exact (hf σ' hs'.coroSelf' hs'.seek').sim σ σ' τ τ' hs ht hn

include hc hext ihs in
/-- A rewrite step of `EliminateDoWhile` simulates as a statement: if `s` is a post-test loop and `t` is
its rewrite (`Rw s t`), then `evalStmt` on `s` with fuel `n + 1` is simulated by `evalStmt` on `t`
with any fuel `M ≥ 6 * (n + 1)`. It needs `FundAt` for every fuel up to `n`, a backend satisfying
`CfgB`, and an `externalTruthy` that always gets stuck. -/
private theorem dw_stmt {s t : StmtExprMd} (hrw : Rw s t) (M : Nat) (hM : 6 * (n + 1) ≤ M) :
    FS (Sm E Gl G) Eq (evalStmt cfg (n + 1) s) (evalStmt cfg M t) := by
  obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, hcc, his, hbb, hL, hB, hB'⟩ := hrw
  obtain ⟨M, rfl⟩ : ∃ m, M = m + 4 := ⟨M - 4, by omega⟩
  simp only [evalStmt, target]
  refine fs_get_rS (fun s' => ?_)
  refine fs_openR L hL (fun ol hol => ?_)
  refine fs_get_l (fun s hco _ hsk => ?_)
  simp only [hco, hsk, Option.isNone_none, Option.isSome_none, Bool.and_self, ite_true,
    Bool.false_eq_true, ite_false]
  rw [wbs_nil rfl]
  have hL' : ∀ l, Gl l → (l == L) = false := by
    intro l hl
    cases hb : (l == L)
    · rfl
    · simp only [beq_iff_eq] at hb
      subst hb
      exact absurd hL hl
  refine fsc_stmtList1 _ _ _ (statementLabels_other _ _ (by intros; nofun) (by intros; nofun))
    (by simp [loopW, stackAnnotation?]) ?_
  refine fsc_loopW _ _ ?_
  have hci : FS (SmO E Gl G ol) Eq
      (do
        forIn invs PUnit.unit fun inv _ => do
          evalStmt cfg n ⟨.Assert inv none, inv.source⟩
          pure (ForInStep.yield PUnit.unit)
        pure PUnit.unit)
      (do
        forIn invs' PUnit.unit fun inv _ => do
          evalStmt cfg (M + 1) ⟨.Assert inv none, inv.source⟩
          pure (ForInStep.yield PUnit.unit)
        pure PUnit.unit) :=
    FSH.toO (fun o => by have ih := keepsAt cfg (M + 1); keep_tac) ol
      (fs_bind (fs_forIn his (fun a a' ha _ => fs_bind ((ihs n (Nat.le_refl n)).stmt _ _
        (nr_triv (fun _ _ => trivial) (fun _ _ => trivial) (.assert ha) (fun _ _ h => by cases h)) (ovOK_none rfl _ _) _
          (by omega)) (fun _ _ _ => fs_pure rfl)))
        (fun _ _ _ => fs_pure rfl))
  refine loop hc hext ihs (fun c hc => ?_) hcc hbb hB hB' hol (fun σ τ => ?_) hci _ n M (Nat.le_refl n) (by omega)
  · cases c with
    | exit_ l => simp only [hL' l hc, Bool.false_eq_true, ite_false]
    | goto_ l => simp only [hL' l hc, Bool.false_eq_true, ite_false]
    | _ => rfl
  · refine ⟨_, by simp only [beq_self_eq_true, ite_true]; exact run_modify _ _ _, fun s0 hs0 => ?_⟩
    exact ⟨by strel hs0.1, hs0.2⟩

include ihs in
/-- A rewrite step of `EliminateDoWhile` simulates as a scoped statement: if `Rw s t`, then
`evalScopedStmt` on `s` with fuel `n + 1` is simulated by `evalScopedStmt` on `t` with any fuel
`M ≥ 6 * (n + 1)`, given `FundAt` for every fuel up to `n`. -/
private theorem dw_scoped {s t : StmtExprMd} (hrw : Rw s t) (M : Nat) (hM : 6 * (n + 1) ≤ M) :
    FS (Sm E Gl G) Eq (evalScopedStmt cfg (n + 1) s) (evalScopedStmt cfg M t) := by
  have hN : NR E Rw Gl s t := .inr hrw
  obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, -⟩ := hrw
  obtain ⟨M, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e1 : evalScopedStmt cfg (n + 1) ⟨.While c invs dec body true, src⟩ =
      withOperandWindow ⟨.While c invs dec body true, src⟩ (evalStmt cfg n ⟨.While c invs dec body true, src⟩) := by
    show withBlockScope [⟨.While c invs dec body true, src⟩]
      (withOperandWindow ⟨.While c invs dec body true, src⟩ (evalStmt cfg n ⟨.While c invs dec body true, src⟩)) = _
    exact wbs_nil rfl _
  rw [e1]
  exact fs_wowL ((ihs n (Nat.le_refl n)).stmt _ _ hN (ovOK_none rfl _ _) M (by omega))

/-- A rewrite step of `EliminateDoWhile` simulates when evaluated as an expression or for call outputs:
if `Rw s t`, then `evalExpr`, `evalExprMd` and `evalCallOutputs` on `s` with fuel `n + 1` are
simulated by the same functions on `t` with any fuel `M ≥ 6 * (n + 1)`. Both sides report an
evaluation error, since a loop is not an expression. -/
private theorem dw_errs {s t : StmtExprMd} (hrw : Rw s t) (M : Nat) (hM : 6 * (n + 1) ≤ M) :
    FS (Sm E Gl G) Eq (evalExpr cfg (n + 1) s.val) (evalExpr cfg M t.val) ∧
    FS (Sm E Gl G) Eq (evalExprMd cfg (n + 1) s) (evalExprMd cfg M t) ∧
    FS (Sm E Gl G) Eq (evalCallOutputs cfg (n + 1) s.val) (evalCallOutputs cfg M t.val) := by
  obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, -⟩ := hrw
  obtain ⟨M, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  refine ⟨fs_evalError _ _, ?_, ?_⟩
  · rcases n with _ | n
    · exact fs_vac rfl
    · exact fs_evalError _ _
  · rcases n with _ | n
    · exact fs_vac rfl
    · exact fs_bind (fs_evalError (A := Eq) _ _) (fun a b hab => by subst hab; exact fs_pure rfl)

end Loop

/-- `EliminateDoWhile` satisfies `PassRel cfg E Rw 6 Gl` for every backend `cfg` that satisfies `CfgB`
and whose `externalTruthy` always gets stuck. -/
theorem dw_rel {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg)) : PassRel cfg E Rw 6 Gl where
  K_pos := by omega
  cfg_ok := hc
  closed := closed
  decl := fun _ s t hrw => by
    obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, -⟩ := hrw
    rfl
  declX := fun _ s t hrw => .ofEq (by
      obtain ⟨c, invs, dec, body, src, c', invs', dec', body', src', L, rfl, rfl, -⟩ := hrw
      rfl)
  declOK := fun _ _ _ x _ => ⟨fun h => h, notV_none rfl x⟩
  exDecl := fun _ _ _ h => h.elim
  exDeclOK := fun _ _ h => h.elim
  retV := fun h => absurd rfl h
  retHook := fun _ _ _ => trivial
  retPlain := fun _ _ => ⟨fun _ h => h, fun _ => rfl⟩
  retGl := fun _ h => by cases h
  retRes := fun _ h => by cases h
  glRes := fun _ h h' => h h'
  labE := fun s t h l hl => labE s t h l hl
  rwLab := fun s t hrw => rwLab s t hrw
  exLab := fun _ _ h => h.elim
  renAnn := fun _ _ h => h.elim
  retK := fun h => absurd rfl h
  retNG := fun h => absurd rfl h
  retVok := fun h => absurd rfl h
  renOp := fun _ _ h => (h : False).elim
  step := fun n ihs => {
    scoped_ := fun _ _ hrw _ M hM => dw_scoped ihs hrw M hM
    exprMd := fun _ _ hrw _ M hM => FS.vr ((dw_errs hrw M hM).2.1)
    expr := fun _ _ hrw _ M hM => FS.vr ((dw_errs hrw M hM).1)
    stmt := fun _ _ hrw _ M hM => dw_stmt hc hext ihs hrw M hM
    outputs := fun _ _ hrw _ M hM => FS.vr ((dw_errs hrw M hM).2.2)
    exStmt := fun _ _ h => h.elim
    exLast := fun _ _ h => h.elim }

end Strata.Laurel.PassSemantics.DoWhileSim

namespace Strata.Laurel.PassSemantics.DoWhileSim

open Strata.Laurel
open Strata.Laurel.Interpreter
open EliminateDoWhile

local instance : Reserved := Reserved.none (fun l => "$dowhile_exit_".isPrefixOf l)

private theorem pass_run (opts : LaurelTranslateOptions) (p : LaurelProgram) (m : SemanticModel) :
    eliminateDoWhilePass.run opts (.Unordered p) m =
      (.Unordered ((mapLaurelProgramStmtExprM rewriteNode p).run {}).1, [], {}) := rfl

private theorem dw_hc (r : StmtExprMd) (st : ElimState) :
    ((rewriteNode r).run st).1 = r ∨ NodeRw r ((rewriteNode r).run st).1 := by
  rcases r with ⟨v, s⟩
  unfold rewriteNode
  split
  · rename_i heq
    dsimp only at heq
    subst heq
    right
    refine ⟨(fun _ _ h => by simp at h), rfl, (fun _ _ h => ?_), ?_⟩ <;>
      simp_all [freshExitLabel, StateT.run, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        pure, StateT.pure, StmtExprMd.isWildcard]
  · left; rfl

private theorem dw_trav : TravOK rewriteNode := travOK_mk dw_hc

/-- `mapLaurelProgramStmtExprM rewriteNode` preserves a whole-program run of any program satisfying
`ProgOK (Hered PDW)`: running the rewritten program with 6 times the fuel gives an `ERel`-related
result to running the input, unless the input gets stuck or runs out of fuel. The backend satisfies
`CfgB` and its `externalTruthy` always gets stuck, neither run uses a step budget, both use the same
entry procedure and `printAsserts`, and the traces are related. -/
private theorem eliminateDoWhile_correct {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg))
    {p : LaurelProgram} (hp : ProgOK (Hered PDW) p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n) (hM : 6 * n ≤ o'.fuel) (he : o.entryProcedure = o'.entryProcedure)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {τ τ' : Trace} (ht : TrRel (Sm E Gl {}) τ τ') (hnf : NotOOFEntry (runEntry cfg o p τ)) :
    ERel (Sm E Gl {}) (runEntry cfg o p τ)
      (runEntry cfg o' ((mapLaurelProgramStmtExprM rewriteNode p).run {}).1 τ') :=
  entry_sim (dw_rel hc hext) (prog_trav (g := rewriteNode) dw_trav (fun _ _ _ => trivial) rfl rfl (fun _ _ => trivial) (fun _ _ _ => trivial) id (fun _ _ h => (h : False).elim) hp dw_lit {}) hn hM he hl hl' hq (fun h => h) (fun h => absurd rfl h) (fun h => absurd rfl h) (fun _ _ => valued_none rfl _) ht hnf


private theorem eliminateDoWhile_procAt {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg))
    {p : LaurelProgram} (hp : ProgOK (Hered PDW) p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : 6 * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {P : Procedure} (hPm : P ∈ p.staticProcedures) :
    ∃ P' ∈ ((mapLaurelProgramStmtExprM rewriteNode p).run {}).1.staticProcedures, ∀ τ τ', TrRel (Sm E Gl {}) τ τ' → NotOOFEntry (runProcAt cfg o p P τ) →
      ERel (Sm E Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' ((mapLaurelProgramStmtExprM rewriteNode p).run {}).1 P' τ') :=
  procAt_all (dw_rel hc hext) (prog_trav (g := rewriteNode) dw_trav (fun _ _ _ => trivial) rfl rfl (fun _ _ => trivial) (fun _ _ _ => trivial) id (fun _ _ h => (h : False).elim) hp dw_lit {}) hn hM hl hl' hq rfl hPm

/-- The default backend `{}` satisfies the hypothesis on `externalTruthy` that
`eliminateDoWhilePass_correct` and `eliminateDoWhilePass_procAt` take: its `externalTruthy`
always gets stuck. -/
theorem hext_default :
    ∀ e, ∃ msg, ∀ τ, ({} : ExternalBackendM PM).externalTruthy e τ = .error (.stuck msg) :=
  fun _ => ⟨_, fun _ => rfl⟩

private theorem pass_out {opts : LaurelTranslateOptions} {p q : LaurelProgram} {m : SemanticModel} {d : List Message}
    {st : Statistics} (hrun : eliminateDoWhilePass.run opts (.Unordered p) m = (.Unordered q, d, st)) :
    q = ((mapLaurelProgramStmtExprM rewriteNode p).run {}).1 := by
  rw [pass_run] at hrun
  simp only [Prod.mk.injEq, Program.Unordered.injEq] at hrun
  exact hrun.1.symm

/-- `EliminateDoWhile` preserves a whole-program run: running the pass's output with 6 times the
fuel ends with the same outcome and the same number of failed checks as running the input, unless
the input gets stuck. The interpreter runs without a step budget (`limitSteps = false`). -/
theorem eliminateDoWhilePass_correct {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg)) (opts : LaurelTranslateOptions)
    {p q : LaurelProgram} {m : SemanticModel} {d : List Message} {st : Statistics}
    (hrun : eliminateDoWhilePass.run opts (.Unordered p) m = (.Unordered q, d, st))
    (hp : ProgOK (Hered PDW) p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n) (hM : 6 * n ≤ o'.fuel) (he : o.entryProcedure = o'.entryProcedure)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {τ τ' : Trace} (ht : TrRel (Sm E Gl {}) τ τ') (hnf : NotOOFEntry (runEntry cfg o p τ)) :
    ERel (Sm E Gl {}) (runEntry cfg o p τ) (runEntry cfg o' q τ') := by
  rw [pass_out hrun]
  exact eliminateDoWhile_correct hc hext hp hn hM he hl hl' hq ht hnf

/-- `EliminateDoWhile` preserves a run started at any static procedure: running the pass's output
from that procedure with 6 times the fuel ends with the same outcome and the same number of failed
checks as running the input from it, unless the input gets stuck. The interpreter runs without a
step budget (`limitSteps = false`). -/
theorem eliminateDoWhilePass_procAt {cfg : ExternalBackendM PM} (hc : CfgB cfg)
    (hext : ∀ e, ∃ msg, ∀ τ, cfg.externalTruthy e τ = .error (.stuck msg)) (opts : LaurelTranslateOptions)
    {p q : LaurelProgram} {m : SemanticModel} {d : List Message} {st : Statistics}
    (hrun : eliminateDoWhilePass.run opts (.Unordered p) m = (.Unordered q, d, st))
    (hp : ProgOK (Hered PDW) p) {o o' : Options} {n : Nat}
    (hn : o.fuel = n + 1) (hM : 6 * (n + 1) ≤ o'.fuel)
    (hl : o.limitSteps = false) (hl' : o'.limitSteps = false) (hq : o.printAsserts = o'.printAsserts)
    {P : Procedure} (hPm : P ∈ p.staticProcedures) :
    ∃ P' ∈ q.staticProcedures, ∀ τ τ', TrRel (Sm E Gl {}) τ τ' → NotOOFEntry (runProcAt cfg o p P τ) →
      ERel (Sm E Gl {}) (runProcAt cfg o p P τ) (runProcAt cfg o' q P' τ') := by
  rw [pass_out hrun]
  exact eliminateDoWhile_procAt hc hext hp hn hM hl hl' hq hPm

end Strata.Laurel.PassSemantics.DoWhileSim

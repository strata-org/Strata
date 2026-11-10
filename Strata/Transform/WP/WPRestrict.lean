/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOver
public import Strata.Transform.WP.Adequacy
import Strata.DL.Imperative.BigStep.StoreAgree
import Strata.Transform.WP.WPOverEffects
import Strata.Transform.WP.WPReplay

/-! # Restricting the store of a failing loop-free list

A failure of a loop-free list from a store is one from the store restricted to the variables in
scope the list reads, at an event of the same kind (`claimK_restrict`, `fails_restrict`).

Key theorems: `claimK_restrict`, `fails_restrict`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
variable {F : P.Factory} {N N' Lc S V : List P.Ident} {σ σ' σ1 σp σp' : SemanticStore P}
  {o o' r r' : Outcome P} {X X' K K' : Outcome P → Prop} {x : P.Ident} {v : P.Expr} {c : Cmd P}
  {evs : List (Event P)} {B : PStmts P} {s : PStmt P}

/-! ## Restricting the store to the variables a list reads

A run from a store `σ` is replayed from a store `σ'` that agrees with `σ` on the identifiers of
the list and elsewhere agrees with it or is undefined: every command evaluates alike, and the
off-path shadow runs, which evaluate nothing, exist from any store. -/

/-- The outcomes have the same kind and label. -/
private def OSame : Outcome P → Outcome P → Prop
  | .normal _, .normal _ => True
  | .exit l _, .exit l' _ => l = l'
  | _, _ => False

/-- `X'` holds of every outcome of the same kind and label as an outcome satisfying `X`. -/
private def PImp (X X' : Outcome P → Prop) : Prop := ∀ o o', OSame o o' → X o → X' o'

section
omit iDE iBE iLB iHF iSF iHI iWL iOp iLV iHa iHFs
/-- Agreeing outcomes have the same kind and label. -/
private theorem _root_.Imperative.OAgree.same (h : OAgree F N o o') : OSame o o' := by
  cases o <;> cases o' <;> grind [OAgree, OSame]

omit iHB
/-- Projecting the stores keeps the kind and label of outcomes. -/
private theorem OSame.proj (σ σ' : SemanticStore P) (h : OSame o o') :
    OSame (o.proj σ) (o'.proj σ') := by cases o <;> cases o' <;> exact h

/-- Leaving a block keeps the kind and label of outcomes. -/
private theorem OSame.block (l : String) (σ σ' : SemanticStore P)
    (h : OSame o o') : OSame (o.block l σ) (o'.block l σ') := by
  cases o <;> cases o' <;> grind [OSame, Outcome.block]

/-- The requirement on untaken ends depends on the real end only through its kind. -/
private theorem PImp.virtK (hr : OSame r r') (hX : PImp X X') : PImp (VirtK r X) (VirtK r' X') := by
  rintro (_ | _) (_ | _) ho h <;> cases r <;> cases r' <;> grind [VirtK, OSame, PImp]

end

omit iBE iLB iHF iSF iHI iWL iOp iLV iHa iHFs in
mutual
/-- A shadow run of a list exists from any store, for a requirement holding of every outcome of
    the kind and label of an outcome satisfying the original requirement. -/
private theorem shL_transfer : ∀ {ss : PStmts P} {σ σ' : SemanticStore P}
    {K K' : Outcome P → Prop}, PImp K K' → ShL F ss σ K → ShL F ss σ' K'
  | [], _, _, _, _, hK, h => hK (.normal _) (.normal _) trivial h
  | _ :: _, _, _, _, _, hK, h => shS_transfer (fun
      | .normal _, .normal _, _, h1 => shL_transfer hK h1
      | .exit _ _, .exit _ _, ho, h1 => hK _ _ ho h1
      | .normal _, .exit _ _, ho, _ | .exit _ _, .normal _, ho, _ => ho.elim) h
/-- A shadow run of a statement exists from any store (as `shL_transfer`). -/
private theorem shS_transfer : ∀ {s : PStmt P} {σ σ' : SemanticStore P}
    {K K' : Outcome P → Prop}, PImp K K' → ShS F s σ K → ShS F s σ' K'
  | .cmd (.cmd c), _, _, _, _, hK, h => by
    cases c <;> first
      | exact hK (.normal _) (.normal _) trivial h
      | exact Exists.imp (fun _ h => ⟨h.1, hK (.normal _) (.normal _) trivial h.2⟩) h
  | .exit _ _, _, _, _, _, hK, h | .typeDecl _ _, _, _, _, _, hK, h => hK _ _ (by trivial) h
  | .ite (.det _) tss ess _, σ, σ', _, _, hK, ⟨h1, h2⟩ => by
    have hP := fun (o o' : Outcome P) ho => hK (o.proj σ) (o'.proj σ') (OSame.proj σ σ' ho)
    constructor <;> split <;> simp only [*, ite_true, ite_false, Bool.false_eq_true] at h1 h2
    all_goals first
      | exact hK (.normal _) (.normal _) trivial ‹_›
      | exact shL_transfer hP ‹_›
  | .block l _ _, σ, σ', _, _, hK, h =>
    shL_transfer (fun o o' ho => hK _ _ (OSame.block l σ σ' ho)) h
  | .cmd (.call _ _ _), _, _, _, _, _, h | .ite .nondet _ _ _, _, _, _, _, _, h
  | .loop _ _ _ _ _, _, _, _, _, _, h => h.elim
end

omit iBE iLB iHF iSF iHI iWL iOp iLV iHa iHFs in
/-- A shadow run of a branch exists from any store (as `shL_transfer`). -/
private theorem shB_transfer (hK : PImp K K') (h : ShB F B σ K) : ShB F B σ' K' := by
  cases hb : isLocal B <;> simp only [ShB, hb, ite_true, ite_false, Bool.false_eq_true] at h ⊢ <;>
    first | exact shL_transfer hK h | exact hK (.normal _) (.normal _) trivial h


omit iSF iHI iLI iWL iOp iLF iLFs iHa iBE iLB iLV in
mutual
/-- **An annotated run, replayed.**  An annotated run of `ss` from the value-valued `σ` gives
    an annotated run of `ss` from any store agreeing with `σ` on the identifiers of `ss` and on
    `live`, for any requirement on untaken ends implied by the original one on outcomes of the
    same kind and label, observed alike, whose outcome agrees with the original on `live`. -/
private theorem drun_agr [BEq P.Ident] [LawfulBEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {X : Outcome P → Prop} {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, DRun F X ss σ evs o → ∀ {X' : Outcome P → Prop} {live : List P.Ident}
    {σ' : SemanticStore P}, PImp X X' → WellFormedStore σ F → Agree (Block.idents ss ++ live) σ σ' →
    ∃ evs' o', DRun F X' ss σ' evs' o' ∧ evs'.map Event.obs = evs.map Event.obs ∧ OAgree F live o o'
  | _, _, _, _, _, .nil, _, _, _, _, hC, hA =>
    ⟨[], _, .nil, rfl, by simpa [Block.idents] using hA, hC⟩
  | _, _, _, _, _, .cons_normal (σ1 := σ1) (rest := rest) h1 h2, X', live, _, hX, hC, hA => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := drunS_agr hE (X' := VirtK (.normal σ1) X')
      (live := Block.idents rest ++ live) h1 (PImp.virtK trivial hX) hC
      (hA.mono fun y hy => by simpa [Block.idents] using hy)
    rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
    obtain ⟨evs2', o', h2', hm2, hO⟩ := drun_agr hE h2 hX hO1.2 hO1.1
    have hV : VirtK (.normal σ1) X' = VirtK (.normal σ1') X' := funext fun o => by cases o <;> rfl
    exact ⟨evs1' ++ evs2', o', .cons_normal (hV ▸ h1') h2', by simp [hm1, hm2], hO⟩
  | _, _, _, _, _, .cons_exit (rest := rest) h1, X', live, _, hX, hC, hA => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := drunS_agr hE (live := Block.idents rest ++ live) h1
      (X' := fun o => match o with
        | .normal σv => ShL F rest σv X'
        | .exit l' σx => X' (.exit l' σx))
      (fun
        | .normal _, .normal _, _, h => shL_transfer hX h
        | .exit _ _, .exit _ _, ho, h => hX _ _ ho h
        | .normal _, .exit _ _, ho, _ | .exit _ _, .normal _, ho, _ => ho.elim) hC
      (hA.mono fun y hy => by simpa [Block.idents] using hy)
    rcases o1' with _ | ⟨l', σ1'⟩ <;> simp only [OAgree] at hO1
    obtain ⟨rfl, hA1, hC1⟩ := hO1
    exact ⟨evs1', _, .cons_exit h1', hm1, rfl, hA1.mono fun _ => List.mem_append_right _, hC1⟩
/-- **An annotated statement run, replayed**: `drun_agr` for one statement. -/
private theorem drunS_agr [BEq P.Ident] [LawfulBEq P.Ident] [LawfulHasVal P] (hE : EvCongr F) :
    ∀ {X : Outcome P → Prop} {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}
    {o : Outcome P}, DRunS F X s σ evs o → ∀ {X' : Outcome P → Prop} {live : List P.Ident}
    {σ' : SemanticStore P}, PImp X X' → WellFormedStore σ F → Agree (Stmt.idents s ++ live) σ σ' →
    ∃ evs' o', DRunS F X' s σ' evs' o' ∧ evs'.map Event.obs = evs.map Event.obs ∧ OAgree F live o o'
  | _, _, _, _, _, .cmd (c := .cmd c) h, _, _, _, _, hC, hA =>
    (cmd_sim hE h hC hA).elim fun _ ⟨evs', h', hm, hO⟩ => ⟨evs', _, .cmd h', hm.map_obs hE, hO⟩
  | _, _, _, _, _, .cmd (c := .call _ _ _) h, _, _, _, _, _, _ => h.elim
  | X, _, σ, _, _, .ite_true (ess := B) hc h hsh, X', live, σ', hX, hC, hA
  | X, _, σ, _, _, .ite_false (tss := B) hc h hsh, X', live, σ', hX, hC, hA => by
    simp only [Stmt.idents, List.append_assoc, ExprOrNondet.getVars_det] at hA
    have hP : PImp (fun o' => X (o'.proj σ)) (fun o' => X' (o'.proj σ')) :=
      fun a b hab => hX _ _ (OSame.proj σ σ' hab)
    obtain ⟨evs', o', h', hm, hO⟩ := drun_agr hE (live := Block.idents B ++ live) h hP hC
      (hA.mono fun y hy => by simp only [List.mem_append] at hy ⊢; grind)
    have hc' := (ev_agree hE hC hA fun _ h => List.mem_append_left _ h).trans hc
    refine ⟨evs', _, ?_, hm,
      (hO.mono fun _ => List.mem_append_right _).proj (hA.mono fun y hy => by simp [hy])⟩
    first
      | exact .ite_true hc' h' (shB_transfer (PImp.virtK hO.same hP) hsh)
      | exact .ite_false hc' h' (shB_transfer (PImp.virtK hO.same hP) hsh)
  | _, _, σ, _, _, .block (l := l) h, _, live, σ', hX, hC, hA =>
    (drun_agr hE h (fun _ _ hab => hX _ _ (OSame.block l σ σ' hab)) hC hA).elim
      fun _ ⟨_, h', hm, hO⟩ =>
        ⟨_, _, .block h', hm, hO.block l (hA.mono fun _ => List.mem_append_right _)⟩
  | _, _, _, _, _, .exit, _, _, _, _, hC, hA =>
    ⟨[], _, .exit, rfl, rfl, hA.mono fun _ => List.mem_append_right _, hC⟩
  | _, _, _, _, _, .typeDecl, _, _, _, _, hC, hA =>
    ⟨[], _, .typeDecl, rfl, hA.mono fun _ => List.mem_append_right _, hC⟩
end

omit iSF iHI iLI iWL iOp iLF iLFs iHa iBE iLB in
mutual
/-- **An annotated reach, replayed.**  An annotated reach of `ss` from the value-valued `σ`
    gives one of `ss` from any store agreeing with `σ` on the identifiers of `ss`, observed
    alike. -/
private theorem dreach_agr [BEq P.Ident] [LawfulBEq P.Ident] (hE : EvCongr F) :
    ∀ {ss : PStmts P} {σ : SemanticStore P} {evs : List (Event P)}, DReach F ss σ evs →
    ∀ {σ' : SemanticStore P}, WellFormedStore σ F → Agree (Block.idents ss) σ σ' →
    ∃ evs', DReach F ss σ' evs' ∧ evs'.map Event.obs = evs.map Event.obs
  | _, _, _, .here h, _, hC, hA =>
    (dreachS_agr hE h hC (hA.mono fun _ => List.mem_append_left _)).imp fun _ h => ⟨.here h.1, h.2⟩
  | _, _, _, .later (rest := rest) h1 h2, _, hC, hA => by
    obtain ⟨evs1', o1', h1', hm1, hO1⟩ := drunS_agr hE (X' := fun _ => True)
      (live := Block.idents rest) h1 (fun _ _ _ _ => trivial) hC (by simpa [Block.idents] using hA)
    rcases o1' with σ1' | _ <;> simp only [OAgree] at hO1
    obtain ⟨evs2', h2', hm2⟩ := dreach_agr hE h2 hO1.2 hO1.1
    exact ⟨evs1' ++ evs2', .later h1' h2', by simp [hm1, hm2]⟩
/-- **An annotated statement reach, replayed**: `dreach_agr` for one statement. -/
private theorem dreachS_agr (hE : EvCongr F) :
    ∀ {s : PStmt P} {σ : SemanticStore P} {evs : List (Event P)}, DReachS F s σ evs →
    ∀ {σ' : SemanticStore P}, WellFormedStore σ F → Agree (Stmt.idents s) σ σ' →
    ∃ evs', DReachS F s σ' evs' ∧ evs'.map Event.obs = evs.map Event.obs
  | _, _, _, .cmd (c := .cmd c) h, _, hC, hA => by
    obtain ⟨_, evs', h', hm, -⟩ := cmd_sim hE (N := []) h hC (by simpa using hA)
    exact ⟨evs', .cmd h', hm.map_obs hE⟩
  | _, _, _, .cmd (c := .call _ _ _) h, _, _, _ => h.elim
  | _, _, _, .ite_true hc h, _, hC, hA | _, _, _, .ite_false hc h hsh, _, hC, hA => by
    simp only [Stmt.idents, List.append_assoc, ExprOrNondet.getVars_det] at hA
    obtain ⟨evs', h', hm⟩ := dreach_agr hE h hC (hA.mono fun y hy => by simp [hy])
    have hc' := (ev_agree hE hC hA fun _ h => List.mem_append_left _ h).trans hc
    first
      | exact ⟨evs', .ite_true hc' h', hm⟩
      | exact ⟨evs', .ite_false hc' h' (shB_transfer (fun _ _ _ _ => trivial) hsh), hm⟩
  | _, _, _, .block h, _, hC, hA => (dreach_agr hE h hC hA).imp fun _ h => ⟨.block h.1, h.2⟩
end

omit iLV iDE iHB iHF iSF iHI iLI iWL iOp iLF iLFs in
/-- Every identifier of a well-scoped list is read by it, or is a local outside its scope. -/
private theorem idents_wfl {Lc : List P.Ident} (ss : PStmts P) : ∀ {S : List P.Ident},
    Block.WellScoped Lc S ss → ∀ y ∈ Block.idents ss, y ∈ Block.freeVars ss ∨ (y ∈ Lc ∧ y ∉ S) := by
  induction ss using stmtsInits.induct <;> intro S hwf y hy
  case' case6 s _ _ _ _ _ _ => rcases s with ⟨⟨⟨_, _, _ | _, _⟩ | ⟨_, _ | _, _⟩ | _⟩ | _⟩ | _
  all_goals (try cases ‹ExprOrNondet P›) <;> simp only [Block.WellScoped, Stmt.WellScoped,
    Block.idents, Stmt.idents, Block.freeVars, Stmt.freeVars, ← mem_exprFV,
    ExprOrNondet.getVars_det, List.mem_append, List.mem_cons] at * <;> grind

/-- The store `σ` restricted to the variables of `S` that `V` contains. -/
@[expose] def restrictStore (S V : List P.Ident) (σ : SemanticStore P) : SemanticStore P :=
  fun x => if S.contains x && V.contains x then σ x else none

omit iHI iLI iWL iOp iLF iLFs in
/-- A reach of a well-scoped loop-free list from `σ` whose off-path runs exist (`DReach`) and whose
    trace fails the target `t` on a feasible path at an event of kind `k` with the condition `c`
    (`ClaimK`) gives such a reach from `σ` restricted to the variables of `S` the list reads, when
    the locals outside `S` are undefined in `σ`. -/
theorem claimK_restrict {F : P.Factory} (hF : WellFormedSemanticEvalBase F)
    {Lc S : List P.Ident} {ss : PStmts P} (hwf : Block.WellScoped Lc S ss)
    (hVS : ∀ x ∈ Block.freeVars ss, x ∈ S)
    {σ : SemanticStore P} (hundef : ∀ x ∈ Lc, x ∉ S → σ x = none) (hC : WellFormedStore σ F)
    {tr : List (Event P)} (hb : DReach F ss σ tr) {t : AssertId P} {c : P.Expr} {k : Bool}
    (hc : ClaimK k t c tr) :
    ∃ tr', DReach F ss (fun x => if S.contains x && (contFV [ss]).contains x then σ x else none)
      tr' ∧ ClaimK k t c tr' := by
  have hA : Agree (Block.idents ss) σ (restrictStore S (contFV [ss]) σ) :=
    ⟨fun _ hy => by grind [restrictStore, idents_wfl _ hwf, mem_contFV],
      storeAgreement_iff.2 fun _ => by grind [restrictStore]⟩
  exact (dreach_agr (evCongr_of_congr hF.exprCongr) hb hC hA).imp fun _ h =>
    ⟨h.1, claimK_obs h.2 hc⟩

omit iHI iLI iWL iOp iLF iLFs in
/-- A failure of a well-scoped loop-free list from `σ`, along a run whose off-path runs exist, at
    an occurrence of condition `e`, is one from `σ` restricted to the variables of `S` the list
    reads, when the locals outside `S` are undefined in `σ`. -/
theorem fails_restrict {F : P.Factory} (hF : WellFormedSemanticEvalBase F) {Lc S : List P.Ident}
    {ss : PStmts P} (hwf : Block.WellScoped Lc S ss) (hVS : ∀ x ∈ Block.freeVars ss, x ∈ S)
    {σ : SemanticStore P}
    (hundef : ∀ x ∈ Lc, x ∉ S → σ x = none) (hC : WellFormedStore σ F) {t : AssertId P}
    {e : P.Expr} (h : FailsD F ss σ t e) :
    FailsD F ss (fun x => if S.contains x && (contFV [ss]).contains x then σ x else none) t e := by
  obtain ⟨evs, ev, hb, hfeas, hfe, -⟩ := h
  obtain ⟨k, hk⟩ := Claim.kind ⟨evs, ev, rfl, hfeas, hfe⟩
  obtain ⟨_, hb', evs', _, rfl, hf, hfe', hce'⟩ := claimK_restrict hF hwf hVS hundef hC hb hk
  exact ⟨evs', _, hb', hf, hfe', by cases k <;> exact hce'⟩

end -- public section

end WP
end Imperative

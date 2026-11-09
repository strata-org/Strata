/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSAEval
public import Strata.DL.Imperative.Logic.TraceRelations
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.BigStep.SemProps


/-! # The SSA phase preserves failures and replays traces

A failing occurrence of a target that a guarded program reaches on a feasible path from a store
`σL` is also reached by its obligation program from any store `σS` holding, under the entry
names, the values `σL` gives the free variables: an occurrence of the same target whose condition
is the guarded occurrence's under the substitution of the SSA entry of an obligation with its
label (`ssaEntry_over`).  The proof is an induction on the
guarded program along the traversal, with the two stores agreeing on the free variables of the
rest of the list (`SAgree`); folding is a refinement of evaluation (`evalsTo_foldE`).

Along the same induction, every reach and every run of the guarded program has a counterpart in
the obligation program whose trace is the source trace with its assumptions weakened
(`Trace.WeakensAssumes evalInterp`, `ssaEntry_sim`); for runs, every arm of every `ite *` must
contain an obligation (`Block.armsHaveChecks`), so that the phase drops no arm.  The facts about the
evaluator these proofs use are those of `SSAEval`.

Key theorems: `ssaEntry_over`, `ssaEntry_sim`, `Block.treeForm_allSubstmts`.

Key definitions: `SDom`, `SClaim`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]
  [iOp : HasOps P] [iLFv : LawfulHasFvar P] [iLFvs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iOp iLFv iLFvs
variable {F : P.Factory} {σS σL σ σS' σS1 : SemanticStore P} {x y : P.Ident} {D : List P.Ident}
  {t : AssertId P} {A : AvoidSet P} {n0 n : Nat} {w : P.Val} {ρ : Std.HashMap P.Ident (SVal P)}
  {out o : PStmts P} {tr evs : List (Event P)} {s s1 : SSt P} {cond : P.Expr}


/-! ## Agreement of the two stores

The guarded store `σL` and the obligation store `σS` agree on a name `x` under the SSA mapping
`ρ` when `x` has a value `w` in `σL` that its current value holds in `σS` (`SHolds`). -/

omit iDE iBE iHF iSF iHI iHa iHFs iLV in
/-- `SHolds` survives the growth of the obligation store. -/
private theorem SHolds.mono (hm : StoreAgreement σS σS')
    : ∀ {o : Option (SVal P)}, SHolds F σS x w o → SHolds F σS' x w o
  | o, h => by
    have := storeAgreement_supplies_mono_premise _ _ hm
    rcases o with _ | _ | _ <;> grind [SHolds]

omit iDE iBE iHF iSF iHI iHa iHFs iLV in
/-- The value a current value holds has the type the current value gives `x`. -/
private theorem SHolds.ty {F : P.Factory} {σS : SemanticStore P} {x : P.Ident} {w : P.Val}
    {ty : P.Ty} : ∀ {o : Option (SVal P)}, SHolds F σS x w o →
      (o.getD (.name x none)).ty? = some ty → HasVal.valueOfTy F w ty
  | o, h, hty => by rcases o with _ | (_ | _) <;> grind [SHolds, SVal.ty?, bool_valueOfTy]

omit iDE iLB iHF iSF iHI iHFs iLV in
/-- Agreement on `y` survives a step that keeps the guarded value and the current value of `y`
    and grows the obligation store. -/
private theorem SAgree.transfer {F : P.Factory} {ρ ρ' : Std.HashMap P.Ident (SVal P)}
    {σL σL' σS σS' : SemanticStore P} {y : P.Ident} (h : SAgree F ρ σL σS y)
    (hL : σL' y = σL y) (hρ : ρ'[y]? = ρ[y]?) (hm : StoreAgreement σS σS') :
    SAgree F ρ' σL' σS' y :=
  h.imp fun _ ⟨h1, h2⟩ => ⟨hL ▸ h1, hρ ▸ h2.mono hm⟩

/-! ## Names of the obligation store

The obligation store binds only names of a list `Dc` of names that are names of `D` or fresh
names with a counter at least `n0` outside the avoided names, and that a fresh name with a
counter at least the current one is never in (`SDom`). -/

/-- The obligation store `σS` binds only names that are in `D` or are fresh names with a counter
    at least `n0` outside `A`, and no fresh name with a counter at least `n` outside `A`. -/
@[expose] def SDom (A : AvoidSet P) (D : List P.Ident) (n0 : Nat) (σS : SemanticStore P)
    (n : Nat) : Prop :=
  ∃ Dc, NamesOK A.toList Dc n ∧ SemanticStore.DomIn σS Dc ∧
    ∀ z ∈ Dc, z ∈ D ∨ ∃ b j, n0 ≤ j ∧ z = freshName b j ∧ z ∉ A.toList

omit iLI iWL iLV in
/-- `SDom` holds for a larger counter. -/
private theorem SDom.le {n' : Nat} (h : SDom A D n0 σS n) (hn : n ≤ n') : SDom A D n0 σS n' :=
  h.imp fun _ ⟨hN, hD, hz⟩ => ⟨fun y hy b j hj => hN y hy b j (Nat.le_trans hn hj), hD, hz⟩

omit iLI iWL iLV in
/-- A name bound in the obligation store is in `D` or a fresh name with a counter at least `n0`
    outside the avoided names. -/
private theorem SDom.bound (h : SDom A D n0 σS n) {z : P.Ident} (hz : (σS z).isSome) :
    z ∈ D ∨ ∃ b j, n0 ≤ j ∧ z = freshName b j ∧ z ∉ A.toList :=
  h.elim fun _ ⟨_, hD, hm⟩ => hm z (hD z hz)

omit iLV in
/-- A fresh name of the traversal is unbound in the obligation store, and binding it to a value
    keeps `SDom` at the advanced counter, grows the store and keeps it value-valued. -/
private theorem SDom.fresh (h : SDom A D n0 σS s.next) (hA : s.avoid = A) (hn : n0 ≤ s.next)
    (hf : sFresh x s = .ok (y, s1)) (hC : WellFormedStore σS F) {v : P.Val}
    (hv : HasVal.value F v) :
    σS y = none ∧ SDom A D n0 (SemanticStore.update σS y v) s1.next ∧
      StoreAgreement σS (SemanticStore.update σS y v) ∧
      WellFormedStore (SemanticStore.update σS y v) F ∧
      s1 = { s with next := s1.next } := by
  obtain ⟨j, hj, rfl, hy, rfl⟩ := sFresh_ok hf
  obtain ⟨Dc, hN, hD, hm⟩ := h
  subst hA
  have h0 : σS (freshName (baseOf x) j) = none :=
    Option.not_isSome_iff_eq_none.mp fun hs => hN.fresh_not_mem hj hy (hD _ hs)
  refine ⟨h0, ⟨_ :: Dc, hN.add_fresh (baseOf x) hj, ?_, ?_⟩,
    storeAgreement_storeWith _ _ _ _ (StoreAgreement.refl _) h0, wfStore_update hC _ hv, rfl⟩
  all_goals grind [SemanticStore.update, SemanticStore.DomIn]

/-! ## Assignments -/

omit iLV in
/-- **An assignment of the obligation program.**  When the guarded value of `x := e` is `v0`
    (of type `ty`) under agreement on the free variables of `e`, the output of `assignVal` runs
    from the obligation store to a larger one in which the recorded value of `x` holds `v0`. -/
private theorem ssaAssign_sim (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) {ty : P.Ty} {e : P.Expr} {v : SVal P} {v0 : P.Val}
    (h : assignVal x ty e s = .ok ((o, v), s1))
    (hA : ∀ y ∈ HasFvars.getFvars e, SAgree F s.ρ σL σS y) (he : EvalsTo F σL e v0)
    (hty : HasVal.valueOfTy F v0 ty) (hD : SDom A D n0 σS s.next) (hav : s.avoid = A)
    (hn : n0 ≤ s.next) :
    ∃ σS1, BRun F o σS [] (.normal σS1) ∧ StoreAgreement σS σS1 ∧ WellFormedStore σS1 F ∧
      SDom A D n0 σS1 s1.next ∧ SHolds F σS1 x v0 (some v) ∧ s1 = { s with next := s1.next } := by
  have hev := evalsTo_foldE hF hCL hCS s.ρ e hA he
  have hval := hev.value hF.val hCS
  rcases assignVal_ok h with ⟨b, x', hb, hf, rfl, rfl⟩ | ⟨y, hy, -, rfl, rfl, rfl⟩ |
    ⟨x', hf, rfl, rfl⟩
  · obtain rfl := evalsTo_boolLit hF hb hev
    obtain ⟨h0, hD1, hm, hC1, hs⟩ := hD.fresh hav hn hf hCS hval
    refine ⟨_, run_init hF h0 (bool_valueOfTy ?_) fun _ h => ExprOrNondet.det.inj h ▸
      evalsTo_lit F hF _ b, hm, hC1, hD1, ?_, hs⟩
    all_goals cases b <;> simp [SHolds, SemanticStore.update]
  · exact ⟨σS, .nil, StoreAgreement.refl _, hCS, hD, ⟨hev.var hF.var hCS hy,
      fun T h => Option.some.inj h ▸ hty⟩, rfl⟩
  · obtain ⟨h0, hD1, hm, hC1, hs⟩ := hD.fresh hav hn hf hCS hval
    exact ⟨_, run_init hF h0 hty fun _ h => ExprOrNondet.det.inj h ▸ hev, hm, hC1, hD1,
      by simp [SHolds, SemanticStore.update, hty], hs⟩

/-! ## Obligations -/

omit iLI iLV in
/-- **An obligation of the traversal.**  The condition the traversal emits for a guarded
    obligation on the condition `e` is `e` under the substitution of its entry, with the facts of
    `SClaim` on that substitution. -/
private theorem obl_claim (hD : SDom A D n0 σS n) {e : P.Expr}
    (hA : ∀ x ∈ HasFvars.getFvars e, SAgree F ρ σL σS x) :
    renM' ρ e = substObl (oblSubS ρ e) e ∧
      (∀ q ∈ oblSubS ρ e, q.1 ∈ exprFV e) ∧
      ∀ y ∈ exprFV e, (∃ z ty, (y, z, ty) ∈ oblSubS ρ e) ∨ y ∈ D ∨
        ∃ b j, n0 ≤ j ∧ y = freshName b j ∧ y ∉ A.toList := by
  refine ⟨?_, fun q hq => ?_, fun y hy => ?_⟩
  · refine WPLang.substFn_eq _ _ _ fun x hx => ?_
    refine (Map.find?_filterMap_self
      (fun z => (oblVar ρ z).map fun (y, ty) => HasFvar.mkVar y ty) _ x
      (mem_exprFV.2 hx)).symm.trans ?_
    simp only [oblSubS, List.map_filterMap, Option.map_map]
    rfl
  · grind [oblSubS, Option.map_eq_some_iff]
  · obtain ⟨w, -, ho⟩ := Exists.imp (fun _ => And.imp_right oblVar_holds) (hA y (mem_exprFV.1 hy))
    rcases hov : oblVar ρ y with _ | ⟨z, ty⟩ <;> rw [hov] at ho
    · exact .inr (hD.bound (by simp [ho]))
    · exact .inl ⟨z, ty, List.mem_filterMap.2 ⟨y, hy, by rw [hov]; rfl⟩⟩

/-! ## The simulation -/

/-- A reach of the obligation program `out` from `σS` claims a failure of the target `t` at an
    occurrence whose condition is `e` under the substitution `ssub` of an entry
    `obl t.label ssub` of `obls`, whose keys are free variables of `e`; every free variable of
    `e` without an entry is in `D` or a fresh name with a counter at least `n0` outside `A`. -/
@[expose] def SClaim (F : P.Factory) (t : AssertId P) (e : P.Expr) (A : AvoidSet P)
    (D : List P.Ident) (n0 : Nat) (out : PStmts P) (σS : SemanticStore P)
    (obls : List (Option (LogEntry P))) : Prop :=
  ∃ ssub tr, some (.obl t.label ssub) ∈ obls ∧ BReach F out σS tr ∧
    Claim t (substObl ssub e) tr ∧ (∀ q ∈ ssub, q.1 ∈ exprFV e) ∧
    ∀ y ∈ exprFV e, (∃ z ty, (y, z, ty) ∈ ssub) ∨ y ∈ D ∨
      ∃ b j, n0 ≤ j ∧ y = freshName b j ∧ y ∉ A.toList

omit iLI iWL iLV in
/-- `SClaim` holds for more choice-record entries and for any list a reach of `out` is a
    reach of. -/
private theorem SClaim.mono {out' : PStmts P} {obls obls' : List (Option (LogEntry P))}
    (h : SClaim F t cond A D n0 out σS obls) (ho : ∃ l, obls' = l ++ obls)
    (hr : ∀ {tr}, BReach F out σS tr → ∃ tr0, BReach F out' σS' (tr0 ++ tr) ∧
      Trace.AssumptionsHold P evalInterp () tr0) : SClaim F t cond A D n0 out' σS' obls' :=
  let ⟨_, _, hm, hb, hc, hk⟩ := h
  let ⟨_, hb', hf⟩ := hr hb
  ⟨_, _, ho.elim fun l hl => hl ▸ List.mem_append_right l hm, hb', claim_prepend hf hc, hk⟩

omit iHF iSF iHI iHFs iLV in
/-- Agreement after an assignment of `x`: on `x`, from the value the new current value holds;
    on the other names of `V`, from the agreement before. -/
private theorem SAgree.assign {σL1 : SemanticStore P} {v : SVal P} {V : List P.Ident}
    (hx : SHolds F σS1 x w (some v)) (hx1 : σL1 x = some w) (hfr : ∀ y, x ≠ y → σL1 y = σL y)
    (hm : StoreAgreement σS σS1)
    (hold : ∀ y ∈ V, y ≠ x → SAgree F ρ σL σS y) : ∀ y ∈ V, SAgree F (ρ.insert x v) σL1 σS1 y :=
  fun y hy => by by_cases h : x = y <;> grind [SAgree, SAgree.transfer]

/-- **The traversal preserves failures.**  A failure of the target `t` at an occurrence of
    condition `cond` reached by a guarded list from `σL` is one of the traversal's output from
    `σS` at an occurrence of `cond` under a recorded substitution (`SClaim`), when the two stores
    agree on the free variables of the list and the obligation store binds only the names `SDom`
    allows. -/
private theorem ssaList_over (hF : SSALaws F) (t : AssertId P) (cond : P.Expr) (A : AvoidSet P)
    (D : List P.Ident) (n0 : Nat) (ss : PStmts P) :
    ∀ {s s' : SSt P} {out : PStmts P}, ssaList ss s = .ok (out, s') →
    ∀ {σL σS : SemanticStore P} {tr : List (Event P)}, s.avoid = A → n0 ≤ s.next →
    (∀ x ∈ Block.freeVars ss, SAgree F s.ρ σL σS x) → WellFormedStore σL F → WellFormedStore σS F →
    SDom A D n0 σS s.next → BReach F ss σL tr → Claim t cond tr →
    SClaim F t cond A D n0 out σS s'.obls := by
  intro s s' out h
  refine no_implicit_lambda% (ssaList_ind (fun _ _ _ _ _ _ _ _ _ _ hR => by cases hR) ?initDet
    ?initNondet ?setDet ?setNondet ?assume ?check ?ite ?typeDecl h)
  case' initDet => intro x ty _ _ _ s _ _ _ _ _ h1 ih _ σS _ hav hn hA hCL hCS hD hR hC
  case' setDet => intro x _ _ _ s ty _ _ _ _ _ hc h1 ih _ σS _ hav hn hA hCL hCS hD hR hC
  case' initNondet => intro x ty _ _ s x' _ _ _ h1 ih _ σS _ hav hn hA hCL hCS hD hR hC
  case' setNondet => intro x _ _ s ty x' _ _ _ hc h1 ih _ σS _ hav hn hA hCL hCS hD hR hC
  case initDet | setDet | initNondet | setNondet =>
    obtain ⟨σL1, _, hE, hC1⟩ := reach_cmd_claim hR hC
    first
    | obtain ⟨v0, he, -, hx1, hfr, rfl, hty⟩ := evalE_init_det_inv_typed hE
    | obtain ⟨v0, hty, -, hx1, hfr, rfl⟩ := evalE_init_nondet_inv_typed hE
    | obtain ⟨v0, he, ⟨prev, T, hp, hpT, hvT⟩, hx1, hfr, rfl⟩ := evalE_set_det_inv hE
    | obtain ⟨v0, ⟨prev, T, hp, hpT, hvT⟩, hx1, hfr, rfl⟩ := evalE_set_nondet_inv hE
    obtain ⟨tr', hR', -, hC'⟩ := hC1.resolve_left Claim.not_nil
    try
      obtain ⟨w, hw, hh⟩ := hA x (by simp [Block.freeVars, Stmt.freeVars])
      have hty := LawfulHasVal.valueOfTy_congr F w v0 ty T (hh.ty (curTy_ok hc).2)
        (Option.some.inj (hp.symm.trans hw) ▸ hpT) hvT
    first
    | obtain ⟨σS1, hrun, hm, hC1, hD1, hx, hs1⟩ := ssaAssign_sim hF hCL hCS h1
        (fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy])) he hty hD
        hav hn
      have hf := assignVal_frame h1
      have hv0 := EvalsTo.value hF.val hCL he
    | have hv0 := LawfulHasVal.valueOfTy_isVal _ _ _ hty
      obtain ⟨h0, hD1, hm, hC1, hs1⟩ := hD.fresh hav hn h1 hCS hv0
      have hf := sFresh_frame h1
      have hrun := run_init (e := .nondet) hF h0 hty fun _ h => by cases h
      have hx : SHolds F _ x v0 (some (.name x' (some ty))) :=
        ⟨(update_facts σS x' v0).1, fun T hT => by cases hT; exact hty⟩
    exact (ih (by simp [SSt.defd, SSt.bound, hf.1, hav]) (Nat.le_trans hn hf.2.1)
      (SAgree.assign hx hx1 hfr hm fun y hy hne => hs1 ▸ hA y
        (by simp [Block.freeVars, Stmt.freeVars, hy, hne]))
      (evalCmdE_storeWellDefined hF.val hE hCL) hC1 hD1 hR' hC').mono ⟨[], rfl⟩
      (reach_after_run hrun)
  case assume =>
    intro l a md rest s out' s' ih σL σS tr hav hn hA hCL hCS hD hR hC
    obtain ⟨σ1, evs, hE, hC1⟩ := reach_cmd_claim hR hC
    cases hE
    obtain ⟨tr', hR', hf, hc⟩ := hC1.resolve_left fun h => (claim_single h).elim
    have hev := evalsTo_foldE hF hCL hCS s.ρ a
      (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hx]))
      (evalInterp_holds_iff.1 (hf _ (.head _)))
    have hS := ih hav hn (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, hx]))
        hCL hCS hD hR' hc
    split
    · exact hS
    · refine hS.mono ⟨[], rfl⟩ fun hb => reach_after_stmt (.cmd (by exact .eval_assume)) ?_ hb
      exact fun _ hc => by cases List.mem_singleton.1 hc; exact evalInterp_holds_iff.2 hev
  case check =>
    intro mk l e md rest s out' s' hmk h' ih σL σS tr hav hn hA hCL hCS hD hR hC
    have hmem := (ssaList_frame rest h').2.2.1.elim fun l' hl =>
      hl ▸ List.mem_append_right l' (.head _)
    obtain ⟨σ1, evs, hE, hc | ⟨tr', hR', hf, hc⟩⟩ := reach_cmd_claim hR hC
    · rcases hmk with rfl | rfl <;> cases hE
      all_goals
        have hA' : ∀ x ∈ HasFvars.getFvars e, SAgree F s.ρ σL σS x :=
          fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hx])
        have hfa := claim_single hc
        obtain rfl : e = cond := hfa.2.2.1
        obtain ⟨h1, h3, h4⟩ := obl_claim hD hA'
        obtain ⟨hl, hmd, -, hv⟩ :=
          failsAt_transfer (by simp) (fun _ => evalsTo_renM' hF hCL hCS hA') hfa
        refine ⟨_, _, hl ▸ hmem, .here (.cmd (by constructor)), ⟨[], _, rfl, nofun, ?_⟩, h3, h4⟩
        exact ⟨hl, hmd, h1, hv⟩
    · rcases hmk with rfl | rfl <;> cases hE <;>
        exact (ih hav hn (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, hx]))
            hCL hCS hD hR' hc).mono
          ⟨[], rfl⟩ fun hb => reach_after_stmt (.cmd (by constructor)) (fun _ h => by simp at h) hb
  case ite =>
    intro tss ess md s t' sT sU e' out' s' hT ihT hU hE ihE ho1 ho2 ho3 σL σS tr hav hn hA hCL hCS
      hD hR hC
    obtain ⟨⟨ha, hn', -⟩, hρU⟩ := undoTo_frame (ssaList_frame _ hT) hU
    obtain rfl := undoTo_ok hU
    obtain ⟨-, -, ho, -⟩ := ssaList_frame _ hE
    rcases hR with ⟨_ | ⟨_, _⟩ | ⟨_, _⟩ | hRT | hRE | _⟩ | ⟨-, ⟨⟩⟩
    · have hcT := ihT hav hn (fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy]))
          hCL hCS hD hRT hC
      have hne : t' ≠ [] := fun h => by obtain ⟨_, _, _, ⟨⟩, _⟩ := h ▸ hcT
      refine hcT.mono ho fun hR0 => ⟨[], ?_, nofun⟩
      by_cases he : e' = [] <;> simp only [ho2 hne, ho3 hne, he, ne_eq, not_false_eq_true] <;>
        first | exact hR0 | exact .here (.ite_nondet_true hR0)
    · have hcE := ihE (ha.trans hav) (Nat.le_trans hn hn')
        (fun y hy => (hA y (by simp [Block.freeVars, Stmt.freeVars, hy])).transfer rfl (hρU y)
          (StoreAgreement.refl _))
        hCL hCS (hD.le hn') hRE hC
      have hne : e' ≠ [] := fun h => by obtain ⟨_, _, _, ⟨⟩, _⟩ := h ▸ hcE
      refine hcE.mono ⟨[], rfl⟩ fun hR0 => ⟨[], ?_, nofun⟩
      by_cases ht : t' = [] <;> simp only [ho1, (ho3 · hne), ht, ne_eq, not_false_eq_true] <;>
        first | exact hR0 | exact .here (.ite_nondet_false hR0)
  case typeDecl =>
    intro tc md rest s out' s' ih σL σS tr hav hn hA hCL hCS hD hR hC
    rcases hR with ⟨⟨⟩⟩ | ⟨⟨⟩, hR⟩
    exact ih hav hn hA hCL hCS hD hR hC

/-! ## The trace simulation

Every reach and every run of a guarded list has a counterpart in the traversal's output, from a
store agreeing with the guarded one on the free variables, whose trace is the source trace with
its assumptions weakened (`Trace.WeakensAssumes evalInterp`); a run has one when every arm of
every `ite *` contains an obligation (`Block.armsHaveChecks`), so that the traversal drops no
arm. -/

omit iLI iLV in
/-- The traversal's output of a list containing an `assert` or a `cover` is not empty. -/
private theorem ssaList_ne_nil (ss : PStmts P) {s s' : SSt P} {out : PStmts P}
    (h : ssaList ss s = .ok (out, s')) : Block.hasCheck ss = true → out ≠ [] := by
  refine ssaList_ind (Q := fun ss _ out _ => Block.hasCheck ss = true → out ≠ [])
    (fun _ h => by simp [Block.hasCheck] at h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;> intros <;>
    (try simp only [Block.hasCheck, Stmt.hasCheck, Bool.false_or] at *) <;>
    grind [List.append_eq_nil_iff]

/-- **The traversal simulates the guarded list.**  When the two stores agree on the free
    variables of the list and the obligation store binds only the names `SDom` allows: every
    reach of the guarded list from `σL` has a target trace, empty or a reach of the output from
    `σS`, whose assumptions are weakened; and, when every arm of every `ite *` of the list
    contains an obligation, every run of the list from `σL` ends normally and has a run of the
    output from `σS` ending normally whose trace weakens the assumptions of the source's. -/
private theorem ssaList_sim (hF : SSALaws F) (A : AvoidSet P) (D : List P.Ident) (n0 : Nat)
    (ss : PStmts P) :
    ∀ {s s' : SSt P} {out : PStmts P}, ssaList ss s = .ok (out, s') →
    ∀ {σL σS : SemanticStore P}, s.avoid = A → n0 ≤ s.next →
    (∀ x ∈ Block.freeVars ss, SAgree F s.ρ σL σS x) → WellFormedStore σL F → WellFormedStore σS F →
    SDom A D n0 σS s.next →
    (∀ {tr}, BReach F ss σL tr → ∃ tr', Trace.WeakensAssumes evalInterp tr tr' ∧
      (tr' = [] ∨ BReach F out σS tr')) ∧
    (Block.armsHaveChecks ss = true → ∀ {tr o}, BRun F ss σL tr o → ∃ σL', o = .normal σL' ∧
      ∃ tr' σS', BRun F out σS tr' (.normal σS') ∧ Trace.WeakensAssumes evalInterp tr tr') := by
  intro s s' out h
  refine no_implicit_lambda% (ssaList_ind (fun _ _ _ _ _ _ _ _ _ => ⟨nofun, fun _ _ _ hR => ?nil⟩)
    ?initDet ?initNondet ?setDet ?setNondet ?assume ?check ?ite ?typeDecl h)
  case nil =>
    cases hR
    exact ⟨_, rfl, [], _, .nil, .nil⟩
  case' initDet => intro x ty _ _ _ s _ _ _ _ _ h1 ih σL σS hav hn hA hCL hCS hD
  case' setDet => intro x _ _ _ s ty _ _ _ _ _ hc h1 ih σL σS hav hn hA hCL hCS hD
  case' initNondet => intro x ty _ _ s x' _ _ _ h1 ih σL σS hav hn hA hCL hCS hD
  case' setNondet => intro x _ _ s ty x' _ _ _ hc h1 ih σL σS hav hn hA hCL hCS hD
  case initDet | setDet | initNondet | setNondet =>
    refine ⟨fun {tr} hR => ?_, fun harm {tr o} hR => ?_⟩
    case' refine_1 => rcases hR with ⟨⟨hE⟩⟩ | ⟨⟨hE⟩, hR'⟩
    case' refine_2 => rcases hR with _ | ⟨⟨hE⟩, hR'⟩ | ⟨⟨⟩⟩
    all_goals
      first
      | obtain ⟨v0, he, -, hx1, hfr, rfl, hty⟩ := evalE_init_det_inv_typed hE
      | obtain ⟨v0, hty, -, hx1, hfr, rfl⟩ := evalE_init_nondet_inv_typed hE
      | obtain ⟨v0, he, ⟨prev, T, hp, hpT, hvT⟩, hx1, hfr, rfl⟩ := evalE_set_det_inv hE
      | obtain ⟨v0, ⟨prev, T, hp, hpT, hvT⟩, hx1, hfr, rfl⟩ := evalE_set_nondet_inv hE
    all_goals try exact ⟨[], .nil, .inl rfl⟩
    all_goals
      try
        obtain ⟨w, hw, hh⟩ := hA x (by simp [Block.freeVars, Stmt.freeVars])
        have hty := LawfulHasVal.valueOfTy_congr F w v0 ty T (hh.ty (curTy_ok hc).2)
          (Option.some.inj (hp.symm.trans hw) ▸ hpT) hvT
      first
      | obtain ⟨σS1, hrun, hm, hC1, hD1, hx, hs1⟩ := ssaAssign_sim hF hCL hCS h1
          (fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy])) he hty
          hD hav hn
        have hf := assignVal_frame h1
      | have hv0 := LawfulHasVal.valueOfTy_isVal _ _ _ hty
        obtain ⟨h0, hD1, hm, hC1, hs1⟩ := hD.fresh hav hn h1 hCS hv0
        have hf := sFresh_frame h1
        have hrun := run_init (e := .nondet) hF h0 hty fun _ h => by cases h
        have hx : SHolds F _ x v0 (some (.name x' (some ty))) :=
          ⟨(update_facts σS x' v0).1, fun T hT => by cases hT; exact hty⟩
      have hI := ih (by simp [SSt.defd, SSt.bound, hf.1, hav]) (Nat.le_trans hn hf.2.1)
        (SAgree.assign hx hx1 hfr hm fun y hy hne =>
          hs1 ▸ hA y (by simp [Block.freeVars, Stmt.freeVars, hy, hne]))
        (evalCmdE_storeWellDefined hF.val hE hCL) hC1 hD1
      first
      | obtain ⟨tr', hw, h'⟩ := hI.1 hR'
        exact ⟨tr', hw, h'.imp_right (breach_append_run hrun)⟩
      | obtain ⟨σL', rfl, tr', σS', hr, hw⟩ :=
          hI.2 (by simpa [Block.armsHaveChecks, Stmt.armsHaveChecks] using harm) hR'
        exact ⟨σL', rfl, tr', σS', brun_append hrun hr, hw⟩
  case assume =>
    intro l a md rest s out' s' ih σL σS hav hn hA hCL hCS hD
    have hI := ih hav hn (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, hx])) hCL hCS hD
    have hw := Event.WeakensAssume.assume (l := l) (md := md) (evalsTo_foldE hF hCL hCS s.ρ a
      (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hx])))
    refine ⟨fun {tr} hR => ?_, fun harm {tr o} hR => ?_⟩
    · rcases hR with ⟨⟨⟨⟩⟩⟩ | ⟨⟨⟨⟩⟩, hR'⟩
      · split
        · exact ⟨[], .dropAssume .nil, .inl rfl⟩
        · exact ⟨_, .cons hw .nil, .inr (.here (.cmd (by exact .eval_assume)))⟩
      · obtain ⟨tr', h1, h2⟩ := hI.1 hR'
        split
        · exact ⟨tr', .dropAssume h1, h2⟩
        · exact ⟨_, .cons hw h1, .inr (breach_cmd_cons (evs := [_]) (by exact .eval_assume) h2)⟩
    · rcases hR with _ | ⟨⟨⟨⟩⟩, hR'⟩ | ⟨⟨⟩⟩
      obtain ⟨σL', rfl, tr', σS', h1, h2⟩ :=
        hI.2 (by simpa [Block.armsHaveChecks, Stmt.armsHaveChecks] using harm) hR'
      split
      · exact ⟨σL', rfl, tr', σS', h1, .dropAssume h2⟩
      · exact ⟨σL', rfl, _, σS', .cons_normal (evs1 := [_]) (.cmd (by exact .eval_assume)) h1,
          .cons hw h2⟩
  case check =>
    intro mk l e md rest s out' s' hmk h' ih σL σS hav hn hA hCL hCS hD
    rcases hmk with rfl | rfl
    all_goals
      have hI := ih hav hn (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, hx]))
          hCL hCS hD
      have hev := fun v => evalsTo_renM' hF hCL hCS (ρ := s.ρ) (e := e) (v := v)
        (fun x hx => hA x (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hx]))
      refine ⟨fun {tr} hR => ?_, fun harm {tr o} hR => ?_⟩
      · rcases hR with ⟨⟨⟨⟩⟩⟩ | ⟨⟨⟨⟩⟩, hR'⟩
        · exact ⟨_, .cons (Event.WeakensAssume.check (by simp) hev) .nil,
            .inr (.here (.cmd (by constructor)))⟩
        · obtain ⟨tr', h1, h2⟩ := hI.1 hR'
          exact ⟨_, .cons (Event.WeakensAssume.check (by simp) hev) h1,
            .inr (breach_cmd_cons (evs := [_]) (by constructor) h2)⟩
      · rcases hR with _ | ⟨⟨⟨⟩⟩, hR'⟩ | ⟨⟨⟩⟩
        obtain ⟨σL', rfl, tr', σS', h1, h2⟩ :=
          hI.2 (by simpa [Block.armsHaveChecks, Stmt.armsHaveChecks] using harm) hR'
        exact ⟨σL', rfl, _, σS', .cons_normal (evs1 := [_]) (.cmd (by constructor)) h1,
          .cons (Event.WeakensAssume.check (by simp) hev) h2⟩
  case ite =>
    intro tss ess md s t' sT sU e' out' s' hT ihT hU hE ihE ho1 ho2 ho3 σL σS hav hn hA hCL hCS
      hD
    obtain ⟨⟨ha, hn', -⟩, hρU⟩ := undoTo_frame (ssaList_frame _ hT) hU
    obtain rfl := undoTo_ok hU
    have hIT := ihT hav hn (fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy]))
        hCL hCS hD
    have hIE := ihE (ha.trans hav) (Nat.le_trans hn hn')
      (fun y hy => (hA y (by simp [Block.freeVars, Stmt.freeVars, hy])).transfer rfl (hρU y)
        (StoreAgreement.refl _))
      hCL hCS (hD.le hn')
    refine ⟨fun {tr} hR => ?_, fun harm {tr o} hR => ?_⟩
    · rcases hR with ⟨_ | ⟨_, _⟩ | ⟨_, _⟩ | hRT | hRE | _⟩ | ⟨-, ⟨⟩⟩
      · obtain ⟨tr', h1, h2⟩ := hIT.1 hRT
        refine ⟨tr', h1, ?_⟩
        by_cases ht : t' = []
        · exact .inl (h2.resolve_right (ht ▸ nofun))
        by_cases he : e' = []
        · exact ho2 ht he ▸ h2
        · exact ho3 ht he ▸ h2.imp_right fun h => .here (.ite_nondet_true h)
      · obtain ⟨tr', h1, h2⟩ := hIE.1 hRE
        refine ⟨tr', h1, ?_⟩
        by_cases he : e' = []
        · exact .inl (h2.resolve_right (he ▸ nofun))
        by_cases ht : t' = []
        · exact ho1 ht ▸ h2
        · exact ho3 ht he ▸ h2.imp_right fun h => .here (.ite_nondet_false h)
    · simp only [Block.armsHaveChecks, Stmt.armsHaveChecks, Bool.and_true, Bool.and_eq_true] at harm
      obtain ⟨⟨⟨hoT, hoE⟩, haT⟩, haE⟩ := harm
      obtain rfl := ho3 (ssaList_ne_nil _ hT hoT) (ssaList_ne_nil _ hE hoE)
      have hinv : ∀ {tr o'}, BRunS F (.ite .nondet tss ess md) σL tr o' →
          ∃ o : Outcome P, (∃ σL', o = .normal σL' ∧ ∃ tr' σS',
            BRun F [.ite .nondet t' e' md] σS tr' (.normal σS') ∧
            Trace.WeakensAssumes evalInterp tr tr') ∧ o' = o.proj σL := fun h => by
        rcases h with _ | _ | _ | ⟨hr⟩ | ⟨hr⟩
        · obtain ⟨σL', rfl, tr', σS', h1, h2⟩ := hIT.2 haT hr
          exact ⟨_, ⟨σL', rfl, _, _, .cons_normal (.ite_nondet_true h1) .nil, by simpa using h2⟩,
            rfl⟩
        · obtain ⟨σL', rfl, tr', σS', h1, h2⟩ := hIE.2 haE hr
          exact ⟨_, ⟨σL', rfl, _, _, .cons_normal (.ite_nondet_false h1) .nil, by simpa using h2⟩,
            rfl⟩
      rcases hR with _ | ⟨h1, ⟨⟩⟩ | ⟨h1⟩
      · obtain ⟨_, ⟨σL', rfl, tr', σS', h2, h3⟩, -⟩ := hinv h1
        exact ⟨_, rfl, tr', σS', h2, by simpa using h3⟩
      · obtain ⟨_, ⟨σL', rfl, -⟩, h⟩ := hinv h1
        cases h
  case typeDecl =>
    intro tc md rest s out' s' ih σL σS hav hn hA hCL hCS hD
    have hI := ih hav hn hA hCL hCS hD
    refine ⟨fun {tr} hR => ?_, fun harm {tr o} hR => ?_⟩
    · rcases hR with ⟨⟨⟩⟩ | ⟨⟨⟩, hR⟩
      exact hI.1 hR
    · rcases hR with _ | ⟨⟨⟩, hR⟩ | ⟨⟨⟩⟩
      exact hI.2 (by simpa [Block.armsHaveChecks, Stmt.armsHaveChecks] using harm) hR

omit iDE iHF iSF iHI iLI iWL iLV in
/-- The two stores agree on the free variables of `lay` under the entry mapping of `ρ0`, when
    each free variable `x` is defined in `σL` with the value `σS` gives `ρ0.get x` and has its
    type of `tys`. -/
private theorem entryMap_agree {tys : Tys P} {ρ0 : Ren P} {lay : PStmts P}
    (hρ : ∀ x ∈ Block.freeVars lay, σL x = σS (ρ0.get x) ∧ (σL x).isSome)
    (hty : TyOK F tys (Block.freeVars lay) (Block.freeVars lay) σL) :
    ∀ x ∈ Block.freeVars lay, SAgree F (entryMap tys ρ0) σL σS x := fun x hx => by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hρ x hx).2
  cases hp : ρ0.find? (·.1 == x) <;> grind [SAgree, SHolds, Ren.get, TyOK, entryMap_lookup]

/-- **The SSA phase preserves failures.**  If the guarded program `lay` fails the target `t` from
    the store `σL` at an occurrence whose condition is `e`, then its obligation program `so.out`
    fails `t`, from the store `σS`, at an occurrence whose condition is `e` under the substitution
    `ssub` of an entry `obl t.label ssub` the phase records.  Hypotheses:
    every free variable `x` of `lay` is defined in `σL` with the value `σS` gives its entry name
    `ρ0.get x`, and has its declared type (`TyOK`); both stores hold values; `σS` binds only names
    of `D`, and every name of `D` of the form of a fresh name the phase may introduce is avoided
    (`NamesOK`). -/
private theorem ssaBody_over (hF : SSALaws F) {st : FreshSt P} {ρ0 : Ren P} {lay : PStmts P}
    {so : SOut P} (h : ssaBody st ρ0 lay = .ok so) (hN : NamesOK st.avoid.toList D st.next)
    (hρ : ∀ x ∈ Block.freeVars lay, σL x = σS (ρ0.get x) ∧ (σL x).isSome)
    (hty : TyOK F st.tys (Block.freeVars lay) (Block.freeVars lay) σL) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) (hdom : SemanticStore.DomIn σS D) {e : P.Expr}
    (hfail : Fails F lay σL t e) :
    ∃ ssub, some (.obl t.label ssub) ∈ so.obls ∧ Fails F so.out σS t (substObl ssub e) ∧
      (∀ q ∈ ssub, q.1 ∈ exprFV e) ∧
      ∀ y ∈ exprFV e, (∃ z ty, (y, z, ty) ∈ ssub) ∨ y ∈ D ∨
        ∃ b j, st.next ≤ j ∧ y = freshName b j ∧ y ∉ st.avoid.toList := by
  obtain ⟨s1, h1, hobls⟩ := ssaBody_ok h
  obtain ⟨evs, ev, hr, hf, hfa⟩ := hfail
  obtain ⟨ssub, tr, hm, hr', ⟨evs', ev', rfl, hf', hfa'⟩, hk, hy⟩ :=
    ssaList_over hF t e st.avoid D st.next lay h1 rfl (Nat.le_refl _) (entryMap_agree hρ hty) hCL
      hCS ⟨D, hN, hdom, fun z hz => .inl hz⟩ hr ⟨evs, ev, rfl, hf, hfa⟩
  exact ⟨ssub, hobls ▸ List.mem_reverse.2 hm, ⟨evs', ev', hr', hf', hfa'⟩, hk, hy⟩

/-- **The SSA phase preserves failures.**  Let `ssaEntry G tys xs al lay` give the entry renaming
    `ρ0` and the obligation program `so.out` of the guarded program `lay`.  If `lay` fails the
    target `t` from the store `σL` at an occurrence whose condition is `e`, then `so.out` fails
    `t`, from the store `σS`, at an occurrence whose condition is `e` under the substitution
    `ssub` of an entry `obl t.label ssub` the phase records; the keys of `ssub` are free
    variables of `e`, and every free variable of `e` is a key of `ssub` or a name `σS` may
    bind.  Hypotheses: every `(a, x)` of `al` has `x` in `xs`; every free variable `x` of
    `lay` is defined in `σL` with the value `σS` gives its entry name `ρ0.get x`, and has its
    type in `tys` (`TyOK`); both stores hold values; `σS` binds only names of `D`, each an entry
    name or not of the form of a fresh name.  Hypotheses on the factory: the mainline evaluator
    laws for variables and values, and the folding law `WellFormedSemanticEvalSubstLits`. -/
theorem ssaEntry_over {F : P.Factory} (hVar : WellFormedSemanticEvalVar (P := P) F)
    (hVal : WellFormedSemanticEvalVal (P := P) F)
    (hLits : WellFormedSemanticEvalSubstLits (P := P) F) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    {σL σS : SemanticStore P} (hρ : ∀ x ∈ Block.freeVars lay, σL x = σS (ρ0.get x) ∧ (σL x).isSome)
    (hty : TyOK F tys (Block.freeVars lay) (Block.freeVars lay) σL) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) {D : List P.Ident} (hdom : SemanticStore.DomIn σS D)
    (hD : ∀ y ∈ D, y ∈ ρ0.map (·.2) ∨ ∀ b j, y ≠ freshName b j) {t : AssertId P} {e : P.Expr}
    (hfail : Fails F lay σL t e) :
    ∃ ssub, some (.obl t.label ssub) ∈ so.obls ∧ Fails F so.out σS t (substObl ssub e) ∧
      (∀ q ∈ ssub, q.1 ∈ exprFV e) ∧
      ∀ y ∈ exprFV e, (∃ z ty, (y, z, ty) ∈ ssub) ∨ y ∈ D := by
  obtain ⟨rfl, hs⟩ := ssaEntry_ok h
  obtain ⟨ssub, hm, hfs, hk, hc⟩ := ssaBody_over ⟨hVar, hVal, hLits⟩ hs
      (ssaEntryRen_namesOK _ xs al hal hD) hρ hty hCL hCS hdom hfail
  exact ⟨ssub, hm, hfs, hk, fun y hy => (hc y hy).imp_right (·.resolve_right fun ⟨_, _, _, _, hn⟩ =>
    hn (by simp [inputAvoid, AvoidSet.toList, IdSet.ofList, fails_fv hfail y hy]))⟩

/-- **The SSA phase simulates the traces of the guarded program.**  Let `ssaEntry G tys xs al lay`
    give the entry renaming `ρ0` and the obligation program `so.out` of the guarded program
    `lay`, under the hypotheses of `ssaEntry_over` on the stores `σL` and `σS`.  Then every reach
    of `lay` from `σL` emitting `tr` has a trace `tr'`, empty or emitted by a reach of `so.out`
    from `σS`, that is `tr` with its assumptions weakened (`Trace.WeakensAssumes evalInterp`:
    each assertion and cover kept with its label and metadata, holding exactly when the source's
    holds; each assumption kept, with its label and metadata, holding whenever the source's
    holds, or dropped).  When moreover every arm of every `ite *` of `lay` contains an `assert`
    or a `cover` (`Block.armsHaveChecks`), every run of `lay` from `σL` ends normally, and has a run
    of `so.out` from `σS` ending normally with such a trace. -/
theorem ssaEntry_sim {F : P.Factory} (hVar : WellFormedSemanticEvalVar (P := P) F)
    (hVal : WellFormedSemanticEvalVal (P := P) F)
    (hLits : WellFormedSemanticEvalSubstLits (P := P) F) {G : IdSet P} {tys : Tys P}
    {xs : List P.Ident} {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P}
    {so : SOut P} (h : ssaEntry G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    {σL σS : SemanticStore P} (hρ : ∀ x ∈ Block.freeVars lay, σL x = σS (ρ0.get x) ∧ (σL x).isSome)
    (hty : TyOK F tys (Block.freeVars lay) (Block.freeVars lay) σL) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) {D : List P.Ident} (hdom : SemanticStore.DomIn σS D)
    (hD : ∀ y ∈ D, y ∈ ρ0.map (·.2) ∨ ∀ b j, y ≠ freshName b j) :
    (∀ {tr}, BReach F lay σL tr → ∃ tr', Trace.WeakensAssumes evalInterp tr tr' ∧
      (tr' = [] ∨ BReach F so.out σS tr')) ∧
    (Block.armsHaveChecks lay = true → ∀ {tr o}, BRun F lay σL tr o → ∃ σL', o = .normal σL' ∧
      ∃ tr' σS', BRun F so.out σS tr' (.normal σS') ∧ Trace.WeakensAssumes evalInterp tr tr') := by
  obtain ⟨rfl, hs⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hs
  exact ssaList_sim ⟨hVar, hVal, hLits⟩ _ D _ lay h1 rfl (Nat.le_refl _) (entryMap_agree hρ hty)
      hCL hCS ⟨D, ssaEntryRen_namesOK _ xs al hal hD, hdom, fun z hz => .inl hz⟩

end -- public section

end WP
end Imperative

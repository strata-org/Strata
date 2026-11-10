/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
public import Strata.Transform.WP.WPOverEmit
public import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
public import Strata.Transform.WP.WPOverEffects
public import Strata.Transform.WP.WPReads
import Strata.DL.Imperative.BigStep.StoreAgree
public import Strata.Transform.WP.WPOverIteLaidCore
import all Strata.Transform.WP.WPOverIteLaidCore
public import Strata.Transform.WP.WPOverIteLaidNoExit
import all Strata.Transform.WP.WPOverIteLaidNoExit

/-! # The simulation through a laid-out `ite` one of whose arms always exits

When an arm of a laid-out `ite` always exits, the end of its walk is described by `LaidEnvAx`
and `LaidAxTail`: the saves, copies and restores of step 3 and of step 3b around the
always-exiting arms, the copy `qm` of the enclosing context, the copy `rEm` of the else-arm reach
and the carried merges (`laidPartsAx`).  A failure of the `ite` on the loop-free path is a hit of
its output (`LaidEnvAx.hit`), a run along its then arm (`LaidEnvAx.runThen`) or its else arm
(`LaidEnvAx.runElse`) is matched by a run of the output, and every shadow run off the path is
matched by a run of the output (`LaidEnvAx.off`), from the setting `LaidCore` and `LaidStates`.

Key definitions: `LaidEnvAx`, `LaidAxTail`.

Key theorems: `LaidEnvAx.hit`, `LaidEnvAx.runThen`, `LaidEnvAx.runElse`, `LaidEnvAx.off`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P]
  [iWL : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iIL
variable {tE : TypedEval P} {Γ : VarTyping P}

variable {F : P.Factory} {Lc : List P.Ident} {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P}
  {md : MetaData P} {st0 : WSt P} {r : WRes P} {st' : WSt P} {T : Std.HashMap P.Ident P.Ty}
  {Y : Std.HashMap P.Ident P.Ident} {items : List (Item P)} {S : List P.Ident} {Ex : P.Ident → Prop}
  {k : List (PStmts P)} {Lab : String → List P.Ident} {wc : WExpr P} {rdc : List P.Ident}
  {s1 : WSt P} {g : P.Ident} {s2 : WSt P} {rT : P.Ident} {s3 : WSt P} {κE : RE P}
  {rE? : Option P.Ident} {s4 : WSt P} {Er : WRes P} {s5 : WSt P} {Tr : WRes P} {s6 : WSt P}
  {M : List P.Ident} {sv cp rs : Rope (WItem P)} {cps : List (P.Ident × P.Ident)} {s7 : WSt P}
  {gm? : Option P.Ident} {s8 : WSt P} {cr : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))}
  {ns : List (P.Ident × P.Ident × P.Ident)} {σ σL σ1 σs σ' σE : SemanticStore P} {n : P.Ident}
  {X K : Outcome P → Prop} {evs : List (Event P)} {st : WSt P} {gv : P.Val} {iE iU : List (Item P)}
  {ss : PStmts P} {ext : List P.Ident} {qm? : Option P.Ident} {o oT oE : Outcome P}


open Lean Meta Elab Tactic in
/-- On a goal `MainRun F items σ tr σ'`: composes the latest `MainRun` hypothesis ending in `σ'`,
    preceded by the latest one ending where it starts, and so on, and closes the goal with the
    composed run up to the equations `eqs` and the reassociation of the item and event lists. -/
local elab "wp_chain" " [" eqs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let mut cur := (← whnfR (← getMainTarget)).appArg!
  let mut run : Option Expr := none
  for d in (← getLCtx).getFVars.reverse do
    let t ← instantiateMVars (← inferType d)
    if t.isAppOf ``MainRun && t.appArg! == cur then
      run ← run.elim (pure d) (mkAppM ``MainRun.append #[d, ·])
      cur := t.appFn!.appFn!.appArg!
  let some p := run | throwError "wp_chain: no run"
  evalTactic (← `(tactic| simpa only [$eqs,*, List.cons_append, List.append_assoc,
    List.nil_append, List.append_nil] using $(← Term.exprToSyntax p)))


/-- The conclusion of `Spec` for one walk from `st` to `st'` with result `r`. -/
@[expose] def SpecBody (F : P.Factory) (Lc : List P.Ident) (κ : RE P) (d : Nat) (ss : PStmts P)
    (wf : List P.Ident → Prop) (fol : Bool) (hitP : SemanticStore P → List (Event P) → Prop)
    (runP : (Outcome P → Prop) → SemanticStore P → List (Event P) → Outcome P → Prop)
    (offP : SemanticStore P → (Outcome P → Prop) → Prop) (st : WSt P) (r : WRes P)
    (st' : WSt P) : Prop :=
  ∀ T Y, FinalOK Lc st' T Y → ∀ items, resolveItems T Y r.out.toList = .ok items →
  ∀ S, wf S → (∀ x ∈ S ++ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true) →
  ∀ Ex : P.Ident → Prop,
    (∀ y, Ex y → (∀ b j, y = freshName b j → j < st.next) ∧ st'.back[y]? = none) →
  ∀ (k : List (PStmts P)) (Lab : String → List P.Ident),
    (∀ l t, st.labelDepth[l]? = some t → t ≤ d ∧ ∀ x ∈ Lab l, x ∈ contFV k ∧ x ∈ S) →
    (∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧ st.avoid.contains y = false ∧
      (∀ x : P.Ident, st.nm[x]? ≠ some y) ∧ st.back[y]? = none) →
    DeadBelow st → LiveKeys st → (∀ k, d < k → st.carries.getD k [] = []) →
    (∀ σ σL t cnd b tr, OnInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σ σL → hitP σ tr →
      ClaimK b t cnd tr → HitPost F st' r items σL t cnd b) ∧
    (fol = true → ∀ σ σL X evs o, OnInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σ σL →
      runP X σ evs o → Trace.AssumptionsHold P evalInterp () evs →
      (κ = .top ∧ ∃ l σ1, o = .exit l σ1) ∨
      ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
        RunPost F T Y Lc Ex Lab st st' r κ S (scopeAfter S ss) (contFV k) X σL' o) ∧
    (fol = true → ∀ σs σL K, OffInv F T Y Lc Ex st' κ S (contFV (ss :: k)) σL → offP σs K →
      OffPost F T Y Lc Ex st st' r κ S (scopeAfter S ss) (contFV k) items σL K)

/-- The setting of the simulation proof for a laid-out `ite` one of whose arms always exits: the
    common setting `LaidCore`, and the end of the walk as `LaidRunAx` says (the saves, copies,
    restores and copy pairs of step 3 (`sv3 cp3 rs3 cps3`, of no variable when the then arm always
    exits) and of step 3b around the then arm (`svT cpT rsT cpsT`) and the else arm
    (`svE cpE rsE cpsE`), with states `s7`, `s7T`, `s7E`, then the end `LaidTailRest`). -/
structure LaidEnvAx (F : P.Factory) (tE : TypedEval P) (Γ : VarTyping P) (Lc : List P.Ident)
    (κ : RE P) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (md : MetaData P) (st0 : WSt P) (r : WRes P) (st' : WSt P)
    (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (items : List (Item P))
    (S : List P.Ident) (Ex : P.Ident → Prop) (k : List (PStmts P))
    (Lab : String → List P.Ident) (wc : WExpr P) (rdc : List P.Ident) (s1 : WSt P)
    (g : P.Ident) (s2 : WSt P) (rT : P.Ident) (s3 : WSt P) (κE : RE P) (rE? : Option P.Ident)
    (s4 : WSt P) (Er : WRes P) (s5 : WSt P) (Tr : WRes P) (s6 : WSt P)
    (sv3 cp3 rs3 : Rope (WItem P)) (cps3 : List (P.Ident × P.Ident)) (s7 : WSt P)
    (svT cpT rsT : Rope (WItem P)) (cpsT : List (P.Ident × P.Ident)) (s7T : WSt P)
    (svE cpE rsE : Rope (WItem P)) (cpsE : List (P.Ident × P.Ident)) (s7E : WSt P) : Prop
    extends LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
       Ex k Lab wc rdc s1 g s2 rT s3 κE
      rE? s4 Er s5 Tr s6 where
  ax : Tr.ax = true ∨ Er.ax = true
  run7 : (saveRestore (if Tr.ax then [] else interSet Tr.A Er.R)).run s6 =
    .ok ((sv3, cp3, rs3, cps3), s7)
  run7T : (saveRestore (laidCT Tr Er s6 s4.clock)).run s7 = .ok ((svT, cpT, rsT, cpsT), s7T)
  run7E : (saveRestore (laidCE Er s6 s4.clock)).run s7T = .ok ((svE, cpE, rsE, cpsE), s7E)
  rest : LaidTailRest κ d wc rdc g rT κE rE? s4.clock Er Tr s6 sv3 cp3 rs3 svT cpT rsT svE cpE rsE
    cps3 cpsT cpsE s7E r st'

omit iWL iOp iLF iLFs iLV in
/-- A run of `wFreshBool b` drawing an optional name `o?` (from `s` to `s'`, with `s' = s` when
    nothing is drawn) changes only the counter and the declared types, these only at the drawn
    name, which is Boolean. -/
private theorem optFresh_facts {b : String} {o? : Option P.Ident} {s s' : WSt P}
    (h : (∃ x, o? = some x ∧ (wFreshBool b).run s = .ok (x, s')) ∨ (o? = none ∧ s' = s)) :
    s' = { s with next := s'.next, tys := s'.tys } ∧ s.next ≤ s'.next ∧
      (∀ n, (∀ x, o? = some x → n ≠ x) → s'.tys[n]? = s.tys[n]?) ∧
      ∀ x, o? = some x → Drawn s s' x ∧ s'.tys[x]? = some HasBool.boolTy := by
  rcases h with ⟨x, rfl, h⟩ | ⟨rfl, rfl⟩
  · obtain ⟨k, rfl, hav, hle, rfl⟩ := wFreshBool_facts h
    exact ⟨rfl, Nat.le_succ_of_le hle, fun n hn => by grind, fun x hx => by grind [Drawn]⟩
  · exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl, nofun⟩

/-- The end of the walk of a laid-out `ite` one of whose arms always exits (`LaidTailRest`, from
    the state `s7E` after the saves) with its names: the merge guard `gm?` (state `s8`), the copy
    `qm?` of the enclosing context (state `s9`), the copy `rEm?` of the else-arm reach (state
    `s10`), the result's flags and registrations, and its output. -/
structure LaidAxTail (κ : RE P) (d : Nat) (wc : WExpr P) (rdc : List P.Ident)
    (g rT : P.Ident) (κE : RE P) (rE? : Option P.Ident) (t0 : Nat) (E T : WRes P)
    (s6 : WSt P) (sv3 cp3 rs3 svT cpT rsT svE cpE rsE : Rope (WItem P))
    (cps3 cpsT cpsE : List (P.Ident × P.Ident)) (s7E : WSt P) (r : WRes P) (st' : WSt P)
    (gm? : Option P.Ident) (s8 : WSt P) (qm? : Option P.Ident) (s9 : WSt P)
    (rEm? : Option P.Ident) (s10 : WSt P) : Prop where
  gm : (laidNeedGm κ E (cps3.filter fun p => liveBefore s6 p.1 t0) (laidCarry T s6 cpsT)
        (laidCarry E s6 cpsE) = true ∧ ∃ x, gm? = some x ∧ (wFreshBool "g").run s7E = .ok (x, s8)) ∨
      (laidNeedGm κ E (cps3.filter fun p => liveBefore s6 p.1 t0) (laidCarry T s6 cpsT)
        (laidCarry E s6 cpsE) = false ∧ gm? = none ∧ s8 = s7E)
  qm : ((∃ q, κ = .name q) ∧ (laidCarry E s6 cpsE).isEmpty = false ∧
        ∃ x, qm? = some x ∧ (wFreshBool "r").run s8 = .ok (x, s9)) ∨
      (¬ ((∃ q, κ = .name q) ∧ (laidCarry E s6 cpsE).isEmpty = false) ∧ qm? = none ∧ s9 = s8)
  rEm : (rE?.isSome ∧ (laidCarry E s6 cpsE).isEmpty = false ∧
        ∃ x, rEm? = some x ∧ (wFreshBool "r").run s9 = .ok (x, s10)) ∨
      (¬ (rE?.isSome ∧ (laidCarry E s6 cpsE).isEmpty = false) ∧ rEm? = none ∧ s10 = s9)
  ax : r.ax = (T.ax && E.ax)
  drop : r.drop = false
  regs : r.regs.toList = T.regs.toList ++ E.regs.toList ++
    ((laidCarry T s6 cpsT).map (·.2) ++ (laidCarry E s6 cpsE).map (·.2))
  out : (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 t0) T E (laidU κ κE rT T E d)).all Rope.isNil =
        true ∧
      r.out = .nil ∧ st' = { s10 with carries := (laidCarries s10.carries T E
        (laidCarry T s6 cpsT) (laidCarry E s6 cpsE) (optVar gm?) (elseGuard κ gm? qm? rEm?)) } ∨
    (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 t0) T E (laidU κ κE rT T E d)).all Rope.isNil =
        false ∧
      r.out.toList = .init g (.known HasBool.boolTy) (some (kAnd κ wc)) ::
        (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
          (cps3.filter fun p => liveBefore s6 p.1 t0) T E (laidU κ κE rT T E d)).flatMap
          Rope.toList ∧
      r.sk = [.ite g T.sk E.sk] ∧ r.hasObl = (T.hasObl || E.hasObl) ∧
      r.A = unionSet (if T.ax then {} else T.A) (if E.ax then {} else E.A) ∧
      r.R = unionSet (unionSet T.R E.R) (Std.HashSet.ofList rdc) ∧
      (liveAdd (rdc ++ RE.vars κ)).run { s10 with carries := (laidCarries s10.carries T E
        (laidCarry T s6 cpsT) (laidCarry E s6 cpsE) (optVar gm?) (elseGuard κ gm? qm? rEm?)) } =
        .ok ((), st')

omit iLI iWL iOp iLF iLFs iLV in
/-- The end `LaidTailRest` of the walk of a laid-out `ite` names its parts as `LaidAxTail`. -/
private theorem laidTailRest_names {t0 : Nat} {E T : WRes P}
    {sv3 cp3 rs3 svT cpT rsT svE cpE rsE : Rope (WItem P)}
    {cps3 cpsT cpsE : List (P.Ident × P.Ident)} {s7E : WSt P}
    (h : LaidTailRest κ d wc rdc g rT κE rE? t0 E T s6 sv3 cp3 rs3 svT cpT rsT svE cpE rsE cps3
      cpsT cpsE s7E r st') :
    ∃ gm? s8 qm? s9 rEm? s10, LaidAxTail κ d wc rdc g rT κE rE? t0 E T s6 sv3 cp3 rs3 svT cpT rsT
      svE cpE rsE cps3 cpsT cpsE s7E r st' gm? s8 qm? s9 rEm? s10 :=
  let ⟨_, _, hg, _, _, hq, _, _, hr, ha, hd, hrg, ho⟩ := h
  ⟨_, _, _, _, _, _, hg, hq, hr, ha, hd, hrg, ho⟩

omit iWL iOp iLF iLFs iLV in
/-- How the end of the walk of a laid-out `ite` one of whose arms always exits changes the state
    after the then arm's saves (`s7T`, the saves from `s6`): the else arm's saves (to `s7E`), the
    merge guard, the copies `qm` and `rEm`, the carried merges and the live additions leave the
    state as `AfterFacts` says. -/
private theorem LaidAxTail.after {t0 : Nat} {E T : WRes P} {s7T : WSt P}
    {sv3 cp3 rs3 svT cpT rsT svE cpE rsE : Rope (WItem P)}
    {cps3 cpsT cpsE : List (P.Ident × P.Ident)} {s7E : WSt P} {s9 : WSt P} {rEm? : Option P.Ident}
    {s10 : WSt P} {ME : List P.Ident}
    (ht : LaidAxTail κ d wc rdc g rT κE rE? t0 E T s6 sv3 cp3 rs3 svT cpT rsT svE cpE rsE cps3
      cpsT cpsE s7E r st' gm? s8 qm? s9 rEm? s10)
    (h6 : s7T = { s6 with next := s7T.next, tyOf := s7T.tyOf })
    (hE : SaveFacts s7T ME svE cpE rsE cpsE s7E) :
    AfterFacts κ rdc s6 s7T gm? st'
      ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 t0) T E (laidU κ κE rT T E d)).all Rope.isNil =
          false) := by
  obtain ⟨ns, -, -, -, -, -, -, hdr, hty, hle, h7⟩ := hE
  obtain ⟨h8, hle8, ht8, hd8⟩ := optFresh_facts (ht.gm.imp (·.2) (·.2))
  obtain ⟨h9, hle9, ht9, hd9⟩ := optFresh_facts (ht.qm.imp (·.2.2) (·.2))
  obtain ⟨h10, hle10, ht10, hd10⟩ := optFresh_facts (ht.rEm.imp (·.2.2) (·.2))
  have h9n := Nat.le_trans hle9 hle10
  have hTy : ∀ n, ¬ Drawn s7T s10 n → s10.tyOf[n]? = s7T.tyOf[n]? := fun n hn => by
    rw [h10, h9, h8]
    exact hty n fun q hq => ⟨fun h => hn (h ▸ ((hdr q hq).1.mono (Nat.le_trans hle8 h9n))),
      fun h => hn (h ▸ ((hdr q hq).2.1.mono (Nat.le_trans hle8 h9n)))⟩
  have hTs : ∀ n, ¬ Drawn s7T s10 n → s10.tys[n]? = s6.tys[n]? := fun n hn => by
    rw [ht10 n fun x hx h => hn (h ▸ ((hd10 x hx).1.of_le (by rw [h9, h8, h7])
        (Nat.le_trans hle (Nat.le_trans hle8 hle9)))),
      ht9 n fun x hx h => hn (h ▸ ((hd9 x hx).1.of_le (by rw [h8, h7])
        (Nat.le_trans hle hle8)).mono hle10),
      ht8 n fun x hx h => hn (h ▸ ((hd8 x hx).1.of_le (by rw [h7]) hle).mono h9n), h7, h6]
  have hgT : ∀ x, gm? = some x → s10.tys[x]? = some HasBool.boolTy := fun x hx => by
    rw [ht10 x fun y hy he => (hd8 x hx).1.disj (he ▸ (hd10 y hy).1) hle9,
      ht9 x fun y hy he => (hd8 x hx).1.disj (he ▸ (hd9 y hy).1) (Nat.le_refl _)]
    exact (hd8 x hx).2
  have hgD : ∀ x, gm? = some x → Drawn s7T s10 x := fun x hx =>
    ((hd8 x hx).1.of_le (by rw [h7]) hle).mono h9n
  have hnx : s7T.next ≤ s10.next := Nat.le_trans hle (Nat.le_trans hle8 h9n)
  obtain ⟨hnm, hta, hav, hba, hpe, hla, hL⟩ : s10.nm = s6.nm ∧ s10.taken = s6.taken ∧
      s10.avoid = s6.avoid ∧ s10.back = s6.back ∧ s10.pending = s6.pending ∧
      s10.labelDepth = s6.labelDepth ∧ s10.live = s6.live := by
    rw [h10, h9, h8, h7, h6]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases ht.out with ⟨hn, -, rfl⟩ | ⟨hn, -, -, -, -, -, hl⟩
  · exact ⟨hnm, hta, hav, hba, hpe, hla, hTy, hTs, hgT, hgD, hnx, fun _ _ h => hL ▸ h,
      fun h => nomatch hn.symm.trans h⟩
  · obtain ⟨live, clock, hrun, hiff, hkeep, -, -⟩ := liveAdd_run (rdc ++ RE.vars κ) _
    cases hrun.symm.trans hl
    exact ⟨hnm, hta, hav, hba, hpe, hla, hTy, hTs, hgT, hgD, hnx, fun n s h => hkeep n s (hL ▸ h),
      fun _ n hn => (hiff n).2 (.inr hn)⟩

omit iLI iWL iOp iLF iLFs iLV in
/-- The variables saved around the else arm of a laid-out `ite` when it always exits (step 3b)
    have no duplicates. -/
private theorem laidCE_nodup (E : WRes P) (st : WSt P) (t0 : Nat) : (laidCE E st t0).Nodup := by
  unfold laidCE
  split <;> simp only [Std.HashSet.fold_eq_foldl_toList, List.nodup_nil]
  exact nodup_foldl_filter _ _ (Std.HashSet.distinct_toList.imp fun h he => by simp [he] at h)
    List.nodup_nil fun _ _ h => nomatch h

section PartsAx0

variable {sv3 cp3 rs3 : Rope (WItem P)} {cps3 : List (P.Ident × P.Ident)} {s7 : WSt P}
  {svT cpT rsT : Rope (WItem P)} {cpsT : List (P.Ident × P.Ident)} {s7T : WSt P}
  {svE cpE rsE : Rope (WItem P)} {cpsE : List (P.Ident × P.Ident)} {s7E : WSt P}

omit iOp iLF iLFs iLV in
/-- The saves before the then arm of a laid-out `ite` one of whose arms always exits are those of
    one run of `saveRestore`, from `s6` to `s7T`: of step 3 (`interSet`) when the then arm does not
    always exit, of step 3b (`laidCT`) otherwise; the other run saves no variable. -/
private theorem LaidEnvAx.saves
    (e : LaidEnvAx F tE Γ Lc κ d c tss ess md st0 r st' T Y items S Ex k Lab wc rdc s1 g s2 rT s3 κE
      rE? s4 Er s5 Tr s6 sv3 cp3 rs3 cps3 s7 svT cpT rsT cpsT s7T svE cpE rsE cpsE s7E) :
    ∃ M sv cp rs cps, SaveFacts s6 M sv cp rs cps s7T ∧ M.Nodup ∧
      sv.toList = sv3.toList ++ svT.toList ∧ cp.toList = cp3.toList ++ cpT.toList ∧
      rs.toList = rs3.toList ++ rsT.toList ∧
      ((Tr.ax = false ∧ M = interSet Tr.A Er.R ∧ cps = cps3 ∧ cpsT = []) ∨
        (Tr.ax = true ∧ M = laidCT Tr Er s6 s4.clock ∧ cps = cpsT ∧ cps3 = [])) := by
  have h7 := e.run7
  have h7T := e.run7T
  cases hT : Tr.ax
  · rw [show laidCT Tr Er s6 s4.clock = [] by simp [laidCT, hT], saveRestore_nil_run] at h7T
    cases h7T
    exact ⟨_, _, _, _, _, saveRestore_run (hT ▸ h7), interSet_nodup _ _, by simp [Rope.toList_nil],
      by simp [Rope.toList_nil], by simp [Rope.toList_nil], .inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · rw [hT, ite_eq_left rfl, saveRestore_nil_run] at h7
    cases h7
    have hnd : (laidCT Tr Er s6 s4.clock).Nodup := by
      rw [laidCT, ite_eq_left hT, Std.HashSet.fold_eq_foldl_toList]
      exact nodup_foldl_filter _ _ (Std.HashSet.distinct_toList.imp fun h he => by simp [he] at h)
        List.nodup_nil fun _ _ h => nomatch h
    exact ⟨_, _, _, _, _, saveRestore_run h7T, hnd, by simp [Rope.toList_nil],
      by simp [Rope.toList_nil], by simp [Rope.toList_nil], .inr ⟨rfl, rfl, rfl, rfl⟩⟩

end PartsAx0

/-- Two entries of a duplicate-free list that are equal sit at the same index. -/
private theorem rex_nodupIdx {α : Type} : ∀ (l : List α), l.Nodup → ∀ (i j : Nat) (a : α),
    l[i]? = some a → l[j]? = some a → i = j := fun _ hl _ _ _ hi hj =>
  (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hi).1 hl).1 (hi.trans hj.symm)

section PartsAx1

variable {sv3 cp3 rs3 : Rope (WItem P)} {cps3 : List (P.Ident × P.Ident)} {s7 : WSt P}
  {svT cpT rsT : Rope (WItem P)} {cpsT : List (P.Ident × P.Ident)} {s7T : WSt P}
  {svE cpE rsE : Rope (WItem P)} {cpsE : List (P.Ident × P.Ident)} {s7E : WSt P}
  {gm? : Option P.Ident} {s8 : WSt P} {qm? : Option P.Ident} {s9 : WSt P} {rEm? : Option P.Ident}
  {s10 : WSt P}
  (e : LaidEnvAx F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
    Ex k Lab wc rdc s1 g s2 rT s3 κE rE? s4
    Er s5 Tr s6 sv3 cp3 rs3 cps3 s7 svT cpT rsT cpsT s7T svE cpE rsE cpsE s7E)
  (ht : LaidAxTail κ d wc rdc g rT κE rE? s4.clock Er Tr s6 sv3 cp3 rs3 svT cpT rsT svE cpE rsE cps3
    cpsT cpsE s7E r st' gm? s8 qm? s9 rEm? s10)
include e ht

section

omit iLFs

omit iLI iOp iLF iLV in
/-- The resolved output of a laid-out `ite` one of whose arms always exits, with a nonempty body:
    the guard's `init` followed by the resolved parts. -/
private theorem LaidEnvAx.split
    (hnn : (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
      (cps3.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all
        Rope.isNil = false) (hsv : sv.toList = sv3.toList ++ svT.toList)
    (hcp : cp.toList = cp3.toList ++ cpT.toList) (hrs : rs.toList = rs3.toList ++ rsT.toList) :
    ∃ ce iRT iGM iQM iSV iT iCP iRS iRE iREM iSVE iE iCPE iRSE iMG iU,
      resolveE T Y (kAnd κ wc) = .ok ce ∧
      resolveItems T Y (if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then Rope.nil
        else Rope.one (WItem.init rT (.known HasBool.boolTy) (some (.var g)))).toList = .ok iRT ∧
      resolveItems T Y (match gm? with
        | some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var g)))
        | none => Rope.nil).toList = .ok iGM ∧
      resolveItems T Y (match κ, qm? with
        | .name q, some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var q)))
        | _, _ => Rope.nil).toList = .ok iQM ∧
      resolveItems T Y sv.toList = .ok iSV ∧ resolveItems T Y Tr.out.toList = .ok iT ∧
      resolveItems T Y cp.toList = .ok iCP ∧ resolveItems T Y rs.toList = .ok iRS ∧
      resolveItems T Y (match rE? with
        | some r => if (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil && rEm?.isNone) = true
          then Rope.nil
          else Rope.one (WItem.init r (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)))
        | none => Rope.nil).toList = .ok iRE ∧
      resolveItems T Y (match rE?, rEm? with
        | some r, some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var r)))
        | _, _ => Rope.nil).toList = .ok iREM ∧
      resolveItems T Y svE.toList = .ok iSVE ∧ resolveItems T Y Er.out.toList = .ok iE ∧
      resolveItems T Y cpE.toList = .ok iCPE ∧ resolveItems T Y rsE.toList = .ok iRSE ∧
      resolveItems T Y (laidMergesAx gm? Er
        (cps3.filter fun p => liveBefore s6 p.1 s4.clock)).toList = .ok iMG ∧
      resolveItems T Y (laidU κ κE rT Tr Er d).toList = .ok iU ∧
      items = .plain (mkInit g HasBool.boolTy (.det ce)) ::
        (iRT ++ (iGM ++ (iQM ++ (iSV ++ (iT ++ (iCP ++ (iRS ++ (iRE ++ (iREM ++ (iSVE ++ (iE ++
          (iCPE ++ (iRSE ++ (iMG ++ iU)))))))))))))) := by
  rcases ht.out with ⟨h, -⟩ | ⟨-, hout, -⟩
  · simp [h] at hnn
  obtain ⟨a, its, ha, hits, rfl⟩ := resolveItems_cons_ok (hout ▸ e.res)
  obtain ⟨ty, ce, rfl, hce, rfl⟩ := resolveItem_init_inv ha
  delta laidPartsAx at hits
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hits
  iterate 17 (rw [resolveItems_append] at hits; obtain ⟨_, _, _, hits, rfl⟩ := hits)
  rw [hsv, hcp, hrs]
  have hap {a b ia ib} (ha : resolveItems T Y a = .ok ia) (hb : resolveItems T Y b = .ok ib) :=
    (resolveItems_append T Y a b).2 ⟨ia, ib, ha, hb, rfl⟩
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hce, ‹_›, ‹_›, ‹_›, hap ‹_› ‹_›, ‹_›,
    hap ‹_› ‹_›, hap ‹_› ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›,
    by simp only [List.append_assoc]⟩

omit iWL iOp iLF iLV e in
/-- The merge guard and the copies `qm`, `rEm` of a laid-out `ite` one of whose arms always exits
    are drawn after the else arm's saves (state `s7E`), are distinct and are Boolean at the walk
    output, whose avoided names are those of `s7E`. -/
private theorem LaidAxTail.late :
    (∀ x, gm? = some x → Drawn s7E st' x ∧ st'.tys[x]? = some HasBool.boolTy) ∧
    (∀ x, qm? = some x → Drawn s7E st' x ∧ st'.tys[x]? = some HasBool.boolTy ∧
      ∀ y, gm? = some y → x ≠ y) ∧
    (∀ x, rEm? = some x → Drawn s7E st' x ∧ st'.tys[x]? = some HasBool.boolTy ∧
      (∀ y, gm? = some y → x ≠ y) ∧ ∀ y, qm? = some y → x ≠ y) ∧
    st'.avoid = s7E.avoid ∧ st'.tyOf = s7E.tyOf ∧ s7E.next ≤ st'.next := by
  obtain ⟨h8, hle8, ht8, hd8⟩ := optFresh_facts (ht.gm.imp (·.2) (·.2))
  obtain ⟨h9, hle9, ht9, hd9⟩ := optFresh_facts (ht.qm.imp (·.2.2) (·.2))
  obtain ⟨h10, hle10, ht10, hd10⟩ := optFresh_facts (ht.rEm.imp (·.2.2) (·.2))
  rcases ht.out with ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, hl⟩
  case' inr =>
    obtain ⟨live, clock, hrun, -⟩ := liveAdd_run (rdc ++ RE.vars κ) _
    cases hrun.symm.trans hl
  all_goals exact ⟨fun x hx => ⟨(hd8 x hx).1.mono (Nat.le_trans hle9 hle10),
      (ht10 x fun y hy he => (hd8 x hx).1.disj (he ▸ (hd10 y hy).1) hle9).trans
        ((ht9 x fun y hy he => (hd8 x hx).1.disj (he ▸ (hd9 y hy).1) (Nat.le_refl _)).trans
          (hd8 x hx).2)⟩,
    fun x hx => ⟨((hd9 x hx).1.of_le (by rw [h8]) hle8).mono hle10,
      (ht10 x fun y hy he => (hd9 x hx).1.disj (he ▸ (hd10 y hy).1) (Nat.le_refl _)).trans
        (hd9 x hx).2, fun y hy he => (hd8 y hy).1.disj (he ▸ (hd9 x hx).1) (Nat.le_refl _)⟩,
    fun x hx => ⟨(hd10 x hx).1.of_le (by rw [h9, h8]) (Nat.le_trans hle8 hle9), (hd10 x hx).2,
      fun y hy he => (hd8 y hy).1.disj (he ▸ (hd10 x hx).1) hle9,
      fun y hy he => (hd9 y hy).1.disj (he ▸ (hd10 x hx).1) (Nat.le_refl _)⟩,
    by rw [h10, h9, h8], by rw [h10, h9, h8], Nat.le_trans hle8 (Nat.le_trans hle9 hle10)⟩

omit iOp iLF iLV ht in
/-- A name drawn by the walk of a laid-out `ite` one of whose arms always exits (between a state
    `s` and the walk output, which avoid the names `st0` does) that is Boolean at the walk output
    has the Boolean final type. -/
private theorem LaidEnvAx.finBool {s : WSt P} (hav : s.avoid = st0.avoid)
    (hav' : st'.avoid = st0.avoid) {x : P.Ident} (hd : Drawn s st' x)
    (hty : st'.tys[x]? = some HasBool.boolTy) : T[x]? = some HasBool.boolTy := by
  obtain ⟨b, j, hx, hs, -, hj⟩ := hd
  exact (e.fin.1 x _ hty).elim (fun h => h)
    fun ho1 => ho1.elim (fun ⟨_, h, _⟩ => nomatch (hav' ▸ h b j hx).symm.trans (hav ▸ hs))
    fun ⟨b', j', hx', hj', _⟩ => absurd (freshName_counter_inj (hx.symm.trans hx')) (by omega)

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLV e ht in
/-- The copy `qm` listed by `laidQm` is drawn. -/
private theorem mem_laidQm {κ' : RE P} {o? : Option P.Ident} {x : P.Ident}
    (h : x ∈ laidQm κ' o?) : o? = some x := by cases o? <;> cases κ' <;> simp_all [laidQm]

omit iLB iHI iLI e ht in
/-- The copy `init rEm := rE` of the else-arm reach of a laid-out `ite` (when emitted) runs from a
    store where `rE` holds a Boolean `bv` and `rEm` is unbound, binding `rEm` to `bv`. -/
private theorem rEmRun (hF : WellFormedSemanticEvalBase F) {rE? rEm? : Option P.Ident}
    (hC : WellFormedStore σ F) {bv : P.Val} (hbv : bv = HasBool.ttVal F ∨ bv = HasBool.ffVal F)
    (hr : ∀ r x, rE? = some r → rEm? = some x → σ r = some bv ∧ σ x = none) {iREM : List (Item P)}
    (h : resolveItems T Y (match rE?, rEm? with
        | some r, some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var r)))
        | _, _ => Rope.nil).toList = .ok iREM) :
    ∃ σ', MainRun F iREM σ [] σ' ∧ WellFormedStore σ' F ∧
      ((σ' = σ ∧ ∀ r x, rE? = some r → rEm? = some x → False) ∨
        ∃ r x, rE? = some r ∧ rEm? = some x ∧ σ' = SemanticStore.update σ x bv) := by
  rcases rE? with _ | r <;> rcases rEm? with _ | x
  all_goals try exact ⟨σ, by cases resolve_isNil rfl h; exact .nil, hC, .inl ⟨rfl, nofun⟩⟩
  obtain ⟨a, ha, rfl⟩ := resolve_one h
  obtain ⟨ty, e', rfl, he, rfl⟩ := resolveItem_init_inv ha
  obtain ⟨t, rfl⟩ := resolveE_var he
  obtain ⟨hrv, hx0⟩ := hr r x rfl rfl
  exact ⟨_, run_init1 hF hx0 (ev_var hF.var hC hrv) (bool_valueOfTy hbv),
    wfStore_update_bool hC x hbv, .inr ⟨r, x, rfl, rfl, rfl⟩⟩

omit iOp iLF iLV in
/-- A laid-out `ite` one of whose arms always exits whose output parts are all empty saves
    nothing before the then arm, draws no merge guard, has an empty resolved output and empty arm
    outputs, and registers nothing. -/
private theorem LaidEnvAx.nilParts {nonnil : Prop}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc nonnil) (hns : SaveNs s6 M sv cp rs cps s7T ns)
    (hsv : sv.toList = sv3.toList ++ svT.toList)
    (hnil : (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all
          Rope.isNil = true) :
    ns = [] ∧ gm? = none ∧ items = [] ∧ resolveItems T Y Tr.out.toList = .ok [] ∧
      resolveItems T Y Er.out.toList = .ok [] ∧ r.regs.toList = [] := by
  have hro : r.out = .nil := ht.out.elim (·.2.1) fun h => by simp [hnil] at h
  delta laidPartsAx at hnil
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hnil
  obtain ⟨-, hgm, -, hsv3, hsvT, hTn, -, -, -, -, -, -, hsvE, hEn, -⟩ := hnil
  obtain ⟨nsT, hnsT⟩ := saveRestore_run e.run7T
  obtain ⟨nsE, hnsE⟩ := saveRestore_run e.run7E
  obtain rfl : nsT = [] := by simpa [Rope.isNil_toList hsvT] using hnsT.saves
  obtain rfl : nsE = [] := by simpa [Rope.isNil_toList hsvE] using hnsE.saves
  refine ⟨by simpa [hsv, Rope.isNil_toList hsv3, Rope.isNil_toList hsvT] using hns.saves,
    Option.eq_none_iff_forall_ne_some.2 fun y hy => by simp [hy, Rope.isNil] at hgm,
    resolve_isNil (by rw [hro]; rfl) e.res, Rope.isNil_toList hTn ▸ rfl,
    Rope.isNil_toList hEn ▸ rfl,
    List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_⟩
  simp only [ht.regs, hnsT.pairs, hnsE.pairs, List.map_nil, List.reverse_nil, laidCarry_nil,
    List.append_nil, List.mem_append] at hx
  exact hx.elim (fun hx => by simpa [Rope.isNil_toList hTn, wDecls] using hs.armT.regs x hx)
    fun hx => by simpa [Rope.isNil_toList hEn, wDecls] using hs.armE.regs x hx

omit iOp iLF iLV in
/-- The saves around the else arm of a laid-out `ite` one of whose arms always exits (triples
    `nsE`, from `s7T` to `s7E`, avoiding the names `s6` avoids), and the copy `qm` of the
    enclosing context: drawn after the then arm's saves, distinct from the merge guard, with the
    Boolean final type. -/
private theorem LaidEnvAx.saveE {nonnil : Prop}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc nonnil) (hns : SaveNs s6 M sv cp rs cps s7T ns) :
    ∃ nsE, SaveNs s7T (laidCE Er s6 s4.clock) svE cpE rsE cpsE s7E nsE ∧ s7T.next ≤ s7E.next ∧
      s7E.avoid = s7T.avoid ∧ s7T.avoid = s6.avoid ∧
      (∀ x, qm? = some x → Drawn s7T st' x ∧ ∀ y, gm? = some y → x ≠ y) ∧
      (∀ x ∈ laidQm κ qm?, Drawn s7T st' x) ∧ (∀ x ∈ laidQm κ qm?, T[x]? = some HasBool.boolTy) ∧
      (∀ x, rE? = some x → ∀ n, Drawn s7T st' n → x ≠ n) ∧
      ∀ x, rEm? = some x → Drawn s7T st' x ∧ x ∉ laidQm κ qm? ∧ ∀ y, gm? = some y → x ≠ y := by
  have hnx := hs.nexts
  obtain ⟨nsE, hnsE⟩ := saveRestore_run e.run7E
  have a7E : s7E.avoid = s7T.avoid := by rw [hnsE.eq]
  have a7T : s7T.avoid = s6.avoid := by rw [hns.eq]
  obtain ⟨-, hlq, hlr, -⟩ := ht.late
  have hqmD : ∀ x, qm? = some x → Drawn s7T st' x ∧ ∀ y, gm? = some y → x ≠ y := fun x hx =>
    ⟨(hlq x hx).1.of_le a7E hnsE.next, (hlq x hx).2.2⟩
  refine ⟨nsE, hnsE, hnsE.next, a7E, a7T, hqmD, fun x hx => (hqmD x (mem_laidQm hx)).1,
    fun x hx => e.finBool (s := s7E) (a7E.trans (a7T.trans hs.avoids.2.2.2.1))
      hs.avoids.2.2.2.2 (hlq x (mem_laidQm hx)).1 (hlq x (mem_laidQm hx)).2.1,
    fun x hx n hn he => (hs.pre.drawn x (.inr (.inr hx))).disj (he ▸ hn) (by omega),
    fun x hx => ⟨(hlr x hx).1.of_le a7E hnsE.next, fun h => (hlr x hx).2.2.2 x (mem_laidQm h) rfl,
      (hlr x hx).2.2.1⟩⟩

/-- Between the arms of a laid-out `ite` one of whose arms always exits, with a nonempty body:
    from a store `σ1` after the then arm's output (agreeing with `σL` on the context variables,
    holding the guard value `gv` at the guard and the merge guard), the copies, the restores (to
    `σR`, which agrees with `σL` on the saved variables and with `σ1` elsewhere outside the
    copies), the else-arm reach and its copy `rEm` (both writing `bv`) and the saves around the
    else arm run to `σS`, each variable of `σS` holding its value in `σR`, `bv` at the reach or
    its copy, or the value in `σR` of the variable a save copies. -/
private theorem LaidEnvAx.midG {nsE : List (P.Ident × P.Ident × P.Ident)}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all
          Rope.isNil = false)) (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hnsE : SaveNs s7T (laidCE Er s6 s4.clock) svE cpE rsE cpsE s7E nsE)
    {σB : SemanticStore P} (hfr : FreshInv Lc Ex st' σL) (hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hsrcE : ∀ q ∈ nsE, (σL q.1).isSome ∧ ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hB : PreStore F σL σB (g :: ((if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then []
      else [rT]) ++ gm?.toList)) gv ns (laidQm κ qm?)) (hext : ∀ x ∈ laidQm κ qm?, Drawn s7T st' x)
    (hC1 : WellFormedStore σ1 F) (hfr1 : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1)
    (hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hκ1 : ∀ y ∈ RE.vars κ, σ1 y = σL y)
    (hsrc1 : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hpre1 : ∀ n ∈ g :: gm?.toList, σ1 n = some gv) (hsv1 : ∀ q ∈ ns, σ1 q.2.1 = σL q.1)
    (hunb1 : ∀ n, σB n = none → n ≠ rT → ¬ Wr0 (Block.idents tss) s5 s6 n → σ1 n = none)
    {iCP iRS iRE iREM iSVE : List (Item P)} (hCP : resolveItems T Y cp.toList = .ok iCP)
    (hRS : resolveItems T Y rs.toList = .ok iRS) (hREM : resolveItems T Y (match rE?, rEm? with
        | some r, some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var r)))
        | _, _ => Rope.nil).toList = .ok iREM)
    (hSVE : resolveItems T Y svE.toList = .ok iSVE)
    {bv : P.Val} (hbv : bv = HasBool.ttVal F ∨ bv = HasBool.ffVal F)
    (hD : ∀ σR, WellFormedStore σR F → (∀ y ∈ RE.vars κ, σR y = σL y) →
      σR g = some gv → (∀ x, rE? = some x → σR x = none) → ∃ σD, MainRun F iRE σR [] σD ∧
        WellFormedStore σD F ∧ ((iRE = [] ∧ σD = σR ∧ (rE? = none ∨
          (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil && rEm?.isNone) = true)) ∨
            ∃ x, rE? = some x ∧ (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil && rEm?.isNone) =
              false ∧ σD = SemanticStore.update σR x bv)) :
    ∃ σR σD σM σS, MainRun F (iCP ++ (iRS ++ (iRE ++ (iREM ++ iSVE)))) σ1 [] σS ∧
      WellFormedStore σS F ∧ (∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty) ∧
      (∀ q ∈ ns, σ1 q.2.2 = none) ∧
      (∀ n, Drawn s7T st' n → n ∉ laidQm κ qm? → (∀ y, gm? = some y → n ≠ y) → σ1 n = none) ∧
      (∀ n, (∀ q ∈ ns, n ≠ q.1 ∧ n ≠ q.2.2) → σR n = σ1 n) ∧ (∀ q ∈ ns, σR q.1 = σL q.1) ∧
      (∀ q ∈ ns, σR q.2.2 = σ1 q.1) ∧ (∀ y ∈ RE.vars κ, σR y = σL y) ∧
      σR g = some gv ∧ (∀ x, rE? = some x → σR x = none) ∧
      (∀ n, Drawn s7T st' n → n ∉ laidQm κ qm? → (∀ y, gm? = some y → n ≠ y) → σR n = none) ∧
      ((iRE = [] ∧ σD = σR ∧ (rE? = none ∨
        (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil && rEm?.isNone) = true)) ∨
          ∃ x, rE? = some x ∧ σD = SemanticStore.update σR x bv) ∧
      ((σM = σD ∧ ∀ r x, rE? = some r → rEm? = some x → False) ∨
        ∃ r x, rE? = some r ∧ rEm? = some x ∧ σM = SemanticStore.update σD x bv) ∧
      (∀ n, σM n = σD n ∨ (rEm? = some n ∧ σM n = some bv)) ∧
      (∀ n, (∀ q ∈ nsE, n ≠ q.2.1) → σS n = σM n) ∧ (∀ q ∈ nsE, σS q.2.1 = σR q.1) ∧
      (∀ q ∈ nsE, ∃ w, σR q.1 = some w ∧
        ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty) ∧
      (∀ n, σS n = σR n ∨ (rE? = some n ∧ σS n = some bv) ∨
        (rEm? = some n ∧ σS n = some bv) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σS n = σR q.1)) ∧
      (∀ σE : SemanticStore P, (∀ n, σE n = σR n ∨ (rE? = some n ∧ σE n = some bv) ∨
        (rEm? = some n ∧ σE n = some bv) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σE n = σR q.1)) →
        (∀ n, (σL n).isSome → σE n = σR n) ∧ (∀ n w, σE n = some w → Y[n]? = none →
          ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
          FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE) ∧
      ((∀ n, (σL n).isSome → σ1 n = σL n) → (∀ n, (σL n).isSome → σR n = σL n) ∧
        ∀ n, (∀ q ∈ ns, n ≠ q.2.2) → σR n = σ1 n) ∧
      (bv = (HasBool.ttVal F) → gv = (HasBool.ffVal F) → κ.Holds F σL →
        ∃ σEs : SemanticStore P, WellFormedStore σEs F ∧
        (∀ n, σEs n = σR n ∨ (rE? = some n ∧ σEs n = some (HasBool.ttVal F)) ∨
          (rEm? = some n ∧ σEs n = some (HasBool.ttVal F)) ∨
          (∃ q ∈ nsE, n = q.2.1 ∧ σEs n = σR q.1)) ∧
        κE.Holds F σEs ∧ (σEs = σS ∨ ∃ x, rE? = some x ∧
          σEs = SemanticStore.update σS x (HasBool.ttVal F) ∧
          σS x = none ∧ Er.out.isNil = true ∧ (laidU κ κE rT Tr Er d).isNil = true)) := by
  have hnx := hs.nexts
  have hav := hs.avoids
  obtain ⟨hlg, hlq, hlr, -, hyoE, hnE⟩ := ht.late
  have a7E : s7E.avoid = s7T.avoid := by rw [hnsE.eq]
  have hle7 : s7T.next ≤ st'.next := hs.aft.next
  have hcpD : ∀ q ∈ ns, Drawn s6 s7T q.2.2 := fun q hq => (hns.drawn q hq).2.1
  have hlate6 : ∀ n, Drawn s7T st' n → Drawn s6 st' n := fun n hn =>
    hn.of_le (by rw [hns.eq]) hns.next
  have hunbL : ∀ n, Drawn s6 st' n → σL n = none := fun n hn => e.unbound hs hfr (.inr hn)
  have hrEL : ∀ x, rE? = some x → σL x = none := fun x hx =>
    e.unbound hs hfr (.inl (.inr (.inr hx)))
  have hgD := hs.pre.drawn g (.inl rfl)
  have hu1 : ∀ n, ((n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) → n ≠ rT → σB n = σL n →
      σ1 n = none := fun n hn hr hb =>
    hunb1 n (hb.trans (e.unbound hs hfr hn)) hr (e.notWT hs hn)
  have hcp1 : ∀ q ∈ ns, σ1 q.2.2 = none := fun q hq => by
    obtain ⟨hng, hnr, hngm, -⟩ := hs.saveNe (hcpD q hq)
    exact hu1 _ (.inr ((hcpD q hq).mono hle7)) hnr
      (hB.2.2.1 q.2.2 (fun h => (hcpD q hq).disj (hext _ h) (Nat.le_refl _))
        (notin_pre hng hnr hngm) fun p hp he => flat_ne ns hns.nodup p hp q hq he.symm)
  have hlate1 : ∀ n, Drawn s7T st' n → n ∉ laidQm κ qm? → (∀ y, gm? = some y → n ≠ y) →
      σ1 n = none := fun n hn hq hgm => by
    have hng : n ≠ g := fun h => hgD.disj (h ▸ hn) (by omega)
    have hnr : n ≠ rT := fun h => (hs.pre.drawn rT (.inr (.inl rfl))).disj (h ▸ hn) (by omega)
    exact hu1 n (.inr (hlate6 n hn)) hnr (hB.2.2.1 n hq (notin_pre hng hnr hgm) fun q hq' he =>
      (hns.drawn q hq').1.disj (he ▸ hn) (Nat.le_refl _))
  have hML : ∀ q ∈ ns, (σL q.1).isSome := fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]
  have hLcp : ∀ n, (σL n).isSome → ∀ q ∈ ns, n ≠ q.2.2 := fun n hn q hq he => by
    simp [he, hunbL _ ((hcpD q hq).mono hle7)] at hn
  obtain ⟨σC, σR, hrunC, hrunR, hCR, hRcp, hRv, hRo, htyC⟩ := copyRestore e.hF hns hMnd hC1 hCP
    hRS hcp1 hsrc1 (fun q hq => (hsrcS q hq).imp fun _ h => ⟨(hsv1 q hq).trans h.1, h.2⟩)
    fun q hq p hp => ⟨fun he => absurd (hML q hq) (by simp [he, e.preUnbound hs hns hfr
      (.inr ⟨p, hp, rfl⟩)]), hLcp q.1 (hML q hq) p hp⟩
  replace hRv : ∀ q ∈ ns, σR q.1 = σL q.1 := fun q hq => (hRv q hq).trans (hsv1 q hq)
  have hR0 : ∀ n, σL n = none → (∀ q ∈ ns, n ≠ q.2.2) → σR n = σ1 n := fun n h0 hn =>
    hRo n fun q hq => ⟨fun he => absurd (hML q hq) (by simp [← he, h0]), hn q hq⟩
  have hκR : ∀ y ∈ RE.vars κ, σR y = σL y := fun y hy =>
    (Classical.em (∃ q ∈ ns, y = q.1)).elim (fun ⟨q, hq, he⟩ => he ▸ hRv q hq) fun hq =>
      (hRo y fun q hq' => ⟨fun he => hq ⟨q, hq', he⟩, fun he =>
        (e.of_ctxNe hs hy).2.2.2 s6 s7T (by omega) (he ▸ hcpD q hq')⟩).trans (hκ1 y hy)
  have hgR : σR g = some gv := (hR0 g (e.unbound hs hfr (.inl (.inl rfl))) fun q hq he =>
    (hs.saveNe (hcpD q hq)).1 he.symm).trans (hpre1 g (List.mem_cons_self ..))
  have h0R : ∀ x, rE? = some x → σR x = none := fun x hx => by
    obtain ⟨hxg, hxr⟩ := hs.pre.rE_ne x hx
    rw [hR0 x (hrEL x hx) fun q hq he => (hs.saveNe (hcpD q hq)).2.2.2 x hx he.symm]
    exact hu1 x (.inl (.inr (.inr hx))) hxr
      (hB.2.2.1 x (fun h => (hs.pre.drawn x (.inr (.inr hx))).disj (hext x h) (by omega))
      (notin_pre hxg hxr fun y hy he => (hs.pre.drawn x (.inr (.inr hx))).disj
        (he ▸ hs.aft.gmDrawn y hy) (by omega))
      fun q hq he => (hs.saveNe (hns.drawn q hq).1).2.2.2 x hx he.symm)
  have hlateR : ∀ n, Drawn s7T st' n → n ∉ laidQm κ qm? → (∀ y, gm? = some y → n ≠ y) →
      σR n = none := fun n hn hq hgm =>
    (hR0 n (hunbL n (hlate6 n hn)) fun q hq' he => (hcpD q hq').disj (he ▸ hn)
      (Nat.le_refl _)).trans (hlate1 n hn hq hgm)
  obtain ⟨σD, hrunD, hCD, hcaseD⟩ := hD σR hCR hκR hgR h0R
  replace hcaseD := hcaseD.imp_right (Exists.imp fun _ h => And.intro h.1 h.2.2)
  have hDR : ∀ n, (∀ x, rE? = some x → n ≠ x) → σD n = σR n := fun n hn => by
    rcases hcaseD with ⟨-, h, -⟩ | ⟨x, hx, h⟩ <;> rw [h]
    exact (update_facts σR x bv).2 n (Ne.symm (hn x hx))
  have hrEng : ∀ x, rE? = some x → ∀ n, Drawn s7T st' n → x ≠ n := fun x hx n hn he =>
    (hs.pre.drawn x (.inr (.inr hx))).disj (he ▸ hn) (by omega)
  have hrEmD : ∀ x, rEm? = some x → Drawn s7T st' x := fun x hx =>
    (hlr x hx).1.of_le a7E hnsE.next
  obtain ⟨σM, hrunM, hCM, hcaseM⟩ := rEmRun e.hF hCD hbv (fun r x hr hx => ⟨by
      rcases hcaseD with ⟨-, -, h | h⟩ | ⟨x', hx', rfl⟩
      · simp [h] at hr
      · simp [hx] at h
      · exact Option.some.inj (hr.symm.trans hx') ▸ (update_facts σR x' bv).1,
    (hDR x fun y hy => (hrEng y hy x (hrEmD x hx)).symm).trans
      (hlateR x (hrEmD x hx) (fun h => (hlr x hx).2.2.2 x (mem_laidQm h) rfl)
        (hlr x hx).2.2.1)⟩) hREM
  have hMx : ∀ n, σM n = σD n ∨ (rEm? = some n ∧ σM n = some bv) := fun n => by
    exact hcaseM.elim (fun ⟨h, _⟩ => .inl (congrFun h n)) fun ⟨_, x, _, hx, h⟩ => h ▸
      (update_cases σD x bv n).imp_right fun ⟨he, h⟩ => ⟨he ▸ hx, h⟩
  have hMR : ∀ n, (σL n).isSome → σM n = σR n := fun n hn => by
    have hnE : ∀ x, rE? = some x → n ≠ x := fun x hx he => by simp [he, hrEL x hx] at hn
    exact (hMx n).elim (fun h => by rw [h, hDR n hnE])
      fun ⟨h, _⟩ => by simp [hunbL n (hlate6 n (hrEmD n h))] at hn
  have hRb : ∀ q ∈ nsE, ∃ w, σR q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    (Classical.em (∃ p ∈ ns, q.1 = p.1)).elim (fun ⟨p, hp, he⟩ => he ▸ (hRv p hp).symm ▸ hsrcS p hp)
      fun hM => (hRo _ fun p hp => ⟨fun he => hM ⟨p, hp, he⟩, hLcp _ (hsrcE q hq).1 p hp⟩) ▸
        (hsrcE q hq).2
  have hsvE : ∀ q ∈ nsE, Drawn s7T st' q.2.1 := fun q hq => (hnsE.drawn q hq).1.mono hnE
  obtain ⟨σS, hrunS, hCS, hvalS, hothS, -⟩ := nsInitsRun e.hF (·.2.1) hCM
    (hnsE.saves ▸ hSVE) ((sub_flat nsE).nodup hnsE.nodup) (fun q hq => by
      have hd := (hnsE.drawn q hq).1
      rcases hMx q.2.1 with h | ⟨h, -⟩
      · rw [h, hDR _ fun x hx he => hrEng x hx _ (hsvE q hq) he.symm]
        exact hlateR _ (hsvE q hq) (fun h => hd.disj (hlq _ (mem_laidQm h)).1 (Nat.le_refl _))
          fun y hy he => hd.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)
      · exact absurd ((hlr _ h).1) fun h' => hd.disj h' (Nat.le_refl _))
    fun q hq => (hRb q hq).imp fun _ h => ⟨(hMR _ (hsrcE q hq).1).trans h.1, h.2⟩
  have hSL : ∀ q ∈ nsE, σS q.2.1 = σR q.1 := fun q hq =>
    (hvalS q hq).trans (hMR _ (hsrcE q hq).1)
  have hdesc : ∀ n, σS n = σR n ∨ (rE? = some n ∧ σS n = some bv) ∨
      (rEm? = some n ∧ σS n = some bv) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σS n = σR q.1) := fun n => by
    rcases Classical.em (∃ q ∈ nsE, n = q.2.1) with ⟨q, hq, rfl⟩ | hq
    · exact .inr (.inr (.inr ⟨q, hq, rfl, hSL q hq⟩))
    rw [hothS n fun q hq' he => hq ⟨q, hq', he⟩]
    rcases hMx n with h | h
    · rw [h]
      exact hcaseD.elim (fun ⟨_, h, _⟩ => .inl (congrFun h n)) fun ⟨x, hx, h⟩ => h ▸
        (update_cases σR x bv n).imp_right fun ⟨he, h⟩ => .inl ⟨he ▸ hx, h⟩
    · exact .inr (.inr (.inl h))
  have hkeep : ∀ σE : SemanticStore P, (∀ n, σE n = σR n ∨ (rE? = some n ∧ σE n = some bv) ∨
      (rEm? = some n ∧ σE n = some bv) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σE n = σR q.1)) →
      (∀ n, (σL n).isSome → σE n = σR n) ∧ (∀ n w, σE n = some w → Y[n]? = none →
        ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
        FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE := by
    refine fun σE hσE => ⟨fun n hn => ?_, fun n w hw hY ty hty => ?_, fun y hy => ?_⟩
    · rcases hσE n with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, rfl, -⟩
      · exact h
      · simp [hrEL n h] at hn
      · simp [hunbL n (hlate6 n (hrEmD n h))] at hn
      · simp [hunbL _ (hlate6 _ (hsvE q hq))] at hn
    · rcases hσE n with h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨q, hq, rfl, -⟩
      · rw [h] at hw
        rcases Classical.em (∃ q ∈ ns, n = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · simp [e.fin.2.1 q.2.2 q.1
            ((hs.aft.tyOf _ fun h => (hcpD q hq).disj h (Nat.le_refl _)).trans
            (hns.drawn q hq).2.2.2)] at hY
        rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq', rfl⟩ | hM
        · exact (hsrcS q hq').elim fun w' ⟨hw', ht'⟩ =>
            Option.some.inj (hw'.symm.trans ((hRv q hq').symm.trans hw)) ▸ ht' ty hty
        · exact hgt1 n w ((hRo n fun q hq' => ⟨fun he => hM ⟨q, hq', he⟩,
            fun he => hq ⟨q, hq', he⟩⟩).symm.trans hw) hY ty hty
      · cases h'.symm.trans hw
        exact tyOfName_bool (e.preT hs (.inl (.inr (.inr h)))) hbv hty
      · cases h'.symm.trans hw
        exact tyOfName_bool (e.finBool (s := s7E) (by rw [a7E, hns.eq]; exact hav.2.2.2.1)
          hav.2.2.2.2 (hlr n h).1 (hlr n h).2.1) hbv hty
      · simp [e.fin.2.1 q.2.1 q.1 (hyoE ▸ (hnsE.drawn q hq).2.2.1)] at hY
    · have hfrD : ∀ y, Drawn s6 st' y → (y ∈ Lc → (∀ b j, y = freshName b j →
          s5.avoid.contains y = true) → s5.taken.contains y = false) ∧ ∀ b j, y = freshName b j →
          s5.avoid.contains y = false → s5.next ≤ j ∨ (∃ x : P.Ident, s5.nm[x]? = some y) ∨
            Ex y ∨ y = g ∨ y = rT ∨ rE? = some y := fun y ⟨b, j, h1, h2, h3, _⟩ => by
        have h2' : s5.avoid.contains y = false := by rw [hav.2.2.1, ← hav.2.2.2.1]; exact h2
        exact ⟨fun _ hfa => by simp [hfa b j h1] at h2', fun b' j' h1' _ =>
          .inl (by rw [freshName_counter_inj (h1'.symm.trans h1)]; omega)⟩
      rcases hσE y with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, rfl, -⟩
      · rw [h] at hy
        rcases Classical.em (∃ q ∈ ns, y = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · exact hfrD _ ((hcpD q hq).mono hle7)
        refine (hfr1 y ?_).imp id fun f1 b j hj ha =>
          (f1 b j hj ha).imp_right (.imp_right (.imp_right (.imp_right .inl)))
        rcases Classical.em (∃ q ∈ ns, y = q.1) with ⟨q, hq', rfl⟩ | hM
        · exact Option.isSome_iff_exists.2 ((hsrc1 q hq').imp fun _ h => h.1)
        · rwa [hRo y fun q hq' => ⟨fun he => hM ⟨q, hq', he⟩, fun he => hq ⟨q, hq', he⟩⟩] at hy
      · obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn y (.inr (.inr h))
        exact ⟨fun _ hfa => by simp [hav.1, ← hav.2.2.1, hfa b j h1] at h2,
          fun _ _ _ _ => .inr (.inr (.inr (.inr (.inr h))))⟩
      · exact hfrD y (hlate6 y (hrEmD y h))
      · exact hfrD _ (hlate6 _ (hsvE q hq))
  refine ⟨σR, σD, σM, σS, MainRun.append hrunC (MainRun.append hrunR (MainRun.append hrunD
    (MainRun.append hrunM hrunS))), hCS, htyC, hcp1, hlate1, hRo, hRv, hRcp, hκR, hgR, h0R,
    hlateR, hcaseD, hcaseM, hMx, hothS, hSL, hRb, hdesc, hkeep, fun hk1 => ⟨fun n hn => ?_,
    fun n hn => ?_⟩, fun hbt hgf hκ => ?_⟩
  · exact (Classical.em (∃ q ∈ ns, n = q.1)).elim (fun ⟨q, hq, he⟩ => he ▸ hRv q hq) fun hM =>
      (hRo n fun q hq => ⟨fun he => hM ⟨q, hq, he⟩, hLcp n hn q hq⟩).trans (hk1 n hn)
  · exact (Classical.em (∃ q ∈ ns, n = q.1)).elim
      (fun ⟨q, hq, he⟩ => he ▸ (hRv q hq).trans (hk1 _ (hML q hq)).symm)
      fun hM => hRo n fun q hq => ⟨fun he => hM ⟨q, hq, he⟩, hn q hq⟩
  subst hbt hgf
  have hSg : σS g = some (HasBool.ffVal F) := by
    rw [hothS g fun q hq he => hgD.disj (he ▸ hsvE q hq) (by omega)]
    exact (hMx g).elim (fun h => by rw [h, hDR g fun x hx he => (hs.pre.rE_ne x hx).1 he.symm, hgR])
      fun ⟨h, _⟩ => absurd (hrEmD g h) fun h' => hgD.disj h' (by omega)
  rcases hcaseD with ⟨-, hDR', hcase⟩ | ⟨x, hx, hσD⟩
  · rcases e.ctx.cases' with ⟨hr, hκE⟩ | ⟨x, hx, hκE⟩
    · refine ⟨σS, hCS, hdesc, ?_, .inl rfl⟩
      rcases hκE with h | ⟨q, hq, h⟩
      · exact h ▸ hSg
      · have hq' : σL q = some (HasBool.ttVal F) := by simpa [hq, RE.Holds] using hκ
        exact h ▸ ⟨((hkeep σS hdesc).1 q (by simp [hq'])).trans
          ((hκR q (by simp [hq, RE.vars])).trans hq'), hSg⟩
    · rcases hcase with hr | hb
      · simp [hr] at hx
      · obtain ⟨⟨hEn, hUn⟩, -⟩ : (_ ∧ _) ∧ _ := by simpa only [Bool.and_eq_true] using hb
        have hSx : σS x = none := (hothS x fun q hq => hrEng x hx _ (hsvE q hq)).trans <|
          (hMx x).elim (fun h => h ▸ hDR' ▸ h0R x hx)
            fun ⟨h, _⟩ => absurd rfl (hrEng x hx x (hrEmD x h))
        refine ⟨SemanticStore.update σS x (HasBool.ttVal F), wfStore_update_bool hCS x (.inl rfl),
          fun n => ?_, ?_,
          .inr ⟨x, hx, rfl, hSx, hEn, hUn⟩⟩
        · exact (update_cases σS x (HasBool.ttVal F) n).elim (fun h => h ▸ hdesc n) fun ⟨he, h⟩ =>
            .inr (.inl ⟨he ▸ hx, h⟩)
        · exact hκE ▸ (update_facts σS x (HasBool.ttVal F)).1
  · refine ⟨σS, hCS, hdesc, ?_, .inl rfl⟩
    rcases e.ctx.cases' with ⟨hr, -⟩ | ⟨y, hy, hκE⟩
    · simp [hr] at hx
    · cases hx.symm.trans hy
      rw [hκE]
      show σS x = some (HasBool.ttVal F)
      rw [hothS x fun q hq => hrEng x hx _ (hsvE q hq)]
      exact (hMx x).elim
        (fun h => by rw [h, hσD, (update_facts σR x (HasBool.ttVal F)).1]) fun ⟨h, _⟩ =>
        absurd rfl (hrEng x hx x (hrEmD x h))

include iIL in
/-- A failure of a laid-out `ite` one of whose arms always exits, on the loop-free path, is a hit
    of its output, given the facts of its walk states (`LaidStates`, the saves before the then arm
    those of one run of `saveRestore` over `M`), the saved variables being current names of
    variables in scope that the arms mention. -/
private theorem LaidEnvAx.hit
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all
          Rope.isNil = false)) (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hsv : sv.toList = sv3.toList ++ svT.toList) (hcp : cp.toList = cp3.toList ++ cpT.toList)
    (hrs : rs.toList = rs3.toList ++ rsT.toList)
    (hMv : ∀ x ∈ M, ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hCEv : ∀ x ∈ laidCE Er s6 s4.clock, ∃ z ∈ S,
      (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x) :
    ∀ σ σL t cnd b tr,
      OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL →
      DReachS F (.ite (.det c) tss ess md) σ tr → ClaimK b t cnd tr →
      HitPost F st' r items σL t cnd b := by
  intro σ σL t cnd b tr hon hreach hcl
  rcases ht.out with ⟨hnil, -, -⟩ | ⟨hnn, -, hsk, hobl, -⟩
  · obtain ⟨rfl, rfl, -, hT, hE, -⟩ := e.nilParts ht hs hns hsv hnil
    cases hreach with
    | ite_true hc hR =>
      have hCv := wfStore_update_bool (wfStore_update_bool hon.canonL g (.inl rfl)) rT (.inl rfl)
      obtain ⟨-, -, -, -, trT, ⟨⟩, -⟩ := (e.armTp hs hT).1 σ _ t cnd b tr
        (e.thenT hs hns hon (preStore_two hs.pre.g_rT) nofun nofun hCv) hR hcl
    | ite_false hc hR hsh =>
      obtain ⟨σE, -, -, honE⟩ := e.rn_elseStore hs hns rfl hT hon (shL_of_shB hsh)
      obtain ⟨-, -, -, -, trE, ⟨⟩, -⟩ := (e.armEp hs hE).1 σ σE t cnd b tr honE hR hcl
  have hnx := hs.nexts
  obtain ⟨nsE, hnsE, -, -, -, hqmD, hext, hextT, -, -⟩ := e.saveE ht hs hns
  have hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    e.boundOn hs hon (hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq))
  have ⟨ce, iRT, iGM, iQM, iSV, iT, iCP, iRS, iRE, iREM, iSVE, iE, iCPE, iRSE, iMG, iU, hsp⟩ :=
    e.split ht hnn hsv hcp hrs
  obtain ⟨hce, hRT, hGM, hQM, hSV, hT, hCP, hRS, hRE, hREM, hSVE, hE, hCPE, hRSE, hMG, hU,
    hitems⟩ := hsp
  cases hreach with
  | ite_true hc hR =>
    obtain ⟨σB, hrun0, hCB, hB, -⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM
      hQM hqmD (fun q x hq _ => .inl (hq ▸ hon.reach :)) hSV
      (e.guardOn hs hon hnn hs.aft.liveC hc (.inl rfl) hce) (.inl rfl) hsrcS
    have hrD := hs.pre.drawn rT (.inr (.inl rfl))
    by_cases hb : (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true
    · obtain rfl : iT = [] := resolve_isNil (Bool.and_eq_true_iff.1 hb).1 hT
      have hB' : PreStore F σL σB (g :: gm?.toList) (HasBool.ttVal F) ns (laidQm κ qm?) := by
        simpa [hb] using hB
      obtain ⟨-, -, -, -, trT, ⟨⟩, -⟩ := (e.armTp hs hT).1 σ _ t cnd b tr
        (e.thenT hs hns hon (hB'.add (x := rT) (fun q hq he => hrD.disj (he ▸ (hns.drawn q hq).1)
          (by omega)) fun h => hrD.disj (hext rT h) (by omega)) hext hextT
          (wfStore_update_bool hCB rT (.inl rfl))) hR hcl
    · have hBv : PreStore F σL σB (g :: rT :: gm?.toList) (HasBool.ttVal F) ns (laidQm κ qm?) := by
        simpa [hb] using hB
      obtain ⟨hobT, hskT, wsub, hwsub, trT, hhit, hclT⟩ := (e.armTp hs hT).1 σ σB t cnd b tr
        (e.thenT hs hns hon hBv hext hextT hCB) hR hcl
      refine ⟨by rw [hobl, hobT]; rfl, hsk ▸ .iteT g _ _ hskT, wsub,
        fun q hq => ⟨hs.aft.back ▸ (hwsub q hq).1, (hwsub q hq).2⟩, [] ++ trT, ?_,
        by simpa using hclT⟩
      have h := HitIn.append_right hrun0 (HitIn.append_left (b := iCP ++ (iRS ++ (iRE ++ (iREM ++
        (iSVE ++ (iE ++ (iCPE ++ (iRSE ++ (iMG ++ iU))))))))) hhit)
      simpa only [hitems, List.cons_append, List.append_assoc] using h
  | ite_false hc hR hsh =>
    obtain ⟨σB, hrun0, hCB, hB, -⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM hQM
      hqmD (fun q x hq _ => .inl (by simpa [hq, RE.Holds] using hon.reach)) hSV
      (e.guardOn hs hon hnn hs.aft.liveC hc (.inr rfl) hce) (.inr rfl) hsrcS
    have hdefdL : ∀ x ∈ S, x ∈ contFV ([.ite (.det c) tss ess md] :: k) → ∀ n,
        curName st' x = some n → ∃ w, σL n = some w ∧
          ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun x hx hv n hn => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hon.defd x hx hv).2 n hn)
      exact ⟨w, hw, fun ty hty => hon.gtyped n w hw (e.curY hs hx hn) ty hty⟩
    obtain ⟨trT, σ1, hrunT, hfeasT, hC1, hfr1, hgt1, hk1, hpre1, hsv1, hunb1, -⟩ :=
      e.of_T hs hns hdefdL hon.gtyped hon.fresh
        (fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]) hB hext hextT hCB hT
        (shL_of_shB hsh)
    obtain ⟨_, _, _, σS, hmid⟩ := e.midG ht hs hns hMnd hnsE hon.fresh hsrcS (fun q hq =>
        (e.boundOn hs hon (hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq))).elim
          fun w ⟨hw, hty⟩ => ⟨by simp [hw], w, (hk1 _ (by simp [hw])).trans hw, hty⟩) hB hext hC1
      hfr1 hgt1 (fun y hy => hk1 y (hon.reach.bound y hy))
      (fun q hq => (hsrcS q hq).imp fun _ h => ⟨(hk1 _ (by simp [h.1])).trans h.1, h.2⟩) hpre1
      hsv1 hunb1 hCP hRS hREM hSVE (.inl rfl)
        fun σR hCR hκR hgR h0R => rEiRun e.hF hCR h0R (.inl ⟨hon.reach.congr hκR, hgR, rfl⟩) hRE
    obtain ⟨hrunCS, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkeep, hk1C, hEs⟩ := hmid
    obtain ⟨σEs, hCEs, hdescS, hreachE, hvirt⟩ := hEs rfl rfl hon.reach
    obtain ⟨hobE, hskE, wsub, hwsub, trE, hhit, hclE⟩ := (e.armEp hs hE).1 σ σEs t cnd b tr
      (hs.elseE hon hCEs (fun n hn => ((hkeep σEs hdescS).1 n hn).trans ((hk1C hk1).1 n hn))
        (hkeep σEs hdescS).2.1 (hkeep σEs hdescS).2.2 hreachE) hR hcl
    rcases hvirt with rfl | ⟨-, -, -, -, hEn, -⟩
    · refine ⟨by simp [hobl, hobE], hsk ▸ .iteE g _ _ hskE, wsub,
        fun q hq => ⟨hs.aft.back ▸ hs.wT.toWalkCore.back_keep hs.wf5 (hwsub q hq).1,
          (hwsub q hq).2⟩, trT ++ trE, ?_, claimK_prepend hfeasT hclE⟩
      have h := HitIn.append_right (MainRun.append hrun0 (MainRun.append hrunT hrunCS))
        (HitIn.append_left (b := iCPE ++ (iRSE ++ (iMG ++ iU))) hhit)
      simpa only [hitems, List.cons_append, List.append_assoc, List.nil_append] using h
    · obtain rfl : iE = [] := resolve_isNil hEn hE
      cases hhit

omit iLI iWL iOp iLF iLV e ht in
/-- The carried copies of an always-exiting arm are among its copy pairs. -/
private theorem mem_laidCarry {B : WRes P}
    {p : P.Ident × P.Ident} (h : p ∈ laidCarry B st cps) : p ∈ cps := carryOf_sub h

omit iLB iHI iLI iOp iLF iLV e ht in
/-- A variable with a final type resolves to itself at that type. -/
private theorem resolveE_var_ok {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
    {y : P.Ident} {ty : P.Ty} (hT : T[y]? = some ty) :
    resolveE T Y (.var y) = .ok (HasFvar.mkVar y (some ty)) := by
  simp [resolveE, tyOfName, hT, bind, Except.bind, pure, Except.pure]

omit iLB iHI iLI e ht iLV in
/-- The selector `gm` of a then arm's carried merge (`false` when not drawn) is false when the
    merge guard is a false Boolean with the Boolean final type. -/
private theorem selIs_gm (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    {gm? : Option P.Ident}
    (hgm : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ffVal F))
    (c x : P.Ident) :
    SelIs F T Y σ (.ite (optVar gm?) (.var c) (.var x)) false := by
  rcases gm? with _ | y
  · exact ⟨_, _, _, rfl, _, rfl, hF.val.eval_ff σ⟩
  · exact ⟨_, _, _, rfl, _, resolveE_var_ok (hgm y rfl).1, ev_var hF.var hC (hgm y rfl).2⟩

omit iLB iHI iLI e ht iLV in
include iIL in
/-- The selector of an else arm's carried merge is false off the path: the copies `qm` and `rEm`
    are false Booleans and the merge guard a Boolean, all with the Boolean final type. -/
private theorem selIs_eE (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    {κ' : RE P} (hκ : κ' ≠ .top) {gm? qm? rEm? : Option P.Ident}
    (hgm : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧
      (σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)))
    (hqm : ∀ q y, κ' = .name q → qm? = some y →
      T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ffVal F))
    (hrm : ∀ y, rEm? = some y → T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ffVal F))
    (c x : P.Ident) :
    SelIs F T Y σ (.ite (elseGuard κ' gm? qm? rEm?) (.var c) (.var x)) false := by
  refine ⟨_, _, _, rfl, ?_⟩
  rcases κ' with _ | q | g | ⟨q, g⟩ <;> rcases qm? with _ | qm <;> rcases rEm? with _ | rm
  all_goals first
    | exact absurd rfl hκ
    | exact ⟨_, rfl, hF.val.eval_ff σ⟩
    | exact ⟨_, resolveE_var_ok (hrm _ rfl).1, ev_var hF.var hC (hrm _ rfl).2⟩
    | skip
  all_goals
    obtain ⟨hT, hq⟩ := hqm q qm rfl rfl
    rcases gm? with _ | m
    · simp only [elseGuard, optVar, WExpr.and, WExpr.not, resolveE, tyOfName, hT, pure,
        Except.pure, bind, Except.bind]
      exact ⟨_, rfl, ev_ite_false_b (ev_var hF.var hC hq) (hF.val.eval_ff σ) (.inr rfl)
        (.inl (hF.val.eval_tt σ))⟩
    · obtain ⟨hTm, hm⟩ := hgm m rfl
      simp only [elseGuard, optVar, WExpr.and, WExpr.not, resolveE, tyOfName, hT, hTm, pure,
        Except.pure, bind, Except.bind]
      refine ⟨_, rfl, ev_ite_false_b (ev_var hF.var hC hq) (hF.val.eval_ff σ) (.inr rfl) ?_⟩
      rcases hm with hm | hm
      · exact .inr (ev_ite_true_b (ev_var hF.var hC hm) (hF.val.eval_ff σ) (.inr rfl)
          (.inl (hF.val.eval_tt σ)))
      · exact .inl (ev_ite_false_b (ev_var hF.var hC hm) (hF.val.eval_tt σ) (.inl rfl)
          (.inr (hF.val.eval_ff σ)))

omit iLI iWL iOp iLF iLV e ht in
/-- A carried merge of a laid-out `ite`'s carries map is one of the map it extends or a new merge
    of a copy pair of one of its arms. -/
private theorem mem_laidCarries {c : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))}
    {T E : WRes P} {cT cE : List (P.Ident × P.Ident)} {eT eE : WExpr P} {k : Nat}
    {q : P.Ident × WExpr P × P.Ident} (h : q ∈ (laidCarries c T E cT cE eT eE).getD k []) :
    q ∈ c.getD k [] ∨ (∃ p ∈ cT, q = (p.1, .ite eT (.var p.2) (.var p.1), p.2)) ∨
      ∃ p ∈ cE, q = (p.1, .ite eE (.var p.2) (.var p.1), p.2) := by grind [rex_getD]

omit iOp iLF iLV in
/-- The declarations of the arms of a laid-out `ite` one of whose arms always exits and the
    copies of its carried merges, with the saves `ns` before the then arm and `nsE` around the
    else arm. Each arm's declaration is drawn by its walk, avoided by `st0` when it has the form
    of a fresh name, or a renaming of the state before the walk. The then arm's declarations are
    drawn by no step after its saves, and are neither prelude names nor copies of the saves `ns`;
    the else arm's are no copies of the saves `nsE`.
    The live copy pairs of step 3 are pairs of the saves `ns`, with distinct first names.
    The copy pairs of the carried merges are pairs of the saves, the then arm's only when it
    always exits; their copies are drawn after the arms. A registration of the result pending at
    the end of the walk is a registration of the then arm pending after it, or one of the else arm
    pending after the else arm. -/
private theorem LaidEnvAx.decls {nsE : List (P.Ident × P.Ident × P.Ident)} {nonnil : Prop}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc nonnil) (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hnsE : SaveNs s7T (laidCE Er s6 s4.clock) svE cpE rsE cpsE s7E nsE)
    (hcase : (Tr.ax = false ∧ M = interSet Tr.A Er.R ∧ cps = cps3 ∧ cpsT = []) ∨
      (Tr.ax = true ∧ M = laidCT Tr Er s6 s4.clock ∧ cps = cpsT ∧ cps3 = [])) :
    (∀ n ∈ wDecls Tr.out.toList, (Drawn s5 s6 n ∨ AvoidedIfFresh st0 n) ∨
      ∃ y : P.Ident, s5.nm[y]? = some n) ∧
    (∀ n ∈ wDecls Er.out.toList, (Drawn s4 s5 n ∨ AvoidedIfFresh st0 n) ∨
      ∃ y : P.Ident, s4.nm[y]? = some n) ∧ (∀ n ∈ wDecls Tr.out.toList, ¬ Drawn s7T st' n) ∧
    (∀ n ∈ wDecls Tr.out.toList, ∀ m, (m = g ∨ m = rT ∨ rE? = some m) → n ≠ m) ∧
    (∀ n ∈ wDecls Tr.out.toList, ∀ q ∈ ns, n ≠ q.2.2) ∧
    (∀ n ∈ wDecls Er.out.toList, ∀ q ∈ nsE, n ≠ q.2.2) ∧
    (∀ p ∈ cps3.filter (fun p => liveBefore s6 p.1 s4.clock), ∃ q ∈ ns, p = (q.1, q.2.2)) ∧
    ((cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1)).Nodup ∧
    (∀ p ∈ laidCarry Tr s6 cpsT, Tr.ax = true ∧ ∃ q ∈ ns, p = (q.1, q.2.2)) ∧
    (∀ p ∈ laidCarry Er s6 cpsE, ∃ q ∈ nsE, p = (q.1, q.2.2)) ∧
    (∀ x ∈ (laidCarry Tr s6 cpsT).map (·.2) ++ (laidCarry Er s6 cpsE).map (·.2),
      Drawn s6 st' x) ∧
    ∀ l x, x ∈ r.regs.toList → x ∈ st'.pending.getD l [] →
      (x ∈ Tr.regs.toList ∧ x ∈ s6.pending.getD l []) ∨
        (x ∈ Er.regs.toList ∧ x ∈ s5.pending.getD l []) := by
  have hnx := hs.nexts
  have hav := hs.avoids
  have a7T : s7T.avoid = s6.avoid := by rw [hns.eq]
  have hTk : ∀ n ∈ wDecls Tr.out.toList, (Drawn s5 s6 n ∨ AvoidedIfFresh st0 n) ∨
      ∃ y, s5.nm[y]? = some n := fun n hn => (hs.armT.declW hn).elim (.inl ∘ .inl) fun h =>
    h.elim .inr fun h => .inl (.inr (e.avoidArm (.inl h)))
  have hEk : ∀ n ∈ wDecls Er.out.toList, (Drawn s4 s5 n ∨ AvoidedIfFresh st0 n) ∨
      ∃ y, s4.nm[y]? = some n := fun n hn => (hs.armE.declW hn).elim (.inl ∘ .inl) fun h =>
    h.elim .inr fun h => .inl (.inr (e.avoidArm (.inr h)))
  have hcpT : ∀ p ∈ laidCarry Tr s6 cpsT, Tr.ax = true ∧ ∃ q ∈ ns, p = (q.1, q.2.2) :=
    fun p hp => hcase.elim (fun ⟨_, _, _, h3⟩ => absurd (mem_laidCarry hp) (by simp [h3]))
      fun ⟨h1, _, he, _⟩ => ⟨h1, hns.mem_pairs.1 p (he ▸ mem_laidCarry hp)⟩
  have hcpE : ∀ p ∈ laidCarry Er s6 cpsE, ∃ q ∈ nsE, p = (q.1, q.2.2) := fun p hp =>
    hnsE.mem_pairs.1 p (mem_laidCarry hp)
  have hcp6 : ∀ x ∈ (laidCarry Tr s6 cpsT).map (·.2) ++ (laidCarry Er s6 cpsE).map (·.2),
      Drawn s6 st' x := fun x hx => by
    rcases (List.mem_append.1 hx).imp List.mem_map.1 List.mem_map.1 with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact (hcpT p hp).2.elim fun q ⟨hq, he⟩ => he ▸ (hns.drawn q hq).2.1.mono hnx.2.2.2.2.2
    · obtain ⟨q, hq, rfl⟩ := hcpE p hp
      exact ((hnsE.drawn q hq).2.1.mono ht.late.2.2.2.2.2).of_le a7T hnx.2.2.2.2.1
  refine ⟨hTk, hEk, fun n hn hd => ?_, fun n hn m hm he => ?_, fun n hn q hq he => ?_,
    fun n hn q hq he => ?_, fun p hp => ?_, ?_, hcpT, hcpE,
    hcp6, fun l x hx hp => ?_⟩
  · rcases hTk n hn with hk | ⟨y, hy⟩
    · exact not_drawn_of n s7T st' s5 s6 hk (a7T.trans hav.2.2.2.1) (.inr hnx.2.2.2.2.1) hd
    · exact hd.not_below ((dl_nmBelow hs.wf5 hy).imp fun b ⟨j, h1, h2⟩ => ⟨j, h1, by omega⟩)
  · rcases hTk n hn with hk | ⟨y, hy⟩
    · exact not_drawn_of n s1 s4 s5 s6 hk hav.1 (.inl hnx.2.2.1) (he ▸ hs.pre.drawn m hm)
    · exact (hs.preNm hm y).2.1 (he ▸ hy)
  · rcases hTk n hn with hk | ⟨z, hz⟩
    · exact not_drawn_of n s6 s7T s5 s6 hk hav.2.2.2.1 (.inr (Nat.le_refl _))
        (he ▸ (hns.drawn q hq).2.1)
    · obtain ⟨b, j, h1, h2⟩ := dl_nmBelow hs.wf5 hz
      exact (hns.drawn q hq).2.1.not_below ⟨b, j, he ▸ h1, by omega⟩
  · rcases hEk n hn with hk | ⟨y, hy⟩
    · exact not_drawn_of n s7T s7E s4 s5 hk (a7T.trans hav.2.2.2.1) (.inr (by omega))
        (he ▸ (hnsE.drawn q hq).2.1)
    · obtain ⟨b, j, h1, h2⟩ := dl_nmBelow hs.wf4 hy
      exact (hnsE.drawn q hq).2.1.not_below ⟨b, j, he ▸ h1, by omega⟩
  · exact hcase.elim (fun ⟨_, _, he, _⟩ => hns.mem_pairs.1 p (he ▸ (List.mem_filter.1 hp).1))
      fun ⟨_, _, _, hc⟩ => by simp [hc] at hp
  · exact hcase.elim (fun ⟨_, _, hc, _⟩ => ((List.filter_sublist (l := cps3)).map (·.1)).nodup
      (hc ▸ hns.mem_pairs.2 hMnd)) fun ⟨_, _, _, hc⟩ => by simp [hc]
  simp only [ht.regs, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact .inl ⟨hx, hs.aft.pending ▸ hp⟩
  · exact .inr ⟨hx, (hs.armT.pendNew l x (hs.aft.pending ▸ hp)).resolve_right (e.regsE hs hx)⟩
  obtain ⟨b, j, h1, h2⟩ := hs.wf6.pending_fresh l x (hs.aft.pending ▸ hp)
  obtain ⟨b', j', h3, -, h4, -⟩ := hcp6 x (List.mem_append.2 hx)
  exact absurd (freshName_counter_inj (h1.symm.trans h3)) (by omega)


omit iOp iLF iLV in
/-- The carries map of the walk output of a laid-out `ite` one of whose arms always exits is that
    of the then arm's walk output `s6` with the new carried merges of the arms' copy pairs. -/
private theorem LaidEnvAx.outCarries (hns : SaveNs s6 M sv cp rs cps s7T ns) :
    st'.carries = laidCarries s6.carries Tr Er (laidCarry Tr s6 cpsT) (laidCarry Er s6 cpsE)
      (optVar gm?) (elseGuard κ gm? qm? rEm?) := by
  obtain ⟨nsE, hnsE⟩ := saveRestore_run e.run7E
  obtain ⟨e8, -, -, -⟩ := optFresh_facts (ht.gm.imp (·.2) (·.2))
  obtain ⟨e9, -, -, -⟩ := optFresh_facts (ht.qm.imp (·.2.2) (·.2))
  obtain ⟨e10, -, -, -⟩ := optFresh_facts (ht.rEm.imp (·.2.2) (·.2))
  rw [← show s10.carries = s6.carries by rw [e10, e9, e8, hnsE.eq, hns.eq]]
  rcases ht.out with ⟨-, -, h⟩ | ⟨-, -, -, -, -, -, hl⟩
  · rw [h]
  · obtain ⟨live, clock, hrun, -⟩ := liveAdd_run (rdc ++ RE.vars κ) _
    exact (congrArg (·.2.carries) (Except.ok.inj (hrun.symm.trans hl))).symm

omit iOp iLF iLV in
/-- The carried merges a laid-out `ite` one of whose arms always exits registered at a depth.
    First, with `m` new merges in front: the then arm's merges shifted by `m`, and each merge is
    one of these, one of the else arm, a new merge of the then arm before `m` at its innermost
    target, or a new merge of the else arm. Second, with `m` the new merges and the then arm's
    new ones in front: the then arm's merges, the else arm's merges shifted by `m`, its then
    arm's new merges, and the else arm's new merges, in front at the else arm's innermost
    target. -/
private theorem LaidEnvAx.rtxCls {nonnil : Prop}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc nonnil) (hns : SaveNs s6 M sv cp rs cps s7T ns)
    (hcp6 : ∀ x ∈ (laidCarry Tr s6 cpsT).map (·.2) ++ (laidCarry Er s6 cpsE).map (·.2),
      Drawn s6 st' x) (k : Nat) : (∃ m,
    (∀ i n v xB, CarryReg Tr s6 k i n v xB → CarryReg r st' k (i + m) n v xB) ∧
    (∀ i n v xB, CarryReg r st' k i n v xB →
      (m ≤ i ∧ CarryReg Tr s6 k (i - m) n v xB) ∨ (∃ i', CarryReg Er s5 k i' n v xB) ∨
      (i < m ∧ Tr.tgt.max? = some k ∧ ∃ p ∈ laidCarry Tr s6 cpsT,
        (n, v, xB) = (p.1, .ite (optVar gm?) (.var p.2) (.var p.1), p.2)) ∨
      ∃ p ∈ laidCarry Er s6 cpsE,
        (n, v, xB) = (p.1, .ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)) ∧
    (Tr.tgt.max? = some k → ∀ p ∈ laidCarry Tr s6 cpsT, ∃ i, i < m ∧
      CarryReg r st' k i p.1 (.ite (optVar gm?) (.var p.2) (.var p.1)) p.2)) ∧
    ∃ m, (st'.carries.getD k []).length = m + (s5.carries.getD k []).length ∧
      (∀ i n v xB, CarryReg Er s5 k i n v xB → CarryReg r st' k (i + m) n v xB) ∧
      (Er.tgt.max? = some k → ∀ i q, (((laidCarry Er s6 cpsE).map fun p =>
          (p.1, .ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)).reverse)[i]? = some q →
            (st'.carries.getD k [])[i]? = some q ∧ i < m) ∧
      ∀ i n v xB, CarryReg r st' k i n v xB →
        (∃ i', CarryReg Tr s6 k i' n v xB) ∨ (m ≤ i ∧ CarryReg Er s5 k (i - m) n v xB) ∨
        (∃ p ∈ laidCarry Tr s6 cpsT,
          (n, v, xB) = (p.1, .ite (optVar gm?) (.var p.2) (.var p.1), p.2)) ∨
        (Er.tgt.max? = some k ∧ (((laidCarry Er s6 cpsE).map fun p =>
          (p.1, .ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)).reverse)[i]? =
            some (n, v, xB) ∧ i < m) := by
  generalize hAE : (if Er.tgt.max? = some k then ((laidCarry Er s6 cpsE).map fun p =>
    (p.1, WExpr.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)).reverse else []) = AE
  generalize hAT : (if Tr.tgt.max? = some k then ((laidCarry Tr s6 cpsT).map fun p =>
    (p.1, WExpr.ite (optVar gm?) (.var p.2) (.var p.1), p.2)).reverse else []) = AT
  have hk : st'.carries.getD k [] = (AE ++ AT) ++ s6.carries.getD k [] := by
    rw [e.outCarries ht hns, rex_getD, hAE, hAT, List.append_assoc]
  obtain ⟨new, hnew, hdr⟩ := hs.armT.carriesNew k
  have hreg : ∀ x, x ∈ r.regs.toList ↔ x ∈ Tr.regs.toList ∨ x ∈ Er.regs.toList ∨
      x ∈ (laidCarry Tr s6 cpsT).map (·.2) ++ (laidCarry Er s6 cpsE).map (·.2) := fun x => by
    simp only [ht.regs, List.mem_append, or_assoc]
  refine ⟨⟨(AE ++ AT).length, fun i n v xB ⟨hget, hx⟩ => ⟨?_, (hreg xB).2 (.inl hx)⟩,
    fun i n v xB ⟨hget, hx⟩ => ?_, fun hK p hp => ?_⟩, (AE ++ AT).length + new.length,
    by rw [hk, hnew]; simp only [List.length_append]; omega,
    fun i n v xB ⟨hget, hx⟩ => ⟨?_, (hreg xB).2 (.inr (.inl hx))⟩, ?_, fun i n v xB ⟨hg, hx⟩ => ?_⟩
  · rwa [hk, List.getElem?_append_right (by omega), Nat.add_sub_cancel]
  · rw [hk] at hget
    by_cases hi : i < (AE ++ AT).length
    · have hm := List.mem_of_getElem? (List.getElem?_append_left hi ▸ hget)
      rw [← hAE, ← hAT] at hm
      rcases List.mem_append.1 hm with h | h <;> split at h <;>
        simp only [List.mem_reverse, List.mem_map, List.not_mem_nil] at h
      · exact h.elim fun p ⟨hp, he⟩ => .inr (.inr (.inr ⟨p, hp, he.symm⟩))
      · exact h.elim fun p ⟨hp, he⟩ => .inr (.inr (.inl ⟨hi, ‹_›, p, hp, he.symm⟩))
    rw [List.getElem?_append_right (by omega)] at hget
    rcases (hreg xB).1 hx with hx | hx | hx
    · exact .inl ⟨by omega, hget, hx⟩
    · rw [hnew] at hget
      by_cases hi3 : i - (AE ++ AT).length < new.length
      · exact (e.regsE hs hx
          (hdr _ (List.mem_of_getElem? (List.getElem?_append_left hi3 ▸ hget)))).elim
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hi3)] at hget
        exact .inr (.inl ⟨_, hget, hx⟩)
    · obtain ⟨⟨b, j, h1, h2⟩, -⟩ := hs.wf6.carries_get (List.mem_of_getElem? hget)
      obtain ⟨b', j', h3, -, h4, -⟩ := hcp6 _ hx
      exact absurd (freshName_counter_inj (h1.symm.trans h3)) (by omega)
  · obtain rfl := (ite_eq_left hK).symm.trans hAT
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (List.mem_reverse.2 (List.mem_map_of_mem
      (f := fun p => (p.1, WExpr.ite (optVar gm?) (.var p.2) (.var p.1), p.2)) hp))
    have hlt := (List.getElem?_eq_some_iff.1 hj).1
    refine ⟨AE.length + j, by simp only [List.length_append]; omega, ?_,
      (hreg _).2 (.inr (.inr (List.mem_append_left _ (List.mem_map_of_mem hp))))⟩
    rwa [hk, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hlt]
  · rw [hk, hnew, ← List.append_assoc,
      List.getElem?_append_right (by rw [List.length_append]; omega)]
    simpa only [List.length_append, Nat.add_sub_cancel] using hget
  · intro hK i q hq
    obtain rfl := (ite_eq_left hK).symm.trans hAE
    have hlt := (List.getElem?_eq_some_iff.1 hq).1
    refine ⟨?_, by simp only [List.length_append] at hlt ⊢; omega⟩
    rwa [hk, List.append_assoc, List.getElem?_append_left hlt]
  rw [hk] at hg
  by_cases hi1 : i < AE.length
  · rw [List.append_assoc, List.getElem?_append_left hi1] at hg
    split at hAE <;> subst hAE
    · exact .inr (.inr (.inr ⟨‹_›, hg, by simp only [List.length_append]; omega⟩))
    · simp at hi1
  by_cases hi2 : i < (AE ++ AT).length
  · rw [List.getElem?_append_left hi2, List.getElem?_append_right (by omega)] at hg
    split at hAT <;> subst hAT
    · obtain ⟨p, hp, he⟩ := List.mem_map.1 (List.mem_reverse.1 (List.mem_of_getElem? hg))
      exact .inr (.inr (.inl ⟨p, hp, he.symm⟩))
    · simp at hg
  rw [List.getElem?_append_right (by omega)] at hg
  rcases (hreg xB).1 hx with hx | hx | hx
  · exact .inl ⟨_, hg, hx⟩
  · rw [hnew] at hg
    by_cases hi3 : i - (AE ++ AT).length < new.length
    · exact (e.regsE hs hx (hdr _ (List.mem_of_getElem? (List.getElem?_append_left hi3 ▸ hg)))).elim
    · rw [List.getElem?_append_right (by omega), Nat.sub_sub] at hg
      exact .inr (.inl ⟨by omega, hg, hx⟩)
  · obtain ⟨⟨b, j, h1, h2⟩, -⟩ := hs.wf6.carries_get (List.mem_of_getElem? hg)
    obtain ⟨b', j', h3, -, h4, -⟩ := hcp6 _ hx
    exact absurd (freshName_counter_inj (h1.symm.trans h3)) (by omega)

omit iLI e ht in
include iIL in
/-- The reach update of a laid-out `ite` runs from a value-valued store in which the variables of
    `κ` hold Booleans and, when the update is emitted, `rT` and the variables of `κE` hold
    Booleans and `κE` holds or fails.  Let `xv` be the truth of `rT ∨ κE`.  The run changes only
    the variables of `κ`, which stay Boolean; when the update is empty the run is empty and keeps
    the store; otherwise, under `top` its trace is the assumption, feasible exactly when `xv`, and
    under a variable context it emits nothing and makes the context hold when `xv` (and, for
    `q ∧ ¬g`, `q` holds and differs from `g`) and fail otherwise. -/
private theorem run_U' (hF : WellFormedSemanticEvalBase F)
    (hres : resolveItems T Y (laidU κ κE rT Tr Er d).toList = .ok iU) (hC : WellFormedStore σ F)
    (hrT : (laidU κ κE rT Tr Er d).isNil = false →
      σ rT = some (HasBool.ttVal F) ∨ σ rT = some (HasBool.ffVal F))
    (hE : (laidU κ κE rT Tr Er d).isNil = false → κE.Holds F σ ∨ κE.Fails F σ)
    (hκ : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F))
    (hκE : (laidU κ κE rT Tr Er d).isNil = false →
      ∀ y ∈ RE.vars κE, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
    ∃ tr σ', MainRun F iU σ tr σ' ∧ WellFormedStore σ' F ∧ (∀ y, y ∉ RE.vars κ → σ' y = σ y) ∧
      (∀ y ∈ RE.vars κ, σ' y = some (HasBool.ttVal F) ∨ σ' y = some (HasBool.ffVal F)) ∧
      ((laidU κ κE rT Tr Er d).isNil = true → tr = [] ∧ σ' = σ) ∧
      ((laidU κ κE rT Tr Er d).isNil = false →
        (κ = .top → (Trace.AssumptionsHold P evalInterp () tr ↔
          (σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ))) ∧
        (κ ≠ .top → tr = [] ∧
          ((σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ) →
            (∀ q g, κ = .andNeg q g → σ q = some (HasBool.ttVal F) ∧ q ≠ g) →
            κ.Holds F σ') ∧
          (¬ (σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ) → κ.Fails F σ'))) ∧
      ∀ q g, κ = .andNeg q g → ∀ y, y ≠ g → σ' y = σ y := by
  cases hUn : (laidU κ κE rT Tr Er d).isNil
  · obtain ⟨tr, σ', h1, h2, h3, h4, -, h6, h7⟩ := run_U hF hres hC (hrT hUn) (hE hUn) hκ (hκE hUn)
    exact ⟨tr, σ', h1, h2, h3, h4, nofun, fun _ => h6 hUn, h7⟩
  · obtain rfl := resolve_isNil hUn hres
    exact ⟨[], σ, .nil, hC, fun _ _ => rfl, hκ, fun _ => ⟨rfl, rfl⟩, nofun, fun _ _ _ _ _ => rfl⟩

include iIL in
/-- After the saves around the else arm of a laid-out `ite` one of whose arms always exits, with a
    nonempty body: from the store `σS` the saves reach (described relative to the restored store
    `σR`, which holds the guard value `gv` at the guard and the merge guard, `gv` true where the
    context holds at `σL` and false where it fails), the else arm runs off its path to `σEr`, its
    copies and restores to `σR2` and the merges (over the set `EA`) to `σM2`.  Names keep their
    values in `σR` outside the else arm's writes, copies and merges; the context variables keep
    their values in `σL`, the merge guard `gv`, the then-arm reach its value in `σR`, and the
    else-arm context fails at `σM2`, its variables Boolean, when the reach update is not empty. -/
private theorem LaidEnvAx.elseTail {nsE : List (P.Ident × P.Ident × P.Ident)} {nonnil : Prop}
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc nonnil) (hns : SaveNs s6 M sv cp rs cps s7T ns)
    (hnsE : SaveNs s7T (laidCE Er s6 s4.clock) svE cpE rsE cpsE s7E nsE)
    (hlm : ∀ p ∈ cps3.filter (fun p => liveBefore s6 p.1 s4.clock), ∃ q ∈ ns, p = (q.1, q.2.2))
    (hlnd : ((cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1)).Nodup)
    {iCPE iRSE iMG iRE : List (Item P)} {EA : Std.HashSet P.Ident}
    (hE : resolveItems T Y Er.out.toList = .ok iE) (hCPE : resolveItems T Y cpE.toList = .ok iCPE)
    (hRSE : resolveItems T Y rsE.toList = .ok iRSE) (hMG : resolveItems T Y (laidMerges gm? EA
      (cps3.filter fun p => liveBefore s6 p.1 s4.clock)).toList = .ok iMG)
    {σR σD σM σS : SemanticStore P} (hshE : ShL F ess σs K) (hfr : FreshInv Lc Ex st' σL)
    (hcκ : gv = (HasBool.ttVal F) ∧ κ.Holds F σL ∨ gv = (HasBool.ffVal F) ∧ κ.Fails F σL)
    (hκb : ∀ y ∈ RE.vars κ, σL y = some (HasBool.ttVal F) ∨ σL y = some (HasBool.ffVal F))
    (hκR : ∀ y ∈ RE.vars κ, σR y = σL y)
    (hq1 : ∀ q ∈ ns, (σL q.1).isSome ∧ q.1 ∉ RE.vars κ)
    (hCEb : ∀ q ∈ nsE, (σL q.1).isSome ∧ q.1 ∉ RE.vars κ) (hRb : ∀ n, (σL n).isSome → (σR n).isSome)
    (hdR : ∀ x ∈ S, x ∈ contFV (ess :: ess :: k) → ∀ n, curName s5 x = some n → (σL n).isSome ∧
      ∃ w, σR n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty)
    (hvR : ∀ q ∈ ns, ∃ w w' ty, σR q.1 = some w ∧ σR q.2.2 = some w' ∧
      HasVal.valueOfTy F w ty ∧ HasVal.valueOfTy F w' ty)
    (hgmR : ∀ x, gm? = some x → σR x = some gv) (hCS : WellFormedStore σS F)
    (hgR : σR g = some gv) (h0R : ∀ x, rE? = some x → σR x = none)
    (hlateR : ∀ n, Drawn s7T st' n → n ∉ laidQm κ qm? → (∀ y, gm? = some y → n ≠ y) → σR n = none)
    (hcaseD : (iRE = [] ∧ σD = σR ∧ (rE? = none ∨
        (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil && rEm?.isNone) = true)) ∨
      ∃ x, rE? = some x ∧ σD = SemanticStore.update σR x (HasBool.ffVal F))
    (hcaseM : (σM = σD ∧ ∀ r x, rE? = some r → rEm? = some x → False) ∨
      ∃ r x, rE? = some r ∧ rEm? = some x ∧ σM = SemanticStore.update σD x (HasBool.ffVal F))
    (hMx : ∀ n, σM n = σD n ∨ (rEm? = some n ∧ σM n = some (HasBool.ffVal F)))
    (hothS : ∀ n, (∀ q ∈ nsE, n ≠ q.2.1) → σS n = σM n) (hSL : ∀ q ∈ nsE, σS q.2.1 = σR q.1)
    (hRbE : ∀ q ∈ nsE, ∃ w, σR q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hSdesc : ∀ n, σS n = σR n ∨ (rE? = some n ∧ σS n = some (HasBool.ffVal F)) ∨
      (rEm? = some n ∧ σS n = some (HasBool.ffVal F)) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σS n = σR q.1))
    (hkeep : ∀ σE : SemanticStore P, (∀ n, σE n = σR n ∨
      (rE? = some n ∧ σE n = some (HasBool.ffVal F)) ∨
      (rEm? = some n ∧ σE n = some (HasBool.ffVal F)) ∨ (∃ q ∈ nsE, n = q.2.1 ∧ σE n = σR q.1)) →
      (∀ n, (σL n).isSome → σE n = σR n) ∧ (∀ n w, σE n = some w → Y[n]? = none →
        ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
        FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE) :
    ∃ trE σEr σEo σC2 σR2 σM2, MainRun F iE σS trE σEr ∧ MainRun F iCPE σEr [] σC2 ∧
      MainRun F iRSE σC2 [] σR2 ∧ MainRun F iMG σR2 [] σM2 ∧
      Trace.AssumptionsHold P evalInterp () trE ∧ WellFormedStore σEr F ∧ WellFormedStore σM2 F ∧
      OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 κE
        (if Er.ax = true then S else scopeAfter S ess) (contFV (ess :: k)) σEo ∧
      Frame κE σS σEr ∧ SnapFF F Er s5 none σEr ∧ CarryFF F T Y Er s5 σEr ∧
      CarryOK F T Y Er s5 σEr ∧ ShEnds Er s5 none K ∧ (∀ n, (σEr n).isSome → σEo n = σEr n) ∧
      (∀ n, rE? ≠ some n → ¬ Drawn s7T st' n → σS n = σR n) ∧
      (∀ n, Drawn s7T st' n → σEr n = σS n) ∧ (∀ n, (σL n).isSome → n ∉ RE.vars κ → σEr n = σR n) ∧
      (∀ n, (∀ q ∈ nsE, n ≠ q.2.2) → σR2 n = σEr n) ∧ (∀ q ∈ nsE, σR2 q.2.2 = σEr q.1) ∧
      (∀ q ∈ nsE, ∃ ty, tyOfName T Y q.1 = .ok ty) ∧ (∀ q ∈ ns, σR2 q.1 = σR q.1) ∧
      (∀ q ∈ ns, σR2 q.2.2 = σR q.2.2) ∧ (∀ p ∈ cps3.filter (fun p => liveBefore s6 p.1 s4.clock),
        σM2 p.1 = mergeVal F σR2 gm? EA p) ∧
      (∀ n, n ∉ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1) → σM2 n = σR2 n) ∧
      (∀ x, gm? = some x → σM2 x = some gv) ∧ (∀ y, qm? = some y → σM2 y = σR y) ∧
      (∀ y, rEm? = some y → σM2 y = some (HasBool.ffVal F)) ∧ (∀ y ∈ RE.vars κ, σM2 y = σL y) ∧
      (∀ b, σR rT = some b → σM2 rT = some b) ∧
      ((laidU κ κE rT Tr Er d).isNil = false → κE.Fails F σM2 ∧
        ∀ y ∈ RE.vars κE, σM2 y = some (HasBool.ttVal F) ∨ σM2 y = some (HasBool.ffVal F)) := by
  have hnx := hs.nexts
  obtain ⟨-, -, -, -, a7T, -, -, -, hrEng, hrEmD⟩ := e.saveE ht hs hns
  obtain ⟨hlg, hlq, hlr, -, -, hnE⟩ := ht.late
  have a7E : s7E.avoid = s7T.avoid := by rw [hnsE.eq]
  have hsvED : ∀ q ∈ nsE, Drawn s7T st' q.2.1 := fun q hq => (hnsE.drawn q hq).1.mono hnE
  have hcpED : ∀ q ∈ nsE, Drawn s7T st' q.2.2 := fun q hq => (hnsE.drawn q hq).2.1.mono hnE
  have hcpD : ∀ q ∈ ns, Drawn s6 s7T q.2.2 := fun q hq => (hns.drawn q hq).2.1
  have hLlate : ∀ n, (σL n).isSome → ¬ Drawn s7T st' n := fun n hn hd => by
    simp [e.unbound hs hfr (.inr (hd.of_le a7T hnx.2.2.2.2.1))] at hn
  have hSLb := (hkeep σS hSdesc).1
  have hκS : ∀ y ∈ RE.vars κ, σS y = σL y := fun y hy =>
    (hSLb y (by rcases hκb y hy with h | h <;> simp [h])).trans (hκR y hy)
  have hSR : ∀ n, rE? ≠ some n → ¬ Drawn s7T st' n → σS n = σR n := fun n hr hd => by
    rcases hSdesc n with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, rfl, -⟩
    · exact h
    · exact absurd h hr
    · exact absurd (hrEmD n h).1 hd
    · exact absurd (hsvED q hq) hd
  have hSg : σS g = some gv := (hSR g (fun h => (hs.pre.rE_ne g h).1 rfl) fun hd =>
    (hs.pre.drawn g (.inl rfl)).disj hd (by omega)).trans hgR
  obtain ⟨trE, σEr, σEo, hrunE, hfeasE, hCEr, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE, hEo1, -,
    hEo3⟩ := e.offE hs hE hshE hCS (fun σE hCE hdesc hreach hbools => ⟨hCE, hreach, hbools,
      fun x hx hv n hn => (hdR x hx hv n hn).2.imp fun _ h =>
        ⟨((hkeep σE hdesc).1 n (hdR x hx hv n hn).1).trans h.1, h.2⟩,
      (hkeep σE hdesc).2.1, (hkeep σE hdesc).2.2⟩) hSdesc <| by
    have hc := e.ctx
    cases κ with
    | top =>
      obtain ⟨rfl, -, -⟩ := hc
      rcases hcκ with ⟨rfl, -⟩ | ⟨-, ⟨⟩⟩
      exact .inl ⟨hSg, fun y hy => .inl (List.mem_singleton.1 hy ▸ hSg)⟩
    | name q =>
      obtain ⟨rfl, -, -⟩ := hc
      have hq := hκS q (by simp [RE.vars])
      refine .inl ⟨?_, fun y hy => ?_⟩
      · exact hcκ.elim (fun ⟨he, h⟩ => .inr ⟨hq.trans h, he ▸ hSg⟩) fun ⟨he, h⟩ =>
          .inl ⟨hq.trans h, by simp [hSg, he]⟩
      · simp only [RE.vars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hq ▸ hκb _ (by simp [RE.vars])
        · rcases hcκ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [hSg]
    | neg g0 | andNeg q0 g0 =>
      obtain ⟨x, rfl, rfl, -⟩ := hc
      have hSD : σS x = σD x := by
        rw [hothS x fun q hq => hrEng x rfl _ (hsvED q hq)]
        exact (hMx x).elim id fun ⟨h, _⟩ => absurd rfl (hrEng x rfl x (hrEmD x h).1)
      rcases hcaseD with ⟨-, hDR, hr | hb⟩ | ⟨x', hx', hDx'⟩
      · cases hr
      · obtain ⟨⟨hEn, hUn⟩, -⟩ : (_ ∧ _) ∧ _ := by simpa only [Bool.and_eq_true] using hb
        refine .inr ⟨x, rfl, by rw [hSD, hDR]; exact h0R x rfl, hEn, hUn, fun n => ?_⟩
        exact (update_cases σS x (HasBool.ffVal F) n).elim (fun h => h ▸ hSdesc n) fun ⟨he, h⟩ =>
          .inr (.inl ⟨he ▸ rfl, h⟩)
      · cases hx'
        have hSx : σS x = some (HasBool.ffVal F) := by
          rw [hSD, hDx']; exact (update_facts σR x (HasBool.ffVal F)).1
        exact .inl ⟨hSx, fun y hy => .inr (List.mem_singleton.1 hy ▸ hSx)⟩
  have hlateκE : ∀ n, Drawn s7T st' n → n ∉ RE.vars κE := fun n hn hm =>
    (e.of_κEvars' hm).elim (fun h => (hs.pre.drawn g (.inl rfl)).disj (h ▸ hn) (by omega))
      fun h => h.elim (hrEng n · n hn rfl) fun h => (e.of_ctxNe hs h).2.2.2 s7T st' (by omega) hn
  have hkE : ∀ n, (σL n).isSome → n ∉ RE.vars κ → σEr n = σR n := fun n hn hnk => by
    refine (hfrmE n (by rw [hSLb n hn]; exact hRb n hn) fun hm => ?_).trans (hSLb n hn)
    exact (e.of_κEvars' hm).elim (fun h => by simp [h, e.unbound hs hfr (.inl (.inl rfl))] at hn)
      fun h => h.elim (fun h => by simp [e.unbound hs hfr (.inl (.inr (.inr h)))] at hn) hnk
  have hlE : ∀ n, Drawn s7T st' n → σEr n = σS n := fun n hn =>
    e.lateE hs hE hrunE (hn.of_le a7T hnx.2.2.2.2.1) (hlateκE n hn)
  have hcpEL : ∀ q ∈ nsE, σEr q.2.2 = none := fun q hq => by
    rw [hlE _ (hcpED q hq)]
    rcases hSdesc q.2.2 with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨p, hp, he, -⟩
    · refine h.trans (hlateR _ (hcpED q hq) (fun h' => (hnsE.drawn q hq).2.1.disj
        (hlq _ (mem_laidQm h')).1 (Nat.le_refl _)) fun y hy he => ?_)
      exact (hnsE.drawn q hq).2.1.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)
    · exact absurd rfl (hrEng _ h _ (hcpED q hq))
    · exact ((hnsE.drawn q hq).2.1.disj (hlr _ h).1 (Nat.le_refl _)).elim
    · exact absurd he (flat_ne nsE hnsE.nodup p hp q hq).symm
  have hsrcE : ∀ q ∈ nsE, ∃ w, σEr q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    (hRbE q hq).imp fun _ h => ⟨(hkE q.1 (hCEb q hq).1 (hCEb q hq).2).trans h.1, h.2⟩
  obtain ⟨σC2, σR2, hrunC2, hrunR2, hCR2, hRcp2, hRv2, hRo2, htyC2⟩ := copyRestore e.hF hnsE
    (laidCE_nodup _ _ _) hCEr hCPE hRSE hcpEL hsrcE (fun q hq => (hsrcE q hq).imp fun _ h =>
      ⟨by rw [hlE _ (hsvED q hq), hSL q hq, ← hkE q.1 (hCEb q hq).1 (hCEb q hq).2, h.1], h.2⟩)
    fun q hq p hp => ⟨fun he => hLlate _ (he ▸ (hCEb q hq).1) (hsvED p hp),
      fun he => hLlate _ (he ▸ (hCEb q hq).1) (hcpED p hp)⟩
  have hR2 : ∀ n, (∀ q ∈ nsE, n ≠ q.2.2) → σR2 n = σEr n := fun n hn => by
    rcases Classical.em (∃ q ∈ nsE, n = q.1) with ⟨q, hq, rfl⟩ | hq
    · rw [hRv2 q hq, hlE _ (hsvED q hq), hSL q hq, hkE q.1 (hCEb q hq).1 (hCEb q hq).2]
    · exact hRo2 n fun q hq' => ⟨fun he => hq ⟨q, hq', he⟩, hn q hq'⟩
  have hEq1 : ∀ q ∈ ns, σR2 q.1 = σR q.1 := fun q hq => by
    rw [hR2 _ fun p hp he => hLlate _ (he ▸ (hq1 q hq).1) (hcpED p hp),
      hkE q.1 (hq1 q hq).1 (hq1 q hq).2]
  have hEq2 : ∀ q ∈ ns, σR2 q.2.2 = σR q.2.2 := fun q hq => by
    have hcd := hcpD q hq
    have hSc : σS q.2.2 = σR q.2.2 :=
      hSR _ (fun h => (hs.saveNe hcd).2.2.2 _ h rfl) fun hd => hcd.disj hd (Nat.le_refl _)
    obtain ⟨w, w', ty, -, hw', -⟩ := hvR q hq
    rw [hR2 _ fun p hp he => hcd.disj (he ▸ (hnsE.drawn p hp).2.1) (Nat.le_refl _),
      hfrmE _ (by simp [hSc, hw']) fun hm => ?_, hSc]
    exact (e.of_κEvars' hm).elim (hs.saveNe hcd).1 fun h => h.elim ((hs.saveNe hcd).2.2.2 _ · rfl)
      fun h => (e.of_ctxNe hs h).2.2.2 s6 s7T (by omega) hcd
  have hnml : ∀ n, (σL n).isSome = false ∨ n ∈ RE.vars κ →
      n ∉ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1) := fun n hn hin => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hin
    obtain ⟨q, hq, rfl⟩ := hlm p hp
    exact hn.elim (fun h => by simp [(hq1 q hq).1] at h) (hq1 q hq).2
  have hlL : ∀ y, Drawn s7E st' y → (σL y).isSome = false := fun y hy => by
    simp [e.unbound hs hfr (.inr ((hy.of_le a7E hnsE.next).of_le a7T hnx.2.2.2.2.1))]
  have hlR2 : ∀ y, Drawn s7E st' y → σR2 y = σS y := fun y hy => by
    rw [hR2 y fun q hq he => (hnsE.drawn q hq).2.1.disj (he ▸ hy) (Nat.le_refl _),
      hlE y (hy.of_le a7E hnsE.next)]
  have hSl : ∀ y, Drawn s7E st' y → rEm? ≠ some y → σS y = σR y := fun y hy hm => by
    rcases hSdesc y with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, he, -⟩
    · exact h
    · exact absurd rfl (hrEng _ h _ (hy.of_le a7E hnsE.next))
    · exact absurd h hm
    · exact ((hnsE.drawn q hq).1.disj (he ▸ hy) (Nat.le_refl _)).elim
  have hgmR2 : ∀ x, gm? = some x → σR2 x = some gv := fun x hx => (hlR2 x (hlg x hx).1).trans
    ((hSl x (hlg x hx).1 fun h => (hlr _ h).2.2.1 x hx rfl).trans (hgmR x hx))
  obtain ⟨σM2, hrunM2, hCM2, hvalM2, hMeq⟩ := run_merges e.hF gm? EA _ σR2 iMG hMG hCR2 hlnd
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hlm p hp
      exact hnml _ (.inl (by simp [e.unbound hs hfr (.inr ((hcpD q hq).mono hnx.2.2.2.2.2))])))
    (fun x hx => ⟨hgmR2 x hx ▸ (hcκ.imp (·.1) (·.1)).imp (congrArg some) (congrArg some),
      hnml x (.inl (hlL x (hlg x hx).1))⟩)
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hlm p hp
      obtain ⟨w, w', ty, hw, hw', ht1, ht2⟩ := hvR q hq
      exact ⟨w, w', ty, (hEq1 q hq).trans hw, (hEq2 q hq).trans hw', ht1, ht2⟩)
  have hrS : ∀ b, σR rT = some b → σS rT = some b := fun b hb =>
    (hSR rT (fun h => (hs.pre.rE_ne rT h).2 rfl) fun hd =>
      (hs.pre.drawn rT (.inr (.inl rfl))).disj hd (by omega)).trans hb
  refine ⟨trE, σEr, σEo, σC2, σR2, σM2, hrunE, hrunC2, hrunR2, hrunM2, hfeasE, hCEr, hCM2, hoffE,
    hfrmE, hsnE, hcfE, hcoE, hseE, hEo1, hSR, hlE, hkE, hR2, hRcp2, htyC2, hEq1, hEq2, hvalM2,
    hMeq, fun x hx => by rw [hMeq x (hnml x (.inl (hlL x (hlg x hx).1))), hgmR2 x hx],
    fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun b hb => ?_,
    fun hUn => (fun (hv : ∀ y ∈ RE.vars κE, σM2 y = σEo y) => ⟨of_failsCongr hoffE.reach hv,
      fun y hy => hv y hy ▸ hoffE.bools y hy⟩) fun y hy => ?_⟩
  · rw [hMeq y (hnml y (.inl (hlL y (hlq y hy).1))), hlR2 y (hlq y hy).1]
    exact hSl y (hlq y hy).1 fun h => (hlr _ h).2.2.2 y hy rfl
  · rw [hMeq y (hnml y (.inl (hlL y (hlr y hy).1))), hlR2 y (hlr y hy).1,
      hothS y fun q hq he => (hnsE.drawn q hq).1.disj (he ▸ (hlr y hy).1) (Nat.le_refl _)]
    rcases hcaseM with ⟨rfl, hno⟩ | ⟨r', x, -, hx, rfl⟩
    · exact ht.rEm.elim (fun ⟨hrs, _⟩ => (Option.isSome_iff_exists.1 hrs).elim fun r0 hr0 =>
        (hno r0 y hr0 hy).elim) fun ⟨_, hn, _⟩ => by simp [hn] at hy
    · cases hx.symm.trans hy
      exact (update_facts σD y (HasBool.ffVal F)).1
  · rw [hMeq y (hnml y (.inr hy)), ← hκS y hy,
      hR2 y fun q hq he => (e.of_ctxNe hs hy).2.2.2 s7T st' (by omega) (he ▸ hcpED q hq)]
    exact e.keepκ hs hE hrunE hfrmE hy (by rw [hκS y hy]; rcases hκb y hy with h | h <;> simp [h])
  · have hrd := hs.pre.drawn rT (.inr (.inl rfl))
    rw [hMeq rT (hnml rT (.inl (by simp [e.unbound hs hfr (.inl (.inr (.inl rfl)))]))),
      hR2 rT fun q hq he => hrd.disj (he ▸ hcpED q hq) (by omega),
      hfrmE rT (by simp [hrS b hb]) fun hm => ?_, hrS b hb]
    exact (e.of_κEvars' hm).elim (fun h => hs.pre.g_rT h.symm) fun h => h.elim
      (fun h => (hs.pre.rE_ne rT h).2 rfl) fun h => (e.of_ctxNe hs h).2.2.2 s1 s4 hnx.1 hrd
  · refine (hMeq y (hnml y ?_)).trans ((hR2 y fun q hq he => ?_).trans (congrFun (hEo3 hUn) y).symm)
    · exact (e.of_κEvars' hy).elim (fun h => .inl (by simp [h, e.unbound hs hfr (.inl (.inl rfl))]))
        fun h => h.elim (fun h => .inl (by simp [e.unbound hs hfr (.inl (.inr (.inr h)))])) .inr
    · exact hlateκE _ (hcpED q hq) (he ▸ hy)

include iLFs iIL in
/-- Off the loop-free path, a shadow run of a laid-out `ite` one of whose arms always exits gives
    a run of its output (`OffPost`), given the facts of its walk states (`LaidStates`, the saves
    before the then arm those of one run of `saveRestore` over `M`), the saved variables being
    current names of variables in scope that the arms mention. -/
private theorem LaidEnvAx.off
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm?
      st' rdc ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
        (cps3.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all
          Rope.isNil = false)) (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hsv : sv.toList = sv3.toList ++ svT.toList) (hcp : cp.toList = cp3.toList ++ cpT.toList)
    (hrs : rs.toList = rs3.toList ++ rsT.toList)
    (hcase : (Tr.ax = false ∧ M = interSet Tr.A Er.R ∧ cps = cps3 ∧ cpsT = []) ∨
      (Tr.ax = true ∧ M = laidCT Tr Er s6 s4.clock ∧ cps = cpsT ∧ cps3 = []))
    (hMv : ∀ x ∈ M, ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hCEv : ∀ x ∈ laidCE Er s6 s4.clock, ∃ z ∈ S,
      (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x) :
    ∀ σs σL K,
      OffInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σL →
      ShS F (.ite (.det c) tss ess md) σs K →
      OffPost F T Y Lc Ex st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        items σL K := by
  intro σs σL K hoff hsh
  have hnx := hs.nexts
  have hav := hs.avoids
  obtain ⟨nsE, hnsE, hleE, a7E, a7T, hqmD, hext, hextT, -, hrEmD⟩ := e.saveE ht hs hns
  obtain ⟨-, -, hTlate, hTpre, hTcp, hEcp, hlm, hlnd, hcpT, hcpE, hcp6, hregP⟩ :=
    e.decls ht hs hns hMnd hnsE hcase
  obtain ⟨hlg, hlq, hlr, -, hyoE, hnE⟩ := ht.late
  have hshT : ShL F tss σs (fun o => K (o.proj σs)) := shL_of_shB hsh.1
  have hshE : ShL F ess σs (fun o => K (o.proj σs)) := shL_of_shB hsh.2
  have hscope : (if r.ax = true then S else scopeAfter S [.ite (.det c) tss ess md]) = S := by
    split <;> simp [scopeAfter, Stmt.topInits]
  have hbnd : ∀ x, (∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
        curName st' z = some x) →
      ∃ w, σL x = some w ∧ ∀ ty, tyOfName T Y x = .ok ty → HasVal.valueOfTy F w ty :=
    fun x ⟨z, hz, hfv, hzn⟩ => hoff.defd z hz (mem_contFV_cons.2 (.inl (by
      rcases hfv with h | h <;> simp [Block.freeVars, Stmt.freeVars, h]))) x hzn
  have hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    hbnd q.1 (hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq))
  have hq1 : ∀ q ∈ ns, (σL q.1).isSome := fun q hq =>
    Option.isSome_iff_exists.2 ((hsrcS q hq).imp fun _ h => h.1)
  have hκt : κ ≠ .top := fun h => by subst h; exact hoff.reach
  have hgL : σL g = none := e.unbound hs hoff.fresh (.inl (.inl rfl))
  have hfr0 : FreshInv Lc Ex st0 σL := of_freshPost hoff.fresh (fun y hy => e.whole.taken y hy)
    e.whole.avoid e.whole.next (fun x y h => e.whole.nm x y h) fun y hy => .inl hy
  rcases ht.out with ⟨hnil, -, -⟩ | ⟨hnn, -, -, -, -, -, -⟩
  · obtain ⟨rfl, rfl, rfl, hT, hE, hregs⟩ := e.nilParts ht hs hns hsv hnil
    have hreg : ∀ x ∈ r.regs.toList, False := fun x hx => by simp [hregs] at hx
    have hgr := hs.pre.g_rT
    obtain ⟨trT, σT, hrunT, -, hoffT5, -, -, -, -, hshT'⟩ := (e.armTp hs hT).2.2 σs _ _
      (e.offT hs hns hoff.defd hoff.gtyped hoff.fresh (preStore_two hgr) nofun nofun
        (wfStore_update_bool (wfStore_update_bool hoff.canonL g (.inr rfl)) rT (.inr rfl))) hshT
    cases hrunT
    refine ⟨[], σL, .nil, nofun, ?_, fun _ _ _ => rfl, fun _ x hx => (hreg x hx).elim,
      fun _ _ _ _ _ hc => (hreg _ hc.2).elim, fun _ _ _ _ _ hc => (hreg _ hc.2).elim,
      ⟨fun hax => ?_, fun _ x hx => (hreg x hx).elim⟩⟩
    · rw [hscope]
      exact ⟨hoff.canonL, hoff.reach, hoff.bools, fun x hx hv n hn => hoff.defd x hx
        (mem_contFV_cons.2 (.inr hv)) n (e.of_cur0 hs hx hn).2.2, hoff.gtyped, hfr0⟩
    rw [ht.ax] at hax
    cases hTa : Tr.ax
    · exact (hshT'.1 hTa).elim fun _ h => ⟨_, h⟩
    have hrL : σL rT = none := e.unbound hs hoff.fresh (.inl (.inr (.inl rfl)))
    have hkB : ∀ n, (σL n).isSome →
        SemanticStore.update (SemanticStore.update σL g (HasBool.ffVal F)) rT (HasBool.ffVal F) n =
          σL n := fun n hn => by
      rw [(update_facts _ rT (HasBool.ffVal F)).2 n fun h => by simp [← h, hrL] at hn,
        (update_facts _ g (HasBool.ffVal F)).2 n fun h => by simp [← h, hgL] at hn]
    have hgB :
        SemanticStore.update (SemanticStore.update σL g (HasBool.ffVal F)) rT (HasBool.ffVal F) g =
          some (HasBool.ffVal F) := by
      rw [(update_facts _ rT (HasBool.ffVal F)).2 g (Ne.symm hgr),
        (update_facts _ g (HasBool.ffVal F)).1]
    delta laidPartsAx at hnil
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hnil
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEn, -, -, -, hUn⟩ := hnil
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hseE, -⟩ := e.offE (D := fun σE => ∀ n,
      σE n =
        SemanticStore.update (SemanticStore.update σL g (HasBool.ffVal F)) rT (HasBool.ffVal F) n ∨
        (rE? = some n ∧ σE n = some (HasBool.ffVal F))) hs hE hshE hoffT5.canonL
      (fun σE hCE hd hreach hbools => ⟨hCE, hreach, hbools, fun x hx hv n hn => by
        obtain ⟨w, hw, hty⟩ := hoff.defd x hx (contFV_else_sub hv) n (hs.cur5 hx hn).1
        refine ⟨w, ((hd n).resolve_right fun ⟨hr, _⟩ => ?_).trans ((hkB n ?_).trans hw), hty⟩
        · simp [e.unbound hs hoff.fresh (.inl (.inr (.inr hr)))] at hw
        · simp [hw],
      fun n w hw hY ty hty => (hd n).elim (fun h => hoffT5.gtyped n w (h ▸ hw) hY ty hty)
        fun ⟨hr, h⟩ => tyOfName_bool (e.preT hs (.inl (.inr (.inr hr))))
          (.inr (Option.some.inj (h.symm.trans hw)).symm) hty,
      fun y hy => (hd y).elim (fun h => by
        obtain ⟨l1, f1⟩ := hoffT5.fresh y (h ▸ hy)
        exact ⟨l1, fun b j hj ha =>
          (f1 b j hj ha).imp_right (.imp_right (.imp_right (.imp_right .inl)))⟩) fun ⟨hr, _⟩ => by
        obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn y (.inr (.inr hr))
        have h2' : s5.avoid.contains y = false := by rw [hav.2.2.1, ← hav.1]; exact h2
        exact ⟨fun _ hfa => by simp [hfa b j h1] at h2',
          fun _ _ _ _ => .inr (.inr (.inr (.inr (.inr hr))))⟩⟩) (fun _ => .inl rfl) <| by
      rcases e.ctx.cases' with ⟨hr, h | ⟨q, hq, h⟩⟩ | ⟨x, hx, hκE⟩
      · have hc := e.ctx
        exact absurd (by cases κ <;> first | rfl | simp [LaidCtx, h] at hc) hκt
      · have hq' : σL q = some (HasBool.ffVal F) := by simpa [hq, RE.Fails] using hoff.reach
        have hqB := (hkB q (by simp [hq'])).trans hq'
        refine .inl ⟨by rw [h]; exact .inl ⟨hqB, by simp [hgB]⟩, fun y hy => ?_⟩
        simp only [h, RE.vars, List.mem_cons, List.not_mem_nil, or_false] at hy
        exact hy.elim (fun h => by subst h; exact .inr hqB) fun h => by subst h; exact .inr hgB
      · obtain ⟨hxg, hxr⟩ := hs.pre.rE_ne x hx
        refine .inr ⟨x, hκE, ?_, hEn, hUn, fun n =>
          (update_cases _ x (HasBool.ffVal F) n).imp_right fun ⟨he, h⟩ => ⟨he ▸ hx, h⟩⟩
        rw [(update_facts _ rT (HasBool.ffVal F)).2 x (Ne.symm hxr),
          (update_facts _ g (HasBool.ffVal F)).2 x (Ne.symm hxg)]
        exact e.unbound hs hoff.fresh (.inl (.inr (.inr hx)))
    exact (hseE.1 (by simpa [hTa] using hax)).elim fun _ h => ⟨_, h⟩
  have ⟨ce, iRT, iGM, iQM, iSV, iT, iCP, iRS, iRE, iREM, iSVE, iE, iCPE, iRSE, iMG, iU, hsp⟩ :=
    e.split ht hnn hsv hcp hrs
  obtain ⟨hce, hRT, hGM, hQM, hSV, hT, hCP, hRS, hRE, hREM, hSVE, hE, hCPE, hRSE, hMG, hU,
    hitems⟩ := hsp
  obtain ⟨σB, hrun0, hCB, hB, hqmv⟩ := e.preRunQ hs hns hoff.fresh hoff.canonL hRT hGM
    hQM hqmD (fun q x hq _ => hoff.bools q (by simp [hq, RE.vars]))
    hSV (ev_kAnd_fails e.hF hoff.canonL hoff.reach hce
      (e.guardOff hs hoff) hoff.bools) (.inr rfl) hsrcS
  obtain ⟨trT, σ1, hrunT, hfeasT, hC1, hfr1, hgt1, hk1, hpre1, hsv1, hunb1, hsnT, hcfT, hcoT, hseT,
    hrT1, hext1⟩ := e.of_T hs hns hoff.defd hoff.gtyped hoff.fresh hq1 hB hext hextT hCB hT hshT
  have hκb : ∀ y ∈ RE.vars κ, (σL y).isSome := fun y hy => by
    rcases hoff.bools y hy with h | h <;> simp [h]
  obtain ⟨σR, σD, σM, σS, hmid⟩ := e.midG ht hs hns hMnd hnsE
      hoff.fresh hsrcS (fun q hq => (hbnd q.1 (hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq))).elim
        fun w ⟨hw, hty⟩ => ⟨by simp [hw], w, (hk1 _ (by simp [hw])).trans hw, hty⟩) hB hext hC1
      hfr1 hgt1 (fun y hy => hk1 y (hκb y hy))
      (fun q hq => (hsrcS q hq).imp fun _ h => ⟨(hk1 _ (hq1 q hq)).trans h.1, h.2⟩) hpre1 hsv1
      hunb1 hCP hRS hREM hSVE (.inr rfl)
      fun σR hCR hκR hgR h0R => rEiRun e.hF hCR h0R (.inr (.inl ⟨of_failsCongr hoff.reach hκR,
        .inr hgR, fun y hy => (hκR y hy).symm ▸ hoff.bools y hy, rfl⟩)) hRE
  obtain ⟨hrunCS, hCS, htyC, hσ1cp, hlate, -, -, hRcp, -, hgR, h0R, hlateR, hcaseD, hcaseM, hMx,
    hothS, hSL, hRbE, hSdesc, hkeep, hk1C, -⟩ := hmid
  have hcpD : ∀ q ∈ ns, Drawn s6 s7T q.2.2 := fun q hq => (hns.drawn q hq).2.1
  obtain ⟨hkR, hR1⟩ := hk1C hk1
  have hcpED : ∀ q ∈ nsE, Drawn s7T st' q.2.2 := fun q hq => (hnsE.drawn q hq).2.1.mono hnE
  have hLlate : ∀ n, (σL n).isSome → ¬ Drawn s7T st' n := fun n hn hd => by
    simp [e.unbound hs hoff.fresh (.inr (hd.of_le a7T hnx.2.2.2.2.1))] at hn
  have hCEb : ∀ q ∈ nsE, (σL q.1).isSome ∧ q.1 ∉ RE.vars κ := fun q hq => by
    obtain ⟨z, hz, hfv, hzn⟩ := hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq)
    obtain ⟨w, hw, -⟩ := hbnd q.1 ⟨z, hz, hfv, hzn⟩
    exact ⟨by simp [hw], fun hk => (e.of_ctxNe hs hk).2.2.1 z hz hzn⟩
  have hq1κ : ∀ q ∈ ns, q.1 ∉ RE.vars κ := fun q hq hk => by
    obtain ⟨z, hzS, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
    exact (e.of_ctxNe hs hk).2.2.1 z hzS hzn
  rw [laidMergesAx_eq] at hMG
  obtain ⟨trE, σEr, σEo, σC2, σR2, σM2, hET⟩ := e.elseTail ht hs hns hnsE hlm hlnd hE hCPE hRSE
      hMG hshE hoff.fresh (.inr ⟨rfl, hoff.reach⟩) hoff.bools (fun y hy => hkR y (hκb y hy))
      (fun q hq => ⟨hq1 q hq, hq1κ q hq⟩) hCEb (fun n hn => hkR n hn ▸ hn)
      (fun x hx hv n hn => (hoff.defd x hx (contFV_else_sub hv) n (hs.cur5 hx hn).1).elim
        fun w ⟨hw, hty⟩ => ⟨by simp [hw], w, (hkR n (by simp [hw])).trans hw, hty⟩)
      (fun q hq => (hsrcS q hq).elim fun w ⟨hw, hty⟩ => (htyC q hq).elim fun ty h0 =>
        ⟨w, w, ty, (hkR _ (hq1 q hq)).trans hw, ((hRcp q hq).trans (hk1 _ (hq1 q hq))).trans hw,
          hty ty h0, hty ty h0⟩)
      (fun x hx => (hR1 x fun q hq he => (hcpD q hq).disj (he ▸ (hlg x hx).1.of_le a7E hleE)
        (Nat.le_refl _)).trans (hpre1 x (List.mem_cons_of_mem _ (Option.mem_toList.2 hx))))
      hCS hgR h0R hlateR hcaseD hcaseM hMx hothS hSL hRbE hSdesc hkeep
  obtain ⟨hrunE, hrunC2, hrunR2, hrunM2, hfeasE, hCEr, hCM2, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE,
    hEo1, hSR, hlE, hkE, hR2, hRcp2, htyC2, hEq1, hEq2, hvalM2, hothM2, hgmM2, hqmM2, hrmM2, hκM,
    hrM2, hEM⟩ := hET
  have hMeq : ∀ n, σM2 n = σR2 n := fun n => by
    by_cases hn : n ∈ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
      rw [hvalM2 p hp]
      obtain ⟨q, hq, rfl⟩ := hlm p hp
      exact of_mergeVal_eq (by
        rw [hEq2 q hq, hEq1 q hq, hRcp q hq, hk1 _ (hq1 q hq), hkR _ (hq1 q hq)])
    · exact hothM2 n hn
  have hrM : (laidU κ κE rT Tr Er d).isNil = false → σM2 rT = some (HasBool.ffVal F) := fun hUn =>
    hrM2 (HasBool.ffVal F) ((hR1 rT fun q hq he => (hs.pre.drawn rT (.inr (.inl rfl))).disj
      (he ▸ hcpD q hq)
      (by omega)).trans (hrT1 (by simp [hUn])))
  obtain ⟨trU, σF, hrunU, hCF, hfrU, hbU, hUnil, hUnn, -⟩ := run_U' e.hF hU hCM2 (.inr ∘ hrM)
    (fun h => .inr (hEM h).1) (fun y hy => by rw [hκM y hy]; exact hoff.bools y hy)
    fun h => (hEM h).2
  obtain ⟨rfl, hfF⟩ : trU = [] ∧ κ.Fails F σF := by
    cases hUn : (laidU κ κE rT Tr Er d).isNil
    · obtain ⟨htr, -, hfail⟩ := (hUnn hUn).2 hκt
      exact ⟨htr, hfail fun h => h.elim (fun h => HasBool.ttVal_ne_ffVal F (Option.some.inj
        ((hrM hUn).symm.trans h)).symm) (·.not_fails (hEM hUn).1)⟩
    · obtain ⟨rfl, rfl⟩ := hUnil hUn
      exact ⟨rfl, of_failsCongr hoff.reach hκM⟩
  have hfinT : ∀ n ∈ wDecls Tr.out.toList, (σ1 n).isSome → σF n = σ1 n := fun n hn hb => by
    have hnκ : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).1 hn
    have hnκE : n ∉ RE.vars κE := fun hm => (e.of_κEvars' hm).elim (hTpre n hn g (.inl rfl))
      fun h => h.elim (fun h => hTpre n hn n (.inr (.inr h)) rfl) hnκ
    have hS : σS n = σR n := hSR n (fun h => hTpre n hn n (.inr (.inr h)) rfl) (hTlate n hn)
    have hR : σR n = σ1 n := hR1 n (hTcp n hn)
    rw [hfrU n hnκ, hMeq, hR2 n fun q hq he => hTlate n hn (he ▸ hcpED q hq),
      hfrmE n (by rw [hS, hR]; exact hb) hnκE, hS, hR]
  have hfinE : ∀ n ∈ wDecls Er.out.toList, σF n = σEr n := fun n hn => by
    rw [hfrU n fun h => (e.of_ctxNe hs h).2.1 hn, hMeq, hR2 n (hEcp n hn)]
  have hframe : Frame κ σL σF := fun y hy hny => by
    rw [hfrU y hny, hMeq, hR2 y fun q hq he => hLlate _ (he ▸ hy) (hcpED q hq), hkE y hy hny,
      hkR y hy]
  have hcar : CarryFF F T Y r st' σF ∧ CarryOK F T Y r st' σF := by
    have hcls := fun k => (Classical.choose_spec (e.rtxCls ht hs hns hcp6 k).1).2.1
    have hlate1 : ∀ n, (σ1 n).isSome → ∀ m, Drawn s7T s7E m → n ≠ m := fun n hb m hm he => by
      subst he
      simp [hlate n (hm.mono hnE) (fun h => hm.disj (hlq _ (mem_laidQm h)).1 (Nat.le_refl _))
        fun y hy he => hm.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)] at hb
    have hdT : ∀ n ∈ wDecls Tr.out.toList, σF n = σ1 n := fun n hn =>
      hfinT n hn (mainRun_binds _ _ hT hrunT n hn)
    have htT : ∀ k i n v xB, CarryReg Tr s6 k i n v xB → (σ1 n).isSome → σF n = σ1 n :=
      fun k i n v xB hr hb => by
        rcases hs.armT.carryTgt k i n v xB hr with ⟨z, hz, hzn⟩ | hn
        · rw [hs.cur6 z] at hzn
          have hnk : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).2.2.1 z hz hzn
          have hR : σR n = σ1 n := hR1 n (fun q hq he => by simp [he, hσ1cp q hq] at hb)
          have hS : σS n = σR n := by
            rcases hSdesc n with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, he, -⟩
            · exact h
            · simp [← hR, h0R n h] at hb
            · simp [hlate n (hrEmD n h).1 (hrEmD n h).2.1 (hrEmD n h).2.2] at hb
            · exact absurd he (hlate1 n hb _ (hnsE.drawn q hq).1)
          rw [hfrU n hnk, hMeq, hR2 n fun q hq => hlate1 n hb _ (hnsE.drawn q hq).2.1,
            hfrmE n (by rw [hS, hR]; exact hb) (e.of_notκE hs hnk (.inl ⟨z, hz, hzn⟩)), hS, hR]
        · exact hdT n hn
    have htE : ∀ k i n v xB, CarryReg Er s5 k i n v xB → σF n = σEr n := fun k i n v xB hr => by
      rcases hs.armE.carryTgt k i n v xB hr with ⟨z, hz, hzn⟩ | hn
      · rw [hfrU n fun h => (e.of_ctxNe hs h).2.2.1 z hz (hs.cur5 hz hzn).1, hMeq,
          hR2 n fun q hq he => ?_]
        obtain ⟨b, j, h1, h2, h3, -⟩ := hcpED q hq
        rw [← he] at h1 h2
        have h2' : st0.avoid.contains n = false := by rw [← hav.2.2.2.1, ← a7T]; exact h2
        rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
        · obtain ⟨-, b', j', h4, h5, -⟩ := hs.wf5.nm_fresh z n hm
          exact absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
        · simp [e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2'
      · exact hfinE n hn
    have ha7E : s7E.avoid = st0.avoid := by rw [a7E, a7T]; exact hav.2.2.2.1
    have hlateκ : ∀ y, Drawn s7T st' y → y ∉ RE.vars κ := fun y hd hk =>
      (e.of_ctxNe hs hk).2.2.2 s7T st' (by omega) hd
    have hgmF : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ffVal F) :=
      fun y hy => ⟨e.finBool ha7E hav.2.2.2.2 (hlg y hy).1 (hlg y hy).2, by
        rw [hfrU y (hlateκ y ((hlg y hy).1.of_le a7E hleE)), hgmM2 y hy]⟩
    have hqmF : ∀ q y, κ = .name q → qm? = some y →
        T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ffVal F) := fun q y hκq hy => by
      refine ⟨e.finBool ha7E hav.2.2.2.2 (hlq y hy).1 (hlq y hy).2.1, ?_⟩
      have hd := (hlq y hy).1.of_le a7E hleE
      have hyq : y ∈ laidQm κ qm? := by rw [hκq, hy]; simp [laidQm]
      have hR : σR y = σ1 y := hR1 y fun q' hq' he => (hcpD q' hq').disj (he ▸ hd) (Nat.le_refl _)
      rw [hfrU y (hlateκ y hd), hqmM2 y hy, hR, hext1 y hyq, hqmv q y hκq hy]
      exact (hκq ▸ hoff.reach : (RE.name q).Fails F σL)
    have hrmF : ∀ y, rEm? = some y →
        T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ffVal F) := fun y hy =>
      ⟨e.finBool ha7E hav.2.2.2.2 (hlr y hy).1 (hlr y hy).2.1, by
        rw [hfrU y (hlateκ y (hrEmD y hy).1), hrmM2 y hy]⟩
    have hselT : ∀ p ∈ laidCarry Tr s6 cpsT,
        SelIs F T Y σF (.ite (optVar gm?) (.var p.2) (.var p.1)) false := fun p _ =>
      selIs_gm e.hF hCF hgmF p.2 p.1
    have hselE : ∀ p ∈ laidCarry Er s6 cpsE,
        SelIs F T Y σF (.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1)) false := fun p _ =>
      selIs_eE e.hF hCF hκt (fun y hy => ⟨(hgmF y hy).1, .inr (hgmF y hy).2⟩) hqmF hrmF p.2 p.1
    refine ⟨fun k i n v xB hr => ?_, fun k i n v xB hr => ?_⟩
    · rcases hcls k i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, -, p, hp, ⟨⟩⟩ | ⟨p, hp, ⟨⟩⟩
      · exact hs.armT.sel e.hF hCF hC1 hdT h (hcfT _ _ _ _ _ h)
      · exact hs.armE.sel e.hF hCF hCEr hfinE h (hcfE _ _ _ _ _ h)
      · exact hselT p hp
      · exact hselE p hp
    · rcases hcls k i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, -, p, hp, ⟨⟩⟩ | ⟨p, hp, ⟨⟩⟩
      · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoT _ _ _ _ _ h
        refine ⟨hsel.imp (hs.armT.sel e.hF hCF hC1 hdT h) (hs.armT.sel e.hF hCF hC1 hdT h), hty,
          ⟨w, (htT _ _ _ _ _ h (by simp [hw])).trans hw, hwt⟩, ⟨w', ?_, hwt'⟩⟩
        rw [hdT xB (hs.armT.regs xB h.2), hw']
      · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoE _ _ _ _ _ h
        refine ⟨hsel.imp (hs.armE.sel e.hF hCF hCEr hfinE h) (hs.armE.sel e.hF hCF hCEr hfinE h),
          hty, ⟨w, (htE _ _ _ _ _ h).trans hw, hwt⟩, ⟨w', ?_, hwt'⟩⟩
        rw [hfinE xB (hs.armE.regs xB h.2), hw']
      · obtain ⟨-, q, hq, rfl⟩ := hcpT p hp
        obtain ⟨w, hw, hty⟩ := hsrcS q hq
        refine ⟨.inr (hselT _ hp), htyC q hq, ⟨w, (hframe q.1 (hq1 q hq) (hq1κ q hq)).trans hw,
          hty⟩, ⟨w, ?_, hty⟩⟩
        rw [hfrU _ fun hk => (e.of_ctxNe hs hk).2.2.2 s6 s7T (by omega) (hcpD q hq),
          hMeq, hEq2 q hq, hRcp q hq, hk1 _ (hq1 q hq), hw]
      · obtain ⟨q, hq, rfl⟩ := hcpE p hp
        obtain ⟨w, hw, hty⟩ := hbnd q.1 (hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq))
        refine ⟨.inr (hselE _ hp), htyC2 q hq, ⟨w, (hframe q.1 (hCEb q hq).1
          (hCEb q hq).2).trans hw, hty⟩, ⟨w, ?_, hty⟩⟩
        rw [hfrU _ (hlateκ _ (hcpED q hq)), hMeq, hRcp2 q hq, hkE q.1 (hCEb q hq).1 (hCEb q hq).2,
          hkR _ (hCEb q hq).1, hw]
  refine ⟨trT ++ (trE ++ []), σF, by wp_chain [hitems],
    Trace.AssumptionsHold.append hfeasT (Trace.AssumptionsHold.append hfeasE nofun), ?_, hframe,
    fun l x hx hp _ => ?_, hcar.1, hcar.2, ⟨fun hax => ?_, fun l x hx hp hl => ?_⟩⟩
  · rw [hscope]
    refine ⟨hCF, hfF, hbU, fun x hx hv n hn => ?_, fun n w hw hY ty hty => ?_, fun y hy => ?_⟩
    · have hc0 := (e.of_cur0 hs hx hn).2.2
      obtain ⟨w, hw, hty⟩ := hoff.defd x hx (mem_contFV_cons.2 (.inr hv)) n hc0
      exact ⟨w, (hframe n (by simp [hw]) fun h => (e.of_ctxNe hs h).2.2.1 x hx hc0).trans hw, hty⟩
    · by_cases hnκ : n ∈ RE.vars κ
      · exact rn_boolTyped (hoff.bools n hnκ) (fun w0 hw0 => hoff.gtyped n w0 hw0 hY ty hty)
          (hbU n hnκ) hw
      · rcases Classical.em (∃ q ∈ nsE, n = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · simp [e.fin.2.1 q.2.2 q.1 (hyoE ▸ (hnsE.drawn q hq).2.2.2)] at hY
        · rw [hfrU n hnκ, hMeq, hR2 n fun q hq' he => hq ⟨q, hq', he⟩] at hw
          exact hoffE.gtyped n w (by rw [hEo1 n (by simp [hw]), hw]) hY ty hty
    · by_cases hyκ : y ∈ RE.vars κ
      · exact hfr0 y (hκb y hyκ)
      · rcases Classical.em (∃ q ∈ nsE, y = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · obtain ⟨b, j, h1, h2, h3, -⟩ := hcpED q hq
          have h2' : st0.avoid.contains q.2.2 = false := by rw [← hav.2.2.2.1, ← a7T]; exact h2
          exact ⟨fun _ hfa => by simp [hfa b j h1] at h2', fun b' j' h1' _ =>
            .inl (by rw [freshName_counter_inj (h1'.symm.trans h1)]; omega)⟩
        · rw [hfrU y hyκ, hMeq, hR2 y fun q hq' he => hq ⟨q, hq', he⟩] at hy
          exact e.fresh0 hs hoffE.fresh y (by rw [hEo1 y hy]; exact hy)
  · rcases hregP l x hx hp with ⟨hx, hp⟩ | ⟨hx, hp⟩
    · have h := hsnT l x hx hp (by simp)
      rw [hfinT x (hs.armT.regs x hx) (by simp [h]), h]
    · rw [hfinE x (hs.armE.regs x hx)]
      exact hsnE l x hx hp (by simp)
  · rw [ht.ax] at hax
    exact (Bool.eq_false_or_eq_true Tr.ax).elim (fun hTa => (hseE.1 (by simpa [hTa] using hax)).elim
      fun _ h => ⟨_, h⟩) fun hTa => (hseT.1 hTa).elim fun _ h => ⟨_, h⟩
  · exact (hregP l x hx hp).elim (fun ⟨hx, hp⟩ => (hseT.2 l x hx hp hl).elim fun _ h => ⟨_, h⟩)
      fun ⟨hx, hp⟩ => (hseE.2 l x hx hp hl).elim fun _ h => ⟨_, h⟩

end

omit iLB iHI iLI iLFs e ht iLV in
include iIL in
/-- The selector of an else arm's carried merge is false on the then path: the merge guard is a
    true Boolean (drawn whenever the selector reads it), the copy `qm` a Boolean and the copy
    `rEm` a false Boolean, all with the Boolean final type. -/
private theorem selIs_eE_then (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    {κ' : RE P} {gm? qm? rEm? : Option P.Ident}
    (hgm : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ttVal F))
    (hneed : (κ' = .top ∨ ∃ q y, κ' = .name q ∧ qm? = some y) → gm?.isSome)
    (hqm : ∀ q y, κ' = .name q → qm? = some y → T[y]? = some HasBool.boolTy ∧
      (σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)))
    (hrm : ∀ y, rEm? = some y → T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ffVal F))
    (c x : P.Ident) :
    SelIs F T Y σ (.ite (elseGuard κ' gm? qm? rEm?) (.var c) (.var x)) false := by
  refine ⟨_, c, x, rfl, ?_⟩
  cases κ'
  case top =>
    obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 (hneed (.inl rfl))
    obtain ⟨h1, h2⟩ := hgm y rfl
    exact ⟨_, resolveE_ite.2 ⟨_, _, _, resolveE_var_ok h1, rfl, rfl, rfl⟩,
      ev_ite_true_b (ev_var hF.var hC h2) (hF.val.eval_ff σ) (.inr rfl) (.inl (hF.val.eval_tt σ))⟩
  case' name q => cases hq : qm?
  case some y =>
    obtain ⟨h1, h2⟩ := hqm q y rfl hq
    obtain ⟨g, rfl⟩ := Option.isSome_iff_exists.1 (hneed (.inr ⟨q, y, rfl, hq⟩))
    obtain ⟨h3, h4⟩ := hgm g rfl
    refine ⟨_, resolveE_ite.2 ⟨_, _, _, resolveE_var_ok h1,
      resolveE_ite.2 ⟨_, _, _, resolveE_var_ok h3, rfl, rfl, rfl⟩, rfl, rfl⟩, ?_⟩
    rcases h2 with h2 | h2
    · exact ev_ite_true_b (ev_var hF.var hC h2) (ev_ite_true_b (ev_var hF.var hC h4)
        (hF.val.eval_ff σ) (.inr rfl) (.inl (hF.val.eval_tt σ)))
        (.inr rfl) (.inr (hF.val.eval_ff σ))
    · exact ev_ite_false_b (ev_var hF.var hC h2) (hF.val.eval_ff σ) (.inr rfl)
        (.inr (ev_ite_true_b (ev_var hF.var hC h4) (hF.val.eval_ff σ) (.inr rfl)
          (.inl (hF.val.eval_tt σ))))
  all_goals cases hr : rEm? with
    | none => exact ⟨_, rfl, hF.val.eval_ff σ⟩
    | some y => exact ⟨_, resolveE_var_ok (hrm y hr).1, ev_var hF.var hC (hrm y hr).2⟩

omit e ht in
/-- A property of bounded indices holding somewhere holds at a largest index. -/
private theorem rtx_maxIdx {Q : Nat → Prop} {i0 : Nat} (h0 : Q i0) :
    ∀ {N : Nat}, (∀ i, Q i → i < N) → ∃ i, Q i ∧ ∀ j, Q j → j ≤ i
  | 0, hN => absurd (hN i0 h0) (Nat.not_lt_zero _)
  | N + 1, hN => (Classical.em (Q N)).elim
    (fun hQ => ⟨N, hQ, fun j hj => Nat.le_of_lt_succ (hN j hj)⟩) fun hQ => rtx_maxIdx h0
      fun i hi => Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hN i hi)) fun he => hQ (he ▸ hi) 
include iIL in
/-- On the then path of a laid-out `ite` one of whose arms always exits, with a nonempty body
    (the context holding, the condition true), a feasible loop-free run of the then arm (ending
    with `oT`, the else arm shadowed) is a feasible run of the output establishing `RunPost`,
    unless it exits under `top`. -/
private theorem LaidEnvAx.runThen
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm? st'
      rdc ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE (cps3.filter
        fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false))
    (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hsv : sv.toList = sv3.toList ++ svT.toList) (hcp : cp.toList = cp3.toList ++ cpT.toList)
    (hrs : rs.toList = rs3.toList ++ rsT.toList)
    (hcase : (Tr.ax = false ∧ M = interSet Tr.A Er.R ∧ cps = cps3 ∧ cpsT = []) ∨
      (Tr.ax = true ∧ M = laidCT Tr Er s6 s4.clock ∧ cps = cpsT ∧ cps3 = []))
    (hMv : ∀ x ∈ M, ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hCEv : ∀ x ∈ laidCE Er s6 s4.clock, ∃ z ∈ S,
      (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hnn : (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE (cps3.filter
        fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hc : P.eval F σ c = some (HasBool.ttVal F))
    (hsh : ShB F ess σ (VirtK oT fun o' => X (o'.proj σ)))
    (hT' : DRun F (fun o' => X (o'.proj σ)) tss σ evs oT)
    (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    (κ = .top ∧ ∃ l σ1, oT.proj σ = .exit l σ1) ∨
    ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL' (oT.proj σ) := by
  have hnx := hs.nexts
  have hav := hs.avoids
  obtain ⟨nsE, hnsE, hleE, a7E, a7T, hqmD, hext, hextT, -, hrEmD⟩ := e.saveE ht hs hns
  have hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    e.boundOn hs hon (hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq))
  have hnsC : ∀ n, (∃ q ∈ ns, n = q.1) ∨ ∀ q ∈ ns, n ≠ q.1 := fun n =>
    (Classical.em _).imp_right fun h q hq he => h ⟨q, hq, he⟩
  have ⟨ce, iRT, iGM, iQM, iSV, iT, iCP, iRS, iRE, iREM, iSVE, iE, iCPE, iRSE, iMG, iU, hsp⟩ :=
    e.split ht hnn hsv hcp hrs
  obtain ⟨hce, hRT, hGM, hQM, hSV, hT, hCP, hRS, hRE, hREM, hSVE, hE, hCPE, hRSE, hMG, hU,
    hitems⟩ := hsp
  obtain ⟨σB, hrun0, hCB, hB, hqmv⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM
    hQM hqmD (fun q x hq _ => .inl (hq ▸ hon.reach :)) hSV
    (e.guardOn hs hon hnn hs.aft.liveC hc (.inl rfl) hce) (.inl rfl) hsrcS
  have hrsv : ∀ q ∈ ns, rT ≠ q.2.1 := fun q hq he =>
    (hs.pre.drawn rT (.inr (.inl rfl))).disj (he ▸ (hns.drawn q hq).1) (by omega)
  have hrext : rT ∉ laidQm κ qm? := fun h =>
    (hs.pre.drawn rT (.inr (.inl rfl))).disj (hext rT h) (by omega)
  have hrTL : σL rT = none := e.preUnbound hs hns hon.fresh (.inl (by simp))
  obtain ⟨hrgm, -, hrg⟩ := hs.rTFacts hns
  have hrnot : rT ∉ g :: gm?.toList := by simpa [hrg] using fun h => hrgm _ h rfl
  obtain ⟨trT, σT', σ1, hrunT, hfT, hpost, h1T, h1rT, hch, hrTe⟩ : ∃ trT σT' σ1,
      MainRun F iT σB trT σ1 ∧ Trace.AssumptionsHold P evalInterp () trT ∧ RunPost F T Y Lc
      (fun y => Ex y ∨ y = g ∨ y = rT) Lab s5 s6 Tr (.name rT) S (scopeAfter S tss)
      (contFV (ess :: k)) (fun o' => X (o'.proj σ)) σT' oT ∧ (∀ n, n ≠ rT → σ1 n = σT' n) ∧
      (σ1 rT = none ∨ σ1 rT = σT' rT) ∧ (∀ n, σ1 n ≠ σB n → Wr0 (Block.idents tss) s5 s6 n ∨
      n = rT) ∧ ((Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = false → σ1 rT = σT' rT) := by
    by_cases hb : (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true
    · have hB' : PreStore F σL σB (g :: gm?.toList) (HasBool.ttVal F) ns (laidQm κ qm?) := by
        simpa [hb] using hB
      obtain rfl : iT = [] := resolve_isNil (Bool.and_eq_true_iff.1 hb).1 hT
      have hσBr : σB rT = none := (hB'.2.2.1 rT hrext hrnot hrsv).trans hrTL
      obtain ⟨trT, σT', hrun, hf, hpost⟩ := (e.armTp hs hT).2.1 σ _ _ evs oT (e.thenT hs hns hon
        (hB'.add (x := rT) hrsv hrext) hext hextT (wfStore_update_bool hCB rT (.inl rfl))) hT' hfeas
      cases hrun
      exact ⟨_, _, _, .nil, hf, hpost,
        fun n hn => ((update_facts σB rT (HasBool.ttVal F)).2 n (Ne.symm hn)).symm,
        .inl hσBr, fun n h => absurd rfl h, fun h => by simp [hb] at h⟩
    · obtain ⟨trT, σT', hrun, hf, hpost⟩ := (e.armTp hs hT).2.1 σ σB _ evs oT
        (e.thenT hs hns hon (by simpa [hb] using hB) hext hextT hCB) hT' hfeas
      refine ⟨_, _, _, hrun, hf, hpost, fun _ _ => rfl, .inr rfl, fun n hn => ?_, fun _ => rfl⟩
      exact (hs.armT.writesW T Y iT hT σB trT σT' hrun n hn).elim .inl
        fun h => .inr (Option.some.inj h).symm
  obtain ⟨hCT, hgtT, hfrT, hcoT⟩ : WellFormedStore σT' F ∧ (∀ n w, σT' n = some w →
      Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σT' ∧ CarryOK F T Y Tr s6 σT' := by
    cases oT <;> exact ⟨hpost.1.canonL, hpost.1.gtyped, hpost.1.fresh, hpost.2.2.2.1⟩
  obtain ⟨-, -, hTlate, hTpre, hTcp, hEcp, hlm, hlnd, hcpTn, hcpE, hcp6, hregP⟩ :=
    e.decls ht hs hns hMnd hnsE hcase
  obtain ⟨hlg, hlq, hlr, -, hyoE, hnE⟩ := ht.late
  have hsub : ∀ n w, σ1 n = some w → σT' n = some w := fun n w hw =>
    if hn : n = rT then by subst hn; exact h1rT.elim (by simp [·] at hw) (· ▸ hw) else h1T n hn ▸ hw
  have hC1 : WellFormedStore σ1 F := fun n w hw => hCT n w (hsub n w hw)
  have hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty := fun n w hw => hgtT n w (hsub n w hw)
  have hm1B := mainRun_mono hrunT
  have hq1 : ∀ q ∈ ns, (σL q.1).isSome := fun q hq =>
    Option.isSome_iff_exists.2 ((hsrcS q hq).imp fun _ h => h.1)
  have hBL : ∀ n, (σL n).isSome → σB n = σL n := fun n hn => by
    have hne : ∀ m, σL m = none → n ≠ m := fun m hm he => by simp [he, hm] at hn
    refine hB.2.2.1 n (fun h => hne _ (e.unbound hs hon.fresh (.inr ((hext n h).of_le a7T
      hnx.2.2.2.2.1))) rfl) (notin_pre (hne _ (e.preUnbound hs hns hon.fresh (.inl (by simp))))
      (hne _ hrTL) fun x hx => hne _ (e.preUnbound hs hns hon.fresh (.inl (by simp [hx]))))
      fun q hq => hne _ (e.preUnbound hs hns hon.fresh (.inr ⟨q, hq, rfl⟩))
  have hkeep : ∀ n, ¬ Wr0 (Block.idents tss) s5 s6 n → n ≠ rT → σ1 n = σB n := fun n hW hr =>
    Classical.byContradiction fun hne => (hch n hne).elim hW hr
  have hb1 : ∀ n, (σL n).isSome → (∃ z ∈ S, curName st' z = some n) → ∃ w, σ1 n = some w ∧
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun n hn ⟨z, hz, hzn⟩ => by
    obtain ⟨w1, hw1⟩ := Option.isSome_iff_exists.1 (hm1B n (by rwa [hBL n hn]))
    exact ⟨w1, hw1, hgt1 _ w1 hw1 (e.curY hs hz hzn)⟩
  have hsrc1 : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    hb1 q.1 (hq1 q hq) ((hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)).imp fun _ h => ⟨h.1, h.2.2⟩)
  have hcpD : ∀ q ∈ ns, Drawn s6 s7T q.2.2 := fun q hq => (hns.drawn q hq).2.1
  have hLcp : ∀ n, (σL n).isSome → ∀ q ∈ ns, n ≠ q.2.2 := fun n hn q hq he => by
    simp [he, e.unbound hs hon.fresh (.inr ((hcpD q hq).mono hnx.2.2.2.2.2))] at hn
  have hfr1 : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1 := fun y hy =>
    (Option.isSome_iff_exists.1 hy).elim fun w hw => hfrT y (by rw [hsub y w hw]; rfl)
  have hpre1 : ∀ n ∈ g :: gm?.toList, σ1 n = some (HasBool.ttVal F) := fun n hn => by
    refine (hkeep n ?_ fun he => hrnot (he ▸ hn)).trans
      (hB.1 n (List.mem_cons.2 ((List.mem_cons.1 hn).imp_right (List.mem_append_right _))))
    rcases List.mem_cons.1 hn with rfl | hn
    · exact e.notWT hs (.inl (.inl rfl))
    · exact e.notWT hs (.inr (((hlg n (Option.mem_toList.1 hn)).1.of_le a7E hleE).of_le a7T
        hnx.2.2.2.2.1))
  have hCEb : ∀ q ∈ nsE, (σL q.1).isSome ∧ q.1 ∉ RE.vars κ := fun q hq => by
    obtain ⟨z, hz, hfv, hzn⟩ := hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq)
    obtain ⟨w, hw, -⟩ := e.boundOn hs hon ⟨z, hz, hfv, hzn⟩
    exact ⟨by simp [hw], fun hk => (e.of_ctxNe hs hk).2.2.1 z hz hzn⟩
  obtain ⟨σR, σD, σM, σS, hmid⟩ :=
    e.midG ht hs hns hMnd hnsE hon.fresh hsrcS (fun q hq => ⟨(hCEb q hq).1, hb1 q.1 (hCEb q hq).1
    ((hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq)).imp fun _ h =>
    ⟨h.1, h.2.2⟩)⟩) hB hext hC1 hfr1 hgt1 (fun y hy => (hkeep y (e.notWTκ hs hy) fun he =>
    (e.of_ctxNe hs hy).2.2.2 s1 s4 hnx.1 (he ▸ hs.pre.drawn rT (.inr (.inl rfl)))).trans
    (hBL y (hon.reach.bound y hy))) hsrc1 hpre1 (fun q hq => by
        obtain ⟨hng, hnr, -, -⟩ := hs.saveNe (hns.drawn q hq).1
        rw [hkeep _ (e.notWT hs (.inr ((hns.drawn q hq).1.mono hnx.2.2.2.2.2))) hnr]
        exact hB.2.1 q hq)
      (fun n hb hr hW => (hkeep n hW hr).trans hb) hCP
      hRS hREM hSVE (.inr rfl) fun σR hCR hκR hgR h0R =>
        rEiRun e.hF hCR h0R (.inr (.inr ⟨hon.reach.congr hκR, hgR, rfl⟩)) hRE
  obtain ⟨hrunCS, hCS, htyC, hσ1cp, hlate, hR1, hRv, hRcp, hσRκ, hgR, h0R, hlateR, hcaseD, hcaseM,
    hMx, hothS, hSL, hRb, hSdesc, hkeepE, -⟩ := hmid
  have hLlate : ∀ n, (σL n).isSome → ¬ Drawn s7T st' n := fun n hn hd => by
    simp [e.unbound hs hon.fresh (.inr (hd.of_le a7T hnx.2.2.2.2.1))] at hn
  have hcpED : ∀ q ∈ nsE, Drawn s7T st' q.2.2 := fun q hq => (hnsE.drawn q hq).2.1.mono hnE
  have hq1κ : ∀ q ∈ ns, q.1 ∉ RE.vars κ := fun q hq hk => by
    obtain ⟨z, hzS, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
    exact (e.of_ctxNe hs hk).2.2.1 z hzS hzn
  have hlmq : ∀ n ∈ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1), ∃ q ∈ ns,
      n = q.1 := fun n hn => (List.mem_map.1 hn).elim fun p ⟨hp, he⟩ =>
    (hlm p hp).elim fun q ⟨hq, hpq⟩ => ⟨q, hq, by rw [← he, hpq]⟩
  have hnml : ∀ n, (∀ q ∈ ns, n ≠ q.1) → n ∉ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map
      (·.1) := fun n hn hin => (hlmq n hin).elim fun q ⟨hq, he⟩ => hn q hq he
  have hMG' : resolveItems T Y (laidMerges gm? ({} : Std.HashSet P.Ident)
      (cps3.filter fun p => liveBefore s6 p.1 s4.clock)).toList = .ok iMG := by
    have h := hMG
    cases hTa : Tr.ax
    · rwa [laidMergesAx_eq, e.ax.resolve_left (by simp [hTa]), ite_eq_left rfl] at h
    · exact hcase.elim (fun ⟨h', _⟩ => by simp [hTa] at h') fun ⟨_, _, _, h3⟩ => by rwa [h3] at h ⊢
  obtain ⟨trE, σEr, σEo, σC2, σR2, σM2, hET⟩ := e.elseTail ht hs hns hnsE hlm hlnd hE hCPE hRSE
      hMG' (shL_of_shB hsh) hon.fresh (.inl ⟨rfl, hon.reach⟩) hon.reach.bools hσRκ
      (fun q hq => ⟨hq1 q hq, hq1κ q hq⟩) hCEb (fun n hn => by
        rcases hnsC n with ⟨q, hq, rfl⟩ | hM
        · exact (hRv q hq) ▸ hn
        · rw [hR1 n fun q hq => ⟨hM q hq, hLcp n hn q hq⟩]
          exact hm1B n (by rwa [hBL n hn]))
      (fun x hx hv n hn => by
        have hn' := (hs.cur5 hx hn).1
        have hnL := (hon.defd x hx (contFV_else_sub hv)).2 n hn'
        refine ⟨hnL, ?_⟩
        rcases hnsC n with ⟨q, hq, rfl⟩ | hM
        · exact (hsrcS q hq).imp fun w h => ⟨(hRv q hq).trans h.1, h.2⟩
        · obtain ⟨w, hw, hty⟩ := hb1 n hnL ⟨x, hx, hn'⟩
          refine ⟨w, ?_, hty⟩
          rw [hR1 n fun q hq => ⟨hM q hq, hLcp n hnL q hq⟩, hw])
      (fun q hq => by
        obtain ⟨w, hw, hty⟩ := hsrcS q hq
        obtain ⟨w1, hw1, hty1⟩ := hsrc1 q hq
        obtain ⟨ty, hty0⟩ := htyC q hq
        exact ⟨w, w1, ty, (hRv q hq).trans hw, (hRcp q hq).trans hw1, hty ty hty0, hty1 ty hty0⟩)
      (fun x hx => by
        have hd := (hlg x hx).1.of_le a7E hleE
        refine (hR1 x fun q hq => ⟨fun he => hLlate _ (he ▸ hq1 q hq) hd, fun he =>
          (hcpD q hq).disj (he ▸ hd) (Nat.le_refl _)⟩).trans ?_
        exact hpre1 x (List.mem_cons_of_mem _ (Option.mem_toList.2 hx)))
      hCS hgR h0R hlateR hcaseD hcaseM hMx hothS hSL hRb hSdesc hkeepE
  obtain ⟨hrunE, hrunC2, hrunR2, hrunM2, hfeasE, hCEr, hCM2, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE,
    hEo1, hSR, hlE, hkE, hR2, hRcp2, htyC2, hEq1, hEq2, hvalM2, hMeq, hgmM2, hqmM2, hrmM2, hκM,
    hrM2, hEM⟩ := hET
  have hUM : ∀ b, σ1 rT = some b → σM2 rT = some b := fun b hr1 => hrM2 b ((hR1 rT fun q hq =>
    ⟨fun he => absurd (hq1 q hq) (by simp [← he, hrTL]),
      fun he => (hs.saveNe (hcpD q hq)).2.1 he.symm⟩).trans hr1)
  obtain ⟨-, -, h1eq0, hkeep0⟩ := wRen_run e.run1
  have h4eq : s4 = { s1 with next := s4.next, tys := s4.tys } := hs.pre.eq
  have hcurRT : ∀ z ∈ S, curName st' z ≠ some rT := fun z hz h => by
    rcases curName_cases h with h1 | ⟨-, -, rfl⟩
    · exact (hs.preNm (.inr (.inl rfl)) z).2.2.2 h1
    · obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn _ (.inr (.inl rfl))
      simp [hav.1, e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2
  have hst0cur : ∀ z ∈ S, ∀ n, curName st0 z = some n → curName s4 z = some n ∧
      curName s5 z = some n ∧ curName st' z = some n := fun z hz n hn =>
    (hs.curS hz (hkeep0 z n hn)).elim fun a ⟨b, _, d⟩ => ⟨a, b, d⟩
  have hlive : ∀ x ∈ S, ∀ n, curName st0 x = some n → st0.live.contains n = true →
      liveBefore s6 n s4.clock = true ∧ s5.live.contains n = true := by
    intro x hx n hn hl
    obtain ⟨s, hs0⟩ := Option.isSome_iff_exists.1 (Std.HashMap.mem_iff_isSome_getElem?.1 hl)
    obtain ⟨h4, h5, -⟩ := hst0cur x hx n hn
    have hs5 := hs.armE.liveKeep x hx n h4 s (by rwa [h4eq, h1eq0])
    exact ⟨by simp [liveBefore, hs.armT.liveKeep x hx n h5 s hs5, e.wf0.live_stamp n s hs0,
      (by rw [h4eq, h1eq0] : s4.clock = st0.clock)],
      by simp [Std.HashMap.contains_eq_isSome_getElem?, hs5]⟩
  have hrTv : σT' rT = some (HasBool.ttVal F) ∨ σT' rT = some (HasBool.ffVal F) := by
    cases oT <;> first | exact .inl hpost.1.reach | exact .inr hpost.1.reach
  obtain ⟨trU, σF, hrunU, hCF, hfrU, hbU, hUnil, hUnn, hkU⟩ := run_U' e.hF hU hCM2 (fun hUf =>
    hrTv.imp (fun h => hUM _ ((hrTe (by simp [hUf])).trans h)) fun h => hUM _
    ((hrTe (by simp [hUf])).trans h)) (fun h => .inr (hEM h).1)
    (fun y hy => hκM y hy ▸ hon.reach.bools y hy) fun h => (hEM h).2
  have hrunAll : MainRun F items σL (trT ++ (trE ++ trU)) σF := by wp_chain [hitems]
  have hTd : ∀ y ∈ wDecls Tr.out.toList, σF y = σT' y := fun y hy => by
    have hyM : ∀ q ∈ ns, y ≠ q.1 := fun q hq he => by
      obtain ⟨z, hz, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
      exact hs.armT.declNotCur y hy z hz ((hs.cur6 z).trans (he ▸ hzn))
    rw [hfrU y fun hk => (e.of_ctxNe hs hk).1 hy, hMeq y (hnml y hyM),
      hR2 y fun q hq he => hTlate y hy (he ▸ hcpED q hq), e.crossKeep hs hE hrunE y hy,
      hSR y (fun h => hTpre y hy y (.inr (.inr h)) rfl) (hTlate y hy),
      hR1 y fun q hq => ⟨hyM q hq, hTcp y hy q hq⟩, h1T y (hTpre y hy rT (.inr (.inl rfl)))]
  have hEdM : ∀ x ∈ wDecls Er.out.toList, ∀ q ∈ ns, x ≠ q.1 := fun x hD q hq he => by
    obtain ⟨z, hzS, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
    exact e.re_EdeclNotM hs hD hzS (he ▸ hzn)
  have hfinE : ∀ x ∈ wDecls Er.out.toList, σF x = σEr x := fun x hx => by
    rw [hfrU x fun h => (e.of_ctxNe hs h).2.1 hx, hMeq x (hnml x (hEdM x hx)), hR2 x (hEcp x hx)]
  have hFq : ∀ q ∈ ns, Tr.ax = false → liveBefore s6 q.1 s4.clock = true → σF q.1 = σ1 q.1 :=
    fun q hq hTa hl => by
      rw [hfrU _ (hq1κ q hq), hvalM2 (q.1, q.2.2) (List.mem_filter.2 ⟨?_, hl⟩)]
      · simpa only [mergeVal, Std.HashSet.contains_empty, Bool.false_eq_true, ite_false] using
          (hEq2 q hq).trans (hRcp q hq)
      refine hcase.elim (fun ⟨_, _, hc, _⟩ => ?_) fun ⟨h, _⟩ => by simp [hTa] at h
      rw [← hc, hns.pairs, List.mem_reverse]
      exact List.mem_map_of_mem hq
  have hFq' : ∀ q ∈ ns, (Tr.ax = true ∨ liveBefore s6 q.1 s4.clock = false) →
      σF q.1 = σL q.1 := fun q hq hl => by
    have hml : q.1 ∉ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1) := fun hin => by
        obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hin
        rcases hl with hl | hl
        · exact hcase.elim (fun ⟨h, _⟩ => by simp [hl] at h) fun ⟨_, _, _, h3⟩ => by simp [h3] at hp
        · simp [List.mem_filter, hpe, hl] at hp
    rw [hfrU _ (hq1κ q hq), hMeq _ hml, hEq1 q hq, hRv q hq]
  have hbool : ∀ {s : WSt P} {y : P.Ident}, s.avoid = st0.avoid → Drawn s st' y →
      st'.tys[y]? = some HasBool.boolTy → T[y]? = some HasBool.boolTy := fun ha hd ht' =>
    e.finBool ha hav.2.2.2.2 hd ht'
  have ha7E : s7E.avoid = st0.avoid := by rw [a7E, a7T]; exact hav.2.2.2.1
  have hlateκ : ∀ y, Drawn s7T st' y → y ∉ RE.vars κ := fun y hd hk =>
    (e.of_ctxNe hs hk).2.2.2 s7T st' (by omega) hd
  have hlateNs : ∀ y, Drawn s7T st' y → ∀ q ∈ ns, y ≠ q.1 := fun y hd q hq he =>
    hLlate _ (he ▸ hq1 q hq) hd
  have hgmF : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ttVal F) :=
    fun y hy => ⟨hbool ha7E (hlg y hy).1 (hlg y hy).2, by
      have hd := (hlg y hy).1.of_le a7E hleE
      rw [hfrU y (hlateκ y hd), hgmM2 y hy]⟩
  have hselE : ∀ p ∈ laidCarry Er s6 cpsE,
      SelIs F T Y σF (.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1)) false := by
    refine fun p hp => selIs_eE_then e.hF hCF hgmF (fun hk => ?_) (fun q y hκq hy => ?_)
      (fun y hy => ⟨hbool ha7E (hlr y hy).1 (hlr y hy).2.1, by
        rw [hfrU y (hlateκ y (hrEmD y hy).1), hrmM2 y hy]⟩) p.2 p.1
    · have hne : (laidCarry Er s6 cpsE).isEmpty = false := by simpa using List.ne_nil_of_mem hp
      rcases ht.gm with ⟨-, x, hx, -⟩ | ⟨hng, -, -⟩
      · simp [hx]
      · rcases hk with hk | ⟨q, y, hk, -⟩ <;> subst hk <;> simp [laidNeedGm, hne] at hng
    refine ⟨hbool ha7E (hlq y hy).1 (hlq y hy).2.1, .inl ?_⟩
    have hd := (hlq y hy).1.of_le a7E hleE
    have hR : σR y = σ1 y := hR1 y fun q' hq' =>
      ⟨hlateNs y hd q' hq', fun he => (hcpD q' hq').disj (he ▸ hd) (Nat.le_refl _)⟩
    have hyr : y ≠ rT := fun he => (hs.pre.drawn rT (.inr (.inl rfl))).disj (he ▸ hd) (by omega)
    have h1B : σ1 y = σB y := hkeep y (e.notWT hs (.inr (hd.of_le a7T hnx.2.2.2.2.1))) hyr
    rw [hfrU y (hlateκ y hd), hqmM2 y hy, hR, h1B, hqmv q y hκq hy]
    exact (hκq ▸ hon.reach : (RE.name q).Holds F σL)
  have hsavedTy : ∀ q ∈ ns, ∃ w, σF q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq => by
    cases hTa : Tr.ax <;> cases hl : liveBefore s6 q.1 s4.clock
    · exact hFq' q hq (.inr hl) ▸ hsrcS q hq
    · exact hFq q hq hTa hl ▸ hsrc1 q hq
    all_goals exact hFq' q hq (.inl hTa) ▸ hsrcS q hq
  have hlate1 : ∀ n, (σ1 n).isSome → ∀ m, Drawn s7T s7E m → n ≠ m := fun n hb m hm he => by
    subst he
    simp [hlate n (hm.mono hnE) (fun h => hm.disj (hlq _ (mem_laidQm h)).1 (Nat.le_refl _))
      fun y hy he => hm.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)] at hb
  have hcurF : ∀ z ∈ S, ∀ n, curName st' z = some n → (σT' n).isSome → (∀ q ∈ ns, n ≠ q.1) →
      σF n = σT' n := fun z hz n hzn hb' hM => by
    have hnr : n ≠ rT := fun he => hcurRT z hz (he ▸ hzn)
    have hnk : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).2.2.1 z hz hzn
    have hb : (σ1 n).isSome := by rwa [h1T n hnr]
    have hR : σR n = σ1 n := hR1 n fun q hq => ⟨hM q hq, fun he => by simp [he, hσ1cp q hq] at hb⟩
    have hS : σS n = σR n := by
      rcases hSdesc n with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨q, hq, he, -⟩
      · exact h
      · simp [← hR, h0R n h] at hb
      · simp [hlate n (hrEmD n h).1 (hrEmD n h).2.1 (hrEmD n h).2.2] at hb
      · exact absurd he (hlate1 n hb _ (hnsE.drawn q hq).1)
    rw [hfrU n hnk, hMeq n (hnml n hM), hR2 n fun q hq => hlate1 n hb _ (hnsE.drawn q hq).2.1,
      hfrmE n (by rwa [hS, hR]) (e.of_notκE hs hnk (.inl ⟨z, hz, hzn⟩)), hS, hR, h1T n hnr]
  have hfr0 : FreshInv Lc Ex st0 σL := of_freshPost hon.fresh (fun y hy => e.whole.taken y hy)
    e.whole.avoid e.whole.next (fun x y h => e.whole.nm x y h) fun y hy => .inl hy
  have hgtF : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
    by_cases hk : n ∈ RE.vars κ
    · exact rn_boolTyped (hon.reach.bools n hk) (fun w0 hw0 => hon.gtyped n w0 hw0 hY ty hty)
        (hbU n hk) hw
    · rw [hfrU n hk] at hw
      by_cases hml : n ∈ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hml
        obtain ⟨q, hq, rfl⟩ := hlm p hp
        simp only [hvalM2 _ hp, mergeVal, Std.HashSet.contains_empty, Bool.false_eq_true,
          ite_false, hEq2 q hq, hRcp q hq] at hw
        exact hgt1 _ w hw hY ty hty
      · rw [hMeq n hml] at hw
        rcases Classical.em (∃ q ∈ nsE, n = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · simp [e.fin.2.1 q.2.2 q.1 (hyoE ▸ (hnsE.drawn q hq).2.2.2)] at hY
        · rw [hR2 n fun q hq' he => hq ⟨q, hq', he⟩] at hw
          exact hoffE.gtyped n w (by rw [hEo1 n (by simp [hw]), hw]) hY ty hty
  have hfrF : FreshInv Lc Ex st0 σF := fun y hy => by
    by_cases hyκ : y ∈ RE.vars κ
    · exact hfr0 y (hon.reach.bound y hyκ)
    · rw [hfrU y hyκ] at hy
      by_cases hml : y ∈ (cps3.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1)
      · exact (hlmq y hml).elim fun q ⟨hq, he⟩ => hfr0 y (he ▸ hq1 q hq)
      · rw [hMeq y hml] at hy
        rcases Classical.em (∃ q ∈ nsE, y = q.2.2) with ⟨q, hq, rfl⟩ | hq
        · obtain ⟨b, j, h1, h2, h3, -⟩ := hcpED q hq
          have h2' : st0.avoid.contains q.2.2 = false := (a7T.trans hav.2.2.2.1) ▸ h2
          exact ⟨fun _ hfa => by simp [hfa b j h1] at h2', fun b' j' h1' _ =>
            .inl (by rw [freshName_counter_inj (h1'.symm.trans h1)]; omega)⟩
        · rw [hR2 y fun q hq' he => hq ⟨q, hq', he⟩] at hy
          exact e.fresh0 hs hoffE.fresh y (by rwa [hEo1 y hy])
  have hselE' : ∀ p ∈ laidCarry Er s6 cpsE, SelIs F T Y σF (.ite (elseGuard κ gm? qm? rEm?)
      (.var p.2) (.var p.1)) false ∧ (∃ ty, tyOfName T Y p.1 = .ok ty) ∧ (∃ w, σF p.1 = some w ∧
      ∀ ty, tyOfName T Y p.1 = .ok ty → HasVal.valueOfTy F w ty) ∧ ∃ w, σF p.2 = some w ∧ ∀ ty,
      tyOfName T Y p.1 = .ok ty → HasVal.valueOfTy F w ty := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := hcpE p hp
    obtain ⟨hqL, hqk⟩ := hCEb q hq
    obtain ⟨w, hw, hty⟩ := hRb q hq
    refine ⟨hselE _ hp, htyC2 q hq, ?_, ⟨w, ?_, hty⟩⟩
    · rcases hnsC q.1 with ⟨q', hq', he⟩ | hM
      · exact he ▸ hsavedTy q' hq'
      · refine ⟨w, ?_, hty⟩
        rw [hfrU _ hqk, hMeq _ (hnml _ hM),
          hR2 _ fun p hp he => hLlate _ (he ▸ hqL) (hcpED p hp), hkE q.1 hqL hqk, hw]
    · rw [hfrU _ (hlateκ _ (hcpED q hq)), hMeq _ (hnml _ (hlateNs _ (hcpED q hq))),
        hRcp2 q hq, hkE q.1 hqL hqk, hw]
  have hFcp : ∀ q ∈ ns, σF q.2.2 = σ1 q.1 := fun q hq => by
    rw [hfrU _ fun hk => (e.of_ctxNe hs hk).2.2.2 s6 s7T (by omega) (hcpD q hq),
      hMeq _ (hnml _ fun p hp he => hLcp p.1 (hq1 p hp) q hq he.symm), hEq2 q hq, hRcp q hq]
  have hE1 : ∀ z ∈ S, ∀ n, curName s5 z = some n → n ∉ RE.vars κ → (∀ q ∈ ns, n ≠ q.1) →
      σF n = σEr n := fun z hz n hzn hκ hM => by
    rw [hfrU n hκ, hMeq n (hnml n hM), hR2 n fun q hq he => ?_]
    obtain ⟨b, j, h1, h2, h3, -⟩ := he ▸ hcpED q hq
    have h2' : st0.avoid.contains n = false := (a7T.trans hav.2.2.2.1) ▸ h2
    rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
    · obtain ⟨-, b', j', h4, h5, -⟩ := hs.wf5.nm_fresh z n hm
      exact absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
    · simp [e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2'
  have hcl := fun k => Classical.choose_spec (e.rtxCls ht hs hns hcp6 k).1
  have hgmT : ∀ p ∈ laidCarry Tr s6 cpsT,
      SelIs F T Y σF (.ite (optVar gm?) (.var p.2) (.var p.1)) true := fun p hp => by
    obtain ⟨y, hy⟩ : ∃ y, gm? = some y := by
      rcases ht.gm with ⟨-, x, hx, -⟩ | ⟨hng, -, -⟩
      · exact ⟨x, hx⟩
      · have hne : (laidCarry Tr s6 cpsT).isEmpty = false := by simpa using List.ne_nil_of_mem hp
        simp [laidNeedGm, hne] at hng
    obtain ⟨h1, h2⟩ := hgmF y hy
    rw [hy]
    exact ⟨_, _, _, rfl, _, resolveE_var_ok h1, ev_var e.hF.var hCF h2⟩
  have hcoR : CarryOK F T Y r st' σF := fun k i n v xB hr => by
    rcases (hcl k).2.1 i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, -, p, hp, he⟩ | ⟨p, hp, he⟩
    · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoT _ _ _ _ _ h
      refine ⟨hsel.imp (hs.armT.sel e.hF hCF hCT hTd h) (hs.armT.sel e.hF hCF hCT hTd h), hty, ?_,
        ⟨w', hTd xB (hs.armT.regs xB h.2) ▸ hw', hwt'⟩⟩
      rcases hs.armT.carryTgt _ _ n v xB h with ⟨z, hz, hzn⟩ | hD
      · rw [hs.cur6 z] at hzn
        rcases hnsC n with ⟨q, hq, rfl⟩ | hM
        · exact hsavedTy q hq
        · exact ⟨w, (hcurF z hz n hzn (by rw [hw]; rfl) hM).trans hw, hwt⟩
      · exact ⟨w, hTd n hD ▸ hw, hwt⟩
    · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoE _ _ _ _ _ h
      refine ⟨hsel.imp (hs.armE.sel e.hF hCF hCEr hfinE h) (hs.armE.sel e.hF hCF hCEr hfinE h), hty,
        ?_, ⟨w', hfinE xB (hs.armE.regs xB h.2) ▸ hw', hwt'⟩⟩
      rcases hs.armE.carryTgt _ _ n v xB h with ⟨z, hz, hzn⟩ | hD
      · rcases hnsC n with ⟨q, hq, rfl⟩ | hM
        · exact hsavedTy q hq
        · have hκ : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).2.2.1 z hz (hs.cur5 hz hzn).1
          exact ⟨w, (hE1 z hz n hzn hκ hM).trans hw, hwt⟩
      · exact ⟨w, hfinE n hD ▸ hw, hwt⟩
    · cases he
      obtain ⟨-, q, hq, rfl⟩ := hcpTn p hp
      obtain ⟨w1, hw1, hty1⟩ := hsrc1 q hq
      exact ⟨.inl (hgmT _ hp), htyC q hq, hsavedTy q hq, ⟨w1, (hFcp q hq).trans hw1, hty1⟩⟩
    · cases he
      exact ⟨.inr (hselE' p hp).1, (hselE' p hp).2⟩
  have hsnR : ∀ ex, (∀ l e0, e0 ∈ Tr.regs.toList → e0 ∈ s6.pending.getD l [] → some e0 ≠ ex →
      σT' e0 = some (HasBool.ffVal F)) → SnapFF F r st' ex σF := fun ex hsnT l x hx hp hne => by
    rcases hregP l x hx hp with ⟨hx, hp⟩ | ⟨hx, hp⟩
    · exact (hTd x (hs.armT.regs x hx)).trans (hsnT l x hx hp hne)
    · exact (hfinE x (hs.armE.regs x hx)).trans (hsnE l x hx hp (by simp))
  have hexR : ∀ ex, ExitEnds Tr s6 ex (fun o' => X (o'.proj σ)) → ExitEnds r st' ex X := by
    intro ex hexT l x hx hp hl
    rcases hregP l x hx hp with ⟨hx, hp⟩ | ⟨hx, hp⟩
    · exact (hexT l x hx hp hl).elim fun σs1 h => ⟨_, h⟩
    · obtain ⟨σs1, h⟩ := hseE.2 l x hx hp (by simp)
      cases oT <;> exact ⟨_, h⟩
  have hEff : ∀ k i n v xB, CarryReg Er s5 k i n v xB → SelIs F T Y σF v false :=
    fun k i n v xB h => hs.armE.sel e.hF hCF hCEr hfinE h (hcfE _ _ _ _ _ h)
  have hS1 : ∀ x ∈ S, x ∈ scopeAfter S tss := fun x hx => scopeAfter_sub S tss hx
  cases oT with
  | normal σT =>
    refine .inr ?_
    obtain ⟨hOT, hsnT, hcfT, -, hTax, -, hexT⟩ := hpost
    obtain ⟨hfU, hHF⟩ : Trace.AssumptionsHold P evalInterp () trU ∧ κ.Holds F σF := by
      cases hUn : (laidU κ κE rT Tr Er d).isNil
      · have hrM := hUM (HasBool.ttVal F) ((hrTe (by simp [hUn])).trans hOT.reach)
        by_cases hκt : κ = .top
        · exact ⟨((hUnn hUn).1 hκt).2 (.inl hrM), by subst hκt; trivial⟩
        obtain ⟨rfl, hhold, -⟩ := (hUnn hUn).2 hκt
        refine ⟨nofun, hhold (.inl hrM) fun q g' hq => ?_⟩
        obtain ⟨h1, h2⟩ := (hq ▸ hon.reach : (RE.andNeg q g').Holds F σL)
        refine ⟨by rw [hκM q (by simp [hq, RE.vars])]; exact h1, fun he => ?_⟩
        exact HasBool.ttVal_ne_ffVal F (Option.some.inj ((he ▸ h1).symm.trans h2))
      · obtain ⟨rfl, rfl⟩ := hUnil hUn
        exact ⟨nofun, hon.reach.congr hκM⟩
    refine ⟨_, σF, hrunAll, Trace.AssumptionsHold.append hfT
      (Trace.AssumptionsHold.append hfeasE hfU), ?_, hsnR none hsnT,
      fun k i n v xB hr => ?_, hcoR, by rw [ht.ax, hTax]; rfl, ht.drop, hexR none hexT⟩
    · have hproj : ∀ x ∈ S, x ∈ contFV k → projectStore σ σT x = σT x := fun x hx hv => by
        simp [projectStore, (hon.defd x hx (mem_contFV_cons.2 (.inr hv))).1]
      have hV1 : ∀ x ∈ contFV k, x ∈ contFV (ess :: k) := fun x hx => mem_contFV_cons.2 (.inr hx)
      have hagr : ∀ x ∈ S, x ∈ contFV k → ∀ n, curName st0 x = some n →
          (st0.live.contains n = true ∨ ∀ q ∈ ns, n ≠ q.1) → σF n = σT' n := by
        intro x hx hv n hn hor
        obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
        have hnr : n ≠ rT := fun he => hcurRT x hx (he ▸ h')
        rcases hnsC n with ⟨q, hq, rfl⟩ | hM
        · exact hor.elim (fun hl => by rw [hFq q hq hTax (hlive x hx _ hn hl).1, h1T _ hnr])
            fun hno => absurd rfl (hno q hq)
        · exact hcurF x hx n h' ((hOT.defd x (hS1 x hx) (hV1 x hv)).2 n h5) hM
      refine { toOnCore := ?_, reach := hHF }
      exact
        { agree := fun x hx hv n hn hl => by
            obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
            rw [hagr x hx hv n hn (.inl hl), hproj x hx hv]
            exact hOT.agree x (hS1 x hx) (hV1 x hv) n h5 (hlive x hx n hn hl).2
          defd := fun x hx hv => ⟨hproj x hx hv ▸ (hOT.defd x (hS1 x hx) (hV1 x hv)).1,
            fun n hn => by
              rcases hnsC n with ⟨q, hq, rfl⟩ | hM
              · cases hl : liveBefore s6 q.1 s4.clock
                · exact hFq' q hq (.inr hl) ▸ hq1 q hq
                · exact (hsrc1 q hq).elim fun w1 ⟨hw1, _⟩ => by simp [hFq q hq hTax hl, hw1]
              · obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
                rw [hagr x hx hv n hn (.inr hM)]
                exact (hOT.defd x (hS1 x hx) (hV1 x hv)).2 n h5⟩
          alike := fun x hx hv n hn hnt w w' h1 h2 ty hty => by
            rcases hnsC n with ⟨q, hq, rfl⟩ | hM
            · exact (htyC q hq).elim fun ty0 h0 => absurd h0 (hnt ty0)
            · obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
              rw [hagr x hx hv n hn (.inr hM)] at h2
              exact hOT.alike x (hS1 x hx) (hV1 x hv) n h5 hnt w w' (hproj x hx hv ▸ h1) h2 ty hty
          undef := fun x hx hxS => by simp [projectStore, hon.undef x hx hxS]
          canon := WellFormedStore.proj hOT.canon
          canonL := hCF
          gtyped := hgtF
          ltyped := fun x hx hv n hn w hw ty hty => by
            obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
            exact hOT.ltyped x (hS1 x hx) (hV1 x hv) n h5 w (hproj x hx hv ▸ hw) ty hty
          fresh := hfrF }
    · exact ((hcl k).2.1 i n v xB hr).elim (fun ⟨_, h⟩ => hs.armT.sel e.hF hCF hCT hTd h
        (hcfT _ _ _ _ _ h)) fun ho1 => ho1.elim (fun ⟨i', h⟩ => hEff _ _ _ _ _ h) fun ho2 =>
        ho2.elim (fun ⟨_, _, p, hp, _⟩ => absurd (hcpTn p hp).1 (by simp [hTax])) fun ⟨p, hp, he⟩ =>
        (Prod.mk.inj (Prod.mk.inj he).2).1 ▸ hselE p hp
  | exit l0 σx =>
    by_cases hκt : κ = .top
    · exact .inl ⟨hκt, l0, _, rfl⟩
    refine .inr ?_
    have hUf : (laidU κ κE rT Tr Er d).isNil = false := rx_Unn (hs.armT.exitMin
      (fun l' t h' => (e.lab l' t ((e.labels hs l').2 ▸ h')).1) _ σ evs l0 σx hT')
    obtain ⟨hOT, hshT, -, -, hlabT⟩ := hpost
    rw [(e.labels hs l0).2] at hlabT
    have hrM := hUM (HasBool.ffVal F) ((hrTe (by simp [hUf])).trans hOT.reach)
    obtain ⟨rfl, -, hfail⟩ := (hUnn hUf).2 hκt
    have hHF : κ.Fails F σF := hfail fun h =>
      h.elim (fun h => (HasBool.ttVal_ne_ffVal F).symm (Option.some.inj (hrM.symm.trans h)))
        (·.not_fails (hEM hUf).1)
    have hqF : ∀ q g', κ = .andNeg q g' → σF q = some (HasBool.ttVal F) := fun q g' hq => by
      have h := (hq ▸ hon.reach : (RE.andNeg q g').Holds F σL)
      have hne : q ≠ g' :=
        fun he => HasBool.ttVal_ne_ffVal F (Option.some.inj (h.1.symm.trans (he ▸ h.2)))
      rw [hkU q g' hq q hne, hκM q (by simp [hq, RE.vars]), h.1]
    refine ⟨_, σF, hrunAll, Trace.AssumptionsHold.append hfT
      (Trace.AssumptionsHold.append hfeasE nofun), ?_⟩
    have hdF : ∀ x ∈ S, x ∈ contFV k → ∀ n, curName st0 x = some n → ∃ w, σF n = some w ∧
        ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := by
      intro x hx hv n hn
      obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
      rcases hnsC n with ⟨q, hq, rfl⟩ | hM
      · exact hsavedTy q hq
      · obtain ⟨w, hw, hwt⟩ := hOT.defd x hx (mem_contFV_cons.2 (.inr hv)) n h5
        exact ⟨w, by rw [hcurF x hx n h' (by rw [hw]; rfl) hM, hw], hwt⟩
    refine ⟨⟨hCF, hHF, hbU, hdF, hgtF, hfrF⟩, ⟨fun hra => ?_, hexR _ hshT.2⟩, hqF, hcoR, ?_⟩
    · rw [ht.ax] at hra
      cases hTa : Tr.ax
      · exact (hshT.1 hTa).elim fun _ h => ⟨_, h⟩
      · exact (hseE.1 (by simpa [hTa] using hra)).elim fun _ h => ⟨_, h⟩
    cases hlt : st0.labelDepth[l0]? with
    | none => exact hsnR none (hlt ▸ hlabT :)
    | some t =>
      obtain ⟨e0, he1, he2, he3, hsnT, hxc, hlow⟩ := (hlt ▸ hlabT :)
      obtain ⟨K, hK, htK, l', hl'⟩ := arm_exitTgt e.runT nofun (e.deadE hs)
        (fun l t h => (e.lab l t ((e.labels hs l).2 ▸ h)).1) hT' ((e.labels hs l0).2 ▸ hlt)
      have hLab := (e.lab l0 t hlt).2
      have hprojL : ∀ x ∈ Lab l0, projectStore σ σx x = σx x := fun x hx => by
        simp [projectStore, (hon.defd x (hLab x hx).2 (mem_contFV_cons.2 (.inr (hLab x hx).1))).1]
      refine ⟨e0, ht.regs ▸ List.mem_append_left _ (List.mem_append_left _ he1),
        hs.aft.pending ▸ he2, hTd e0 (hs.armT.regs e0 he1) ▸ he3,
        hsnR (some e0) hsnT, ?_, fun k i n v xB hk hr => ?_⟩
      · refine
          { xagree := fun x hx hv n hn hl hlf w hw => ?_
            defd := fun x hx hv => ⟨hprojL x hv ▸ (hxc.defd x (hS1 x hx) hv).1,
              fun n hn => Option.isSome_of_eq_some (hdF x hx (hLab x hv).1 n hn).choose_spec.1⟩
            alike := fun x hx hv n hn hnt w w' h1 h2 ty hty => ?_
            undef := fun x hx hxS => by simp [projectStore, hon.undef x hx hxS]
            canon := WellFormedStore.proj hxc.canon
            canonL := hCF
            gtyped := hgtF
            ltyped := fun x hx hv n hn w hw ty hty => by
              obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
              exact hxc.ltyped x (hS1 x hx) hv n h5 w (hprojL x hv ▸ hw) ty hty
            fresh := hfrF }
        · obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
          have hag := hxc.xagree x (hS1 x hx) hv n h5 (hlive x hx n hn hl).2
            (e.liveFrom hs hx hn hl hlf).2.1 w (hprojL x hv ▸ hw)
          have hnr : n ≠ rT := fun he => hcurRT x hx (he ▸ h')
          refine ⟨fun k i v xB h => (hcoR k i n v xB h).1, ?_⟩
          rcases hag.2 with ⟨hall, hnw⟩ | ⟨k1, i1, v1, xB1, htk, hrg, hsel, hxB, hmax⟩
          · by_cases hnew : Tr.ax = true ∧ ∃ q ∈ ns, n = q.1
            · obtain ⟨hTa, q, hq, rfl⟩ := hnew
              have hpc : (q.1, q.2.2) ∈ laidCarry Tr s6 cpsT := by
                have hl6 : s6.labelDepth[l']? = some K := (hs.wT.labelDepth l').trans hl'
                simp only [laidCarry, carryOf, hK]
                refine List.mem_filter.2 ⟨?_, (e.liveFrom hs hx hn hl hlf).2.2 l' K hl6 htK⟩
                refine hcase.elim (fun ⟨h, _⟩ => by simp [hTa] at h) fun ⟨_, _, h2, _⟩ => ?_
                rw [← h2, hns.pairs, List.mem_reverse]
                exact List.mem_map_of_mem hq
              obtain ⟨i0, -, hr0⟩ := (hcl K).2.2 hK _ hpc
              have hnotold : ∀ k' i' v' xB', t ≤ k' → CarryReg r st' k' i' q.1 v' xB' →
                  SelIs F T Y σF v' true → k' = K ∧ ∃ p ∈ laidCarry Tr s6 cpsT,
                    (q.1, v', xB') = (p.1, .ite (optVar gm?) (.var p.2) (.var p.1), p.2) := by
                intro k' i' v' xB' htk' hr' hs'
                rcases (hcl k').2.1 i' _ v' xB' hr' with ⟨-, h⟩ | ⟨i'', h⟩ | ⟨-, hk', p, hp, he⟩ |
                    ⟨p, hp, he⟩
                · exact (hs'.ne (hs.armT.sel e.hF hCF hCT hTd h (hall _ _ _ _ htk' h))).elim
                · exact (hs'.ne (hEff _ _ _ _ _ h)).elim
                · exact ⟨Option.some.inj (hk'.symm.trans hK), p, hp, he⟩
                · exact (hs'.ne ((Prod.mk.inj (Prod.mk.inj he).2).1 ▸ hselE p hp)).elim
              obtain ⟨i1, ⟨v1, xB1, hr1, hs1⟩, hmx⟩ := rtx_maxIdx
                (Q := fun i => ∃ v xB, CarryReg r st' K i q.1 v xB ∧ SelIs F T Y σF v true)
                ⟨_, _, hr0, hgmT _ hpc⟩ fun i ⟨_, _, hr, _⟩ => (List.getElem?_eq_some_iff.1 hr.1).1
              obtain ⟨-, p, hp, he⟩ := hnotold K i1 v1 xB1 htK hr1 hs1
              obtain ⟨hp1, -, rfl⟩ := (Prod.mk.inj he).imp_right Prod.mk.inj
              obtain ⟨-, q', hq', rfl⟩ := hcpTn p hp
              refine .inr ⟨K, i1, v1, q'.2.2, htK, hr1, hs1, ?_,
                fun k' i' v' xB' htk' hr' hs' => ?_⟩
              · rw [hFcp q' hq', ← (hp1 : q.1 = q'.1), h1T _ hnr, hnw]
              · obtain ⟨rfl, -⟩ := hnotold k' i' v' xB' htk' hr' hs'
                exact .inr ⟨rfl, hmx i' ⟨v', xB', hr', hs'⟩⟩
            · have hFn : σF n = some w := by
                rcases hnsC n with ⟨q, hq, rfl⟩ | hM
                · have hTa : Tr.ax = false := Bool.eq_false_iff.2 fun h => hnew ⟨h, q, hq, rfl⟩
                  rw [hFq q hq hTa (hlive x hx _ hn hl).1, h1T _ hnr, hnw]
                · rw [hcurF x hx n h' (by rw [hnw]; rfl) hM, hnw]
              refine .inl ⟨fun k' i' v' xB' htk' hr' => ?_, hFn⟩
              rcases (hcl k').2.1 i' n v' xB' hr' with ⟨-, h⟩ | ⟨i'', h⟩ | ⟨-, -, p, hp, he⟩ |
                  ⟨p, hp, he⟩
              · exact hs.armT.sel e.hF hCF hCT hTd h (hall _ _ _ _ htk' h)
              · exact hEff _ _ _ _ _ h
              · obtain ⟨hTa, q, hq, rfl⟩ := hcpTn p hp
                exact (hnew ⟨hTa, q, hq, (Prod.mk.inj he).1⟩).elim
              · exact (Prod.mk.inj (Prod.mk.inj he).2).1 ▸ hselE p hp
          · obtain ⟨K1, hK1, hk1⟩ := arm_carryDepth e.runT hs.wf5 (e.deadE hs)
              (fun l' t' h' => (e.lab l' t' ((e.labels hs l').2 ▸ h')).1) nofun hrg.1 hrg.2
            refine .inr ⟨k1, _, v1, xB1, htk, (hcl k1).1 _ _ _ _ hrg,
              hs.armT.sel e.hF hCF hCT hTd hrg hsel, hTd xB1 (hs.armT.regs xB1 hrg.2) ▸ hxB,
              fun k' i' v' xB' htk' hr' hs' => ?_⟩
            rcases (hcl k').2.1 i' n v' xB' hr' with ⟨hle, h⟩ | ⟨i'', h⟩ | ⟨hlt, hk', -⟩ |
                ⟨p, hp, he⟩
            · rcases (hcoT _ _ _ _ _ h).1 with ht' | hf
              · exact (hmax _ _ _ _ htk' h ht').imp_right fun ⟨he, _⟩ => ⟨he, by subst he; omega⟩
              · exact (hs'.ne (hs.armT.sel e.hF hCF hCT hTd h hf)).elim
            · exact (hs'.ne (hEff _ _ _ _ _ h)).elim
            · obtain rfl : K1 = k' := Option.some.inj (hK1.symm.trans hk')
              exact (Nat.lt_or_eq_of_le hk1).imp_right fun he => ⟨he, by subst he; omega⟩
            · exact (hs'.ne ((Prod.mk.inj (Prod.mk.inj he).2).1 ▸ hselE p hp)).elim
        · rcases hnsC n with ⟨q, hq, rfl⟩ | hM
          · exact (htyC q hq).elim fun ty0 h0 => absurd h0 (hnt ty0)
          · obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
            exact hxc.alike x (hS1 x hx) hv n h5 hnt w w' ((hprojL x hv).symm.trans h1)
              ((hcurF x hx n h' ((hxc.defd x (hS1 x hx) hv).2 n h5) hM).symm.trans h2) ty hty
      · rcases (hcl k).2.1 i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, hk', -⟩ | ⟨p, hp, he⟩
        · exact hs.armT.sel e.hF hCF hCT hTd h (hlow _ _ _ _ _ hk h)
        · exact hEff _ _ _ _ _ h
        · obtain rfl := Option.some.inj (hK.symm.trans hk')
          omega
        · exact (Prod.mk.inj (Prod.mk.inj he).2).1 ▸ hselE p hp

omit iLI iWL iOp iLF iLFs iLV e ht in
/-- The else-arm reach of a laid-out `ite` under a context that is neither `top` nor a name is
    drawn. -/
private theorem rex_rEsome {κ' κE' : RE P} {g' : P.Ident} {s3' s4' : WSt P}
    {rE' : Option P.Ident} (h : LaidCtx κ' g' s3' κE' rE' s4') (h1 : κ' ≠ .top)
    (h2 : ∀ q, κ' ≠ .name q) : ∃ x, rE' = some x := by
  cases κ' <;> grind [LaidCtx]

omit iLB iHI iLI iLFs e ht iLV in
include iIL in
/-- The selector of an else arm's carried merge is true on the else path under a variable
    context: the merge guard is false, and the copy `qm` of the enclosing context `name q`, or
    otherwise the copy `rEm` of the else-arm reach, is true, all with the Boolean final type. -/
private theorem rex_selE (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F)
    {κ' : RE P} (hκ : κ' ≠ .top) {gm? qm? rEm? : Option P.Ident}
    (hgm : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ffVal F))
    (hqm : ∀ q, κ' = .name q → ∃ y, qm? = some y ∧
      T[y]? = some HasBool.boolTy ∧ σ y = some (HasBool.ttVal F))
    (hrm : (∀ q, κ' ≠ .name q) → ∃ y, rEm? = some y ∧ T[y]? = some HasBool.boolTy ∧
      σ y = some (HasBool.ttVal F)) (c x : P.Ident) :
    SelIs F T Y σ (.ite (elseGuard κ' gm? qm? rEm?) (.var c) (.var x)) true := by
  refine ⟨_, _, _, rfl, ?_⟩
  rcases κ' with _ | q | g | ⟨q, g⟩
  · exact absurd rfl hκ
  · obtain ⟨y, rfl, hTq, hq⟩ := hqm q rfl
    rcases gm? with _ | m
    · simp only [elseGuard, optVar, WExpr.not, WExpr.and, resolveE, tyOfName, hTq, pure,
        Except.pure, bind, Except.bind]
      exact ⟨_, rfl, ev_ite_true_b (ev_var hF.var hC hq) (hF.val.eval_tt σ) (.inl rfl)
        (.inr (hF.val.eval_ff σ))⟩
    · obtain ⟨hTm, hm⟩ := hgm m rfl
      simp only [elseGuard, optVar, WExpr.not, WExpr.and, resolveE, tyOfName, hTq, hTm, pure,
        Except.pure, bind, Except.bind]
      exact ⟨_, rfl, ev_ite_true_b (ev_var hF.var hC hq) (ev_ite_false_b (ev_var hF.var hC hm)
        (hF.val.eval_tt σ) (.inl rfl) (.inr (hF.val.eval_ff σ))) (.inl rfl)
        (.inr (hF.val.eval_ff σ))⟩
  all_goals obtain ⟨y, rfl, hT, hv⟩ := hrm nofun
  all_goals exact ⟨_, resolveE_var_ok hT, ev_var hF.var hC hv⟩

include iIL in
/-- **Gap (always-exiting arms: runs through the else arm).** On the else path of a laid-out
    `ite` one of whose arms always exits, with a nonempty body, a feasible loop-free run of the
    else arm (the then arm shadowed) is a feasible run of the output establishing `RunPost`,
    unless it exits under `top`. -/
private theorem LaidEnvAx.runElse
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7T gm? st'
      rdc ((laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE (cps3.filter
        fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false))
    (hns : SaveNs s6 M sv cp rs cps s7T ns) (hMnd : M.Nodup)
    (hsv : sv.toList = sv3.toList ++ svT.toList) (hcp : cp.toList = cp3.toList ++ cpT.toList)
    (hrs : rs.toList = rs3.toList ++ rsT.toList)
    (hcase : (Tr.ax = false ∧ M = interSet Tr.A Er.R ∧ cps = cps3 ∧ cpsT = []) ∨
      (Tr.ax = true ∧ M = laidCT Tr Er s6 s4.clock ∧ cps = cpsT ∧ cps3 = []))
    (hMv : ∀ x ∈ M, ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hCEv : ∀ x ∈ laidCE Er s6 s4.clock, ∃ z ∈ S,
      (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
      curName st' z = some x)
    (hnn : (laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE (cps3.filter
        fun p => liveBefore s6 p.1 s4.clock) Tr Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hc : P.eval F σ c = some (HasBool.ffVal F))
    (hE' : DRun F (fun o' => X (o'.proj σ)) ess σ evs oE)
    (hsh : ShB F tss σ (VirtK oE fun o' => X (o'.proj σ)))
    (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    (κ = .top ∧ ∃ l σ1, oE.proj σ = .exit l σ1) ∨
    ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL' (oE.proj σ) := by
  by_cases htop : κ = .top ∧ ∃ l σ1, oE.proj σ = .exit l σ1
  · exact .inl htop
  refine .inr ?_
  obtain ⟨nsE, hnsE, hleE, a7E, a7T, hqmD, hext, hextT, hrEng, hrEmD⟩ := e.saveE ht hs hns
  have ⟨ce, iRT, iGM, iQM, iSV, iT, iCP, iRS, iRE, iREM, iSVE, iE, iCPE, iRSE, iMG, iU, hsp⟩ :=
    e.split ht hnn hsv hcp hrs
  obtain ⟨hce, hRT, hGM, hQM, hSV, hT, hCP, hRS, hRE, hREM, hSVE, hE, hCPE, hRSE, hMG, hU,
    hitems⟩ := hsp
  have hnx := hs.nexts
  have hav := hs.avoids
  have hkLE : ∀ {σa σb tr x}, WellFormedStore σa F → MainRun F iE σa tr σb →
      Er.A.contains x = false → x ∉ RE.vars κE → liveBefore s5 x s4.clock = true → σb x = σa x :=
    fun {σa σb tr x} hC hrun hA hκE hl => Classical.byContradiction fun hne => by
      have hD := ((arm_writesLive e.hF e.runE hs.ctxE hs.wf4
        (fun x hx => hav.2.1 ▸ e.avoidArm (.inr hx)) T Y iE hE σa tr σb hC hrun x
          hne).resolve_left (by simp [hA])).resolve_right (by simp [hκE, hl])
      obtain ⟨t, ht, htc⟩ : ∃ t, s5.live[x]? = some t ∧ t < s4.clock := by
        revert hl; cases h5 : s5.live[x]? <;> simp [liveBefore, h5]
      obtain ⟨h4, b, j, h1, h2, h3⟩ := arm_declNotLive e.runE hs.ctxE hs.wf4 e.wfS.2.2
        (fun x hx b j hxj => hav.2.1 ▸ e.avoidSArm (.inr rfl) hx b j hxj)
        (fun l t h => (e.lab l t ((e.labels hs l).1 ▸ h)).1) x hD t ht htc
      exact (hs.liveK4 x t h4).elim (fun h => by simp [h b j h1] at h2)
        fun ⟨b', j', h4', h5⟩ => absurd (freshName_counter_inj (h1.symm.trans h4')) (by omega)
  obtain ⟨hlg, hlq, hlr, -, hyoE, hnE⟩ := ht.late
  have h7T6 : ∀ n, Drawn s7T st' n → Drawn s6 st' n := fun n hn => hn.of_le a7T hnx.2.2.2.2.1
  have hfB := fun x => e.finBool (x := x) (a7E.trans (a7T.trans hav.2.2.2.1)) hav.2.2.2.2
  have hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq =>
    e.boundOn hs hon (hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq))
  have hq1 : ∀ q ∈ ns, (σL q.1).isSome := fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]
  obtain ⟨σB, hrun0, hCB, hB, hBq⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM hQM
    hqmD (fun q x hq _ => .inl (hq ▸ hon.reach :)) hSV
    (e.guardOn hs hon hnn hs.aft.liveC hc (.inr rfl) hce) (.inr rfl) hsrcS
  obtain ⟨trT, σ1, hrunT, hfeasT, hC1, hfr1, hgt1, hk1, hpre1, hsv1, hunb1, hsnT, hcfT, hcoT,
    hseT, hrT1, hext1⟩ := e.of_T hs hns (fun x hx hv n hn =>
      let ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hon.defd x hx hv).2 n hn)
      ⟨w, hw, hon.gtyped n w hw (e.curY hs hx hn)⟩) hon.gtyped hon.fresh
      hq1 hB hext hextT hCB hT (shL_of_shB hsh)
  have hcpD : ∀ q ∈ ns, Drawn s6 s7T q.2.2 := fun q hq => (hns.drawn q hq).2.1
  have hcpL : ∀ q ∈ ns, σL q.2.2 = none := fun q hq =>
    e.unbound hs hon.fresh (.inr ((hcpD q hq).mono hnx.2.2.2.2.2))
  have hLcp : ∀ n, (σL n).isSome → ∀ q ∈ ns, n ≠ q.2.2 := fun n hn q hq he => by
    simp [he, hcpL q hq] at hn
  have hLlate : ∀ n, (σL n).isSome → ¬ Drawn s7T st' n := fun n hn hd => by
    simp [e.unbound hs hon.fresh (.inr (h7T6 n hd))] at hn
  obtain ⟨σR, σD, σM, σS, hmid⟩ := e.midG ht hs hns hMnd hnsE hon.fresh
      hsrcS (fun q hq => (e.boundOn hs hon (hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq))).elim
        fun w ⟨hw, hty⟩ => ⟨by simp [hw], w, (hk1 _ (by simp [hw])).trans hw, hty⟩) hB hext hC1
      hfr1 hgt1 (fun y hy => hk1 y (hon.reach.bound y hy))
      (fun q hq => (hsrcS q hq).imp fun _ h => ⟨(hk1 _ (hq1 q hq)).trans h.1, h.2⟩) hpre1 hsv1
      hunb1 hCP hRS hREM hSVE (.inl rfl)
      fun σR hCR hκR hgR h0R => rEiRun e.hF hCR h0R (.inl ⟨hon.reach.congr hκR, hgR, rfl⟩) hRE
  obtain ⟨hrunCS, hCS, htyC, -, -, -, -, hRcp, -, hgR, h0R, hlateR, hcaseD, hcaseM, hMx, hothS, hSL,
    -, hSdesc, hkeep, hk1C, hEs⟩ := hmid
  obtain ⟨hkR, hR1⟩ := hk1C hk1
  have hsvED : ∀ q ∈ nsE, Drawn s7T st' q.2.1 := fun q hq => (hnsE.drawn q hq).1.mono hnE
  have hSLb : ∀ n, (σL n).isSome → σS n = σL n := fun n hn =>
    ((hkeep σS hSdesc).1 n hn).trans (hkR n hn)
  have hSR : ∀ y, rE? ≠ some y → rEm? ≠ some y → (∀ q ∈ nsE, y ≠ q.2.1) → σS y = σR y :=
    fun y h1 h2 h3 => (hSdesc y).elim id fun ho1 => ho1.elim (fun ⟨h, _⟩ => absurd h h1)
        fun ho2 => ho2.elim (fun ⟨h, _⟩ => absurd h h2) fun ⟨q, hq, he, _⟩ => absurd he (h3 q hq)
  obtain ⟨σEs, hCEs, hdescS, hreachE, hvirt⟩ := hEs rfl rfl hon.reach
  obtain ⟨trE, σE', hrunE, hfeasE, hpost⟩ := (e.armEp hs hE).2.1 σ σEs _ evs oE
    (hs.elseE hon hCEs (fun n hn => ((hkeep σEs hdescS).1 n hn).trans (hkR n hn))
      (hkeep σEs hdescS).2.1 (hkeep σEs hdescS).2.2 hreachE) hE' hfeas
  have hgL : σL g = none := e.unbound hs hon.fresh (.inl (.inl rfl))
  have hκE' : ∀ y ∈ RE.vars κE, y = g ∨ rE? = some y ∨ y ∈ RE.vars κ := fun _ => e.of_κEvars'
  have hlateκ : ∀ y, Drawn s7T st' y → y ∉ RE.vars κ := fun y hd hk =>
    (e.of_ctxNe hs hk).2.2.2 s7T st' (by omega) hd
  have hlateκE : ∀ n, Drawn s7T st' n → n ∉ RE.vars κE := fun n hn hm =>
    (hκE' n hm).elim (fun h => (hs.pre.drawn g (.inl rfl)).disj (h ▸ hn) (by omega))
      fun ho1 => ho1.elim (fun h => hrEng n h n hn rfl) fun h => hlateκ n hn h
  obtain ⟨-, -, hst1, hcur1⟩ := wRen_run e.run1
  have hlive4 : s4.live = st0.live := by rw [hs.pre.eq, hst1]
  have htk4 : s4.taken = st0.taken := by rw [hs.pre.eq, hst1]
  have hn4 : ∀ x n, curName st0 x = some n → curName s4 x = some n := fun x n hn => by
    rw [hs.pre.eq]; exact hcur1 x n hn
  obtain ⟨hTk, hEk, hTlate, hTpre, hTcp, -, -, -, hcpTm, hcpEm, hcp6, hregP⟩ :=
    e.decls ht hs hns hMnd hnsE hcase
  have hrE : rT ∉ RE.vars κE := fun hm => (hκE' rT hm).elim (fun h => hs.pre.g_rT h.symm)
      fun ho1 => ho1.elim (fun h => (hs.pre.rE_ne rT h).2 rfl)
      fun h => (e.of_ctxNe hs h).2.2.2 s1 s4 hnx.1 (hs.pre.drawn rT (.inr (.inl rfl)))
  have hcpS : ∀ q ∈ ns, q.2.2 ∉ RE.vars κE ∧ σS q.2.2 = σL q.1 := fun q hq => by
    have hcd := hcpD q hq
    refine ⟨fun hm => ?_, (hSR q.2.2 (fun h => (hs.saveNe hcd).2.2.2 _ h rfl)
      (fun h => hcd.disj (hrEmD _ h).1 (Nat.le_refl _)) fun p hp he => hcd.disj
        (he.symm ▸ (hnsE.drawn p hp).1 : Drawn s7T s7E q.2.2) (Nat.le_refl _)).trans
          ((hRcp q hq).trans (hk1 _ (hq1 q hq)))⟩
    exact (hκE' _ hm).elim (fun h => (hs.saveNe hcd).1 h) fun ho1 => ho1.elim (fun h =>
      (hs.saveNe hcd).2.2.2 _ h rfl) fun h => (e.of_ctxNe hs h).2.2.2 s6 s7T (by omega) hcd
  have hTS : ∀ y ∈ wDecls Tr.out.toList, σS y = σ1 y := fun y hy => by
    rw [hSR y (fun h => hTpre y hy y (.inr (.inr h)) rfl) (fun h => hTlate y hy (hrEmD y h).1)
      fun q hq he => hTlate y hy (he ▸ hsvED q hq), hR1 y (hTcp y hy)]
  have hgmS : ∀ y, gm? = some y → σS y = some (HasBool.ffVal F) := fun y hy => by
    have hd := (hlg y hy).1.of_le a7E hleE
    rw [hSR y (fun h => hrEng y h y hd rfl) (fun h => (hlr y h).2.2.1 y hy rfl)
      fun q hq he => (hnsE.drawn q hq).1.disj (he ▸ (hlg y hy).1) (Nat.le_refl _),
      hR1 y fun q hq he => (hcpD q hq).disj (he ▸ hd) (Nat.le_refl _)]
    exact hpre1 y (List.mem_cons_of_mem _ (Option.mem_toList.2 hy))
  have hrS : (laidU κ κE rT Tr Er d).isNil = false → σS rT = some (HasBool.ffVal F) := fun hUf => by
    have hrd := hs.pre.drawn rT (.inr (.inl rfl))
    rw [hSR rT (fun h => (hs.pre.rE_ne rT h).2 rfl) (fun h => hrd.disj (hrEmD rT h).1 (by omega))
      fun q hq he => hrd.disj (he ▸ hsvED q hq) (by omega),
      hR1 rT fun q hq he => (hs.saveNe (hcpD q hq)).2.1 he.symm]
    exact hrT1 (by simp [hUf])
  have hwrS : ∀ σ' : SemanticStore P, (∀ n, σ' n ≠ σS n → Wr0 (Block.idents ess) s4 s5 n ∨
      κE.wvar = some n) → (∀ q, κE = .andNeg q g → σ' q = σS q) →
      ((laidU κ κE rT Tr Er d).isNil = false → σ' rT = some (HasBool.ffVal F)) ∧
      ∀ y ∈ RE.vars κ, σ' y = σL y :=
      fun σ' hwr hq => by
      refine ⟨fun hUf => hrS hUf ▸ Classical.byContradiction fun hne => (hwr rT hne).elim
        (e.notWE hs (.inl (.inr (.inl rfl)))) fun h => hrE (wvar_mem h), fun y hy => ?_⟩
      have hyL := hon.reach.bound y hy
      rw [← hSLb y hyL]
      by_cases hyE : y ∈ RE.vars κE
      · rcases e.ctx.cases' with ⟨hr, h | ⟨q, hq', h⟩⟩ | ⟨x, hx, h⟩ <;> rw [h] at hyE <;>
          simp only [RE.vars, List.mem_cons, List.not_mem_nil, or_false] at hyE
        · simp [hyE, hgL] at hyL
        · exact hyE.elim (fun he => he ▸ hq q h) fun he => by simp [he, hgL] at hyL
        · simp [hyE, e.unbound hs hon.fresh (.inl (.inr (.inr hx)))] at hyL
      · exact Classical.byContradiction fun hne =>
          (hwr y hne).elim (e.notWEκ hs hy) fun h => hyE (wvar_mem h)
  have hκgt : ∀ σ' : SemanticStore P,
      (∀ y ∈ RE.vars κ, σ' y = some (HasBool.ttVal F) ∨ σ' y = some (HasBool.ffVal F)) →
      ∀ n ∈ RE.vars κ, ∀ w, σ' n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun σ' hbU n hnκ w hw hY ty hty => by
    obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.1 (hon.reach.bound n hnκ)
    exact LawfulHasVal.valueOfTy_congr F w0 w ty HasBool.boolTy (hon.gtyped n w0 hw0 hY ty hty)
      (bool_valueOfTy (by
        rcases hon.reach.bools n hnκ with h | h <;> rw [hw0] at h <;> cases h <;> simp))
      (bool_valueOfTy (by rcases hbU n hnκ with h | h <;> rw [hw] at h <;> cases h <;> simp))
  have hfr0 : ∀ σ' σ'' : SemanticStore P,
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 σ' →
      (∀ y, (σ'' y).isSome → (σ' y).isSome ∨ ∃ q ∈ nsE, y = q.2.2) → FreshInv Lc Ex st0 σ'' := by
    intro σ' σ'' hfr hb y hy
    rcases hb y hy with hyE | ⟨q, hq, rfl⟩
    · obtain ⟨l1, f1⟩ := hfr y hyE
      refine ⟨fun hl hf => ?_, fun b j hb ha => ?_⟩
      · exact htk4 ▸ l1 hl fun b j hb => hav.2.1 ▸ hf b j hb
      · rcases f1 b j hb (hav.2.1 ▸ ha) with h | ⟨x, hx⟩ | h | h | h | h
        · exact .inl (by omega)
        · exact (hs.c1.nm x y (hs.pre.eq ▸ hx :)).elim (fun h => .inr (.inl ⟨x, h⟩))
            fun ⟨b', j', hy', _, hj'⟩ => .inl (freshName_counter_inj (hb.symm.trans hy') ▸ hj')
        · exact .inr (.inr h)
        all_goals
          obtain ⟨b', j', hy', -, hj', -⟩ := hs.preDrawn (n := y) (by
            first | exact .inl h | exact .inr (.inl h) | exact .inr (.inr h))
          exact .inl (freshName_counter_inj (hb.symm.trans hy') ▸ hj')
    · obtain ⟨b, j, h1, h2, h3, -⟩ := (hnsE.drawn q hq).2.1.mono hnE
      have h2' : st0.avoid.contains q.2.2 = false := a7T.trans hav.2.2.2.1 ▸ h2
      exact ⟨fun _ hf => by simp [hf b j h1] at h2', fun b' j' h1' _ =>
        .inl (by rw [freshName_counter_inj (h1'.symm.trans h1)]; omega)⟩
  have hsnG : ∀ σF : SemanticStore P, (∀ y ∈ wDecls Tr.out.toList, σF y = σ1 y) →
      (∀ n ∈ wDecls Er.out.toList, σF n = σE' n) → ∀ ex, SnapFF F Er s5 ex σE' →
        SnapFF F r st' ex σF := fun σF hdT hFE ex hsnE l x hx hp hne =>
    (hregP l x hx hp).elim (fun ⟨hx, hp⟩ => (hdT x (hs.armT.regs x hx)).trans
      (hsnT l x hx hp nofun)) fun ⟨hx, hp⟩ => (hFE x (hs.armE.regs x hx)).trans (hsnE l x hx hp hne)
  have hokT : ∀ σF : SemanticStore P, WellFormedStore σF F → (∀ y ∈ wDecls Tr.out.toList,
      σF y = σ1 y) → (∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) → (∀ n, (σ1 n).isSome → (σF n).isSome) → CarryOK F T Y Tr s6 σF :=
      fun σF hCF hdT hFgt hb1F k i n v xB h => by
    obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoT _ _ _ _ _ h
    refine ⟨hsel.imp (hs.armT.sel e.hF hCF hC1 hdT h) (hs.armT.sel e.hF hCF hC1 hdT h), hty, ?_,
      ⟨w', by rw [hdT xB (hs.armT.regs xB h.2), hw'], hwt'⟩⟩
    rcases hs.armT.carryTgt _ _ _ _ _ h with ⟨z, hz, hzn⟩ | hn
    · rw [hs.cur6 z] at hzn
      obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.1 (hb1F n (by simp [hw]))
      exact ⟨w2, hw2, hFgt n w2 hw2 (e.curY hs hz hzn)⟩
    · exact ⟨w, by rw [hdT n hn, hw], hwt⟩
  rcases oE with σE1 | ⟨l, σE1⟩
  · obtain ⟨hOnE, hsnE, hcfE, hcoE, hEax, -, hexE⟩ := hpost
    obtain rfl : nsE = [] := by simpa [laidCE, hEax] using hnsE.vars
    rw [laidMergesAx_eq, hEax] at hMG
    have hTax : Tr.ax = true := e.ax.resolve_right (by simp [hEax])
    obtain ⟨σEr, hrunEr, hEr, hwrE, hlE, hTkE, hqE, hEreal⟩ : ∃ σEr : SemanticStore P,
        MainRun F iE σS trE σEr ∧ (∀ n, σEr n = σE' n ∨ (rE? = some n ∧ σEr n = none)) ∧
        (∀ n, σEr n ≠ σS n → Wr0 (Block.idents ess) s4 s5 n ∨ κE.wvar = some n) ∧
        (∀ n, Drawn s6 st' n → n ∉ RE.vars κE → σEr n = σS n) ∧ (∀ n ∈ wDecls Tr.out.toList,
        σEr n = σS n) ∧ (∀ q, κE = .andNeg q g → σEr q = σS q) ∧
        ((laidU κ κE rT Tr Er d).isNil = false → σEr = σE') := by
      rcases hvirt with rfl | ⟨x, hx, rfl, hx0, hEn, hUn⟩
      · exact ⟨σE', hrunE, fun _ => .inl rfl, hs.armE.writesW T Y iE hE _ trE σE' hrunE,
          fun n hn hnE => e.lateE hs hE hrunE hn hnE,
          e.crossKeep hs hE hrunE, fun q hq => hs.of_keepQ hE hrunE hq, fun _ => rfl⟩
      · obtain rfl := resolve_isNil hEn hE
        cases hrunE
        refine ⟨σS, .nil, fun n => ?_, fun n h => absurd rfl h, fun _ _ _ => rfl,
          fun _ _ => rfl, fun _ _ => rfl, fun h => by simp [hUn] at h⟩
        exact (Classical.em (x = n)).elim (fun h => h ▸ .inr ⟨hx, hx0⟩)
          fun hn => .inl ((update_facts σS x (HasBool.ttVal F)).2 n hn).symm
    have hCEr : WellFormedStore σEr F := fun x v hx =>
      (hEr x).elim (fun h => hOnE.canonL x v (h ▸ hx)) fun ⟨_, h⟩ => by simp [h] at hx
    obtain ⟨σC2, hrunC2, -, -, hothC2, -⟩ := copyRun e.hF hnsE hCEr hCPE nofun nofun
    rw [show σC2 = σEr from funext fun n => hothC2 n nofun] at hrunC2
    obtain ⟨σR2, hrunR2, -, -, hothR2⟩ := restoreRun e.hF hnsE hCEr hRSE (laidCE_nodup _ _ _)
      nofun nofun
    rw [show σR2 = σEr from funext fun n => hothR2 n nofun] at hrunR2
    have hgmEr : ∀ y, gm? = some y → σEr y = some (HasBool.ffVal F) := fun y hy => by
      have hd := (hlg y hy).1.of_le a7E hleE
      rw [hlE y (h7T6 y hd) (hlateκE y hd), hgmS y hy]
    rw [hcase.elim (fun h => by simp [hTax] at h) fun h => h.2.2.2, List.filter_nil] at hMG
    obtain ⟨σM2, hrunM2, -, -, hothM2⟩ := run_merges e.hF gm? _ [] σEr iMG hMG hCEr List.nodup_nil
      nofun (fun x hx => ⟨.inr (hgmEr x hx), nofun⟩) nofun
    rw [show σM2 = σEr from funext fun n => hothM2 n nofun] at hrunM2
    obtain ⟨hrM, hκEr⟩ := hwrS σEr hwrE hqE
    obtain ⟨trU, σF, hrunU, hCF, hfrU, hbU, hnilU, hnnU, -⟩ := run_U' e.hF hU hCEr
      (fun h => .inr (hrM h)) (fun h => .inl (hEreal h ▸ hOnE.reach))
      (fun y hy => hκEr y hy ▸ hon.reach.bools y hy)
      fun h => RE.Holds.bools (hEreal h ▸ hOnE.reach : κE.Holds F σEr)
    obtain ⟨hfU, hHF⟩ : Trace.AssumptionsHold P evalInterp () trU ∧ κ.Holds F σF := by
      cases hUn : (laidU κ κE rT Tr Er d).isNil
      · rcases Classical.em (κ = .top) with rfl | hκt
        · exact ⟨((hnnU hUn).1 rfl).2 (.inr (hEreal hUn ▸ hOnE.reach)), trivial⟩
        · obtain ⟨rfl, hhold, -⟩ := (hnnU hUn).2 hκt
          refine ⟨nofun, hhold (.inr (hEreal hUn ▸ hOnE.reach)) fun q g' hq => ?_⟩
          obtain ⟨h1, h2⟩ := hq ▸ hon.reach
          exact ⟨(hκEr q (by simp [hq, RE.vars])).trans h1,
            fun he => HasBool.ttVal_ne_ffVal F (Option.some.inj ((he ▸ h1).symm.trans h2))⟩
      · obtain ⟨rfl, rfl⟩ := hnilU hUn
        exact ⟨nofun, hon.reach.congr hκEr⟩
    refine ⟨_, σF, by wp_chain [hitems],
      Trace.AssumptionsHold.append hfeasT (Trace.AssumptionsHold.append hfeasE hfU), ?_⟩
    have hFst : ∀ z ∈ S, ∀ n, curName st' z = some n → σF n = σE' n := fun z hz n hzn => by
      rw [hfrU n fun h => (e.of_ctxNe hs h).2.2.1 z hz hzn]
      exact (hEr n).elim (fun h => h) fun ⟨h, _⟩ => absurd hzn (e.of_preNotCur hs (.inr h) hz)
    have hFn : ∀ z ∈ S, ∀ n, curName st0 z = some n → σF n = σE' n := fun z hz n hzn =>
      hFst z hz n (e.of_cur0 hs hz hzn).2.2
    have hFgt : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
      by_cases hnκ : n ∈ RE.vars κ
      · exact hκgt σF hbU n hnκ w hw hY ty hty
      · rw [hfrU n hnκ] at hw
        exact (hEr n).elim (fun h => hOnE.gtyped n w (h ▸ hw) hY ty hty)
          fun ⟨_, h⟩ => by simp [h] at hw
    have hFbE : ∀ y, (σF y).isSome → (σE' y).isSome := fun y hy => by
      have hyr : (σEr y).isSome := (Classical.em (y ∈ RE.vars κ)).elim (fun hyκ =>
        hκEr y hyκ ▸ hon.reach.bound y hyκ) fun hyκ => hfrU y hyκ ▸ hy
      exact (hEr y).elim (fun h => h ▸ hyr) fun ⟨_, h⟩ => by simp [h] at hyr
    have hfrF := hfr0 σE' σF hOnE.fresh fun y hy => .inl (hFbE y hy)
    have hdT : ∀ y ∈ wDecls Tr.out.toList, σF y = σ1 y := fun y hy => by
      rw [hfrU y fun hk => (e.of_ctxNe hs hk).1 hy, hTkE y hy, hTS y hy]
    have hFE : ∀ n ∈ wDecls Er.out.toList, σF n = σE' n := fun n hn => by
      rw [hfrU n fun h => (e.of_ctxNe hs h).2.1 hn]
      refine (hEr n).resolve_right fun ⟨h, _⟩ => (hEk n hn).elim (fun hk => ?_)
        fun ⟨y, hy⟩ => (hs.preNm (.inr (.inr h)) y).1 hy
      exact not_drawn_of n s1 s4 s4 s5 hk hav.1 (.inl (Nat.le_refl _))
        (hs.pre.drawn n (.inr (.inr h)))
    have hcpE : ∀ p ∈ laidCarry Er s6 cpsE, False := fun p hp => by
      simpa [hnsE.pairs] using mem_laidCarry hp
    have hb1F : ∀ n, (σ1 n).isSome → (σF n).isSome := fun n hn =>
      mainRun_mono hrunU n (mainRun_mono hrunEr n (mainRun_mono hrunCS n hn))
    have hcpF : ∀ q ∈ ns, σF q.2.2 = σL q.1 := fun q hq => by
      rw [hfrU _ fun hk => (e.of_ctxNe hs hk).2.2.2 s6 s7T (by omega) (hcpD q hq),
        hlE _ ((hcpD q hq).mono hnx.2.2.2.2.2) (hcpS q hq).1, (hcpS q hq).2]
    have hgmF : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ffVal F) :=
      fun y hy => ⟨hfB _ (hlg y hy).1 (hlg y hy).2, by
        rw [hfrU y (hlateκ y ((hlg y hy).1.of_le a7E hleE)), hgmEr y hy]⟩
    have hcar : CarryFF F T Y r st' σF ∧ CarryOK F T Y r st' σF := by
      have hcls := fun k => (Classical.choose_spec (e.rtxCls ht hs hns hcp6 k).1).2.1
      have hselT : ∀ p ∈ laidCarry Tr s6 cpsT, SelIs F T Y σF (.ite (optVar gm?) (.var p.2)
          (.var p.1)) false := fun p _ => selIs_gm e.hF hCF hgmF p.2 p.1
      refine ⟨fun k i n v xB hr => ?_, fun k i n v xB hr => ?_⟩
      · rcases hcls k i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, -, p, hp, ⟨⟩⟩ | ⟨p, hp, -⟩
        · exact hs.armT.sel e.hF hCF hC1 hdT h (hcfT _ _ _ _ _ h)
        · exact hs.armE.sel e.hF hCF hOnE.canonL hFE h (hcfE _ _ _ _ _ h)
        · exact hselT p hp
        · exact (hcpE p hp).elim
      · rcases hcls k i n v xB hr with ⟨-, h⟩ | ⟨i', h⟩ | ⟨-, -, p, hp, ⟨⟩⟩ | ⟨p, hp, -⟩
        · exact hokT σF hCF hdT hFgt hb1F _ _ _ _ _ h
        · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoE _ _ _ _ _ h
          exact ⟨hsel.imp (hs.armE.sel e.hF hCF hOnE.canonL hFE h)
              (hs.armE.sel e.hF hCF hOnE.canonL hFE h), hty,
            ⟨w, ((hs.armE.carryTgt _ _ _ _ _ h).elim (fun ⟨z, hz, hzn⟩ => hFst z hz _
              (hs.cur5 hz hzn).1) (hFE _ ·)).trans hw, hwt⟩,
            ⟨w', by rw [hFE xB (hs.armE.regs xB h.2), hw'], hwt'⟩⟩
        · obtain ⟨-, q, hq, rfl⟩ := hcpTm p hp
          obtain ⟨w, hw, hty⟩ := hsrcS q hq
          obtain ⟨z, hz, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
          obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.1
            (hb1F _ (mainRun_mono (MainRun.append hrun0 hrunT) _ (hq1 q hq)))
          exact ⟨.inr (hselT _ hp), htyC q hq,
            ⟨w2, hw2, hFgt _ w2 hw2 (e.curY hs hz hzn)⟩, ⟨w, (hcpF q hq).trans hw, hty⟩⟩
        · exact (hcpE p hp).elim
    have hpj : ∀ x ∈ S, x ∈ contFV k → projectStore σ σE1 x = σE1 x := fun x hx hv => by
      simp [projectStore, (hon.defd x hx (mem_contFV_cons.2 (.inr hv))).1]
    have hv' : ∀ x, x ∈ contFV k → x ∈ contFV (ess :: k) := fun x hv => mem_contFV_cons.2 (.inr hv)
    refine ⟨⟨⟨fun x hx hv n hn hl => ?_, fun x hx hv => ?_, fun x hx hv n hn hty w w' h1 h2 => ?_,
      fun x hx hxS => ?_, WellFormedStore.proj hOnE.canon, hCF, hFgt,
      fun x hx hv n hn w hw ty hty => ?_, hfrF⟩, hHF⟩, ?_, ?_, ?_,
      by rw [ht.ax, hTax, hEax]; rfl, ht.drop, ?_⟩
    · rw [hFn x hx n hn, hpj x hx hv]
      exact hOnE.agree x (scopeAfter_sub S ess hx) (hv' x hv) n (hn4 x n hn) (hlive4 ▸ hl)
    · rw [hpj x hx hv]
      exact ⟨(hOnE.defd x (scopeAfter_sub S ess hx) (hv' x hv)).1, fun n hn => hFn x hx n hn ▸
        (hOnE.defd x (scopeAfter_sub S ess hx) (hv' x hv)).2 n (hn4 x n hn)⟩
    · exact hOnE.alike x (scopeAfter_sub S ess hx) (hv' x hv) n (hn4 x n hn) hty w w'
        (hpj x hx hv ▸ h1) (hFn x hx n hn ▸ h2)
    · simp [projectStore, hon.undef x hx hxS]
    · exact hOnE.ltyped x (scopeAfter_sub S ess hx) (hv' x hv) n (hn4 x n hn) w (hpj x hx hv ▸ hw)
        ty hty
    · exact hsnG σF hdT hFE none hsnE
    · exact hcar.1
    · exact hcar.2
    · intro l x hx hp hl
      exact (hregP l x hx hp).elim (fun ⟨hx, hp⟩ => (hseT.2 l x hx hp hl).elim fun _ h => ⟨_, h⟩)
        fun ⟨hx, hp⟩ => (hexE l x hx hp hl).elim fun _ h => ⟨_, h⟩
  · obtain ⟨hOffE, hshE, hqE0, hcoE, hlabE⟩ := hpost
    obtain rfl : σS = σEs := by
      rcases hvirt with h | ⟨x, hx, rfl, hx0, hEn, hUn⟩
      · exact h.symm
      · obtain rfl := resolve_isNil hEn hE
        cases hrunE
        exact (hreachE.not_fails hOffE.reach).elim
    have hCE' : WellFormedStore σE' F := hOffE.canonL
    have hlE : ∀ n, Drawn s6 st' n → n ∉ RE.vars κE → σE' n = σS n := fun n hn hnE =>
      e.lateE hs hE hrunE hn hnE
    have hqE : ∀ q, κE = .andNeg q g → σE' q = σS q := fun q hq => hs.of_keepQ hE hrunE hq
    have hsvE6 : ∀ q ∈ nsE, Drawn s7T st' q.2.1 ∧ Drawn s7T st' q.2.2 := fun q hq =>
      ⟨hsvED q hq, (hnsE.drawn q hq).2.1.mono hnE⟩
    have hsrcE : ∀ q ∈ nsE, ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧
        curName st' z = some q.1 := fun q hq => hCEv q.1 (hnsE.vars ▸ List.mem_map_of_mem hq)
    have hL1E : ∀ q ∈ nsE, ∃ w, σL q.1 = some w ∧ ∀ ty, tyOfName T Y q.1 = .ok ty →
        HasVal.valueOfTy F w ty := fun q hq => e.boundOn hs hon (hsrcE q hq)
    have hbL1E : ∀ q ∈ nsE, (σL q.1).isSome := fun q hq => (hL1E q hq).elim fun _ h => by simp [h.1]
    have hE'b : ∀ n, (σL n).isSome → (σE' n).isSome := fun n hn =>
      mainRun_mono hrunE n (hSLb n hn ▸ hn)
    have hsrcE' : ∀ q ∈ nsE, ∃ w, σE' q.1 = some w ∧
        ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hE'b q.1 (hbL1E q hq))
      obtain ⟨z, hz, -, hzn⟩ := hsrcE q hq
      exact ⟨w, hw, fun ty hty => hOffE.gtyped q.1 w hw (e.curY hs hz hzn) ty hty⟩
    have hE0 : ∀ q ∈ nsE, σE' q.2.2 = none := fun q hq => by
      have hd := (hsvE6 q hq).2
      have hd7 := (hnsE.drawn q hq).2.1
      rw [hlE _ (h7T6 _ hd) (hlateκE _ hd), hSR _ (fun h => hrEng _ h _ hd rfl) (fun h => hd7.disj
        (hlr _ h).1 (Nat.le_refl _)) fun p hp => (flat_ne nsE hnsE.nodup p hp q hq).symm]
      exact hlateR _ hd (fun h' => hd7.disj (hlq _ (mem_laidQm h')).1 (Nat.le_refl _))
        fun y hy he => hd7.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)
    have hE'sv : ∀ q ∈ nsE, σE' q.2.1 = σL q.1 := fun q hq => by
      rw [hlE _ (h7T6 _ (hsvE6 q hq).1) (hlateκE _ (hsvE6 q hq).1), hSL q hq, hkR _ (hbL1E q hq)]
    obtain ⟨σC2, σR2, hrunC2, hrunR2, hCR2, hRcp2, hRv2, hRo2, htyC2⟩ := copyRestore e.hF hnsE
      (laidCE_nodup _ _ _) hCE' hCPE hRSE hE0 hsrcE' (fun q hq => (hL1E q hq).imp fun _ h =>
      ⟨(hE'sv q hq).trans h.1, h.2⟩) fun q hq p hp => ⟨fun he => hLlate q.1 (hbL1E q hq)
      (he ▸ (hsvE6 p hp).1), fun he => hLlate q.1 (hbL1E q hq) (he ▸ (hsvE6 p hp).2)⟩
    have hR2r : ∀ q ∈ nsE, σR2 q.1 = σL q.1 := fun q hq => (hRv2 q hq).trans (hE'sv q hq)
    have hR2keep' : ∀ n, (∀ q ∈ nsE, n ≠ q.1) → (∀ q ∈ nsE, n ≠ q.2.2) → σR2 n = σE' n :=
      fun n h1 h2 => hRo2 n fun q hq => ⟨h1 q hq, h2 q hq⟩
    have hR2gt : ∀ n w, σR2 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
      rcases Classical.em (∃ q ∈ nsE, n = q.1) with ⟨q, hq, rfl⟩ | hr
      · exact hon.gtyped _ w ((hR2r q hq).symm.trans hw) hY ty hty
      · rcases Classical.em (∃ q ∈ nsE, n = q.2.2) with ⟨q, hq, rfl⟩ | hc
        · simp [e.fin.2.1 q.2.2 q.1 (hyoE ▸ (hnsE.drawn q hq).2.2.2)] at hY
        · rw [hR2keep' n (fun q hq he => hr ⟨q, hq, he⟩) (fun q hq he => hc ⟨q, hq, he⟩)] at hw
          exact hOffE.gtyped n w hw hY ty hty
    have hR2cp : ∀ q ∈ ns, σR2 q.2.2 = σL q.1 := fun q hq => by
      have h1 : ∀ p ∈ nsE, q.2.2 ≠ p.1 := fun p hp he => by simpa [← he, hcpL q hq] using hbL1E p hp
      have h2 : ∀ p ∈ nsE, q.2.2 ≠ p.2.2 := fun p hp he =>
        (hcpD q hq).disj (he.symm ▸ (hnsE.drawn p hp).2.1 : Drawn s7T s7E q.2.2) (Nat.le_refl _)
      rw [hR2keep' _ h1 h2, hlE _ ((hcpD q hq).mono hnx.2.2.2.2.2) (hcpS q hq).1, (hcpS q hq).2]
    rw [laidMergesAx_eq] at hMG
    generalize hlM : cps3.filter (fun p => liveBefore s6 p.1 s4.clock) = lM at hMG
    have hlMmem : ∀ p ∈ lM, ∃ q ∈ ns, p = (q.1, q.2.2) ∧ liveBefore s6 q.1 s4.clock = true ∧
        Tr.ax = false := fun p hp => by
      rw [← hlM] at hp
      obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
      rcases hcase with ⟨hTa, -, hc3, -⟩ | ⟨-, -, -, hc3⟩
      · obtain ⟨q, hq, rfl⟩ := hns.mem_pairs.1 _ (hc3 ▸ hp1)
        exact ⟨q, hq, rfl, hp2, hTa⟩
      · simp [hc3] at hp1
    have hEax : ∀ p ∈ lM, Er.ax = true := fun p hp =>
      (hlMmem p hp).elim fun q ⟨_, _, _, hTa⟩ => e.ax.resolve_left (by simp [hTa])
    have hlMnd : (lM.map (·.1)).Nodup := by
      rw [← hlM]
      refine (List.filter_sublist.map _).nodup ?_
      rcases hcase with ⟨-, -, hc3, -⟩ | ⟨-, -, -, hc3⟩
      · exact hc3 ▸ hns.mem_pairs.2 hMnd
      · simp [hc3]
    have hlMfst : ∀ n ∈ lM.map (·.1), ∃ q ∈ ns, n = q.1 := fun n hn => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
      obtain ⟨q, hq, rfl, -⟩ := hlMmem p hp
      exact ⟨q, hq, rfl⟩
    have hcpnot : ∀ p ∈ lM, p.2 ∉ lM.map (·.1) := fun p hp hm => by
      obtain ⟨q, hq, rfl, -⟩ := hlMmem p hp
      exact (hlMfst _ hm).elim fun q' ⟨hq', he⟩ => hLcp q'.1 (hq1 q' hq') q hq he.symm
    have hgmR2 : ∀ y, gm? = some y → σR2 y = some (HasBool.ffVal F) := fun y hy => by
      have hd := (hlg y hy).1.of_le a7E hleE
      rw [hR2keep' y (fun q hq he => hLlate q.1 (hbL1E q hq) (he ▸ hd))
          (fun q hq he => (hnsE.drawn q hq).2.1.disj (he ▸ (hlg y hy).1) (Nat.le_refl _)),
        hlE y (h7T6 y hd) (hlateκE y hd), hgmS y hy]
    have hgmM : ∀ x, gm? = some x →
        (σR2 x = some (HasBool.ttVal F) ∨ σR2 x = some (HasBool.ffVal F)) ∧ x ∉ lM.map (·.1) :=
      fun x hx => ⟨.inr (hgmR2 x hx), fun hm => by
        obtain ⟨q, hq, rfl⟩ := hlMfst _ hm
        exact hLlate q.1 (hq1 q hq) ((hlg q.1 hx).1.of_le a7E hleE)⟩
    have htyM : ∀ p ∈ lM, ∃ w w' ty, σR2 p.1 = some w ∧ σR2 p.2 = some w' ∧
        HasVal.valueOfTy F w ty ∧ HasVal.valueOfTy F w' ty := fun p hp => by
      obtain ⟨q, hq, rfl, -⟩ := hlMmem p hp
      obtain ⟨ty, hty⟩ := htyC q hq
      obtain ⟨w', hw', hty'⟩ := hsrcS q hq
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
        (mainRun_mono hrunR2 _ (mainRun_mono hrunC2 _ (hE'b _ (hq1 q hq))))
      obtain ⟨z, hz, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
      exact ⟨w, w', ty, hw, by rw [hR2cp q hq, hw'],
        hR2gt q.1 w hw (e.curY hs hz hzn) ty hty, hty' ty hty⟩
    obtain ⟨σM2, hrunM2, hCM2, hvalM2, hothM2⟩ :=
      run_merges e.hF gm? (if Er.ax then {} else Er.A) lM σR2 iMG hMG hCR2 hlMnd hcpnot hgmM htyM
    have hM2v : ∀ p ∈ lM, σM2 p.1 = σR2 p.2 := fun p hp => by
      simp [hvalM2 p hp, hEax p hp, mergeVal]
    have hcurPre : ∀ z ∈ S, ∀ n, curName st' z = some n →
        ∀ x, (x = g ∨ x = rT ∨ rE? = some x) → n ≠ x := fun z hz n hzn x hx he => by
      subst he
      rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
      · exact (hs.preNm hx z).2.2.2 hm
      · obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn _ hx
        simp [hav.1, e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2
    have hM2keep : ∀ n, (∀ z ∈ S, curName st' z ≠ some n) → ¬ Drawn s7T st' n → σM2 n = σE' n :=
        fun n h1 h2 => by rw [hothM2 n fun hm => (hlMfst _ hm).elim fun q ⟨hq, he⟩ => (hMv q.1
        (hns.vars ▸ List.mem_map_of_mem hq)).elim fun z ⟨hz, _, hzn⟩ => h1 z hz (he ▸ hzn), hRo2 n
        fun q hq => ⟨fun he => (hsrcE q hq).elim fun z ⟨hz, _, hzn⟩ => h1 z hz (he ▸ hzn), fun he =>
        h2 (he ▸ (hsvE6 q hq).2)⟩]
    have hκ : κ ≠ .top := fun h => htop ⟨h, l, _, rfl⟩
    have hUf : (laidU κ κE rT Tr Er d).isNil = false := by
      have h := hs.armE.exitMin (fun l t hl =>
        (e.lab l t ((e.labels hs l).1.symm.trans hl)).1) _ σ evs l σE1 hE'
      cases κ <;> simp [laidU, h, setReach, Rope.isNil] at hκ ⊢
    obtain ⟨hrE', hκEr⟩ := hwrS σE' (hs.armE.writesW T Y iE hE _ trE σE' hrunE) hqE
    have hrM : σM2 rT = some (HasBool.ffVal F) := by
      rw [hM2keep rT (fun z hz hzn => hcurPre z hz rT hzn rT (.inr (.inl rfl)) rfl)
        (fun hd => (hs.pre.drawn rT (.inr (.inl rfl))).disj hd (by omega)), hrE' hUf]
    have hM2E : ∀ y ∈ RE.vars κE, σM2 y = σE' y := fun y hy =>
      hM2keep y (fun z hz hzn => (hκE' y hy).elim (fun h => hcurPre z hz y hzn y (.inl h) rfl)
          fun ho1 => ho1.elim (fun h => hcurPre z hz y hzn y (.inr (.inr h)) rfl)
          fun h => (e.of_ctxNe hs h).2.2.1 z hz hzn) fun hd => hlateκE y hd hy
    have hfailM : κE.Fails F σM2 := of_failsCongr hOffE.reach hM2E
    have hκM : ∀ y ∈ RE.vars κ, σM2 y = σL y := fun y hy => by rw [hM2keep y (fun z hz hzn =>
      (e.of_ctxNe hs hy).2.2.1 z hz hzn) (fun hd => hlateκ y hd hy), hκEr y hy]
    obtain ⟨trU, σF, hrunU, hCF, hfrU, hbU, -, hnnU, hkU⟩ := run_U e.hF hU hCM2 (.inr hrM)
        (.inr hfailM) (fun y hy => hκM y hy ▸ hon.reach.bools y hy)
        fun y hy => hM2E y hy ▸ hOffE.bools y hy
    obtain ⟨rfl, -, hfailF0⟩ := (hnnU hUf).2 hκ
    have hfailF : κ.Fails F σF := hfailF0 fun h => h.elim
      (fun h => HasBool.ttVal_ne_ffVal F (Option.some.inj (h.symm.trans hrM)))
      fun h => h.not_fails hfailM
    have hrunAll : MainRun F items σL (trT ++ (trE ++ [])) σF := by wp_chain [hitems]
    refine ⟨_, σF, hrunAll, Trace.AssumptionsHold.append hfeasT
      (Trace.AssumptionsHold.append hfeasE nofun), ?_⟩
    have hdT : ∀ y ∈ wDecls Tr.out.toList, σF y = σ1 y := fun y hy => by rw [hfrU y fun hk =>
      (e.of_ctxNe hs hk).1 hy, hM2keep y (fun z hz hzn => hs.armT.declNotCur y hy z hz
      ((hs.cur6 z).trans hzn)) (hTlate y hy), e.crossKeep hs hE hrunE y hy, hTS y hy]
    have hFE : ∀ n ∈ wDecls Er.out.toList, σF n = σE' n := fun n hn => by
      rw [hfrU n fun h => (e.of_ctxNe hs h).2.1 hn]
      refine hM2keep n (fun z hz hc => ?_) fun hd => ?_
      · exact e.re_EdeclNotM hs hn hz hc
      · rcases hEk n hn with hk | ⟨y, hy⟩
        · exact not_drawn_of n s7T st' s4 s5 hk (a7T.trans hav.2.2.2.1) (.inr (by omega)) hd
        · exact (dl_nmBelow hs.wf4 hy).elim fun b ⟨j, h1, h2⟩ => hd.not_below ⟨b, j, h1, by omega⟩
    have hcpFT : ∀ q ∈ ns, σF q.2.2 = σL q.1 := fun q hq => by rw [hfrU _ fun hk =>
      (e.of_ctxNe hs hk).2.2.2 s6 s7T (by omega) (hcpD q hq), hothM2 _ fun hm => (hlMfst _ hm).elim
      fun q' ⟨hq', he⟩ => hLcp q'.1 (hq1 q' hq') q hq he.symm, hR2cp q hq]
    have hcpFE : ∀ q ∈ nsE, σF q.2.2 = σE' q.1 := fun q hq => by
      rw [hfrU _ (hlateκ _ (hsvE6 q hq).2), hothM2 _ fun hm => (hlMfst _ hm).elim fun p ⟨hp, he⟩ =>
          hLlate p.1 (hq1 p hp) (he ▸ (hsvE6 q hq).2), hRcp2 q hq]
    have hcurLate : ∀ z ∈ S, ∀ n, curName st' z = some n → ¬ Drawn s6 st' n :=
      fun z hz n hzn hd => by
        rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
        · exact hd.elim fun b ⟨j, h1, _, h3, _⟩ => hs.lateNm ⟨b, j, h1, h3⟩ z hm
        · obtain ⟨b, j, h1, h2, -, -⟩ := hd
          simp [hav.2.2.2.1, e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2
    have hFcur : ∀ z ∈ S, ∀ n, curName st' z = some n →
        (((∃ q ∈ nsE, n = q.1) ∨ (∃ q ∈ ns, n = q.1 ∧ n ∈ lM.map (·.1))) ∧ σF n = σL n) ∨
        ((∀ q ∈ nsE, n ≠ q.1) ∧ n ∉ lM.map (·.1) ∧ σF n = σE' n) := fun z hz n hzn => by
      rw [hfrU n fun hk => (e.of_ctxNe hs hk).2.2.1 z hz hzn]
      by_cases hm : n ∈ lM.map (·.1)
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
        obtain ⟨q, hq, rfl, -⟩ := hlMmem p hp
        exact .inl ⟨.inr ⟨q, hq, rfl, hm⟩, (hM2v _ hp).trans (hR2cp q hq)⟩
      · rw [hothM2 n hm]
        rcases Classical.em (∃ q ∈ nsE, n = q.1) with ⟨q, hq, rfl⟩ | hr
        · exact .inl ⟨.inl ⟨q, hq, rfl⟩, hR2r q hq⟩
        · exact .inr ⟨fun q hq he => hr ⟨q, hq, he⟩, hm, hR2keep' n (fun q hq he => hr ⟨q, hq, he⟩)
            fun q hq he => hcurLate z hz n hzn (h7T6 _ (he ▸ (hsvE6 q hq).2))⟩
    have hFgt : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
      by_cases hnκ : n ∈ RE.vars κ
      · exact hκgt σF hbU n hnκ w hw hY ty hty
      · rw [hfrU n hnκ] at hw
        by_cases hm : n ∈ lM.map (·.1)
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
          obtain ⟨q, hq, rfl, -⟩ := hlMmem p hp
          exact hon.gtyped _ w (((hM2v _ hp).trans (hR2cp q hq)).symm.trans hw) hY ty hty
        · exact hR2gt n w ((hothM2 n hm).symm.trans hw) hY ty hty
    have hbF : ∀ n, (σL n).isSome → (σF n).isSome := fun n hn => mainRun_mono hrunAll n hn
    have hE'F : ∀ n, (σE' n).isSome → (σF n).isSome := fun n hn => mainRun_mono hrunU n
      (mainRun_mono hrunM2 n (mainRun_mono hrunR2 n (mainRun_mono hrunC2 n hn)))
    have hfrF := hfr0 σE' σF hOffE.fresh fun y hy => by
      by_cases hyκ : y ∈ RE.vars κ
      · exact .inl (hκEr y hyκ ▸ hon.reach.bound y hyκ)
      · rw [hfrU y hyκ] at hy
        by_cases hm : y ∈ lM.map (·.1)
        · obtain ⟨q, hq, rfl⟩ := hlMfst y hm
          exact .inl (hE'b _ (hq1 q hq))
        · rw [hothM2 y hm] at hy
          rcases Classical.em (∃ q ∈ nsE, y = q.1) with ⟨q, hq, rfl⟩ | hr
          · exact .inl (hE'b _ (hbL1E q hq))
          · by_cases hc : ∃ q ∈ nsE, y = q.2.2
            · exact .inr hc
            · rw [hR2keep' y (fun q hq he => hr ⟨q, hq, he⟩) (fun q hq he => hc ⟨q, hq, he⟩)] at hy
              exact .inl hy
    have hgmF : ∀ y, gm? = some y → T[y]? = some HasBool.boolTy ∧ σF y = some (HasBool.ffVal F) :=
      fun y hy => ⟨hfB _ (hlg y hy).1 (hlg y hy).2, by
        rw [hfrU y (hlateκ y ((hlg y hy).1.of_le a7E hleE)), hothM2 y (hgmM y hy).2, hgmR2 y hy]⟩
    have hselEF : ∀ p ∈ laidCarry Er s6 cpsE,
        SelIs F T Y σF (.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1)) true := by
      intro p hp
      have hne : (laidCarry Er s6 cpsE).isEmpty = false :=
        List.isEmpty_eq_false_iff_exists_mem.2 ⟨_, hp⟩
      refine rex_selE e.hF hCF hκ hgmF (fun q hq => ?_) (fun hnq => ?_) p.2 p.1
      · rcases ht.qm with ⟨-, -, y, hy, -⟩ | ⟨hno, -, -⟩
        · refine ⟨y, hy, hextT y (by simp only [hq, hy, laidQm, List.mem_singleton]), ?_⟩
          have hd := (hqmD y hy).1
          have hyS := hSR y (fun h => hrEng y h y hd rfl) (fun h => (hlr y h).2.2.2 y hy rfl)
            fun q' hq' he => (hnsE.drawn q' hq').1.disj (he ▸ (hlq y hy).1) (Nat.le_refl _)
          rw [hfrU y (hlateκ y hd), hothM2 y fun hm => (hlMfst _ hm).elim fun q' ⟨hq', he⟩ =>
              hLlate q'.1 (hq1 q' hq') (he ▸ hd), hR2keep' y (fun q' hq' he => hLlate q'.1
              (hbL1E q' hq') (he ▸ hd)) (fun q' hq' he => (hnsE.drawn q' hq').2.1.disj
              (he ▸ (hlq y hy).1) (Nat.le_refl _)), hlE y (h7T6 y hd) (hlateκE y hd), hyS, hR1 y
              fun q' hq' he => (hcpD q' hq').disj (he ▸ hd) (Nat.le_refl _), hext1 y
              (by simp only [hq, hy, laidQm, List.mem_singleton]), hBq q y hq hy]
          simpa [hq, RE.Holds] using hon.reach
        · exact absurd ⟨⟨q, hq⟩, hne⟩ hno
      · obtain ⟨xr, hxr⟩ := rex_rEsome e.ctx hκ hnq
        rcases ht.rEm with ⟨-, -, y, hy, -⟩ | ⟨hno, -, -⟩
        · refine ⟨y, hy, hfB _ (hlr y hy).1 (hlr y hy).2.1, ?_⟩
          have hd := (hrEmD y hy).1
          rw [hfrU y (hlateκ y hd), hothM2 y fun hm => (hlMfst _ hm).elim fun q' ⟨hq', he⟩ =>
              hLlate q'.1 (hq1 q' hq') (he ▸ hd), hR2keep' y (fun q' hq' he => hLlate q'.1
              (hbL1E q' hq') (he ▸ hd)) (fun q' hq' he => (hnsE.drawn q' hq').2.1.disj
              (he ▸ (hlr y hy).1) (Nat.le_refl _)), hlE y (h7T6 y hd) (hlateκE y hd), hothS y
              fun q' hq' he => (hnsE.drawn q' hq').1.disj (he ▸ (hlr y hy).1) (Nat.le_refl _)]
          rcases hcaseM with ⟨-, hno⟩ | ⟨r', x', -, hx', hσM⟩
          · exact (hno xr y hxr hy).elim
          · cases hy.symm.trans hx'
            exact hσM ▸ (update_facts σD _ (HasBool.ttVal F)).1
        · exact absurd ⟨by simp [hxr], hne⟩ hno
    have hcoR : CarryOK F T Y r st' σF := fun k i n v xB hr => by
      obtain ⟨m, -, -, -, hcls⟩ := (e.rtxCls ht hs hns hcp6 k).2
      rcases hcls i n v xB hr with ⟨i', h⟩ | ⟨-, h⟩ | ⟨p, hp, ⟨⟩⟩ | ⟨-, hget, -⟩
      · exact hokT σF hCF hdT hFgt (fun n hn => hE'F n (mainRun_mono hrunE n
          (mainRun_mono hrunCS n hn))) _ _ _ _ _ h
      · obtain ⟨hsel, hty, ⟨w, hw, hwt⟩, ⟨w', hw', hwt'⟩⟩ := hcoE _ _ _ _ _ h
        refine ⟨hsel.imp (hs.armE.sel e.hF hCF hCE' hFE h) (hs.armE.sel e.hF hCF hCE' hFE h), hty,
          ?_, ⟨w', by rw [hFE xB (hs.armE.regs xB h.2), hw'], hwt'⟩⟩
        rcases hs.armE.carryTgt _ _ _ _ _ h with ⟨z, hz, hzn⟩ | hn
        · obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.1 (hE'F n (by simp [hw]))
          exact ⟨w2, hw2, hFgt n w2 hw2 (e.curY hs hz (hs.cur5 hz hzn).1)⟩
        · exact ⟨w, by rw [hFE n hn, hw], hwt⟩
      · obtain ⟨-, q, hq, rfl⟩ := hcpTm p hp
        obtain ⟨w, hw, hty⟩ := hsrcS q hq
        obtain ⟨z, hz, -, hzn⟩ := hMv q.1 (hns.vars ▸ List.mem_map_of_mem hq)
        obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.1 (hbF q.1 (hq1 q hq))
        exact ⟨.inr (selIs_gm e.hF hCF hgmF _ _), htyC q hq,
          ⟨w2, hw2, hFgt _ w2 hw2 (e.curY hs hz hzn)⟩, ⟨w, (hcpFT q hq).trans hw, hty⟩⟩
      · obtain ⟨p, hp, ⟨⟩⟩ := List.mem_map.1 (List.mem_reverse.1 (List.mem_of_getElem? hget))
        obtain ⟨q, hq, rfl⟩ := hcpEm p hp
        obtain ⟨w, hw, hty⟩ := hsrcE' q hq
        obtain ⟨z, hz, -, hzn⟩ := hsrcE q hq
        obtain ⟨w2, hw2⟩ := Option.isSome_iff_exists.1 (hbF q.1 (hbL1E q hq))
        exact ⟨.inl (hselEF _ hp), htyC2 q hq,
          ⟨w2, hw2, hFgt _ w2 hw2 (e.curY hs hz hzn)⟩, ⟨w, (hcpFE q hq).trans hw, hty⟩⟩
    have hsnF := hsnG σF hdT hFE
    refine ⟨⟨hCF, hfailF, hbU, fun x hx hv n hn => ?_, hFgt, hfrF⟩, ⟨fun hax => ?_,
      fun l' x hx hp hl => ?_⟩, fun q0 g0 hq => ?_, hcoR, ?_⟩
    · have hn' := (e.of_cur0 hs hx hn).2.2
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
        (hbF n ((hon.defd x hx (mem_contFV_cons.2 (.inr hv))).2 n hn'))
      exact ⟨w, hw, fun ty hty => hFgt n w hw (e.curY hs hx hn') ty hty⟩
    · rw [ht.ax] at hax
      cases hTa : Tr.ax
      · exact (hseT.1 hTa).elim fun _ h => ⟨_, h⟩
      · exact (hshE.1 (by simpa [hTa] using hax)).elim fun _ h => ⟨_, h⟩
    · exact (hregP l' x hx hp).elim (fun ⟨hx, hp⟩ => (hseT.2 l' x hx hp nofun).elim
        fun _ h => ⟨_, h⟩) fun ⟨hx, hp⟩ => (hshE.2 l' x hx hp hl).elim fun _ h => ⟨_, h⟩
    · have h := hq ▸ hon.reach
      rw [hkU _ _ hq q0 fun he =>
          HasBool.ttVal_ne_ffVal F (Option.some.inj (h.1.symm.trans (he ▸ h.2))),
        hκM q0 (by simp [hq, RE.vars])]
      exact h.1
    have hl4 : s4.labelDepth[l]? = st0.labelDepth[l]? := (e.labels hs l).1
    split
    · rename_i t hlt
      split at hlabE
      · rename_i t' ht4
        cases hlt.symm.trans (hl4.symm.trans ht4)
        obtain ⟨e0, he0, hp0, het, hsn0, hcore, hbelow⟩ := hlabE
        have hL4 : ∀ (l : String) (t : Nat), s4.labelDepth[l]? = some t → t ≤ d := fun l t h =>
          (e.lab l t ((e.labels hs l).1 ▸ h)).1
        obtain ⟨K, hK, htK, lK, hlK⟩ := arm_exitTgt e.runE hs.ctxE hs.dead4 hL4 hE' (hl4.trans hlt)
        have hKE : ∀ k i n v xB, CarryReg Er s5 k i n v xB → k ≤ K := fun k i n v xB h => by
          obtain ⟨K', hK', hk⟩ := arm_carryDepth e.runE hs.wf4 hs.dead4
            (fun l t h => (e.lab l t ((e.labels hs l).1 ▸ h)).1) (fun h => absurd h hs.ctxE) h.1 h.2
          cases hK.symm.trans hK'
          exact hk
        have hprojL : ∀ x ∈ Lab l, projectStore σ σE1 x = σE1 x := fun x hx => by
          simp [projectStore, (hon.defd x ((e.lab l t hlt).2 x hx).2
            (mem_contFV_cons.2 (.inr ((e.lab l t hlt).2 x hx).1))).1]
        have hndE : ((laidCarry Er s6 cpsE).map (·.1)).Nodup := by
          have h0 : (cpsE.map (·.1)).Nodup := hnsE.mem_pairs.2 (laidCE_nodup _ _ _)
          unfold laidCarry carryOf
          split
          · exact (List.filter_sublist.map _).nodup h0
          · exact List.nodup_nil
        refine ⟨e0, ht.regs ▸ List.mem_append_left _ (List.mem_append_right _ he0),
          hs.aft.pending ▸ hs.armT.pendKeep l e0 hp0,
          (hFE e0 (hs.armE.regs e0 he0)).trans het, hsnF _ hsn0, ?_, fun k' i n v xB hk h => ?_⟩
        · refine
            { xagree := fun x hx hv n hn hl hlf w hw => ?_
              defd := fun x hx hv => ⟨hprojL x hv ▸ (hcore.defd x (scopeAfter_sub S ess hx) hv).1,
                fun n hn => hE'F n ((hcore.defd x (scopeAfter_sub S ess hx) hv).2 n (hn4 x n hn))⟩
              alike := fun x hx hv n hn hnt w w' h1 h2 ty hty => ?_
              undef := fun x hx hxS => by simp [projectStore, hon.undef x hx hxS]
              canon := WellFormedStore.proj hcore.canon
              canonL := hCF
              gtyped := hFgt
              ltyped := fun x hx hv n hn w hw ty hty =>
                hcore.ltyped x (scopeAfter_sub _ _ hx) hv n (hn4 x n hn) w (hprojL x hv ▸ hw) ty hty
              fresh := hfrF }
          · have hn' := (e.of_cur0 hs hx hn).2.2
            obtain ⟨hlf4, -, hlf6⟩ := e.liveFrom hs hx hn hl hlf
            have hag := hcore.xagree x (scopeAfter_sub S ess hx) hv n (hn4 x n hn)
              (hlive4 ▸ hl) hlf4 w (hprojL x hv ▸ hw)
            have hcomp : ∀ k' i' v' xB', CarryReg r st' k' i' n v' xB' → SelIs F T Y σF v' true →
                (∃ m, (st'.carries.getD k' []).length = m + (s5.carries.getD k' []).length ∧
                m ≤ i' ∧ CarryReg Er s5 k' (i' - m) n v' xB' ∧ SelIs F T Y σE' v' true) ∨ (k' = K ∧
                ∃ m, (st'.carries.getD k' []).length = m + (s5.carries.getD k' []).length ∧ i' < m ∧
                (((laidCarry Er s6 cpsE).map fun p => (p.1, .ite (elseGuard κ gm? qm? rEm?)
                (.var p.2) (.var p.1), p.2)).reverse)[i']? = some (n, v', xB')) := by
              intro k' i' v' xB' h hsel
              obtain ⟨m, hm, -, -, hcls⟩ := (e.rtxCls ht hs hns hcp6 k').2
              rcases hcls i' n v' xB' h with ⟨i'', h'⟩ | ⟨hle, h'⟩ | ⟨p, hp, ⟨⟩⟩ | ⟨hK', hget, hlt⟩
              · exact (SelIs.ne hsel (hs.armT.sel e.hF hCF hC1 hdT h' (hcfT _ _ _ _ _ h'))).elim
              · exact .inl ⟨m, hm, hle, h', hs.armE.sel e.hF hCE' hCF (Eq.symm <| hFE · ·) h' hsel⟩
              · exact (SelIs.ne hsel (selIs_gm e.hF hCF hgmF _ _)).elim
              · cases hK.symm.trans hK'
                exact .inr ⟨rfl, m, hm, hlt, hget⟩
            have hndAE : ((((laidCarry Er s6 cpsE).map fun p =>
                (p.1, WExpr.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)).reverse).map
                  (·.1)).Nodup := by
              rw [List.map_reverse, List.map_map]
              exact (List.reverse_perm _).nodup_iff.2 hndE
            refine ⟨fun k i v xB h => (hcoR k i n v xB h).1, ?_⟩
            rcases hag.2 with ⟨hall, hnw⟩ | ⟨k, i, v, xB, htk, hrg, hsel, hxB, hmax⟩
            · rcases Classical.em (∃ q ∈ nsE, n = q.1) with ⟨q, hq, rfl⟩ | hCE
              · have hp : (q.1, q.2.2) ∈ laidCarry Er s6 cpsE := by
                  unfold laidCarry carryOf
                  rw [hK]
                  refine List.mem_filter.2 ⟨?_, ?_⟩
                  · exact hnsE.pairs ▸ List.mem_reverse.2 (List.mem_map_of_mem
                      (f := fun q : P.Ident × P.Ident × P.Ident => (q.1, q.2.2)) hq)
                  · exact hlf6 lK K (by rw [hs.wT.labelDepth lK, (e.labels hs lK).2,
                      ← (e.labels hs lK).1, hlK]) htK
                obtain ⟨i0, hi0⟩ := List.mem_iff_getElem?.1 (List.mem_reverse.2
                  (List.mem_map_of_mem (f := fun p =>
                    (p.1, WExpr.ite (elseGuard κ gm? qm? rEm?) (.var p.2) (.var p.1), p.2)) hp))
                obtain ⟨m, -, -, hnew, -⟩ := (e.rtxCls ht hs hns hcp6 K).2
                obtain ⟨hget0, -⟩ := hnew hK i0 _ hi0
                refine .inr ⟨K, i0, _, q.2.2, htK, ⟨hget0, ?_⟩, hselEF _ hp, (hcpFE q hq).trans hnw,
                  fun k' i' v' xB' htk' h hs' => ?_⟩
                · rw [ht.regs]
                  exact List.mem_append_right _
                    (List.mem_append_right _ (List.mem_map.2 ⟨_, hp, rfl⟩))
                · rcases hcomp k' i' v' xB' h hs' with ⟨m', -, -, h', hsel'⟩ |
                    ⟨rfl, m', -, -, hget'⟩
                  · exact (SelIs.ne hsel' (hall _ _ _ _ htk' h')).elim
                  · exact .inr ⟨rfl, Nat.le_of_eq (rex_nodupIdx _ hndAE i' i0 q.1
                      (by rw [List.getElem?_map, hget']; rfl)
                      (by rw [List.getElem?_map, hi0]; rfl))⟩
              · have hnot : ∀ p ∈ laidCarry Er s6 cpsE, p.1 ≠ n := fun p hp he => by
                  obtain ⟨q, hq, rfl⟩ := hcpEm p hp
                  exact hCE ⟨q, hq, he.symm⟩
                have hFn : σF n = σE' n := by
                  rcases hFcur x hx n hn' with ⟨hsv, hFL⟩ | ⟨-, -, hFn⟩
                  · rcases hsv with ⟨q, hq, he⟩ | ⟨q, hq, rfl, hm⟩
                    · exact (hCE ⟨q, hq, he⟩).elim
                    · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hm
                      obtain ⟨q', -, hpq, hlv, -⟩ := hlMmem p hp
                      have hlvn : liveBefore s6 q.1 s4.clock = true := by rwa [← hpe, hpq]
                      have hA : Er.A.contains q.1 = false := Bool.eq_false_iff.2 fun hA => by
                        have hmem : q.1 ∈ laidCE Er s6 s4.clock := by
                          simp [laidCE, hEax p hp, Std.HashSet.fold_eq_foldl_toList,
                            mem_foldl_filter, Std.HashSet.mem_iff_contains, hA, hlvn]
                        obtain ⟨q'', hq'', he⟩ := List.mem_map.1 (hnsE.vars ▸ hmem)
                        exact hCE ⟨q'', hq'', he.symm⟩
                      have hnκE : q.1 ∉ RE.vars κE := e.of_notκE hs
                        (fun h => (e.of_ctxNe hs h).2.2.1 x hx hn') (.inl ⟨x, hx, hn'⟩)
                      rw [hFL, hkLE hCS hrunE hA hnκE (LaidCore.live65 hs hlvn), hSLb _ (hq1 q hq)]
                  · exact hFn
                refine .inl ⟨fun k' i' v' xB' htk' h => ?_, hFn.trans hnw⟩
                obtain ⟨m, -, -, -, hcls⟩ := (e.rtxCls ht hs hns hcp6 k').2
                rcases hcls i' n v' xB' h with ⟨i'', h'⟩ | ⟨-, h'⟩ | ⟨p, hp, ⟨⟩⟩ | ⟨-, hget, -⟩
                · exact hs.armT.sel e.hF hCF hC1 hdT h' (hcfT _ _ _ _ _ h')
                · exact hs.armE.sel e.hF hCF hCE' hFE h' (hall _ _ _ _ htk' h')
                · exact selIs_gm e.hF hCF hgmF _ _
                · obtain ⟨p, hp, ⟨⟩⟩ :=
                    List.mem_map.1 (List.mem_reverse.1 (List.mem_of_getElem? hget))
                  exact (hnot p hp rfl).elim
            · obtain ⟨m, hm, hsh, -, -⟩ := (e.rtxCls ht hs hns hcp6 k).2
              refine .inr ⟨k, i + m, v, xB, htk, hsh _ _ _ _ hrg,
                hs.armE.sel e.hF hCF hCE' hFE hrg hsel,
                (hFE xB (hs.armE.regs xB hrg.2)).trans hxB, fun k' i' v' xB' htk' h hs' => ?_⟩
              rcases hcomp k' i' v' xB' h hs' with ⟨m', hm', hle, h', hsel'⟩ |
                ⟨rfl, m', hm', hlt, -⟩
              · exact (hmax _ _ _ _ htk' h' hsel').imp_right fun ⟨he, _⟩ => ⟨he, by subst he; omega⟩
              · exact (Nat.lt_or_eq_of_le (hKE _ _ _ _ _ hrg)).imp_right fun he =>
                  ⟨he, by subst he; omega⟩
          · rcases hFcur x hx n (e.of_cur0 hs hx hn).2.2 with ⟨hsv, -⟩ | ⟨-, -, hFn⟩
            · rcases hsv with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl, -⟩
              · exact (htyC2 q hq).elim fun ty0 h0 => (hnt ty0 h0).elim
              · exact (htyC q hq).elim fun ty0 h0 => (hnt ty0 h0).elim
            · exact hcore.alike x (scopeAfter_sub S ess hx) hv n (hn4 x n hn) hnt w w'
                (hprojL x hv ▸ h1) (hFn ▸ h2) ty hty
        · obtain ⟨m, -, -, -, hcls⟩ := (e.rtxCls ht hs hns hcp6 k').2
          rcases hcls i n v xB h with ⟨i', h'⟩ | ⟨-, h'⟩ | ⟨p, hp, ⟨⟩⟩ | ⟨hK', -, -⟩
          · exact hs.armT.sel e.hF hCF hC1 hdT h' (hcfT _ _ _ _ _ h')
          · exact hs.armE.sel e.hF hCF hCE' hFE h' (hbelow k' _ n v xB hk h')
          · exact selIs_gm e.hF hCF hgmF _ _
          · cases hK.symm.trans hK'
            omega
      · rename_i ht4
        simp [hl4, hlt] at ht4
    · rename_i hlt
      split at hlabE
      · rename_i t' ht4
        simp [hl4, hlt] at ht4
      · exact hsnF none hlabE

end PartsAx1

end -- public section

end WP
end Imperative

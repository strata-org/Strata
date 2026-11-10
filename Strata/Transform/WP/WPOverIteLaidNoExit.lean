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

/-! # The simulation through a laid-out `ite` no arm of which always exits

When no arm of a laid-out `ite` always exits (`LaidEnv`), its output is the guard followed by the
parts `laidParts`.  A run of the `ite` along its then arm (`LaidEnv.runThen`) or its else arm
(`LaidEnv.runElse`), or with an empty output (`LaidEnv.runNil`), is matched by a run of the
output, and every shadow run off the path is matched by a run of the output (`LaidEnv.offAll`),
from the setting `LaidCore` and `LaidStates`.

Key theorems: `LaidEnv.runThen`, `LaidEnv.runElse`, `LaidEnv.runNil`, `LaidEnv.offAll`. -/

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

section Parts2b

variable {nonnil : Prop}
  (e : LaidEnv F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
    Ex k Lab wc rdc s1 g s2 rT s3 κE rE? s4
    Er s5 Tr s6 sv cp rs cps s7 gm? s8 cr)
  (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 (interSet Tr.A Er.R) sv cp
    rs cps s7 gm? st' rdc nonnil)
include e hs
omit iOp iLF iLFs iLV

/-- A variable of the context is no current name, at the walk output of the `ite`, of a variable
    in scope. -/
private theorem LaidEnv.re_curNotκ {z : P.Ident} (hz : z ∈ S)
    (hzn : curName st' z = some n) : n ∉ RE.vars κ := fun hy => (e.of_ctxNe hs hy).2.2.1 z hz hzn

/-- The else arm neither assigns nor declares a variable of the context. -/
private theorem LaidEnv.re_κNotE {y : P.Ident} (hy : y ∈ RE.vars κ) :
    Er.A.contains y = false ∧ y ∉ wDecls Er.out.toList := by
  obtain ⟨-, hE, hS, -⟩ := e.of_ctxNe hs hy
  exact ⟨hs.armE.notA (fun z hz h => hS z hz (hs.cur5 hz h).1) hE, hE⟩

/-- A current name of a variable in scope at the walk output of a laid-out `ite` is neither a
    prelude name nor drawn after the arms, nor declared by either arm. -/
private theorem LaidEnv.rt_curNe {z : P.Ident} (hz : z ∈ S) (hzn : curName st' z = some n) :
    ¬ ((n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) ∧ n ∉ wDecls Tr.out.toList ∧
      n ∉ wDecls Er.out.toList := by
  refine ⟨fun hn => ?_, fun hD => hs.armT.declNotCur n hD z hz ((hs.cur6 z).trans hzn),
    fun hD => e.re_EdeclNotM hs hD hz hzn⟩
  obtain ⟨b, j, hnb, hnav, -⟩ := hs.preOrLate hn
  rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
  · exact hn.elim (fun hn => (hs.preNm hn z).2.2.2 hm)
      fun hn => hn.elim fun b' ⟨j', h1, _, h2, _⟩ => hs.lateNm ⟨b', j', h1, h2⟩ z hm
  · simp [e.avoidS _ (List.mem_append_left _ hz) b j hnb] at hnav

/-- A name the then arm declares is neither assigned nor declared by the else arm, is no
    current name of a variable in scope, no prelude name, no name drawn after the arms and no
    variable of the context. -/
private theorem LaidEnv.re_TdeclFacts (hn : n ∈ wDecls Tr.out.toList) :
    Er.A.contains n = false ∧ n ∉ wDecls Er.out.toList ∧ (∀ z ∈ S, curName st' z ≠ some n) ∧
      (∀ x, (x = g ∨ x = rT ∨ rE? = some x) → n ≠ x) ∧ (∀ m, Drawn s6 st' m → n ≠ m) ∧
      n ∉ RE.vars κ := by
  have hE : n ∉ wDecls Er.out.toList := fun hE => e.dl_declDisj hs hn hE
  have hS : ∀ z ∈ S, curName st' z ≠ some n := fun z hz h =>
    hs.armT.declNotCur n hn z hz ((hs.cur6 z).trans h)
  exact ⟨hs.armE.notA (fun z hz h => hS z hz (hs.cur5 hz h).1) hE, hE, hS,
    fun x hx he => (e.notT hs (.inl (he ▸ hx))).2 hn,
    fun m hm he => (e.notT hs (.inr (he ▸ hm))).2 hn, fun hy => (e.of_ctxNe hs hy).1 hn⟩

/-- A variable of the context of a laid-out `ite` is no current name of a variable in scope at
    the arms' walk states, and neither arm assigns or declares it. -/
private theorem LaidEnv.rt_kvar {y : P.Ident} (hy : y ∈ RE.vars κ) :
    (∀ z ∈ S, curName s5 z ≠ some y ∧ curName s6 z ≠ some y ∧ curName st' z ≠ some y) ∧
    Tr.A.contains y = false ∧ y ∉ wDecls Tr.out.toList ∧ y ∉ wDecls Er.out.toList := by
  obtain ⟨hT, hE, hS, -⟩ := e.of_ctxNe hs hy
  have h6 : ∀ z ∈ S, curName s6 z ≠ some y := fun z hz h => hS z hz ((hs.cur6 z).symm.trans h)
  exact ⟨fun z hz => ⟨fun h => hS z hz (hs.cur5 hz h).1, h6 z hz, hS z hz⟩, hs.armT.notA h6 hT,
    hT, hE⟩

include iOp iLF in
/-- After the then arm of a laid-out `ite` ran (on or off its path, from the prelude store `σB`
    with guard value `gv` to `σ1`), the copies and the restores run: each copy holds its
    variable's value at the then arm's end, each saved variable is back to its value before the
    `ite`, every other name keeps its value, the copies are unbound at the then arm's end, the
    guard holds `gv`, the context's variables keep their values before the `ite` and the
    else-arm reach is unbound and differs from the saved variables and the copies. -/
private theorem LaidEnv.ry_midRun
    (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hfrL : FreshInv Lc Ex st' σL) (hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hB : PreStore F σL σB (g :: ((if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then []
      else [rT]) ++ gm?.toList)) gv ns []) (hC1 : WellFormedStore σ1 F)
    (hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hmono1 : ∀ n, (σB n).isSome → (σ1 n).isSome)
    (hch : ∀ n, σ1 n ≠ σB n → Wr0 (Block.idents tss) s5 s6 n ∨ n = rT) {iCP iRS : List (Item P)}
    (hCP : resolveItems T Y cp.toList = .ok iCP) (hRS : resolveItems T Y rs.toList = .ok iRS) :
    ∃ σR, MainRun F (iCP ++ iRS) σ1 [] σR ∧ WellFormedStore σR F ∧
      (∀ q ∈ ns, σR q.2.2 = σ1 q.1) ∧ (∀ q ∈ ns, σR q.1 = σL q.1) ∧
      (∀ n, (∀ q ∈ ns, n ≠ q.1 ∧ n ≠ q.2.2) → σR n = σ1 n) ∧
      (∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty) ∧ (∀ q ∈ ns, σ1 q.2.2 = none) ∧
      σR g = some gv ∧ (∀ y ∈ RE.vars κ, σR y = σL y) ∧
      ∀ x, rE? = some x → σR x = none ∧ ∀ q ∈ ns, x ≠ q.1 ∧ x ≠ q.2.2 := by
  have hnx := hs.nexts
  have hd : ∀ q ∈ ns, Drawn s6 st' q.2.1 ∧ Drawn s6 st' q.2.2 := fun q hq =>
    ⟨(hns.drawn q hq).1.mono hs.aft.next, (hns.drawn q hq).2.1.mono hs.aft.next⟩
  have hq1 : ∀ q ∈ ns, ∃ z ∈ S, curName st' z = some q.1 := fun q hq =>
    (e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)).imp fun _ ⟨hz, _, h⟩ => ⟨hz, h⟩
  have hc1 : ∀ q ∈ ns, ¬ ((q.1 = g ∨ q.1 = rT ∨ rE? = some q.1) ∨ Drawn s6 st' q.1) :=
    fun q hq => let ⟨z, hz, h⟩ := hq1 q hq; (e.rt_curNe hs hz h).1
  have h1B : ∀ n, ((n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) → n ≠ rT → σ1 n = σB n :=
    fun n hn hr => Classical.byContradiction fun hne => (hch n hne).elim (e.notWT hs hn) hr
  have hBL : ∀ n, n ≠ g → n ≠ rT → (∀ x, gm? = some x → n ≠ x) → (∀ q ∈ ns, n ≠ q.2.1) →
      σB n = σL n := fun n hg hr hgm hp => hB.2.2.1 n nofun (notin_pre hg hr hgm) hp
  have hgmD : ∀ x, gm? = some x → Drawn s6 st' x := fun x hx =>
    (hs.aft.gmDrawn x hx).of_le (by rw [hns.eq]) hnx.2.2.2.2.1
  have hcp0 : ∀ q ∈ ns, σ1 q.2.2 = none := fun q hq => by
    obtain ⟨hg, hr, hgm, -⟩ := hs.saveNe (hns.drawn q hq).2.1
    rw [h1B _ (.inr (hd q hq).2) hr,
      hBL _ hg hr hgm fun p hp => (flat_ne ns hns.nodup p hp q hq).symm]
    exact e.unbound hs hfrL (.inr (hd q hq).2)
  have hsrc1 : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq => by
    obtain ⟨w0, hw0, -⟩ := hsrcS q hq
    have hsB : σB q.1 = σL q.1 := hBL _ (fun h => hc1 q hq (.inl (.inl h)))
      (fun h => hc1 q hq (.inl (.inr (.inl h)))) (fun x hx h => hc1 q hq (.inr (h ▸ hgmD x hx)))
      fun p hp h => hc1 q hq (.inr (h ▸ (hd p hp).1))
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hmono1 q.1 (by simp [hsB, hw0]))
    exact (hq1 q hq).elim fun z ⟨hz, hzn⟩ => ⟨w, hw, hgt1 _ w hw (e.curY hs hz hzn)⟩
  have hsv : ∀ q ∈ ns, σ1 q.2.1 = σL q.1 := fun q hq =>
    (h1B _ (.inr (hd q hq).1) (hs.saveNe (hns.drawn q hq).1).2.1).trans (hB.2.1 q hq)
  obtain ⟨σC, σR, hrC, hrR, hCR, hcR, hvR, hRC, htyC⟩ := copyRestore e.hF hns
    (interSet_nodup _ _) hC1 hCP hRS hcp0 hsrc1
    (fun q hq => (hsrcS q hq).imp fun _ h => ⟨(hsv q hq).trans h.1, h.2⟩) fun q hq p hp =>
      ⟨fun h => hc1 q hq (.inr (h ▸ (hd p hp).1)), fun h => hc1 q hq (.inr (h ▸ (hd p hp).2))⟩
  have hgR : σR g = some gv := by
    rw [hRC g fun q hq => ⟨fun h => hc1 q hq (.inl (.inl h.symm)),
      fun h => (hs.saveNe (hns.drawn q hq).2.1).1 h.symm⟩, h1B g (.inl (.inl rfl)) hs.pre.g_rT]
    exact hB.1 g (List.mem_cons_self ..)
  have hκR : ∀ y ∈ RE.vars κ, σR y = σL y := fun y hy => by
    have hκd := (e.of_ctxNe hs hy).2.2.2
    have hpre : ∀ x, (x = g ∨ x = rT ∨ rE? = some x) → y ≠ x := fun x hx h =>
      hκd s1 s4 hnx.1 (h ▸ hs.pre.drawn x hx)
    rw [hRC y fun q hq => ⟨fun h => let ⟨z, hz, hzn⟩ := hq1 q hq; e.re_curNotκ hs hz hzn (h ▸ hy),
      fun h => hκd s6 s7 (by omega) (h ▸ (hns.drawn q hq).2.1)⟩]
    rw [Classical.byContradiction fun hne => (hch y hne).elim (e.notWTκ hs hy)
      (hpre rT (.inr (.inl rfl)))]
    exact hBL y (hpre g (.inl rfl)) (hpre rT (.inr (.inl rfl)))
      (fun x hx h => hκd s6 st' (by omega) (h ▸ hgmD x hx))
      fun q hq h => hκd s6 s7 (by omega) (h ▸ (hns.drawn q hq).1)
  have hrEd : ∀ x, rE? = some x → ∀ q ∈ ns, x ≠ q.1 ∧ x ≠ q.2.2 := fun x hx q hq =>
    ⟨fun h => hc1 q hq (.inl (.inr (.inr (h ▸ hx)))),
      fun h => (hs.saveNe (hns.drawn q hq).2.1).2.2.2 x hx h.symm⟩
  have h0R : ∀ x, rE? = some x → σR x = none := fun x hx => by
    obtain ⟨hxg, hxr⟩ := hs.pre.rE_ne x hx
    rw [hRC x (hrEd x hx), h1B x (.inl (.inr (.inr hx))) hxr,
      hBL x hxg hxr (fun y hy h => (hs.pre.drawn x (.inr (.inr hx))).disj (h ▸ hgmD y hy)
        (by omega)) fun q hq h => (hs.saveNe (hns.drawn q hq).1).2.2.2 x hx h.symm]
    exact e.unbound hs hfrL (.inl (.inr (.inr hx)))
  exact ⟨σR, hrC.append hrR, hCR, hcR, fun q hq => (hvR q hq).trans (hsv q hq), hRC, htyC, hcp0,
    hgR, hκR, fun x hx => ⟨h0R x hx, hrEd x hx⟩⟩

/-- After the then arm of a laid-out `ite` ran to `σ1` and the copies, the restores and the
    else-arm reach to `σD`, a store `σDv` agreeing with `σD` but binding the else-arm reach `rE`
    to a Boolean binds the current names at the else arm's walk input of the variables in scope
    it reads to values of their final types, holds values of their final types and binds no name
    the rest of the else arm's walk declares, the prelude names excepted. -/
private theorem LaidEnv.ry_elseFacts
    (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns) {σD σDv : SemanticStore P}
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hfr1 : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1)
    (hm1 : ∀ n, (σL n).isSome → (σ1 n).isSome) (hMD : ∀ q ∈ ns, σD q.1 = σL q.1)
    (hoth : ∀ n, (∀ q ∈ ns, n ≠ q.1 ∧ n ≠ q.2.2) → (∀ x, rE? = some x → n ≠ x) → σD n = σ1 n)
    (hDv : ∀ n, (∀ x, rE? = some x → n ≠ x) → σDv n = σD n) {bv : P.Val}
    (hbv : bv = HasBool.ttVal F ∨ bv = HasBool.ffVal F)
    (hDvrE : ∀ x, rE? = some x → σDv x = some bv) :
    (∀ x ∈ S, x ∈ contFV (ess :: ess :: k) → ∀ n, curName s5 x = some n →
      ∃ w, σDv n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty) ∧
    (∀ n w, σDv n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) ∧
    FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σDv := by
  have hnx := hs.nexts
  have hav := hs.avoids
  obtain ⟨-, -, -, -, -, -, hdr, -, -, -⟩ := hns
  have hY : ∀ q ∈ ns, Y[q.2.2]? = some q.1 := fun q hq => e.fin.2.1 _ _ (by
    rw [hs.aft.tyOf _ fun h => (hdr q hq).2.1.disj h (Nat.le_refl _)]
    exact (hdr q hq).2.2.2)
  have hval : ∀ n w, σDv n = some w → (∀ x, rE? = some x → n ≠ x) → (∀ q ∈ ns, n ≠ q.2.2) →
      σ1 n = some w ∨ ∃ q ∈ ns, n = q.1 ∧ σL q.1 = some w := fun n w hw hr hq => by
    rw [hDv n hr] at hw
    rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq', rfl⟩ | hn
    · exact .inr ⟨q, hq', rfl, (hMD q hq').symm.trans hw⟩
    · exact .inl ((hoth n (fun q hq' => ⟨fun h => hn ⟨q, hq', h⟩, hq q hq'⟩) hr).symm.trans hw)
  have hD : ∀ {sa sb : WSt P} {y : P.Ident}, sa.avoid = st0.avoid → Drawn sa sb y → y ∈ Lc →
      (∀ b j, y = freshName b j → s5.avoid.contains y = true) → s5.taken.contains y = false :=
    fun ha ⟨b, j, hb, hna, _, _⟩ _ hfa => absurd (hfa b j hb) (by rw [hav.2.2.1, ← ha]; simp [hna])
  refine ⟨fun x hx hv n hn => ?_, fun n w hw hYn ty hty => ?_, fun y hy => ?_⟩
  · have h' := (hs.cur5 hx hn).1
    obtain ⟨hpl, -, -⟩ := e.rt_curNe hs hx h'
    obtain ⟨w, hw⟩ :=
      Option.isSome_iff_exists.1 (hm1 n ((hon.defd x hx (contFV_else_sub hv)).2 n h'))
    have hr : ∀ x, rE? = some x → n ≠ x := fun x hx he => hpl (.inl (.inr (.inr (he ▸ hx))))
    rw [hDv n hr]
    rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hq
    · exact hMD q hq ▸ hsrcS q hq
    · rw [hoth n (fun q hq' => ⟨fun h => hq ⟨q, hq', h⟩,
        fun h => hpl (.inr (h ▸ (hdr q hq').2.1.mono hs.aft.next))⟩) hr]
      exact ⟨w, hw, hgt1 n w hw (e.curY hs hx h')⟩
  · rcases Classical.em (rE? = some n) with hr | hr
    · exact tyOfName_bool (e.preT hs (.inl (.inr (.inr hr))))
        (Option.some.inj ((hDvrE n hr).symm.trans hw) ▸ hbv) hty
    rcases hval n w hw (fun x hx he => hr (he ▸ hx)) fun q hq he => by simp [he, hY q hq] at hYn
      with h | ⟨q, hq, rfl, h⟩
    · exact hgt1 n w h hYn ty hty
    · obtain ⟨w', hw', hty'⟩ := hsrcS q hq
      exact Option.some.inj (hw'.symm.trans h) ▸ hty' ty hty
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hy
    rcases Classical.em (rE? = some y) with hr | hr
    · exact ⟨hD hav.1 (hs.pre.drawn y (.inr (.inr hr))),
        fun _ _ _ _ => .inr (.inr (.inr (.inr (.inr hr))))⟩
    rcases Classical.em (∃ q ∈ ns, y = q.2.2) with ⟨q, hq, rfl⟩ | hc
    · obtain ⟨b, j, hb, -, hj, -⟩ := (hdr q hq).2.1
      refine ⟨hD hav.2.2.2.1 (hdr q hq).2.1, fun b' j' hb' _ => .inl ?_⟩
      have hjj := freshName_counter_inj (hb'.symm.trans hb)
      omega
    have h1 : (σ1 y).isSome := by
      rcases hval y w hw (fun x hx he => hr (he ▸ hx)) fun q hq he => hc ⟨q, hq, he⟩ with
        h | ⟨q, hq, rfl, h⟩
      · simp [h]
      · exact hm1 _ (by simp [h])
    obtain ⟨p1, p2⟩ := hfr1 y h1
    exact ⟨p1, fun b j hb ha => (p2 b j hb ha).imp_right (.imp_right fun h =>
      h.imp_right (.imp_right .inl))⟩

/-- The carried merges at the walk output of a laid-out `ite` are those after its then arm. -/
private theorem LaidEnv.rt_carries (k : Nat) : st'.carries.getD k [] = s6.carries.getD k [] := by
  have h8 : s8.carries = s6.carries := by
    have h7 : s7.carries = s6.carries := by rw [hs.save.choose_spec.eq]
    rcases e.gm with ⟨-, x, -, hx⟩ | ⟨-, -, rfl⟩
    · exact (wFreshBool_facts hx).elim fun _ ⟨_, _, _, h⟩ => h ▸ h7
    · exact h7
  rcases e.out with ⟨-, -, rfl⟩ | ⟨-, -, -, -, hl⟩
  · exact (e.carries k).trans (h8 ▸ rfl)
  obtain ⟨live, clock, hrun, -⟩ := liveAdd_run (rdc ++ RE.vars κ) { s8 with carries := cr }
  exact (Prod.mk.inj (Except.ok.inj (hrun.symm.trans hl))).2 ▸ (e.carries k).trans (h8 ▸ rfl)

/-- The state before the arms of a laid-out `ite` keeps the current names, live set, clock and
    declared names of its walk input, and a guarded store binding no name the rest of the else
    arm's walk declares (prelude names excepted) binds no name the rest of the `ite`'s walk
    declares. -/
private theorem LaidEnv.rt_st0 :
    (∀ z ∈ S, ∀ n, curName st0 z = some n → curName s4 z = some n ∧ curName s5 z = some n ∧
      curName st' z = some n) ∧
    (∀ (n : P.Ident) (s : Nat), st0.live[n]? = some s → s4.live[n]? = some s) ∧
    s4.clock = st0.clock ∧ (∀ σE : SemanticStore P,
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 σE →
      FreshInv Lc Ex st0 σE) := by
  obtain ⟨-, -, h1, -⟩ := wRen_run e.run1
  refine ⟨fun z hz n h0 => e.of_cur0 hs hz h0, fun n s h => by rw [hs.pre.eq, h1]; exact h,
    by rw [hs.pre.eq, h1], fun σE hf => of_freshPost hf (fun y h => by
      rw [hs.pre.eq]; exact hs.c1.taken y h) hs.avoids.2.1 (Nat.le_trans hs.c1.next hs.pre.next)
      (fun x y h => hs.c1.nm x y (by rwa [hs.pre.eq] at h)) fun y hy =>
        hy.imp_right fun hp b j hj => ?_⟩
  obtain ⟨b', j', h1', -, h2, -⟩ := hs.pre.drawn y hp
  have hjj := freshName_counter_inj (hj.symm.trans h1')
  have hn1 := hs.c1.next
  omega

omit iLI iWL e hs in
/-- The reach update of a laid-out `ite` is not empty when the then arm's `minT` is at most the
    depth. -/
private theorem rx_Unn {κ' κE' : RE P} {rT' : P.Ident} {Tr' Er' : WRes P} {d' : Nat}
    (h : leOpt Tr'.minT d' = true) : (laidU κ' κE' rT' Tr' Er' d').isNil = false := by
  cases κ' <;> simp [laidU, h, setReach, Rope.isNil]

omit iLI e hs in
/-- A selector of a carried merge an arm registered keeps its value in a value-valued store
    agreeing with the arm's end store on the names the arm's output declares. -/
private theorem ArmFacts.sel {κ' : RE P} {d' : Nat} {sa sb : WSt P}
    {r' : WRes P} (ha : ArmFacts F Lc S κ' d' ss sa r' sb) (hF : WellFormedSemanticEvalBase F)
    {σA σF : SemanticStore P} (hCF : WellFormedStore σF F) (hCA : WellFormedStore σA F)
    (hk : ∀ n ∈ wDecls r'.out.toList, σF n = σA n) {k i : Nat} {v : WExpr P}
    {xB : P.Ident} {b : Bool} (hr : CarryReg r' sb k i n v xB) (hsel : SelIs F T Y σA v b) :
    SelIs F T Y σF v b := by
  obtain ⟨e, xB', x, rfl, e', he, hv⟩ := hsel
  exact ⟨e, xB', x, rfl, e', he, (ev_congr hF hCA hCF e' fun y hy =>
    (hk y (ha.carrySel T Y k i n _ xB hr _ _ _ rfl _ he y (mem_exprFV.2 hy))).symm).symm.trans hv⟩

/-- At each depth `k`, the carried merges of the laid-out `ite` are those its then arm
    registered, or those of its else arm at the index shifted by the number `m` of merges the
    then arm added at `k`. -/
private theorem LaidEnv.ry_regIdx (k : Nat) : ∃ m,
    (s6.carries.getD k []).length = m + (s5.carries.getD k []).length ∧
    (∀ i n v xB, CarryReg r st' k i n v xB →
      CarryReg Tr s6 k i n v xB ∨ m ≤ i ∧ CarryReg Er s5 k (i - m) n v xB) ∧
    ∀ i n v xB, CarryReg Er s5 k i n v xB → CarryReg r st' k (i + m) n v xB := by
  obtain ⟨new, hnew, hdr⟩ := hs.armT.carriesNew k
  refine ⟨new.length, by simp [hnew], fun i n v xB ⟨hi, hxB⟩ => ?_, fun i n v xB ⟨hi, hxB⟩ =>
    ⟨?_, e.regs ▸ List.mem_append_right _ hxB⟩⟩
  · rw [e.rt_carries hs] at hi
    rcases List.mem_append.1 (e.regs ▸ hxB) with hT | hE
    · exact .inl ⟨hi, hT⟩
    rw [hnew, List.getElem?_append] at hi
    split at hi
    · exact (e.regsE hs hE (hdr _ (List.mem_of_getElem? hi))).elim
    · exact .inr ⟨by omega, hi, hE⟩
  · rw [e.rt_carries hs, hnew, List.getElem?_append_right (by omega)]
    simpa using hi

/-- A carried merge the laid-out `ite` registered is one its then arm registered, or one its
    else arm registered (at another index). -/
private theorem LaidEnv.of_regCases {k i : Nat} {v : WExpr P} {xB : P.Ident}
    (h : CarryReg r st' k i n v xB) :
    CarryReg Tr s6 k i n v xB ∨ ∃ i', CarryReg Er s5 k i' n v xB :=
  let ⟨_, _, h1, _⟩ := e.ry_regIdx hs k
  (h1 i n v xB h).imp_right fun h => ⟨_, h.2⟩

/-- After the else arm ran on its path and the then arm off it, the carried merges the `ite`
    registered (those of its arms) are well formed in the final store `σF`, from the arms'
    `CarryOK`, when `σF` agrees with the arms' end stores on the names they declare, keeps
    their bindings and types the names without a type reference. -/
private theorem LaidEnv.ry_carryOK {σE' σF : SemanticStore P}
    (hcoT : CarryOK F T Y Tr s6 σ1) (hcoE : CarryOK F T Y Er s5 σE') (hCF : WellFormedStore σF F)
    (hC1 : WellFormedStore σ1 F) (hCE : WellFormedStore σE' F)
    (hkT : ∀ n ∈ wDecls Tr.out.toList, σF n = σ1 n) (hkE : ∀ n ∈ wDecls Er.out.toList, σF n = σE' n)
    (htyF : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hbT : ∀ z ∈ S, ∀ n, curName st' z = some n → (σ1 n).isSome → (σF n).isSome)
    (hbE : ∀ n, (∀ x, rE? = some x → n ≠ x) → (σE' n).isSome → (σF n).isSome) :
    CarryOK F T Y r st' σF := by
  intro k i n v xB hr
  rcases e.of_regCases hs hr with h | ⟨i', h⟩
  · obtain ⟨hsel, hty, ⟨w, hw, ht⟩, w', hw', ht'⟩ := hcoT _ _ _ _ _ h
    refine ⟨hsel.imp (hs.armT.sel e.hF hCF hC1 hkT h) (hs.armT.sel e.hF hCF hC1 hkT h), hty, ?_,
      w', (hkT _ (hs.armT.regs _ h.2)).trans hw', ht'⟩
    rcases hs.armT.carryTgt k i n v xB h with ⟨z, hz, hzn⟩ | hd
    · have h' := (hs.cur6 z).symm.trans hzn
      obtain ⟨w1, hw1⟩ := Option.isSome_iff_exists.1 (hbT z hz n h' (by simp [hw]))
      exact ⟨w1, hw1, htyF n w1 hw1 (e.curY hs hz h')⟩
    · exact ⟨w, (hkT n hd).trans hw, ht⟩
  · obtain ⟨hsel, hty, ⟨w, hw, ht⟩, w', hw', ht'⟩ := hcoE _ _ _ _ _ h
    refine ⟨hsel.imp (hs.armE.sel e.hF hCF hCE hkE h) (hs.armE.sel e.hF hCF hCE hkE h), hty, ?_,
      w', (hkE _ (hs.armE.regs _ h.2)).trans hw', ht'⟩
    rcases hs.armE.carryTgt _ _ n v xB h with ⟨z, hz, hzn⟩ | hd
    · have h' := (hs.cur5 hz hzn).1
      obtain ⟨w1, hw1⟩ := Option.isSome_iff_exists.1 (hbE n (fun x hx he =>
        (e.rt_curNe hs hz h').1 (.inl (.inr (.inr (he ▸ hx))))) (by simp [hw]))
      exact ⟨w1, hw1, htyF n w1 hw1 (e.curY hs hz h')⟩
    · exact ⟨w, (hkE n hd).trans hw, ht⟩

include iLV in
omit iDE iBE iLB iHF iSF iHI iLI iHa iWL e hs iHFs in
/-- A Boolean held at `n` by a store `σ'` has the type `ty` that the Boolean held at `n` by a
    store `σ0` has. -/
private theorem rn_boolTyped {F : P.Factory} {σ0 : SemanticStore P}
    {w : P.Val} {ty : P.Ty} (hb0 : σ0 n = some (HasBool.ttVal F) ∨ σ0 n = some (HasBool.ffVal F))
    (ht0 : ∀ w0, σ0 n = some w0 → HasVal.valueOfTy F w0 ty)
    (hb : σ' n = some (HasBool.ttVal F) ∨ σ' n = some (HasBool.ffVal F))
    (hw : σ' n = some w) : HasVal.valueOfTy F w ty := by
  rcases hb0 with h0 | h0 <;> rcases hb with h | h <;> cases hw.symm.trans h <;>
    exact LawfulHasVal.valueOfTy_congr F _ _ ty _ (ht0 _ h0) (bool_valueOfTy (by simp))
      (bool_valueOfTy (by simp))

/-- An else-arm registration pending at the walk output of a laid-out `ite` was pending after
    the else arm. -/
private theorem LaidEnv.pendE {l : String} {x : P.Ident} (hx : x ∈ Er.regs.toList)
    (hp : x ∈ st'.pending.getD l []) : x ∈ s5.pending.getD l [] :=
  (hs.armT.pendNew l x (hs.aft.pending ▸ hp)).resolve_right (e.regsE hs hx)

include iOp iLF iLV iIL in
/-- The merges and the reach update of a laid-out `ite` whose arms do not always exit run from a
    value-valued store `σE` binding each copy to the value `σ1` gives its saved variable, each
    saved variable and its copy to values of one type, the merge guard to the Boolean `b`,
    the variables of `κ` to Booleans and, when the update is emitted, `rT` to a Boolean, where
    `κE` holds or fails.  Let `xv` be the truth of `rT ∨ κE` in `σE`.  A live saved variable ends
    with its value in `σ1` when `b` is true or the else arm does not assign it, with its value in
    `σE` otherwise; every other name outside `κ` keeps its value, the variables of `κ` stay Boolean,
    and the context `q` of `κ = q ∧ ¬g` keeps its value; when the update is empty the run is
    empty and keeps `κ`; otherwise under `top` its trace is the assumption, feasible exactly
    when `xv`, and under a variable context it is empty and makes `κ` hold when `xv` (and, for
    `q ∧ ¬g`, `q` holds and differs from `g`) and fail otherwise. -/
private theorem LaidEnv.postRun (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns)
    (b : Bool) (hfrL : FreshInv Lc Ex st' σL) (hML : ∀ q ∈ ns, (σL q.1).isSome)
    (hCE : WellFormedStore σE F) (hcp : ∀ q ∈ ns, σE q.2.2 = σ1 q.1)
    (hty : ∀ q ∈ ns, ∃ ty w w', σ1 q.1 = some w ∧ σE q.1 = some w' ∧
      HasVal.valueOfTy F w ty ∧ HasVal.valueOfTy F w' ty)
    (hgm : ∀ x, gm? = some x → σE x = some (if b then HasBool.ttVal F else HasBool.ffVal F))
    (hrT : (laidU κ κE rT Tr Er d).isNil = false →
      σE rT = some (HasBool.ttVal F) ∨ σE rT = some (HasBool.ffVal F))
    (hκE : (laidU κ κE rT Tr Er d).isNil = false → κE.Holds F σE ∨ κE.Fails F σE)
    (hκEb : (laidU κ κE rT Tr Er d).isNil = false →
      ∀ y ∈ RE.vars κE, σE y = some (HasBool.ttVal F) ∨ σE y = some (HasBool.ffVal F))
    (hκb : ∀ y ∈ RE.vars κ, σE y = some (HasBool.ttVal F) ∨ σE y = some (HasBool.ffVal F))
    {iMG : List (Item P)}
    (hMG : resolveItems T Y
      (laidMerges gm? Er.A (cps.filter fun p => liveBefore s6 p.1 s4.clock)).toList = .ok iMG)
    (hU : resolveItems T Y (laidU κ κE rT Tr Er d).toList = .ok iU) :
    ∃ trU σF, MainRun F (iMG ++ iU) σE trU σF ∧ WellFormedStore σF F ∧
      (∀ q ∈ ns, liveBefore s6 q.1 s4.clock = true →
        σF q.1 = if b ∨ Er.A.contains q.1 = false then σ1 q.1 else σE q.1) ∧
      (∀ n, (∀ q ∈ ns, liveBefore s6 q.1 s4.clock = true → n ≠ q.1) → n ∉ RE.vars κ →
        σF n = σE n) ∧
      (∀ y ∈ RE.vars κ, σF y = some (HasBool.ttVal F) ∨ σF y = some (HasBool.ffVal F)) ∧
      (∀ q g', κ = .andNeg q g' → q ≠ g' → σF q = σE q) ∧
      ((laidU κ κE rT Tr Er d).isNil = true → trU = [] ∧ ∀ y ∈ RE.vars κ, σF y = σE y) ∧
      ((laidU κ κE rT Tr Er d).isNil = false →
        (κ = .top → (Trace.AssumptionsHold P evalInterp () trU ↔
          (σE rT = some (HasBool.ttVal F) ∨ κE.Holds F σE))) ∧
        (κ ≠ .top → trU = [] ∧
          ((σE rT = some (HasBool.ttVal F) ∨ κE.Holds F σE) →
            (∀ q g, κ = .andNeg q g → σE q = some (HasBool.ttVal F) ∧ q ≠ g) →
            κ.Holds F σF) ∧
          (¬ (σE rT = some (HasBool.ttVal F) ∨ κE.Holds F σE) → κ.Fails F σF))) := by
  have hmem : ∀ p ∈ cps.filter fun p => liveBefore s6 p.1 s4.clock, ∃ q ∈ ns, p = (q.1, q.2.2) :=
    fun p hp => hns.mem_pairs.1 p (List.mem_filter.1 hp).1
  have hnd := ((List.filter_sublist (p := fun p => liveBefore s6 p.1 s4.clock) (l := cps)).map
    (·.1)).nodup (hns.mem_pairs.2 (interSet_nodup _ _))
  have hnames : ∀ n ∈ (cps.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1),
      ∃ q ∈ ns, n = q.1 ∧ liveBefore s6 q.1 s4.clock = true := fun n hn => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
    obtain ⟨q, hq, rfl⟩ := hmem p hp
    exact ⟨q, hq, rfl, (List.mem_filter.1 hp).2⟩
  have hin : ∀ q ∈ ns, liveBefore s6 q.1 s4.clock = true →
      (q.1, q.2.2) ∈ cps.filter fun p => liveBefore s6 p.1 s4.clock := fun q hq hl =>
    List.mem_filter.2 ⟨hns.pairs ▸ List.mem_reverse.2 (List.mem_map.2 ⟨q, hq, rfl⟩), hl⟩
  have hnot : ∀ n, (σL n = none ∨ n ∈ RE.vars κ) →
      n ∉ (cps.filter fun p => liveBefore s6 p.1 s4.clock).map (·.1) := fun n hn hm => by
    obtain ⟨q, hq, rfl, -⟩ := hnames n hm
    obtain ⟨z, hz, -, hzn⟩ := e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)
    exact hn.elim (Option.isSome_iff_ne_none.1 (hML q hq)) fun h => (e.of_ctxNe hs h).2.2.1 z hz hzn
  obtain ⟨σM, hrunM, hCM, hvalM, hothM⟩ := run_merges e.hF gm? Er.A _ σE iMG hMG hCE hnd
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hmem p hp
      exact hnot _ (.inl (e.unbound hs hfrL (.inr ((hns.drawn q hq).2.1.mono hs.nexts.2.2.2.2.2)))))
    (fun x hx => ⟨by cases b <;> first | exact .inl (hgm x hx) | exact .inr (hgm x hx),
      hnot x (.inl (e.preUnbound hs hns hfrL (.inl (by simp [hx]))))⟩)
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := hmem p hp
      obtain ⟨ty, w, w', hw, hw', ht, ht'⟩ := hty q hq
      exact ⟨w', w, ty, hw', (hcp q hq).trans hw, ht', ht⟩)
  have hoth : ∀ n, (σL n = none ∨ n ∈ RE.vars κ) → σM n = σE n := fun n hn => hothM n (hnot n hn)
  have hκM : ∀ y ∈ RE.vars κ, σM y = σE y := fun y hy => hoth y (.inr hy)
  have hκEM : ∀ y ∈ RE.vars κE, σM y = σE y := fun y hy => hoth y <|
    (e.of_κEvars' hy).elim (fun h => .inl (e.unbound hs hfrL (.inl (.inl h)))) fun h =>
      h.elim (fun h => .inl (e.unbound hs hfrL (.inl (.inr (.inr h))))) .inr
  have hrTM : σM rT = σE rT := hoth rT (.inl (e.unbound hs hfrL (.inl (.inr (.inl rfl)))))
  have hval : ∀ q ∈ ns, liveBefore s6 q.1 s4.clock = true →
      σM q.1 = if b ∨ Er.A.contains q.1 = false then σ1 q.1 else σE q.1 := fun q hq hl => by
    rw [hvalM _ (hin q hq hl)]
    unfold mergeVal
    by_cases hA : Er.A.contains q.1 = true
    · obtain ⟨y, hy⟩ : ∃ y, gm? = some y := e.gm.elim (fun ⟨_, x, hx, _⟩ => ⟨x, hx⟩)
        fun ⟨hany, _, _⟩ => by simpa [hA] using List.any_eq_false.1 hany _ (hin q hq hl)
      cases b <;> simp [hy, hgm y hy, hA, (HasBool.ttVal_ne_ffVal F).symm, hcp q hq]
    · simp [hA, hcp q hq]
  have hothL : ∀ n, (∀ q ∈ ns, liveBefore s6 q.1 s4.clock = true → n ≠ q.1) → σM n = σE n :=
    fun n hn => hothM n fun hm => (hnames n hm).elim fun q ⟨hq, he, hl⟩ => hn q hq hl he
  by_cases hUn : (laidU κ κE rT Tr Er d).isNil = true
  · obtain rfl : iU = [] := resolve_isNil hUn hU
    refine ⟨[], σM, by simpa using hrunM, hCM, hval, fun n hn _ => hothL n hn,
      fun y hy => hκM y hy ▸ hκb y hy, fun q g' hq _ => hκM q (by simp [hq, RE.vars]),
      fun _ => ⟨rfl, hκM⟩, fun h => by simp [hUn] at h⟩
  have hUf : (laidU κ κE rT Tr Er d).isNil = false := Bool.eq_false_iff.2 hUn
  obtain ⟨trU, σF, hrunU, hCF, hothU, hbU, -, hnU, hkU⟩ := run_U e.hF hU hCM (hrTM ▸ hrT hUf)
    ((hκE hUf).imp (·.congr hκEM) (of_failsCongr · hκEM)) (fun y hy => hκM y hy ▸ hκb y hy)
    fun y hy => hκEM y hy ▸ hκEb hUf y hy
  have hX : (σM rT = some (HasBool.ttVal F) ∨ κE.Holds F σM) ↔
      (σE rT = some (HasBool.ttVal F) ∨ κE.Holds F σE) := by
    exact hrTM ▸ or_congr_right ⟨(·.congr fun y hy => (hκEM y hy).symm), (·.congr hκEM)⟩
  refine ⟨[] ++ trU, σF, hrunM.append hrunU, hCF, fun q hq hl => ?_, fun n hn hk => ?_, hbU,
    fun q g' hq hne => ?_, fun h => by simp [hUf] at h, fun _ => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · rw [hothU _ fun hk => hnot _ (.inr hk) (List.mem_map.2 ⟨_, hin q hq hl, rfl⟩), hval q hq hl]
  · rw [hothU n hk, hothL n hn]
  · rw [hkU q g' hq q hne, hκM q (by simp [hq, RE.vars])]
  · simpa [← hX] using ((hnU hUf).1 ht)
  · obtain ⟨h1, h2, h3⟩ := (hnU hUf).2 ht
    exact ⟨by simpa using h1, fun hx hq => h2 (hX.2 hx) fun q g hqg => by
      rw [hκM q (by simp [hqg, RE.vars])]
      exact hq q g hqg, fun hx => h3 (hx ∘ hX.1)⟩

include iOp iLF iLFs iLV in
omit hs in
include iIL in
/-- On the then path of a laid-out `ite` with a nonempty body (the context holding, the
    condition true), a feasible loop-free run of the then arm (with the else arm's shadow run
    `hsh`) is a feasible run of the output establishing `RunPost`, unless it exits under `top`. -/
private theorem LaidEnv.runThen (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hnn : (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr
      Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false)
    (hc : P.eval F σ c = some (HasBool.ttVal F))
    (hT' : DRun F (fun o' => X (o'.proj σ)) tss σ evs oT)
    (hsh : ShB F ess σ (VirtK oT fun o' => X (o'.proj σ)))
    (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    (κ = .top ∧ ∃ l σ1, oT.proj σ = .exit l σ1) ∨
    ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL' (oT.proj σ) := by
  have hs := e.states
  obtain ⟨ce, iRT, iGM, iSV, iT, iCP, iRS, iRE, iE, iMG, iU, hsp⟩ := e.split hnn
  obtain ⟨hce, hRT, hGM, hSV, hT, hCP, hRS, hRE, hE, hMG, hU, hitems⟩ := hsp
  have hsrcS := e.savedOn hs hon hns
  obtain ⟨σB, hrun0, hCB, hB, -⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM (iQM := [])
    (qm? := none) (by cases κ <;> simp only [Rope.toList_nil] <;> rfl) nofun nofun hSV
    (e.guardOn hs hon hnn hs.aft.liveC hc (.inl rfl) hce) (.inl rfl) hsrcS
  obtain ⟨trT, σT', σ1, hrunT, hfT, hpost, h1T, h1rT, hch, hrTe⟩ : ∃ trT σT' σ1,
      MainRun F iT σB trT σ1 ∧ Trace.AssumptionsHold P evalInterp () trT ∧
      RunPost F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) Lab s5 s6 Tr (.name rT) S
        (scopeAfter S tss) (contFV (ess :: k)) (fun o' => X (o'.proj σ)) σT' oT ∧
      (∀ n, n ≠ rT → σ1 n = σT' n) ∧ (σ1 rT = none ∨ σ1 rT = σT' rT) ∧
      (∀ n, σ1 n ≠ σB n → Wr0 (Block.idents tss) s5 s6 n ∨ n = rT) ∧
      ((Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = false → σ1 rT = σT' rT) := by
    obtain ⟨hrgm, hrsv, hrg⟩ := hs.rTFacts hns
    cases hb : (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil)
    · obtain ⟨tr, σL', hrun, hfe, hpost⟩ := (e.armTp hs hT).2.1 σ σB _ evs oT
        (e.thenT hs hns hon (ext := []) (by simpa [hb, laidQm] using hB) nofun nofun hCB) hT' hfeas
      refine ⟨tr, σL', σL', hrun, hfe, hpost, fun _ _ => rfl, .inr rfl, fun n hn => ?_,
        fun _ => rfl⟩
      exact (hs.armT.writesW T Y iT hT σB tr σL' hrun n hn).imp_right fun h =>
        (Option.some.inj h).symm
    · have hB2 : PreStore F σL σB (g :: gm?.toList) (HasBool.ttVal F) ns [] := by
        simpa [hb, laidQm] using hB
      obtain rfl := resolve_isNil (Bool.and_eq_true_iff.1 hb).1 hT
      obtain ⟨tr, σL', hrun, hfe, hpost⟩ := (e.armTp hs hT).2.1 σ _ _ evs oT
        (e.thenT hs hns hon (hB2.add hrsv nofun) nofun nofun
          (wfStore_update_bool hCB rT (.inl rfl))) hT' hfeas
      cases hrun
      have hr0 : σB rT = none := (hB2.2.2.1 rT nofun (by simpa [hrg] using fun h => hrgm rT h rfl)
        hrsv).trans (e.preUnbound hs hns hon.fresh (.inl (by simp)))
      exact ⟨[], _, σB, .nil, hfe, hpost,
        fun n hn => ((update_facts σB rT (HasBool.ttVal F)).2 n (Ne.symm hn)).symm, .inl hr0,
        fun n hn => absurd rfl hn, nofun⟩
  cases oT
  case' normal σT =>
    refine .inr ?_
    obtain ⟨hOT, hsnT, hcfT, hcoT, -, -, hexT⟩ := hpost
  case' exit l σx =>
    by_cases htop : κ = .top
    · exact .inl ⟨htop, l, _, rfl⟩
    refine .inr ?_
    have hUf : (laidU κ κE rT Tr Er d).isNil = false := rx_Unn (hs.armT.exitMin
      (fun l' t h => (e.lab l' t ((e.labels hs l').2 ▸ h)).1) _ σ evs l σx hT')
    obtain ⟨hOT, hshT, -, hcoT, hlabT⟩ := hpost
  all_goals
    have hnx := hs.nexts
    have hsub : ∀ n w, σ1 n = some w → σT' n = some w := fun n w hw => by
      by_cases hn : n = rT
      · exact h1rT.elim (fun h => by simp [hn, h] at hw) fun h => by subst hn; exact h ▸ hw
      · rwa [← h1T n hn]
    have hC1 : WellFormedStore σ1 F := fun n w hw => hOT.canonL n w (hsub n w hw)
    have hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun n w hw => hOT.gtyped n w (hsub n w hw)
    have hfr1 : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1 := fun y hy => by
      exact (Option.isSome_iff_exists.1 hy).elim fun w hw => hOT.fresh y (by rw [hsub y w hw]; rfl)
    have hm1B := mainRun_mono hrunT
    have hneL : ∀ m n, (σL m).isSome → σL n = none → m ≠ n := fun m n hm hn he => by
      simp [he, hn] at hm
    have hrTL : σL rT = none := e.preUnbound hs hns hon.fresh (.inl (by simp))
    have hgL : σL g = none := e.preUnbound hs hns hon.fresh (.inl (by simp))
    have hBL : ∀ n, (σL n).isSome → σB n = σL n := fun n hn =>
      hB.2.2.1 n nofun (notin_pre (hneL _ _ hn hgL) (hneL _ _ hn hrTL) fun x hx =>
        hneL _ _ hn (e.preUnbound hs hns hon.fresh (.inl (by simp [hx])))) fun q hq =>
        hneL _ _ hn (e.preUnbound hs hns hon.fresh (.inr ⟨q, hq, rfl⟩))
    have hm1 : ∀ n, (σL n).isSome → (σ1 n).isSome := fun n hn => hm1B n (by rw [hBL n hn]; exact hn)
    obtain ⟨σD, hrunD, hCD, hcpD, hMD, hothD, hrED, htyC, hgD⟩ :
        ∃ σD, MainRun F (iCP ++ (iRS ++ iRE)) σ1 [] σD ∧ WellFormedStore σD F ∧
        (∀ q ∈ ns, σD q.2.2 = σ1 q.1) ∧ (∀ q ∈ ns, σD q.1 = σL q.1) ∧
        (∀ n, (∀ q ∈ ns, n ≠ q.1 ∧ n ≠ q.2.2) → (∀ x, rE? = some x → n ≠ x) → σD n = σ1 n) ∧
        (∀ x, rE? = some x →
          (σD x = some (HasBool.ffVal F) ∧
            (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil) = false) ∨
            (σD x = none ∧ (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true)) ∧
        (∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty) ∧ σD g = some (HasBool.ttVal F) := by
      obtain ⟨σR, hrR, hCR, hcR, hvR, hoR, htyR, -, hgR, hκR, h0R⟩ :=
        e.ry_midRun hs hns hon.fresh hsrcS hB hC1 hgt1 hm1B hch hCP hRS
      obtain ⟨σD, hrD, hCD, hcase⟩ :=
        rEiRun e.hF hCR (fun x hx => (h0R x hx).1) (.inr (.inr ⟨hon.reach.congr hκR, hgR, rfl⟩)) hRE
      have hDR : ∀ n, (∀ x, rE? = some x → n ≠ x) → σD n = σR n := fun n hn => by
        rcases hcase with ⟨-, rfl, -⟩ | ⟨x, hx, -, rfl⟩
        · rfl
        · exact (update_facts σR x (HasBool.ffVal F)).2 n (Ne.symm (hn x hx))
      refine ⟨σD, List.append_assoc .. ▸ hrR.append hrD, hCD,
        fun q hq => (hDR _ fun x hx h => ((h0R x hx).2 q hq).2 h.symm).trans (hcR q hq),
        fun q hq => (hDR _ fun x hx h => ((h0R x hx).2 q hq).1 h.symm).trans (hvR q hq),
        fun n hn hx => (hDR n hx).trans (hoR n hn), fun x hx => ?_, htyR,
        (hDR g fun x hx => (hs.pre.rE_ne x hx).1.symm).trans hgR⟩
      rcases hcase with ⟨-, rfl, h | h⟩ | ⟨x', hx', hb, rfl⟩
      · simp [h] at hx
      · exact .inr ⟨(h0R x hx).1, h⟩
      · exact .inl ⟨Option.some.inj (hx.symm.trans hx') ▸
          (update_facts σR x (HasBool.ffVal F)).1, hb⟩
    have hrEL : ∀ x, rE? = some x → σL x = none := fun x hx =>
      e.unbound hs hon.fresh (.inl (.inr (.inr hx)))
    have hMz : ∀ q ∈ ns, ∃ z ∈ S, z ∈ Block.freeVars ess ∧ curName st' z = some q.1 := fun q hq =>
      e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)
    have hML : ∀ q ∈ ns, (σL q.1).isSome := fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]
    have hcpL : ∀ q ∈ ns, σL q.2.2 = none := fun q hq =>
      e.unbound hs hon.fresh (.inr ((hns.drawn q hq).2.1.mono hnx.2.2.2.2.2))
    have hκne : ∀ y ∈ RE.vars κ, ∀ q ∈ ns, y ≠ q.1 := fun y hy q hq he => by
      exact (hMz q hq).elim fun z ⟨hz, _, hzn⟩ => ((e.rt_kvar hs hy).1 z hz).2.2 (he ▸ hzn)
    have hκ1 : ∀ y ∈ RE.vars κ, σ1 y = σL y := fun y hy => by
      have hyL := hon.reach.bound y hy
      exact (Classical.byContradiction fun hne =>
        (hch y hne).elim (e.notWTκ hs hy) (hneL y rT hyL hrTL)).trans (hBL y hyL)
    have hκD : ∀ y ∈ RE.vars κ, σD y = σL y := fun y hy => by
      have hyL := hon.reach.bound y hy
      rw [hothD y (fun q hq => ⟨hκne y hy q hq, hneL _ _ hyL (hcpL q hq)⟩)
        (fun x hx => hneL _ _ hyL (hrEL x hx)), hκ1 y hy]
    have hAE : ∀ {K : Outcome P → Prop}, ShL F ess σ K →
        ∃ trE σEv σE, MainRun F iE σD trE σE ∧ Trace.AssumptionsHold P evalInterp () trE ∧
        OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 κE
          (if Er.ax then S else scopeAfter S ess) (contFV (ess :: k)) σEv ∧
        (∀ n, (σD n).isSome → n ∉ RE.vars κE → σEv n = σD n) ∧
        SnapFF F Er s5 none σEv ∧ CarryFF F T Y Er s5 σEv ∧ CarryOK F T Y Er s5 σEv ∧
        ShEnds Er s5 none K ∧ (∀ n, (∀ x, rE? = some x → n ≠ x) → σE n = σEv n) ∧
        (∀ x, rE? = some x → σE x = σEv x ∨
          (σE x = none ∧ (laidU κ κE rT Tr Er d).isNil = true)) := fun hsh => by
      obtain ⟨σDv, hDv, hDvrE, hCDv⟩ : ∃ σDv : SemanticStore P,
          (∀ n, (∀ x, rE? = some x → n ≠ x) → σDv n = σD n) ∧
          (∀ x, rE? = some x → σDv x = some (HasBool.ffVal F)) ∧ WellFormedStore σDv F := by
        refine ⟨fun n => if rE? = some n then some (HasBool.ffVal F) else σD n,
          fun n h => ite_eq_right fun h' => h n h' rfl, fun x h => ite_eq_left h, fun x v hv => ?_⟩
        dsimp only at hv
        split at hv
        · exact Option.some.inj hv ▸ (HasBool.boolIsVal F).2
        · exact hCD x v hv
      obtain ⟨hdefd, hgtD, hfrD⟩ :=
        e.ry_elseFacts hs hns hon hsrcS hgt1 hfr1 hm1 hMD hothD hDv (.inr rfl) hDvrE
      have hgDv : rE? = none → σDv g = some (HasBool.ttVal F) :=
        fun h => (hDv g (by simp [h])).trans hgD
      obtain ⟨hreach, hbools⟩ :
          κE.Fails F σDv ∧ ∀ y ∈ RE.vars κE,
            σDv y = some (HasBool.ttVal F) ∨ σDv y = some (HasBool.ffVal F) := by
        rcases LaidCtx.cases' e.ctx with ⟨h0, rfl | ⟨q, rfl, rfl⟩⟩ | ⟨x, rfl, rfl⟩
        · simp [RE.Fails, RE.vars, hgDv h0]
        · have hq : σDv q = some (HasBool.ttVal F) :=
            (hDv q (by simp [h0])).trans (hon.reach.congr hκD)
          simp [RE.Fails, RE.vars, hgDv h0, hq]
        · simp [RE.Fails, RE.vars, hDvrE x rfl]
      obtain ⟨tr, σL', hrun, hfe, hoffP, hfr, hsn, hcf, hco, hse⟩ := (e.armEp hs hE).2.2 σ σDv _
        ⟨hCDv, hreach, hbools, hdefd, hgtD, hfrD⟩ hsh
      cases hb : (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil)
      · obtain rfl : σDv = σD := funext fun n => (Classical.em (rE? = some n)).elim
          (fun h => (hDvrE n h).trans
            ((hrED n h).resolve_right fun h' => by simp [hb] at h').1.symm)
          fun h => hDv n fun x hx he => h (he ▸ hx)
        exact ⟨tr, σL', σL', hrun, hfe, hoffP, hfr, hsn, hcf, hco, hse, fun _ _ => rfl,
          fun _ _ => .inl rfl⟩
      · obtain ⟨hEn, hUn⟩ := Bool.and_eq_true_iff.1 hb
        obtain rfl := resolve_isNil hEn hE
        have h0 : ∀ x, rE? = some x → σD x = none := fun x h =>
          ((hrED x h).resolve_left fun h' => by simp [hb] at h').1
        cases hrun
        exact ⟨[], σDv, σD, .nil, hfe, hoffP,
          fun n hn _ => hDv n fun x hx he => (by simp [he, h0 x hx] at hn), hsn, hcf, hco, hse,
          fun n h => (hDv n h).symm, fun x h => .inr ⟨h0 x h, hUn⟩⟩
    obtain ⟨trE, σEv, σE, hrunE, hfE, hoffE, hfrmE, hsnE, hcfE, hcoE, hshE, hEv, hEvrE⟩ :=
      hAE (shL_of_shB hsh)
    have hκEv : ∀ y ∈ RE.vars κE, y = g ∨ rE? = some y ∨ ∃ q, κ = .name q ∧ y = q := fun y hy => by
      rcases e.ctx.cases' with ⟨-, h | ⟨q, hq, h⟩⟩ | ⟨x, hx, h⟩ <;> rw [h] at hy <;>
        simp only [RE.vars, List.mem_cons, List.not_mem_nil, or_false] at hy
      · exact .inl hy
      · exact hy.elim (fun hy => .inr (.inr ⟨q, hq, hy⟩)) .inl
      · exact .inr (.inl (hy ▸ hx))
    have hnotE : ∀ n, (σL n).isSome → (∀ q, κ = .name q → n ≠ q) → n ∉ RE.vars κE :=
      fun n hn hq hk => (hκEv n hk).elim (fun h => hneL _ _ hn hgL h)
        fun ho1 => ho1.elim (fun h => hneL _ _ hn (hrEL n h) rfl) fun ⟨q, h1, h2⟩ => hq q h1 h2
    have hnκE : ∀ n, n ≠ g → (∀ x, rE? = some x → n ≠ x) → n ∉ RE.vars κ → n ∉ RE.vars κE :=
      fun n hg hr hk hE => (e.of_κEvars' hE).elim hg fun h => h.elim (fun h => hr n h rfl) hk
    have hED : ∀ n, (σD n).isSome → n ∉ RE.vars κE → (∀ x, rE? = some x → n ≠ x) →
        σE n = σD n := fun n hb hk hr => (hEv n hr).trans (hfrmE n hb hk)
    have hEEv : ∀ n w, σE n = some w → σEv n = some w := fun n w hw => by
      rcases Classical.em (∃ x, rE? = some x ∧ n = x) with ⟨x, hx, rfl⟩ | hr
      · exact (hEvrE n hx).elim (fun h => h ▸ hw) fun ⟨h, _⟩ => by simp [h] at hw
      · rwa [← hEv n fun x hx he => hr ⟨x, hx, he⟩]
    have hCE : WellFormedStore σE F := fun n w hw => hoffE.canonL n w (hEEv n w hw)
    have hp1 : ∀ q ∈ ns, σE q.1 = σL q.1 := fun q hq => by
      rw [hED q.1 (by rw [hMD q hq]; exact hML q hq) (hnotE _ (hML q hq) fun q' hq' he =>
          hκne q' (by simp [hq', RE.vars]) q hq he.symm)
        (fun x hx => hneL _ _ (hML q hq) (hrEL x hx)), hMD q hq]
    have hty1 : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
        ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq => by
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hm1 q.1 (hML q hq))
      exact (hMz q hq).elim fun z ⟨hz, _, hzn⟩ => ⟨w, hw, hgt1 _ w hw (e.curY hs hz hzn)⟩
    have hcpS : ∀ q ∈ ns, Drawn s6 s7 q.2.2 := fun q hq => (hns.drawn q hq).2.1
    have hp2 : ∀ q ∈ ns, σE q.2.2 = σ1 q.1 := fun q hq => by
      obtain ⟨hng, -, -, hnrE⟩ := hs.saveNe (hcpS q hq)
      have hnk := hnκE _ hng (fun x hx he => hnrE x hx he)
        (fun hk => by simpa [hcpL q hq] using hon.reach.bound _ hk)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (hm1 q.1 (hML q hq))
      rw [hED _ (by rw [hcpD q hq, hw]; rfl) hnk fun x hx he => hnrE x hx he, hcpD q hq]
    have hgm : ∀ x, gm? = some x → σE x = some (HasBool.ttVal F) := fun x hx => by
      have hd := hs.aft.gmDrawn x hx
      have hxL : σL x = none := e.preUnbound hs hns hon.fresh (.inl (by simp [hx]))
      have hxg : x ≠ g := fun he => (hs.pre.drawn g (.inl rfl)).disj (he ▸ hd) (by omega)
      have hxE : ∀ y, rE? = some y → x ≠ y := fun y hy he =>
        (hs.pre.drawn y (.inr (.inr hy))).disj (he ▸ hd) (by omega)
      have hxM : ∀ q ∈ ns, x ≠ q.1 := fun q hq he => hneL _ _ (hML q hq) hxL he.symm
      have hxc : ∀ q ∈ ns, x ≠ q.2.2 := fun q hq he => (hcpS q hq).disj (he ▸ hd) (Nat.le_refl _)
      have h1 : σ1 x = σB x := Classical.byContradiction fun hne =>
        (hch x hne).elim (e.notWT hs (.inr (hd.of_le (by rw [hns.eq]) hnx.2.2.2.2.1)))
          fun h => (hs.rTFacts hns).1 x hx h.symm
      have hDx : σD x = some (HasBool.ttVal F) := by
        rw [hothD x (fun q hq => ⟨hxM q hq, hxc q hq⟩) hxE, h1, hB.1 x (by simp [hx])]
      rw [hED x (by rw [hDx]; rfl) (hnκE x hxg hxE fun hk => by
        simpa [hxL] using hon.reach.bound x hk) hxE, hDx]
    have hrTD : σD rT = σ1 rT := hothD rT (fun q hq => ⟨fun he => hneL _ _ (hML q hq) hrTL he.symm,
        fun he => (hs.saveNe (hcpS q hq)).2.1 he.symm⟩)
        (fun x hx he => (hs.pre.rE_ne x hx).2 he.symm)
    have hrTE : (laidU κ κE rT Tr Er d).isNil = false → σE rT = σT' rT := fun hUf => by
      have h1 : σ1 rT = σT' rT := hrTe (by simp [hUf])
      have hr : ∀ x, rE? = some x → rT ≠ x := fun x hx he => (hs.pre.rE_ne x hx).2 he.symm
      rw [hED rT (by rw [hrTD, h1.trans hOT.reach]; rfl) (hnκE rT (Ne.symm hs.pre.g_rT) hr
        fun hk => by simpa [hrTL] using hon.reach.bound rT hk) hr, hrTD, h1]
    have hEκE : (laidU κ κE rT Tr Er d).isNil = false → ∀ y ∈ RE.vars κE, σE y = σEv y :=
      fun hUf y _ => by
        rcases Classical.em (∃ x, rE? = some x ∧ y = x) with ⟨x, hx, rfl⟩ | hr
        · exact (hEvrE y hx).elim id fun ⟨_, h⟩ => by simp [h] at hUf
        · exact hEv y fun x hx he => hr ⟨x, hx, he⟩
    have hκEf : (laidU κ κE rT Tr Er d).isNil = false → κE.Fails F σE := fun hUf =>
      of_failsCongr hoffE.reach (hEκE hUf)
    have hκE : ∀ y ∈ RE.vars κ, σE y = σL y := fun y hy => by
      have hyL := hon.reach.bound y hy
      rcases Classical.em (∃ q, κ = .name q ∧ y = q) with ⟨q, hq1, rfl⟩ | hq
      · rw [hs.of_keepQ hE hrunE (hq1 ▸ e.ctx).1, hκD y hy]
      · rw [hED y (by rw [hκD y hy]; exact hyL) (hnotE y hyL fun q h1 h2 => hq ⟨q, h1, h2⟩)
          (fun x hx => hneL _ _ hyL (hrEL x hx)), hκD y hy]
    have hκH := hon.reach.congr hκE
    obtain ⟨trU, σF, hrunU, hCF, hvalF, hothF, hbF, hqU, hUnil, hUnn⟩ :=
      e.postRun hs hns true hon.fresh hML hCE hp2 (fun q hq => by
        obtain ⟨ty, hty0⟩ := htyC q hq
        obtain ⟨w, hw, ht⟩ := hty1 q hq
        obtain ⟨w', hw', ht'⟩ := hsrcS q hq
        exact ⟨ty, w, w', hw, (hp1 q hq).trans hw', ht ty hty0, ht' ty hty0⟩) hgm
        (fun hUf => by
          rw [hrTE hUf]
          first | exact .inl hOT.reach | exact .inr hOT.reach)
        (fun hUf => .inr (hκEf hUf)) (fun hUf y hy => hEκE hUf y hy ▸ hoffE.bools y hy)
        (fun y hy => hκE y hy ▸ hon.reach.bools y hy) hMG hU
    simp only [true_or, ↓reduceIte] at hvalF
  obtain ⟨hfU, hFF, hqF⟩ : Trace.AssumptionsHold P evalInterp () trU ∧ κ.Fails F σF ∧
      (∀ q g', κ = .andNeg q g' → σF q = some (HasBool.ttVal F)) := by
    obtain ⟨rfl, -, hfail⟩ := (hUnn hUf).2 htop
    refine ⟨nofun, hfail fun h => h.elim (fun h => ?_) (·.not_fails (hκEf hUf)),
      fun q g' hq => ?_⟩
    · exact HasBool.ttVal_ne_ffVal F (Option.some.inj (h.symm.trans ((hrTE hUf).trans hOT.reach)))
    · obtain ⟨h1, h2⟩ := hq ▸ hκH
      rw [hqU q g' hq fun he =>
          HasBool.ttVal_ne_ffVal F (Option.some.inj (h1.symm.trans (he ▸ h2))), h1]
  rotate_left
  obtain ⟨hfU, hHF⟩ : Trace.AssumptionsHold P evalInterp () trU ∧ κ.Holds F σF := by
    by_cases hUn : (laidU κ κE rT Tr Er d).isNil = true
    · exact (hUnil hUn).1 ▸ ⟨nofun, hκH.congr (hUnil hUn).2⟩
    have hUf := Bool.eq_false_iff.2 hUn
    have hX : σE rT = some (HasBool.ttVal F) ∨ κE.Holds F σE := .inl ((hrTE hUf).trans hOT.reach)
    by_cases ht : κ = .top
    · exact ⟨((hUnn hUf).1 ht).2 hX, ht ▸ trivial⟩
    obtain ⟨rfl, hh, -⟩ := (hUnn hUf).2 ht
    refine ⟨nofun, hh hX fun q g hq => ?_⟩
    obtain ⟨h1, h2⟩ := hq ▸ hκH
    exact ⟨h1, fun he => HasBool.ttVal_ne_ffVal F (Option.some.inj (h1.symm.trans (he ▸ h2)))⟩
  rotate_left
  all_goals
    refine ⟨_, σF, by wp_chain [hitems],
      by simpa using Trace.AssumptionsHold.append hfT (Trace.AssumptionsHold.append hfE hfU), ?_⟩
    obtain ⟨hst0cur, hst0live, hclock, hfr0⟩ := e.rt_st0 hs
    have hTd : ∀ y ∈ wDecls Tr.out.toList, σF y = σT' y := fun y hy => by
      have hyM : ∀ q ∈ ns, y ≠ q.1 := fun q hq he => by
        exact (hMz q hq).elim fun z ⟨hz, _, hzn⟩ => (e.rt_curNe hs hz hzn).2.1 (he ▸ hy)
      have hyr : y ≠ rT := fun he => (e.notT hs (.inl (.inr (.inl rfl)))).2 (he ▸ hy)
      have hyE : ∀ x, rE? = some x → y ≠ x := fun x hx he =>
        (e.notT hs (.inl (.inr (.inr hx)))).2 (he ▸ hy)
      have hyk : y ∉ RE.vars κ := fun hk => (e.rt_kvar hs hk).2.2.1 hy
      have hyD : σD y = σ1 y := hothD y (fun q hq => ⟨hyM q hq, fun he =>
        (e.notT hs (.inr ((hcpS q hq).mono hnx.2.2.2.2.2))).2 (he ▸ hy)⟩) hyE
      have hyEd : σE y = σD y := e.crossKeep hs hE hrunE y hy
      rw [hothF y (fun q hq _ => hyM q hq) hyk, hyEd, hyD, h1T y hyr]
    have hEd : ∀ y ∈ wDecls Er.out.toList, σF y = σEv y := fun y hy => by
      have hyM : ∀ q ∈ ns, y ≠ q.1 := fun q hq he => by
        exact (hMz q hq).elim fun z ⟨hz, _, hzn⟩ => (e.rt_curNe hs hz hzn).2.2 (he ▸ hy)
      rw [hothF y (fun q hq _ => hyM q hq) (fun hk => (e.rt_kvar hs hk).2.2.2 hy),
        hEv y fun x hx he => e.notWE hs (.inl (.inr (.inr hx))) (hs.armE.declW (he ▸ hy))]
    have hcur : ∀ x ∈ S, ∀ n, curName st' x = some n → (σ1 n).isSome → (∀ q ∈ ns, n ≠ q.1) →
        σF n = σ1 n := by
      intro x hx n hn hb hM
      obtain ⟨hpre, -, -⟩ := e.rt_curNe hs hx hn
      have hk : n ∉ RE.vars κ := fun hk => ((e.rt_kvar hs hk).1 x hx).2.2 hn
      have hnE : ∀ y, rE? = some y → n ≠ y := fun y hy he => hpre (.inl (he ▸ .inr (.inr hy)))
      have hnc : ∀ q ∈ ns, n ≠ q.2.2 := fun q hq he =>
        hpre (.inr (he ▸ (hcpS q hq).mono hnx.2.2.2.2.2))
      have hD : σD n = σ1 n := hothD n (fun q hq => ⟨hM q hq, hnc q hq⟩) hnE
      have hkE := hnκE n (fun h => hpre (.inl (.inl h))) hnE hk
      rw [hothF n (fun q hq _ => hM q hq) hk, hED n (by rw [hD]; exact hb) hkE hnE, hD]
    have hlive : ∀ x ∈ S, ∀ n, curName st0 x = some n → st0.live.contains n = true →
        liveBefore s6 n s4.clock = true ∧ s5.live.contains n = true := by
      intro x hx n hn hl
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hl
      obtain ⟨s, hs0⟩ := Option.isSome_iff_exists.1 hl
      obtain ⟨h4, h5, -⟩ := hst0cur x hx n hn
      have hs5 := hs.armE.liveKeep x hx n h4 s (hst0live n s hs0)
      have hlt := e.wf0.live_stamp n s hs0
      refine ⟨by simp [liveBefore, hs.armT.liveKeep x hx n h5 s hs5, hclock, hlt], ?_⟩
      simp [Std.HashMap.contains_eq_isSome_getElem?, hs5]
    have hfin : ∀ x ∈ S, ∀ n, curName st0 x = some n → st0.live.contains n = true →
        (σ1 n).isSome → σF n = σ1 n := by
      intro x hx n hn hl hb
      rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hM
      · exact hvalF q hq (hlive x hx _ hn hl).1
      · exact hcur x hx n (hst0cur x hx n hn).2.2 hb fun q hq he => hM ⟨q, hq, he⟩
    have hrT1 : ∀ x ∈ S, ∀ n, curName st' x = some n → σ1 n = σT' n := fun x hx n hn =>
      h1T n fun he => (e.rt_curNe hs hx hn).1 (.inl (.inr (.inl he)))
    have hS1 : ∀ x ∈ S, x ∈ scopeAfter S tss := fun x hx => scopeAfter_sub S tss hx
    have hV1 : ∀ x ∈ contFV k, x ∈ contFV (ess :: k) := fun x hx => mem_contFV_cons.2 (.inr hx)
    have hmono : ∀ n, (σ1 n).isSome → (σF n).isSome := fun n hn =>
      mainRun_mono hrunU n (mainRun_mono hrunE n (mainRun_mono hrunD n hn))
    have hFEv : ∀ y, (σF y).isSome → (σEv y).isSome := fun y hy => by
      have hE : (σE y).isSome := by
        by_cases hk : y ∈ RE.vars κ
        · exact hκE y hk ▸ hon.reach.bound y hk
        by_cases hM : ∃ q ∈ ns, liveBefore s6 q.1 s4.clock = true ∧ y = q.1
        · exact hM.elim fun q ⟨hq, _, he⟩ => he ▸ hp1 q hq ▸ hML q hq
        · rwa [← hothF y (fun q hq hl he => hM ⟨q, hq, hl, he⟩) hk]
      exact (Option.isSome_iff_exists.1 hE).elim fun w hw => by simp [hEEv y w hw]
    have hselT : ∀ k i n v xB, CarryReg Tr s6 k i n v xB → ∀ b, SelIs F T Y σT' v b →
        SelIs F T Y σF v b := fun _ _ _ _ _ h _ => hs.armT.sel e.hF hCF hOT.canonL hTd h
    have hselE : ∀ k i n v xB, CarryReg Er s5 k i n v xB → ∀ b, SelIs F T Y σEv v b →
        SelIs F T Y σF v b := fun _ _ _ _ _ h _ => hs.armE.sel e.hF hCF hoffE.canonL hEd h
    have hpend : ∀ l e0, e0 ∈ r.regs.toList → e0 ∈ st'.pending.getD l [] →
        (e0 ∈ Tr.regs.toList ∧ e0 ∈ s6.pending.getD l []) ∨
          (e0 ∈ Er.regs.toList ∧ e0 ∈ s5.pending.getD l []) := fun l e0 he1 he2 =>
      (List.mem_append.1 (e.regs ▸ he1)).imp (⟨·, hs.aft.pending ▸ he2⟩)
        fun h => ⟨h, e.pendE hs h he2⟩
    have hgtF : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
      by_cases hk : n ∈ RE.vars κ
      · exact rn_boolTyped (hon.reach.bools n hk)
          (fun w0 h => hon.gtyped n w0 h hY ty hty) (hbF n hk) hw
      · by_cases hM : ∃ q ∈ ns, liveBefore s6 q.1 s4.clock = true ∧ n = q.1
        · obtain ⟨q, hq, hl, rfl⟩ := hM
          exact hgt1 _ w (hvalF q hq hl ▸ hw) hY ty hty
        · rw [hothF n (fun q hq hl he => hM ⟨q, hq, hl, he⟩) hk] at hw
          exact hoffE.gtyped n w (hEEv n w hw) hY ty hty
    have hfrF : FreshInv Lc Ex st0 σF := fun y hy => hfr0 σEv hoffE.fresh y (hFEv y hy)
    have hcoR : CarryOK F T Y r st' σF := e.ry_carryOK hs hcoT hcoE hCF hOT.canonL hoffE.canonL
      hTd hEd hgtF (fun z hz n hzn hb => hmono n (hrT1 z hz n hzn ▸ hb))
      fun n hr hb => mainRun_mono hrunU n (hEv n hr ▸ hb)
    have hsnR : ∀ ex, (∀ l e0, e0 ∈ Tr.regs.toList → e0 ∈ s6.pending.getD l [] → some e0 ≠ ex →
        σT' e0 = some (HasBool.ffVal F)) →
        SnapFF F r st' ex σF := fun ex hsnT l e0 he1 he2 hne => by
      rcases hpend l e0 he1 he2 with ⟨h, h6⟩ | ⟨h, h5⟩
      · exact (hTd e0 (hs.armT.regs e0 h)) ▸ hsnT l e0 h h6 hne
      · exact (hEd e0 (hs.armE.regs e0 h)) ▸ hsnE l e0 h h5 (by simp)
  · have hregT : ∀ k i n v xB, CarryReg Tr s6 k i n v xB → CarryReg r st' k i n v xB :=
      fun k i n v xB h => ⟨e.rt_carries hs k ▸ h.1, e.regs ▸ List.mem_append_left _ h.2⟩
    have hdF : ∀ x ∈ S, x ∈ contFV k → ∀ n, curName st0 x = some n → ∃ w, σF n = some w ∧
        ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := by
      intro x hx hv n hn
      obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
      obtain ⟨w, hw, hwt⟩ := hOT.defd x hx (hV1 x hv) n h5
      have hw1 : σ1 n = some w := (hrT1 x hx n h').trans hw
      rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hM
      · by_cases hl : liveBefore s6 q.1 s4.clock = true
        · exact ⟨w, by rw [hvalF q hq hl, hw1], hwt⟩
        · obtain ⟨w0, hw0, hwt0⟩ := hsrcS q hq
          exact ⟨w0, by rw [hothF _ (fun q' hq' hl' he => hl (by rw [he]; exact hl'))
            fun hk => hκne _ hk q hq rfl, hp1 q hq, hw0], hwt0⟩
      · exact ⟨w, by rw [hcur x hx n h' (by rw [hw1]; rfl) fun q hq he => hM ⟨q, hq, he⟩, hw1], hwt⟩
    refine ⟨⟨hCF, hFF, hbF, hdF, hgtF, hfrF⟩, ⟨fun _ => ?_, fun l' e0 he1 he2 hne => ?_⟩, hqF,
      hcoR, ?_⟩
    · exact (hshE.1 e.axE).elim fun σs h => ⟨_, h⟩
    · rcases hpend l' e0 he1 he2 with ⟨h, h6⟩ | ⟨h, h5⟩
      · exact (hshT.2 l' e0 h h6 hne).elim fun σs hσs => ⟨_, hσs⟩
      · exact (hshE.2 l' e0 h h5 (by simp)).elim fun σs hσs => ⟨_, hσs⟩
    rw [(e.labels hs l).2] at hlabT
    cases hlt : st0.labelDepth[l]? with
    | none => exact hsnR none (by rwa [hlt] at hlabT)
    | some t =>
      rw [hlt] at hlabT
      obtain ⟨e0, he1, he2, he3, hsnT, hxc, hlow⟩ := hlabT
      have hLab := (e.lab l t hlt).2
      have hprojL : ∀ x ∈ Lab l, projectStore σ σx x = σx x := fun x hx => by
        simp [projectStore, (hon.defd x (hLab x hx).2 (mem_contFV_cons.2 (.inr (hLab x hx).1))).1]
      refine ⟨e0, e.regs ▸ List.mem_append_left _ he1, hs.aft.pending ▸ he2,
        (hTd e0 (hs.armT.regs e0 he1)).trans he3, hsnR (some e0) hsnT, ?_, fun k i n v xB hk h =>
          ?_⟩
      · refine
          { xagree := fun x hx hv n hn hl hlf w hw => ?_
            defd := fun x hx hv => ⟨by rw [hprojL x hv]; exact (hxc.defd x (hS1 x hx) hv).1,
              fun n hn => by
                obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
                exact hmono n (by rw [hrT1 x hx n h']; exact (hxc.defd x (hS1 x hx) hv).2 n h5)⟩
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
          rw [hprojL x hv] at hw
          have hag := hxc.xagree x (hS1 x hx) hv n h5 (hlive x hx n hn hl).2
            (e.liveFrom hs hx hn hl hlf).2.1 w hw
          refine ⟨fun k i v xB h => (hcoR k i n v xB h).1, ?_⟩
          rcases hag.2 with ⟨hall, hnw⟩ | ⟨k, i, v, xB, htk, hrg, hsel, hxB, hmax⟩
          · refine .inl ⟨fun k i v xB htk h => ?_, ?_⟩
            · rcases e.of_regCases hs h with h' | ⟨i', h'⟩
              · exact hselT k i n v xB h' false (hall k i v xB htk h')
              · exact hselE k i' n v xB h' false (hcfE k i' n v xB h')
            · have hb : (σ1 n).isSome := by rw [hrT1 x hx n h', hnw]; rfl
              rw [hfin x hx n hn hl hb, hrT1 x hx n h', hnw]
          · refine .inr ⟨k, i, v, xB, htk, hregT k i n v xB hrg, hselT k i n v xB hrg true hsel,
              by rw [hTd xB (hs.armT.regs xB hrg.2)]; exact hxB, fun k' i' v' xB' htk' h hs' => ?_⟩
            rcases e.of_regCases hs h with h'' | ⟨i'', h''⟩
            · exact (hcoT k' i' n v' xB' h'').1.elim (fun ht => hmax k' i' v' xB' htk' h'' ht)
                fun hf => (SelIs.ne hs' (hselT k' i' n v' xB' h'' false hf)).elim
            · exact (SelIs.ne hs'
                (hselE k' i'' n v' xB' h'' false (hcfE k' i'' n v' xB' h''))).elim
        · rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hM
          · exact (htyC q hq).elim fun ty0 h0 => absurd h0 (hnt ty0)
          · obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
            have hb : (σ1 n).isSome := hrT1 x hx n h' ▸ (hxc.defd x (hS1 x hx) hv).2 n h5
            rw [hcur x hx n h' hb (fun q hq he => hM ⟨q, hq, he⟩), hrT1 x hx n h'] at h2
            exact hxc.alike x (hS1 x hx) hv n h5 hnt w w' (hprojL x hv ▸ h1) h2 ty hty
      · rcases e.of_regCases hs h with h' | ⟨i', h'⟩
        · exact hselT k i n v xB h' false (hlow k i n v xB hk h')
        · exact hselE k i' n v xB h' false (hcfE k i' n v xB h')
  · have hproj : ∀ x ∈ S, x ∈ contFV k → projectStore σ σT x = σT x := fun x hx hv => by
      simp [projectStore, (hon.defd x hx (mem_contFV_cons.2 (.inr hv))).1]
    have hb1 : ∀ x ∈ S, x ∈ contFV k → ∀ n, curName st0 x = some n → (σ1 n).isSome :=
      fun x hx hv n hn => by
        obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
        exact (hrT1 x hx n h') ▸ (hOT.defd x (hS1 x hx) (hV1 x hv)).2 n h5
    refine ⟨{ toOnCore := ?_, reach := hHF }, hsnR none hsnT,
      fun k i n v xB h => ?_, hcoR, e.ax, e.drop, fun l e0 he1 he2 hne => ?_⟩
    · exact
        { agree := fun x hx hv n hn hl => by
            obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
            rw [hfin x hx n hn hl (hb1 x hx hv n hn), hrT1 x hx n h', hproj x hx hv]
            exact hOT.agree x (hS1 x hx) (hV1 x hv) n h5 (hlive x hx n hn hl).2
          defd := fun x hx hv => ⟨by rw [hproj x hx hv]; exact (hOT.defd x (hS1 x hx) (hV1 x hv)).1,
            fun n hn => hmono n (hb1 x hx hv n hn)⟩
          alike := fun x hx hv n hn hnt w w' h1 h2 ty hty => by
            rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hM
            · exact (htyC q hq).elim fun ty0 h0 => absurd h0 (hnt ty0)
            · obtain ⟨-, h5, h'⟩ := hst0cur x hx n hn
              rw [hcur x hx n h' (hb1 x hx hv n hn) (fun q hq he => hM ⟨q, hq, he⟩),
                hrT1 x hx n h'] at h2
              exact hOT.alike x (hS1 x hx) (hV1 x hv) n h5 hnt w w' (hproj x hx hv ▸ h1) h2 ty hty
          undef := fun x hx hxS => by simp [projectStore, hon.undef x hx hxS]
          canon := WellFormedStore.proj hOT.canon
          canonL := hCF
          gtyped := hgtF
          ltyped := fun x hx hv n hn w hw ty hty => by
            obtain ⟨-, h5, -⟩ := hst0cur x hx n hn
            exact hOT.ltyped x (hS1 x hx) (hV1 x hv) n h5 w (hproj x hx hv ▸ hw) ty hty
          fresh := hfrF }
    · exact (e.of_regCases hs h).elim (fun h' => hselT k i n v xB h' false (hcfT k i n v xB h'))
        fun ⟨i', h'⟩ => hselE k i' n v xB h' false (hcfE k i' n v xB h')
    · rcases hpend l e0 he1 he2 with ⟨h, h6⟩ | ⟨h, h5⟩
      · exact (hexT l e0 h h6 hne).elim fun σs hσs => ⟨_, hσs⟩
      · exact (hshE.2 l e0 h h5 hne).elim fun σs hσs => ⟨_, hσs⟩

omit iLI in
/-- With empty arm outputs, a laid-out `ite` registers nothing. -/
private theorem LaidEnv.rn_regs (hTn : Tr.out.isNil = true) (hEn : Er.out.isNil = true) :
    r.regs.toList = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
  rcases List.mem_append.1 (e.regs ▸ hx) with h | h
  · simpa [Rope.isNil_toList hTn, wDecls] using hs.armT.regs x h
  · simpa [Rope.isNil_toList hEn, wDecls] using hs.armE.regs x h

include iLV in
/-- A feasible loop-free run of a laid-out `ite` with an empty body (no output) is the empty run
    of the output establishing `RunPost`, unless it exits under `top`. -/
private theorem LaidEnv.runNil (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hout : r.out = .nil) (hrun : DRunS F X (.ite (.det c) tss ess md) σ evs o)
        (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    (κ = .top ∧ ∃ l σ1, o = .exit l σ1) ∨
    ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL' o := by
  obtain ⟨hnil, -, -⟩ := e.out.resolve_right fun ⟨_, h, _⟩ => by simp [hout, Rope.toList_nil] at h
  obtain ⟨hTn, hEn, rfl, rfl, -⟩ := hs.nilParts hns hnil
  obtain rfl : items = [] := by
    simpa [hout, Rope.toList_nil, resolveItems, pure, Except.pure] using e.res.symm
  exact .inr ⟨[], σL, .nil, nofun, e.nilRun hs hns rfl (Rope.isNil_toList hTn ▸ rfl)
    (Rope.isNil_toList hEn ▸ rfl) (e.rn_regs hs hTn hEn) (by rw [e.ax, e.axT]; rfl) e.drop hon
    hrun hfeas⟩

/-- A store that agrees with `σR` except at the else-arm reach name, which holds the Boolean
    `v`, has values of their final types and binds no name declared later, when `σR` agrees with
    the then arm's end store `σ1` except at the copies. -/
private theorem LaidEnv.elseStore
    (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns) {σR : SemanticStore P}
    {v : P.Val} (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F)
    (hgt1 : ∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hfr1 : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1)
    (hR1 : ∀ n, (∀ q ∈ ns, n ≠ q.2.2) → σR n = σ1 n)
    (hdesc : ∀ n, σE n = σR n ∨ (rE? = some n ∧ σE n = some v)) :
    (∀ n w, σE n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) ∧
    FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE := by
  refine ⟨fun n w hw hY ty hty => ?_, fun y hy => ?_⟩
  · rcases hdesc n with h | ⟨hn, h⟩
    · rcases Classical.em (∃ q ∈ ns, n = q.2.2) with ⟨q, hq, rfl⟩ | hq
      · have hY' := e.fin.2.1 q.2.2 q.1 (by
          rw [hs.aft.tyOf _ fun h => (hns.drawn q hq).2.1.disj h (Nat.le_refl _)]
          exact (hns.drawn q hq).2.2.2)
        simp [hY'] at hY
      · rw [h, hR1 n fun q hq' he => hq ⟨q, hq', he⟩] at hw
        exact hgt1 n w hw hY ty hty
    · exact tyOfName_bool (e.preT hs (.inl (.inr (.inr hn))))
        (Option.some.inj (h.symm.trans hw) ▸ hv) hty
  · rcases hdesc y with h | ⟨hn, -⟩
    · rcases Classical.em (∃ q ∈ ns, y = q.2.2) with ⟨q, hq, rfl⟩ | hq
      · obtain ⟨b, j, h1, h2, h3, -⟩ := (hns.drawn q hq).2.1
        have h2' : s5.avoid.contains q.2.2 = false := by rwa [hs.avoids.2.2.1, ← hs.avoids.2.2.2.1]
        refine ⟨fun _ hfa => by simp [hfa b j h1] at h2', fun b' j' h1' _ => .inl ?_⟩
        exact freshName_counter_inj (h1'.symm.trans h1) ▸ Nat.le_trans hs.nexts.2.2.2.1 h3
      · rw [h, hR1 y fun q hq' he => hq ⟨q, hq', he⟩] at hy
        exact (hfr1 y hy).imp_right fun h b j h1 h2 =>
          (h b j h1 h2).imp_right (.imp_right fun h => h.imp_right (.imp_right .inl))
    · obtain ⟨b, j, h1, h2, -⟩ := hs.preDrawn (.inr (.inr hn))
      exact ⟨fun _ hfa => absurd (hfa b j h1) (by simp [hs.avoids.2.2.1, h2]),
        fun _ _ _ _ => .inr (.inr (.inr (.inr (.inr hn))))⟩

include iOp iLF iLFs iLV in
omit hs in
include iIL in
/-- On the else path of a laid-out `ite` with a nonempty body (the context holding, the
    condition false), a feasible loop-free run of the else arm (with the then arm's shadow run
    `hsh`) is a feasible run of the output establishing `RunPost`, unless it exits under `top`. -/
private theorem LaidEnv.runElse (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hnn : (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr
      Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false)
    (hc : P.eval F σ c = some (HasBool.ffVal F))
    (hE' : DRun F (fun o' => X (o'.proj σ)) ess σ evs oE)
    (hsh : ShB F tss σ (VirtK oE fun o' => X (o'.proj σ)))
    (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    (κ = .top ∧ ∃ l σ1, oE.proj σ = .exit l σ1) ∨
    ∃ tr σL', MainRun F items σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL' (oE.proj σ) := by
  have hs := e.states
  obtain ⟨ce, iRT, iGM, iSV, iT, iCP, iRS, iRE, iE, iMG, iU, hsp⟩ := e.split hnn
  obtain ⟨hce, hRT, hGM, hSV, hT, hCP, hRS, hRE, hE, hMG, hU, hitems⟩ := hsp
  by_cases htop : κ = .top ∧ ∃ l σ1, oE.proj σ = .exit l σ1
  · exact .inl htop
  refine .inr ?_
  have hnx := hs.nexts
  have hav := hs.avoids
  have hsrcS := e.savedOn hs hon hns
  have hq1 : ∀ q ∈ ns, (σL q.1).isSome := fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]
  obtain ⟨σB, hrun0, hCB, hB, -⟩ := e.preRunQ hs hns hon.fresh hon.canonL hRT hGM (iQM := [])
    (qm? := none) (by cases κ <;> simp only [Rope.toList_nil] <;> rfl) nofun nofun hSV
    (e.guardOn hs hon hnn hs.aft.liveC hc (.inr rfl) hce) (.inr rfl) hsrcS
  have hdefdL : ∀ x ∈ S, x ∈ contFV ([.ite (.det c) tss ess md] :: k) → ∀ n,
      curName st' x = some n → ∃ w, σL n = some w ∧
        ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty := fun x hx hv n hn =>
    let ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hon.defd x hx hv).2 n hn)
    ⟨w, hw, hon.gtyped n w hw (e.curY hs hx hn)⟩
  obtain ⟨trT, σ1, hrunT, hfeasT, hC1, hfr1, hgt1, hk1, hpre1, -, -, hsnT, hcfT, hcoT, hshT,
      hrT1, -⟩ :=
    e.of_T hs hns hdefdL hon.gtyped hon.fresh hq1 hB nofun nofun hCB hT (shL_of_shB hsh)
  have hcpD : ∀ q ∈ ns, Drawn s6 s7 q.2.2 := fun q hq => (hns.drawn q hq).2.1
  obtain ⟨σR, hrunCR, hCR, hcR, hvR, hoR, htyC, -, hgR, -, h0R'⟩ := e.ry_midRun hs hns
    hon.fresh hsrcS hB hC1 hgt1 (fun n => mainRun_mono hrunT n) (fun n hn =>
      (hs.armT.writesW T Y iT hT σB trT σ1 hrunT n hn).imp_right fun h => (Option.some.inj h).symm)
    hCP hRS
  have hcpL : ∀ q ∈ ns, σL q.2.2 = none := fun q hq =>
    e.unbound hs hon.fresh (.inr ((hcpD q hq).mono hnx.2.2.2.2.2))
  have hR1 : ∀ n, (∀ q ∈ ns, n ≠ q.2.2) → σR n = σ1 n := fun n hn => by
    rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hq
    · rw [hvR q hq, hk1 _ (hq1 q hq)]
    · exact hoR n fun q hq' => ⟨fun he => hq ⟨q, hq', he⟩, hn q hq'⟩
  have hkR : ∀ n, (σL n).isSome → σR n = σL n := fun n hn =>
    (hR1 n fun q hq he => by simp [he, hcpL q hq] at hn).trans (hk1 n hn)
  have h0R : ∀ x, rE? = some x → σR x = none := fun x hx => (h0R' x hx).1
  obtain ⟨σD, hrunD, hCD, hcase⟩ := rEiRun e.hF hCR h0R
    (.inl ⟨hon.reach.congr fun y hy => hkR y (hon.reach.bound y hy), hgR, rfl⟩) hRE
  have hDR : ∀ n, (∀ x, rE? = some x → n ≠ x) → σD n = σR n := by
    rcases hcase with ⟨-, hDR, -⟩ | ⟨x, hx, -, rfl⟩
    · exact fun n _ => by rw [hDR]
    · exact fun n hn => (update_facts σR x (HasBool.ttVal F)).2 n (Ne.symm (hn x hx))
  obtain ⟨σEs, hCEs, hdesc, hreachE, hvirt⟩ : ∃ σEs : SemanticStore P, WellFormedStore σEs F ∧
      (∀ n, σEs n = σR n ∨ (rE? = some n ∧ σEs n = some (HasBool.ttVal F))) ∧ κE.Holds F σEs ∧
      (σEs = σD ∨ ∃ x, rE? = some x ∧ σEs = SemanticStore.update σD x (HasBool.ttVal F) ∧
        σD x = none ∧
        Er.out.isNil = true ∧ (laidU κ κE rT Tr Er d).isNil = true) := by
    rcases hcase with ⟨-, hDR', hcase⟩ | ⟨x, hx, -, rfl⟩
    · rcases e.ctx.cases' with ⟨hr, hκE⟩ | ⟨x, hx, hκE⟩
      · refine ⟨σD, hCD, fun n => .inl (by rw [hDR']), ?_, .inl rfl⟩
        rw [hDR']
        rcases hκE with h | ⟨q, hq, h⟩
        · rwa [h]
        · have hq' := hq ▸ hon.reach
          exact h ▸ ⟨(hkR q (hq'.bound q (List.mem_singleton_self _))).trans hq', hgR⟩
      · rcases hcase with hr | hb
        · exact nomatch hr ▸ hx
        refine ⟨SemanticStore.update σD x (HasBool.ttVal F), wfStore_update_bool hCD x (.inl rfl),
          fun n => ?_,
          hκE ▸ (update_facts σD x (HasBool.ttVal F)).1,
          .inr ⟨x, hx, rfl, by rw [hDR']; exact h0R x hx, Bool.and_eq_true _ _ ▸ hb⟩⟩
        exact (update_cases σD x (HasBool.ttVal F) n).imp (·.trans (by rw [hDR']))
          fun ⟨he, h⟩ => ⟨he ▸ hx, h⟩
    · refine ⟨_, hCD, fun n => ?_, ?_, .inl rfl⟩
      · exact (update_cases σR x (HasBool.ttVal F) n).imp_right fun ⟨he, h⟩ => ⟨he ▸ hx, h⟩
      · rcases e.ctx.cases' with ⟨hr, -⟩ | ⟨y, hy, hκE⟩
        · exact nomatch hr ▸ hx
        · cases hx ▸ hy
          exact hκE ▸ (update_facts σR x (HasBool.ttVal F)).1
  have hES := e.elseStore hs hns (.inl rfl) hgt1 hfr1 hR1 hdesc
  obtain ⟨trE, σE', hrunE, hfeasE, hpost⟩ := (e.armEp hs hE).2.1 σ σEs _ evs oE
    (hs.elseE hon hCEs (fun n hn => (hdesc n).elim (·.trans (hkR n hn)) fun ⟨h, _⟩ => by
      simp [e.unbound hs hon.fresh (.inl (.inr (.inr h)))] at hn) hES.1 hES.2 hreachE) hE' hfeas
  obtain ⟨σEr, hrunEr, hEr, hwrE, hEreal⟩ : ∃ σEr : SemanticStore P,
      MainRun F iE σD trE σEr ∧ (∀ n, σEr n = σE' n ∨ (rE? = some n ∧ σEr n = none)) ∧
      ((∀ n, σEr n ≠ σD n → Wr0 (Block.idents ess) s4 s5 n ∨ κE.wvar = some n) ∧
        (∀ n, σEr n ≠ σD n → Er.A.contains n = true ∨ n ∈ wDecls Er.out.toList ∨
          n ∈ RE.vars κE ∨ liveBefore s5 n s4.clock = false) ∧
        ∀ n ∈ wDecls Tr.out.toList, σEr n = σD n) ∧
      ((laidU κ κE rT Tr Er d).isNil = false → σEr = σE') := by
    rcases hvirt with rfl | ⟨x, hx, rfl, hx0, hEn, hUn⟩
    · exact ⟨σE', hrunE, fun _ => .inl rfl, ⟨hs.armE.writesW T Y iE hE _ trE σE' hrunE,
        arm_writesLive e.hF e.runE hs.ctxE hs.wf4 (fun x hx => hs.avoids.2.1 ▸ e.avoidArm (.inr hx))
          T Y iE hE _ trE σE' hCD hrunE,
        e.crossKeep hs hE hrunE⟩, fun _ => rfl⟩
    · obtain rfl := resolve_isNil hEn hE
      cases hrunE
      refine ⟨σD, .nil, fun n => ?_, ⟨fun n h => absurd rfl h, fun n h => absurd rfl h,
        fun _ _ => rfl⟩, fun h => by simp [hUn] at h⟩
      exact (update_cases σD x (HasBool.ttVal F) n).imp Eq.symm fun ⟨he, _⟩ => ⟨he ▸ hx, he ▸ hx0⟩
  obtain ⟨hCE', hgtE', hfrE', hqE', hκE', hκEb'⟩ : WellFormedStore σE' F ∧
      (∀ n w, σE' n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty) ∧
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 σE' ∧
      (∀ q g', κE = .andNeg q g' → σE' q = some (HasBool.ttVal F)) ∧
      (κE.Holds F σE' ∨ κE.Fails F σE') ∧
      ∀ y ∈ RE.vars κE, σE' y = some (HasBool.ttVal F) ∨ σE' y = some (HasBool.ffVal F) := by
    cases oE with
    | normal σE1 =>
      exact ⟨hpost.1.canonL, hpost.1.gtyped, hpost.1.fresh, fun q g' h => (h ▸ hpost.1.reach).1,
        .inl hpost.1.reach, hpost.1.reach.bools⟩
    | exit l σE1 =>
      exact ⟨hpost.1.canonL, hpost.1.gtyped, hpost.1.fresh, hpost.2.2.1, .inr hpost.1.reach,
        hpost.1.bools⟩
  have hrEL : ∀ x, rE? = some x → σL x = none := fun x hx =>
    e.unbound hs hon.fresh (.inl (.inr (.inr hx)))
  have hgL : σL g = none := e.unbound hs hon.fresh (.inl (.inl rfl))
  have hκEL : ∀ n, (σL n).isSome → n ∉ RE.vars κ → n ∉ RE.vars κE := fun n hn hnκ hE =>
    (e.of_κEvars' hE).elim (fun h => by simp [h, hgL] at hn) (·.elim (by simp [hrEL n ·] at hn) hnκ)
  have hkEW : ∀ n, ¬ Wr0 (Block.idents ess) s4 s5 n → n ∉ RE.vars κE → σEr n = σD n :=
    fun n hW hκ => Classical.byContradiction fun hne =>
      (hwrE.1 n hne).elim hW fun h => hκ (wvar_mem h)
  have hkEL : ∀ n, Er.A.contains n = false → n ∉ wDecls Er.out.toList → n ∉ RE.vars κE →
      liveBefore s5 n s4.clock = true → σEr n = σD n := fun n h1 h2 h3 h4 =>
    Classical.byContradiction fun hne => (hwrE.2.1 n hne).elim (by simp [h1]) fun h =>
      h.elim h2 fun h => h.elim h3 (by simp [h4])
  have hErE : ∀ n, (∀ x, rE? = some x → n ≠ x) → σEr n = σE' n := fun n hn =>
    (hEr n).elim id fun ⟨h, _⟩ => absurd rfl (hn n h)
  have hσLrE : ∀ n, (σL n).isSome → ∀ x, rE? = some x → n ≠ x := fun n hn x hx he => by
    simp [he, hrEL x hx] at hn
  have hmv := fun q (hq : q ∈ ns) => e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)
  have hnotκEd : ∀ m, Drawn s6 st' m → m ∉ RE.vars κE := fun m hm hE => by
    exact (e.of_κEvars' hE).elim (fun h => (hs.pre.drawn m (.inl h)).disj hm (by omega))
      fun ho1 => ho1.elim (fun h => (hs.pre.drawn m (.inr (.inr h))).disj hm (by omega))
      fun h => (e.of_ctxNe hs h).2.2.2 s6 st' (by omega) hm
  have hcp6 : ∀ q ∈ ns, Drawn s6 st' q.2.2 := fun q hq => (hcpD q hq).mono hnx.2.2.2.2.2
  have hErcp : ∀ q ∈ ns, σEr q.2.2 = σL q.1 := fun q hq => by
    rw [hkEW _ (e.notWE hs (.inr (hcp6 q hq))) (hnotκEd _ (hcp6 q hq)),
      hDR _ (hs.saveNe (hcpD q hq)).2.2.2, hcR q hq, hk1 _ (hq1 q hq)]
  have hDsv : ∀ q ∈ ns, σD q.1 = σL q.1 := fun q hq => by
    rw [hDR _ (hσLrE q.1 (hq1 q hq)), hkR _ (hq1 q hq)]
  have hgmFF : ∀ x, gm? = some x →
      σEr x = some (if false then HasBool.ttVal F else HasBool.ffVal F) := fun x hx => by
    have hd6 := (hs.aft.gmDrawn x hx).of_le (by rw [hns.eq]) hns.next
    rw [hkEW _ (e.notWE hs (.inr hd6)) (hnotκEd _ hd6), hDR _ fun y hy he =>
      (hs.pre.drawn y (.inr (.inr hy))).disj (he ▸ hd6) (by omega),
      hR1 _ fun q hq he => (hcpD q hq).disj (he ▸ hs.aft.gmDrawn x hx) (Nat.le_refl _)]
    exact hpre1 x (List.mem_cons_of_mem _ (Option.mem_toList.2 hx))
  have hty : ∀ q ∈ ns, ∃ ty w w', σL q.1 = some w ∧ σEr q.1 = some w' ∧
      HasVal.valueOfTy F w ty ∧ HasVal.valueOfTy F w' ty := fun q hq => by
    obtain ⟨ty, hty⟩ := htyC q hq
    obtain ⟨w', hw', hty'⟩ := hsrcS q hq
    have hb : (σEr q.1).isSome := mainRun_mono hrunEr q.1 (by rw [hDsv q hq, hw']; rfl)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hb
    obtain ⟨z, hz, -, hzn⟩ := hmv q hq
    refine ⟨ty, w', w, hw', hw, hty' ty hty, ?_⟩
    exact hgtE' q.1 w (hErE _ (hσLrE q.1 (by simp [hw'])) ▸ hw) (e.curY hs hz hzn) ty hty
  have hCEr : WellFormedStore σEr F := fun x v hx => by
    exact (hEr x).elim (fun h => hCE' x v (h ▸ hx)) fun ⟨_, h⟩ => by simp [h] at hx
  have hκEr : ∀ y ∈ RE.vars κ, σEr y = σL y := fun y hy => by
    have hyL := hon.reach.bound y hy
    by_cases hyE : y ∈ RE.vars κE
    · rcases e.ctx.cases' with ⟨hr, h | ⟨q, hq, h⟩⟩ | ⟨x, hx, h⟩ <;> rw [h] at hyE <;>
        simp only [RE.vars, List.mem_cons, List.not_mem_nil, or_false] at hyE
      · simp [hyE, hgL] at hyL
      · rcases hyE with rfl | rfl
        · rw [hErE _ (hσLrE _ hyL), hqE' _ _ h, (hq ▸ hon.reach :)]
        · simp [hgL] at hyL
      · simp [hyE, hrEL x hx] at hyL
    · rw [hkEW y (e.notWEκ hs hy) hyE, hDR _ (hσLrE _ hyL), hkR _ hyL]
  have hreachEr : κ.Holds F σEr := hon.reach.congr hκEr
  have hrTEr : (laidU κ κE rT Tr Er d).isNil = false →
      σEr rT = some (HasBool.ffVal F) := fun hUf => by
    have hrTE : rT ∉ RE.vars κE := fun hE => by
      exact (e.of_κEvars' hE).elim (fun h => hs.pre.g_rT h.symm)
        fun ho1 => ho1.elim (fun h => (hs.pre.rE_ne rT h).2 rfl)
        fun h => (e.of_ctxNe hs h).2.2.2 s1 s4 hnx.1 (hs.pre.drawn rT (.inr (.inl rfl)))
    rw [hkEW rT (e.notWE hs (.inl (.inr (.inl rfl)))) hrTE,
      hDR rT fun x hx he => (hs.pre.rE_ne x hx).2 he.symm,
      hR1 rT fun q hq he => (hs.saveNe (hcpD q hq)).2.1 he.symm]
    exact hrT1 (by revert hUf; cases Tr.out.isNil <;> simp)
  obtain ⟨trU, σF, hrunU, hCF, hvalF, hothF, hboolF, hqU, hUnil, hUnn⟩ :=
    e.postRun hs hns false hon.fresh hq1 hCEr hErcp hty hgmFF (fun hUf => .inr (hrTEr hUf))
      (fun hUf => hEreal hUf ▸ hκE') (fun hUf => hEreal hUf ▸ hκEb') (hreachEr.bools) hMG hU
  have hUh : κE.Holds F σE' →
      Trace.AssumptionsHold P evalInterp () trU ∧ κ.Holds F σF := fun hh => by
    by_cases hUn : (laidU κ κE rT Tr Er d).isNil = true
    · exact (hUnil hUn).1 ▸ ⟨nofun, hreachEr.congr (hUnil hUn).2⟩
    have hUf := Bool.eq_false_iff.2 hUn
    have hx : σEr rT = some (HasBool.ttVal F) ∨ κE.Holds F σEr := .inr (hEreal hUf ▸ hh)
    by_cases hκt : κ = .top
    · exact ⟨((hUnn hUf).1 hκt).2 hx, by subst hκt; trivial⟩
    obtain ⟨rfl, hh2, -⟩ := (hUnn hUf).2 hκt
    refine ⟨nofun, hh2 hx fun q g' hq => ?_⟩
    obtain ⟨h1, h2⟩ := hq ▸ hreachEr
    exact ⟨h1, fun he => HasBool.ttVal_ne_ffVal F (Option.some.inj (h1.symm.trans (he ▸ h2)))⟩
  have hUx : κE.Fails F σE' → κ ≠ .top → (laidU κ κE rT Tr Er d).isNil = false →
      trU = [] ∧ κ.Fails F σF := fun hf hκt hUf => by
    obtain ⟨h1, -, h3⟩ := (hUnn hUf).2 hκt
    refine ⟨h1, h3 fun hx => hx.elim (fun h => ?_) fun h => h.not_fails ?_⟩
    · exact HasBool.ttVal_ne_ffVal F (Option.some.inj (h.symm.trans (hrTEr hUf)))
    · exact hEreal hUf ▸ hf
  obtain ⟨-, -, hst1, hcur1⟩ := wRen_run e.run1
  have hlive4 : s4.live = st0.live := by rw [hs.pre.eq]; show s1.live = st0.live; rw [hst1]
  have hcurPre : ∀ z ∈ S, ∀ n, curName st' z = some n →
      ∀ x, (x = g ∨ x = rT ∨ rE? = some x) → n ≠ x := fun z hz n hzn x hx he => by
    subst he
    rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
    · exact (hs.preNm hx z).2.2.2 hm
    · obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn _ hx
      simp [hav.1, e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2
  have hFn : ∀ z ∈ S, ∀ n, curName st0 z = some n → σF n = σE' n := fun z hz n hzn => by
    have hn' : curName st' z = some n := (hs.curS hz (hcur1 z n hzn)).2.2.2
    have hnrE : ∀ x, rE? = some x → n ≠ x := fun x hx => hcurPre z hz n hn' x (.inr (.inr hx))
    by_cases hm : ∃ q ∈ ns, liveBefore s6 q.1 s4.clock = true ∧ n = q.1
    · obtain ⟨q, hq, hl, rfl⟩ := hm
      rw [hvalF q hq hl]
      split
      · rename_i hA
        rw [← hErE _ hnrE, hkEL _ (hA.resolve_left Bool.false_ne_true) (e.re_EdeclNotM hs · hz hn')
          (hκEL _ (hq1 q hq) (e.re_curNotκ hs hz hn')) (LaidCore.live65 hs hl), hDsv q hq]
      · exact hErE _ hnrE
    · rw [hothF n (fun q hq hl he => hm ⟨q, hq, hl, he⟩) (e.re_curNotκ hs hz hn'), hErE n hnrE]
  have hFbound : ∀ n, (σF n).isSome → (σEr n).isSome := fun n hn => by
    by_cases hnκ : n ∈ RE.vars κ
    · exact hκEr n hnκ ▸ hon.reach.bound n hnκ
    by_cases hm : ∃ q ∈ ns, liveBefore s6 q.1 s4.clock = true ∧ n = q.1
    · exact hm.elim fun q ⟨hq, _, he⟩ => he ▸ (hty q hq).elim fun _ ⟨_, _, _, h, _⟩ => by simp [h]
    · rwa [hothF n (fun q hq hl he => hm ⟨q, hq, hl, he⟩) hnκ] at hn
  have hFgt : ∀ n w, σF n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty := fun n w hw hY ty hty => by
    by_cases hnκ : n ∈ RE.vars κ
    · exact rn_boolTyped (hon.reach.bools n hnκ)
        (fun w0 h => hon.gtyped n w0 h hY ty hty) (hboolF n hnκ) hw
    by_cases hm : ∃ q ∈ ns, liveBefore s6 q.1 s4.clock = true ∧ n = q.1
    · obtain ⟨q, hq, hl, rfl⟩ := hm
      rw [hvalF q hq hl] at hw
      split at hw
      · obtain ⟨w', hw', hty'⟩ := hsrcS q hq
        exact Option.some.inj (hw'.symm.trans hw) ▸ hty' ty hty
      · obtain ⟨z, hz, -, hzn⟩ := hmv q hq
        exact hgtE' q.1 w (hErE _ (hσLrE _ (hq1 q hq)) ▸ hw) (e.curY hs hz hzn) ty hty
    · rw [hothF n (fun q hq hl he => hm ⟨q, hq, hl, he⟩) hnκ] at hw
      exact (hEr n).elim (fun h => hgtE' n w (h ▸ hw) hY ty hty) fun ⟨_, h⟩ => by simp [h] at hw
  have hEdecl : ∀ n ∈ wDecls Er.out.toList, ∀ x, rE? = some x → n ≠ x := fun n hn x hx he => by
    rcases hs.armE.decl n hn with hd | ⟨hi, -⟩ | ⟨y, -, hy⟩
    · exact (hs.pre.drawn x (.inr (.inr hx))).disj (he ▸ hd) (Nat.le_refl _)
    · obtain ⟨b, j, h1, h2, -, -⟩ := hs.pre.drawn x (.inr (.inr hx))
      subst he
      simp [hav.1, e.avoidArm (.inr (stmtsInits_mem_idents _ hi)) b j h1] at h2
    · exact (hs.preNm (.inr (.inr hx)) y).1 (he ▸ hy)
  have hFE : ∀ n ∈ wDecls Er.out.toList, σF n = σE' n := fun n hn => by
    rw [hothF n (fun q hq _ he => (hmv q hq).elim fun z ⟨hz, _, hzn⟩ =>
      e.re_EdeclNotM hs hn hz (he ▸ hzn)) fun hκ => (e.re_κNotE hs hκ).2 hn, hErE n (hEdecl n hn)]
  have hFT : ∀ n ∈ wDecls Tr.out.toList, σF n = σ1 n := fun n hn => by
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := e.re_TdeclFacts hs hn
    rw [hothF n (fun q hq _ he => (hmv q hq).elim fun z ⟨hz, _, hzn⟩ => i3 z hz (he ▸ hzn)) i6,
      hwrE.2.2 n hn, hDR n fun x hx => i4 x (.inr (.inr hx)), hR1 n fun q hq => i5 _ (hcp6 q hq)]
  have hbT : ∀ z ∈ S, ∀ n, curName st' z = some n → (σ1 n).isSome → (σF n).isSome :=
    fun _ _ n _ hn =>
      mainRun_mono hrunU n (mainRun_mono hrunEr n (mainRun_mono (hrunCR.append hrunD) n hn))
  have hbE : ∀ n, (∀ x, rE? = some x → n ≠ x) → (σE' n).isSome → (σF n).isSome :=
    fun n hnr hn => (hEr n).elim (fun h => mainRun_mono hrunU n (h ▸ hn))
      fun ⟨h, _⟩ => absurd rfl (hnr n h)
  have hsnF : ∀ ex, SnapFF F Er s5 ex σE' →
      SnapFF F r st' ex σF := fun ex hsnE l e' he' hp hne => by
    rcases List.mem_append.1 (e.regs ▸ he') with hT' | hE'
    · exact hFT e' (hs.armT.regs e' hT') ▸ hsnT l e' hT' (hs.aft.pending ▸ hp) (by simp)
    · exact hFE e' (hs.armE.regs e' hE') ▸ hsnE l e' hE' (e.pendE hs hE' hp) hne
  have hvx : ∀ l σs, VirtK oE (fun o' => X (o'.proj σ)) (.exit l σs) →
      X (.exit l (projectStore σ σs)) := by
    cases oE <;> exact fun _ _ h => h
  have hendF : ∀ ex, ExitEnds Er s5 ex (fun o' => X (o'.proj σ)) → ExitEnds r st' ex X :=
    fun ex hexE l e' he' hp hne => by
      rcases List.mem_append.1 (e.regs ▸ he') with hT' | hE'
      · exact (hshT.2 l e' hT' (hs.aft.pending ▸ hp) (by simp)).elim fun σs h => ⟨_, hvx l σs h⟩
      · exact (hexE l e' hE' (e.pendE hs hE' hp) hne).elim fun _ h => ⟨_, h⟩
  obtain ⟨-, -, -, hfr0⟩ := e.rt_st0 hs
  have hfrF : FreshInv Lc Ex st0 σF := fun y hy => hfr0 σE' hfrE' y <| by
    exact (hEr y).elim (fun h => h ▸ hFbound y hy) fun ⟨_, h⟩ => by simpa [h] using hFbound y hy
  have hn4 : ∀ x n, curName st0 x = some n → curName s4 x = some n := fun x n hn =>
    hs.pre.eq ▸ hcur1 x n hn
  refine ⟨trT ++ (trE ++ trU), σF, by wp_chain [hitems], ?_⟩
  cases oE with
  | normal σE1 =>
  obtain ⟨hOnE, hsnE, hcfE, hcoE, -, -, hexE⟩ := hpost
  obtain ⟨hfeasU, hreachF⟩ := hUh hOnE.reach
  refine ⟨Trace.AssumptionsHold.append hfeasT (Trace.AssumptionsHold.append hfeasE hfeasU), ?_⟩
  have hcarry : CarryFF F T Y r st' σF := fun _ _ _ _ _ hr => (e.of_regCases hs hr).elim
    (fun hr => hs.armT.sel e.hF hCF hC1 hFT hr (hcfT _ _ _ _ _ hr))
    fun ⟨_, hr⟩ => hs.armE.sel e.hF hCF hCE' hFE hr (hcfE _ _ _ _ _ hr)
  have hP : ∀ x ∈ S, x ∈ contFV k → projectStore σ σE1 x = σE1 x := fun x hx hv => by
    simp [projectStore, (hon.defd x hx (mem_contFV_cons.2 (.inr hv))).1]
  refine ⟨⟨⟨fun x hx hv n hn hl => ?_, fun x hx hv => ?_, fun x hx hv n hn hty w w' h1 h2 => ?_,
    fun x hx hxS => ?_, WellFormedStore.proj hOnE.canon, hCF, hFgt,
    fun x hx hv n hn w hw ty hty => ?_, hfrF⟩, hreachF⟩, hsnF none hsnE, hcarry,
    e.ry_carryOK hs hcoT hcoE hCF hC1 hCE' hFT hFE hFgt hbT hbE, e.ax, e.drop, hendF none hexE⟩
  · rw [hFn x hx n hn, hP x hx hv]
    exact hOnE.agree x (scopeAfter_sub S ess hx) (mem_contFV_cons.2 (.inr hv)) n (hn4 x n hn)
      (by rw [hlive4]; exact hl)
  · have hd := hOnE.defd x (scopeAfter_sub S ess hx) (mem_contFV_cons.2 (.inr hv))
    exact ⟨hP x hx hv ▸ hd.1, fun n hn => hFn x hx n hn ▸ hd.2 n (hn4 x n hn)⟩
  · exact hOnE.alike x (scopeAfter_sub S ess hx) (mem_contFV_cons.2 (.inr hv)) n (hn4 x n hn) hty
      w w' (hP x hx hv ▸ h1) (hFn x hx n hn ▸ h2)
  · simp [projectStore, hon.undef x hx hxS]
  · exact hOnE.ltyped x (scopeAfter_sub S ess hx) (mem_contFV_cons.2 (.inr hv)) n (hn4 x n hn) w
      (hP x hx hv ▸ hw) ty hty
  | exit l σE1 =>
  obtain ⟨hOffE, hshE, -, hcoE, hlabE⟩ := hpost
  have hκ : κ ≠ .top := fun h => htop ⟨h, l, _, rfl⟩
  have hUf : (laidU κ κE rT Tr Er d).isNil = false := by
    have h := hs.armE.exitMin (fun l t hl => (e.lab l t ((e.labels hs l).1.symm.trans hl)).1) _
      σ evs l σE1 hE'
    cases κ <;> simp [laidU, h, setReach, Rope.isNil] at hκ ⊢
  obtain ⟨rfl, hfailF⟩ := hUx hOffE.reach hκ hUf
  refine ⟨Trace.AssumptionsHold.append hfeasT (Trace.AssumptionsHold.append hfeasE nofun),
    ⟨hCF, hfailF, hboolF, fun x hx hv n hn => ?_, hFgt, hfrF⟩, ⟨fun _ => ?_, hendF _ hshE.2⟩,
    fun q0 g0 hq => ?_, e.ry_carryOK hs hcoT hcoE hCF hC1 hCE' hFT hFE hFgt hbT hbE, ?_⟩
  · exact hFn x hx n hn ▸ hOffE.defd x hx (mem_contFV_cons.2 (.inr hv)) n (hn4 x n hn)
  · exact (hshT.1 e.axT).elim fun _ h => ⟨_, h⟩
  · obtain ⟨h1, h2⟩ := hq ▸ hon.reach
    rw [hqU q0 g0 hq fun he => HasBool.ttVal_ne_ffVal F (Option.some.inj (h1.symm.trans (he ▸ h2))),
      hκEr q0 (by simp [hq, RE.vars])]
    exact h1
  rw [(e.labels hs l).1] at hlabE
  revert hlabE
  cases hlt : st0.labelDepth[l]? with
  | none => exact hsnF none
  | some t =>
    rintro ⟨e0, he0, hp0, het, hsn0, hcore, hbelow⟩
    have hV : ∀ x ∈ S, x ∈ Lab l → projectStore σ σE1 x = σE1 x := fun x hx hv => by
      simp [projectStore, (hon.defd x hx (mem_contFV_cons.2 (.inr ((e.lab l t hlt).2 x hv).1))).1]
    refine ⟨e0, e.regs ▸ List.mem_append_right _ he0, hs.aft.pending ▸ hs.armT.pendKeep l e0 hp0,
      (hFE e0 (hs.armE.regs e0 he0)).trans het, hsnF _ hsn0,
      ⟨fun x hx hv n hn hln hlf w hw => ?_, fun x hx hv => ?_,
        fun x hx hv n hn hty w w' h1 h2 => ?_, fun x hx hxS => ?_,
        WellFormedStore.proj hcore.canon, hCF, hFgt, fun x hx hv n hn w hw ty hty => ?_, hfrF⟩,
      fun k' i n v xB hk hr => ?_⟩
    · obtain ⟨h1, h2⟩ := hcore.xagree x (scopeAfter_sub S ess hx) hv n (hn4 x n hn)
        (by rw [hlive4]; exact hln) (e.liveFrom hs hx hn hln hlf).1 w (hV x hx hv ▸ hw)
      have hT : ∀ k i n v xB, CarryReg Tr s6 k i n v xB → SelIs F T Y σF v false :=
        fun k i n v xB hr => hs.armT.sel e.hF hCF hC1 hFT hr (hcfT _ _ _ _ _ hr)
      refine ⟨fun k i v xB hr => ?_, ?_⟩
      · exact (e.of_regCases hs hr).elim (fun h => .inr (hT _ _ _ _ _ h))
          fun ⟨i', h⟩ => (h1 _ _ _ _ h).imp (hs.armE.sel e.hF hCF hCE' hFE h)
            (hs.armE.sel e.hF hCF hCE' hFE h)
      rcases h2 with ⟨hA, hw⟩ | ⟨k, i, v, xB, htk, hr, hsel, hxB, hmax⟩
      · refine .inl ⟨fun k i v xB htk hr => ?_, (hFn x hx n hn).trans hw⟩
        exact (e.of_regCases hs hr).elim (fun h => hT _ _ _ _ _ h)
          fun ⟨i', h⟩ => hs.armE.sel e.hF hCF hCE' hFE h (hA _ _ _ _ htk h)
      obtain ⟨m, hm, -, hm2⟩ := e.ry_regIdx hs k
      refine .inr ⟨k, i + m, v, xB, htk, hm2 _ _ _ _ hr, hs.armE.sel e.hF hCF hCE' hFE hr hsel,
        (hFE xB (hs.armE.regs xB hr.2)).trans hxB, fun k' i' v' xB' htk' hr' hs' => ?_⟩
      obtain ⟨m', hm', hm1', -⟩ := e.ry_regIdx hs k'
      rcases hm1' _ _ _ _ hr' with h | ⟨hle, h⟩
      · exact (SelIs.ne hs' (hT _ _ _ _ _ h)).elim
      rcases hmax _ _ _ _ htk' h (hs.armE.sel e.hF hCE' hCF (fun n hn => (hFE n hn).symm) h hs')
        with hlt | ⟨rfl, hle'⟩
      · exact .inl hlt
      · exact .inr ⟨rfl, by omega⟩
    · have hd := hcore.defd x (scopeAfter_sub S ess hx) hv
      exact ⟨hV x hx hv ▸ hd.1, fun n hn => hFn x hx n hn ▸ hd.2 n (hn4 x n hn)⟩
    · exact hcore.alike x (scopeAfter_sub S ess hx) hv n (hn4 x n hn) hty w w' (hV x hx hv ▸ h1)
        (hFn x hx n hn ▸ h2)
    · simp [projectStore, hon.undef x hx hxS]
    · exact hcore.ltyped x (scopeAfter_sub S ess hx) hv n (hn4 x n hn) w (hV x hx hv ▸ hw) ty hty
    · exact (e.of_regCases hs hr).elim (fun h => hs.armT.sel e.hF hCF hC1 hFT h (hcfT _ _ _ _ _ h))
        fun ⟨i', h⟩ => hs.armE.sel e.hF hCF hCE' hFE h (hbelow k' i' n v xB hk h)

omit iDE iLB iHF iSF iHI iLI iHFs iWL e hs in
/-- A merge whose copy holds the variable's own value gives the variable its own value. -/
private theorem of_mergeVal_eq {gm? : Option P.Ident}
    {EA : Std.HashSet P.Ident} {p : P.Ident × P.Ident} (h : σ p.2 = σ p.1) :
    mergeVal F σ gm? EA p = σ p.1 := by cases gm? <;> simp [mergeVal, h]

include iLV in
omit e hs in
/-- Off its path, the else arm of a laid-out `ite` one of whose arms always exits runs from a
    value-valued store `σS` satisfying a description `D` under which every store where `κE`
    fails with Boolean variables meets the else arm's `OffInv`: either `κE` fails at `σS` with
    Boolean variables, or the else arm's output and the reach update are empty and `κE` is a
    variable `x` unbound at `σS` whose update to false keeps `D`.  The run ends at `σEr`, with
    the else arm's off-path facts at a store `σEo` that agrees with `σEr` where `σEr` is bound,
    outside `κE` where `σEo` is bound, and everywhere when the reach update is not empty. -/
private theorem LaidCore.offE
    (e : LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
      Ex k Lab wc rdc s1 g s2 rT s3 κE rE?
      s4 Er s5 Tr s6)
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7 gm?
      st' rdc nonnil) (hE : resolveItems T Y Er.out.toList = .ok iE)
    {σS : SemanticStore P} (hshE : ShL F ess σs K)
    (hCS : WellFormedStore σS F) {D : SemanticStore P → Prop}
    (hEoff : ∀ σE, WellFormedStore σE F → D σE → κE.Fails F σE →
      (∀ y ∈ RE.vars κE, σE y = some (HasBool.ttVal F) ∨ σE y = some (HasBool.ffVal F)) →
      OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σE) (hD : D σS)
    (hcase : (κE.Fails F σS ∧ ∀ y ∈ RE.vars κE,
        σS y = some (HasBool.ttVal F) ∨ σS y = some (HasBool.ffVal F)) ∨
      ∃ x, κE = .name x ∧ σS x = none ∧ Er.out.isNil = true ∧
        (laidU κ κE rT Tr Er d).isNil = true ∧ D (SemanticStore.update σS x (HasBool.ffVal F))) :
    ∃ trE σEr σEo, MainRun F iE σS trE σEr ∧ Trace.AssumptionsHold P evalInterp () trE ∧
      WellFormedStore σEr F ∧
      OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 κE
        (if Er.ax = true then S else scopeAfter S ess) (contFV (ess :: k)) σEo ∧
      Frame κE σS σEr ∧ SnapFF F Er s5 none σEr ∧ CarryFF F T Y Er s5 σEr ∧
      CarryOK F T Y Er s5 σEr ∧ ShEnds Er s5 none K ∧
      (∀ n, (σEr n).isSome → σEo n = σEr n) ∧ (∀ n, (σEo n).isSome → n ∉ RE.vars κE →
        σEr n = σEo n) ∧ ((laidU κ κE rT Tr Er d).isNil = false → σEo = σEr) := by
  rcases hcase with ⟨hf, hb⟩ | ⟨x, rfl, hSx, hEn, hUn, hDx⟩
  · obtain ⟨trE, σE', hrunE, hfeasE, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE⟩ :=
      (e.armEp hs hE).2.2 σs σS _ (hEoff σS hCS hD hf hb) hshE
    exact ⟨trE, σE', σE', hrunE, hfeasE, hoffE.canonL, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ => rfl⟩
  obtain rfl : iE = [] := resolve_isNil hEn hE
  have hreg : ∀ y ∈ Er.regs.toList, False := fun y hy => by
    simpa [Rope.isNil_toList hEn, wDecls] using hs.armE.regs y hy
  have hxff : SemanticStore.update σS x (HasBool.ffVal F) x = some (HasBool.ffVal F) :=
    (update_facts σS x (HasBool.ffVal F)).1
  obtain ⟨trE, σE', hrunE, -, hoffE, -, -, -, -, hseE⟩ := (e.armEp hs hE).2.2 σs _ _
    (hEoff _ (wfStore_update_bool hCS x (.inr rfl)) hDx hxff fun y hy =>
      .inr (List.mem_singleton.1 hy ▸ hxff)) hshE
  cases hrunE
  refine ⟨[], σS, _, .nil, nofun, hCS, hoffE, fun _ _ _ => rfl,
    fun _ y hy => (hreg y hy).elim, fun _ _ _ _ _ hc => (hreg _ hc.2).elim,
    fun _ _ _ _ _ hc => (hreg _ hc.2).elim, ⟨hseE.1, fun _ y hy => (hreg y hy).elim⟩,
    fun n hn => ?_, fun n _ hn => ?_, fun h => by simp [hUn] at h⟩
  · exact (update_facts σS x (HasBool.ffVal F)).2 n fun he => by subst he; simp [hSx] at hn
  · exact ((update_facts σS x (HasBool.ffVal F)).2 n fun he => hn (by simp [RE.vars, he])).symm

omit e hs in
/-- A run of the else arm's output of a laid-out `ite` that changes only the variables of `κE`
    among the names it binds keeps every bound variable of the context `κ`. -/
private theorem LaidCore.keepκ
    (e : LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
      Ex k Lab wc rdc s1 g s2 rT s3 κE rE?
      s4 Er s5 Tr s6)
    (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7 gm?
      st' rdc nonnil) (hE : resolveItems T Y Er.out.toList = .ok iE) {σa σb : SemanticStore P}
    {tr : List (Event P)} (hrun : MainRun F iE σa tr σb) (hfrm : Frame κE σa σb) {y : P.Ident}
    (hy : y ∈ RE.vars κ) (hb : (σa y).isSome) : σb y = σa y := by
  have hc := e.ctx
  cases κ with
  | top => simp [RE.vars] at hy
  | name q =>
    obtain ⟨hκE, -, -⟩ := hc
    exact List.mem_singleton.1 hy ▸ hs.of_keepQ hE hrun hκE
  | neg g0 | andNeg q0 g0 =>
    obtain ⟨x, hκE, hrE, -⟩ := hc
    have hyx : y ≠ x := fun he => (e.of_ctxNe hs hy).2.2.2 s1 s4 hs.nexts.1
      (he ▸ hs.pre.drawn x (.inr (.inr hrE)))
    exact hfrm y hb (by simpa [hκE, RE.vars] using hyx)

include iOp iLF iLFs iLV iIL in
/-- Off the loop-free path, a shadow run of a laid-out `ite` gives a run of its output
    (`OffPost`). -/
private theorem LaidEnv.offAll (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns)
    (hoff : OffInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σL)
    (hsh : ShS F (.ite (.det c) tss ess md) σs K) :
    OffPost F T Y Lc Ex st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k) items
      σL K := by
  have hnx := hs.nexts
  have hav := hs.avoids
  have hshT : ShL F tss σs (fun o => K (o.proj σs)) := shL_of_shB hsh.1
  have hscope : (if r.ax = true then S else scopeAfter S [.ite (.det c) tss ess md]) = S := by
    simp [e.ax, scopeAfter, Stmt.topInits]
  rcases e.out with ⟨hnil, hro, -⟩ | ⟨hnn, -, -, -, -⟩
  · obtain ⟨hTn, hEn, rfl, rfl, -⟩ := hs.nilParts hns hnil
    obtain rfl := resolve_isNil (by rw [hro]; rfl) e.res
    have hreg : ∀ x ∈ r.regs.toList, False := fun x hx => by simp [e.rn_regs hs hTn hEn] at hx
    have hT : resolveItems T Y Tr.out.toList = .ok [] := Rope.isNil_toList hTn ▸ rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, hshT'⟩ := (e.armTp hs hT).2.2 σs _ _ (e.offT hs hns
      hoff.defd hoff.gtyped hoff.fresh (preStore_two hs.pre.g_rT) nofun nofun
      (wfStore_update_bool (wfStore_update_bool hoff.canonL g (.inr rfl)) rT (.inr rfl))) hshT
    refine ⟨[], σL, .nil, nofun, ?_, fun _ _ _ => rfl, fun _ x hx => (hreg x hx).elim,
      fun _ _ _ _ _ hc => (hreg _ hc.2).elim, fun _ _ _ _ _ hc => (hreg _ hc.2).elim,
      ⟨fun hax => ?_, fun _ x hx => (hreg x hx).elim⟩⟩
    · rw [hscope]
      exact
        { canonL := hoff.canonL
          reach := hoff.reach
          bools := hoff.bools
          defd := fun x hx hv n hn => hoff.defd x hx (mem_contFV_cons.2 (.inr hv)) n
            (e.of_cur0 hs hx hn).2.2
          gtyped := hoff.gtyped
          fresh := of_freshPost hoff.fresh (fun y hy => e.whole.taken y hy) e.whole.avoid
            e.whole.next (fun x y h => e.whole.nm x y h) fun y hy => .inl hy }
    · exact (hshT'.1 e.axT).elim fun σs1 h => ⟨_, h⟩
  obtain ⟨ce, iRT, iGM, iSV, iT, iCP, iRS, iRE, iE, iMG, iU, hsp⟩ := e.split hnn
  obtain ⟨hce, hRT, hGM, hSV, hT, hCP, hRS, hRE, hE, hMG, hU, hitems⟩ := hsp
  have hκt : κ ≠ .top := fun h => by simpa [h, RE.Fails] using hoff.reach
  have hsrcS : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty := fun q hq => by
    obtain ⟨z, hzS, hzfv, hzn⟩ := e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)
    exact hoff.defd z hzS
      (mem_contFV_cons.2 (.inl (by simp [Block.freeVars, Stmt.freeVars, hzfv]))) _ hzn
  have hq1 : ∀ q ∈ ns, (σL q.1).isSome := fun q hq => (hsrcS q hq).elim fun _ h => by simp [h.1]
  obtain ⟨σB, hrun0, hCB, hB, -⟩ := e.preRunQ hs hns hoff.fresh hoff.canonL hRT hGM (iQM := [])
    (qm? := none) (by cases κ <;> simp only [Rope.toList_nil] <;> rfl) nofun nofun hSV
    (ev_kAnd_fails e.hF hoff.canonL hoff.reach hce
      (e.guardOff hs hoff) hoff.bools)
    (.inr rfl) hsrcS
  obtain ⟨trT, σ1, hrunT, hfeasT, hC1, hfr1, hgt1, hk1, hpre1, hsv1, hunb1, hsnT, hcfT, hcoT,
    hseT, hrT1, -⟩ := e.of_T hs hns hoff.defd hoff.gtyped hoff.fresh hq1 hB nofun nofun hCB hT hshT
  have hcpD : ∀ q ∈ ns, Drawn s6 s7 q.2.2 := fun q hq => (hns.drawn q hq).2.1
  obtain ⟨σR, hrunCR, hCR, hcR, hvR, hoR, htyC, hσ1cp, hgR, -, h0R'⟩ := e.ry_midRun hs hns
    hoff.fresh hsrcS hB hC1 hgt1 (fun n => mainRun_mono hrunT n) (fun n hn =>
      (hs.armT.writesW T Y iT hT σB trT σ1 hrunT n hn).imp_right fun h => (Option.some.inj h).symm)
    hCP hRS
  have hcpL : ∀ q ∈ ns, σL q.2.2 = none := fun q hq =>
    e.unbound hs hoff.fresh (.inr ((hcpD q hq).mono hnx.2.2.2.2.2))
  have hR1 : ∀ n, (∀ q ∈ ns, n ≠ q.2.2) → σR n = σ1 n := fun n hn => by
    rcases Classical.em (∃ q ∈ ns, n = q.1) with ⟨q, hq, rfl⟩ | hq
    · rw [hvR q hq, hk1 _ (hq1 q hq)]
    · exact hoR n fun q hq' => ⟨fun he => hq ⟨q, hq', he⟩, hn q hq'⟩
  have hkR : ∀ n, (σL n).isSome → σR n = σL n := fun n hn =>
    (hR1 n fun q hq he => by simp [he, hcpL q hq] at hn).trans (hk1 n hn)
  have hRcp : ∀ q ∈ ns, σR q.2.2 = σL q.1 := fun q hq => (hcR q hq).trans (hk1 _ (hq1 q hq))
  have h0R : ∀ x, rE? = some x → σR x = none := fun x hx => (h0R' x hx).1
  have hκb : ∀ y ∈ RE.vars κ, (σL y).isSome := fun y hy => by
    rcases hoff.bools y hy with h | h <;> simp [h]
  have hκR : κ.Fails F σR := of_failsCongr hoff.reach fun y hy => hkR y (hκb y hy)
  obtain ⟨σD, hrunD, hCD, hcase⟩ := rEiRun e.hF hCR h0R
    (.inr (.inl ⟨hκR, .inr hgR, fun y hy => (hkR y (hκb y hy)).symm ▸ hoff.bools y hy, rfl⟩)) hRE
  have hEoff : ∀ σE : SemanticStore P, WellFormedStore σE F →
      (∀ n, σE n = σR n ∨ (rE? = some n ∧ σE n = some (HasBool.ffVal F))) → κE.Fails F σE →
      (∀ y ∈ RE.vars κE, σE y = some (HasBool.ttVal F) ∨ σE y = some (HasBool.ffVal F)) →
      OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σE := fun σE hCE hdesc hreach hbools => by
    have hES := e.elseStore hs hns (.inr rfl) hgt1 hfr1 hR1 hdesc
    refine ⟨hCE, hreach, hbools, fun x hx hv n hn => ?_, hES.1, hES.2⟩
    · obtain ⟨w, hw, hty⟩ := hoff.defd x hx (contFV_else_sub hv) n (hs.cur5 hx hn).1
      refine ⟨w, (hdesc n).elim (fun h => by rw [h, hkR n (by simp [hw]), hw])
        fun ⟨h, _⟩ => by simp [e.unbound hs hoff.fresh (.inl (.inr (.inr h)))] at hw, hty⟩
  have hdesc : ∀ n, σD n = σR n ∨ (rE? = some n ∧ σD n = some (HasBool.ffVal F)) := fun n => by
    rcases hcase with ⟨-, h, -⟩ | ⟨x, hx, -, h⟩ <;> rw [h]
    · exact .inl rfl
    · exact (update_cases σR x (HasBool.ffVal F) n).imp_right fun ⟨he, h⟩ => ⟨hx ▸ he ▸ rfl, h⟩
  have hc' : (κE.Fails F σD ∧ ∀ y ∈ RE.vars κE,
        σD y = some (HasBool.ttVal F) ∨ σD y = some (HasBool.ffVal F)) ∨
      ∃ x, κE = .name x ∧ σD x = none ∧ Er.out.isNil = true ∧
        (laidU κ κE rT Tr Er d).isNil = true ∧
        ∀ n, SemanticStore.update σD x (HasBool.ffVal F) n = σR n ∨
          (rE? = some n ∧
            SemanticStore.update σD x (HasBool.ffVal F) n = some (HasBool.ffVal F)) := by
    have hc := e.ctx
    cases κ with
    | top => exact absurd rfl hκt
    | name q =>
      obtain ⟨rfl, hrE, -⟩ := hc
      rcases hcase with ⟨-, h, -⟩ | ⟨x, hx, -⟩
      · rw [h]
        have hq : σR q = some (HasBool.ffVal F) :=
          (hkR q (hκb q (by simp [RE.vars]))).trans hoff.reach
        exact .inl ⟨.inl ⟨hq, hgR ▸ rfl⟩, by simp [RE.vars, hq, hgR]⟩
      · exact nomatch hrE ▸ hx
    | neg g0 | andNeg q0 g0 =>
      obtain ⟨x, rfl, rfl, -⟩ := hc
      have hxff : SemanticStore.update σR x (HasBool.ffVal F) x = some (HasBool.ffVal F) :=
        (update_facts σR x (HasBool.ffVal F)).1
      rcases hcase with ⟨-, h, hr | hb⟩ | ⟨x', hx', -, h⟩ <;> rw [h]
      · cases hr
      · obtain ⟨hEn, hUn⟩ : _ ∧ _ := Bool.and_eq_true _ _ ▸ hb
        exact .inr ⟨x, rfl, h0R x rfl, hEn, hUn, fun n =>
          (update_cases σR x (HasBool.ffVal F) n).imp_right fun ⟨he, h⟩ => ⟨he ▸ rfl, h⟩⟩
      · cases hx'
        exact .inl ⟨hxff, by simp [RE.vars, hxff]⟩
  obtain ⟨trE, σEr, σEo, hrunE, hfeasE, hCEr, hoffE, hfrmE, hsnE, hcfE, hcoE, hseE, hEo1, hEo2,
    hEo3⟩ := e.offE hs hE (shL_of_shB hsh.2) hCD hEoff hdesc hc'
  have hfE : ∀ n, (σD n).isSome → n ≠ g → (∀ x, rE? = some x → n ≠ x) → n ∉ RE.vars κ →
      σEr n = σD n := fun n hb hg hr hk => hfrmE n hb fun hm =>
    (e.of_κEvars' hm).elim hg fun h => h.elim (fun h => hr n h rfl) hk
  have hgL : σL g = none := e.unbound hs hoff.fresh (.inl (.inl rfl))
  have hDR : ∀ n, (∀ x, rE? = some x → n ≠ x) → σD n = σR n := fun n hn => by
    rcases hcase with ⟨-, h, -⟩ | ⟨x, hx, -, h⟩ <;> rw [h]
    exact (update_facts σR x (HasBool.ffVal F)).2 n (Ne.symm (hn x hx))
  have hkE : ∀ n, (σL n).isSome → n ∉ RE.vars κ → σEr n = σL n := fun n hn hnk => by
    have hnr : ∀ x, rE? = some x → n ≠ x := fun x hx he => by
      simp [he, e.unbound hs hoff.fresh (.inl (.inr (.inr hx)))] at hn
    have hD : σD n = σL n := (hDR n hnr).trans (hkR n hn)
    exact (hfE n (by rw [hD]; exact hn) (fun h => by simp [h, hgL] at hn) hnr hnk).trans hD
  have hq1κ : ∀ q ∈ ns, q.1 ∉ RE.vars κ := fun q hq hk => by
    obtain ⟨z, hzS, -, hzn⟩ := e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)
    exact (e.of_ctxNe hs hk).2.2.1 z hzS hzn
  have hEq1 : ∀ q ∈ ns, σEr q.1 = σL q.1 := fun q hq => hkE q.1 (hq1 q hq) (hq1κ q hq)
  have hEq2 : ∀ q ∈ ns, σEr q.2.2 = σL q.1 := fun q hq => by
    have hcd := hcpD q hq
    have hnr : ∀ x, rE? = some x → q.2.2 ≠ x := fun x hx => (hs.saveNe hcd).2.2.2 x hx
    have hD : σD q.2.2 = σL q.1 := (hDR _ hnr).trans (hRcp q hq)
    exact (hfE _ (by rw [hD]; exact hq1 q hq) (hs.saveNe hcd).1 hnr
      fun h => (e.of_ctxNe hs h).2.2.2 s6 s7 (by omega) hcd).trans hD
  have hgmE : ∀ x, gm? = some x → σEr x = some (HasBool.ffVal F) := fun x hx => by
    have hd := hs.aft.gmDrawn x hx
    have hnc : ∀ q ∈ ns, x ≠ q.2.2 := fun q hq he => (hcpD q hq).disj (he ▸ hd) (Nat.le_refl _)
    have hnr : ∀ y, rE? = some y → x ≠ y := fun y hy he =>
      (hs.pre.drawn y (.inr (.inr hy))).disj (he ▸ hd) (by omega)
    have hD : σD x = some (HasBool.ffVal F) := (hDR x hnr).trans ((hR1 x hnc).trans
      (hpre1 x (List.mem_cons_of_mem _ (Option.mem_toList.2 hx))))
    exact (hfE x (by simp [hD]) (fun h => (hs.pre.drawn g (.inl rfl)).disj (h ▸ hd) (by omega))
      hnr fun h => (e.of_ctxNe hs h).2.2.2 s7 st' (by omega) hd).trans hD
  have hκL : ∀ y ∈ RE.vars κ, σEr y = σL y := fun y hy => by
    have hD : σD y = σL y := (hDR y fun x hx he => (e.of_ctxNe hs hy).2.2.2 s1 s4 hnx.1
      (he ▸ hs.pre.drawn x (.inr (.inr hx)))).trans (hkR y (hκb y hy))
    exact (e.keepκ hs hE hrunE hfrmE hy (hD ▸ hκb y hy)).trans hD
  have hrEr : (laidU κ κE rT Tr Er d).isNil = false →
      σEr rT = some (HasBool.ffVal F) := fun hUf => by
    obtain ⟨hrgm, hrsv, hrg⟩ := hs.rTFacts hns
    have hnc : ∀ q ∈ ns, rT ≠ q.2.2 := fun q hq he =>
      (hs.pre.drawn rT (.inr (.inl rfl))).disj (he ▸ hcpD q hq) (by omega)
    have hnr : ∀ x, rE? = some x → rT ≠ x := fun x hx he => (hs.pre.rE_ne x hx).2 he.symm
    have hD : σD rT = some (HasBool.ffVal F) :=
      (hDR rT hnr).trans ((hR1 rT hnc).trans (hrT1 (by simp [hUf])))
    rw [hfE rT (by simp [hD]) hrg hnr fun h => (e.of_ctxNe hs h).2.2.2 s1 s4 hnx.1
      (hs.pre.drawn rT (.inr (.inl rfl))), hD]
  have hEf : (laidU κ κE rT Tr Er d).isNil = false → κE.Fails F σEr := fun hUf =>
    of_failsCongr hoffE.reach fun y _ => by rw [hEo3 hUf]
  obtain ⟨trU, σF, hrunU, hCF, hvalF, hothF, hbU, -, hUnil, hUnn⟩ :=
    e.postRun hs hns false hoff.fresh hq1 hCEr hEq2 (fun q hq => by
      obtain ⟨w, hw, hty⟩ := hsrcS q hq
      obtain ⟨ty, hty0⟩ := htyC q hq
      exact ⟨ty, w, w, hw, (hEq1 q hq).trans hw, hty ty hty0, hty ty hty0⟩) hgmE
      (fun hUf => .inr (hrEr hUf)) (fun hUf => .inr (hEf hUf))
      (fun hUf y hy => by rw [← hEo3 hUf]; exact hoffE.bools y hy)
      (fun y hy => hκL y hy ▸ hoff.bools y hy) hMG hU
  obtain ⟨rfl, hfF⟩ : trU = [] ∧ κ.Fails F σF := by
    cases hUf : (laidU κ κE rT Tr Er d).isNil
    · obtain ⟨h1, -, h3⟩ := (hUnn hUf).2 hκt
      exact ⟨h1, h3 fun h => h.elim
        (fun h => HasBool.ttVal_ne_ffVal F (Option.some.inj (h.symm.trans
        (hrEr hUf)))) (·.not_fails (hEf hUf))⟩
    · obtain ⟨rfl, hk⟩ := hUnil hUf
      exact ⟨rfl, of_failsCongr hoff.reach fun y hy => (hk y hy).trans (hκL y hy)⟩
  have hFEr : ∀ n, n ∉ RE.vars κ → σF n = σEr n := fun n hnκ => by
    rcases Classical.em (∃ q ∈ ns, liveBefore s6 q.1 s4.clock ∧ n = q.1) with ⟨q, hq, hl, rfl⟩ | hm
    · rw [hvalF q hq hl, hEq1 q hq, ite_self]
    · exact hothF n (fun q hq hl he => hm ⟨q, hq, hl, he⟩) hnκ
  have hTk : ∀ n ∈ wDecls Tr.out.toList, (Drawn s5 s6 n ∨ AvoidedIfFresh st0 n) ∨
      ∃ y, s5.nm[y]? = some n := fun n hn => (hs.armT.declW hn).elim (.inl ∘ .inl) fun h =>
    h.elim .inr fun h => .inl (.inr (e.avoidArm (.inl h)))
  have hfinT : ∀ n ∈ wDecls Tr.out.toList, (σ1 n).isSome → σF n = σ1 n := fun n hn hb => by
    obtain ⟨hnc, hng, hnr⟩ : (∀ q ∈ ns, n ≠ q.2.2) ∧ n ≠ g ∧ ∀ x, rE? = some x → n ≠ x := by
      rcases hTk n hn with hk | ⟨y, hy⟩
      · have hd := not_drawn_of n s1 s4 s5 s6 hk hav.1 (.inl hnx.2.2.1)
        exact ⟨fun q hq he => not_drawn_of n s6 s7 s5 s6 hk hav.2.2.2.1 (.inr (Nat.le_refl _))
          (he ▸ hcpD q hq), fun h => hd (h ▸ hs.pre.drawn g (.inl rfl)),
          fun x hx he => hd (he ▸ hs.pre.drawn x (.inr (.inr hx)))⟩
      · obtain ⟨b, j, h1, h2⟩ := dl_nmBelow hs.wf5 hy
        exact ⟨fun q hq he => (hcpD q hq).not_below ⟨b, j, he ▸ h1, by omega⟩,
          fun h => (hs.preNm (.inl rfl) y).2.1 (h ▸ hy),
          fun x hx he => (hs.preNm (.inr (.inr hx)) y).2.1 (he ▸ hy)⟩
    have hnκ : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).1 hn
    have hD : σD n = σ1 n := (hDR n hnr).trans (hR1 n hnc)
    rw [hFEr n hnκ, hfE n (by rw [hD]; exact hb) hng hnr hnκ, hD]
  have hframe : Frame κ σL σF := fun y hy hny => by rw [hFEr y hny, hkE y hy hny]
  have hfr0 : FreshInv Lc Ex st0 σL := of_freshPost hoff.fresh (fun y hy => e.whole.taken y hy)
    e.whole.avoid e.whole.next (fun x y h => e.whole.nm x y h) fun y hy => .inl hy
  have hT1 : ∀ n, (σ1 n).isSome → n ∉ RE.vars κE → n ∉ RE.vars κ → σF n = σ1 n :=
    fun n hb hnκE hnκ => by
      have hnc : ∀ q ∈ ns, n ≠ q.2.2 := fun q hq he => by simp [he, hσ1cp q hq] at hb
      have hnr : ∀ x, rE? = some x → n ≠ x := fun x hx he => by
        simp [← hR1 _ hnc, he ▸ h0R _ hx] at hb
      have hD : σD n = σ1 n := (hDR n hnr).trans (hR1 n hnc)
      rw [hFEr n hnκ, hfrmE n (by rw [hD]; exact hb) hnκE, hD]
  have hkT : ∀ n ∈ wDecls Tr.out.toList, σF n = σ1 n := fun n hn =>
    hfinT n hn (mainRun_binds _ _ hT hrunT n hn)
  have hkE : ∀ n ∈ wDecls Er.out.toList, σF n = σEr n := fun n hn =>
    hFEr n fun hκ => (e.re_κNotE hs hκ).2 hn
  have hcar : CarryFF F T Y r st' σF ∧ CarryOK F T Y r st' σF := by
    refine ⟨fun k i n v xB hr => ?_, fun k i n v xB hr => ?_⟩
    · exact (e.of_regCases hs hr).elim
        (fun h => hs.armT.sel e.hF hCF hC1 hkT h (hcfT _ _ _ _ _ h))
        fun ⟨i', h⟩ => hs.armE.sel e.hF hCF hCEr hkE h (hcfE _ _ _ _ _ h)
    rcases e.of_regCases hs hr with h | ⟨i', h⟩
    · obtain ⟨hsel, hty, ⟨w, hw, ht⟩, w', hw', ht'⟩ := hcoT _ _ _ _ _ h
      have hn := (hs.armT.carryTgt k i n v xB h).imp_left fun ⟨z, hz, h⟩ =>
        (⟨z, hz, (hs.cur6 z).symm.trans h⟩ : ∃ z ∈ S, curName st' z = some n)
      have hκ : n ∉ RE.vars κ := hn.elim (fun ⟨_, hz, h⟩ => e.re_curNotκ hs hz h) fun h =>
        (e.re_TdeclFacts hs h).2.2.2.2.2
      refine ⟨hsel.imp (hs.armT.sel e.hF hCF hC1 hkT h) (hs.armT.sel e.hF hCF hC1 hkT h), hty,
        ⟨w, (hT1 n (by simp [hw]) (e.of_notκE hs hκ hn) hκ).trans hw, ht⟩, w',
        (hkT _ (hs.armT.regs _ h.2)).trans hw', ht'⟩
    · obtain ⟨hsel, hty, ⟨w, hw, ht⟩, w', hw', ht'⟩ := hcoE _ _ _ _ _ h
      have hκ : n ∉ RE.vars κ := (hs.armE.carryTgt _ _ n v xB h).elim
        (fun ⟨_, hz, h⟩ => e.re_curNotκ hs hz (hs.cur5 hz h).1) fun hd hκ => (e.re_κNotE hs hκ).2 hd
      exact ⟨hsel.imp (hs.armE.sel e.hF hCF hCEr hkE h) (hs.armE.sel e.hF hCF hCEr hkE h), hty,
        ⟨w, (hFEr n hκ).trans hw, ht⟩, w', (hkE _ (hs.armE.regs _ h.2)).trans hw', ht'⟩
  refine ⟨trT ++ (trE ++ []), σF, by wp_chain [hitems],
    Trace.AssumptionsHold.append hfeasT (Trace.AssumptionsHold.append hfeasE nofun), ?_, hframe,
    fun l x hx hp _ => ?_, hcar.1, hcar.2, ⟨fun _ => ?_, fun l x hx hp hl => ?_⟩⟩
  · rw [hscope]
    refine ⟨hCF, hfF, hbU, fun x hx hv n hn => ?_, fun n w hw hY ty hty => ?_, fun y hy => ?_⟩
    · obtain ⟨w, hw, hty⟩ := hoff.defd x hx (mem_contFV_cons.2 (.inr hv)) n (e.of_cur0 hs hx hn).2.2
      have hnκ : n ∉ RE.vars κ := fun h => (e.of_ctxNe hs h).2.2.1 x hx (e.of_cur0 hs hx hn).2.2
      exact ⟨w, (hframe n (by simp [hw]) hnκ).trans hw, hty⟩
    · by_cases hnκ : n ∈ RE.vars κ
      · exact rn_boolTyped (hoff.bools n hnκ) (fun w0 h => hoff.gtyped n w0 h hY ty hty)
          (hbU n hnκ) hw
      · rw [hFEr n hnκ] at hw
        exact hoffE.gtyped n w (by rw [hEo1 n (by simp [hw]), hw]) hY ty hty
    · by_cases hyκ : y ∈ RE.vars κ
      · exact hfr0 y (hκb y hyκ)
      · rw [hFEr y hyκ] at hy
        exact e.fresh0 hs hoffE.fresh y (by rw [hEo1 y hy]; exact hy)
  · rcases List.mem_append.1 (e.regs ▸ hx) with hx | hx
    · have h := hsnT l x hx (hs.aft.pending ▸ hp) (by simp)
      rw [hfinT x (hs.armT.regs x hx) (by simp [h]), h]
    · exact hFEr x (fun h => (e.of_ctxNe hs h).2.1 (hs.armE.regs x hx)) ▸
        hsnE l x hx (e.pendE hs hx hp) (by simp)
  · exact (hseT.1 e.axT).elim fun _ h => ⟨_, h⟩
  · rcases List.mem_append.1 (e.regs ▸ hx) with hx | hx
    · exact (hseT.2 l x hx (hs.aft.pending ▸ hp) hl).elim fun _ h => ⟨_, h⟩
    · exact (hseE.2 l x hx (e.pendE hs hx hp) hl).elim fun _ h => ⟨_, h⟩

end Parts2b

end -- public section

end WP
end Imperative

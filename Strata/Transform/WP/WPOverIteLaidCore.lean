/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
public import Strata.Transform.WP.WPOverEmit
public import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverFacts
import Strata.Transform.WP.WPOverTyped
public import Strata.Transform.WP.WPOverEffects
public import Strata.Transform.WP.WPReads
import Strata.DL.Imperative.BigStep.StoreAgree

/-! # The walk of a laid-out `ite` and the setting of its simulation

The walk of an `ite` after which an obligation follows (laid out: guard, arms under their reach
contexts, saves, restores, copies and merges) is inverted (`LaidRunAx`): the guard's renaming,
the guard `g`, the then-arm reach `rT`, the else-arm context, the arms' walks and the rest of the
walk (`LaidTailAx`, `LaidTailRest`).  When no arm always exits (`LaidEnv`), the output is the guard
followed by the parts `laidParts` (then-arm reach, merge guard, saves, then arm, copies,
restores, else-arm reach, else arm, merges, reach update); when an arm always exits, the parts
`laidPartsAx` add the copy `qm` of the enclosing context, the saves, copies and restores around
the always-exiting arms (step 3b), the copy `rEm` of the else-arm reach, and carried merges.

The simulation through either shape rests on the setting common to both (`LaidCore`,
`LaidStates`): the facts of the arms' walks (`ArmFacts`), and the arms' simulation properties
instantiated at the intermediate walk states (`LaidCore.armTp`, `LaidCore.armEp`).

Key definitions: `LaidRunAx`, `LaidTailAx`, `LaidTailRest`, `laidParts`, `laidPartsAx`,
`ArmFacts`, `LaidCore`, `LaidEnv`, `LaidStates`. -/

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


omit iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs iLV in
/-- After updating `x` to `v`, a variable keeps its value, or it is `x` and holds `v`. -/
private theorem update_cases (σ : SemanticStore P) (x : P.Ident) (v : P.Val) (n : P.Ident) :
    SemanticStore.update σ x v n = σ n ∨ (x = n ∧ SemanticStore.update σ x v n = some v) := by
  by_cases h : n = x <;> simp [SemanticStore.update, h]

omit iLB iHI iLI iOp iLF iLFs iLV in
/-- An empty sequence of output items resolves to the empty list. -/
private theorem resolve_isNil {s : Rope (WItem P)} {is : List (Item P)} (hn : s.isNil = true)
    (h : resolveItems T Y s.toList = .ok is) : is = [] :=
  (Except.ok.inj (Rope.isNil_toList hn ▸ h : resolveItems T Y [] = .ok is)).symm

/-! ## The walk of a laid-out `ite` -/

section

omit iLI iWL iOp iLF iLFs iLV

include iWL in
/-- `saveRestore` of no variable emits nothing and keeps the state. -/
private theorem saveRestore_nil_run (s : WSt P) :
    (saveRestore (P := P) []).run s = .ok ((.nil, .nil, .nil, []), s) := (rfl)

/-- The reach update of a laid-out `ite`: when an arm may exit the `ite`, the context `κ` is
    made `rT ∨ κE` (assumed under `top`). -/
@[expose] def laidU (κ κE : RE P) (rT : P.Ident) (T E : WRes P) (d : Nat) : Rope (WItem P) :=
  if (leOpt T.minT d || leOpt E.minT d) = true then
    match κ with
    | .top => .one (.assume joinLabel ((WExpr.var rT).or (kExpr κE)) .empty)
    | κ => setReach κ ((WExpr.var rT).or (kExpr κE))
  else .nil

/-- The merges of a laid-out `ite` whose arms do not always exit: for each variable `x` saved
    around the then arm and live after the `ite`, with copy `xT`, `x := ite(gm, xT, x)` when the
    else arm assigns `x`, `x := xT` otherwise. -/
@[expose] def laidMerges (gm? : Option P.Ident) (EA : Std.HashSet P.Ident)
    (liveM : List (P.Ident × P.Ident)) : Rope (WItem P) :=
  liveM.foldl (fun acc x => acc.app (.one (.set x.1 (some (if EA.contains x.1 = true then
    WExpr.ite (match gm? with | some y => .var y | none => .lit false) (.var x.2) (.var x.1)
    else .var x.2))))) .nil

/-- The parts after the guard of the output of a laid-out `ite` whose arms do not always exit,
    in program order: the then-arm reach `rT`, the merge guard `gm`, the saves, the then arm,
    the copies, the restores, the else-arm reach `rE`, the else arm, the merges, the reach
    update. -/
@[expose] def laidParts (κ : RE P) (g rT : P.Ident) (rE? gm? : Option P.Ident)
    (sv cp rs : Rope (WItem P)) (liveM : List (P.Ident × P.Ident)) (T E : WRes P)
    (U : Rope (WItem P)) : List (Rope (WItem P)) :=
  [if (T.out.isNil && U.isNil) = true then .nil
    else .one (.init rT (.known HasBool.boolTy) (some (.var g))),
   match gm? with
   | some x => .one (.init x (.known HasBool.boolTy) (some (.var g)))
   | none => .nil,
   sv, T.out, cp, rs,
   match rE? with
   | some r => if (E.out.isNil && U.isNil) = true then .nil
     else .one (.init r (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)))
   | none => .nil,
   E.out, laidMerges gm? E.A liveM, U]

/-- The else-arm context of a laid-out `ite` under `κ` with guard `g` (walk state `s3` before
    it is chosen, `s4` after): `neg g` under `top`, `andNeg q g` under `name q`, otherwise a fresh
    Boolean `rE`. -/
@[expose] def LaidCtx (κ : RE P) (g : P.Ident) (s3 : WSt P) (κE : RE P) (rE? : Option P.Ident)
    (s4 : WSt P) : Prop :=
  match κ with
  | .top => κE = .neg g ∧ rE? = none ∧ s4 = s3
  | .name q => κE = .andNeg q g ∧ rE? = none ∧ s4 = s3
  | _ => ∃ rE, κE = .name rE ∧ rE? = some rE ∧ (wFreshBool "r").run s3 = .ok (rE, s4)


/-- The variables saved around the then arm when it always exits (step 3b): those it assigns
    that are live after the `ite` (before the clock `t0` of the arms' walks) or read by the else
    arm. -/
@[expose] def laidCT (T E : WRes P) (st : WSt P) (t0 : Nat) : List P.Ident :=
  if T.ax then T.A.fold (fun l x =>
      if liveBefore st x t0 || E.R.contains x then x :: l else l) [] else []

/-- The variables saved around the else arm when it always exits (step 3b): those it assigns
    that are live after the `ite`. -/
@[expose] def laidCE (E : WRes P) (st : WSt P) (t0 : Nat) : List P.Ident :=
  if E.ax then E.A.fold (fun l x => if liveBefore st x t0 then x :: l else l) [] else []

/-- The carried copies of an always-exiting arm `B` (copy pairs `cps`): those of variables live
    after its innermost target block. -/
@[expose] def laidCarry (B : WRes P) (st : WSt P) (cps : List (P.Ident × P.Ident)) :
    List (P.Ident × P.Ident) := carryOf st cps B.tgt.max?

/-- Whether a laid-out `ite` draws the merge guard `gm`: a merge reads it or a carry selects
    with it. -/
@[expose] def laidNeedGm (κ : RE P) (E : WRes P) (liveM carryT carryE : List (P.Ident × P.Ident)) :
    Bool :=
  (liveM.any fun (x, _) => E.A.contains x && !E.ax) || !carryT.isEmpty ||
    (!carryE.isEmpty && match κ with | .top | .name _ => true | _ => false)

/-- The copy `qm` of the enclosing context `name q` of a laid-out `ite`, when drawn, as a list. -/
@[expose] def laidQm (κ : RE P) (qm? : Option P.Ident) : List P.Ident :=
  match qm? with
  | some x => match κ with | .name _ => [x] | _ => []
  | none => []

/-- The carried merges a laid-out `ite` registers in the carries map `c`: the then arm's at its
    innermost target with selector `eT`, then the else arm's at its innermost target with selector
    `eE`, newest first. -/
@[expose] def laidCarries (c : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident)))
    (T E : WRes P) (carryT carryE : List (P.Ident × P.Ident)) (eT eE : WExpr P) :
    Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident)) :=
  carryIns eE carryE (carryIns eT carryT c T.tgt.max?) E.tgt.max?

/-- The merges of a laid-out `ite` (`x := ite(gm, xT, x)` when the else arm assigns `x` and does
    not always exit, `x := xT` otherwise). -/
@[expose] def laidMergesAx (gm? : Option P.Ident) (E : WRes P) (liveM : List (P.Ident × P.Ident)) :
    Rope (WItem P) :=
  liveM.foldl (fun acc (x, xT) =>
    acc.app (.one (.set x (some (if E.A.contains x && !E.ax then
      .ite (optVar gm?) (.var xT) (.var x)
      else .var xT))))) .nil

/-- The parts after the guard of the output of a laid-out `ite`, in program order: the then-arm
    reach, the merge guard, the copy `qm` of the enclosing context, the saves of step 3 and of
    step 3b around the then arm, the then arm, its copies and restores, the else-arm reach and its
    copy `rEm`, the saves of step 3b around the else arm, the else arm, its copies and restores,
    the merges and the reach update. -/
@[expose] def laidPartsAx (κ : RE P) (g rT : P.Ident) (rE? gm? qm? rEm? : Option P.Ident)
    (sv3 cp3 rs3 svT cpT rsT svE cpE rsE : Rope (WItem P)) (liveM : List (P.Ident × P.Ident))
    (T E : WRes P) (U : Rope (WItem P)) : List (Rope (WItem P)) :=
  [if T.out.isNil && U.isNil then .nil
    else .one (.init rT (.known HasBool.boolTy) (some (.var g))),
   match gm? with
   | some x => .one (.init x (.known HasBool.boolTy) (some (.var g)))
   | none => .nil,
   match κ, qm? with
   | .name q, some x => .one (.init x (.known HasBool.boolTy) (some (.var q)))
   | _, _ => .nil,
   sv3, svT, T.out, cp3, cpT, rs3, rsT,
   match rE? with
   | some r => if E.out.isNil && U.isNil && rEm?.isNone then .nil
     else .one (.init r (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)))
   | none => .nil,
   match rE?, rEm? with
   | some r, some x => .one (.init x (.known HasBool.boolTy) (some (.var r)))
   | _, _ => .nil,
   svE, E.out, cpE, rsE, laidMergesAx gm? E liveM, U]

/-- The merges of a laid-out `ite` are those of `laidMerges` over the else arm's assignments when
    it does not always exit, over no assignment otherwise. -/
private theorem laidMergesAx_eq (gm? : Option P.Ident) (E : WRes P) (l : List (P.Ident × P.Ident)) :
    laidMergesAx gm? E l = laidMerges gm? (if E.ax then {} else E.A) l := by
  cases h : E.ax <;> cases gm? <;> simp [laidMergesAx, laidMerges, h, optVar]

/-- The end of the walk of a laid-out `ite` after the saves (from the state `s7E`, with the
    saves, copies, restores and copy pairs `sv3 cp3 rs3 cps3` of step 3 and `svT cpT rsT cpsT`,
    `svE cpE rsE cpsE` of step 3b): the merge guard, the copies `qm` of the enclosing context and
    `rEm` of the else-arm reach when the else arm carries merges, the carried merges registered,
    and the output: nothing when every part is empty, otherwise the guard followed by the parts,
    the live set gaining the guard's reads. -/
@[expose] def LaidTailRest (κ : RE P) (d : Nat) (wc : WExpr P) (rdc : List P.Ident)
    (g rT : P.Ident) (κE : RE P) (rE? : Option P.Ident) (t0 : Nat) (E T : WRes P)
    (s6 : WSt P) (sv3 cp3 rs3 svT cpT rsT svE cpE rsE : Rope (WItem P))
    (cps3 cpsT cpsE : List (P.Ident × P.Ident)) (s7E : WSt P) (r : WRes P) (st' : WSt P) :
    Prop :=
  ∃ gm? s8,
    ((laidNeedGm κ E (cps3.filter fun p => liveBefore s6 p.1 t0) (laidCarry T s6 cpsT)
        (laidCarry E s6 cpsE) = true ∧ ∃ x, gm? = some x ∧ (wFreshBool "g").run s7E = .ok (x, s8)) ∨
      (laidNeedGm κ E (cps3.filter fun p => liveBefore s6 p.1 t0) (laidCarry T s6 cpsT)
        (laidCarry E s6 cpsE) = false ∧ gm? = none ∧ s8 = s7E)) ∧
  ∃ qm? s9,
    (((∃ q, κ = .name q) ∧ (laidCarry E s6 cpsE).isEmpty = false ∧
        ∃ x, qm? = some x ∧ (wFreshBool "r").run s8 = .ok (x, s9)) ∨
      (¬ ((∃ q, κ = .name q) ∧ (laidCarry E s6 cpsE).isEmpty = false) ∧ qm? = none ∧ s9 = s8)) ∧
  ∃ rEm? s10,
    ((rE?.isSome ∧ (laidCarry E s6 cpsE).isEmpty = false ∧
        ∃ x, rEm? = some x ∧ (wFreshBool "r").run s9 = .ok (x, s10)) ∨
      (¬ (rE?.isSome ∧ (laidCarry E s6 cpsE).isEmpty = false) ∧ rEm? = none ∧ s10 = s9)) ∧
  r.ax = (T.ax && E.ax) ∧ r.drop = false ∧
  r.regs.toList = T.regs.toList ++ E.regs.toList ++
    ((laidCarry T s6 cpsT).map (·.2) ++ (laidCarry E s6 cpsE).map (·.2)) ∧
  let cs := laidCarries s10.carries T E (laidCarry T s6 cpsT) (laidCarry E s6 cpsE)
    (optVar gm?) (elseGuard κ gm? qm? rEm?)
  let s11 := { s10 with carries := cs }
  let parts := laidPartsAx κ g rT rE? gm? qm? rEm? sv3 cp3 rs3 svT cpT rsT svE cpE rsE
    (cps3.filter fun p => liveBefore s6 p.1 t0) T E (laidU κ κE rT T E d)
  (parts.all Rope.isNil = true ∧ r.out = .nil ∧ st' = s11 ∨
   parts.all Rope.isNil = false ∧
    r.out.toList = .init g (.known HasBool.boolTy) (some (kAnd κ wc)) :: parts.flatMap Rope.toList ∧
    r.sk = [.ite g T.sk E.sk] ∧ r.hasObl = (T.hasObl || E.hasObl) ∧
    r.A = unionSet (if T.ax then {} else T.A) (if E.ax then {} else E.A) ∧
    r.R = unionSet (unionSet T.R E.R) (Std.HashSet.ofList rdc) ∧
    (liveAdd (rdc ++ RE.vars κ)).run s11 = .ok ((), st'))

/-- The rest of the walk of a laid-out `ite` from the state `s6` after the arms: the saves of
    step 3 and of step 3b around each arm, then the end (`LaidTailRest`). -/
@[expose] def LaidTailAx (κ : RE P) (d : Nat) (wc : WExpr P) (rdc : List P.Ident)
    (g rT : P.Ident) (κE : RE P) (rE? : Option P.Ident) (t0 : Nat) (E T : WRes P)
    (s6 : WSt P) (r : WRes P) (st' : WSt P) : Prop :=
  ∃ sv3 cp3 rs3 cps3 s7, (saveRestore (if T.ax then [] else interSet T.A E.R)).run s6 =
      .ok ((sv3, cp3, rs3, cps3), s7) ∧
  ∃ svT cpT rsT cpsT s7T, (saveRestore (laidCT T E s6 t0)).run s7 =
      .ok ((svT, cpT, rsT, cpsT), s7T) ∧
  ∃ svE cpE rsE cpsE s7E, (saveRestore (laidCE E s6 t0)).run s7T =
      .ok ((svE, cpE, rsE, cpsE), s7E) ∧
  LaidTailRest κ d wc rdc g rT κE rE? t0 E T s6 sv3 cp3 rs3 svT cpT rsT svE cpE rsE cps3 cpsT
    cpsE s7E r st'

/-- The walk of a laid-out `ite` with the rest of the walk described in every case
    (`LaidTailAx`). -/
@[expose] def LaidRunAx (κ : RE P) (d : Nat) (c : P.Expr) (tss ess : PStmts P) (st0 : WSt P)
    (r : WRes P) (st' : WSt P) : Prop :=
  ∃ wc rdc s1 g s2 rT s3 κE rE? s4 E s5 T s6,
    (wRen c).run st0 = .ok ((wc, rdc), s1) ∧ (wFreshBool "g").run s1 = .ok (g, s2) ∧
    (wFreshBool "r").run s2 = .ok (rT, s3) ∧ LaidCtx κ g s3 κE rE? s4 ∧
    (wpList κE d true ess).run s4 = .ok (E, s5) ∧
    (wpList (.name rT) d true tss).run s5 = .ok (T, s6) ∧
    LaidTailAx κ d wc rdc g rT κE rE? s4.clock E T s6 r st'

/-- An optional draw whose name is present exactly when `C` holds draws a name when `C` holds and
    keeps the state otherwise. -/
private theorem OptDraw.cond {b : String} {s s' : WSt P} {o : Option P.Ident} {C : Prop}
    (h : OptDraw b s s' o) (hc : o.isSome ↔ C) :
    (C ∧ ∃ x, o = some x ∧ (wFreshBool b).run s = .ok (x, s')) ∨ (¬ C ∧ o = none ∧ s' = s) := by
  cases o <;> simp_all [OptDraw]

include iWL in
/-- The walk of a laid-out `ite`, every arm-exit case included, decomposes as `LaidRunAx` says. -/
private theorem laid_run_inv_ax (h : (wpIteLaid κ d c tss ess).run st0 = .ok (r, st')) :
    LaidRunAx κ d c tss ess st0 r st' := by
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc h5 h6 h7 h8 h9 hgm hg hqm hq
    hrm hr hEnd => ⟨wc, rdc, s1, g, s2, rT, s3, κE, rE, s4, E, s5, T, s6, h1, h2, h3, ?_, h5, h6,
    sv3, cp3, rs3, cps3, s7, h7, svT, cpT, rsT, cpsT, s8, h8, svE, cpE, rsE, cpsE, s9, h9, gm, s10,
    (hgm.cond hg).imp id fun ⟨hn, hs⟩ => ⟨Bool.eq_false_iff.2 hn, hs⟩, qm, s11,
    (hqm.cond hq).imp (fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩) id, rEm, s12,
    (hrm.cond hr).imp (fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩) id, ?_⟩
  · rcases hc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨⟨q, rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨ht, hn⟩, x, rfl, rfl, hx⟩
    iterate 2 exact ⟨rfl, rfl, rfl⟩
    cases κ <;> first | exact absurd rfl ht | exact absurd rfl (hn _) | exact ⟨x, rfl, rfl, hx⟩
  rcases hEnd with ⟨hb, rfl, rfl⟩ | ⟨hb, hl, rfl⟩
  all_goals refine ⟨rfl, rfl, by rw [Rope.toList_app, Rope.toList_app, Rope.toList_ofList]; rfl, ?_⟩
  · exact .inl ⟨(Rope.isNil_foldl_app' _ _).symm.trans hb, rfl, rfl⟩
  · refine .inr ⟨(Rope.isNil_foldl_app' _ _).symm.trans hb, ?_, rfl, rfl, rfl, rfl, hl⟩
    rw [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil, List.nil_append]
    rfl

/-- An arm with no copy pairs carries no copy. -/
private theorem laidCarry_nil (B : WRes P) (st : WSt P) : laidCarry B st [] = [] := by
  unfold laidCarry carryOf
  split <;> rfl

/-- The carried merges at a depth of a laid-out `ite`'s carries map: the else arm's new merges
    (when its innermost target is that depth), then the then arm's, then the old ones. -/
private theorem rex_getD (c : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident)))
    (T E : WRes P) (cT cE : List (P.Ident × P.Ident)) (eT eE : WExpr P) (k : Nat) :
    (laidCarries c T E cT cE eT eE).getD k [] = (if E.tgt.max? = some k then
        (cE.map fun p => (p.1, .ite eE (.var p.2) (.var p.1), p.2)).reverse else []) ++
      ((if T.tgt.max? = some k then
        (cT.map fun p => (p.1, .ite eT (.var p.2) (.var p.1), p.2)).reverse else []) ++
        c.getD k []) := by
  unfold laidCarries carryIns
  split <;> split <;> grind [List.foldl_flip_cons_eq_append]

/-- A name drawn by the walk between the states `s` and `s'`: a fresh name not avoided with a
    counter from `s.next` on and below `s'.next`. -/
@[expose] def Drawn (s s' : WSt P) (n : P.Ident) : Prop :=
  ∃ b j, n = freshName b j ∧ s.avoid.contains n = false ∧ s.next ≤ j ∧ j < s'.next

/-- The facts of a run of `saveRestore` over the prefix `S` with accumulated saves `sv`, copies
    `cp`, restores `rs` and copy pairs `cps`, from `s` to `s'`, with `ns` the triples of a
    variable, its save name and its copy name: all names distinct and drawn between `s` and
    `s'`, typed like their variable. -/
structure SaveNs (s : WSt P) (S : List P.Ident) (sv cp rs : Rope (WItem P))
    (cps : List (P.Ident × P.Ident)) (s' : WSt P) (ns : List (P.Ident × P.Ident × P.Ident)) :
    Prop where
  vars : ns.map (·.1) = S
  saves : sv.toList = ns.map (fun q => .init q.2.1 (.of q.1) (some (.var q.1)))
  copies : cp.toList = ns.map (fun q => .init q.2.2 (.of q.1) (some (.var q.1)))
  restores : rs.toList = ns.map (fun q => .set q.1 (some (.var q.2.1)))
  pairs : cps = (ns.map fun q => (q.1, q.2.2)).reverse
  nodup : (ns.flatMap fun q => [q.2.1, q.2.2]).Nodup
  drawn : ∀ q ∈ ns, Drawn s s' q.2.1 ∧ Drawn s s' q.2.2 ∧
    s'.tyOf[q.2.1]? = some q.1 ∧ s'.tyOf[q.2.2]? = some q.1
  tyOf_other : ∀ n, (∀ q ∈ ns, n ≠ q.2.1 ∧ n ≠ q.2.2) → s'.tyOf[n]? = s.tyOf[n]?
  next : s.next ≤ s'.next
  eq : s' = { s with next := s'.next, tyOf := s'.tyOf }

/-- The facts of a run of `saveRestore` (`SaveNs` for some triples). -/
@[expose] def SaveFacts (s : WSt P) (S : List P.Ident) (sv cp rs : Rope (WItem P))
    (cps : List (P.Ident × P.Ident)) (s' : WSt P) : Prop :=
  ∃ ns, SaveNs s S sv cp rs cps s' ns

/-- The copy pairs of a run of `saveRestore` are saved variables with their copy names, with
    distinct first names when the saved variables are distinct. -/
private theorem SaveNs.mem_pairs {s s' : WSt P} (h : SaveNs s S sv cp rs cps s' ns) :
    (∀ p ∈ cps, ∃ q ∈ ns, p = (q.1, q.2.2)) ∧ (S.Nodup → (cps.map (·.1)).Nodup) := by
  rw [h.pairs, ← h.vars]
  grind

include iLI iWL in
/-- A run of `wFreshLike y` draws a name between the states before and after it, advances the
    counter and records the name's type reference to `y`. -/
private theorem wFreshLike_facts {y : P.Ident} (h : (wFreshLike y).run st = .ok (n, st')) :
    ∃ k, n = freshName (baseOf y) k ∧ st.avoid.contains n = false ∧ st.next ≤ k ∧
      st' = { st with next := k + 1, tyOf := st.tyOf.insert n y } := by
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid (baseOf y) st.next
  rw [wFreshLike_run, hk] at h
  cases h
  exact ⟨k, rfl, hav, hn, rfl⟩

include iLI in
/-- A name drawn before the state `st` differs from a fresh name with a counter from `st.next`
    on. -/
private theorem Drawn.ne {s : WSt P} {a : P.Ident} (ha : Drawn s st a)
    (hn : ∃ b j, n = freshName b j ∧ st.next ≤ j) : a ≠ n := by grind [Drawn, freshName_counter_inj]

/-- A name drawn between `s` and `st` is drawn between `s` and any later state. -/
private theorem Drawn.mono {s : WSt P} {a : P.Ident} (ha : Drawn s st a)
    (hle : st.next ≤ st'.next) : Drawn s st' a :=
  ha.imp fun _ ⟨j, e, h1, h2, h3⟩ => ⟨j, e, h1, h2, Nat.lt_of_lt_of_le h3 hle⟩

include iLI in
/-- A name drawn between `s` and `s'` is not a fresh name of `s'`. -/
private theorem Drawn.not_freshAt {s s' : WSt P} (h : Drawn s s' n) :
    ¬ FreshAt s' n := fun ⟨b, j, e, _, hj⟩ => h.ne ⟨b, j, e, hj⟩ rfl

include iLI in
/-- No name is drawn in two disjoint intervals of the walk. -/
private theorem Drawn.disj {s s' : WSt P} (h1 : Drawn s s' n)
    (h2 : Drawn s2 s3 n) (hle : s'.next ≤ s2.next) : False :=
  h1.ne (h2.elim fun b ⟨j, e, _, hj, _⟩ => ⟨b, j, e, Nat.le_trans hle hj⟩) rfl

include iLI in
/-- A name drawn between `s` and `s'` has no counter below `s.next`. -/
private theorem Drawn.not_below {s s' : WSt P} (h : Drawn s s' n) :
    ¬ ∃ b j, n = freshName b j ∧ j < s.next := by grind [Drawn, freshName_counter_inj]

/-- A name drawn between `s` and `s'` is drawn between any earlier state with the same avoided
    names and `s'`. -/
private theorem Drawn.of_le {s0 s s' : WSt P} (h : Drawn s s' n)
    (ha : s.avoid = s0.avoid) (hle : s0.next ≤ s.next) : Drawn s0 s' n :=
  h.imp fun _ ⟨j, e, hav, h1, h2⟩ => ⟨j, e, ha ▸ hav, Nat.le_trans hle h1, h2⟩

include iLI in
/-- A walk step keeps a name drawn before it out of the recorded renamings. -/
private theorem WalkCore.nm_not_drawn {D : List P.Ident} {s : WSt P}
    (h : WalkCore D st st') (hd : Drawn s st n) (hn : ∀ x : P.Ident, st.nm[x]? ≠ some n) :
    ∀ x : P.Ident, st'.nm[x]? ≠ some n := fun x hx => (h.nm x n hx).elim (hn x) hd.not_freshAt

include iLI iWL in
/-- A run of `saveRestore xs` draws one save and one copy name per variable of `xs`
    (`SaveFacts`). -/
private theorem saveRestore_run {xs : List P.Ident} {s s' : WSt P}
    (h : (saveRestore xs).run s = .ok ((sv, cp, rs, cps), s')) :
    SaveFacts s xs sv cp rs cps s' := by
  unfold saveRestore at h
  obtain ⟨acc, s1, hl, h⟩ := wm_run_bind_ok h
  obtain ⟨sv1, cp1, rs1, cps1⟩ := acc
  cases h
  have hI := wm_forIn_inv (fun S (b : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) ×
      List (P.Ident × P.Ident)) st =>
      SaveFacts s S b.1 b.2.1 b.2.2.1 b.2.2.2 st) _ ?_ xs [] _ s _ s'
    ⟨[], rfl, Rope.toList_nil, Rope.toList_nil, Rope.toList_nil, rfl, List.nodup_nil, nofun,
      fun _ _ => rfl, Nat.le_refl _, rfl⟩ hl
  · simpa using hI
  intro S y b st b' st' ⟨ns, hS, hsv, hcp, hrs, hcps, hnd, hdr, hty, hle, hst⟩ hb
  obtain ⟨n1, st1, h1, hb⟩ := wm_run_bind_ok hb
  obtain ⟨n2, st2, h2, hb⟩ := wm_run_bind_ok hb
  obtain ⟨k1, hn1, hav1, hk1, rfl⟩ := wFreshLike_facts h1
  obtain ⟨k2, hn2, hav2, hk2, rfl⟩ := wFreshLike_facts h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hb)
  simp only at hav2 hk2
  have hsa : st.avoid = s.avoid := by rw [hst]
  have hd1 : Drawn s ({ st with next := k2 + 1 } : WSt P) n1 :=
    ⟨_, k1, hn1, hsa ▸ hav1, Nat.le_trans hle hk1, by simp only; omega⟩
  have hd2 : Drawn s ({ st with next := k2 + 1 } : WSt P) n2 :=
    ⟨_, k2, hn2, hsa ▸ hav2, by omega, Nat.lt_succ_self k2⟩
  have hn1' : ∀ q ∈ ns, q.2.1 ≠ n1 ∧ q.2.2 ≠ n1 := fun q hq =>
    ⟨(hdr q hq).1.ne ⟨_, k1, hn1, hk1⟩, (hdr q hq).2.1.ne ⟨_, k1, hn1, hk1⟩⟩
  have hn2' : ∀ q ∈ ns, q.2.1 ≠ n2 ∧ q.2.2 ≠ n2 := fun q hq =>
    ⟨(hdr q hq).1.ne ⟨_, k2, hn2, by omega⟩, (hdr q hq).2.1.ne ⟨_, k2, hn2, by omega⟩⟩
  have h12 : n1 ≠ n2 := fun he =>
    absurd (freshName_counter_inj (hn1.symm.trans (he.trans hn2))) (by omega)
  refine ⟨_, rfl, ns ++ [(y, n1, n2)], by simp [hS],
    by simp [Rope.toList_app, Rope.toList_one, hsv],
    by simp [Rope.toList_app, Rope.toList_one, hcp],
    by simp [Rope.toList_app, Rope.toList_one, hrs],
    by simp [hcps], ?_, ?_, ?_, Nat.le_trans hle (by simp only; omega), by rw [hst]⟩
  · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.nodup_append, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
    grind
  · intro q hq
    simp only [List.mem_append, List.mem_singleton, Std.HashMap.getElem?_insert] at hq ⊢
    rcases hq with hq | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := hdr q hq
      exact ⟨h1.mono (by simp only; omega), h2.mono (by simp only; omega), by grind, by grind⟩
    · exact ⟨hd1, hd2, by grind, by grind⟩
  · intro n hn
    have h1 := hn (y, n1, n2) (by simp)
    simp only [Std.HashMap.getElem?_insert]
    rw [← hty n fun q hq => hn q (by simp [hq])]
    grind

/-! ## Sets, declared names and walk facts -/

/-- A fold that conses the elements satisfying `p` collects them. -/
private theorem mem_foldl_filter {α : Type} {p : α → Bool} {y : α} :
    ∀ (l acc : List α),
      y ∈ l.foldl (fun l x => if p x = true then x :: l else l) acc ↔
        y ∈ acc ∨ (y ∈ l ∧ p y = true) := fun l => by
  induction l <;> grind

omit iDE iHB iHF iSF iHI iHFs in
/-- The intersection of two hash sets lists the names of both. -/
private theorem mem_interSet {a b : Std.HashSet P.Ident} {x : P.Ident} :
    x ∈ interSet a b ↔ a.contains x = true ∧ b.contains x = true := by
  unfold interSet
  split <;> rw [Std.HashSet.fold_eq_foldl_toList, mem_foldl_filter] <;> simp [and_comm]

/-- A variable saved around a then arm that always exits (step 3b) is one it assigns that is live
    after the `ite` or read by the else arm. -/
private theorem mem_laidCT {T E : WRes P} {t0 : Nat} {x : P.Ident} (h : x ∈ laidCT T E st t0) :
    T.A.contains x = true ∧ (liveBefore st x t0 || E.R.contains x) = true := by
  simp only [laidCT, Std.HashSet.fold_eq_foldl_toList] at h
  split at h <;> simp only [mem_foldl_filter, List.not_mem_nil] at h <;> grind

/-- A variable saved around an else arm that always exits (step 3b) is one it assigns that is
    live after the `ite`. -/
private theorem mem_laidCE {E : WRes P} {t0 : Nat} {x : P.Ident}
    (h : x ∈ laidCE E st t0) : E.A.contains x = true ∧ liveBefore st x t0 = true := by
  unfold laidCE at h
  split at h <;> simp_all [Std.HashSet.fold_eq_foldl_toList, mem_foldl_filter]

end

/-- Facts of the walk of an arm of a laid-out `ite` (under a variable context `κ`, at depth `d`,
    an obligation following it, well scoped from `S`), from `st` to `st'` with result `r`:
    * the names the output declares are drawn by the walk or loop-free locals of the arm not yet
      recorded as declared, are no current names of variables of `S`, and include the exit
      snapshots; the arm's locals are recorded as declared at its start;
    * the assigned names `A` and the read names `R` are current names of variables of `S` that
      the arm mentions or names the output declares;
    * the live entries of the current names of variables of `S` keep their stamps;
    * the pending snapshots only grow, by names the walk draws (the arm's snapshots, and those
      of code discarded after a statement that always exits);
    * a main-path run of the output changes only names the walk draws, recorded renamings at
      its start, identifiers of the arm and the variable the reach update of `κ` writes, and not
      the enclosing context `q` of `κ = q ∧ ¬g`;
    * a loop-free exit of the arm (the label depths of the region at most `d`) makes `minT` at
      most `d`;
    * the carried merges only grow, by merges whose copies the walk draws; the merges the arm
      registers merge current names of variables of `S` or names its output declares, and their
      selectors read only names its output declares. -/
structure ArmFacts (F : P.Factory) (Lc S : List P.Ident) (κ : RE P) (d : Nat) (ss : PStmts P)
    (st : WSt P) (r : WRes P) (st' : WSt P) : Prop where
  decl : ∀ n ∈ wDecls r.out.toList,
    Drawn st st' n ∨ (n ∈ stmtsInits ss ∧ st.taken.contains n = false) ∨
      ∃ x ∈ stmtsInits ss, st.nm[x]? = some n
  declNotNm : ∀ n ∈ wDecls r.out.toList, ∀ x : P.Ident, st'.nm[x]? ≠ some n
  regs : ∀ e ∈ r.regs.toList, e ∈ wDecls r.out.toList
  declNotCur : ∀ n ∈ wDecls r.out.toList, ∀ z ∈ S, curName st' z ≠ some n
  takenIn : ∀ z ∈ stmtsInits ss, st'.taken.contains z = true
  assigned : ∀ n, r.A.contains n = true →
    (∃ z ∈ S, z ∈ Block.freeVars ss ∧ curName st' z = some n) ∨ n ∈ wDecls r.out.toList
  read : ∀ n, r.R.contains n = true →
    (∃ z ∈ S, z ∈ Block.freeVars ss ∧ curName st' z = some n) ∨ n ∈ wDecls r.out.toList
  liveKeep : ∀ z ∈ S, ∀ n, curName st z = some n → ∀ s : Nat, st.live[n]? = some s →
    st'.live[n]? = some s
  pendKeep : ∀ l e, e ∈ st.pending.getD l [] → e ∈ st'.pending.getD l []
  pendNew : ∀ l e, e ∈ st'.pending.getD l [] → e ∈ st.pending.getD l [] ∨ Drawn st st' e
  writesW : ∀ T Y items, resolveItems T Y r.out.toList = .ok items → ∀ σL tr σL',
    MainRun F items σL tr σL' → ∀ n, σL' n ≠ σL n →
      Wr0 (Block.idents ss) st st' n ∨ κ.wvar = some n
  writesQ : ∀ T Y items, resolveItems T Y r.out.toList = .ok items → ∀ σL tr σL',
    MainRun F items σL tr σL' → ∀ q g, κ = .andNeg q g → σL' q = σL q
  exitMin : (∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d) → ∀ X σ evs l σ1,
    DRun F X ss σ evs (.exit l σ1) → leOpt r.minT d = true
  carriesNew : ∀ k, ∃ new, st'.carries.getD k [] = new ++ st.carries.getD k [] ∧
    ∀ q ∈ new, Drawn st st' q.2.2
  carryTgt : ∀ k i n v xB, CarryReg r st' k i n v xB →
    (∃ z ∈ S, curName st' z = some n) ∨ n ∈ wDecls r.out.toList
  carrySel : ∀ (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) k i n v xB,
    CarryReg r st' k i n v xB → ∀ e xB' x, v = .ite e (.var xB') (.var x) → ∀ e',
      resolveE T Y e = .ok e' → ∀ y ∈ exprFV e', y ∈ wDecls r.out.toList

omit iLV in
/-- The walk of an arm of a laid-out `ite` has the facts `ArmFacts`, when the label depths at
    its start are at most `d`, it carries no merge deeper than `d`, the variables of `κ` are
    fresh names drawn before it that are not renamings, `κ = q ∧ ¬g` has `q ≠ g`, and its
    discarded registrations were drawn before it. -/
private theorem arm_facts
    (h : (wpList κ d true ss).run st = .ok (r, st')) (hκ : κ ≠ .top) (hwf : WFSt st)
    (hS : Block.WellScoped Lc S ss)
    (hav : ∀ x ∈ S ++ Block.idents ss, ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hL : ∀ (l : String) (t : Nat), st.labelDepth[l]? = some t → t ≤ d)
    (hhigh : ∀ k, d < k → st.carries.getD k [] = [])
    (hκv : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ ∀ x : P.Ident, st.nm[x]? ≠ some y)
    (hqg : ∀ q g, κ = .andNeg q g → q ≠ g) (hD : DeadBelow st) :
    ArmFacts F Lc S κ d ss st r st' :=
  ⟨arm_decl h hκ, arm_declNotNm h hκ hwf hS hav hL, arm_regs h hκ,
    arm_declNotCur h hκ hwf hS hav hL, arm_takenIn h hκ, arm_assigned h hκ hwf hS hav hL,
    arm_read h hκ hwf hS hav hL, arm_liveKeep h hκ hwf hS hav hL, fun _ _ he => wpList_pending h he,
    fun _ _ he => (wpList_pending_new h he).imp id fun ⟨b, j, h1, h2, h3, h4⟩ =>
      ⟨b, j, h1, h4, h2, h3⟩, arm_writes h,
    arm_writesQ h (fun x hx => hav x (List.mem_append_right _ hx)) hκv hqg, arm_exitMin h hκ hD,
    arm_carriesNew h hκ hhigh, arm_carryTgt h hκ hwf hS hav hL, arm_carrySel h hκ hwf⟩

/-! ## The setting of a laid-out `ite` whose arms do not always exit -/

/-- The part of the setting of the simulation proof for a laid-out `ite c T E` (statement
    `.ite (.det c) tss ess md` under context `κ` at depth `d`) common to all its walks: the arms'
    walks have the simulation property, the walk from `st0` begins with the guard's renaming
    `(wc, rdc)` (state `s1`), the guard `g` (state `s2`), the then-arm reach `rT` (state `s3`), the
    else-arm context `κE` with reach name `rE?` (state `s4`), the else arm's walk `Er` (state `s5`)
    and the then arm's walk `Tr` (state `s6`), and the premises of `Spec` hold for the final maps
    `T`, `Y`, the resolved output `items` of the result `r`, the scope `S`, the excepted names
    `Ex`, the continuation `k` and the label map `Lab`. -/
structure LaidCore (F : P.Factory) (tE : TypedEval P) (Γ : VarTyping P) (Lc : List P.Ident)
    (κ : RE P) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (md : MetaData P) (st0 : WSt P) (r : WRes P) (st' : WSt P)
    (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (items : List (Item P))
    (S : List P.Ident) (Ex : P.Ident → Prop) (k : List (PStmts P))
    (Lab : String → List P.Ident) (wc : WExpr P) (rdc : List P.Ident) (s1 : WSt P)
    (g : P.Ident) (s2 : WSt P) (rT : P.Ident) (s3 : WSt P) (κE : RE P) (rE? : Option P.Ident)
    (s4 : WSt P) (Er : WRes P) (s5 : WSt P) (Tr : WRes P) (s6 : WSt P) : Prop where
  hF : WellFormedSemanticEvalBase F
  armT : ∀ κ', ListSpec F tE Lc κ' d true tss
  armE : ∀ κ', ListSpec F tE Lc κ' d true ess
  wf0 : WFSt st0
  run1 : (wRen c).run st0 = .ok ((wc, rdc), s1)
  run2 : (wFreshBool "g").run s1 = .ok (g, s2)
  run3 : (wFreshBool "r").run s2 = .ok (rT, s3)
  ctx : LaidCtx κ g s3 κE rE? s4
  runE : (wpList κE d true ess).run s4 = .ok (Er, s5)
  runT : (wpList (.name rT) d true tss).run s5 = .ok (Tr, s6)
  fin : FinalOK Lc st' T Y
  res : resolveItems T Y r.out.toList = .ok items
  wfS : Stmt.WellScoped Lc S (.ite (.det c) tss ess md)
  avoidS : ∀ x ∈ S ++ Block.idents [.ite (.det c) tss ess md], ∀ b j, x = freshName b j →
    st0.avoid.contains x = true
  exc : ∀ y, Ex y → (∀ b j, y = freshName b j → j < st0.next) ∧ st'.back[y]? = none
  lab : ∀ l t, st0.labelDepth[l]? = some t → t ≤ d ∧ ∀ x ∈ Lab l, x ∈ contFV k ∧ x ∈ S
  ctxv : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st0.next) ∧
    st0.avoid.contains y = false ∧ ∀ x : P.Ident, st0.nm[x]? ≠ some y
  ctxb : ∀ y ∈ RE.vars κ, st0.back[y]? = none
  whole : WalkOK (stmtsInits tss ++ stmtsInits ess) st0 st'
  dead0 : DeadBelow st0
  livek : LiveKeys st0
  chigh : ∀ k, d < k → st0.carries.getD k [] = []
  /-- The typing `Γ` of the scope agrees with the final type maps before the `ite`. -/
  tyCtx : TyCtx T Y st' S Γ
  /-- The expressions of the `ite` are typed under `Γ`. -/
  typed : ExprsTyped tE Γ [.ite (.det c) tss ess md]

/-- The setting of the simulation proof for a laid-out `ite` whose arms do not always exit: the
    common setting `LaidCore`, and the end of the walk from the state `s6` after the arms: the
    saves `sv`, copies `cp`, restores `rs` and copy pairs `cps` of the then arm's assignments the
    else arm reads (state `s7`), the merge guard `gm?` when a merge reads it (state `s8`), the
    carries map `cr` (changed to no effect on the output), and the output: nothing when every
    part is empty, otherwise the guard followed by the parts `laidParts`, the live set gaining
    the guard's reads. -/
structure LaidEnv (F : P.Factory) (tE : TypedEval P) (Γ : VarTyping P) (Lc : List P.Ident)
    (κ : RE P) (d : Nat) (c : P.Expr)
    (tss ess : PStmts P) (md : MetaData P) (st0 : WSt P) (r : WRes P) (st' : WSt P)
    (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (items : List (Item P))
    (S : List P.Ident) (Ex : P.Ident → Prop) (k : List (PStmts P))
    (Lab : String → List P.Ident) (wc : WExpr P) (rdc : List P.Ident) (s1 : WSt P)
    (g : P.Ident) (s2 : WSt P) (rT : P.Ident) (s3 : WSt P) (κE : RE P) (rE? : Option P.Ident)
    (s4 : WSt P) (Er : WRes P) (s5 : WSt P) (Tr : WRes P) (s6 : WSt P)
    (sv cp rs : Rope (WItem P)) (cps : List (P.Ident × P.Ident)) (s7 : WSt P)
    (gm? : Option P.Ident) (s8 : WSt P)
    (cr : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))) : Prop
    extends LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
       Ex k Lab wc rdc s1 g s2 rT s3 κE
      rE? s4 Er s5 Tr s6 where
  axT : Tr.ax = false
  axE : Er.ax = false
  run7 : (saveRestore (interSet Tr.A Er.R)).run s6 = .ok ((sv, cp, rs, cps), s7)
  gm : (((cps.filter fun p => liveBefore s6 p.1 s4.clock).any fun p => Er.A.contains p.1) = true ∧
      ∃ x, gm? = some x ∧ (wFreshBool "g").run s7 = .ok (x, s8)) ∨
    (((cps.filter fun p => liveBefore s6 p.1 s4.clock).any fun p => Er.A.contains p.1) = false ∧
      gm? = none ∧ s8 = s7)
  carries : ∀ k, cr.getD k [] = s8.carries.getD k []
  ax : r.ax = false
  drop : r.drop = false
  regs : r.regs.toList = Tr.regs.toList ++ Er.regs.toList
  out : (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er
        (laidU κ κE rT Tr Er d)).all Rope.isNil = true ∧ r.out = .nil ∧
      st' = { s8 with carries := cr } ∨
    (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er
        (laidU κ κE rT Tr Er d)).all Rope.isNil = false ∧
      r.out.toList = .init g (.known HasBool.boolTy) (some (kAnd κ wc)) ::
        (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er
          (laidU κ κE rT Tr Er d)).flatMap Rope.toList ∧
      r.sk = [.ite g Tr.sk Er.sk] ∧ r.hasObl = (Tr.hasObl || Er.hasObl) ∧
      (liveAdd (rdc ++ RE.vars κ)).run { s8 with carries := cr } = .ok ((), st')

/-- How the walk state changes after the arms of a laid-out `ite` (from `s6` to `st'`): the
    saves (to `s7`), the names drawn after them, the merge guard and the live additions leave the
    renamings, the declared names, the avoided names, the back map, the pending snapshots and the
    label depths unchanged; the type references change from `s7`, and the declared types from
    `s6`, only at names drawn after `s7`; the merge guard is Boolean and drawn after `s7`; live
    entries of `s6` keep their stamps; when the output is not empty the guard's reads and the
    context's variables are live. -/
structure AfterFacts (κ : RE P) (rdc : List P.Ident) (s6 s7 : WSt P) (gm? : Option P.Ident)
    (st' : WSt P) (nonnil : Prop) : Prop where
  nm : st'.nm = s6.nm
  taken : st'.taken = s6.taken
  avoid : st'.avoid = s6.avoid
  back : st'.back = s6.back
  pending : st'.pending = s6.pending
  labelDepth : st'.labelDepth = s6.labelDepth
  tyOf : ∀ n, ¬ Drawn s7 st' n → st'.tyOf[n]? = s7.tyOf[n]?
  tys : ∀ n, ¬ Drawn s7 st' n → st'.tys[n]? = s6.tys[n]?
  tysGm : ∀ x, gm? = some x → st'.tys[x]? = some HasBool.boolTy
  gmDrawn : ∀ x, gm? = some x → Drawn s7 st' x
  next : s7.next ≤ st'.next
  live : ∀ (n : P.Ident) (s : Nat), s6.live[n]? = some s → st'.live[n]? = some s
  liveC : nonnil → ∀ n ∈ rdc ++ RE.vars κ, st'.live.contains n = true

omit iWL iOp iLF iLFs iLV in
/-- A run of `wFreshBool b` draws a name, advances the counter and gives the name the Boolean
    type. -/
private theorem wFreshBool_facts {b : String} (h : (wFreshBool b).run st = .ok (n, st')) :
    ∃ k, n = freshName b k ∧ st.avoid.contains n = false ∧ st.next ≤ k ∧
      st' = { st with next := k + 1, tys := st.tys.insert n HasBool.boolTy } := by
  obtain ⟨k, hk, hn, hav⟩ := freshIn_spec st.avoid b st.next
  rw [wFreshBool_run, hk] at h
  cases h
  exact ⟨k, rfl, hav, hn, rfl⟩

/-! ## Runs of guarded items -/

omit iBE iLB iHI iLI iHa iWL iOp iLF iLFs iLV in
/-- A deterministic `init` of an unbound name whose expression evaluates to a value of the
    declared type runs, binding the name to the value. -/
private theorem run_init1 (hF : WellFormedSemanticEvalBase F) {x : P.Ident} {ty : P.Ty}
    {e : P.Expr} {v : P.Val} (h0 : σ x = none) (hv : P.eval F σ e = some v)
    (hty : HasVal.valueOfTy F v ty) :
    MainRun F [.plain (mkInit x ty (.det e))] σ [] (SemanticStore.update σ x v) :=
  .plain (c := .cmd _) (EvalCmdE.eval_init hv
    (.init h0 (update_facts σ x v).1 (update_facts σ x v).2) hty hF.var) .nil

omit iBE iLB iHI iLI iHa iWL iOp iLF iLFs iLV in
/-- A deterministic `set` of a bound name to a value of a type of its stored value runs. -/
private theorem run_set1 (hF : WellFormedSemanticEvalBase F) {x : P.Ident}
    {e : P.Expr} {w : P.Val} {v : P.Val}
    (hx : σ x = some w) (hv : P.eval F σ e = some v)
    (hst : HasVal.valueOfStoredTy (P := P) F σ x v) :
    MainRun F [.plain (.cmd (.cmd (.set x (.det e) .empty)))] σ []
      (SemanticStore.update σ x v) :=
  .plain (c := .cmd _) (EvalCmdE.eval_set hv
    (.update hx (update_facts σ x v).1 (update_facts σ x v).2) hst hF.var) .nil

omit iBE iLB iHI iLI iHa iWL iLFs iLV in
/-- A list of deterministic `init`s of distinct unbound names, each initialized from a variable
    bound to a value of the declared type, runs; each target takes its source's value and every
    other name keeps its value. -/
private theorem run_var_inits (hF : WellFormedSemanticEvalBase F) :
    ∀ (l : List (P.Ident × P.Ty × P.Ident × Option P.Ty)) (σ : SemanticStore P),
      WellFormedStore σ F → (l.map (·.1)).Nodup → (∀ q ∈ l, σ q.1 = none) →
      (∀ q ∈ l, ∃ w, σ q.2.2.1 = some w ∧ HasVal.valueOfTy F w q.2.1) →
      ∃ σ', MainRun F (l.map fun q =>
          .plain (mkInit q.1 q.2.1 (.det (HasFvar.mkVar q.2.2.1 q.2.2.2))))
          σ [] σ' ∧ WellFormedStore σ' F ∧ (∀ q ∈ l, σ' q.1 = σ q.2.2.1) ∧
        (∀ n, (∀ q ∈ l, n ≠ q.1) → σ' n = σ n)
  | [], σ, hC, _, _, _ => ⟨σ, .nil, hC, nofun, fun _ _ => rfl⟩
  | q :: l, σ, hC, hnd, h0, hsrc => by
    obtain ⟨w, hw, hty⟩ := hsrc q (List.mem_cons_self ..)
    obtain ⟨σ', hr, hC', hval, hoth⟩ := run_var_inits hF l _ (wfStore_update hC q.1 (hC _ _ hw))
      (List.nodup_cons.1 hnd).2 (fun p hp => by grind [SemanticStore.update, List.nodup_cons])
      (fun p hp => by grind [SemanticStore.update])
    refine ⟨σ', (run_init1 hF (h0 q (.head _)) (ev_var hF.var hC hw) hty).append hr, hC', ?_, ?_⟩
    all_goals grind [SemanticStore.update, List.nodup_cons]

section

omit iLB iHI iLI iOp iLF iLFs iLV

/-- A resolved `init` with an expression is a deterministic `init` of the resolved expression,
    with the type of its type reference. -/
private theorem resolveItem_init_inv {x : P.Ident} {tr : TyRef P} {we : WExpr P} {a : Item P}
    (h : resolveItem T Y (.init x tr (some we)) = .ok a) :
    ∃ ty e, (match tr with | .known t => ty = t | .of y => tyOfName T Y y = .ok ty) ∧
      resolveE T Y we = .ok e ∧ a = .plain (mkInit x ty (.det e)) := by
  simp only [resolveItem, resolveOE, bind, Except.bind, pure, Except.pure] at h
  (repeat' split at h) <;> grind

/-- The resolution of a one-element rope is the resolution of its element. -/
private theorem resolve_one
    {it : WItem P} {its : List (Item P)} (h : resolveItems T Y (Rope.one it).toList = .ok its) :
    ∃ a, resolveItem T Y it = .ok a ∧ its = [a] := by
  obtain ⟨a, its', ha, hr, rfl⟩ := resolveItems_cons_ok (Rope.toList_one it ▸ h)
  exact ⟨a, ha, by rw [← Except.ok.inj hr]⟩

/-- The resolution of `init`s of names from variables is a list of deterministic `init`s from
    annotated variables, with the types of the type references. -/
private theorem resolve_var_inits :
    ∀ (m : List (P.Ident × TyRef P × P.Ident)) (its : List (Item P)),
      resolveItems T Y (m.map fun p => .init p.1 p.2.1 (some (.var p.2.2))) = .ok its →
      ∃ l : List (P.Ident × P.Ty × P.Ident × Option P.Ty),
        l.map (fun q => (q.1, q.2.2.1)) = m.map (fun p => (p.1, p.2.2)) ∧
        (∀ q ∈ l, ∃ p ∈ m, p.1 = q.1 ∧ p.2.2 = q.2.2.1 ∧
          (match p.2.1 with | .known t => q.2.1 = t | .of y => tyOfName T Y y = .ok q.2.1)) ∧
        its = l.map fun q => .plain (mkInit q.1 q.2.1 (.det (HasFvar.mkVar q.2.2.1 q.2.2.2)))
  | [], its, h => ⟨[], rfl, nofun, (Except.ok.inj h).symm⟩
  | p :: m, its, h => by
    obtain ⟨a, its', ha, hr, rfl⟩ := resolveItems_cons_ok h
    obtain ⟨ty, e, hty, he, rfl⟩ := resolveItem_init_inv ha
    obtain ⟨t, rfl⟩ := resolveE_var he
    obtain ⟨l, h1, h2, rfl⟩ := resolve_var_inits m its' hr
    exact ⟨(p.1, ty, p.2.2, some t) :: l, by simp [h1], by grind, rfl⟩

/-- The resolution of `set`s of names to variables is a list of deterministic `set`s to
    annotated variables. -/
private theorem resolve_var_sets :
    ∀ (m : List (P.Ident × P.Ident)) (its : List (Item P)),
      resolveItems T Y (m.map fun p => .set p.1 (some (.var p.2))) = .ok its →
      ∃ l : List (P.Ident × P.Ident × Option P.Ty),
        l.map (fun q => (q.1, q.2.1)) = m ∧
        its = l.map fun q =>
          .plain (.cmd (.cmd (.set q.1 (.det (HasFvar.mkVar q.2.1 q.2.2)) .empty)))
  | [], its, h => ⟨[], rfl, (Except.ok.inj h).symm⟩
  | p :: m, its, h => by
    obtain ⟨a, its', ha, hr, rfl⟩ := resolveItems_cons_ok h
    obtain ⟨e, he, rfl⟩ := resolveItem_set ha
    obtain ⟨t, rfl⟩ := resolveE_var he
    obtain ⟨l, h1, rfl⟩ := resolve_var_sets m its' hr
    exact ⟨(p.1, p.2, some t) :: l, by simp [h1], rfl⟩

/-- The resolution of a rope of at most one `init` with an expression. -/
private theorem resolve_opt_init
    {b : Bool} {x : P.Ident} {tr : TyRef P} {we : WExpr P} {its : List (Item P)}
    (h : resolveItems T Y (if b = true then Rope.nil
      else Rope.one (WItem.init x tr (some we))).toList
      = .ok its) :
    (b = true ∧ its = []) ∨ (b = false ∧ ∃ ty e',
      (match tr with
        | .known t => ty = t
        | .of y => tyOfName T Y y = .ok ty) ∧
      resolveE T Y we = .ok e' ∧ its = [.plain (mkInit x ty (.det e'))]) := by
  cases b
  · obtain ⟨a, ha, rfl⟩ := resolve_one h
    obtain ⟨ty, e, hty, he, rfl⟩ := resolveItem_init_inv ha
    exact .inr ⟨rfl, ty, e, hty, he, rfl⟩
  · exact .inl ⟨rfl, resolve_isNil rfl h⟩

/-- A Boolean value has the type that the type lookup gives a name declared Boolean. -/
private theorem tyOfName_bool {w : P.Val} {ty : P.Ty}
    (hT : T[n]? = some HasBool.boolTy) (hw : w = HasBool.ttVal F ∨ w = HasBool.ffVal F)
    (h : tyOfName T Y n = .ok ty) :
    HasVal.valueOfTy F w ty := by
  rw [tyOfName, hT] at h
  exact Except.ok.inj h ▸ bool_valueOfTy hw

end

/-- The elements of a fold of one-element ropes. -/
private theorem toList_foldl_one {α β : Type} (f : β → α) :
    ∀ (l : List β) (s : Rope α),
      (l.foldl (fun acc x => acc.app (.one (f x))) s).toList = s.toList ++ l.map f := fun l => by
  induction l <;> simp_all [Rope.toList_app, Rope.toList_one]

omit iDE iLB iHB iHF iSF iHI iLI iHFs iWL iOp iLF iLFs iLV in
/-- The merges of a laid-out `ite` are one `set` per live saved variable. -/
private theorem laidMerges_toList (gm? : Option P.Ident) (EA : Std.HashSet P.Ident)
    (liveM : List (P.Ident × P.Ident)) :
    (laidMerges gm? EA liveM).toList = liveM.map fun x => .set x.1 (some
      (if EA.contains x.1 = true then
        WExpr.ite (match gm? with | some y => .var y | none => .lit false) (.var x.2) (.var x.1)
      else .var x.2)) := by simp [laidMerges, toList_foldl_one, Rope.toList_nil]

open Classical in
/-- The value the merge of a laid-out `ite` gives a saved variable `p.1` with copy `p.2` in the
    store `σ`: when the else arm assigns it, the copy if the merge guard holds and the variable's
    own value otherwise; the copy when the else arm does not assign it. -/
@[expose] noncomputable def mergeVal (F : P.Factory) (σ : SemanticStore P) (gm? : Option P.Ident)
    (EA : Std.HashSet P.Ident) (p : P.Ident × P.Ident) : Option P.Val :=
  if EA.contains p.1 = true then
    (match gm? with
      | some y => if σ y = some (HasBool.ttVal F) then σ p.2 else σ p.1
      | none => σ p.1)
  else σ p.2

omit iLB iHI iLI iLFs in
include iIL in
/-- The merges of a laid-out `ite` run from a value-valued store binding the merge guard to a
    Boolean and each merged variable and its copy to values of a common type, the merged
    variables distinct and no copy merged: each merged variable takes its `mergeVal` and every
    other name keeps its value. -/
private theorem run_merges (hF : WellFormedSemanticEvalBase F) (gm? : Option P.Ident)
    (EA : Std.HashSet P.Ident) :
    ∀ (l : List (P.Ident × P.Ident)) (σ : SemanticStore P) (its : List (Item P)),
      resolveItems T Y (laidMerges gm? EA l).toList = .ok its → WellFormedStore σ F →
      (l.map (·.1)).Nodup → (∀ p ∈ l, p.2 ∉ l.map (·.1)) →
      (∀ x, gm? = some x →
        (σ x = some (HasBool.ttVal F) ∨ σ x = some (HasBool.ffVal F)) ∧ x ∉ l.map (·.1)) →
      (∀ p ∈ l, ∃ w w' ty, σ p.1 = some w ∧ σ p.2 = some w' ∧ HasVal.valueOfTy F w ty ∧
        HasVal.valueOfTy F w' ty) →
      ∃ σ', MainRun F its σ [] σ' ∧ WellFormedStore σ' F ∧
        (∀ p ∈ l, σ' p.1 = mergeVal F σ gm? EA p) ∧
        ∀ n, n ∉ l.map (·.1) → σ' n = σ n := fun l => by
  induction l with
  | nil =>
    exact fun σ its h hC _ _ _ _ => ⟨σ, resolve_isNil rfl h ▸ .nil, hC, nofun, fun _ _ => rfl⟩
  | cons p l ih =>
    intro σ its h hC hnd hcp hgm hval
    rw [laidMerges_toList, List.map_cons] at h
    obtain ⟨a, its', ha, hr, rfl⟩ := resolveItems_cons_ok h
    obtain ⟨e', he, rfl⟩ := resolveItem_set ha
    obtain ⟨w, w', ty, hw, hw', ht, ht'⟩ := hval p (.head _)
    obtain ⟨v, hmv, hev, htv⟩ : ∃ v, mergeVal F σ gm? EA p = some v ∧ P.eval F σ e' = some v ∧
        HasVal.valueOfTy F v ty := by
      have hv : ∀ {y v}, σ y = some v →
          ∀ x', resolveE T Y (.var y) = .ok x' → P.eval F σ x' = some v :=
        fun hr _ h' => (resolveE_var h').elim fun _ he => he ▸ ev_var hF.var hC hr
      unfold mergeVal
      by_cases hc : EA.contains p.1 = true
      · simp only [hc, ↓reduceIte] at he ⊢
        obtain ⟨c', t', e'', hc', htr, her, rfl⟩ := resolveE_ite.1 he
        cases gm? with
        | none =>
          refine ⟨w, hw, WPIteLang.ev_ite_false ?_ (hv hw' _ htr) (hv hw _ her) ht ht', ht⟩
          simpa [← Except.ok.inj hc'] using hF.val.eval_ff σ
        | some y =>
          rcases (hgm y rfl).1 with hy | hy
          · exact ⟨w', by simp [hy, hw'],
              WPIteLang.ev_ite_true (hv hy _ hc') (hv hw' _ htr) (hv hw _ her) ht' ht, ht'⟩
          · exact ⟨w, by simp [hy, hw, (HasBool.ttVal_ne_ffVal F).symm],
              WPIteLang.ev_ite_false (hv hy _ hc') (hv hw' _ htr) (hv hw _ her) ht ht', ht⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at he ⊢
        exact ⟨w', hw', hv hw' _ he, ht'⟩
    obtain ⟨σ', hrun, hC', hm, hoth⟩ := ih (σ.update p.1 v) its' (by rwa [laidMerges_toList])
      (wfStore_update hC p.1 (LawfulHasVal.valueOfTy_isVal F v ty htv)) (List.nodup_cons.1 hnd).2
      (by grind) (by grind [SemanticStore.update]) (by grind [SemanticStore.update])
    refine ⟨σ', MainRun.append (run_set1 hF hw hev ⟨w, ty, hw, ht, htv⟩) hrun, hC', ?_, ?_⟩
    · grind [mergeVal, SemanticStore.update]
    · grind [SemanticStore.update]

omit iBE iLB iHI iLI iHa iWL iOp iLF iLFs in
/-- Setting a Boolean variable to the Boolean value of a resolved expression runs. -/
private theorem run_set_bool (hF : WellFormedSemanticEvalBase F) {x : P.Ident}
    {e : P.Expr} {b : Prop} [Decidable b] (hC : WellFormedStore σ F)
        (hx : σ x = some (HasBool.ttVal F) ∨ σ x = some (HasBool.ffVal F))
        (he : P.eval F σ e = some (if b then HasBool.ttVal F else HasBool.ffVal F)) :
    MainRun F [.plain (.cmd (.cmd (.set x (.det e) .empty)))] σ []
      (SemanticStore.update σ x (if b then HasBool.ttVal F else HasBool.ffVal F)) ∧
      WellFormedStore
        (SemanticStore.update σ x (if b then HasBool.ttVal F else HasBool.ffVal F)) F := by
  have hr := set_run hF he hx (if hb : b then .inl (ite_eq_left hb) else .inr (ite_eq_right hb))
  exact ⟨hr, hr.canon hF hC⟩

open Classical in
omit iLI iLFs in
include iIL in
/-- The reach update of a laid-out `ite` (`rT ∨ κE` made the context's value, or assumed under
    `top`) runs from a value-valued store in which `rT` and the variables of `κ` hold Booleans
    and `κE` holds or fails.  Let `xv` be the truth of `rT ∨ κE`.  The run changes only the
    variables of `κ`, which stay Boolean; when the update is empty the run is empty; otherwise,
    under `top` its trace is the assumption, feasible exactly when `xv`, and under a variable
    context it emits nothing and makes the context hold when `xv` (and, for `q ∧ ¬g`, `q`
    holds and differs from `g`) and fail otherwise. -/
private theorem run_U (hF : WellFormedSemanticEvalBase F)
    (hres : resolveItems T Y (laidU κ κE rT Tr Er d).toList = .ok iU) (hC : WellFormedStore σ F)
    (hrT : σ rT = some (HasBool.ttVal F) ∨ σ rT = some (HasBool.ffVal F))
    (hE : κE.Holds F σ ∨ κE.Fails F σ)
    (hκ : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F))
    (hκE : ∀ y ∈ RE.vars κE, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
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
  have hX : ∀ x, resolveE T Y ((WExpr.var rT).or (kExpr κE)) = .ok x →
      P.eval F σ x = some (if σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ
        then HasBool.ttVal F else HasBool.ffVal F) := fun x h => by
    rcases hrT with hr | hr
    · rw [ite_eq_left (.inl hr)]
      exact ev_or_tt hF h (fun _ => ev_res_var hF hC hr) fun a ha =>
        hE.elim (fun hk => .inl (ev_kExpr_holds hF hC hk ha)) fun hk =>
          .inr (ev_kExpr_fails hF hC hk hκE ha)
    rcases hE with hk | hk
    · rw [ite_eq_left (.inr hk)]
      exact ev_or_ff hF h (fun _ => ev_res_var hF hC hr) (fun _ => ev_kExpr_holds hF hC hk)
        (.inl rfl)
    · rw [ite_eq_right (not_or.2 ⟨fun h' =>
          (HasBool.ttVal_ne_ffVal F).symm (Option.some.inj (hr.symm.trans h')),
        fun h' => h'.not_fails hk⟩)]
      exact ev_or_ff hF h (fun _ => ev_res_var hF hC hr) (fun _ => ev_kExpr_fails hF hC hk hκE)
        (.inr rfl)
  have hN : ∀ e, resolveE T Y ((WExpr.var rT).or (kExpr κE)).not = .ok e →
      P.eval F σ e = some (if ¬ (σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ)
        then HasBool.ttVal F else HasBool.ffVal F) := fun e he => by
    by_cases hb : σ rT = some (HasBool.ttVal F) ∨ κE.Holds F σ
    · rw [ite_eq_right (Classical.not_not.2 hb)]
      exact ev_not_tt hF he fun a ha => (hX a ha).trans (by rw [ite_eq_left hb])
    · rw [ite_eq_left hb]
      exact ev_not_ff hF he fun a ha => (hX a ha).trans (by rw [ite_eq_right hb])
  cases hc : (leOpt Tr.minT d || leOpt Er.minT d)
  · simp only [laidU, hc, Bool.false_eq_true, ↓reduceIte] at hres ⊢
    exact ⟨[], σ, resolve_isNil rfl hres ▸ .nil, hC, fun _ _ => rfl, hκ, fun _ => ⟨rfl, rfl⟩, nofun,
      fun _ _ _ _ _ => rfl⟩
  simp only [laidU, hc, ↓reduceIte] at hres ⊢
  cases κ
  all_goals obtain ⟨a, ha, rfl⟩ := resolve_one hres
  case top =>
    obtain ⟨e, he, rfl⟩ := resolveItem_assume ha
    refine ⟨_, σ, .plain (c := .cmd _) .eval_assume .nil, hC, fun _ _ => rfl, nofun, nofun,
      fun _ => ⟨fun _ => ?_, nofun⟩, nofun⟩
    simp [Trace.AssumptionsHold, evalInterp, hX e he, (HasBool.ttVal_ne_ffVal F).symm,
      Classical.or_iff_not_imp_left]
  all_goals obtain ⟨e, he, rfl⟩ := resolveItem_set ha
  case' name r => obtain ⟨hr, hC'⟩ := run_set_bool hF hC (hκ r (.head _)) (hX e he)
  case' neg g | andNeg q g =>
    obtain ⟨hr, hC'⟩ := run_set_bool hF hC (hκ g (by simp [RE.vars])) (hN e he)
  all_goals refine ⟨_, _, hr, hC', ?_, ?_, nofun, fun _ => ⟨nofun, fun _ => ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  all_goals clear hX hN hres ha he hrT hE
  all_goals grind [SemanticStore.update, RE.vars, RE.Holds, RE.Fails]

/-- How the prelude of a laid-out `ite` changes the walk state from `s1` (after the guard's
    renaming) to `s4` (before the arms): it draws the guard `g`, the then-arm reach `rT` and,
    for the else-arm context `name rE`, `rE`, all distinct and Boolean, and changes only the
    counter and the declared types. -/
structure PreFacts (s1 : WSt P) (g rT : P.Ident) (rE? : Option P.Ident) (s4 : WSt P) : Prop where
  drawn : ∀ n, (n = g ∨ n = rT ∨ rE? = some n) → Drawn s1 s4 n
  g_rT : g ≠ rT
  rE_ne : ∀ x, rE? = some x → x ≠ g ∧ x ≠ rT
  tys : ∀ n, (n = g ∨ n = rT ∨ rE? = some n) → s4.tys[n]? = some HasBool.boolTy
  next : s1.next ≤ s4.next
  eq : s4 = { s1 with next := s4.next, tys := s4.tys }

omit iWL iOp iLF iLFs iLV in
/-- The prelude of a laid-out `ite` changes the state as `PreFacts` says. -/
private theorem pre_facts (h2 : (wFreshBool "g").run s1 = .ok (g, s2))
    (h3 : (wFreshBool "r").run s2 = .ok (rT, s3)) (hctx : LaidCtx κ g s3 κE rE? s4) :
    PreFacts s1 g rT rE? s4 := by
  obtain ⟨rfl, rfl⟩ | ⟨rE, rfl, h4⟩ : (rE? = none ∧ s4 = s3) ∨ ∃ rE, rE? = some rE ∧
      (wFreshBool "r").run s3 = .ok (rE, s4) := by cases κ <;> grind [LaidCtx]
  all_goals obtain ⟨k2, rfl, ha2, hk2, rfl⟩ := wFreshBool_facts h2
  all_goals obtain ⟨k3, rfl, ha3, hk3, rfl⟩ := wFreshBool_facts h3
  · constructor <;> grind [Drawn, freshName_counter_inj]
  · obtain ⟨k4, rfl, ha4, hk4, rfl⟩ := wFreshBool_facts h4
    constructor <;> grind [Drawn, freshName_counter_inj]

omit iLI iWL iOp iLF iLFs iLV in
/-- The else-arm context of a laid-out `ite`: `neg g` or `andNeg q g` (for `κ = name q`) with no
    else-arm reach name, or `name rE`. -/
private theorem LaidCtx.cases' {κ' κE' : RE P} {g' : P.Ident} {s3' s4' : WSt P}
    {rE' : Option P.Ident} (h : LaidCtx κ' g' s3' κE' rE' s4') :
    (rE' = none ∧ (κE' = .neg g' ∨ ∃ q, κ' = .name q ∧ κE' = .andNeg q g')) ∨
      ∃ x, rE' = some x ∧ κE' = .name x := by cases κ' <;> grind [LaidCtx]

omit iWL iOp iLF iLFs iLV in
/-- The prelude of a laid-out `ite` keeps a well-formed state well-formed, and its else-arm
    context is not `top`. -/
private theorem pre_wf (h2 : (wFreshBool "g").run s1 = .ok (g, s2))
    (h3 : (wFreshBool "r").run s2 = .ok (rT, s3)) (hctx : LaidCtx κ g s3 κE rE? s4)
    (hw : WFSt s1) : WFSt s4 ∧ κE ≠ .top := by
  have hw3 := (wFreshBool_walk h3).wf ((wFreshBool_walk h2).wf hw nofun) nofun
  have hW := fun {s s' : WSt P} {x : P.Ident} (h : (wFreshBool "r").run s = .ok (x, s')) =>
    (wFreshBool_walk h).wf
  cases κ <;> grind [LaidCtx]

/-- The walk states of a laid-out `ite` whose arms do not always exit: the steps from `st0` to
    `st'` and their facts (`WalkCore`, `PreFacts`, `WalkOK` of the arms, `SaveFacts`,
    `AfterFacts`), well-formedness of the intermediate states, the arms' `ArmFacts`, the
    disjointness of the scope from the arms' declarations, and at the else arm's walk input: no
    merge deeper than `d` is carried and the variables of the else-arm context are fresh names
    drawn before it, not avoided and no renamings. -/
structure LaidStates (F : P.Factory) (Lc S : List P.Ident) (κ κE : RE P) (d : Nat)
    (tss ess : PStmts P) (st0 s1 : WSt P) (g rT : P.Ident) (rE? : Option P.Ident)
    (s4 : WSt P) (Er : WRes P) (s5 : WSt P) (Tr : WRes P) (s6 : WSt P) (M : List P.Ident)
    (sv cp rs : Rope (WItem P)) (cps : List (P.Ident × P.Ident)) (s7 : WSt P)
    (gm? : Option P.Ident) (st' : WSt P) (rdc : List P.Ident) (nonnil : Prop) : Prop where
  c1 : WalkCore [] st0 s1
  pre : PreFacts s1 g rT rE? s4
  wE : WalkOK (stmtsInits ess) s4 s5
  wT : WalkOK (stmtsInits tss) s5 s6
  save : SaveFacts s6 M sv cp rs cps s7
  aft : AfterFacts κ rdc s6 s7 gm? st' nonnil
  wf1 : WFSt s1
  wf4 : WFSt s4
  wf5 : WFSt s5
  wf6 : WFSt s6
  armE : ArmFacts F Lc S κE d ess s4 Er s5
  armT : ArmFacts F Lc S (.name rT) d tss s5 Tr s6
  sE : ∀ z ∈ S, z ∉ stmtsInits ess
  sT : ∀ z ∈ S, z ∉ stmtsInits tss
  ctxE : κE ≠ .top
  high4 : ∀ k, d < k → s4.carries.getD k [] = []
  κEv4 : ∀ y ∈ RE.vars κE, (∃ b j, y = freshName b j ∧ j < s4.next) ∧
    s4.avoid.contains y = false ∧ ∀ x : P.Ident, s4.nm[x]? ≠ some y
  dead4 : DeadBelow s4
  liveK4 : LiveKeys s4


omit iLI iWL iOp iLF iLFs iLV in
/-- A renaming of a well-formed state is a fresh name with a counter below the state's counter. -/
private theorem dl_nmBelow (hw : WFSt st) {y : P.Ident} (h : st.nm[y]? = some n) :
    ∃ b j, n = freshName b j ∧ j < st.next :=
  (hw.nm_fresh y n h).2.imp fun _ ⟨j, h1, h2, _⟩ => ⟨j, h1, h2⟩

omit iLI iOp iLF iLFs iLV in
/-- A variable of the else-arm context of a laid-out `ite` is the guard, the else-arm reach or a
    variable of the context. -/
private theorem LaidCore.of_κEvars'
    (e : LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
      Ex k Lab wc rdc s1 g s2 rT s3 κE rE?
      s4 Er s5 Tr s6) {y : P.Ident} (hy : y ∈ RE.vars κE) :
    y = g ∨ rE? = some y ∨ y ∈ RE.vars κ := by
  have hc := e.ctx
  cases κ <;> simp only [LaidCtx] at hc <;> grind [RE.vars]

omit iLV in
/-- The walk states of a laid-out `ite` have the facts `LaidStates`, given the facts of the saves
    after the arms (variables `M`, to `s7`) and of the rest of the walk (`AfterFacts`). -/
private theorem LaidCore.states {nonnil : Prop}
    (e : LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
      Ex k Lab wc rdc s1 g s2 rT s3 κE rE?
      s4 Er s5 Tr s6) (hsave : SaveFacts s6 M sv cp rs cps s7)
    (haft : AfterFacts κ rdc s6 s7 gm? st' nonnil) :
    LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7 gm? st' rdc
      nonnil := by
  have c1 := wRen_walk e.run1
  have pre := pre_facts e.run2 e.run3 e.ctx
  have wE := wpList_walkOK e.runE
  have wT := wpList_walkOK e.runT
  have wf1 := c1.wf e.wf0 fun _ h => nomatch h
  obtain ⟨wf4, hκE⟩ := pre_wf e.run2 e.run3 e.ctx wf1
  have hqg4 : ∀ q g', κE = .andNeg q g' → q ≠ g' := fun q g' hq hqg => by
    rcases LaidCtx.cases' e.ctx with ⟨-, h | ⟨q', rfl, h⟩⟩ | ⟨x, -, h⟩ <;> rw [h] at hq <;> cases hq
    obtain ⟨⟨b, j, h1, h2⟩, -, -⟩ := e.ctxv q (by simp [RE.vars])
    exact (pre.drawn g (.inl rfl)).not_below ⟨b, j, hqg ▸ h1, Nat.lt_of_lt_of_le h2 c1.next⟩
  obtain ⟨-, hST, hSE⟩ := e.wfS
  have hav4 : s4.avoid = st0.avoid := by rw [pre.eq]; exact c1.avoid
  have hid : ∀ x, x ∈ Block.idents tss ∨ x ∈ Block.idents ess →
      x ∈ Block.idents [.ite (.det c) tss ess md] := fun x hx => by
    rcases hx with hx | hx <;>
      simp [Block.idents, Stmt.idents, hx, ExprOrNondet.getVars_det, getFvars_mem_exprFV]
  have hfa : ∀ x, x ∈ Block.idents tss ∨ x ∈ Block.idents ess → AvoidedIfFresh st0 x :=
    fun x hx b j hxj => e.avoidS x (List.mem_append_right _ (hid x hx)) b j hxj
  have wf5 : WFSt s5 := wE.wf wf4 fun x hx b j hxj =>
    hav4 ▸ hfa x (.inr (stmtsInits_mem_idents x hx)) b j hxj
  have wf6 : WFSt s6 := wT.wf wf5 fun x hx b j hxj =>
    wE.avoid ▸ hav4 ▸ hfa x (.inl (stmtsInits_mem_idents x hx)) b j hxj
  obtain ⟨-, -, h01, -⟩ := wRen_run e.run1
  have hL4 : ∀ (l : String) (t : Nat), s4.labelDepth[l]? = some t → t ≤ d := fun l t h =>
    (e.lab l t (by rwa [pre.eq, h01] at h)).1
  have hD4 : DeadBelow s4 := fun b j hj => Nat.lt_of_lt_of_le
    (e.dead0 b j (by rwa [pre.eq, h01] at hj)) (Nat.le_trans c1.next pre.next)
  have hhigh4 : ∀ k, d < k → s4.carries.getD k [] = [] := fun k hk =>
    (by rw [pre.eq, h01] : s4.carries = st0.carries) ▸ e.chigh k hk
  have hpreNm4 : ∀ n, (n = g ∨ n = rT ∨ rE? = some n) → ∀ x : P.Ident, s4.nm[x]? ≠ some n :=
    fun n hn x hx => (pre.drawn n hn).not_below (dl_nmBelow wf1 (by rwa [pre.eq] at hx))
  have hκv4 : ∀ y ∈ RE.vars κE, (∃ b j, y = freshName b j ∧ j < s4.next) ∧
      s4.avoid.contains y = false ∧ ∀ x : P.Ident, s4.nm[x]? ≠ some y := fun y hy => by
    rcases or_assoc.2 ((e.of_κEvars' hy).imp_right (.imp_left Or.inr)) with hp | hp
    · obtain ⟨b, j, h1, h2, -, h4⟩ := pre.drawn y hp
      exact ⟨⟨b, j, h1, h4⟩, by rw [hav4, ← c1.avoid]; exact h2, hpreNm4 y hp⟩
    · obtain ⟨⟨b, j, h1, h2⟩, h3, h4⟩ := e.ctxv y hp
      refine ⟨⟨b, j, h1, by have := c1.next; have := pre.next; omega⟩, by rw [hav4]; exact h3,
        fun x hx => (c1.nm x y (by rwa [pre.eq] at hx)).elim (h4 x) fun ⟨_, j', h5, _, h6⟩ =>
          absurd (freshName_counter_inj (h1.symm.trans h5)) (by omega)⟩
  have armE := arm_facts (F := F) e.runE hκE wf4 hSE (fun x hx b j hxj => hav4 ▸ e.avoidS x
    (List.mem_append.2 ((List.mem_append.1 hx).imp id fun h => hid x (.inr h))) b j hxj)
    hL4 hhigh4 hκv4 hqg4 hD4
  have hrTd := pre.drawn rT (.inr (.inl rfl))
  have hκv5 : ∀ y ∈ RE.vars (RE.name rT), (∃ b j, y = freshName b j ∧ j < s5.next) ∧
      s5.avoid.contains y = false ∧ ∀ x : P.Ident, s5.nm[x]? ≠ some y := fun y hy => by
    obtain rfl : y = rT := by simpa [RE.vars] using hy
    obtain ⟨b, j, h1, h2, -, h4⟩ := id hrTd
    exact ⟨⟨b, j, h1, by have := wE.next; omega⟩, by rw [wE.avoid, hav4, ← c1.avoid]; exact h2,
      wE.toWalkCore.nm_not_drawn hrTd (hpreNm4 _ (.inr (.inl rfl)))⟩
  have armT := arm_facts (F := F) e.runT nofun wf5 hST (fun x hx b j hxj => wE.avoid ▸ hav4 ▸
    e.avoidS x (List.mem_append.2 ((List.mem_append.1 hx).imp id fun h => hid x (.inl h))) b j hxj)
    (fun l t h => hL4 l t ((wE.labelDepth l).symm.trans h)) (wpList_carriesHigh e.runE hL4 hhigh4)
    hκv5 (fun _ _ h => nomatch h) (wpList_deadBelow e.runE hD4)
  have hK4 : LiveKeys s4 := fun n s h => KeyOK.of_le hav4 (Nat.le_trans c1.next pre.next)
    (e.livek n s (by rwa [pre.eq, h01] at h))
  exact ⟨c1, pre, wE, wT, hsave, haft, wf1, wf4, wf5, wf6, armE, armT,
    wfl_inits_disjoint S ess hSE, wfl_inits_disjoint S tss hST, hκE, hhigh4, hκv4, hD4, hK4⟩

omit iLV in
/-- The walk states of a laid-out `ite` whose arms do not always exit have the facts
    `LaidStates`. -/
private theorem LaidEnv.states
    (e : LaidEnv F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
      Ex k Lab wc rdc s1 g s2 rT s3 κE rE?
      s4 Er s5 Tr s6 sv cp rs cps s7 gm? s8 cr) :
    LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 (interSet Tr.A Er.R) sv cp rs
      cps s7 gm? st' rdc
      ((laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er
        (laidU κ κE rT Tr Er d)).all Rope.isNil = false) := by
  refine e.toLaidCore.states (saveRestore_run e.run7) ?_
  obtain ⟨ns, hns⟩ := saveRestore_run e.run7
  have hs7 := hns.eq
  have hn7 := hns.next
  obtain ⟨live, clock, hst, hlv, hlc⟩ : ∃ live clock,
      st' = { s8 with carries := cr, live := live, clock := clock } ∧
      (∀ n t, s8.live[n]? = some t → live[n]? = some t) ∧
      ((laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr Er
        (laidU κ κE rT Tr Er d)).all Rope.isNil = false → ∀ n ∈ rdc ++ RE.vars κ,
          live.contains n = true) := by
    rcases e.out with ⟨hn, -, hs⟩ | ⟨hn, -, -, -, hl⟩
    · exact ⟨_, _, hs, fun _ _ h => h, by simp [hn]⟩
    · obtain ⟨live, clock, hr, h1, h2, -, -⟩ :=
        liveAdd_run (rdc ++ RE.vars κ) { s8 with carries := cr }
      rw [hr] at hl
      exact ⟨live, clock, (Prod.mk.inj (Except.ok.inj hl)).2.symm, h2,
        fun _ n hn => (h1 n).2 (.inr hn)⟩
  rw [hst]
  rcases e.gm with ⟨-, x, rfl, hx⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, rfl, ha, hj, rfl⟩ := wFreshBool_facts hx
    have hd : Drawn s7 { s7 with next := j + 1 } (freshName "g" j) := ⟨_, j, rfl, ha, hj, by simp⟩
    rw [hs7]
    constructor <;> first | rfl | grind [Drawn]
  · rw [hs7]
    constructor <;> first | rfl | grind [Drawn]


omit iBE iLB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs iLV in
/-- A shadow run of a local list (only obligations) ends normally where it starts. -/
private theorem shL_of_local :
    ∀ {ss : PStmts P}, isLocal ss = true → K (.normal σ) → ShL F ss σ K
  | [], _, hK => hK
  | s :: rest, h, hK => by
    rcases s with ((_ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
      first | exact shL_of_local (ss := rest) h hK | nomatch h

omit iBE iLB iHF iSF iHI iLI iHa iHFs iWL iOp iLF iLFs iLV in
/-- A shadow run of a branch is a shadow run of its list. -/
private theorem shL_of_shB (h : ShB F ss σ K) : ShL F ss σ K := by grind [ShB, shL_of_local]

/-- A fold consing new distinct elements keeps a list without duplicates. -/
private theorem nodup_foldl_filter {α : Type} {p : α → Bool} :
    ∀ (l acc : List α), l.Nodup → acc.Nodup → (∀ x ∈ l, x ∉ acc) →
      (l.foldl (fun l x => if p x = true then x :: l else l) acc).Nodup := fun l => by
  induction l <;> grind

omit iDE iHB iHF iSF iHI iLI iHFs iWL iOp iLF iLFs iLV in
/-- The intersection of two hash sets has no duplicates. -/
private theorem interSet_nodup (a b : Std.HashSet P.Ident) : (interSet a b).Nodup := by
  unfold interSet
  split <;> rw [Std.HashSet.fold_eq_foldl_toList] <;>
    exact nodup_foldl_filter _ _ (Std.HashSet.distinct_toList.imp fun h he => by simp [he] at h)
      List.nodup_nil fun _ _ h => nomatch h

omit iBE iLB iHI iLI iHa iWL iLFs iLV in
/-- A list of deterministic `set`s of distinct bound names to variables none of them assigns,
    each value of a type of the stored value, runs; each target takes its source's value and
    every other name keeps its value. -/
private theorem run_var_sets (hF : WellFormedSemanticEvalBase F) :
    ∀ (l : List (P.Ident × P.Ident × Option P.Ty)) (σ : SemanticStore P),
      WellFormedStore σ F → (l.map (·.1)).Nodup → (∀ q ∈ l, ∀ p ∈ l, q.1 ≠ p.2.1) →
      (∀ q ∈ l, ∃ w, σ q.2.1 = some w ∧ HasVal.valueOfStoredTy (P := P) F σ q.1 w) →
      ∃ σ', MainRun F (l.map fun q =>
          .plain (.cmd (.cmd (.set q.1 (.det (HasFvar.mkVar q.2.1 q.2.2))
          .empty)))) σ [] σ' ∧ WellFormedStore σ' F ∧ (∀ q ∈ l, σ' q.1 = σ q.2.1) ∧
        (∀ n, (∀ q ∈ l, n ≠ q.1) → σ' n = σ n)
  | [], σ, hC, _, _, _ => ⟨σ, .nil, hC, nofun, fun _ _ => rfl⟩
  | q :: l, σ, hC, hnd, hst, hsrc => by
    obtain ⟨w, hw, prev, ty, hprev, hpt⟩ := hsrc q (List.mem_cons_self ..)
    obtain ⟨σ', hr, hC', hval, hoth⟩ := run_var_sets hF l _ (wfStore_update hC q.1 (hC _ _ hw))
      (List.nodup_cons.1 hnd).2 (fun p hp p' hp' => hst p (.tail _ hp) p' (.tail _ hp'))
      (fun p hp => by grind [SemanticStore.update, HasVal.valueOfStoredTy, List.nodup_cons])
    refine ⟨σ', (run_set1 hF hprev (ev_var hF.var hC hw) ⟨prev, ty, hprev, hpt⟩).append hr,
      hC', ?_, ?_⟩
    all_goals grind [SemanticStore.update, List.nodup_cons]

/-- The guarded store `σB` after the prelude of a laid-out `ite` from `σL`: the prelude names
    `pre` hold the guard's value `gv`, the save name of each triple of `ns` holds its variable's
    value, the further prelude names `ext` hold Booleans, and every other name keeps its
    value. -/
@[expose] def PreStore (F : P.Factory) (σL σB : SemanticStore P) (pre : List P.Ident) (gv : P.Val)
    (ns : List (P.Ident × P.Ident × P.Ident)) (ext : List P.Ident) : Prop :=
  (∀ n ∈ pre, σB n = some gv) ∧ (∀ q ∈ ns, σB q.2.1 = σL q.1) ∧
    (∀ n, n ∉ ext → n ∉ pre → (∀ q ∈ ns, n ≠ q.2.1) → σB n = σL n) ∧
    ∀ n ∈ ext, σB n = some (HasBool.ttVal F) ∨ σB n = some (HasBool.ffVal F)

section Parts2

variable {nonnil : Prop}
  (e : LaidCore F tE Γ Lc κ d c tss ess md st0 r st' T Y items S
    Ex k Lab wc rdc s1 g s2 rT s3 κE rE? s4
    Er s5 Tr s6)
  (hs : LaidStates F Lc S κ κE d tss ess st0 s1 g rT rE? s4 Er s5 Tr s6 M sv cp rs cps s7 gm? st'
    rdc nonnil)
include e hs
omit iOp iLF iLFs iLV

omit iLI e in
/-- The counters of the walk states of a laid-out `ite` do not decrease. -/
private theorem LaidStates.nexts : st0.next ≤ s1.next ∧ s1.next ≤ s4.next ∧ s4.next ≤ s5.next ∧
    s5.next ≤ s6.next ∧ s6.next ≤ s7.next ∧ s7.next ≤ st'.next :=
  ⟨hs.c1.next, hs.pre.next, hs.wE.next, hs.wT.next, hs.save.elim fun _ h => h.next, hs.aft.next⟩

omit iLI e in
/-- The walk states of a laid-out `ite` avoid the same names. -/
private theorem LaidStates.avoids : s1.avoid = st0.avoid ∧ s4.avoid = st0.avoid ∧
    s5.avoid = st0.avoid ∧ s6.avoid = st0.avoid ∧ st'.avoid = st0.avoid := by
  have h4 : s4.avoid = st0.avoid := (congrArg WSt.avoid hs.pre.eq).trans hs.c1.avoid
  have h6 := hs.wT.avoid.trans (hs.wE.avoid.trans h4)
  exact ⟨hs.c1.avoid, h4, hs.wE.avoid.trans h4, h6, hs.aft.avoid.trans h6⟩

omit iLI e in
/-- The prelude names of a laid-out `ite` are drawn between `st0` and `s4`. -/
private theorem LaidStates.preDrawn (hn : n = g ∨ n = rT ∨ rE? = some n) :
    Drawn st0 s4 n := (hs.pre.drawn n hn).of_le hs.c1.avoid hs.c1.next

omit e in
/-- The prelude names of a laid-out `ite` are not renamings of the states after the prelude. -/
private theorem LaidStates.preNm (hn : n = g ∨ n = rT ∨ rE? = some n) (x : P.Ident) :
    s4.nm[x]? ≠ some n ∧ s5.nm[x]? ≠ some n ∧ s6.nm[x]? ≠ some n ∧ st'.nm[x]? ≠ some n := by
  have hd := hs.pre.drawn n hn
  have h4 : ∀ x : P.Ident, s4.nm[x]? ≠ some n := fun x hx =>
    hd.not_below (dl_nmBelow hs.wf1 (by rwa [hs.pre.eq] at hx))
  have h5 := hs.wE.toWalkCore.nm_not_drawn hd h4
  have h6 := hs.wT.toWalkCore.nm_not_drawn (hd.mono hs.wE.next) h5
  exact ⟨h4 x, h5 x, h6 x, hs.aft.nm ▸ h6 x⟩

omit e in
/-- A name drawn after the arms of a laid-out `ite` is not a renaming of the final state. -/
private theorem LaidStates.lateNm (hn : ∃ b j, n = freshName b j ∧ s6.next ≤ j)
    (x : P.Ident) : st'.nm[x]? ≠ some n := fun hx => by
  obtain ⟨-, b, j, h1, h2, -⟩ := hs.wf6.nm_fresh x n (by rwa [hs.aft.nm] at hx)
  exact hn.elim fun b' ⟨j', h3, h4⟩ => absurd (freshName_counter_inj (h1.symm.trans h3)) (by omega)

omit e in
/-- The prelude names of a laid-out `ite` are not in the back map up to the then arm's walk
    output. -/
private theorem LaidStates.preBack (hn : n = g ∨ n = rT ∨ rE? = some n) :
    s4.back[n]? = none ∧ s5.back[n]? = none ∧ s6.back[n]? = none := by
  have hd := hs.pre.drawn n hn
  have h4 : s4.back[n]? = none := hs.pre.eq ▸
    Option.eq_none_iff_forall_ne_some.2 fun x hx => hd.not_below (hs.wf1.back_fresh n x hx)
  have h5 : s5.back[n]? = none := Classical.byContradiction fun h =>
    hd.not_freshAt (hs.wE.back n (by rwa [h4]))
  exact ⟨h4, h5, Classical.byContradiction fun h =>
    (hd.mono hs.wE.next).not_freshAt (hs.wT.back n (by rwa [h5]))⟩

/-- A guarded store that binds no name the rest declares (`FreshInv` at the walk output of a
    laid-out `ite`) binds neither its prelude names nor the names drawn after its arms. -/
private theorem LaidCore.unbound (hf : FreshInv Lc Ex st' σL)
    (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) : σL n = none := by
  have hnx := hs.nexts
  have hav := hs.avoids
  obtain ⟨hd, hnm⟩ : Drawn st0 st' n ∧ ∀ x : P.Ident, st'.nm[x]? ≠ some n := hn.elim
    (fun hn => ⟨(hs.preDrawn hn).mono (by omega), fun x => (hs.preNm hn x).2.2.2⟩) fun hn =>
    ⟨hn.of_le hav.2.2.2.1 (by omega), hs.lateNm (hn.elim fun b ⟨j, h1, _, h2, _⟩ => ⟨b, j, h1, h2⟩)⟩
  refine Option.eq_none_iff_forall_ne_some.2 fun w hσ => ?_
  obtain ⟨b, j, h1, h2, h3, h4⟩ := hd
  exact ((hf n (by simp [hσ])).2 b j h1 (by rw [hav.2.2.2.2]; exact h2)).elim (fun h => by omega)
    fun ho1 => ho1.elim (fun h => h.elim fun x hx => hnm x hx)
    fun h => absurd (e.exc n h).1 fun hlt => by have := hlt b j h1; omega

/-- The label depths are those of `st0` up to the arms' walks. -/
private theorem LaidCore.labels (l : String) : s4.labelDepth[l]? = st0.labelDepth[l]? ∧
    s5.labelDepth[l]? = st0.labelDepth[l]? := by
  obtain ⟨-, -, h1, -⟩ := wRen_run e.run1
  have h4 : s4.labelDepth[l]? = st0.labelDepth[l]? := by rw [hs.pre.eq, h1]
  exact ⟨h4, (hs.wE.labelDepth l).trans h4⟩

omit e in
/-- The final type maps extend the types of the walk state after the then arm, up to names
    still to be declared or drawn. -/
private theorem LaidStates.fin6 (hfin : FinalOK Lc st' T Y) : FinalOK Lc s6 T Y := by
  obtain ⟨ns, -, -, -, -, -, -, hdr, htyo, h67, h7⟩ := hs.save
  obtain ⟨h1, h2, h3⟩ := hfin
  obtain ⟨-, htk, hav, -, -, -, htf, hty, -⟩ := hs.aft
  have hnx := hs.nexts
  refine ⟨fun n ty hn => ?_, fun n x hn => ?_, fun n hn => ?_⟩
  · by_cases hg : Drawn s7 st' n <;> grind [Drawn]
  · have hb := hs.wf6.tyOf_fresh n x hn
    have h76 := htyo n fun q hq => ⟨fun h => (h ▸ (hdr q hq).1).not_below hb,
      fun h => (h ▸ (hdr q hq).2.1).not_below hb⟩
    grind [Drawn, freshName_counter_inj]
  · by_cases hg : Drawn s7 st' n <;> grind [Drawn]

omit iWL e hs in
/-- A walk step keeps the declared type of a name drawn before it that is no renaming and that
    the step does not declare. -/
private theorem WalkCore.tys_drawn {D : List P.Ident} {s st' : WSt P}
    (h : WalkCore D st st') (hd : Drawn s st n) (hnm : ∀ x : P.Ident, st.nm[x]? ≠ some n)
    (hD : n ∉ D) : st'.tys[n]? = st.tys[n]? :=
  Classical.byContradiction fun hne => (h.tys n hne).elim (fun h => hD h.1) fun h =>
    h.elim (fun ⟨x, hx⟩ => hnm x hx) hd.not_freshAt

omit iLI hs in
/-- A name of an arm of a laid-out `ite` is avoided by `st0` if it has the form of a fresh
    name. -/
private theorem LaidCore.avoidArm {x : P.Ident}
    (h : x ∈ Block.idents tss ∨ x ∈ Block.idents ess) : AvoidedIfFresh st0 x := fun b j =>
  e.avoidS x (by rcases h with h | h <;> simp [Block.idents, Stmt.idents, h]) b j

omit iLI hs in
/-- A name of the scope or of an arm of a laid-out `ite` is avoided by `st0` if it has the form
    of a fresh name. -/
private theorem LaidCore.avoidSArm {x : P.Ident} (hss : ss = tss ∨ ss = ess)
    (h : x ∈ S ++ Block.idents ss) : AvoidedIfFresh st0 x := fun b j =>
  e.avoidS x (by rcases hss with rfl | rfl <;> grind [Block.idents, Stmt.idents]) b j

/-- The prelude names and the merge guard of a laid-out `ite` have the Boolean final type. -/
private theorem LaidCore.preT
    (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ gm? = some n) : T[n]? = some HasBool.boolTy := by
  have hnx := hs.nexts
  have hav := hs.avoids
  have hfin := e.fin.1 n HasBool.boolTy
  rcases hn with hn | hn
  · have hd := hs.preDrawn hn
    have hnD : ∀ ss, ss = tss ∨ ss = ess → n ∉ stmtsInits ss := fun ss hss hi => by
      obtain ⟨b, j, h1, h2, -⟩ := hd
      simp [e.avoidSArm hss (List.mem_append_right _ (stmtsInits_mem_idents n hi)) b j h1] at h2
    have h5 := hs.wE.toWalkCore.tys_drawn hd (fun x => (hs.preNm hn x).1) (hnD ess (.inr rfl))
    have h6 := hs.wT.toWalkCore.tys_drawn (hd.mono hs.wE.next) (fun x => (hs.preNm hn x).2.1)
      (hnD tss (.inl rfl))
    have h7 := hs.aft.tys n fun h => hd.disj h (by omega)
    grind [Drawn, hs.pre.tys n hn, freshName_counter_inj]
  · have h7 : s7.avoid = s6.avoid := hs.save.elim fun _ h => by rw [h.eq]
    grind [Drawn, hs.aft.tysGm n hn, hs.aft.gmDrawn n hn, freshName_counter_inj]

omit iLI e hs in
/-- The resolved output of a laid-out `ite` with a nonempty body: the guard's `init` followed by
    the resolved parts. -/
private theorem LaidEnv.split
    (e : LaidEnv F tE Γ Lc κ d c tss ess md st0 r st' T Y items S Ex k Lab wc
      rdc s1 g s2 rT s3 κE rE? s4 Er s5 Tr s6 sv cp rs cps s7 gm? s8 cr)
    (hnn : (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr
      Er (laidU κ κE rT Tr Er d)).all Rope.isNil = false) :
    ∃ ce iRT iGM iSV iT iCP iRS iRE iE iMG iU, resolveE T Y (kAnd κ wc) = .ok ce ∧
      resolveItems T Y (if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then Rope.nil
        else Rope.one (WItem.init rT (.known HasBool.boolTy) (some (.var g)))).toList = .ok iRT ∧
      resolveItems T Y (match gm? with
        | some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var g)))
        | none => Rope.nil).toList = .ok iGM ∧
      resolveItems T Y sv.toList = .ok iSV ∧ resolveItems T Y Tr.out.toList = .ok iT ∧
      resolveItems T Y cp.toList = .ok iCP ∧ resolveItems T Y rs.toList = .ok iRS ∧
      resolveItems T Y (match rE? with
        | some r => if (Er.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then Rope.nil
          else Rope.one (WItem.init r (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)))
        | none => Rope.nil).toList = .ok iRE ∧
      resolveItems T Y Er.out.toList = .ok iE ∧
      resolveItems T Y (laidMerges gm? Er.A (cps.filter fun p => liveBefore s6 p.1 s4.clock)).toList
        = .ok iMG ∧
      resolveItems T Y (laidU κ κE rT Tr Er d).toList = .ok iU ∧
      items = .plain (mkInit g HasBool.boolTy (.det ce)) ::
        (iRT ++ (iGM ++ (iSV ++ (iT ++ (iCP ++ (iRS ++ (iRE ++ (iE ++ (iMG ++ iU))))))))) := by
  rcases e.out with ⟨h, -⟩ | ⟨-, hout, -⟩
  · simp [h] at hnn
  obtain ⟨a, its, ha, hits, rfl⟩ := resolveItems_cons_ok (hout ▸ e.res)
  obtain ⟨ty, ce, rfl, hce, rfl⟩ := resolveItem_init_inv ha
  simp only [laidParts, List.flatMap_cons, List.flatMap_nil, List.append_nil, resolveItems_append]
    at hits
  grind

omit e hs in
/-- Picking one of the last two components of each triple, in order, gives a sublist of the list
    of their last two components. -/
private theorem sub_flat {α : Type} {f : α × α × α → α} (ns : List (α × α × α))
    (hf : ∀ q, [f q].Sublist [q.2.1, q.2.2] := by simp) :
    (ns.map f).Sublist (ns.flatMap fun q => [q.2.1, q.2.2]) :=
  ns.rec .slnil fun q _ ih => (hf q).append ih

include iOp iLF in
omit iLB iHI iLI e hs in
/-- Initializing, for each triple `q` of `ns`, the name `f q` to the variable `q.1` runs from a
    store binding none of these names and binding the variables to values of their final types:
    each name takes its variable's value, and every variable has a final type. -/
private theorem nsInitsRun (hF : WellFormedSemanticEvalBase F)
    (f : P.Ident × P.Ident × P.Ident → P.Ident) (hC : WellFormedStore σ1 F) {its : List (Item P)}
    (hits : resolveItems T Y (ns.map fun q => .init (f q) (.of q.1) (some (.var q.1))) = .ok its)
    (hnd : (ns.map f).Nodup) (h0 : ∀ q ∈ ns, σ1 (f q) = none)
    (hsrc : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty) :
    ∃ σC, MainRun F its σ1 [] σC ∧ WellFormedStore σC F ∧ (∀ q ∈ ns, σC (f q) = σ1 q.1) ∧
      (∀ n, (∀ q ∈ ns, n ≠ f q) → σC n = σ1 n) ∧ ∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty := by
  obtain ⟨l, h1, h2, rfl⟩ := resolve_var_inits (ns.map fun q => (f q, .of q.1, q.1)) its
    (by rwa [List.map_map])
  have hl : ∀ p ∈ l, ∃ q ∈ ns, f q = p.1 ∧ q.1 = p.2.2.1 ∧ tyOfName T Y q.1 = .ok p.2.1 :=
    fun p hp => (h2 p hp).elim fun _ ⟨hm0, h3⟩ =>
      (List.mem_map.1 hm0).elim fun q ⟨hq, he⟩ => ⟨q, hq, (he ▸ h3 :)⟩
  have hr : ∀ q ∈ ns, ∃ p ∈ l, p.1 = f q ∧ p.2.2.1 = q.1 := fun q hq => by
    obtain ⟨p, hp, he⟩ := List.mem_map.1 (show (f q, q.1) ∈ l.map fun p => (p.1, p.2.2.1) by
      rw [h1]; exact List.mem_map.2 ⟨_, List.mem_map_of_mem hq, rfl⟩)
    exact ⟨p, hp, Prod.mk.inj he⟩
  have hfst : l.map (·.1) = ns.map f := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) h1
  obtain ⟨σC, hrun, hC', hval, hoth⟩ := run_var_inits hF l σ1 hC (hfst ▸ hnd)
    (fun p hp => (hl p hp).elim fun q ⟨hq, hf, _⟩ => hf ▸ h0 q hq)
    (fun p hp => (hl p hp).elim fun q ⟨hq, _, he, ht⟩ =>
      (hsrc q hq).elim fun w ⟨hw, hty⟩ => ⟨w, he ▸ hw, hty _ ht⟩)
  refine ⟨σC, hrun, hC', fun q hq => ?_, fun n hn => hoth n fun p hp => ?_, fun q hq => ?_⟩
  · exact (hr q hq).elim fun p ⟨hp, h3, h4⟩ => by rw [← h3, hval p hp, h4]
  · exact (hl p hp).elim fun q ⟨hq, hf, _⟩ => hf ▸ hn q hq
  · obtain ⟨p, hp, -, h4⟩ := hr q hq
    exact (hl p hp).elim fun q' ⟨_, _, h5, h6⟩ => ⟨_, h4 ▸ h5 ▸ h6⟩

include iOp iLF iHFs iLV in
/-- The prelude of a laid-out `ite` with a nonempty body, the copy `qm` of the enclosing context
    included, runs from a value-valued guarded store `σL` that binds none of the names the
    prelude declares, when the guard evaluates to a Boolean `gv`, the enclosing context variable
    copied is a Boolean and the saved variables are bound to values of their final types; it
    reaches a store `PreStore` describes (`qm` holding a Boolean), the then-arm reach `rT`
    declared only when its `init` is emitted. -/
private theorem LaidCore.preRunQ (hns : SaveNs s6 M sv cp rs cps s7 ns)
    (hfr : FreshInv Lc Ex st' σL) (hC : WellFormedStore σL F)
    {ce : P.Expr} {iRT iGM iQM iSV : List (Item P)}
    (hRT : resolveItems T Y (if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then Rope.nil
        else Rope.one (WItem.init rT (.known HasBool.boolTy) (some (.var g)))).toList = .ok iRT)
    (hGM : resolveItems T Y (match gm? with
        | some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var g)))
        | none => Rope.nil).toList = .ok iGM) (hQM : resolveItems T Y (match κ, qm? with
      | .name q, some x => Rope.one (WItem.init x (.known HasBool.boolTy) (some (.var q)))
      | _, _ => Rope.nil).toList = .ok iQM)
    (hqmD : ∀ x, qm? = some x → Drawn s7 st' x ∧ ∀ y, gm? = some y → x ≠ y)
    (hqv : ∀ q x, κ = .name q → qm? = some x →
      σL q = some (HasBool.ttVal F) ∨ σL q = some (HasBool.ffVal F))
    (hSV : resolveItems T Y sv.toList = .ok iSV)
    (hce : P.eval F σL ce = some gv) (hgb : gv = HasBool.ttVal F ∨ gv = HasBool.ffVal F)
    (hsrc : ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty) :
    ∃ σB, MainRun F (.plain (mkInit g HasBool.boolTy (.det ce)) :: (iRT ++ (iGM ++ (iQM ++ iSV))))
        σL [] σB ∧ WellFormedStore σB F ∧
      PreStore F σL σB (g :: ((if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then []
        else [rT]) ++ gm?.toList)) gv ns (laidQm κ qm?) ∧
      ∀ q x, κ = .name q → qm? = some x → σB x = σL q := by
  have hnx := hs.nexts
  have hnd : ∀ (b : Bool) (lA lQ : List (P.Ident × P.Ty × P.Ident × Option P.Ty)),
      lA.map (·.1) = (if b = true then [] else [rT]) ++ gm?.toList →
      lQ.map (·.1) = laidQm κ qm? → ((lA ++ lQ).map (·.1)).Nodup := fun b lA lQ hlA hlQ => by
    have hrT : ∀ x, Drawn s7 st' x → rT ≠ x := fun x hx h =>
      (hs.preDrawn (.inr (.inl rfl))).disj (h ▸ hx) (by omega)
    have hgm : ∀ y, gm? = some y → Drawn s7 st' y ∧ ∀ x, qm? = some x → y ≠ x := fun y hy =>
      ⟨hs.aft.gmDrawn y hy, fun x hx h => (hqmD x hx).2 y hy h.symm⟩
    have hQ : (laidQm κ qm?).Sublist qm?.toList := by
      cases qm? <;> cases κ <;> first | exact .refl _ | exact List.nil_sublist _
    rw [List.map_append, hlA, hlQ]
    refine (hQ.append_left _).nodup ?_
    clear hRT hGM hQM hqv hSV hce hsrc hC hfr hQ hnx hns e hs hlA hlQ
    cases b <;> cases gm? <;> cases qm? <;> simp_all
  have hun : ∀ n, (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n → σL n = none :=
    fun n hn => e.unbound hs hfr hn
  obtain ⟨l1, rfl, hm1, hs1⟩ : ∃ l1 : List (P.Ident × P.Ty × P.Ident × Option P.Ty),
      iRT = l1.map (fun q => .plain (mkInit q.1 q.2.1 (.det (HasFvar.mkVar q.2.2.1 q.2.2.2)))) ∧
      l1.map (·.1) = (if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then []
        else [rT]) ∧ ∀ q ∈ l1, q.1 = rT ∧ q.2.1 = HasBool.boolTy ∧ q.2.2.1 = g := by
    rcases resolve_opt_init hRT with ⟨hb, rfl⟩ | ⟨hb, ty, e', rfl, he, rfl⟩
    · exact ⟨[], rfl, by simp [hb], nofun⟩
    · obtain ⟨t, rfl⟩ := resolveE_var he
      exact ⟨[(rT, _, g, some t)], rfl, by simp [hb], by simp⟩
  obtain ⟨l2, rfl, hm2, hs2⟩ : ∃ l2 : List (P.Ident × P.Ty × P.Ident × Option P.Ty),
      iGM = l2.map (fun q => .plain (mkInit q.1 q.2.1 (.det (HasFvar.mkVar q.2.2.1 q.2.2.2)))) ∧
      l2.map (·.1) = gm?.toList ∧
        ∀ q ∈ l2, gm? = some q.1 ∧ q.2.1 = HasBool.boolTy ∧ q.2.2.1 = g := by
    cases gm? with
    | none => exact ⟨[], resolve_isNil rfl hGM, rfl, nofun⟩
    | some x =>
      obtain ⟨a, ha, rfl⟩ := resolve_one hGM
      obtain ⟨ty, e', rfl, he, rfl⟩ := resolveItem_init_inv ha
      obtain ⟨t, rfl⟩ := resolveE_var he
      exact ⟨[(x, _, g, some t)], rfl, rfl, by simp⟩
  obtain ⟨lQ, rfl, hlQ, hqQ⟩ : ∃ lQ : List (P.Ident × P.Ty × P.Ident × Option P.Ty),
      iQM = lQ.map (fun q => .plain (mkInit q.1 q.2.1 (.det (HasFvar.mkVar q.2.2.1 q.2.2.2)))) ∧
      lQ.map (·.1) = laidQm κ qm? ∧
      ∀ q ∈ lQ, q.2.1 = HasBool.boolTy ∧ κ = .name q.2.2.1 ∧ qm? = some q.1 := by
    cases κ <;> cases qm? <;> try exact ⟨[], resolve_isNil rfl hQM, rfl, nofun⟩
    rename_i q x
    obtain ⟨a, ha, rfl⟩ := resolve_one hQM
    obtain ⟨ty, e', rfl, he, rfl⟩ := resolveItem_init_inv ha
    obtain ⟨t, rfl⟩ := resolveE_var he
    exact ⟨[(x, HasBool.boolTy, q, some t)], rfl, rfl, by simp⟩
  have hmem : ∀ q ∈ l1 ++ l2 ++ lQ, (q.1 = rT ∨ gm? = some q.1 ∨ qm? = some q.1) ∧
      (q.2.2.1 = g ∨ κ = .name q.2.2.1 ∧ qm? = some q.1) ∧ q.2.1 = HasBool.boolTy := fun q hq =>
    (List.mem_append.1 hq).elim (fun hq => (List.mem_append.1 hq).elim
      (fun hq => (hs1 q hq).elim fun h1 h2 => ⟨.inl h1, .inl h2.2, h2.1⟩)
      fun hq => (hs2 q hq).elim fun h1 h2 => ⟨.inr (.inl h1), .inl h2.2, h2.1⟩)
      fun hq => (hqQ q hq).elim fun h1 h2 => ⟨.inr (.inr h2.2), .inr h2, h1⟩
  have hg0 := hun g (.inl (.inl rfl))
  obtain ⟨u1, u2⟩ := update_facts σL g gv
  have hb1 : ∀ n, σL n ≠ none → SemanticStore.update σL g gv n = σL n := fun n hn =>
    u2 n fun h => hn (h ▸ hg0)
  have hqb : ∀ q x, κ = .name q → qm? = some x → σL q ≠ none := fun q x hκ hx => by
    rcases hqv q x hκ hx with h | h <;> simp [h]
  have hpd : ∀ p ∈ l1 ++ l2 ++ lQ, p.1 = rT ∨ Drawn s7 st' p.1 := fun p hp =>
    (hmem p hp).1.imp_right fun h => h.elim (hs.aft.gmDrawn _) fun h => (hqmD _ h).1
  have hfr1 : ∀ p ∈ l1 ++ l2 ++ lQ, p.1 ≠ g ∧ σL p.1 = none := fun p hp =>
    (hpd p hp).elim (fun h => ⟨h ▸ hs.pre.g_rT.symm, hun _ (.inl (.inr (.inl h)))⟩)
      fun h => ⟨fun he => (hs.preDrawn (.inl rfl)).disj (he ▸ h) (by omega),
        hun _ (.inr (h.of_le (by rw [hns.eq]) (by omega)))⟩
  obtain ⟨σ2, hr2, hC2, hv2, ho2⟩ := run_var_inits e.hF (l1 ++ l2 ++ lQ) _
    (wfStore_update_bool hC g hgb) (hnd _ _ _ (by rw [List.map_append, hm1, hm2]) hlQ)
    (fun q hq => (u2 _ (hfr1 q hq).1.symm).trans (hfr1 q hq).2) (fun q hq => by
      obtain ⟨-, h | ⟨hκ, hx⟩, ht⟩ := hmem q hq
      · exact ⟨gv, h ▸ u1, ht ▸ bool_valueOfTy hgb⟩
      · rcases hqv _ _ hκ hx with h | h <;>
          exact ⟨_, (hb1 _ (hqb _ _ hκ hx)).trans h, ht ▸ bool_valueOfTy (by simp)⟩)
  have hbnd : ∀ n, σL n ≠ none → σ2 n = σL n := fun n hn =>
    (ho2 n fun p hp h => hn (h ▸ (hfr1 p hp).2)).trans (hb1 n hn)
  have hsv : ∀ q ∈ ns, ∀ m, (m = g ∨ m = rT ∨ Drawn s7 st' m) → q.2.1 ≠ m := fun q hq m hm h => by
    have hd := h ▸ (hns.drawn q hq).1
    exact (or_assoc.2 hm).elim (fun hm => (hs.preDrawn (hm.imp_right .inl)).disj hd (by omega))
      (hd.disj · (by omega))
  obtain ⟨σB, hr3, hC3, hv3, ho3, -⟩ := nsInitsRun e.hF (·.2.1) hC2 (hns.saves ▸ hSV)
    ((sub_flat ns).nodup hns.nodup) (fun q hq => (ho2 _ fun p hp =>
      hsv q hq p.1 ((hpd p hp).elim (.inr ∘ .inl) (.inr ∘ .inr))).trans
      ((u2 _ (hsv q hq g (.inl rfl)).symm).trans
        (hun _ (.inr ((hns.drawn q hq).1.mono (by omega))))))
    (fun q hq => (hsrc q hq).elim fun w h => ⟨w, (hbnd _ (by simp [h.1])).trans h.1, h.2⟩)
  have h5 : ∀ q x, κ = .name q → qm? = some x → σB x = σL q := fun q x hκ hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hlQ ▸ (show x ∈ laidQm κ qm? by simp [laidQm, hκ, hx]))
    obtain ⟨-, hκ', -⟩ := hqQ p hp
    cases hκ.symm.trans hκ'
    rw [ho3 _ fun q' hq' => (hsv q' hq' _ (.inr (.inr (hqmD _ hx).1))).symm,
      hv2 p (List.mem_append_right _ hp), hb1 _ (hqb _ _ hκ hx)]
  refine ⟨σB, by simpa using (run_init1 e.hF hg0 hce (bool_valueOfTy hgb)).append (hr2.append hr3),
    hC3, ⟨fun n hn => ?_, fun q hq => ?_, fun n h1 h2 h3 => ?_, fun n hn => ?_⟩, h5⟩
  · rcases List.mem_cons.1 hn with rfl | hn
    · rw [ho3 _ fun q hq => (hsv q hq _ (.inl rfl)).symm, ho2 _ fun p hp => (hfr1 p hp).1.symm, u1]
    · rw [← hm1, ← hm2, ← List.map_append] at hn
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hn
      have hg : p.2.2.1 = g := (List.mem_append.1 hp).elim (fun h => (hs1 _ h).2.2) (hs2 _ · |>.2.2)
      rw [ho3 _ fun q hq => (hsv q hq _ (.inr (hpd p (List.mem_append_left _ hp)))).symm,
        hv2 p (List.mem_append_left _ hp), hg, u1]
  · exact (hsrc q hq).elim fun w h => (hv3 q hq).trans (hbnd _ (by simp [h.1]))
  · rw [← hm1, ← hm2, ← List.map_append] at h2
    rw [ho3 n h3, ho2 n fun p hp he => (List.mem_append.1 hp).elim
      (fun h => h2 (.tail _ (he ▸ List.mem_map_of_mem h)))
      fun h => h1 (hlQ ▸ he ▸ List.mem_map_of_mem h), u2 n fun h => h2 (h ▸ .head _)]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hlQ ▸ hn)
    exact (hqQ p hp).elim fun _ ⟨hκ, hx⟩ => h5 _ _ hκ hx ▸ hqv _ _ hκ hx

omit iDE iHB iHF iSF iHI iLI iWL e hs in
/-- The continuation of the then arm (followed by the else arm) reads what the `ite`'s does. -/
private theorem contFV_arms_sub {x : P.Ident}
    (h : x ∈ contFV (tss :: ess :: k)) : x ∈ contFV ([.ite (.det c) tss ess md] :: k) := by
  grind [mem_contFV_cons, Block.freeVars, Stmt.freeVars]

omit iLI e in
/-- The current names after the then arm are those at the walk output of the `ite`. -/
private theorem LaidStates.cur6 (z : P.Ident) : curName s6 z = curName st' z :=
  curName_eq_of_nm_taken hs.aft.nm.symm hs.aft.taken.symm z

/-- A guarded store that binds no name the rest declares binds neither the prelude names nor
    the save names of a laid-out `ite`. -/
private theorem LaidCore.preUnbound (hns : SaveNs s6 M sv cp rs cps s7 ns)
    (hfr : FreshInv Lc Ex st' σL)
    (hn : n ∈ g :: rT :: gm?.toList ∨ ∃ q ∈ ns, n = q.2.1) : σL n = none := by
  have hnx := hs.nexts
  refine e.unbound hs hfr ?_
  rcases hn with hn | ⟨q, hq, rfl⟩
  · simp only [List.mem_cons, Option.mem_toList] at hn
    exact hn.elim (fun h => .inl (.inl h)) fun hn => hn.elim (fun h => .inl (.inr (.inl h)))
      fun hn => .inr ((hs.aft.gmDrawn _ hn).of_le (by rw [hns.eq]) (by omega))
  · exact .inr ((hns.drawn q hq).1.mono (by omega))

omit iWL e hs in
/-- `FreshInv` carries over to an earlier walk state with fewer declared names, the same avoided
    names, a smaller counter and fewer renamings, the exceptions at the later state being
    exceptions or fresh names at the earlier one. -/
private theorem of_freshPost {Ex' : P.Ident → Prop} {st1 : WSt P} (hf : FreshInv Lc Ex' st σL)
    (htaken : ∀ y, st1.taken.contains y = true → st.taken.contains y = true)
    (hav : st.avoid = st1.avoid) (hnx : st1.next ≤ st.next)
    (hnm : ∀ (x y : P.Ident), st.nm[x]? = some y → st1.nm[x]? = some y ∨ FreshAt st1 y)
    (hEx : ∀ y, Ex' y → Ex y ∨ ∀ b j, y = freshName b j → st1.next ≤ j) :
    FreshInv Lc Ex st1 σL := fun y hy => by
  have h := hf y hy
  grind [FreshAt, freshName_counter_inj]

/-- The prelude store of a laid-out `ite` agrees with the store before it on the names bound
    there. -/
private theorem LaidCore.preKeep (hns : SaveNs s6 M sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hfr : FreshInv Lc Ex st' σL) (hB : PreStore F σL σB (g :: rT :: gm?.toList) gv ns ext)
    (hext : ∀ x ∈ ext, Drawn s7 st' x) (hn : (σL n).isSome) :
    σB n = σL n := by
  refine hB.2.2.1 n (fun h => ?_) (fun h => ?_) fun q hq h => ?_
  · simp [e.unbound hs hfr (.inr ((hext n h).of_le (by rw [hns.eq]) hs.nexts.2.2.2.2.1))] at hn
  · simp [e.preUnbound hs hns hfr (.inl h)] at hn
  · simp [e.preUnbound hs hns hfr (.inr ⟨q, hq, h⟩)] at hn

/-- The prelude store of a laid-out `ite` holds values of their final types, given a store
    before it that does, and binds no name the rest of the then arm's walk declares, the prelude
    names `g` and `rT` excepted. -/
private theorem LaidCore.preB (hns : SaveNs s6 M sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hgv : gv = HasBool.ttVal F ∨ gv = HasBool.ffVal F) (hfr : FreshInv Lc Ex st' σL)
    (hB : PreStore F σL σB (g :: rT :: gm?.toList) gv ns ext) (hext : ∀ x ∈ ext, Drawn s7 st' x)
    (hextT : ∀ x ∈ ext, T[x]? = some HasBool.boolTy)
    (hgt : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) :
    (∀ n w, σB n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) ∧ FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 σB := by
  have hnx := hs.nexts
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hB
  refine ⟨fun n w hn hY => ?_, fun y hy => ?_⟩
  · by_cases h1 : n ∈ ext
    · exact fun _ => tyOfName_bool (hextT n h1) (by grind [hB4 n h1])
    by_cases h2 : n ∈ g :: rT :: gm?.toList
    · exact fun _ => tyOfName_bool (e.preT hs (by grind)) (by grind [hB1 n h2])
    by_cases h3 : ∃ q ∈ ns, n = q.2.1
    · obtain ⟨q, hq, rfl⟩ := h3
      obtain ⟨hd, -, hty, -⟩ := hns.drawn q hq
      simp [e.fin.2.1 q.2.1 q.1 ((hs.aft.tyOf _ fun h => hd.disj h (by omega)).trans hty)] at hY
    exact hgt n w (hB3 n h1 h2 (fun q hq h => h3 ⟨q, hq, h⟩) ▸ hn) hY
  · by_cases hsp : y ∈ ext ∨ y ∈ g :: rT :: gm?.toList ∨ ∃ q ∈ ns, y = q.2.1
    · obtain ⟨b, j, h1, h2, h3⟩ : ∃ b j, y = freshName b j ∧ s6.avoid.contains y = false ∧
          (y = g ∨ y = rT ∨ s6.next ≤ j) := by
        rcases hsp with h | hn
        · obtain ⟨b, j, h1, h2, h3, -⟩ := hext y h
          exact ⟨b, j, h1, by rwa [hns.eq] at h2, .inr (.inr (by omega))⟩
        have hav := hs.avoids
        have hav7 : s7.avoid = s6.avoid := by rw [hns.eq]
        rcases hn with hn | ⟨q, hq, rfl⟩
        · simp only [List.mem_cons, Option.mem_toList] at hn
          rcases or_assoc.2 hn with hn | hn
          · grind [Drawn, hs.preDrawn (hn.imp_right .inl)]
          · grind [Drawn, hs.aft.gmDrawn _ hn]
        · grind [Drawn, (hns.drawn q hq).1]
      grind [freshName_counter_inj]
    · rw [hB3 y (fun h => hsp (.inl h)) (fun h => hsp (.inr (.inl h)))
        fun q hq h => hsp (.inr (.inr ⟨q, hq, h⟩))] at hy
      exact of_freshPost (Ex := fun y => Ex y ∨ y = g ∨ y = rT) hfr (fun _ h => hs.aft.taken ▸ h)
        hs.aft.avoid (by omega) (fun x y h => .inl (hs.aft.nm ▸ h)) (fun _ h => .inl (.inl h)) y hy

omit iLI e hs in
/-- `OnInv` carries over from the walk output of a laid-out `ite` to a walk state `s` and a
    guarded store `σB`, for fewer read variables, when every current name at `s` of a variable in
    scope is its current name at the walk output (live there when live at `s`), and `σB` agrees
    with the guarded store where that is bound, is value-valued, holds values of their final
    types, binds no name the rest declares and makes the new context `κ'` hold. -/
private theorem OnInv.toArm {Ex' : P.Ident → Prop} {s : WSt P} {κ' : RE P} {V V' : List P.Ident}
    {σB : SemanticStore P} (hon : OnInv F T Y Lc Ex st' κ S V σ σL) (hV : ∀ x ∈ V', x ∈ V)
    (hcur : ∀ z ∈ S, ∀ n, curName s z = some n →
      curName st' z = some n ∧ (s.live.contains n = true → st'.live.contains n = true))
    (hkeep : ∀ n, (σL n).isSome → σB n = σL n) (hC : WellFormedStore σB F)
    (hgt : ∀ n w, σB n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hfr : FreshInv Lc Ex' s σB) (hr : κ'.Holds F σB) : OnInv F T Y Lc Ex' s κ' S V' σ σB := by
  obtain ⟨⟨hA, hD, hL, hU, hC0, -, -, hT, -⟩, -⟩ := hon
  exact ⟨⟨by grind, by grind, by grind, hU, hC0, hC, hgt, by grind, hfr⟩, hr⟩

/-- On the then path of a laid-out `ite` (the context holding, the condition true), the store
    after the prelude, with the then-arm reach `rT` bound, relates to the loop-free store before
    the then arm as the then arm's walk requires (`OnInv` at the then arm's walk output under
    `name rT`, the prelude names `g` and `rT` excepted). -/
private theorem LaidCore.thenT (hns : SaveNs s6 M sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hB : PreStore F σL σB (g :: rT :: gm?.toList) (HasBool.ttVal F) ns ext)
    (hext : ∀ x ∈ ext, Drawn s7 st' x) (hextT : ∀ x ∈ ext, T[x]? = some HasBool.boolTy)
    (hCB : WellFormedStore σB F) :
    OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 (.name rT) S
      (contFV (tss :: ess :: k)) σ σB :=
  hon.toArm (fun _ hx => contFV_arms_sub hx) (fun z _ n hn => ⟨hs.cur6 z ▸ hn, fun h => by
      grind [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists, hs.aft.live n]⟩)
    (fun _ hn => e.preKeep hs hns hon.fresh hB hext hn) hCB
    (e.preB hs hns (.inl rfl) hon.fresh hB hext hextT hon.gtyped).1
    (e.preB hs hns (.inl rfl) hon.fresh hB hext hextT hon.gtyped).2 (hB.1 rT (by simp))

/-- Off the then arm's path (the guard false), the store after the prelude, with the then-arm
    reach `rT` bound, is off the path of the then arm's walk (`OffInv` at its walk output under
    `name rT`, the prelude names `g` and `rT` excepted), when the guarded store before the
    `ite` binds the current names of the variables in scope read later to values of their final
    types, holds values of their final types and binds no name the rest declares. -/
private theorem LaidCore.offT (hns : SaveNs s6 M sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hdefd : ∀ x ∈ S, x ∈ contFV ([.ite (.det c) tss ess md] :: k) → ∀ n, curName st' x = some n →
      ∃ w, σL n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty)
    (hgt : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hfr : FreshInv Lc Ex st' σL)
    (hB : PreStore F σL σB (g :: rT :: gm?.toList) (HasBool.ffVal F) ns ext)
    (hext : ∀ x ∈ ext, Drawn s7 st' x) (hextT : ∀ x ∈ ext, T[x]? = some HasBool.boolTy)
    (hCB : WellFormedStore σB F) :
    OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 (.name rT) S
      (contFV (tss :: ess :: k)) σB := by
  have hrT := hB.1 rT (by simp)
  obtain ⟨hty, hfr'⟩ := e.preB hs hns (.inr rfl) hfr hB hext hextT hgt
  refine ⟨hCB, hrT, fun y hy => .inr (List.mem_singleton.1 hy ▸ hrT), fun x hx hv n hn =>
    (hdefd x hx (contFV_arms_sub hv) n (hs.cur6 x ▸ hn)).imp fun w ⟨hw, ht⟩ =>
      ⟨(e.preKeep hs hns hfr hB hext (by simp [hw])).trans hw, ht⟩, hty, hfr'⟩

/-- The discarded registrations stay below the counter up to the then arm's walk input. -/
private theorem LaidCore.deadE : DeadBelow s5 := wpList_deadBelow e.runE hs.dead4

/-- The live keys at the then arm's walk input of a laid-out `ite` are fresh names drawn before
    it or avoided if they have the form of a fresh name. -/
private theorem LaidCore.liveK5 : LiveKeys s5 :=
  wpList_liveKeys e.runE hs.wf4 (fun _ hx b j h => hs.avoids.2.1 ▸ e.avoidArm (.inr hx) b j h)
    (fun y hy => .inr (hs.κEv4 y hy).1) hs.liveK4

/-- The simulation property of the then arm's walk (from `s5` to `s6` under `name rT`),
    instantiated at its resolved output `iT`, the scope `S`, the prelude names `g` and `rT`
    excepted, the continuation `ess :: k` and the label map `Lab`. -/
private theorem LaidCore.armTp {iT : List (Item P)}
    (hiT : resolveItems T Y Tr.out.toList = .ok iT) :
    (∀ σ σL t cnd b tr, OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 (.name rT) S
        (contFV (tss :: ess :: k)) σ σL → DReach F tss σ tr → ClaimK b t cnd tr →
        HitPost F s6 Tr iT σL t cnd b) ∧
    (∀ σ σL X evs o, OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 (.name rT) S
        (contFV (tss :: ess :: k)) σ σL → DRun F X tss σ evs o → Trace.AssumptionsHold P evalInterp
            () evs →
        ∃ tr σL', MainRun F iT σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
          RunPost F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) Lab s5 s6 Tr (.name rT) S
            (scopeAfter S tss) (contFV (ess :: k)) X σL' o) ∧
    (∀ σs σL K, OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s6 (.name rT) S
        (contFV (tss :: ess :: k)) σL → ShL F tss σs K →
        OffPost F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 s6 Tr (.name rT) S
          (scopeAfter S tss) (contFV (ess :: k)) iT σL K) := by
  have hnx := hs.nexts
  obtain ⟨h1a, -, h5a, -, -⟩ := hs.avoids
  have H := e.armT (.name rT) nofun s5 Tr s6 hs.wf5 e.runT T Y (hs.fin6 e.fin) iT hiT
    S e.wfS.2.1 Γ (fun _ => e.tyCtx.back fun z _ n h => hs.cur6 z ▸ h) e.typed.ite.2.2.1
    (fun x hx b j h => h5a ▸ e.avoidSArm (.inl rfl) hx b j h)
    (fun y => Ex y ∨ y = g ∨ y = rT) (fun y hy => ?_) (ess :: k) Lab (fun l t h => ?_)
    (fun y hy => ?_) (e.deadE hs) (e.liveK5 hs)
    (wpList_carriesHigh e.runE (fun l t ht => (e.lab l t ((e.labels hs l).1 ▸ ht)).1) hs.high4)
  · exact H.imp_right (.imp (fun h2 σ σL X evs o hon hr hf =>
      (h2 rfl σ σL X evs o hon hr hf).resolve_left (by simp)) (· rfl))
  · rcases hy with hy | hy
    · exact ⟨fun b j h => by have := (e.exc y hy).1 b j h; omega, hs.aft.back ▸ (e.exc y hy).2⟩
    obtain ⟨b, j, h1, -, -, hj⟩ := hs.pre.drawn y (by grind)
    exact ⟨fun b' j' h => by have := freshName_counter_inj (h1.symm.trans h); omega,
      (hs.preBack (by grind)).2.2⟩
  · exact (e.lab l t ((e.labels hs l).2.symm.trans h)).imp_right fun H x hx =>
      (H x hx).imp_left (contFV_tail_sub ·)
  · obtain rfl : y = rT := by simpa [RE.vars] using hy
    obtain ⟨b, j, h1, ha, -, hj⟩ := hs.pre.drawn y (.inr (.inl rfl))
    exact ⟨⟨b, j, h1, by omega⟩, by rwa [h5a, ← h1a], fun x => (hs.preNm (.inr (.inl rfl)) x).2.1,
      (hs.preBack (.inr (.inl rfl))).2.1⟩

omit iLI iWL e hs in
/-- A current name after a walk step was the current name before it or is a fresh name of the
    state before it. -/
private theorem WalkCore.curName_back {D : List P.Ident} {st' : WSt P} (h : WalkCore D st st')
    {z : P.Ident} (hzD : z ∉ D) (hz : curName st' z = some n) :
    curName st z = some n ∨ FreshAt st n := by
  grind [curName, h.nm z n, h.names z, h.taken z]

/-- The variables of the context of a laid-out `ite` are no renamings of its walk states. -/
private theorem LaidCore.rt_kvarNm {y : P.Ident} (hy : y ∈ RE.vars κ) (x : P.Ident) :
    s4.nm[x]? ≠ some y ∧ s5.nm[x]? ≠ some y ∧ s6.nm[x]? ≠ some y ∧ st'.nm[x]? ≠ some y := by
  obtain ⟨⟨b, j, rfl, hj⟩, hav, hnm⟩ := e.ctxv y hy
  have hd : Drawn { st0 with next := 0 } st0 (freshName b j) := ⟨b, j, rfl, hav, Nat.zero_le _, hj⟩
  obtain ⟨n1, n4, n5, -, -, -⟩ := hs.nexts
  have h1 := hs.c1.nm_not_drawn hd hnm
  have h4 : ∀ x : P.Ident, s4.nm[x]? ≠ some (freshName b j) := hs.pre.eq ▸ h1
  have h5 := hs.wE.nm_not_drawn (hd.mono (by omega)) h4
  have h6 := hs.wT.nm_not_drawn (hd.mono (by omega)) h5
  exact ⟨h4 x, h5 x, h6 x, hs.aft.nm ▸ h6 x⟩

/-- No name is declared by both arms of a laid-out `ite`. -/
private theorem LaidCore.dl_declDisj (hT : n ∈ wDecls Tr.out.toList)
    (hE : n ∈ wDecls Er.out.toList) : False := by
  have hnx := hs.nexts
  obtain ⟨-, hav4, hav5, -⟩ := hs.avoids
  have hA : ∀ x, x ∈ stmtsInits tss ∨ x ∈ stmtsInits ess → AvoidedIfFresh st0 x := fun x hx =>
    e.avoidArm (hx.imp (stmtsInits_mem_idents x) (stmtsInits_mem_idents x))
  rcases hs.armT.decl n hT with hd | ⟨hi, ht⟩ | ⟨x, -, hx⟩
  · rcases hs.armE.decl n hE with hd' | ⟨hi, -⟩ | ⟨x, -, hx⟩
    · exact hd'.disj hd (Nat.le_refl _)
    · grind [Drawn, AvoidedIfFresh, hA n (.inr hi)]
    · exact hd.not_below ((dl_nmBelow hs.wf4 hx).imp fun _ => .imp fun _ h => ⟨h.1, by omega⟩)
  · rcases hs.armE.decl n hE with hd' | ⟨hi', -⟩ | ⟨x, -, hx⟩
    · grind [Drawn, AvoidedIfFresh, hA n (.inl hi)]
    · simp [hs.armE.takenIn n hi'] at ht
    · obtain ⟨-, b, j, h1, -, h2⟩ := hs.wf4.nm_fresh x n hx
      simp [hav4 ▸ hA n (.inl hi) b j h1] at h2
  · exact hs.armE.declNotNm n hE x hx

/-- A name the then arm assigns and the else arm reads is the current name of a variable in
    scope that the else arm reads. -/
private theorem LaidCore.mvars {x : P.Ident} (hx : x ∈ interSet Tr.A Er.R) :
    ∃ z ∈ S, z ∈ Block.freeVars ess ∧ curName st' z = some x := by
  obtain ⟨hA, hR⟩ := mem_interSet.1 hx
  rcases hs.armE.read x hR with ⟨z, hz, hzE, hc⟩ | hd
  · exact ⟨z, hz, hzE, hs.cur6 z ▸ hs.wT.names z x (hs.sT z hz) hc⟩
  rcases hs.armT.assigned x hA with ⟨z, hz, -, hc⟩ | hd'
  · rcases hs.wT.toWalkCore.curName_back (hs.sT z hz) hc with hc | hf
    · exact absurd hc (hs.armE.declNotCur x hd z hz)
    · have hnx := hs.wE.next
      obtain ⟨-, -, hav5, -⟩ := hs.avoids
      rcases hs.armE.decl x hd with hd | ⟨hi, -⟩ | ⟨y, -, hy⟩
      · grind [Drawn, FreshAt, freshName_counter_inj]
      · grind [FreshAt, AvoidedIfFresh, e.avoidArm (.inr (stmtsInits_mem_idents x hi))]
      · grind [FreshAt, freshName_counter_inj, dl_nmBelow hs.wf4 hy]
  · exact (e.dl_declDisj hs hd' hd).elim

/-- The simulation property of the else arm's walk (from `s4` to `s5` under `κE`), instantiated
    at its resolved output `iE`, the scope `S`, the prelude names `g`, `rT` and `rE` excepted,
    the continuation `ess :: k` and the label map `Lab`. -/
private theorem LaidCore.armEp (hiE : resolveItems T Y Er.out.toList = .ok iE) :
    (∀ σ σL t cnd b tr, OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σ σL → DReach F ess σ tr → ClaimK b t cnd tr →
        HitPost F s5 Er iE σL t cnd b) ∧
    (∀ σ σL X evs o, OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σ σL → DRun F X ess σ evs o → Trace.AssumptionsHold P evalInterp
            () evs →
        ∃ tr σL', MainRun F iE σL tr σL' ∧ Trace.AssumptionsHold P evalInterp () tr ∧
          RunPost F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) Lab s4 s5 Er κE S
            (scopeAfter S ess) (contFV (ess :: k)) X σL' o) ∧
    (∀ σs σL K, OffInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σL → ShL F ess σs K →
        OffPost F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 s5 Er κE S
          (scopeAfter S ess) (contFV (ess :: k)) iE σL K) := by
  have hf5 : FinalOK Lc s5 T Y := by
    obtain ⟨h1, h2, h3⟩ := hs.fin6 e.fin
    obtain ⟨-, -, hav5, -⟩ := hs.avoids
    have hnx := hs.wT.next
    exact ⟨fun n ty hn => hs.wT.toWalkCore.tys_final hs.wf5 (fun x hx =>
      ⟨(wfl_inits_scope tss e.wfS.2.1 hx).1, fun b j h => hav5 ▸ e.avoidArm
        (.inl (wfl_inits_scope tss e.wfS.2.1 hx).2.1) b j h⟩) h1 hn,
      fun n x hn => h2 n x (hs.wT.toWalkCore.tyOf_keep hs.wf5 hn), fun n hn => (h3 n hn).elim
        (fun h => (Classical.em (s6.tyOf[n]? = s5.tyOf[n]?)).elim (.inl <| · ▸ h) fun he =>
          (hs.wT.tyOf n he).elim fun b ⟨j, h4, h5, h6⟩ => .inr ⟨b, j, h4, h6, h5⟩)
        fun ⟨b, j, h4, h5, h6⟩ => .inr ⟨b, j, h4, by omega, hs.wT.avoid ▸ h6⟩⟩
  have hnx := hs.nexts
  obtain ⟨-, hav4, -⟩ := hs.avoids
  obtain ⟨h1, h2, h3⟩ := e.armE κE (fun h => absurd h hs.ctxE) s4 Er s5 hs.wf4 e.runE T Y
    hf5 iE hiE S e.wfS.2.2 Γ
    (fun _ => e.tyCtx.back fun z hz n h => hs.cur6 z ▸ hs.wT.names z n (hs.sT z hz) h)
    e.typed.ite.2.2.2 (fun x hx b j h => hav4 ▸ e.avoidSArm (.inr rfl) hx b j h)
    (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) (fun y hy => by
      rcases hy with hy | hy
      · obtain ⟨h4, h5⟩ := e.exc y hy
        refine ⟨fun b j h => Nat.lt_of_lt_of_le (h4 b j h) (by omega),
          Classical.byContradiction fun hne => ?_⟩
        obtain ⟨b, j, h6, -, h7⟩ := hs.wT.back y (by rw [← hs.aft.back, h5]; exact Ne.symm hne)
        exact absurd (h4 b j h6) (by omega)
      · exact ⟨by grind [Drawn, freshName_counter_inj, hs.preDrawn hy], (hs.preBack hy).2.1⟩)
    (ess :: k) Lab (fun l t ht => (e.lab l t ((e.labels hs l).1 ▸ ht)).imp id fun h x hx =>
      ⟨contFV_tail_sub (h x hx).1, (h x hx).2⟩) (fun y hy => by
      refine (hs.κEv4 y hy).imp_right (.imp_right fun h6 => ⟨h6, ?_⟩)
      rcases or_assoc.2 (e.of_κEvars' hy) with h | h
      · exact (hs.preBack (h.imp_right .inr)).1
      · rw [hs.pre.eq]
        refine Classical.byContradiction fun hne => ?_
        obtain ⟨⟨b, j, h7, h8⟩, -⟩ := e.ctxv y h
        exact (hs.c1.back y fun h' => hne (h'.trans (e.ctxb y h))).ne ⟨b, j, h7, h8⟩ rfl)
    hs.dead4 hs.liveK4 hs.high4
  exact ⟨h1, fun σ σL X evs o hon hr ha => (h2 rfl σ σL X evs o hon hr ha).resolve_left
    fun h => absurd h.1 hs.ctxE, h3 rfl⟩

omit iLI e in
/-- The current name of a variable in scope after the guard's renaming stays its current name
    through the arms' walks to the walk output of the `ite`. -/
private theorem LaidStates.curS {z : P.Ident} (hz : z ∈ S) (h1 : curName s1 z = some n) :
    curName s4 z = some n ∧ curName s5 z = some n ∧ curName s6 z = some n ∧
      curName st' z = some n := by
  have h4 : curName s4 z = some n := by rw [hs.pre.eq]; exact h1
  have h5 := hs.wE.names z n (hs.sE z hz) h4
  have h6 := hs.wT.names z n (hs.sT z hz) h5
  exact ⟨h4, h5, h6, hs.cur6 z ▸ h6⟩

/-- A live current name at the walk input of a variable in scope, live before the enclosing
    blocks from depth `t` on, stays so before and after each arm's walk. -/
private theorem LaidCore.liveFrom {z : P.Ident} {t : Nat} (hz : z ∈ S)
    (h0 : curName st0 z = some n) (hl : st0.live.contains n = true) (hf : LiveFrom st0 t n) :
    LiveFrom s4 t n ∧ LiveFrom s5 t n ∧ LiveFrom s6 t n := by
  obtain ⟨-, -, h1eq, hkeep⟩ := wRen_run e.run1
  obtain ⟨h4, h5, -, -⟩ := hs.curS hz (hkeep z n h0)
  have hf4 : LiveFrom s4 t n := fun l j hj htj => by
    rw [hs.pre.eq, h1eq]
    exact hf l j (by rw [← (e.labels hs l).1]; exact hj) htj
  have hc4 : s4.live.contains n = true := by rw [hs.pre.eq, h1eq]; exact hl
  have hk5 := hs.armE.liveKeep z hz n h4
  have hc5 : s5.live.contains n = true := by
    grind [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
  have hf5 := LiveFrom.walk hs.wE.toWalkCore hs.wE.labelDepth hs.wf4 hk5 hc4 hf4
  exact ⟨hf4, hf5, LiveFrom.walk hs.wT.toWalkCore hs.wT.labelDepth hs.wf5
    (hs.armT.liveKeep z hz n h5) hc5 hf5⟩

/-- A current name of a variable in scope has no type reference in the final maps. -/
private theorem LaidCore.curY {z : P.Ident} (hz : z ∈ S) (hzn : curName st' z = some n) :
    Y[n]? = none := by
  have hw := e.whole.wf e.wf0 fun x hx =>
    e.avoidArm ((List.mem_append.1 hx).imp (stmtsInits_mem_idents x) (stmtsInits_mem_idents x))
  have hzS : AvoidedIfFresh st' z := fun b j hb =>
    hs.avoids.2.2.2.2 ▸ e.avoidS z (List.mem_append_left _ hz) b j hb
  refine Option.eq_none_iff_forall_ne_some.2 fun y hY => ?_
  rcases e.fin.2.2 n (by simp [hY]) with h | ⟨b, j, hj, hle, hna⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hna, hnm⟩ := hw.tyOf_keys n x hx
    rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
    · exact hnm z hm
    · exact (hw.tyOf_fresh _ x hx).elim fun b ⟨j, hj, _⟩ => by simp [hzS b j hj] at hna
  · rcases curName_cases hzn with hm | ⟨-, -, rfl⟩
    · obtain ⟨-, b', j', hj', hlt, -⟩ := hw.nm_fresh z n hm
      exact absurd (freshName_counter_inj (hj.symm.trans hj')) (by omega)
    · simp [hzS b j hj] at hna

include iOp iLF iIL in
/-- On the loop-free path, the resolved guard `κ ∧ c` of a laid-out `ite` with a nonempty body
    evaluates in the guarded store like the condition in the loop-free store, when the latter is
    a Boolean. -/
private theorem LaidCore.guardOn
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hnn : nonnil) (hnn' : nonnil → ∀ n ∈ rdc ++ RE.vars κ, st'.live.contains n = true)
    {cv : P.Val} (hc : P.eval F σ c = some cv) (hcb : cv = HasBool.ttVal F ∨ cv = HasBool.ffVal F)
    {ce : P.Expr}
    (hce : resolveE T Y (kAnd κ wc) = .ok ce) : P.eval F σL ce = some cv := by
  obtain ⟨⟨ren, rfl, hren, hfv, -⟩, -⟩ := wRen_run e.run1
  have hag : ∀ y ∈ exprFV c, ∀ n, curName s1 y = some n → n ∈ rdc → σL n = σ y ∧ (σ y).isSome :=
    fun y hy n hn hr => by
      have hS := e.wfS.1 y hy
      have hV : y ∈ contFV ([.ite (.det c) tss ess md] :: k) :=
        mem_contFV_cons.2 (.inl (by simp [Block.freeVars, Stmt.freeVars, hy]))
      exact ⟨hon.agree y hS hV n (hs.curS hS hn).2.2.2 (hnn' hnn n (List.mem_append_left _ hr)),
        (hon.defd y hS hV).1⟩
  refine ev_kAnd_holds e.hF hon.canonL hon.reach hce (fun a h => ?_) hcb
  rw [ev_resolveE_user e.hF hon.canon hon.canonL h (fun p hp => ?_) (fun y hy hn => ?_), hc]
  · obtain ⟨h1, h2, -⟩ := hren p hp
    obtain ⟨n, h3, h4, -⟩ := hfv p.1 h1
    cases h2.symm.trans h3
    exact hag p.1 h1 _ h3 h4
  · obtain ⟨n, h3, h4, h5 | h5⟩ := hfv y hy
    · exact (hag y hy _ (h5 ▸ h3) (h5 ▸ h4)).1
    · exact absurd rfl (hn _ h5)

include iOp iLF iLFs in
/-- Off the loop-free path, the guard's renamed condition of a laid-out `ite` resolves to Boolean
    values. -/
private theorem LaidCore.guardOff
    (hoff : OffInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σL) :
    ResBool F σL T Y wc := by
  obtain ⟨⟨ren, rfl, hren, hfv, -⟩, -⟩ := wRen_run e.run1
  obtain ⟨hcT, hcA, -⟩ := e.typed.ite
  have hV : ∀ y ∈ exprFV c, y ∈ contFV ([.ite (.det c) tss ess md] :: k) := fun y hy =>
    mem_contFV_cons.2 (.inl (by simp [Block.freeVars, Stmt.freeVars, hy]))
  exact ResTy.bool tE (hoff.resTy e.hF hoff.canonL (fun _ _ => id) e.tyCtx hcT hcA
    (fun p hp => ⟨(hren p hp).1, (hs.curS (e.wfS.1 _ (hren p hp).1) (hren p hp).2.1).2.2.2⟩)
    (fun y hy => (hfv y hy).imp fun n h =>
      ⟨(hs.curS (e.wfS.1 y hy) h.1).2.2.2, h.2.2⟩) e.wfS.1 hV)

/-- On the loop-free path, the current name of a variable in scope that an arm mentions is bound
    to a value of its final type. -/
private theorem LaidCore.boundOn
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    {x : P.Ident}
    (hx : ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧ curName st' z = some x) :
    ∃ w, σL x = some w ∧ ∀ ty, tyOfName T Y x = .ok ty → HasVal.valueOfTy F w ty := by
  obtain ⟨z, hz, hzf, hzx⟩ := hx
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((hon.defd z hz (contFV_arms_sub (hzf.elim
    (mem_contFV_cons.2 ∘ .inl) fun h => mem_contFV_cons.2 (.inr (mem_contFV_cons.2 (.inl h)))))).2
      x hzx)
  exact ⟨w, hw, hon.gtyped x w hw (e.curY hs hz hzx)⟩

/-- On the loop-free path, the variables a laid-out `ite` saves are bound to values of their
    final types. -/
private theorem LaidCore.savedOn
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hns : SaveNs s6 (interSet Tr.A Er.R) sv cp rs cps s7 ns) :
    ∀ q ∈ ns, ∃ w, σL q.1 = some w ∧ ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty :=
  fun _ hq => (e.mvars hs (hns.vars ▸ List.mem_map_of_mem hq)).elim fun z ⟨hz, hzE, hzx⟩ =>
    e.boundOn hs hon ⟨z, hz, .inr hzE, hzx⟩

omit iBE iLB iHF iSF iHI iLI iHa iHFs iWL e hs in
/-- Binding a further prelude name `x` to the guard's value extends a prelude store. -/
private theorem PreStore.add {σB : SemanticStore P} {L : List P.Ident} {g x : P.Ident}
    (h : PreStore F σL σB (g :: L) gv ns ext) (hx : ∀ q ∈ ns, x ≠ q.2.1) (hxe : x ∉ ext) :
    PreStore F σL (SemanticStore.update σB x gv) (g :: x :: L) gv ns ext := by
  grind [PreStore, SemanticStore.update]

omit iBE iLB iHF iSF iHI iLI iHa iHFs iWL e hs in
/-- The guard and the then-arm reach bound to a Boolean `gv` over a store make a prelude store
    without merge guard and saves. -/
private theorem preStore_two {g rT : P.Ident} (hgr : g ≠ rT) :
    PreStore F σL (SemanticStore.update (SemanticStore.update σL g gv) rT gv) [g, rT] gv [] [] := by
  grind [PreStore, SemanticStore.update]

omit iLI e in
/-- When every part of the body of a laid-out `ite` is empty, the arms' outputs, the saves and
    the merge guard are empty. -/
private theorem LaidStates.nilParts (hns : SaveNs s6 M sv cp rs cps s7 ns)
    (hnil : (laidParts κ g rT rE? gm? sv cp rs (cps.filter fun p => liveBefore s6 p.1 s4.clock) Tr
      Er (laidU κ κE rT Tr Er d)).all Rope.isNil = true) :
    Tr.out.isNil = true ∧ Er.out.isNil = true ∧ ns = [] ∧ gm? = none ∧
      (laidU κ κE rT Tr Er d).isNil = true := by
  simp only [laidParts, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hnil
  obtain ⟨-, hgm, hsv, hT, -, -, -, hE, -, hU⟩ := hnil
  exact ⟨hT, hE, List.map_eq_nil_iff.1 (hns.saves.symm.trans (Rope.isNil_toList hsv)),
    by cases gm? <;> simp [Rope.isNil] at hgm ⊢, hU⟩

omit e in
/-- The then-arm reach `rT` differs from the merge guard and the save names of a laid-out
    `ite`, and is unbound in a store with `FreshInv` at the walk output. -/
private theorem LaidStates.rTFacts (hns : SaveNs s6 M sv cp rs cps s7 ns) :
    (∀ x, gm? = some x → rT ≠ x) ∧ (∀ q ∈ ns, rT ≠ q.2.1) ∧ rT ≠ g := by
  have hnx := hs.nexts
  have hrT := hs.preDrawn (.inr (.inl rfl))
  exact ⟨fun x hx h => hrT.disj (h ▸ hs.aft.gmDrawn x hx) (by omega),
    fun q hq h => hrT.disj (h ▸ (hns.drawn q hq).1) (by omega), hs.pre.g_rT.symm⟩

omit iLI e in
/-- A prelude name or a name drawn after the arms of a laid-out `ite` is a fresh-form name not
    avoided at `st0`, drawn by the prelude or after the arms. -/
private theorem LaidStates.preOrLate (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) :
    ∃ b j, n = freshName b j ∧ st0.avoid.contains n = false ∧ (Drawn s1 s4 n ∨ Drawn s6 st' n) := by
  have hd := hs.pre.drawn n
  obtain ⟨a1, -, -, a6, -⟩ := hs.avoids
  grind [Drawn]

/-- A prelude name or a name drawn after the arms of a laid-out `ite` is none of the names a
    main-path run of the then arm's output may change apart from its reach (`Wr0`). -/
private theorem LaidCore.notWT (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) :
    ¬ Wr0 (Block.idents tss) s5 s6 n := by
  obtain ⟨b, j, h1, h2, hd⟩ := hs.preOrLate hn
  have hnx := hs.nexts
  rintro (⟨b', j', h3, -, h4, h5⟩ | ⟨z, hz⟩ | hi)
  · rcases hd with ⟨b'', j'', h6, -, -, h7⟩ | ⟨b'', j'', h6, -, h7, -⟩ <;>
      grind [freshName_counter_inj]
  · exact hn.elim (fun hn => (hs.preNm hn z).2.1 hz)
      fun hn => hn.not_below ((dl_nmBelow hs.wf5 hz).imp fun _ => .imp fun _ h => ⟨h.1, by omega⟩)
  · simp [e.avoidArm (.inl hi) b j h1] at h2

include iHFs iLV in
/-- Off the then arm's path, the then arm's output runs from the store after the prelude of a
    laid-out `ite`: the store after it agrees with the store before the `ite` where that is
    bound, keeps the guard, the merge guard and the saves, binds no new name the arm neither
    assigns nor declares, holds values of their final types and binds no name the rest of the
    arm's walk declares (the prelude names `g` and `rT` excepted); it also satisfies the then
    arm's snapshot, carried-merge and shadow-end facts for any shadow continuation `K`, and the
    reach `rT` is false when its `init` is emitted. -/
private theorem LaidCore.of_T (hns : SaveNs s6 M sv cp rs cps s7 ns) {σB : SemanticStore P}
    (hdefd : ∀ x ∈ S, x ∈ contFV ([.ite (.det c) tss ess md] :: k) → ∀ n, curName st' x = some n →
      ∃ w, σL n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F w ty)
    (hgt : ∀ n w, σL n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty) (hfr : FreshInv Lc Ex st' σL) (hsrc : ∀ q ∈ ns, (σL q.1).isSome)
    (hB : PreStore F σL σB (g :: ((if (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = true then []
      else [rT]) ++ gm?.toList)) (HasBool.ffVal F) ns ext) (hext : ∀ x ∈ ext, Drawn s7 st' x)
    (hextT : ∀ x ∈ ext, T[x]? = some HasBool.boolTy) (hCB : WellFormedStore σB F)
    {iT : List (Item P)} (hT : resolveItems T Y Tr.out.toList = .ok iT) (hsh : ShL F tss σs K) :
    ∃ trT σ1, MainRun F iT σB trT σ1 ∧ Trace.AssumptionsHold P evalInterp
        () trT ∧ WellFormedStore σ1 F ∧
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT) s5 σ1 ∧
      (∀ n w, σ1 n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty) ∧
      (∀ n, (σL n).isSome → σ1 n = σL n) ∧ (∀ n ∈ g :: gm?.toList, σ1 n = some (HasBool.ffVal F)) ∧
      (∀ q ∈ ns, σ1 q.2.1 = σL q.1) ∧
      (∀ n, σB n = none → n ≠ rT → ¬ Wr0 (Block.idents tss) s5 s6 n → σ1 n = none) ∧
      SnapFF F Tr s6 none σ1 ∧ CarryFF F T Y Tr s6 σ1 ∧ CarryOK F T Y Tr s6 σ1 ∧
      ShEnds Tr s6 none K ∧
      ((Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil) = false → σ1 rT = some (HasBool.ffVal F)) ∧
      ∀ n ∈ ext, σ1 n = σB n := by
  have hnx := hs.nexts
  obtain ⟨hrg, hrs, -⟩ := hs.rTFacts hns
  have hrL : σL rT = none := e.unbound hs hfr (.inl (.inr (.inl rfl)))
  have hrx : ∀ x ∈ ext, rT ≠ x := fun x hx h =>
    (hs.preDrawn (.inr (.inl rfl))).disj (h ▸ hext x hx) (by omega)
  cases hb : (Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil)
  · have hB' : PreStore F σL σB (g :: rT :: gm?.toList) (HasBool.ffVal F) ns ext := by
      simpa [hb] using hB
    obtain ⟨tr, σ1, hrun, hah, hoff, hfrm, hsn, hcf, hco, hse⟩ :=
      (e.armTp hs hT).2.2 σs σB K (e.offT hs hns hdefd hgt hfr hB' hext hextT hCB) hsh
    have hfr1 : ∀ n, (σB n).isSome → n ≠ rT → σ1 n = σB n := fun n h1 h2 =>
      hfrm n h1 (by simpa [RE.vars] using h2)
    have hkeep : ∀ n, (σL n).isSome → σB n = σL n := fun n hn => e.preKeep hs hns hfr hB' hext hn
    refine ⟨tr, σ1, hrun, hah, hoff.canonL, hoff.fresh, hoff.gtyped, fun n hn => ?_, fun n hn => ?_,
      fun q hq => ?_, fun n h1 h2 h3 => ?_, hsn, hcf, hco, hse, fun _ => hoff.reach,
      fun n hn => hfr1 n (Option.isSome_iff_exists.2 ((hB'.2.2.2 n hn).elim (⟨_, ·⟩) (⟨_, ·⟩)))
        (hrx n hn).symm⟩
    · rw [hfr1 n (by rw [hkeep n hn]; exact hn) fun h => by simp [h, hrL] at hn, hkeep n hn]
    · obtain ⟨hn', hne⟩ : n ∈ g :: rT :: gm?.toList ∧ n ≠ rT := by grind [hs.pre.g_rT]
      rw [hfr1 n (by simp [hB'.1 n hn']) hne, hB'.1 n hn']
    · rw [hfr1 _ (by rw [hB'.2.1 q hq]; exact hsrc q hq) (hrs q hq).symm, hB'.2.1 q hq]
    · exact Classical.byContradiction fun hne => (hs.armT.writesW T Y iT hT σB tr σ1 hrun n
        (h1 ▸ hne)).elim h3 fun h => h2 (Option.some.inj h).symm
  · obtain ⟨hTn, -⟩ := Bool.and_eq_true_iff.1 hb
    obtain rfl := resolve_isNil hTn hT
    have hB0 : PreStore F σL σB (g :: gm?.toList) (HasBool.ffVal F) ns ext := by simpa [hb] using hB
    have hB'' := PreStore.add hB0 (x := rT) hrs fun h => hrx rT h rfl
    have hrB : σB rT = none := (hB0.2.2.1 rT (fun h => hrx rT h rfl) (by grind [hs.pre.g_rT])
      fun q hq h => hrs q hq h).trans hrL
    have hu : ∀ n, n ≠ rT → SemanticStore.update σB rT (HasBool.ffVal F) n = σB n := fun n h =>
      (update_facts σB rT (HasBool.ffVal F)).2 n (Ne.symm h)
    obtain ⟨tr, σ1, hrun, hah, hoff, -, -, -, -, hse⟩ := (e.armTp hs hT).2.2 σs _ K
      (e.offT hs hns hdefd hgt hfr hB'' hext hextT (wfStore_update_bool hCB rT (.inr rfl))) hsh
    cases hrun
    have hreg : ∀ e, e ∉ Tr.regs.toList := fun e he => by
      simpa [Rope.isNil_toList hTn, wDecls] using hs.armT.regs e he
    refine ⟨[], σB, .nil, hah, hCB, fun y hy => hoff.fresh y (hu y (by grind) ▸ hy),
      fun n w hn => hoff.gtyped n w ((hu n (by grind)).trans hn), fun n hn => ?_, hB0.1, hB0.2.1,
      fun n h _ _ => h, fun _ e he => absurd he (hreg e), fun _ _ _ _ _ h => absurd h.2 (hreg _),
      fun _ _ _ _ _ h => absurd h.2 (hreg _), hse, nofun, fun _ _ => rfl⟩
    exact (hu n (by grind)).symm.trans (e.preKeep hs hns hfr hB'' hext hn)

section
omit iLI e hs

/-- In save triples whose names are all distinct, no save name is a copy name. -/
private theorem flat_ne {α : Type} : ∀ (ns : List (α × α × α)),
    (ns.flatMap fun q => [q.2.1, q.2.2]).Nodup → ∀ q ∈ ns, ∀ p ∈ ns, q.2.1 ≠ p.2.2
  | [], _, q, hq, _, _ => nomatch hq
  | a :: ns, hnd, q, hq, p, hp => by
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap] at hnd
    have ih := flat_ne ns hnd.2.2
    grind

include iOp iLF in
/-- The copies of a laid-out `ite` run from a store binding none of the copy names and binding
    the saved variables to values of their final types: each copy takes its variable's value. -/
private theorem copyRun (hF : WellFormedSemanticEvalBase F) (hns : SaveNs s6 M sv cp rs cps s7 ns)
    (hC : WellFormedStore σ1 F) {iCP : List (Item P)} (hCP : resolveItems T Y cp.toList = .ok iCP)
    (h0 : ∀ q ∈ ns, σ1 q.2.2 = none) (hsrc : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty) :
    ∃ σC, MainRun F iCP σ1 [] σC ∧ WellFormedStore σC F ∧ (∀ q ∈ ns, σC q.2.2 = σ1 q.1) ∧
      (∀ n, (∀ q ∈ ns, n ≠ q.2.2) → σC n = σ1 n) ∧
      ∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty :=
  nsInitsRun hF (·.2.2) hC (hns.copies ▸ hCP) ((sub_flat ns).nodup hns.nodup) h0 hsrc

include iOp iLF in
/-- The restores of a laid-out `ite` run from a store binding the save names and the saved
    variables, each saved value of a type of the stored one: each variable takes its save's
    value. -/
private theorem restoreRun (hF : WellFormedSemanticEvalBase F)
    (hns : SaveNs s6 M sv cp rs cps s7 ns) {σC : SemanticStore P}
    (hC : WellFormedStore σC F) {iRS : List (Item P)} (hRS : resolveItems T Y rs.toList = .ok iRS)
    (hMnd : M.Nodup) (hdis : ∀ q ∈ ns, ∀ p ∈ ns, q.1 ≠ p.2.1)
    (hsrc : ∀ q ∈ ns, ∃ w, σC q.2.1 = some w ∧ HasVal.valueOfStoredTy (P := P) F σC q.1 w) :
    ∃ σR, MainRun F iRS σC [] σR ∧ WellFormedStore σR F ∧ (∀ q ∈ ns, σR q.1 = σC q.2.1) ∧
      ∀ n, (∀ q ∈ ns, n ≠ q.1) → σR n = σC n := by
  obtain ⟨l, h1, rfl⟩ := resolve_var_sets (ns.map fun q => (q.1, q.2.1)) iRS
    (by rw [List.map_map]; exact hns.restores ▸ hRS)
  have hl : ∀ p ∈ l, ∃ q ∈ ns, q.1 = p.1 ∧ q.2.1 = p.2.1 := fun p hp =>
    (List.mem_map.1 (h1 ▸ List.mem_map_of_mem hp)).imp fun q ⟨hq, he⟩ => ⟨hq, Prod.mk.inj he⟩
  have hr : ∀ q ∈ ns, ∃ p ∈ l, p.1 = q.1 ∧ p.2.1 = q.2.1 := fun q hq =>
    (List.mem_map.1 (h1.symm ▸ List.mem_map_of_mem hq)).imp fun p ⟨hp, he⟩ => ⟨hp, Prod.mk.inj he⟩
  have hfst : l.map (·.1) = M := by
    rw [← hns.vars]
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) h1
  obtain ⟨σR, hrun, hC', hv, ho⟩ := run_var_sets hF l σC hC (hfst ▸ hMnd) (fun q hq p hp =>
      (hl q hq).elim fun q' ⟨hq', h2, _⟩ => (hl p hp).elim fun p' ⟨hp', _, h3⟩ =>
        h2 ▸ h3 ▸ hdis q' hq' p' hp') fun p hp =>
    (hl p hp).elim fun q ⟨hq, h2, h3⟩ => h2 ▸ h3 ▸ hsrc q hq
  refine ⟨σR, hrun, hC', fun q hq => ?_, fun n hn => ho n fun p hp => ?_⟩
  · exact (hr q hq).elim fun p ⟨hp, h2, h3⟩ => by rw [← h2, hv p hp, h3]
  · exact (hl p hp).elim fun q ⟨hq, h2, _⟩ => h2 ▸ hn q hq

include iOp iLF in
/-- The copies and then the restores of a laid-out `ite` run from a store binding none of the
    copy names, binding the saved variables and the save names to values of the variables' final
    types, where no saved variable is a save or copy name: each copy takes its variable's value,
    each variable its save's value, and every other name keeps its value. -/
private theorem copyRestore (hF : WellFormedSemanticEvalBase F)
    (hns : SaveNs s6 M sv cp rs cps s7 ns) (hMnd : M.Nodup)
    (hC : WellFormedStore σ1 F) {iCP iRS : List (Item P)}
    (hCP : resolveItems T Y cp.toList = .ok iCP) (hRS : resolveItems T Y rs.toList = .ok iRS)
    (h0 : ∀ q ∈ ns, σ1 q.2.2 = none) (hsrc : ∀ q ∈ ns, ∃ w, σ1 q.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hsv : ∀ q ∈ ns, ∃ w, σ1 q.2.1 = some w ∧
      ∀ ty, tyOfName T Y q.1 = .ok ty → HasVal.valueOfTy F w ty)
    (hdis : ∀ q ∈ ns, ∀ p ∈ ns, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2) :
    ∃ σC σR, MainRun F iCP σ1 [] σC ∧ MainRun F iRS σC [] σR ∧ WellFormedStore σR F ∧
      (∀ q ∈ ns, σR q.2.2 = σ1 q.1) ∧ (∀ q ∈ ns, σR q.1 = σ1 q.2.1) ∧
      (∀ n, (∀ q ∈ ns, n ≠ q.1 ∧ n ≠ q.2.2) → σR n = σ1 n) ∧
      ∀ q ∈ ns, ∃ ty, tyOfName T Y q.1 = .ok ty := by
  obtain ⟨σC, hrC, hCC, hvC, hoC, htyC⟩ := copyRun hF hns hC hCP h0 hsrc
  have hsvC : ∀ q ∈ ns, σC q.2.1 = σ1 q.2.1 := fun q hq =>
    hoC _ fun p hp => flat_ne ns hns.nodup q hq p hp
  have h1C : ∀ q ∈ ns, σC q.1 = σ1 q.1 := fun q hq => hoC _ fun p hp => (hdis q hq p hp).2
  obtain ⟨σR, hrR, hCR, hvR, hoR⟩ := restoreRun hF hns hCC hRS hMnd
    (fun q hq p hp => (hdis q hq p hp).1) fun q hq => by
      obtain ⟨w, hw, hty⟩ := hsv q hq
      obtain ⟨w1, hw1, hty1⟩ := hsrc q hq
      obtain ⟨ty, hty0⟩ := htyC q hq
      exact ⟨w, (hsvC q hq).trans hw, w1, ty, (h1C q hq).trans hw1, hty1 ty hty0, hty ty hty0⟩
  refine ⟨σC, σR, hrC, hrR, hCR, fun q hq => ?_, fun q hq => (hvR q hq).trans (hsvC q hq),
    fun n hn => (hoR n fun q hq => (hn q hq).1).trans (hoC n fun q hq => (hn q hq).2), htyC⟩
  rw [hoR _ fun p hp he => (hdis p hp q hq).2 he.symm, hvC q hq]

include iOp iLF iHFs iLV in
omit iLB iHI in
include iIL in
/-- The else-arm reach `init rE := κ ∧ ¬g` of a laid-out `ite` (when emitted) runs from a store
    where `rE` is unbound and either `κ` holds and `g` is false (binding `rE` to `w = tt`), or `κ`
    fails with `g` and the variables of `κ` Boolean, or `κ` holds and `g` is true (binding `rE`
    to `w = ff`). -/
private theorem rEiRun (hF : WellFormedSemanticEvalBase F) {rE? : Option P.Ident} {b : Bool}
    {σR : SemanticStore P}
    {w : P.Val} (hC : WellFormedStore σR F) (h0 : ∀ x, rE? = some x → σR x = none)
    (hw : (κ.Holds F σR ∧ σR g = some (HasBool.ffVal F) ∧ w = (HasBool.ttVal F)) ∨
      (κ.Fails F σR ∧ (σR g = some (HasBool.ttVal F) ∨ σR g = some (HasBool.ffVal F)) ∧
        (∀ y ∈ RE.vars κ, σR y = some (HasBool.ttVal F) ∨ σR y = some (HasBool.ffVal F)) ∧
        w = (HasBool.ffVal F)) ∨
      (κ.Holds F σR ∧ σR g = some (HasBool.ttVal F) ∧ w = HasBool.ffVal F)) {iRE : List (Item P)}
    (hRE : resolveItems T Y (match rE? with
      | some r => if b = true then Rope.nil
        else Rope.one (WItem.init r (.known HasBool.boolTy) (some (kAnd κ (WExpr.var g).not)))
      | none => Rope.nil).toList = .ok iRE) :
    ∃ σD, MainRun F iRE σR [] σD ∧ WellFormedStore σD F ∧
      ((iRE = [] ∧ σD = σR ∧ (rE? = none ∨ b = true)) ∨
        ∃ x, rE? = some x ∧ b = false ∧ σD = SemanticStore.update σR x w) := by
  cases rE? with
  | none =>
    obtain rfl := resolve_isNil (s := .nil) rfl hRE
    exact ⟨σR, .nil, hC, .inl ⟨rfl, rfl, .inl rfl⟩⟩
  | some x =>
    rcases resolve_opt_init hRE with ⟨hb, rfl⟩ | ⟨hb, ty, e', rfl, he, rfl⟩
    · exact ⟨σR, .nil, hC, .inl ⟨rfl, rfl, .inr hb⟩⟩
    have hg : ∀ {v}, σR g = some v →
        ∀ a, resolveE T Y (WExpr.var g) = .ok a → P.eval F σR a = some v :=
      fun hg _ h => (resolveE_var h).elim fun _ ht => ht ▸ ev_var hF.var hC hg
    obtain ⟨hev, hb'⟩ : P.eval F σR e' = some w ∧ (w = HasBool.ttVal F ∨ w = HasBool.ffVal F) := by
      rcases hw with ⟨hκ, hv, rfl⟩ | ⟨hκ, hgb, hκb, rfl⟩ | ⟨hκ, hv, rfl⟩
      · exact ⟨ev_kAnd_holds hF hC hκ he (fun _ h => ev_not_ff hF h (hg hv)) (.inl rfl), .inl rfl⟩
      · exact ⟨ev_kAnd_fails hF hC hκ he (fun _ h => hgb.elim
          (fun hv => .inr (ev_not_tt hF h (hg hv))) fun hv => .inl (ev_not_ff hF h (hg hv))) hκb,
          .inr rfl⟩
      · exact ⟨ev_kAnd_holds hF hC hκ he (fun _ h => ev_not_tt hF h (hg hv)) (.inr rfl), .inr rfl⟩
    exact ⟨_, run_init1 hF (h0 x rfl) hev (bool_valueOfTy hb'), wfStore_update_bool hC x hb',
      .inr ⟨x, rfl, hb, rfl⟩⟩

omit iDE iHB iHF iSF iHI iWL in
/-- The continuation of the else arm (followed by itself) reads what the `ite`'s does. -/
private theorem contFV_else_sub {x : P.Ident}
    (h : x ∈ contFV (ess :: ess :: k)) : x ∈ contFV ([.ite (.det c) tss ess md] :: k) := by
  grind [mem_contFV_cons, Block.freeVars, Stmt.freeVars]

include hs in
/-- A current name of a variable in scope at the else arm's walk output is its current name at
    the walk output of the `ite`, and live there when live after the else arm. -/
private theorem LaidStates.cur5 {z : P.Ident} (hz : z ∈ S) (hn : curName s5 z = some n) :
    curName st' z = some n ∧ (s5.live.contains n = true → st'.live.contains n = true) := by
  refine ⟨hs.cur6 z ▸ hs.wT.names z n (hs.sT z hz) hn, fun hl => ?_⟩
  grind [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists,
    hs.armT.liveKeep z hz n hn, hs.aft.live n]

include hs in
/-- On the else path of a laid-out `ite` (the context holding, the condition false), a store
    before the else arm that agrees with the guarded store before the `ite` where that is bound,
    holds values of their final types, binds no name the rest of the else arm's walk declares and
    makes the else-arm context hold relates to the loop-free store as the else arm's walk
    requires. -/
private theorem LaidStates.elseE
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hCE : WellFormedStore σE F) (hkeep : ∀ n, (σL n).isSome → σE n = σL n)
    (hgtE : ∀ n w, σE n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hfrE : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE)
    (hreach : κE.Holds F σE) :
    OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
      (contFV (ess :: ess :: k)) σ σE :=
  hon.toArm (fun _ hx => contFV_else_sub hx) (fun _ hz _ hn => hs.cur5 hz hn) hkeep hCE hgtE hfrE
    hreach

omit iDE iBE iLB iHF iSF iHI iHa iHFs iWL in
/-- A reach context holds in a store agreeing on its variables with one where it holds. -/
private theorem RE.Holds.congr {κ : RE P} (h : κ.Holds F σ)
    (hv : ∀ y ∈ RE.vars κ, σ' y = σ y) : κ.Holds F σ' := by
  cases κ <;> grind [RE.Holds, RE.vars]

/-- A name the output of an arm declares is one a main-path run of it may change (`Wr0`). -/
private theorem ArmFacts.declW {κ' : RE P} {d' : Nat} {sa sb : WSt P}
    {r' : WRes P} (ha : ArmFacts F Lc S κ' d' ss sa r' sb)
    (hn : n ∈ wDecls r'.out.toList) : Wr0 (Block.idents ss) sa sb n :=
  (ha.decl n hn).elim .inl fun h => h.elim (fun h => .inr (.inr (stmtsInits_mem_idents n h.1)))
    fun ⟨y, _, hy⟩ => .inr (.inl ⟨y, hy⟩)

/-- An arm assigns no name its output does not declare that is no current name, at the end of
    its walk, of a variable in scope. -/
private theorem ArmFacts.notA {κ' : RE P} {d' : Nat} {sa sb : WSt P}
    {r' : WRes P} (ha : ArmFacts F Lc S κ' d' ss sa r' sb)
    (hcur : ∀ z ∈ S, curName sb z ≠ some n) (hD : n ∉ wDecls r'.out.toList) :
    r'.A.contains n = false :=
  Bool.eq_false_iff.2 fun hA => (ha.assigned n hA).elim (fun ⟨z, hz, _, h⟩ => hcur z hz h) hD

end

/-- A prelude name or a name drawn after the arms of a laid-out `ite` is neither assigned nor
    declared by the then arm. -/
private theorem LaidCore.notT (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) :
    Tr.A.contains n = false ∧ n ∉ wDecls Tr.out.toList := by
  obtain ⟨b, j, hnb, hnav, -⟩ := hs.preOrLate hn
  have hW := e.notWT hs hn
  have hcur : ∀ z ∈ S, curName s6 z ≠ some n := fun z hz hc => by
    rcases curName_cases hc with hm | ⟨-, -, rfl⟩
    · exact hn.elim (fun hn => (hs.preNm hn z).2.2.1 hm) (·.not_below (dl_nmBelow hs.wf6 hm))
    · simp [e.avoidS _ (List.mem_append_left _ hz) b j hnb] at hnav
  have hD : n ∉ wDecls Tr.out.toList := fun hD => hW (hs.armT.declW hD)
  exact ⟨hs.armT.notA hcur hD, hD⟩

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL e hs in
/-- The variables of a reach context that holds are bound. -/
private theorem RE.Holds.bound {κ : RE P} (h : κ.Holds F σ) :
    ∀ y ∈ RE.vars κ, (σ y).isSome := by
  cases κ <;> grind [RE.Holds, RE.vars]

omit e in
/-- A name drawn by the saves of a laid-out `ite` differs from its prelude names and its merge
    guard. -/
private theorem LaidStates.saveNe (hn : Drawn s6 s7 n) :
    n ≠ g ∧ n ≠ rT ∧ (∀ x, gm? = some x → n ≠ x) ∧ (∀ x, rE? = some x → n ≠ x) := by
  have hnx := hs.nexts
  have hp : ∀ x, (x = g ∨ x = rT ∨ rE? = some x) → n ≠ x := fun x hx he =>
    (hs.pre.drawn x hx).disj (he ▸ hn) (by omega)
  exact ⟨hp g (.inl rfl), hp rT (.inr (.inl rfl)), fun x hx he => hn.disj (he ▸ hs.aft.gmDrawn x hx)
    (Nat.le_refl _), fun x hx => hp x (.inr (.inr hx))⟩

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL e hs in
/-- A name other than the guard, the then-arm reach and the merge guard is not a prelude name. -/
private theorem notin_pre {g rT : P.Ident} {gm? : Option P.Ident} {b : Bool} (hg : n ≠ g)
    (hr : n ≠ rT) (hgm : ∀ x, gm? = some x → n ≠ x) :
    n ∉ g :: ((if b = true then [] else [rT]) ++ gm?.toList) := by
  grind

include iHFs iLV in
/-- With empty arm outputs, off the then arm's path (the guard false), the store with the
    prelude names `g` and `rT` bound to `ff`, and `rE` to `tt` when it is the else-arm context,
    agrees with the guarded store before the `ite` where that is bound, makes the else-arm
    context hold and relates to the loop-free store as the else arm's walk requires. -/
private theorem LaidCore.rn_elseStore (hns : SaveNs s6 M sv cp rs cps s7 [])
    (hgm : gm? = none) (hT : resolveItems T Y Tr.out.toList = .ok [])
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hsh : ShL F tss σs K) :
    ∃ σE, (∀ n, (σL n).isSome → σE n = σL n) ∧ κE.Holds F σE ∧
      OnInv F T Y Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 κE S
        (contFV (ess :: ess :: k)) σ σE := by
  have hdefd : ∀ x ∈ S, x ∈ contFV ([.ite (.det c) tss ess md] :: k) → ∀ n,
      curName st' x = some n → ∃ w, σL n = some w ∧ ∀ ty, tyOfName T Y n = .ok ty →
        HasVal.valueOfTy F w ty := fun x hx hv n hn =>
    (Option.isSome_iff_exists.1 ((hon.defd x hx hv).2 n hn)).elim fun w hw =>
      ⟨w, hw, hon.gtyped n w hw (e.curY hs hx hn)⟩
  have hC1 := wfStore_update_bool hon.canonL g (.inr rfl)
  obtain ⟨σB, hB, hCB⟩ : ∃ σB, PreStore F σL σB (g :: ((if (Tr.out.isNil &&
      (laidU κ κE rT Tr Er d).isNil) = true then [] else [rT]) ++ gm?.toList))
        (HasBool.ffVal F) [] [] ∧
      WellFormedStore σB F := by
    cases Tr.out.isNil && (laidU κ κE rT Tr Er d).isNil
    · exact ⟨_, by simpa [hgm] using preStore_two hs.pre.g_rT,
        wfStore_update_bool hC1 rT (.inr rfl)⟩
    · exact ⟨_, by rw [hgm]; unfold PreStore; grind [SemanticStore.update], hC1⟩
  obtain ⟨_, σ1, hr, -, hC, hfr, hgt, hk, hg, -⟩ :=
    e.of_T hs hns hdefd hon.gtyped hon.fresh nofun hB nofun nofun hCB hT hsh
  cases hr
  replace hg := hg g (List.mem_cons_self ..)
  have hfrE : ∀ σE : SemanticStore P, (∀ y, (σE y).isSome → (σB y).isSome ∨ rE? = some y) →
      FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s5 σE := fun σE hE y hy => by
    rcases hE y hy with h | h
    · exact (hfr y h).imp_right fun h2 b j h3 h4 =>
        (h2 b j h3 h4).imp_right (.imp_right (·.imp_right (.imp_right .inl)))
    · obtain ⟨b, j, h1, h2, -⟩ := hs.preDrawn (.inr (.inr h))
      obtain ⟨-, -, hav5, -⟩ := hs.avoids
      exact ⟨fun _ ha => by simp [hav5 ▸ ha b j h1] at h2,
        fun _ _ _ _ => .inr (.inr (.inr (.inr (.inr h))))⟩
  rcases LaidCtx.cases' e.ctx with ⟨-, hκE⟩ | ⟨x, hx, rfl⟩
  · have hreach : κE.Holds F σB := by
      rcases hκE with rfl | ⟨q, rfl, rfl⟩
      · exact hg
      · exact ⟨(hk q (Option.isSome_iff_exists.2 ⟨_, hon.reach⟩)).trans hon.reach, hg⟩
    exact ⟨σB, hk, hreach, hs.elseE hon hC hk hgt (hfrE σB fun y h => .inl h) hreach⟩
  · obtain ⟨u1, u2⟩ := update_facts σB x (HasBool.ttVal F)
    have hx0 : σL x = none := e.unbound hs hon.fresh (.inl (.inr (.inr hx)))
    have hkE : ∀ n, (σL n).isSome →
        SemanticStore.update σB x (HasBool.ttVal F) n = σL n := fun n hn =>
      (u2 n fun h => by simp [← h, hx0] at hn).trans (hk n hn)
    refine ⟨_, hkE, u1, hs.elseE hon (wfStore_update_bool hC x (.inl rfl)) hkE
      (fun n w hn hY ty ht => ?_) (hfrE _ fun y h => ?_) u1⟩
    · rcases Classical.em (x = n) with rfl | hnx
      · cases u1.symm.trans hn
        exact tyOfName_bool (e.preT hs (.inl (.inr (.inr hx)))) (.inl rfl) ht
      · exact hgt n w ((u2 n hnx).symm.trans hn) hY ty ht
    · exact (Classical.em (x = y)).elim (fun hyx => .inr (hyx ▸ hx)) fun hyx => .inl (u2 y hyx ▸ h)

include iOp iLF iLFs in
/-- No name that an arm of a laid-out `ite` both declares and assigns is live after the arms with
    a stamp from before the arms' walks. -/
private theorem LaidCore.declNotLive : ∀ n, (Tr.A.contains n = true ∧ n ∈ wDecls Tr.out.toList) ∨
    (Er.A.contains n = true ∧ n ∈ wDecls Er.out.toList) → liveBefore s6 n s4.clock = false := by
  have hnx := hs.nexts
  have hav := hs.avoids
  have hS : _ ∧ _ ∧ _ := e.wfS
  have hno : ∀ (st : WSt P) (n : P.Ident), LiveKeys st → FreshAt st n → ∀ t,
      st.live[n]? = some t → False := fun st n hk hf t ht => by
    grind [KeyOK, FreshAt, AvoidedIfFresh, freshName_counter_inj, hk n t ht]
  refine fun n hn => Bool.eq_false_iff.2 fun hl => ?_
  unfold liveBefore at hl
  cases hsn : s6.live[n]? with
  | none => simp [hsn] at hl
  | some t =>
    simp only [hsn, decide_eq_true_eq] at hl
    have hc45 : s4.clock ≤ s5.clock := hs.wE.clock
    rcases hn with ⟨-, hD⟩ | ⟨-, hD⟩
    · obtain ⟨h5, hf⟩ := arm_declNotLive e.runT nofun hs.wf5 hS.2.1
        (fun x hx b j hxj => hav.2.2.1 ▸ e.avoidSArm (.inl rfl) hx b j hxj)
        (fun l t h => (e.lab l t (by rw [← (e.labels hs l).2]; exact h)).1) n hD t hsn (by omega)
      exact hno s5 n (e.liveK5 hs) hf t h5
    · have h5 := hs.wT.toWalkCore.liveOld n t hsn (by omega)
      obtain ⟨h4, hf⟩ := arm_declNotLive e.runE hs.ctxE hs.wf4 hS.2.2
        (fun x hx b j hxj => hav.2.1 ▸ e.avoidSArm (.inr rfl) hx b j hxj)
        (fun l t h => (e.lab l t (by rw [← (e.labels hs l).1]; exact h)).1) n hD t h5 hl
      exact hno s4 n hs.liveK4 hf t h4

/-- A variable a laid-out `ite` saves around an arm that always exits (step 3b) is the current
    name of a variable in scope that an arm mentions, when no name an arm both declares and
    assigns is live from before the arms' walks. -/
private theorem LaidCore.saved3b (hgap : ∀ n, (Tr.A.contains n = true ∧ n ∈ wDecls Tr.out.toList) ∨
      (Er.A.contains n = true ∧ n ∈ wDecls Er.out.toList) → liveBefore s6 n s4.clock = false)
    {x : P.Ident} (hx : x ∈ laidCT Tr Er s6 s4.clock ∨ x ∈ laidCE Er s6 s4.clock) :
    ∃ z ∈ S, (z ∈ Block.freeVars tss ∨ z ∈ Block.freeVars ess) ∧ curName st' z = some x := by
  rcases hx with hx | hx
  · obtain ⟨hA, hl⟩ := mem_laidCT hx
    rcases hs.armT.assigned x hA with ⟨z, hz, hf, hc⟩ | hd
    · exact ⟨z, hz, .inl hf, hs.cur6 z ▸ hc⟩
    rcases hs.armE.read x (by simpa [hgap x (.inl ⟨hA, hd⟩)] using hl) with ⟨z, hz, hf, hc⟩ | hd'
    · exact ⟨z, hz, .inr hf, (hs.cur5 hz hc).1⟩
    · exact (e.dl_declDisj hs hd hd').elim
  · obtain ⟨hA, hl⟩ := mem_laidCE hx
    exact (hs.armE.assigned x hA).elim (fun ⟨z, hz, hf, hc⟩ => ⟨z, hz, .inr hf, (hs.cur5 hz hc).1⟩)
      fun hd => by simp [hgap x (.inr ⟨hA, hd⟩)] at hl

/-- A defined current name at the walk input of a laid-out `ite` of a variable in scope stays its
    current name through the walk. -/
private theorem LaidCore.of_cur0 {z : P.Ident} (hz : z ∈ S) (h0 : curName st0 z = some n) :
    curName s4 z = some n ∧ curName s5 z = some n ∧ curName st' z = some n := by
  exact (hs.curS hz ((wRen_walk e.run1).names z n nofun h0)).elim fun h4 ⟨h5, _, h7⟩ => ⟨h4, h5, h7⟩

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL e hs in
/-- A false reach context stays false in a store agreeing on its variables. -/
private theorem of_failsCongr {κ : RE P} (h : κ.Fails F σ)
    (hv : ∀ y ∈ RE.vars κ, σ' y = σ y) : κ.Fails F σ' := by
  cases κ <;> grind [RE.Fails, RE.vars]

/-- A variable of the context of a laid-out `ite` is none of the names a main-path run of the
    then arm's output may change apart from its reach (`Wr0`). -/
private theorem LaidCore.notWTκ {y : P.Ident} (hy : y ∈ RE.vars κ) :
    ¬ Wr0 (Block.idents tss) s5 s6 y := by
  obtain ⟨⟨b, j, h1, h2⟩, h3, -⟩ := e.ctxv y hy
  have hnx := hs.nexts
  rintro (⟨b', j', h4, -, h5, -⟩ | ⟨z, hz⟩ | hi)
  · exact absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
  · exact (e.rt_kvarNm hs hy z).2.1 hz
  · simp [e.avoidArm (.inl hi) b j h1] at h3

/-- A variable of the context of a laid-out `ite` is none of the names a main-path run of the
    else arm's output may change apart from its reach (`Wr0`). -/
private theorem LaidCore.notWEκ {y : P.Ident} (hy : y ∈ RE.vars κ) :
    ¬ Wr0 (Block.idents ess) s4 s5 y := by
  obtain ⟨⟨b, j, h1, h2⟩, h3, -⟩ := e.ctxv y hy
  have hnx := hs.nexts
  rintro (⟨b', j', h4, -, h5, -⟩ | ⟨z, hz⟩ | hi)
  · exact absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
  · exact (e.rt_kvarNm hs hy z).1 hz
  · simp [e.avoidArm (.inr hi) b j h1] at h3

/-- A variable of the context of a laid-out `ite` is neither declared by an arm nor a current
    name of a variable in scope nor a name drawn by the walk of the `ite`. -/
private theorem LaidCore.of_ctxNe {y : P.Ident} (hy : y ∈ RE.vars κ) :
    y ∉ wDecls Tr.out.toList ∧ y ∉ wDecls Er.out.toList ∧ (∀ z ∈ S, curName st' z ≠ some y) ∧
      ∀ s s' : WSt P, st0.next ≤ s.next → ¬ Drawn s s' y := by
  obtain ⟨⟨b, j, h1, h2⟩, h3, -⟩ := e.ctxv y hy
  have hnx := hs.nexts
  have hD : ∀ s s' : WSt P, st0.next ≤ s.next → ¬ Drawn s s' y := fun s s' hle ⟨b', j', h4, _⟩ =>
    absurd (freshName_counter_inj (h1.symm.trans h4)) (by omega)
  refine ⟨fun hw => e.notWTκ hs hy (hs.armT.declW hw), fun hw => e.notWEκ hs hy (hs.armE.declW hw),
    fun z hz hc => ?_, hD⟩
  rcases curName_cases hc with h | ⟨-, -, rfl⟩
  · exact (e.rt_kvarNm hs hy z).2.2.2 h
  · simp [e.avoidS y (List.mem_append_left _ hz) b j h1] at h3

/-- A name the else arm declares is no current name of a variable in scope at the walk output
    of the `ite`. -/
private theorem LaidCore.re_EdeclNotM (hn : n ∈ wDecls Er.out.toList) {z : P.Ident}
    (hz : z ∈ S) : curName st' z ≠ some n := fun hzn => by
  rcases hs.wT.toWalkCore.curName_back (hs.sT z hz) ((hs.cur6 z).trans hzn) with
    h5 | ⟨b, j, rfl, hna, hj⟩
  · exact hs.armE.declNotCur _ hn z hz h5
  rcases hs.armE.decl _ hn with ⟨b', j', h1, -, -, h2⟩ | ⟨hi, -⟩ | ⟨y, -, hy⟩
  · exact absurd (freshName_counter_inj h1) (by omega)
  · simp [hs.avoids.2.2.1, e.avoidArm (.inr (stmtsInits_mem_idents _ hi)) b j rfl] at hna
  · obtain ⟨-, b', j', h1, h2, -⟩ := hs.wf4.nm_fresh y _ hy
    exact absurd (freshName_counter_inj h1) (by have hn := hs.wE.next; omega)

omit iLI e in
/-- A run of the guarded output of the else arm of a laid-out `ite` under the context `q ∧ ¬g`
    keeps `q`. -/
private theorem LaidStates.of_keepQ (hiE : resolveItems T Y Er.out.toList = .ok iE)
    {trE : List (Event P)} (hrun : MainRun F iE σ trE σ') {q : P.Ident}
    (hq : κE = .andNeg q g) : σ' q = σ q :=
  hs.armE.writesQ T Y iE hiE σ trE σ' hrun q g hq

omit iDE iBE iLB iSF iHI iLI iHa iHFs iWL e hs in
/-- A main-path run keeps every bound name bound. -/
private theorem mainRun_mono {F : P.Factory} :
    ∀ {its : List (Item P)} {σ : SemanticStore P} {tr : List (Event P)} {σ' : SemanticStore P},
      MainRun F its σ tr σ' → ∀ m, (σ m).isSome → (σ' m).isSome
  | _, _, _, _, .nil, _, h => h
  | _, _, _, _, .plain (c := c) hc hr, m, h => mainRun_mono hr m <| by
    cases c with
    | call => exact hc.elim
    | cmd c => cases hc <;> first | exact h | (rename_i hst; cases hst; grind +splitImp)
  | _, _, _, _, .side hr, m, h => mainRun_mono hr m h

omit iLB iHI iLI e hs in
/-- A main-path run of resolved guarded items binds every name they declare. -/
private theorem mainRun_binds {F : P.Factory} {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} :
    ∀ (ws : List (WItem P)) (its : List (Item P)), resolveItems T Y ws = .ok its →
      ∀ {σ : SemanticStore P} {tr : List (Event P)} {σ' : SemanticStore P},
        MainRun F its σ tr σ' → ∀ n ∈ wDecls ws, (σ' n).isSome
  | [], _, _, _, _, _, _, n, hn => by simp [wDecls] at hn
  | w :: ws, its, h, σ, tr, σ', hr, n, hn => by
    obtain ⟨a, its', ha, hres, rfl⟩ := resolveItems_cons_ok h
    cases w with
    | init x ty oe =>
      obtain ⟨ty', oe', rfl⟩ : ∃ ty' oe', a = .plain (mkInit x ty' oe') := by
        cases ty <;> cases oe <;>
          simp only [resolveItem, resolveOE, bind, Except.bind, pure, Except.pure] at ha <;>
          (repeat' split at ha) <;> cases ha <;> exact ⟨_, _, rfl⟩
      rcases hr with _ | ⟨hc, hr'⟩
      simp only [wDecls, List.mem_cons] at hn
      rcases hn with rfl | hn
      · refine mainRun_mono hr' _ ?_
        cases hc <;> rename_i hst <;> cases hst <;> simp [*]
      · exact mainRun_binds ws its' hres hr' n hn
    | branch t f =>
      simp only [resolveItem, bind, Except.bind, pure, Except.pure] at ha
      (repeat' split at ha) <;> cases ha
      cases hr
    | set x oe | assume l we md | obls ro cs =>
      cases hr <;> exact mainRun_binds ws its' hres (by assumption) n (by simpa [wDecls] using hn)

/-- A main-path run of the else arm's output of a laid-out `ite` keeps the names drawn after the
    arms. -/
private theorem LaidCore.lateE (hiE : resolveItems T Y Er.out.toList = .ok iE)
    {tr : List (Event P)} (hrun : MainRun F iE σ tr σ')
    (hn : Drawn s6 st' n) (hκE : n ∉ RE.vars κE) : σ' n = σ n := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨b, j, hnb, hna, hj, -⟩ := hn
  have hnx := hs.nexts
  rcases hs.armE.writesW T Y iE hiE σ tr σ' hrun n hne with (h | ⟨z, hz⟩ | h) | h
  · obtain ⟨b', j', h1, -, -, h2⟩ := h
    exact absurd (freshName_counter_inj (hnb.symm.trans h1)) (by omega)
  · obtain ⟨-, b', j', h1, h2, -⟩ := hs.wf4.nm_fresh z n hz
    exact absurd (freshName_counter_inj (hnb.symm.trans h1)) (by omega)
  · simp [hs.avoids.2.2.2.1 ▸ e.avoidArm (.inr h) b j hnb] at hna
  · exact hκE (wvar_mem h)

/-- The prelude names `g` and `rE` are not current names of variables in scope. -/
private theorem LaidCore.of_preNotCur {y : P.Ident} (hy : y = g ∨ rE? = some y) {z : P.Ident}
    (hz : z ∈ S) : curName st' z ≠ some y := fun h => by
  have hy' : y = g ∨ y = rT ∨ rE? = some y := hy.elim .inl fun h => .inr (.inr h)
  rcases curName_cases h with h1 | ⟨-, -, rfl⟩
  · exact (hs.preNm hy' z).2.2.2 h1
  · obtain ⟨b, j, h1, h2, -, -⟩ := hs.preDrawn hy'
    simp [e.avoidS _ (List.mem_append_left _ hz) b j h1] at h2

/-- A name with a declared selector, target or copy is not a variable of the else context when
    it is not a variable of `κ` and not a current name of a variable in scope or the name is
    declared by the then arm. -/
private theorem LaidCore.of_notκE (hκ : n ∉ RE.vars κ)
    (hn : (∃ z ∈ S, curName st' z = some n) ∨ n ∈ wDecls Tr.out.toList) : n ∉ RE.vars κE := by
  intro h
  obtain hp | h' : (n = g ∨ rE? = some n) ∨ n ∈ RE.vars κ := by grind [e.of_κEvars' h]
  · exact hn.elim (fun ⟨z, hz, hc⟩ => e.of_preNotCur hs hp hz hc)
      fun hd => (e.notT hs (.inl (hp.imp_right .inr))).2 hd
  · exact hκ h'

include iOp iLF iLFs in
/-- A main-path run of the else arm's output of a laid-out `ite` keeps the names the then arm's
    output declares. -/
private theorem LaidCore.crossKeep
    (hiE : resolveItems T Y Er.out.toList = .ok iE) {σa σb : SemanticStore P}
    {tr : List (Event P)} (hrun : MainRun F iE σa tr σb) :
    ∀ n ∈ wDecls Tr.out.toList, σb n = σa n := by
  have hS : _ ∧ _ ∧ _ := e.wfS
  refine arm_crossKeep e.runE e.runT hs.ctxE hs.wf4 (fun x hx b j hb => ?_) hS.2.1 hS.2.2
    (fun l t h => (e.lab l t (by rw [← (e.labels hs l).1]; exact h)).1) hs.κEv4 T Y iE hiE
    σa tr σb hrun
  rw [hs.avoids.2.1]
  exact (List.mem_append.1 hx).elim (fun hx => e.avoidS x (List.mem_append_left _ hx) b j hb)
    fun hx => e.avoidArm (List.mem_append.1 hx) b j hb

/-- A prelude name or a name drawn after the arms of a laid-out `ite` is none of the names a
    main-path run of the else arm's output may change apart from its reach (`Wr0`). -/
private theorem LaidCore.notWE (hn : (n = g ∨ n = rT ∨ rE? = some n) ∨ Drawn s6 st' n) :
    ¬ Wr0 (Block.idents ess) s4 s5 n := by
  obtain ⟨b, j, h1, h2, hd⟩ := hs.preOrLate hn
  have hnx := hs.nexts
  rintro (⟨b', j', h3, -, h4, h5⟩ | ⟨z, hz⟩ | hi)
  · rcases hd with ⟨b'', j'', h6, -, -, h7⟩ | ⟨b'', j'', h6, -, h7, -⟩ <;>
      grind [freshName_counter_inj]
  · exact hn.elim (fun hn => (hs.preNm hn z).1 hz)
      fun hn => hn.not_below ((dl_nmBelow hs.wf4 hz).imp fun _ => .imp fun _ h => ⟨h.1, by omega⟩)
  · simp [e.avoidArm (.inr hi) b j h1] at h2

omit iLI e in
/-- A name live after the then arm of a laid-out `ite` with a stamp from before the arms' walks
    is live with that stamp after the else arm. -/
private theorem LaidCore.live65 (h : liveBefore s6 n s4.clock = true) :
    liveBefore s5 n s4.clock = true := by
  grind [liveBefore, hs.wT.liveOld, hs.wE.clock]

include iHFs iLV in
/-- A feasible loop-free run of a laid-out `ite` with empty arm outputs, no save, no merge guard
    and no registration establishes `RunPost` at the store before the `ite`, when the `ite` does
    not drop and always exits only when both arms do. -/
private theorem LaidCore.nilRun (hns : SaveNs s6 M sv cp rs cps s7 []) (hgm : gm? = none)
    (hT : resolveItems T Y Tr.out.toList = .ok []) (hE : resolveItems T Y Er.out.toList = .ok [])
    (hreg : r.regs.toList = []) (hax : r.ax = (Tr.ax && Er.ax)) (hdrop : r.drop = false)
    (hon : OnInv F T Y Lc Ex st' κ S (contFV ([.ite (.det c) tss ess md] :: k)) σ σL)
    (hrun : DRunS F X (.ite (.det c) tss ess md) σ evs o)
    (hfeas : Trace.AssumptionsHold P evalInterp () evs) :
    RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
      X σL o := by
  have hl0 : ∀ {z n : P.Ident}, z ∈ S → curName st0 z = some n → st0.live.contains n = true →
      s4.live.contains n = true ∧ s5.live.contains n = true := fun {z n} hz h0 hl => by
    obtain ⟨-, -, h1eq, -⟩ := wRen_run e.run1
    have hl4 : s4.live = st0.live := by rw [hs.pre.eq, h1eq]
    have h5l := hs.armE.liveKeep z hz n (e.of_cur0 hs hz h0).1
    grind [Std.HashMap.contains_eq_isSome_getElem?]
  have H : ∀ {st : WSt P} {Ex' : P.Ident → Prop} {κ' : RE P} {S1 : List P.Ident}
      {σv σ1 : SemanticStore P}, OnInv F T Y Lc Ex' st κ' S1 (contFV (ess :: k)) σ1 σv →
      (∀ z ∈ S, ∀ n, curName st0 z = some n → curName st z = some n ∧
        (st0.live.contains n = true → st.live.contains n = true)) →
      (∀ x ∈ S, x ∈ S1) → (∀ n, (σL n).isSome → σv n = σL n) → r.ax = false →
      RunPost F T Y Lc Ex Lab st0 st' r κ S (scopeAfter S [.ite (.det c) tss ess md]) (contFV k)
        X σL ((Outcome.normal σ1).proj σ) := fun {_ _ _ _ σv σ1} hI hcur hS1 hkeep hax => by
    have hk : ∀ x ∈ contFV k, x ∈ contFV ([.ite (.det c) tss ess md] :: k) :=
      fun x hx => mem_contFV_cons.2 (.inr hx)
    have hk' : ∀ x ∈ contFV k, x ∈ contFV (ess :: k) := fun x hx => mem_contFV_cons.2 (.inr hx)
    have hpj : ∀ x ∈ S, x ∈ contFV k → projectStore σ σ1 x = σ1 x :=
      fun x hx hv => ite_eq_left (hon.defd x hx (hk x hv)).1
    have hn : ∀ x ∈ S, x ∈ contFV k → ∀ n, curName st0 x = some n → σv n = σL n :=
      fun x hx hv n h0 => hkeep n ((hon.defd x hx (hk x hv)).2 n (e.of_cur0 hs hx h0).2.2)
    refine ⟨⟨⟨fun x hx hv n h0 hl => ?_, fun x hx hv => ⟨?_, fun n h0 => ?_⟩,
      fun x hx hv n h0 hty w w' hw hw' => ?_, fun x hx hxS => ?_, WellFormedStore.proj hI.canon,
      hon.canonL, hon.gtyped, fun x hx hv n h0 w hw => ?_, ?_⟩, hon.reach⟩,
      fun _ _ h => by simp [hreg] at h, fun _ _ _ _ _ h => by simp [CarryReg, hreg] at h,
      fun _ _ _ _ _ h => by simp [CarryReg, hreg] at h, hax, hdrop,
      fun _ _ h => by simp [hreg] at h⟩
    · rw [hpj x hx hv, ← hn x hx hv n h0]
      exact hI.agree x (hS1 x hx) (hk' x hv) n (hcur x hx n h0).1 ((hcur x hx n h0).2 hl)
    · exact hpj x hx hv ▸ (hI.defd x (hS1 x hx) (hk' x hv)).1
    · exact (hon.defd x hx (hk x hv)).2 n (e.of_cur0 hs hx h0).2.2
    · exact hI.alike x (hS1 x hx) (hk' x hv) n (hcur x hx n h0).1 hty w w' (hpj x hx hv ▸ hw)
        (hn x hx hv n h0 ▸ hw')
    · simp [projectStore, hon.undef x hx hxS]
    · exact hI.ltyped x (hS1 x hx) (hk' x hv) n (hcur x hx n h0).1 w (hpj x hx hv ▸ hw)
    · exact of_freshPost hon.fresh (fun y hy => e.whole.taken y hy) e.whole.avoid e.whole.next
        (fun x y h => e.whole.nm x y h) fun y hy => .inl hy
  subst hgm
  have hgL : σL g = none := e.unbound hs hon.fresh (.inl (.inl rfl))
  have hrL : σL rT = none := e.unbound hs hon.fresh (.inl (.inr (.inl rfl)))
  cases hrun with
  | ite_true hc hT' hsh =>
    have hCv := wfStore_update_bool (wfStore_update_bool hon.canonL g (.inl rfl)) rT (.inl rfl)
    obtain ⟨trT, σT, hrunT, -, hpost⟩ := (e.armTp hs hT).2.1 σ _ _ evs _
      (e.thenT hs hns hon (preStore_two hs.pre.g_rT) nofun nofun hCv) hT' hfeas
    cases hrunT
    rename_i oT
    cases oT with
    | exit l σ1 =>
      exact (HasBool.ttVal_ne_ffVal F
        (Option.some.inj ((update_facts _ rT (HasBool.ttVal F)).1.symm.trans hpost.1.reach))).elim
    | normal σ1 =>
      obtain ⟨hI, -, -, -, hax', -⟩ := hpost
      refine H hI (fun z hz n hn => ?_) (scopeAfter_sub S tss) (fun n hn => ?_)
        (by rw [hax, hax']; rfl)
      · exact ⟨(e.of_cur0 hs hz hn).2.1, fun h => (hl0 hz hn h).2⟩
      · rw [(update_facts _ rT (HasBool.ttVal F)).2 n fun h => by simp [← h, hrL] at hn,
          (update_facts _ g (HasBool.ttVal F)).2 n fun h => by simp [← h, hgL] at hn]
  | ite_false hc hE' hsh =>
    obtain ⟨σE, hkE, hreach, honE⟩ := e.rn_elseStore hs hns rfl hT hon (shL_of_shB hsh)
    obtain ⟨trE, σE', hrunE, -, hpost⟩ := (e.armEp hs hE).2.1 σ σE _ evs _ honE hE' hfeas
    cases hrunE
    rename_i oE
    cases oE with
    | exit l σ1 => exact absurd hpost.1.reach hreach.not_fails
    | normal σ1 =>
      obtain ⟨hI, -, -, -, hax', -⟩ := hpost
      refine H hI (fun z hz n hn => ?_) (scopeAfter_sub S ess) hkE (by simp [hax, hax'])
      exact ⟨(e.of_cur0 hs hz hn).1, fun h => (hl0 hz hn h).1⟩

omit iWL e hs in
/-- A name drawn between `s` and `s'`, or avoided by `st0` when it has the form of a fresh name,
    is not drawn between states `a` and `b` avoiding the names `st0` avoids whose counters lie
    all after those of `s` and `s'` or all before them. -/
private theorem not_drawn_of (n : P.Ident) (a b s s' : WSt P)
    (hn : Drawn s s' n ∨ AvoidedIfFresh st0 n) (ha : a.avoid = st0.avoid)
    (hle : b.next ≤ s.next ∨ s'.next ≤ a.next) : ¬ Drawn a b n := by
  grind [Drawn, AvoidedIfFresh, freshName_counter_inj]

/-- A registration of the else arm of a laid-out `ite` is not drawn by the then arm's walk. -/
private theorem LaidCore.regsE {x : P.Ident} (hx : x ∈ Er.regs.toList) :
    ¬ Drawn s5 s6 x := fun hd => by
  rcases hs.armE.decl x (hs.armE.regs x hx) with h | ⟨h, -⟩ | ⟨y, -, hy⟩
  · exact h.disj hd (Nat.le_refl _)
  · obtain ⟨b, j, h1, h2, -, -⟩ := hd
    simp [hs.avoids.2.2.1, e.avoidArm (.inr (stmtsInits_mem_idents _ h)) b j h1] at h2
  · obtain ⟨b, j, h1, h2⟩ := dl_nmBelow hs.wf4 hy
    exact hd.not_below ⟨b, j, h1, Nat.lt_of_lt_of_le h2 hs.wE.next⟩

/-- A store fresh at the else arm's walk input of a laid-out `ite`, the prelude names excepted, is
    fresh at the walk input of the `ite`. -/
private theorem LaidCore.fresh0
    (h : FreshInv Lc (fun y => Ex y ∨ y = g ∨ y = rT ∨ rE? = some y) s4 σ) :
    FreshInv Lc Ex st0 σ := by
  have hnx := hs.nexts
  have hs4tk : s4.taken = st0.taken :=
    (wRen_run e.run1).elim fun _ ⟨_, h1, _⟩ => hs.pre.eq ▸ congrArg (·.taken) h1
  exact of_freshPost h (fun y hy => hs4tk ▸ hy) hs.avoids.2.1 (by omega)
    (fun x y h => hs.c1.nm x y (hs.pre.eq ▸ h :)) fun y hy => hy.imp_right fun hy b j hj =>
      (hs.pre.drawn y hy).elim fun _ ⟨j', h1, _, h3, _⟩ =>
        freshName_counter_inj (hj.symm.trans h1) ▸ by omega

end Parts2

end -- public section

end WP
end Imperative

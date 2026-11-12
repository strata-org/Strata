/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverSpec
import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPOverTyped
import Strata.Transform.WP.WPOverEmit
import Strata.Util.ExceptProps

/-! # The simulation through commands

The walk of a command (`init`, `set`, `assume`, `assert`, `cover`) has the simulation property
(`Spec`) under every reach context; a `call` makes the walk fail.  One lemma per command kind
relates the run of the guarded output (one guarded command, or a havoc `init` followed by the
guarded command) to the loop-free step on the path, and to the shadow step off it; the state
facts come from the runs of the state primitives the walk performs.

Key theorems: `stmtSpec_cmd`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P]
  [iWL : WPLang P] [iIL : WPIteLang P]
  [iOp : HasOps P] [iLF : LawfulHasFvar P] [iFs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iIL
omit iFs
variable {tE : TypedEval P}

variable {F : P.Factory} {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
  {Lc S V D : List P.Ident} {Ex : P.Ident → Prop} {κ : RE P} {st st' s s' s1 s1' : WSt P}
  {σ σL σL2 σ1 σ' : SemanticStore P} {n x y : P.Ident}
  {e : P.Expr} {v : P.Val} {ty : P.Ty} {r : WRes P}


/-- Every recorded renaming of `s` is one of `st`, or a fresh name that the walk from `st` on may
    create (`FreshAt`). -/
private def NmGrow (st s : WSt P) : Prop :=
  ∀ z y : P.Ident, s.nm[z]? = some y → st.nm[z]? = some y ∨ FreshAt st y

/-- The renaming facts of a well-formed walk state (`WFSt`): a recorded renaming is a fresh name
    (a counter below `st.next`, not avoided) recorded in the back map, and no two variables have
    the same recorded renaming. -/
private structure NmWF (st : WSt P) : Prop where
  nm_fresh : ∀ x n : P.Ident, st.nm[x]? = some n → st.back[n]? = some x ∧
    ∃ b j, n = freshName b j ∧ j < st.next ∧ st.avoid.contains n = false
  nm_inj : ∀ x z n : P.Ident, st.nm[x]? = some n → st.nm[z]? = some n → x = z

omit iLV iLI iWL iOp iLF in
/-- A well-formed walk state has the renaming facts. -/
private theorem nmWF (h : WFSt st) : NmWF st := ⟨h.nm_fresh, h.nm_inj⟩

omit iLV iOp iLF in
/-- A run of `wName x` keeps well-formedness, the avoided and declared names, grows the
    renamings and does not decrease the counter. -/
private theorem wName_step (h : (wName x).run s = .ok (n, s')) :
    (NmWF s → NmWF s') ∧ NmGrow s s' ∧ s.next ≤ s'.next ∧ s'.avoid = s.avoid ∧
      s'.taken = s.taken := by
  rcases wName_cases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨hx, ht, rfl, rfl⟩
  any_goals exact ⟨id, fun z y hz => .inl hz, Nat.le_refl _, rfl, rfl⟩
  obtain ⟨k, hk, hle, hav⟩ := freshIn_spec s.avoid (baseOf x) s.next
  simp only [hk]
  refine ⟨fun ⟨hf, hi⟩ => ⟨fun z m hz => ?_, fun z1 z2 m h1 h2 => ?_⟩, fun z y hz => ?_,
    Nat.le_succ_of_le hle, trivial, trivial⟩
  all_goals simp only [Std.HashMap.getElem?_insert] at *
  all_goals grind [FreshAt, freshName_counter_inj]

omit iLV iOp iLF in
/-- A run of `wRen e` keeps well-formedness and grows the renamings. -/
private theorem wRen_step {we : WExpr P} {rd : List P.Ident}
    (h : (wRen e).run s = .ok ((we, rd), s')) : (NmWF s → NmWF s') ∧ NmGrow s s' := by
  refine ⟨fun hw => ?_, (wRen_walk h).nm⟩
  unfold wRen at h
  obtain ⟨r, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  refine wm_forIn_inv (fun _ _ s => NmWF s) _ (fun _ y _ s _ _ hs hb => ?_) _ [] _ s r s' hw hl
  obtain ⟨n, s2, hn, hb⟩ := wm_run_bind_ok hb
  split at hb <;> cases hb <;> exact ⟨_, rfl, (wName_step hn).1 hs⟩

omit iLV iLI in
/-- Under `OnInv` at `st`, a loop-free expression reading variables in scope that the
    continuation reads, renamed by `ren` to current names that are live, resolves to an
    expression evaluating, in a value-valued store `σL2` agreeing with the guarded store where
    it is defined, like the original in the loop-free store. -/
private theorem ev_ren_onInv (hF : WellFormedSemanticEvalBase F)
    (hI : OnInv F T Y Lc Ex st κ S V σ σL)
    (hC2 : WellFormedStore σL2 F) (h2 : ∀ m, (σL m).isSome → σL2 m = σL m) {e' : P.Expr}
    {ren : List (P.Ident × P.Ident)}
    (hren : ∀ p ∈ ren, p.1 ∈ exprFV e ∧ curName st p.1 = some p.2 ∧ p.2 ≠ p.1)
    (hrd : ∀ y ∈ exprFV e, ∃ n, curName st y = some n ∧ st.live.contains n = true ∧ (n = y ∨
      (y, n) ∈ ren)) (hS : ∀ y ∈ exprFV e, y ∈ S) (hV : ∀ y ∈ exprFV e, y ∈ V)
    (h : resolveE T Y (.user e ren) = .ok e') : P.eval F σL2 e' = P.eval F σ e := by
  obtain ⟨⟨hA, hD, -, -, hC, -⟩, -⟩ := hI
  refine ev_resolveE_user hF hC hC2 h (fun p hp => ?_) fun y hy hn => ?_ <;> grind

/-- The condition `FreshInv` puts on a name bound in the guarded store. -/
private def FreshOK (Lc : List P.Ident) (Ex : P.Ident → Prop) (st : WSt P) (y : P.Ident) : Prop :=
  (y ∈ Lc → (∀ b j, y = freshName b j → st.avoid.contains y = true) → st.taken.contains y = false) ∧
  ∀ b j, y = freshName b j → st.avoid.contains y = false →
    st.next ≤ j ∨ (∃ x : P.Ident, st.nm[x]? = some y) ∨ Ex y

omit iLV iWL iOp iLF in
/-- `FreshInv` carries over from the point before a fragment (walk output `st'`) to the point
    after it (walk input `st`) across a walk step (`WalkCore`), when each name the guarded store
    gains satisfies it. -/
private theorem freshInv_post {σL' : SemanticStore P} (hF : FreshInv Lc Ex st' σL)
    (hW : WalkCore D st st') (hdom : ∀ y, (σL' y).isSome → (σL y).isSome ∨ FreshOK Lc Ex st y) :
    FreshInv Lc Ex st σL' := fun y hy => (hdom y hy).elim (fun hy => by
    obtain ⟨hav, hnx, -, hnm, htk, -⟩ := hW
    grind [FreshInv, FreshAt, freshName_counter_inj]) id

omit iLV iLI iOp iLF in
/-- `OnInv` carries over, with the same stores, to a point whose current names are current
    names before, whose live names are live before, and where `FreshInv` holds, for fewer
    read variables. -/
private theorem onInv_keep {V' : List P.Ident} (hI : OnInv F T Y Lc Ex st' κ S V' σ σL)
    (hV : ∀ y ∈ V, y ∈ V') (hname : ∀ z m, curName st z = some m → curName st' z = some m)
    (hlive : ∀ m, st.live.contains m = true → st'.live.contains m = true)
    (hfr : FreshInv Lc Ex st σL) : OnInv F T Y Lc Ex st κ S V σ σL := by
  obtain ⟨⟨hA, hD, hL, hU, hC, hCL, hG, hT, -⟩, hR⟩ := hI
  exact ⟨⟨by grind, by grind, by grind, hU, hC, hCL, hG, by grind, hfr⟩, hR⟩

omit iLV iLI iOp iLF in
/-- A walk result without registrations, neither always exiting nor ending its main list, has
    the end facts of a normal end of its run: no exit snapshot or carried merge to be false or
    well formed, and no exit with a shadow end to satisfy. -/
private theorem regsNil_run {X : Outcome P → Prop} (h : r.regs = .nil := by rfl)
    (ha : r.ax = false := by rfl) (hd : r.drop = false := by rfl) :
    SnapFF F r st none σL ∧ CarryFF F T Y r st σL ∧ CarryOK F T Y r st σL ∧ r.ax = false ∧
      r.drop = false ∧ ExitEnds r st none X := by
  simp [SnapFF, CarryFF, CarryOK, ExitEnds, CarryReg, h, ha, hd, Rope.toList_nil]

omit iLV iLI iOp iLF in
/-- A walk result without registrations whose normal shadow end satisfies `K` has the end facts
    of an off-path run: no exit snapshot or carried merge to be false or well formed, and shadow
    ends satisfying `K`. -/
private theorem regsNil_off {K : Outcome P → Prop} (hK : r.ax = false → ∃ σs, K (.normal σs))
    (h : r.regs = .nil := by rfl) :
    SnapFF F r st none σL ∧ CarryFF F T Y r st σL ∧ CarryOK F T Y r st σL ∧ ShEnds r st none K := by
  simpa [SnapFF, CarryFF, CarryOK, ShEnds, ExitEnds, CarryReg, h, Rope.toList_nil] using hK

omit iLV iDE iHB iHF iSF iHI iLI iWL iOp iLF in
/-- The variables of an expression read by a non-`init` command are read by its continuation. -/
private theorem fv_contFV {s : PStmt P} {k : List (PStmts P)}
    (h : ∀ y ∈ exprFV e, y ∈ Stmt.freeVars s) : ∀ y ∈ exprFV e, y ∈ contFV ([s] :: k) :=
  fun y hy => mem_contFV_cons.2 (.inl (Block.freeVars_cons_sub y (h y hy)))

omit iDE iBE iLB iHF iSF iHI iWL iLV iHa iHFs iOp in
/-- The variables of a reach context keep Boolean values as the store grows. -/
private theorem bools_mono (hm : ∀ y w, σ y = some w → σ' y = some w)
    (h : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
    ∀ y ∈ RE.vars κ, σ' y = some (HasBool.ttVal F) ∨ σ' y = some (HasBool.ffVal F) :=
  fun y hy => (h y hy).imp (hm y _) (hm y _)

omit iDE iBE iLB iSF iHI iLV iOp iLF iHa iHFs in
/-- The trace of a command that is not an obligation claims no failure. -/
private theorem claim_noObl {c : Cmd P} {tr : List (Event P)} {t : AssertId P} {e : P.Expr}
    (hc : Stmt.isCheck (.cmd (.cmd c)) = false) (h : EvalE F σ (.cmd c) σ1 tr) :
    ¬ Claim t e tr := by
  rintro ⟨evs, ev, htr, -, hf⟩
  cases (h : EvalCmdE P F σ c σ1 _) <;>
    simp_all [Stmt.isCheck, List.singleton_eq_append_iff, FailsAt]

include iFs in
omit iLV in
include iIL in
/-- The walk of an `assume` after which an obligation follows, or of an obligation (`assert` or
    `cover`), has the simulation property. -/
private theorem spec_check (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident) (κ : RE P)
    (d : Nat) (f : Bool) (l : String) (e : P.Expr) (md : MetaData P) (c : Cmd P)
    (hc : c = .assume l e md ∧ f = true ∨ c = .assert l e md ∨ c = .cover l e md) :
    StmtSpec F tE Lc κ d f (.cmd (.cmd c)) := by
  intro st r st' hwf hrun T Y _ items hres S hwfS Γ hΓ hwt _ Ex _ k _ _ _ _ _ _
  rcases hc with ⟨rfl, rfl⟩ | rfl | rfl
  all_goals
    unfold wpStmt at hrun
    try simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
    obtain ⟨⟨we, rd⟩, s1, h1, hrun⟩ := wm_run_bind_ok hrun
    obtain ⟨u, s2, h2, hrun⟩ := wm_run_bind_ok hrun
    cases hrun
    obtain ⟨⟨ren, rfl, hren, hrd0, -⟩, -, hs1, hname⟩ := wRen_run h1
    obtain ⟨live, clock, h2', hlv, -⟩ := liveAdd_run (rd ++ RE.vars κ) s1
    cases h2.symm.trans h2'
    have hrd : ∀ y ∈ exprFV e, ∃ n, curName s1 y = some n ∧ live.contains n = true ∧
        (n = y ∨ (y, n) ∈ ren) := fun y hy => (hrd0 y hy).imp fun n ⟨hn, hrn, hor⟩ =>
      ⟨hn, (hlv n).2 (.inr (List.mem_append_left _ hrn)), hor⟩
    have hlive := fun m hm => (hlv m).2 (.inl (congrArg WSt.live hs1 ▸ hm))
    have hfr := fun {σL} (h : FreshInv Lc Ex _ σL) =>
      freshInv_post (st' := s1) (σL' := σL) h (wRen_walk h1) fun _ => .inl
    obtain ⟨i, _, hi, ⟨⟩, rfl⟩ := resolveItems_cons_ok (Rope.toList_one _ ▸ hres)
    refine ⟨fun σ σL t cnd b tr hOn (.cmd hE) hct => ?_, fun _ σ σL X evs o hOn hR hfe => ?_,
      fun _ σs σL K hO hK => ?_⟩
  case inl.refl.refl.refine_1 => exact absurd hct.claim (claim_noObl rfl hE)
  case inr.inl.refl.refl.refine_1 | inr.inr.refl.refl.refine_1 =>
    simp only [resolveItem, List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at hi
    obtain ⟨_, ⟨_, ⟨e', he', rfl⟩, _, ⟨⟩, rfl⟩, rfl⟩ := hi
    cases hE
    obtain ⟨evs, ev0, htr, -, hf⟩ := hct
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at htr hf <;>
      obtain ⟨rfl, ⟨⟩⟩ := List.append_inj' (htr.symm.trans (List.nil_append _).symm) rfl
    obtain ⟨⟨rfl, rfl, -, hff⟩, rfl⟩ := hf
    have hev := ev_ren_onInv hF hOn hOn.canonL (fun _ _ => rfl) hren hrd hwfS
      (fv_contFV fun _ => id) he'
    obtain ⟨wsub, hsub, -, rfl⟩ := resolveE_user_eq he'
    refine ⟨rfl, .head _, wsub, fun q hq => ?_, ?_⟩
    · obtain ⟨hq1, hq2, hq3⟩ := hren _ (hsub q hq)
      exact (curName_cases hq2).elim
        (fun h => ⟨(((wRen_step h1).1 (nmWF hwf)).nm_fresh _ _ h).1, hq1⟩)
        fun ⟨_, _, h⟩ => absurd h hq3
    cases κ
    · exact ⟨_, .here (.here (.cmd (by constructor) (List.cons_ne_nil _ _))), [], _, rfl, nofun,
        by exact ⟨⟨rfl, rfl, rfl, hev.trans hff⟩, rfl⟩⟩
    all_goals exact ⟨_, .here (.later (.cmd .eval_assume)
      (.here (.cmd (by constructor) (List.cons_ne_nil _ _)))), [_], _,
      rfl, fun _ h => Event.assume.inj (List.mem_singleton.mp h) ▸
        ev_REexpr_holds hF hOn.canonL hOn.reach, by exact ⟨⟨rfl, rfl, rfl, hev.trans hff⟩, rfl⟩⟩
  all_goals try (obtain ⟨σ1, rfl, hE⟩ := hR.cmd_inv; cases hE)
  all_goals
    obtain ⟨t, hm, hT⟩ : ∃ t, MainRun F [i] σL t σL ∧ Trace.AssumptionsHold P evalInterp () t := by
      first
        | obtain ⟨_, -, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 hi
          exact ⟨[], .side .nil, nofun⟩
        | obtain ⟨a', ha', rfl⟩ := resolveItem_assume hi
          first
            | exact run_assume (ev_kImp_fails hF hO.canonL hO.reach ha'
                (ResTy.bool tE (OffInv.resTy hF hO hO.canonL (fun _ _ => id)
                  (hΓ (.inl rfl)) hwt.2.1.1 hwt.2.2.1
                  (fun p hp => ⟨(hren p hp).1, (hren p hp).2.1⟩)
                  (fun y hy => (hrd y hy).imp fun _ h => ⟨h.1, h.2.2⟩) hwfS
                  (fv_contFV fun _ => id))) hO.bools)
            | exact run_assume (ev_kImp_holds hF hOn.canonL hOn.reach ha' (fun _ h => (ev_ren_onInv
                hF hOn hOn.canonL (fun _ _ => rfl) hren hrd hwfS (fv_contFV fun _ => id) h).trans
                (hfe _ (List.mem_singleton_self _))) (.inl rfl))
    first
      | exact .inr ⟨t, σL, hm, hT, onInv_keep hOn contFV_tail_sub hname hlive (hfr hOn.fresh),
          regsNil_run⟩
      | exact ⟨t, σL, hm, hT, ⟨hO.canonL, hO.reach, hO.bools, fun x hx hv n hn =>
          hO.defd x hx (contFV_tail_sub hv) n (hname _ _ hn), hO.gtyped, hfr hO.fresh⟩,
          fun _ _ _ => rfl, regsNil_off fun _ => ⟨σs, hK⟩⟩

omit iLV iLI iWL iOp iLF in
/-- A successful run of `modify g` applies `g` to the state. -/
private theorem run_modify_ok {g : WSt P → WSt P} {u : PUnit}
    (h : (modify g : WM P PUnit).run s = .ok (u, s')) : s' = g s :=
  (Prod.mk.inj (Except.ok.inj h)).2.symm

omit iLV iLI iWL iOp iLF in
/-- In a well-formed state, two variables that are avoided when of the form of a fresh name and
    have the same current name are equal. -/
private theorem curName_inj (hw : NmWF st) {z1 z2 m : P.Ident}
    (h1av : ∀ b j, z1 = freshName b j → st.avoid.contains z1 = true)
    (h2av : ∀ b j, z2 = freshName b j → st.avoid.contains z2 = true) (h1 : curName st z1 = some m)
    (h2 : curName st z2 = some m) : z1 = z2 := by
  grind [curName, NmWF]

omit iLV iLI iOp iLF in
/-- A run of `wName x` returning `n` records `n` as the renaming of `x`, or returns `x` itself
    (no later declaration of `x` met) and keeps the state. -/
private theorem wName_kind (h : (wName x).run s = .ok (n, s')) :
    s'.nm[x]? = some n ∨ (n = x ∧ s.taken.contains x = false ∧ s' = s) := by
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, h2, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ <;> simp [*]

omit iLV iWL iOp iLF in
/-- A name with a counter from `st.next` on and below `st'.next`, not avoided, not a renaming in
    `st'` (whose avoided names are those of `st`), satisfies the condition `FreshInv` at `st` puts
    on a bound name, and is unbound in every guarded store satisfying `FreshInv` at `st'` with
    exceptions below `st.next`. -/
private theorem fresh_new (hEx : ∀ y, Ex y → ∀ b j, y = freshName b j → j < st.next) {b : String}
    {k : Nat} (hy : y = freshName b k) (hk : st.next ≤ k) (hk' : k < st'.next)
    (hav : st.avoid.contains y = false) (hav' : st'.avoid = st.avoid)
    (hnm : ∀ z : P.Ident, st'.nm[z]? ≠ some y) :
    FreshOK Lc Ex st y ∧ ∀ σL : SemanticStore P, FreshInv Lc Ex st' σL → σL y = none :=
  ⟨by grind [FreshOK, freshName_counter_inj],
    fun _ hF => Option.eq_none_iff_forall_ne_some.2 fun w hw => by grind [FreshInv]⟩

omit iLV iLB iHI iLI iOp iLF in
/-- Updating a name to a value of its final declared type (when it has no type reference) keeps
    every guarded value of a name without a type reference of its final declared type. -/
private theorem gtyped_update
    (hg : ∀ n w, σ n = some w → Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty →
      HasVal.valueOfTy F w ty)
    (hv : Y[n]? = none → ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F v ty) :
    ∀ m w, SemanticStore.update σ n v m = some w → Y[m]? = none → ∀ ty,
      tyOfName T Y m = .ok ty → HasVal.valueOfTy F w ty := by grind [SemanticStore.update]

omit iLV iOp iLF in
/-- `OnInv` after a write of `x` (an assignment or a declaration): from `OnInv` before it (walk
    state `st'`, scope `S`), for the scope `S1` of `x` and the variables of `S`, with `x` holding
    the new value `v` in the loop-free store and the other values kept, its current name `n` at
    the point after the write (`st`) holding `v` in the guarded store `σL2` updated at `n`, where
    `n` is unbound before or the current name at `st'` of no other variable of `S`, `σL2` a
    value-valued store agreeing with the guarded store before where that is defined, current
    names of the other variables and live names (except `n`) of `st` current and live before,
    and the facts on the new guarded store alone. -/
private theorem onInv_upd {S1 : List P.Ident} {l : PStmts P} {k : List (PStmts P)}
    (hI : OnInv F T Y Lc Ex st' κ S (contFV (l :: k)) σ σL) (hS1 : ∀ z, z ∈ S1 ↔ z = x ∨ z ∈ S)
    (hxn : ∀ m, curName st x = some m → m = n)
    (hne : σL n = none ∨ n ∉ RE.vars κ ∧ ∀ z ∈ S, curName st' z = some n → z = x)
    (hname : ∀ z m, z ≠ x → curName st z = some m → curName st' z = some m)
    (hlive : ∀ m, m ≠ n → st.live.contains m = true → st'.live.contains m = true)
    (h1x : σ1 x = some v) (h1o : ∀ z, x ≠ z → σ1 z = σ z) (hv : HasVal.value F v)
    (h2 : ∀ m, (σL m).isSome → σL2 m = σL m) (hC2 : WellFormedStore σL2 F)
    (hvty : ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F v ty)
    (hg2 : ∀ m w, σL2 m = some w → Y[m]? = none → ∀ ty, tyOfName T Y m = .ok ty →
      HasVal.valueOfTy F w ty) (hW : WalkCore D st st')
    (hdom : ∀ y, (SemanticStore.update σL2 n v y).isSome → (σL y).isSome ∨ FreshOK Lc Ex st y) :
    OnInv F T Y Lc Ex st κ S1 (contFV k) σ1 (SemanticStore.update σL2 n v) := by
  obtain ⟨⟨hA, hD, hL, hU, hC, -, -, hT, hF⟩, hR⟩ := hI
  obtain ⟨hLn, hLo⟩ := update_facts σL2 n v
  have hh : ∀ y ∈ RE.vars κ, ∀ b, σL y = some b → SemanticStore.update σL2 n v y = some b :=
    fun y hy b hs => (hLo y fun h => hne.elim (fun h0 => by simp [← h, h0] at hs)
      fun h0 => h0.1 (h ▸ hy)).trans ((h2 y (by simp [hs])).trans hs)
  have hreach : κ.Holds F (SemanticStore.update σL2 n v) := by
    cases κ <;> first
      | trivial
      | exact hh _ (.head _) _ hR
      | exact ⟨hh _ (.head _) _ hR.1, hh _ (.tail _ (.head _)) _ hR.2⟩
  have hK : ∀ z ∈ S1, x ≠ z → z ∈ contFV k → ∀ m, curName st z = some m → z ∈ S ∧
      z ∈ contFV (l :: k) ∧ curName st' z = some m ∧ SemanticStore.update σL2 n v m = σL m ∧
      (σL m).isSome ∧ (st.live.contains m = true → st'.live.contains m = true) := by
    intro z hz hxz hzV m hm
    have hzS := ((hS1 z).1 hz).resolve_left (Ne.symm hxz)
    have hm' := hname z m (Ne.symm hxz) hm
    have hs := (hD z hzS (contFV_tail_sub hzV)).2 m hm'
    have hmn : n ≠ m := fun h => hne.elim (fun h0 => by simp [← h, h0] at hs)
      fun h0 => hxz (h0.2 z hzS (h ▸ hm')).symm
    exact ⟨hzS, contFV_tail_sub hzV, hm', (hLo m hmn).trans (h2 m hs), hs, hlive m (Ne.symm hmn)⟩
  have hC1 : WellFormedStore σ1 F := fun y w hy => (Classical.em (x = y)).elim
    (fun h => Option.some.inj (h1x.symm.trans (h ▸ hy)) ▸ hv) fun h => hC y w (h1o y h ▸ hy)
  refine ⟨⟨fun z hz hzV m hm hl => ?_, fun z hz hzV => ?_, fun z hz hzV m hm _ w w' h1 h2 => ?_,
    fun z hz hzS => ?_, hC1, wfStore_update hC2 n hv, gtyped_update hg2 fun _ => hvty,
    fun z hz hzV m hm w h1 => ?_, freshInv_post hF hW hdom⟩, hreach⟩
  all_goals rcases Classical.em (x = z) with rfl | hxz
  · rw [hxn m hm, hLn, h1x]
  · obtain ⟨hzS, hzV', hm', he, -, hl'⟩ := hK z hz hxz hzV m hm
    rw [he, h1o z hxz, hA z hzS hzV' m hm' (hl' hl)]
  · exact ⟨by simp [h1x], fun m hm => by simp [hxn m hm, hLn]⟩
  · refine ⟨h1o z hxz ▸ (hD z (((hS1 z).1 hz).resolve_left (Ne.symm hxz)) (contFV_tail_sub hzV)).1,
      fun m hm => (hK z hz hxz hzV m hm).elim fun _ ⟨_, _, he, hs, _⟩ => he ▸ hs⟩
  · rw [hxn m hm, hLn] at h2
    exact Option.some.inj (h1x.symm.trans h1) ▸ Option.some.inj h2 ▸ fun _ => id
  · obtain ⟨hzS, hzV', hm', he, -⟩ := hK z hz hxz hzV m hm
    exact hL z hzS hzV' m hm' ‹_› w w' (h1o z hxz ▸ h1) (he ▸ h2)
  · exact absurd ((hS1 _).2 (.inl rfl)) hzS
  · exact (h1o z hxz).trans (hU z hz fun h => hzS ((hS1 z).2 (.inr h)))
  · exact Option.some.inj (h1x.symm.trans h1) ▸ hxn m hm ▸ hvty
  · exact (hK z hz hxz hzV m hm).elim fun hS ⟨hV, hm', _⟩ => hT z hS hV m hm' w (h1o z hxz ▸ h1)

omit iLV iOp iLF in
/-- The WP name `n` that `wName x` returns for a declaration of `x` (from a well-formed state
    `s1`, to `s1'`) has its declared type at the point before the declaration (state `st'`) as
    final type, and is unbound in every guarded store satisfying `FreshInv` at `st'`, when `st'`
    records the declaration of the local `x`, keeps the renamings of `s1'` except `x`'s, its back
    map, counter and avoided names, and the exceptions are not in its back map. -/
private theorem declName_facts (hk : (wName x).run s1 = .ok (n, s1')) (hw1 : NmWF s1)
    (hEx : ∀ y, Ex y → st'.back[y]? = none) (hxLc : x ∈ Lc)
    (hxav : ∀ b j, x = freshName b j → st'.avoid.contains x = true)
    (htk : st'.taken.contains x = true)
    (hnm : ∀ z y : P.Ident, st'.nm[z]? = some y → z ≠ x ∧ s1'.nm[z]? = some y)
    (hback : ∀ m y : P.Ident, s1'.back[m]? = some y → st'.back[m]? = some y)
    (hnext : s1'.next ≤ st'.next) (havd : st'.avoid = s1'.avoid) (hT : FinalOK Lc st' T Y)
    (hty : st'.tys[n]? = some ty) :
    T[n]? = some ty ∧ ∀ σL : SemanticStore P, FreshInv Lc Ex st' σL → σL n = none := by
  obtain ⟨hf, hi⟩ := (wName_step hk).1 hw1
  obtain ⟨hT1, -, -⟩ := hT
  rcases wName_kind hk with h | ⟨rfl, h2, rfl⟩ <;>
    grind [FreshInv, freshName_counter_inj, Option.ne_none_iff_isSome]

omit iLV iOp iLF in
/-- The WP name `n` that `wName x` returns for a declaration of `x` (from a well-formed state
    `s1` reached from `st`) satisfies the condition `FreshInv` at `st` puts on a bound name, when
    `x` is avoided if it has the form of a fresh name. -/
private theorem decl_freshAt (hk : (wName x).run s1 = .ok (n, s1')) (hw1 : NmWF s1)
    (hg : NmGrow st s1) (hnx : st.next ≤ s1.next) (htk : s1.taken = st.taken)
    (havd : s1.avoid = st.avoid)
    (hxav : ∀ b j, x = freshName b j → st.avoid.contains x = true) : FreshOK Lc Ex st n := by
  obtain ⟨k, hk', hn, hav⟩ := freshIn_spec s1.avoid (baseOf x) s1.next
  obtain ⟨hf, -⟩ := hw1
  rcases wName_cases hk with ⟨h1, -⟩ | ⟨-, h2, rfl, -⟩ | ⟨-, -, rfl, -⟩
  all_goals grind [FreshOK, NmGrow, FreshAt, freshName_counter_inj]

omit iLV iLI iWL iOp iLF in
/-- A successful run of `liveDel x` removes `x` from the live set. -/
private theorem liveDel_step {u : Unit}
    (h : (liveDel x).run s = .ok (u, s')) : s' = { s with live := s.live.erase x } :=
  (Prod.mk.inj (Except.ok.inj ((liveDel_run x s).symm.trans h))).2.symm

omit iLV iLI iWL iOp iLF in
/-- A run of `liveDel n` then `liveAdd xs` keeps every field but the live set, keeps live the live
    names other than `n`, and makes the names of `xs` live. -/
private theorem liveDelAdd_step {xs : List P.Ident} {t : WSt P} {u v : Unit}
    (h1 : (liveDel n).run s = .ok (u, t)) (h2 : (liveAdd xs).run t = .ok (v, s')) :
    s'.nm = s.nm ∧ s'.taken = s.taken ∧ s'.avoid = s.avoid ∧ s'.back = s.back ∧
      s'.next = s.next ∧ s'.tys = s.tys ∧
      (∀ m, m ≠ n → s.live.contains m = true → s'.live.contains m = true) ∧
      ∀ m ∈ xs, s'.live.contains m = true := by
  obtain rfl := liveDel_step h1
  obtain ⟨live, clock, rfl, hl⟩ := liveAdd_step h2
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun m hm h => by grind, fun m hm => (hl m).2 (.inr hm)⟩

omit iLV iLB iHI iLI iOp iLF in
/-- The variable in the `else` part of a resolved `ite(κ, t, var r)` under a variable context has
    a final declared type. -/
private theorem resolveE_kIte_var {t : WExpr P} {r : P.Ident} {x : P.Expr}
    (h : resolveE T Y (kIte κ t (.var r)) = .ok x) (hκ : κ ≠ .top) :
    ∃ ty, tyOfName T Y r = .ok ty := by
  cases κ <;> simp only [kIte, resolveE, bind, Except.bind, pure, Except.pure] at h <;> grind

omit iLV iWL iOp iLF in
/-- The current name, at a state whose renamings grow from `st`, of a variable avoided when of
    the form of a fresh name is not a variable of a reach context whose variables are
    non-avoided fresh names below `st.next` that are not renamings at `st`. -/
private theorem notin_vars
    (hk : ∀ y ∈ RE.vars κ, (∃ b j, y = freshName b j ∧ j < st.next) ∧
      st.avoid.contains y = false ∧ (∀ z : P.Ident, st.nm[z]? ≠ some y) ∧ st.back[y]? = none)
    (hg : NmGrow st st') (hxav : ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (h : curName st' x = some n) : n ∉ RE.vars κ := fun hn => by
  obtain ⟨⟨b, j, hj, hjn⟩, hav, hnm, -⟩ := hk n hn
  rcases curName_cases h with h | ⟨-, -, rfl⟩ <;> grind [NmGrow, FreshAt, freshName_counter_inj]

omit iLV iWL iOp iLF in
/-- The current WP name of a variable avoided when of the form of a fresh name has no entry in
    the final type references. -/
private theorem noTyRef (hFin : FinalOK Lc st T Y) (hw : WFSt st)
    (hxav : ∀ b j, x = freshName b j → st.avoid.contains x = true)
    (hxn : curName st x = some n) : Y[n]? = none := by
  obtain ⟨hnf, -, -, htf, -, -, -, htk, -⟩ := hw
  obtain ⟨-, -, hY⟩ := hFin
  refine Option.eq_none_iff_forall_ne_some.2 fun y hy => ?_
  rcases curName_cases hxn with h | ⟨-, -, rfl⟩ <;> grind [freshName_counter_inj]

omit iLI iOp iLF in
/-- The guarded value `w'` of the current WP name `n` of a variable in scope read later, and a
    value `v` sharing a type with the loop-free value, share a type, when `n` has no type
    reference; `v` has every final declared type of `n`. -/
private theorem storedTy (hI : OnInv F T Y Lc Ex st κ S V σ σL) (hxS : x ∈ S) (hxV : x ∈ V)
    (hxn : curName st x = some n) {w' : P.Val} {prev : P.Val} {ty0 : P.Ty} (hprev : σ x = some prev)
    (hpty : HasVal.valueOfTy F prev ty0) (hvty0 : HasVal.valueOfTy F v ty0) (hw' : σL n = some w')
    (hw2 : σL2 n = some w') (hY : Y[n]? = none) :
    HasVal.valueOfStoredTy (P := P) F σL2 n v ∧
      ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F v ty := by
  have hv : ∀ ty, tyOfName T Y n = .ok ty → HasVal.valueOfTy F v ty := fun ty ht =>
    LawfulHasVal.valueOfTy_congr _ _ _ _ _ (hI.ltyped x hxS hxV n hxn prev hprev ty ht) hpty hvty0
  refine ⟨(Classical.em (∃ ty, tyOfName T Y n = .ok ty)).elim (fun ⟨ty, ht⟩ => ?_) fun hT => ?_, hv⟩
  · exact ⟨w', ty, hw2, hI.gtyped n w' hw' hY ty ht, hv ty ht⟩
  · exact ⟨w', ty0, hw2, hI.alike x hxS hxV n hxn (fun ty h => hT ⟨ty, h⟩) _ _ hprev hw' ty0 hpty,
      hvty0⟩

section
omit iBE iLB iHI iLI iHa iWL iOp iLF iLV

/-- A nondeterministic `init` of an unbound name binds it to a value of its type. -/
private theorem initN_run (hF : WellFormedSemanticEvalBase F) (h0 : σ n = none)
    (hv : HasVal.valueOfTy F v ty) :
    EvalE F σ (.cmd (.init n ty .nondet .empty)) (σ.update n v) [] :=
  .eval_init_unconstrained (.init h0 (update_facts σ n v).1 (update_facts σ n v).2) hv hF.var

/-- A deterministic `init` of an unbound name binds it to the value of its expression. -/
private theorem initD_run (hF : WellFormedSemanticEvalBase F) (hev : P.eval F σ e = some v)
    (h0 : σ n = none) (hv : HasVal.valueOfTy F v ty) :
    EvalE F σ (.cmd (.init n ty (.det e) .empty)) (σ.update n v) [] :=
  .eval_init hev (.init h0 (update_facts σ n v).1 (update_facts σ n v).2) hv hF.var

/-- A deterministic `set` of a bound name binds it to the value of its expression. -/
private theorem setD_run (hF : WellFormedSemanticEvalBase F) {w : P.Val}
    (hev : P.eval F σ e = some v)
    (hw : σ n = some w) (hv : HasVal.valueOfStoredTy (P := P) F σ n v) :
    EvalE F σ (.cmd (.set n (.det e) .empty)) (σ.update n v) [] :=
  .eval_set hev (.update hw (update_facts σ n v).1 (update_facts σ n v).2) hv hF.var

end

omit iBE iLB iHB iHF iSF iHI iWL iLV iHa iHFs iOp in
/-- A name bound after an update of a name satisfying `Q` is bound before or satisfies `Q`. -/
private theorem isSome_update {Q : P.Ident → Prop} (h : (SemanticStore.update σ n v y).isSome)
    (hn : Q n) : (σ y).isSome ∨ Q y := by
  by_cases hy : y = n <;> simp_all [SemanticStore.update]

include iFs iIL in
/-- The walk of a deterministic `set x := e` after which an obligation follows has the
    simulation property. -/
private theorem spec_setDet (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident) (κ : RE P)
    (d : Nat) (x : P.Ident) (e : P.Expr) (md : MetaData P) :
    StmtSpec F tE Lc κ d true (.cmd (.cmd (.set x (.det e) md))) := by
  intro st r st' hwf hrun T Y hfin items hres S hwfS Γ hΓ hwt hav Ex _ k _ _ hκv _ _ _
  have hW := wpStmt_walkOK hrun
  have hwf' := hW.wf hwf (by simp [stmtsInits])
  have hname := fun z m => hW.names z m (by simp [stmtsInits])
  have hav' := fun z hz => hW.avoid ▸ hav z (List.mem_append_left _ hz)
  have hV' := fv_contFV (s := .cmd (.cmd (.set x (.det e) md))) (k := k) fun _ => .tail _
  have hxV : x ∈ contFV ([Stmt.cmd (.cmd (.set x (.det e) md))] :: k) :=
    mem_contFV_cons.2 (.inl (List.mem_append_left _ (List.mem_cons_self ..)))
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ite_false] at hrun
  obtain ⟨⟨we, rd⟩, s1, h1, hrun⟩ := wm_run_bind_ok hrun
  obtain ⟨n, s2, h2, hrun⟩ := wm_run_bind_ok hrun
  obtain ⟨⟨ren, rfl, hren, hrd, -⟩, -, hs1, -⟩ := wRen_run h1
  have hk2 := wName_curName_keep h2
  have hl0 : s2.live = st.live := by rw [(wName_state h2).2, hs1]
  split at hrun
  all_goals
    obtain ⟨_, s3, h3, hrun⟩ := wm_run_bind_ok hrun
    obtain ⟨_, _, ⟨⟩, hrun⟩ := wm_run_bind_ok hrun
    obtain ⟨_, s4, h4, hrun⟩ := wm_run_bind_ok hrun
    cases hrun
  case' h_1 =>
    cases liveDel_step h3
    obtain ⟨live, clock, hst, hlv⟩ := liveAdd_step h4
    have hlive : ∀ m, m ≠ n → st.live.contains m = true → st'.live.contains m = true :=
      fun m hm hl => hst ▸ (hlv m).2 (.inl (by simp [hl0, hl, Std.HashMap.contains_erase,
        Ne.symm hm]))
  case' h_2 =>
    obtain ⟨l3, c3, rfl, hlv3⟩ := liveAdd_step h3
    obtain ⟨live, clock, hst, hlv⟩ := liveAdd_step h4
    have hlive : ∀ m, m ≠ n → st.live.contains m = true → st'.live.contains m = true :=
      fun m _ hl => hst ▸ (hlv m).2 (.inl ((hlv3 m).2 (.inl (hl0 ▸ hl))))
  all_goals
    have hcur : ∀ z, curName st' z = curName s2 z := fun z => by rw [hst]; rfl
    obtain ⟨i, _, hi, ⟨⟩, rfl⟩ := resolveItems_cons_ok (Rope.toList_one _ ▸ hres)
    obtain ⟨e'', he'', rfl⟩ := resolveItem_set hi
    have hren' : ∀ p ∈ ren, p.1 ∈ exprFV e ∧ curName st' p.1 = some p.2 ∧ p.2 ≠ p.1 :=
      fun p hp => (hren p hp).imp_right (.imp_left fun h => hcur _ ▸ hk2 _ _ h)
    have hrd' : ∀ y ∈ exprFV e, ∃ m, curName st' y = some m ∧ st'.live.contains m = true ∧
        (m = y ∨ (y, m) ∈ ren) := fun y hy => (hrd y hy).imp fun m ⟨h1, h2, h3⟩ =>
      ⟨hcur _ ▸ hk2 _ _ h1, hst ▸ (hlv m).2 (.inr (List.mem_append_left _ h2)), h3⟩
    have hxn' : curName st' x = some n := hcur x ▸ wName_curName h2
    refine ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE),
      fun _ σ σL X evs o hOn hR _ => ?_, fun _ σs σL K hOff hK => ?_⟩
    · obtain ⟨σ1, rfl, hE⟩ := hR.cmd_inv
      obtain ⟨v, hv, ⟨prev, ty0, hprev, hpty, hvty0⟩, h1x, h1o, rfl⟩ := EvalCmdE.set_det_inv hE
      obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 ((hOn.defd x hwfS.1 hxV).2 n hxn')
      have hxav := hav x (List.mem_append_left _ hwfS.1)
      have hY := noTyRef hfin hwf' (hW.avoid ▸ hxav) hxn'
      obtain ⟨hst, hvty⟩ := storedTy hOn hwfS.1 hxV hxn' hprev hpty hvty0 hw' hw' hY
      obtain ⟨w0, ty1, hw0, hw0ty, hvty1⟩ := hst
      have hev := ev_kIte_holds (e := .var n) (v := v) hF hOn.canonL hOn.reach he''
        (fun _ h => (ev_ren_onInv hF hOn hOn.canonL (fun _ _ => rfl) hren' hrd' hwfS.2 hV' h).trans
          hv) hvty1 fun _ h => ⟨w0, ev_res_var hF hOn.canonL hw0 h, hw0ty⟩
      have hst : HasVal.valueOfStoredTy (P := P) F σL n v := ⟨w0, ty1, hw0, hw0ty, hvty1⟩
      have hval := LawfulHasVal.valueOfTy_isVal F v ty0 hvty0
      refine .inr ⟨[], _, .plain (setD_run hF hev hw' hst) .nil, nofun,
        onInv_upd hOn (fun z => ⟨.inr, (·.elim (· ▸ hwfS.1) id)⟩)
          (fun m h => Option.some.inj ((hname x m h).symm.trans hxn')) (.inr ⟨notin_vars hκv hW.nm
            hxav hxn', fun z hz h => curName_inj (nmWF hwf') (hav' z hz) (hW.avoid ▸ hxav) h hxn'⟩)
          (fun z m _ => hname z m) hlive h1x h1o hval (fun _ _ => rfl) hOn.canonL hvty hOn.gtyped
          hW.1 fun _ h => .inl ((isSome_update (Q := fun y => (σL y).isSome) h
            (by simp [hw'])).elim id id), regsNil_run⟩
    · first
        | exact hOff.reach.elim
        | obtain ⟨w, hw, hwty⟩ := hOff.defd x hwfS.1 hxV n hxn'
          obtain ⟨ty, hty⟩ := resolveE_kIte_var he'' ‹_›
          have hev : P.eval F σL e'' = some w :=
            ev_kIte_fails hF hOff.canonL hOff.reach he'' (fun _ => ev_res_var hF hOff.canonL hw)
              (hwty ty hty)
              (by
                obtain ⟨T', hT', he⟩ := hwt.1.1
                cases Except.ok.inj ((hΓ (.inl rfl) x hwfS.1 T' hT' n hxn').symm.trans hty)
                exact OffInv.resTy hF hOff hOff.canonL (fun _ _ => id) (hΓ (.inl rfl)) he hwt.2.2.1
                  (fun p hp => ⟨(hren' p hp).1, (hren' p hp).2.1⟩)
                  (fun y hy => (hrd' y hy).imp fun _ h => ⟨h.1, h.2.2⟩) hwfS.2 hV')
              hOff.bools
          exact ⟨[], σL, .plain (c := .cmd (.set n (.det e'') .empty)) (EvalCmdE.eval_set hev
            (.update hw hw fun _ _ => rfl) ⟨w, ty, hw, hwty ty hty, hwty ty hty⟩ hF.var) .nil,
            nofun, { hOff with
              defd := fun z hz hzV m hm => hOff.defd z hz (contFV_tail_sub hzV) m (hname z m hm)
              fresh := freshInv_post hOff.fresh hW.1 fun _ => .inl }, fun _ _ _ => rfl,
            regsNil_off fun _ => ⟨σs, hK⟩⟩

omit iBE iLB iHB iHF iSF iHI iWL iLV iHa iHFs iOp in
/-- Updating an unbound name keeps every binding. -/
private theorem update_mono (h : σ n = none) (v : P.Val) :
    ∀ y w, σ y = some w → SemanticStore.update σ n v y = some w := fun y w hy => by
  grind [SemanticStore.update]

omit iBE iLB iHB iHF iSF iHI iWL iLV iHa iHFs iDE iOp in
/-- A store extending `σ` agrees with `σ` wherever `σ` is defined. -/
private theorem eq_of_mono (hm : ∀ y w, σ y = some w → σ' y = some w) :
    ∀ y, (σ y).isSome → σ' y = σ y := fun y hy => by grind [Option.isSome_iff_exists]

include iIL in
/-- The walk of a nondeterministic `set x := *` after which an obligation follows has the
    simulation property. -/
private theorem spec_setNondet (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident) (κ : RE P)
    (d : Nat)
    (x : P.Ident) (md : MetaData P) :
    StmtSpec F tE Lc κ d true (.cmd (.cmd (.set x .nondet md))) := by
  intro st r st' hWF0 h T Y hFin items hres S hxS Γ hΓ hwt hav Ex hEx k _ _ hsep _ _ _
  have hW := wpStmt_walkOK h
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  obtain ⟨n, s1, h1, h⟩ := wm_run_bind_ok h
  obtain ⟨hh, s2, h2, h⟩ := wm_run_bind_ok h
  cases (wFreshLike_run n s1).symm.trans h2
  obtain ⟨kk, hkk, hle, havh⟩ := freshIn_spec s1.avoid (baseOf n) s1.next
  generalize hh : freshName (P := P) (baseOf n) kk = g at *
  obtain ⟨live, clock, rfl, rfl, hlv⟩ : ∃ live clock,
      st' = { s1 with next := kk + 1, tyOf := s1.tyOf.insert g n, live := live, clock := clock } ∧
      r = { out := (Rope.one (WItem.init g (TyRef.of n) none)).app
              (Rope.one (WItem.set n (some (kIte κ (.var g) (.var n))))),
            sk := [SkEntry.havoc g], A := Std.HashSet.ofList [n] } ∧
      (∀ m, m ≠ n → s1.live.contains m = true → live.contains m = true) := by
    simp only [hkk] at h
    split at h
    all_goals
      obtain ⟨u1, t1, g1, h⟩ := wm_run_bind_ok h
      obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    · obtain rfl := liveDel_step g1
      exact ⟨_, _, rfl, rfl, fun m hm h => by simp [h, Std.HashMap.contains_erase, Ne.symm hm]⟩
    · obtain ⟨live, clock, rfl, hl⟩ := liveAdd_step g1
      exact ⟨live, clock, rfl, rfl, fun m _ h => (hl m).2 (.inl h)⟩
  obtain ⟨hw1, hg1, hnext1, hav1, -⟩ := wName_step h1
  have hw := hw1 (nmWF hWF0)
  have hxn : curName s1 x = some n := wName_curName h1
  have hname : ∀ z m, curName st z = some m → curName s1 z = some m := wName_curName_keep h1
  have hlive := fun m hm hl => hlv m hm ((congrArg WSt.live (wName_state h1).2 :) ▸ hl)
  have hxav := hav x (List.mem_append_left _ hxS)
  have hxV : x ∈ contFV ([.cmd (.cmd (.set x .nondet md))] :: k) :=
    mem_contFV_cons.2 (.inl (Block.freeVars_cons_sub x List.mem_cons_self))
  have hinj : ∀ z ∈ S, curName s1 z = some n → z = x := fun z hz hzn =>
    curName_inj hw (fun b j hj => hav1 ▸ hav z (List.mem_append_left _ hz) b j hj)
      (hav1 ▸ hxav) hzn hxn
  have hnm : ∀ z : P.Ident, s1.nm[z]? ≠ some g := fun z hz =>
    let ⟨_, _, _, hj, hjn, _⟩ := hw.nm_fresh z g hz
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hjn hle) (freshName_counter_inj (hh.trans hj)).symm
  have hYg : Y[g]? = some n := hFin.2.1 g n (by simp)
  obtain ⟨hfrg, hunb⟩ := fresh_new (fun y hy => (hEx y hy).1) hh.symm (Nat.le_trans hnext1 hle)
    (Nat.lt_succ_self kk) (hav1 ▸ havh) hW.avoid hnm
  rw [Rope.toList_app, Rope.toList_one, Rope.toList_one] at hres
  obtain ⟨i, _, hi, h2, rfl⟩ := resolveItems_cons_ok hres
  obtain ⟨j, _, hj, ⟨⟩, rfl⟩ := resolveItems_cons_ok h2
  obtain ⟨tyn, htyn, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 hi
  obtain ⟨e'', he'', rfl⟩ := resolveItem_set hj
  refine ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE),
    fun _ σ σL X evs o hI hD _ => ?_, fun _ σs σL K hO hSh => ?_⟩
  · obtain ⟨σ1, rfl, hE⟩ := DRunS.cmd_inv hD
    obtain ⟨v, ⟨prev, ty0, hprev, hpty, hvty0⟩, hx1, hfro, -⟩ := EvalCmdE.set_nondet_inv hE
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 ((hI.defd x hxS hxV).2 n hxn)
    have hv := LawfulHasVal.valueOfTy_isVal _ _ _ hvty0
    have h0 := hunb σL hI.fresh
    have hm1 := update_mono h0 v
    have hC1 := wfStore_update hI.canonL g hv
    have hw1' : SemanticStore.update σL g v n = some w' := hm1 n w' hw'
    obtain ⟨hst, hvty⟩ := storedTy hI hxS hxV hxn hprev hpty hvty0 hw' hw1'
      (noTyRef hFin (hW.wf hWF0 (by simp [stmtsInits])) (hav1 ▸ hxav) hxn)
    obtain ⟨w0, ty1, hw0, hw0ty, hvty1⟩ := hst
    have hev := ev_kIte_holds hF hC1 (hI.reach.mono hm1) he''
      (fun _ => ev_res_var hF hC1 (update_facts σL g v).1) hvty1
      fun _ h => ⟨w0, ev_res_var hF hC1 hw0 h, hw0ty⟩
    have hst : HasVal.valueOfStoredTy (P := P) F (SemanticStore.update σL g v) n v :=
      ⟨w0, ty1, hw0, hw0ty, hvty1⟩
    exact .inr ⟨_, _, .plain (initN_run hF h0 (hvty tyn htyn)) (.plain (setD_run hF hev hw1' hst)
      .nil), nofun, onInv_upd hI (fun z => ⟨.inr, (·.elim (· ▸ hxS) id)⟩)
      (fun m h => Option.some.inj ((hname x m h).symm.trans hxn))
      (.inr ⟨notin_vars hsep hg1 hxav hxn, hinj⟩) (fun z m _ => hname z m) hlive hx1 hfro hv
      (eq_of_mono hm1) hC1 hvty (gtyped_update hI.gtyped fun hY => by simp [hYg] at hY) hW.1
      fun y hy => (isSome_update (Q := fun y => (SemanticStore.update σL g v y).isSome) hy
        (by simp [hw1'])).elim (isSome_update · hfrg) (isSome_update · hfrg), regsNil_run⟩
  · obtain ⟨w', hw', hwty⟩ := hO.defd x hxS hxV n hxn
    have hgt := hwty tyn htyn
    have h0 := hunb σL hO.fresh
    have hm1 := update_mono h0 w'
    have hC1 := wfStore_update hO.canonL g (LawfulHasVal.valueOfTy_isVal _ _ _ hgt)
    have hw1' : SemanticStore.update σL g w' n = some w' := hm1 n w' hw'
    have hev := ev_kIte_fails hF hC1 (hO.reach.mono hm1) he'' (fun _ => ev_res_var hF hC1 hw1')
      hgt (fun _ h => ⟨w', ev_res_var hF hC1 (update_facts σL g w').1 h, hgt⟩)
      (bools_mono hm1 hO.bools)
    refine ⟨_, _, .plain (initN_run hF h0 hgt) (.plain (EvalCmdE.eval_set hev
      (.update hw1' hw1' fun _ _ => rfl) ⟨w', tyn, hw1', hgt, hgt⟩ hF.var) .nil), nofun,
      ⟨hC1, hO.reach.mono hm1, bools_mono hm1 hO.bools, fun z hz hv m hm =>
        (hO.defd z hz (contFV_tail_sub hv) m (hname z m hm)).imp fun w h => ⟨hm1 m w h.1, h.2⟩,
        gtyped_update hO.gtyped fun hY => by simp [hYg] at hY,
        freshInv_post hO.fresh hW.1 fun _ hy => isSome_update hy hfrg⟩,
        fun y hy _ => eq_of_mono hm1 y hy, regsNil_off fun _ => ⟨σs, hSh⟩⟩

omit iLV iLB iHI iLI iOp iLF in
/-- A value of the final declared type of a name has every type its name resolves to. -/
private theorem valueOfTy_of_T (h : T[n]? = some ty) :
    ∀ v, HasVal.valueOfTy F v ty → ∀ ty', tyOfName T Y n = .ok ty' → HasVal.valueOfTy F v ty' :=
  fun v hv _ h' => by simp_all [tyOfName, pure, Except.pure]

omit iOp iLF in
/-- The walk of a nondeterministic `init x : ty` after which an obligation follows has the
    simulation property. -/
private theorem spec_initNondet (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident) (κ : RE P)
    (d : Nat) (x : P.Ident) (ty : P.Ty) (md : MetaData P) :
    StmtSpec F tE Lc κ d true (.cmd (.cmd (.init x ty .nondet md))) := by
  intro st r st' hwf hrun T Y hfin items hres S hwfS Γ hΓ hwt hav Ex hEx k _ _ _ _ _ _
  have hW := wpStmt_walkOK hrun
  have hxav := hav x (List.mem_append_right _ (by simp [Block.idents, Stmt.idents]))
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ite_false] at hrun
  obtain ⟨n, s1, h1, hrun⟩ := wm_run_bind_ok hrun
  obtain ⟨_, s2, h2, hrun⟩ := wm_run_bind_ok hrun
  obtain ⟨_, s3, h3, hrun⟩ := wm_run_bind_ok hrun
  cases hrun
  obtain ⟨_, s0, hk⟩ := wName_ok x st
  cases (wDecl_run hk).symm.trans h1
  cases run_modify_ok h2
  have hst := liveDel_step h3
  obtain ⟨hT, hn0⟩ := declName_facts (ty := ty) hk (nmWF hwf) (fun y hy => (hEx y hy).2) hwfS.2
    (hW.avoid ▸ hxav) (by simp [hst])
    (fun z y h => by simpa [hst, Std.HashMap.getElem?_erase, @eq_comm _ z] using h) (by simp [hst])
    (by simp [hst]) (by simp [hst]) hfin (by simp [hst])
  have hvty := valueOfTy_of_T (F := F) (Y := Y) hT
  have hfrn : FreshOK Lc Ex st n :=
    decl_freshAt hk (nmWF hwf) (fun _ _ => .inl) (Nat.le_refl _) rfl rfl hxav
  have hname : ∀ z m, z ≠ x → curName st z = some m → curName st' z = some m :=
    fun z m hz => hW.names z m (by simp [stmtsInits, hz])
  have hxn : ∀ m, curName st x = some m → m = n := fun m h =>
    Option.some.inj ((wName_curName_keep hk x m h).symm.trans (wName_curName hk))
  have hl0 : s0.live = st.live := (congrArg WSt.live (wName_state hk).2 :)
  have hlive : ∀ m, m ≠ n → st.live.contains m = true → st'.live.contains m = true :=
    fun m hm hl => hst ▸ by simp [hl0, hl, Std.HashMap.contains_erase, Ne.symm hm]
  obtain ⟨i, _, hi, ⟨⟩, rfl⟩ := resolveItems_cons_ok (Rope.toList_one _ ▸ hres)
  obtain ⟨_, ⟨⟩, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 hi
  refine ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE),
    fun _ σ σL X evs o hOn hR _ => ?_, fun _ σs σL K hOff ⟨v, hvt, hKv⟩ => ?_⟩
  · obtain ⟨σ1, rfl, hE⟩ := hR.cmd_inv
    obtain ⟨v, hvt, -, h1x, h1o, rfl⟩ := EvalCmdE.init_nondet_inv hE
    have hnL := hn0 _ hOn.fresh
    have hval := LawfulHasVal.valueOfTy_isVal F v ty hvt
    exact .inr ⟨[], _, .plain (initN_run hF hnL hvt) .nil, nofun,
      onInv_upd hOn (fun _ => List.mem_cons) hxn (.inl hnL) hname hlive h1x h1o hval
        (fun _ _ => rfl) hOn.canonL (hvty v hvt) hOn.gtyped hW.1
        (fun y h => isSome_update h hfrn), regsNil_run⟩
  · have hnL := hn0 _ hOff.fresh
    have hval := LawfulHasVal.valueOfTy_isVal F v ty hvt
    have hm := update_mono hnL v
    refine ⟨[], _, .plain (initN_run hF hnL hvt) .nil, nofun,
      ⟨wfStore_update hOff.canonL n hval, hOff.reach.mono hm, bools_mono hm hOff.bools,
        fun z hz hzV m hm' => ?_, gtyped_update hOff.gtyped fun _ => hvty v hvt,
        freshInv_post hOff.fresh hW.1 fun y h => isSome_update h hfrn⟩,
      fun y hy _ => eq_of_mono hm y hy, regsNil_off fun _ => ⟨_, hKv⟩⟩
    rcases Classical.em (z = x) with rfl | hzx
    · exact (hxn m hm').symm ▸ ⟨v, (update_facts _ n v).1, hvty v hvt⟩
    · exact (hOff.defd z ((List.mem_cons.1 hz).resolve_left hzx) (contFV_tail_sub hzV) m
        (hname z m hzx hm')).imp fun w h => ⟨hm m w h.1, h.2⟩

include iFs iIL in
/-- The walk of a deterministic `init x : ty := e` after which an obligation follows has the
    simulation property. -/
private theorem spec_initDet (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident) (κ : RE P)
    (d : Nat) (x : P.Ident) (ty : P.Ty) (e : P.Expr) (md : MetaData P) :
    StmtSpec F tE Lc κ d true (.cmd (.cmd (.init x ty (.det e) md))) := by
  intro st r st' hWF0 h T Y hFin items hres S ⟨hxS, hxLc, hS⟩ Γ hΓ hwt hav Ex hEx k _ _ _ _ _ _
  have hW := wpStmt_walkOK h
  simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  obtain ⟨⟨we, rd⟩, s0, h0, h⟩ := wm_run_bind_ok h
  obtain ⟨n, s1, h1, h⟩ := wm_run_bind_ok h
  obtain ⟨u, s2, h2, h⟩ := wm_run_bind_ok h
  obtain rfl := run_modify_ok h2
  obtain ⟨⟨hnm2, htk2, hav2, hbk2, hnx2, hlv2, hrdl, hty'⟩, hrg, hax, hdr, hκ⟩ :
      (st'.nm = s1.nm ∧ st'.taken = s1.taken ∧ st'.avoid = s1.avoid ∧ st'.back = s1.back ∧
        s1.next ≤ st'.next ∧
        (∀ m, m ≠ n → s1.live.contains m = true → st'.live.contains m = true) ∧
        (∀ m ∈ rd ++ RE.vars κ, st'.live.contains m = true) ∧ st'.tys[n]? = some ty) ∧
      r.regs = .nil ∧ r.ax = false ∧ r.drop = false ∧
      ((κ = .top ∧ r.out = .one (.init n (.known ty) (some we))) ∨ (κ ≠ .top ∧ ∃ kk, s1.next ≤ kk ∧
          s1.avoid.contains (freshName (P := P) (baseOf x) kk) = false ∧
          st'.next = kk + 1 ∧ st'.tys[freshName (P := P) (baseOf x) kk]? = some ty ∧
          r.out = (Rope.one (.init (freshName (P := P) (baseOf x) kk) (.known ty) none)).app
            (.one (.init n (.known ty)
              (some (kIte κ we (.var (freshName (P := P) (baseOf x) kk)))))))) := by
    split at h
    case' h_2 =>
      obtain ⟨xd, t0, g0, h⟩ := wm_run_bind_ok h
      obtain ⟨kk, hkk, hle, havk⟩ := freshIn_spec s1.avoid (baseOf x) s1.next
      rw [wFresh_run, hkk] at g0
      cases g0
      obtain ⟨u1, t1, g1, h⟩ := wm_run_bind_ok h
      obtain rfl := run_modify_ok g1
    all_goals
      obtain ⟨u2, t2, g2, h⟩ := wm_run_bind_ok h
      obtain ⟨u3, t3, g3, h⟩ := wm_run_bind_ok h
      obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
      obtain ⟨hnm, htk, hav, hbk, hnx, hty, hlv, hrd⟩ := liveDelAdd_step g2 g3
    · exact ⟨⟨hnm, htk, hav, hbk, hnx ▸ Nat.le_succ_of_le hle, hlv, hrd,
        by simp [hty, Std.HashMap.getElem_insert]⟩, rfl, rfl, rfl,
        .inr ⟨‹_›, kk, hle, havk, hnx, by simp [hty], rfl⟩⟩
    · exact ⟨⟨hnm, htk, hav, hbk, hnx ▸ .refl, hlv, hrd, by simp [hty]⟩, rfl, rfl, rfl,
        .inl ⟨rfl, rfl⟩⟩
  obtain ⟨⟨ren, rfl, hren, hrd, -⟩, hnext0, hs0, hkeep0⟩ := wRen_run h0
  obtain ⟨-, -, hcz, -, hst1⟩ := wDecl_spec h1
  obtain ⟨_, s1', hk⟩ := wName_ok x s0
  cases (wDecl_run hk).symm.trans h1
  obtain ⟨-, -, hnk, havk, -⟩ := wName_step hk
  have hw0' := (wRen_step h0).1 (nmWF hWF0)
  obtain ⟨hav0, htk0⟩ : s0.avoid = st.avoid ∧ s0.taken = st.taken := by rw [hs0]; exact ⟨rfl, rfl⟩
  have hl1 : s1'.live = st.live := by rw [hs0] at hst1; simpa using congrArg WSt.live hst1
  have hV := fv_contFV (s := .cmd (.cmd (.init x ty (.det e) md))) (k := k) fun _ => id
  have hxav := hav x (List.mem_append_right _ (by simp [Block.idents, Stmt.idents]))
  have hxav' : ∀ b j, x = freshName b j → st'.avoid.contains x = true := hW.avoid ▸ hxav
  have hcur := fun z hzx => (curName_eq_of_nm_taken hnm2 htk2 z).trans (hcz z hzx)
  have hname := fun z m hzx hm => (hcur z hzx).trans (hkeep0 z m hm)
  have hxn : ∀ m, curName st x = some m → m = n := fun m hm =>
    Option.some.inj ((wName_curName_keep hk x m (hkeep0 x m hm)).symm.trans (wName_curName hk))
  have hlive := fun m hm hl => hlv2 m hm (hl1 ▸ hl)
  have hren' : ∀ p ∈ ren, p.1 ∈ exprFV e ∧ curName st' p.1 = some p.2 ∧ p.2 ≠ p.1 := fun p hp =>
    (hren p hp).imp_right (.imp_left ((hcur _ fun h => hxS (h ▸ hS _ (hren p hp).1)).trans ·))
  have hrd' : ∀ y ∈ exprFV e, ∃ m, curName st' y = some m ∧ st'.live.contains m = true ∧
      (m = y ∨ (y, m) ∈ ren) := fun y hy => (hrd y hy).imp fun m ⟨h1, h2, h3⟩ =>
    ⟨(hcur y fun h => hxS (h ▸ hS y hy)).trans h1, hrdl m (List.mem_append_left _ h2), h3⟩
  have hnmz : ∀ z y, st'.nm[z]? = some y → z ≠ x ∧ s1'.nm[z]? = some y := fun z y hz => by
    simpa [hnm2, Std.HashMap.getElem?_erase, @eq_comm _ z] using hz
  obtain ⟨hTn, hun⟩ := declName_facts hk hw0' (fun y hy => (hEx y hy).2) hxLc hxav' (by simp [htk2])
    hnmz (fun _ _ h => hbk2 ▸ h) hnx2 hav2 hFin hty'
  have hvtyn := valueOfTy_of_T (F := F) (Y := Y) hTn
  have hfrn : FreshOK Lc Ex st n := decl_freshAt hk hw0' (wRen_step h0).2 hnext0 htk0 hav0 hxav
  rcases hκ with ⟨rfl, hout⟩ | ⟨hκ, kk, hle, havx, hnxk, htyx, hout⟩
  · rw [hout] at hres
    obtain ⟨i, _, hi, ⟨⟩, rfl⟩ := resolveItems_cons_ok (Rope.toList_one _ ▸ hres)
    obtain ⟨e', he', rfl⟩ := resolveItem_init_det hi
    refine ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE),
      fun _ σ σL X evs o hI hD _ => ?_, fun _ σs σL K hO _ => hO.reach.elim⟩
    · obtain ⟨σ1, rfl, hE⟩ := DRunS.cmd_inv hD
      obtain ⟨v, hev, -, hx1, h1o, rfl, hvty0⟩ := EvalCmdE.init_det_inv hE
      have hv := EvalsTo.value hF.val hI.canon hev
      have hn0 := hun σL hI.fresh
      have hev' := (ev_ren_onInv hF hI hI.canonL (fun _ _ => rfl) hren' hrd' hS hV he').trans hev
      exact .inr ⟨_, _, .plain (initD_run hF hev' hn0 hvty0) .nil, nofun,
        onInv_upd hI (fun _ => List.mem_cons) hxn (.inl hn0) hname hlive hx1 h1o hv
          (fun _ _ => rfl) hI.canonL (hvtyn v hvty0) hI.gtyped hW.1 fun _ h => isSome_update h hfrn,
        regsNil_run hrg hax hdr⟩
  · generalize hxd : freshName (P := P) (baseOf x) kk = xd at *
    have hstk : st.next ≤ kk := Nat.le_trans hnext0 (Nat.le_trans hnk hle)
    have havxd : st.avoid.contains xd = false := hav0 ▸ havk ▸ havx
    have hxdnm : ∀ z, s1'.nm[z]? ≠ some xd := fun z hz =>
      let ⟨_, _, _, hj, hjn, _⟩ := ((wName_step hk).1 hw0').nm_fresh z xd hz
      Nat.ne_of_lt (Nat.lt_of_lt_of_le hjn hle) (freshName_counter_inj (hxd.trans hj)).symm
    obtain ⟨hfrx, hxdun⟩ := fresh_new (Lc := Lc) (fun y hy => (hEx y hy).1) hxd.symm hstk
      (hnxk ▸ Nat.lt_succ_self kk) havxd hW.avoid fun z hz => hxdnm z (hnmz z xd hz).2
    have hnxd : n ≠ xd := fun he => (wName_kind hk).elim (fun hn => hxdnm x (he ▸ hn))
      fun ⟨hn, _⟩ => nomatch (hxav _ _ (hn ▸ he.trans hxd.symm)).symm.trans (hn ▸ he ▸ havxd :)
    have hvtyx := valueOfTy_of_T (F := F) (Y := Y) ((hFin.1 xd ty htyx).elim id fun h => h.elim
      (fun ⟨_, hfa, _⟩ => nomatch (hav2 ▸ hfa _ _ hxd.symm).symm.trans havx)
      fun ⟨_, _, hj, hjn, _⟩ => absurd (freshName_counter_inj (hxd.trans hj)) (by omega))
    rw [hout, Rope.toList_app, Rope.toList_one, Rope.toList_one] at hres
    obtain ⟨i, _, hi, h2, rfl⟩ := resolveItems_cons_ok hres
    obtain ⟨j, _, hj, ⟨⟩, rfl⟩ := resolveItems_cons_ok h2
    obtain ⟨_, ⟨⟩, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 hi
    obtain ⟨e'', he'', rfl⟩ := resolveItem_init_det hj
    have hstore : ∀ (σL : SemanticStore P) v, FreshInv Lc Ex st' σL → WellFormedStore σL F →
        HasVal.value F v → σL n = none ∧ σL xd = none ∧ (SemanticStore.update σL xd v) n = none ∧
        (∀ m w, σL m = some w →
          SemanticStore.update (SemanticStore.update σL xd v) n v m = some w) ∧
        (∀ m w, σL m = some w → SemanticStore.update σL xd v m = some w) ∧
        WellFormedStore (SemanticStore.update σL xd v) F := fun σL v hf hC hv => by
      have hn0 := hun σL hf
      have hx0 := hxdun σL hf
      have hn1 : SemanticStore.update σL xd v n = none := by simp [SemanticStore.update, hnxd, hn0]
      exact ⟨hn0, hx0, hn1, fun m w h => update_mono hn1 v m w (update_mono hx0 v m w h),
        update_mono hx0 v, wfStore_update hC xd hv⟩
    have hdom : ∀ (σL : SemanticStore P) v y, (SemanticStore.update
        (SemanticStore.update σL xd v) n v y).isSome →
        (σL y).isSome ∨ FreshOK Lc Ex st y := fun σL v y hy =>
      (isSome_update hy hfrn).elim (isSome_update · hfrx) .inr
    refine ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE),
      fun _ σ σL X evs o hI hD _ => ?_, fun _ σs σL K hO hSh => ?_⟩
    · obtain ⟨σ1, rfl, hE⟩ := DRunS.cmd_inv hD
      obtain ⟨v, hev, -, hx1, h1o, rfl, hvty0⟩ := EvalCmdE.init_det_inv hE
      have hv := EvalsTo.value hF.val hI.canon hev
      obtain ⟨hn0, hx0, hn1, hm, hm1, hC1⟩ := hstore σL v hI.fresh hI.canonL hv
      have hev' := ev_kIte_holds hF hC1 (hI.reach.mono hm1) he'' (fun t' ht' =>
        (ev_ren_onInv hF hI hC1 (eq_of_mono hm1) hren' hrd' hS hV ht').trans hev) hvty0
        fun _ h => ⟨v, ev_res_var hF hC1 (update_facts σL xd v).1 h, hvty0⟩
      exact .inr ⟨_, _, .plain (initN_run hF hx0 hvty0) (.plain (initD_run hF hev' hn1 hvty0)
        .nil), nofun, onInv_upd hI (fun _ => List.mem_cons) hxn (.inl hn0) hname hlive
        hx1 h1o hv (eq_of_mono hm1) hC1 (hvtyn v hvty0)
        (gtyped_update hI.gtyped fun _ => hvtyx v hvty0) hW.1 (hdom σL v), regsNil_run hrg hax hdr⟩
    · obtain ⟨v, hvty0, hK⟩ := hSh
      simp only [OffPost, hax, Bool.false_eq_true, ↓reduceIte]
      have hv := LawfulHasVal.valueOfTy_isVal _ _ _ hvty0
      obtain ⟨-, hx0, hn1, hm, hm1, hC1⟩ := hstore σL v hO.fresh hO.canonL hv
      have hev' := ev_kIte_fails hF hC1 (hO.reach.mono hm1) he''
        (fun _ => ev_res_var hF hC1 (update_facts σL xd v).1) hvty0
        (OffInv.resTy hF hO hC1 hm1 (hΓ (.inl rfl)) hwt.1.1 hwt.2.2.1
          (fun p hp => ⟨(hren' p hp).1, (hren' p hp).2.1⟩)
          (fun y hy => (hrd' y hy).imp fun _ h => ⟨h.1, h.2.2⟩) hS hV)
        (bools_mono hm1 hO.bools)
      refine ⟨_, _, .plain (initN_run hF hx0 hvty0) (.plain (initD_run hF hev' hn1 hvty0) .nil),
        nofun, ⟨wfStore_update hC1 _ hv, hO.reach.mono hm,
          bools_mono hm hO.bools, fun z hz hv' m hm' => ?_,
          gtyped_update (gtyped_update hO.gtyped fun _ => hvtyx v hvty0) fun _ => hvtyn v hvty0,
          freshInv_post hO.fresh hW.1 (hdom σL v)⟩, fun y hy _ => eq_of_mono hm y hy,
          regsNil_off (fun _ => ⟨_, hK⟩) hrg⟩
      · rcases Classical.em (z = x) with rfl | hzx
        · exact (hxn m hm').symm ▸ ⟨v, (update_facts _ n v).1, hvtyn v hvty0⟩
        · exact (hO.defd z ((List.mem_cons.1 hz).resolve_left hzx) (contFV_tail_sub hv') m
            (hname z m hzx hm')).imp fun w h => ⟨hm m w h.1, h.2⟩

omit iLV iOp iLF in
/-- The final type of the WP name that the walk of an `init x : ty` (an obligation following it)
    gives `x` after it is `ty`. -/
private theorem init_finalTy {Lc : List P.Ident} {x : P.Ident} {ty : P.Ty}
    {rhs : ExprOrNondet P} {md : MetaData P}
    (hrun : (wpStmt κ d true (.cmd (.cmd (.init x ty rhs md)))).run st = .ok (r, st'))
    (hwf : WFSt st) (hfin : FinalOK Lc st' T Y) (hxLc : x ∈ Lc)
    (hxav : ∀ b j, x = freshName b j → st.avoid.contains x = true) :
    ∀ n, curName st x = some n → T[n]? = some ty := by
  have hW := wpStmt_walkOK hrun
  cases rhs with
  | nondet =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ite_false] at hrun
    obtain ⟨n, s1, h1, hrun⟩ := wm_run_bind_ok hrun
    obtain ⟨_, s2, h2, hrun⟩ := wm_run_bind_ok hrun
    obtain ⟨_, s3, h3, hrun⟩ := wm_run_bind_ok hrun
    cases hrun
    obtain ⟨_, s0, hk⟩ := wName_ok x st
    cases (wDecl_run hk).symm.trans h1
    cases run_modify_ok h2
    have hst := liveDel_step h3
    obtain ⟨hT, -⟩ := declName_facts (Ex := fun _ => False) (ty := ty) hk (nmWF hwf) nofun hxLc
      (hW.avoid ▸ hxav) (by simp [hst])
      (fun z y h => by simpa [hst, Std.HashMap.getElem?_erase, @eq_comm _ z] using h)
      (by simp [hst])
      (by simp [hst]) (by simp [hst]) hfin (by simp [hst])
    exact fun m h => Option.some.inj ((wName_curName_keep hk x m h).symm.trans (wName_curName hk))
      ▸ hT
  | det e =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrun
    obtain ⟨⟨we, rd⟩, s0, h0, h⟩ := wm_run_bind_ok hrun
    obtain ⟨n, s1, h1, h⟩ := wm_run_bind_ok h
    obtain ⟨u, s2, h2, h⟩ := wm_run_bind_ok h
    obtain rfl := run_modify_ok h2
    obtain ⟨hnm2, htk2, hav2, hbk2, hnx2, hty'⟩ :
        st'.nm = s1.nm ∧ st'.taken = s1.taken ∧ st'.avoid = s1.avoid ∧ st'.back = s1.back ∧
          s1.next ≤ st'.next ∧ st'.tys[n]? = some ty := by
      split at h
      case' h_2 =>
        obtain ⟨xd, t0, g0, h⟩ := wm_run_bind_ok h
        obtain ⟨kk, hkk, hle, havk⟩ := freshIn_spec s1.avoid (baseOf x) s1.next
        rw [wFresh_run, hkk] at g0
        cases g0
        obtain ⟨u1, t1, g1, h⟩ := wm_run_bind_ok h
        obtain rfl := run_modify_ok g1
      all_goals
        obtain ⟨u2, t2, g2, h⟩ := wm_run_bind_ok h
        obtain ⟨u3, t3, g3, h⟩ := wm_run_bind_ok h
        obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
        obtain ⟨hnm, htk, hav, hbk, hnx, hty, -, -⟩ := liveDelAdd_step g2 g3
      · exact ⟨hnm, htk, hav, hbk, hnx ▸ Nat.le_succ_of_le hle,
          by simp [hty, Std.HashMap.getElem_insert]⟩
      · exact ⟨hnm, htk, hav, hbk, hnx ▸ .refl, by simp [hty]⟩
    obtain ⟨⟨ren, rfl, -, -, -⟩, -, -, hkeep0⟩ := wRen_run h0
    obtain ⟨_, s1', hk⟩ := wName_ok x s0
    cases (wDecl_run hk).symm.trans h1
    have hw0' := (wRen_step h0).1 (nmWF hwf)
    have hnmz : ∀ z y, st'.nm[z]? = some y → z ≠ x ∧ s1'.nm[z]? = some y := fun z y hz => by
      simpa [hnm2, Std.HashMap.getElem?_erase, @eq_comm _ z] using hz
    obtain ⟨hTn, -⟩ := declName_facts (Ex := fun _ => False) hk hw0' nofun hxLc
      (hW.avoid ▸ hxav) (by simp [htk2]) hnmz (fun _ _ h => hbk2 ▸ h) hnx2 hav2 hfin hty'
    exact fun m hm => Option.some.inj ((wName_curName_keep hk x m (hkeep0 x m hm)).symm.trans
      (wName_curName hk)) ▸ hTn

omit iLV iOp iLF in
/-- **The typing after a statement** (`StmtTyCtx`): the walk of a statement carries the
    agreement of a typing of its scope with the final type maps to the scope after it, the
    typing extended with the statement's definitions. -/
theorem stmtTyCtx (Lc : List P.Ident) (κ : RE P) (d : Nat) (s : PStmt P) : StmtTyCtx Lc κ d s := by
  intro st r st' hwf hrun T Y hfin S hwfS hav Γ hΓ x hx ty hty n hn
  have hnot : ∀ z ∉ Stmt.topInits s, Γ.extend (Stmt.typedDefinedVars s) z = Γ z := fun z hz => by
    rcases s with ((⟨y, _, _, _⟩ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _
    case cmd.cmd.init =>
      have hzy : y ≠ z := fun h => hz (h ▸ .head _)
      simp [VarTyping.extend, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
        CmdExt.typedDefinedVars, Cmd.typedDefinedVars, List.find?, hzy]
    all_goals rfl
  rcases List.mem_append.1 hx with hxi | hxS
  · obtain ⟨y, ty', rhs, md, rfl⟩ : ∃ y ty' rhs md, s = .cmd (.cmd (.init y ty' rhs md)) := by
      rcases s with ((⟨y, ty', rhs, md⟩ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _
      · exact ⟨y, ty', rhs, md, rfl⟩
      all_goals simp [Stmt.topInits] at hxi
    obtain rfl : x = y := by simpa [Stmt.topInits] using hxi
    have hty' : ty' = ty := by
      simpa [VarTyping.extend, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
        CmdExt.typedDefinedVars, Cmd.typedDefinedVars, List.find?] using hty
    subst hty'
    have hxLc : x ∈ Lc := by cases rhs <;> simp_all [Stmt.WellScoped]
    have hT := init_finalTy hrun hwf hfin hxLc
      (hav x (List.mem_append_right _ (by cases rhs <;> simp [Block.idents, Stmt.idents]))) n hn
    simp only [tyOfName, hT]
    rfl
  · have hni : x ∉ stmtsInits [s] := fun h => (wfl_inits_scope [s] ⟨hwfS, trivial⟩ h).2.2 hxS
    have hxi : x ∉ Stmt.topInits s := fun h => hni (by
      rcases s with ((⟨⟩ | _) | _) | _ | _ | _ | _ | _ <;>
        simp_all [Stmt.topInits, stmtsInits])
    exact hΓ x hxS ty ((hnot x hxi).symm.trans hty) n ((wpStmt_walkOK hrun).names x n hni hn)

include iFs iIL in
/-- The walk of a command has the simulation property. -/
theorem stmtSpec_cmd {F : P.Factory} (hF : WellFormedSemanticEvalBase F) (Lc : List P.Ident)
    (κ : RE P) (d : Nat) (f : Bool) (c : CmdExt P) : StmtSpec F tE Lc κ d f (.cmd c) :=
  match c, f with
  | .cmd (.init x ty (.det e) md), true => spec_initDet hF Lc κ d x ty e md
  | .cmd (.init x ty .nondet md), true => spec_initNondet hF Lc κ d x ty md
  | .cmd (.set x (.det e) md), true => spec_setDet hF Lc κ d x e md
  | .cmd (.set x .nondet md), true => spec_setNondet hF Lc κ d x md
  | .cmd (.assume l a md), true => spec_check hF Lc κ d _ l a md _ (.inl ⟨rfl, rfl⟩)
  | .cmd (.assert l e md), f => spec_check hF Lc κ d f l e md _ (.inr (.inl rfl))
  | .cmd (.cover l e md), f => spec_check hF Lc κ d f l e md _ (.inr (.inr rfl))
  | .cmd (.init ..), false | .cmd (.set ..), false | .cmd (.assume ..), false =>
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      ⟨fun _ _ _ _ _ _ _ (.cmd hE) hct => absurd hct.claim (claim_noObl rfl hE), nofun, nofun⟩
  | .call .., _ => fun _ _ _ _ h => nomatch (by simpa only [wpStmt] using h :)

end -- public section

end WP
end Imperative


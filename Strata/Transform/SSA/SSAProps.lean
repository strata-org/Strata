/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSA
public import Strata.Transform.Passive.ProgramProps
import Strata.DL.Imperative.PureExprProps
import Strata.Util.ExceptProps


/-! # Properties of the SSA phase

The output of `ssaBody` on a guarded program is an obligation program with the structural shape
of one, only obligations following an `assert` when only obligations follow it in the input
(`ssaBody_shape`), and it is syntactically well scoped from the entry names
(`ssaEntry_wellScoped`).  The traversal only extends the undo log, and undoing the extension gives
back the mapping it started from (`ssaList_frame`, `undoTo_frame`).

The entry renaming gives each free variable a fresh entry name (`ssaEntryRen_spec`).

Key theorems: `ssaBody_shape`, `ssaEntry_wellScoped`, `ssaEntryRen_spec`, `ssaList_frame`,
`undoTo_frame`.

Key definitions: `SFrame`, `entryMap`, `SNames`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLId : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iW : WPLang P]
  [iLV : LawfulHasVal P] [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFvs : LawfulHasFvars P]
omit iLId iLV iOp iLF iLFvs
variable {x y : P.Ident} {ρ : Std.HashMap P.Ident (SVal P)} {s s' : SSt P} {Dd Dd' : List P.Ident}
  {α β : Type} {v : SVal P} {ty : P.Ty} {e : P.Expr} {u : Unit} {o out lay : PStmts P} {ρ0 : Ren P}
  {so : SOut P}


/-! ## The SSA monad: inversion of successful steps -/

section
omit iW
/-- A bind succeeds exactly when its first part does and its continuation does from the
    intermediate state. -/
private theorem SM.bind_iff {x : SM P α} {f : α → SM P β} {b : β} :
    (x >>= f) s = .ok (b, s') ↔ ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok (b, s') := by
  change (x s >>= fun p => f p.1 p.2) = _ ↔ _
  rcases x s with _ | ⟨a, s1⟩ <;> simp [Bind.bind, Except.bind, and_assoc]

/-- A `pure` succeeds exactly with its value and the state it starts from. -/
private theorem SM.pure_iff {a b : α} :
    (pure a : SM P α) s = .ok (b, s') ↔ a = b ∧ s = s' := by simp [pure, StateT.pure, Except.pure]

/-- A `get` followed by `f` runs `f` on the state, from the state. -/
private theorem SM.get_bind {f : SSt P → SM P α} : (get >>= f) s = f s s := rfl

/-- A `modify f` followed by `g` runs `g` from the state `f s`. -/
private theorem SM.modify_bind {f : SSt P → SSt P} {g : Unit → SM P α} :
    (modify f >>= g) s = g () (f s) := rfl

/-! ## Fresh names -/

include iLId iW in
/-- `sFresh x` returns `freshName (baseOf x) j` for a counter `j` at least the current one,
    outside the avoided names, and advances the counter past `j`. -/
theorem sFresh_ok (h : sFresh x s = .ok (y, s')) :
    ∃ j, s.next ≤ j ∧ y = freshName (baseOf x) j ∧ y ∉ s.avoid.toList ∧
      s' = { s with next := j + 1 } := by
  obtain ⟨k, hk, hle, hav⟩ := freshIn_spec s.avoid (baseOf x) s.next
  cases Nat.succ.inj (congrArg Prod.snd hk)
  cases h
  exact ⟨_, hle, rfl, by simpa [AvoidSet.contains, AvoidSet.toList] using hav, rfl⟩

/-- The state after `bind x v` and recording `v` as the value of `x` at its `init`. -/
@[expose] def SSt.defd (s : SSt P) (x : P.Ident) (v : SVal P) : SSt P := { s with
    ρ := s.ρ.insert x v
    trail := (x, s.ρ[x]?) :: s.trail
    trailLen := s.trailLen + 1
    defs := s.defs.insert x v }

/-- The state after `bind x v`. -/
@[expose] def SSt.bound (s : SSt P) (x : P.Ident) (v : SVal P) : SSt P := { s with
    ρ := s.ρ.insert x v
    trail := (x, s.ρ[x]?) :: s.trail
    trailLen := s.trailLen + 1 }

/-! ## The undo log

`undoTo.go k tr ρ` undoes the `k` newest bindings of the log `tr` in `ρ`.  It depends on `ρ`
only through its lookups, and undoing a concatenation undoes its parts in turn.  A run of the
traversal only extends the log, and undoing the extension gives back the lookups of the
mapping it started from (`SFrame`). -/

omit iHB iHF iSF iHI iHFs in
/-- Undoing the same log from two mappings with the same lookups gives the same log and two
    mappings with the same lookups. -/
private theorem undoGo_congr : ∀ (k : Nat) (tr : List (P.Ident × Option (SVal P)))
    {ρ1 ρ2 : Std.HashMap P.Ident (SVal P)}, (∀ x : P.Ident, ρ1[x]? = ρ2[x]?) →
    (undoTo.go k tr ρ1).1 = (undoTo.go k tr ρ2).1 ∧
      ∀ x : P.Ident, (undoTo.go k tr ρ1).2[x]? = (undoTo.go k tr ρ2).2[x]?
  | 0, _, _, _, h | _ + 1, [], _, _, h => ⟨rfl, h⟩
  | k + 1, (x, old) :: tr, _, _, h => undoGo_congr k tr fun y => by cases old <;> grind

omit iDE iLB iHB iHF iSF iHI iHFs in
/-- Undoing the `a.length + k` newest bindings of `a ++ b` undoes `a`, then `k` bindings
    of `b`. -/
private theorem undoGo_append : ∀ (a b : List (P.Ident × Option (SVal P)))
    (ρ : Std.HashMap P.Ident (SVal P)) (k : Nat),
    undoTo.go (a.length + k) (a ++ b) ρ = undoTo.go k b (undoTo.go a.length a ρ).2
  | [], _, _, _ => by simp [undoTo.go]
  | (x, old) :: a, b, ρ, k => by simpa [Nat.add_right_comm, undoTo.go] using undoGo_append a b _ k

/-- The traversal from `s` to `s'` keeps the avoided names, advances the counter, adds
    choice-record entries, and extends the undo log by bindings whose undoing gives back the
    lookups of `s`. -/
@[expose] def SFrame (s s' : SSt P) : Prop :=
  s'.avoid = s.avoid ∧ s.next ≤ s'.next ∧ (∃ l, s'.obls = l ++ s.obls) ∧
    ∃ ext, s'.trail = ext ++ s.trail ∧ s'.trailLen = s.trailLen + ext.length ∧
      ∀ x : P.Ident, (undoTo.go ext.length ext s'.ρ).2[x]? = s.ρ[x]?

/-- A state frames itself. -/
private theorem SFrame.refl (s : SSt P) : SFrame s s :=
  ⟨rfl, Nat.le_refl _, ⟨[], rfl⟩, [], rfl, rfl, fun _ => rfl⟩

/-- Frames compose. -/
private theorem SFrame.trans {s1 s2 s3 : SSt P} (h1 : SFrame s1 s2) (h2 : SFrame s2 s3) :
    SFrame s1 s3 := by
  obtain ⟨a1, n1, ⟨l1, o1⟩, e1, t1, k1, u1⟩ := h1
  obtain ⟨a2, n2, ⟨l2, o2⟩, e2, t2, k2, u2⟩ := h2
  refine ⟨a2.trans a1, Nat.le_trans n1 n2, ⟨l2 ++ l1, by simp [o2, o1]⟩, e2 ++ e1,
    by simp [t2, t1], by rw [k2, k1, List.length_append]; omega, fun x => ?_⟩
  rw [List.length_append, undoGo_append, (undoGo_congr _ _ u2).2, u1]

/-- Binding `x` frames the state. -/
private theorem SFrame.bound (s : SSt P) (x : P.Ident) (v : SVal P) : SFrame s (s.bound x v) :=
  ⟨rfl, Nat.le_refl _, ⟨[], rfl⟩, [_], rfl, rfl, fun y => by
    cases h : s.ρ[x]? <;> grind [undoTo.go, SSt.bound]⟩

/-- Advancing the counter, recording a definition or adding choice-record entries frames the
    state. -/
private theorem SFrame.of_eq (ha : s'.avoid = s.avoid) (hn : s.next ≤ s'.next)
    (ho : ∃ l, s'.obls = l ++ s.obls) (ht : s'.trail = s.trail) (hk : s'.trailLen = s.trailLen)
    (hρ : s'.ρ = s.ρ) : SFrame s s' := ⟨ha, hn, ho, [], ht, hk, fun _ => by rw [hρ]; rfl⟩

/-- Binding `x` and recording its value at its `init` frames the state. -/
private theorem SFrame.defd (s : SSt P) (x : P.Ident) (v : SVal P) : SFrame s (s.defd x v) :=
  SFrame.bound s x v
/-! ## Steps of the traversal -/

/-- `bind x v` maps `x` to `v` and logs the previous value of `x`. -/
private theorem bind_ok (h : bind x v s = .ok (u, s')) : s' = { s with
      ρ := s.ρ.insert x v
      trail := (x, s.ρ[x]?) :: s.trail
      trailLen := s.trailLen + 1 } := by cases h; rfl

/-- `undoTo mark` undoes the bindings logged after the log had length `mark`. -/
theorem undoTo_ok {mark : Nat} (h : undoTo mark s = .ok (u, s')) :
    s' = { s with
      ρ := (undoTo.go (s.trailLen - mark) s.trail s.ρ).2
      trail := (undoTo.go (s.trailLen - mark) s.trail s.ρ).1
      trailLen := mark } := by cases h; rfl
end

/-- `curTy x` keeps the state and returns the type of the current value of `x`. -/
theorem curTy_ok (h : curTy x s = .ok (ty, s')) :
    s' = s ∧ (s.ρ[x]?.getD (.name x none)).ty? = some ty := by
  cases hc : (s.ρ[x]?.getD (.name x none)).ty? <;> simp only [curTy, SM.get_bind, hc] at h <;>
    cases h
  exact ⟨rfl, rfl⟩

/-- The three outcomes of `assignVal x ty e`: the folded value `e'` is a literal (recorded and
    defined by a fresh Boolean `init`), a variable (recorded, no output, same state), or is
    defined by an `init` of a fresh name. -/
theorem assignVal_ok (h : assignVal x ty e s = .ok ((o, v), s')) :
    (∃ b x', WPOps.boolLit? (foldE s.ρ e) = some b ∧ sFresh x s = .ok (x', s') ∧
      o = [mkInit x' HasBool.boolTy (.det (if b then tt else ff))] ∧ v = .lit b (some x')) ∨
    (∃ y, HasFvar.getFvar (foldE s.ρ e) = some y ∧ o = [] ∧ v = .name y (some ty) ∧ s' = s) ∨
    (∃ x', sFresh x s = .ok (x', s') ∧ o = [mkInit x' ty (.det (foldE s.ρ e))] ∧
      v = .name x' (some ty)) := by
  simp only [assignVal, SM.get_bind] at h
  rcases hb : WPOps.boolLit? (foldE s.ρ e) <;> rcases hy : HasFvar.getFvar (foldE s.ρ e) <;>
    simp only [hb, hy, SM.bind_iff, SM.pure_iff] at h <;> grind

/-- Induction along a successful run of the traversal: a property of the input list, the start
    state, the output and the end state holds of every run when it holds of the run of the empty
    list and each kind of statement in front of a list preserves it, given the steps of the
    traversal and the runs of the sublists. -/
@[elab_as_elim]
theorem ssaList_ind {Q : PStmts P → SSt P → PStmts P → SSt P → Prop} (nil : ∀ s, Q [] s [] s)
    (initDet : ∀ {x ty e md rest s o v s1 out s'}, assignVal x ty e s = .ok ((o, v), s1) →
      Q rest (s1.defd x v) out s' →
      Q (.cmd (.cmd (.init x ty (.det e) md)) :: rest) s (o ++ out) s')
    (initNondet : ∀ {x ty md rest s x' s1 out s'}, sFresh x s = .ok (x', s1) →
      Q rest (s1.defd x (.name x' (some ty))) out s' →
      Q (.cmd (.cmd (.init x ty .nondet md)) :: rest) s (mkInit x' ty .nondet :: out) s')
    (setDet : ∀ {x e md rest s ty o v s1 out s'}, curTy x s = .ok (ty, s) →
      assignVal x ty e s = .ok ((o, v), s1) → Q rest (s1.bound x v) out s' →
      Q (.cmd (.cmd (.set x (.det e) md)) :: rest) s (o ++ out) s')
    (setNondet : ∀ {x md rest s ty x' s1 out s'}, curTy x s = .ok (ty, s) →
      sFresh x s = .ok (x', s1) → Q rest (s1.bound x (.name x' (some ty))) out s' →
      Q (.cmd (.cmd (.set x .nondet md)) :: rest) s (mkInit x' ty .nondet :: out) s')
    (assume : ∀ {l a md rest s out s'}, Q rest s out s' →
      Q (.cmd (.cmd (.assume l a md)) :: rest) s (if WPOps.boolLit? (foldE s.ρ a) == some true
        then out else .cmd (.cmd (.assume l (foldE s.ρ a) md)) :: out) s')
    (check : ∀ {mk : String → P.Expr → MetaData P → Cmd P} {l e md rest s out s'},
      (mk = .assert ∨ mk = .cover) →
      ssaList rest { s with obls := some (.obl l (oblSubS s.ρ e)) :: s.obls } = .ok (out, s') →
      Q rest { s with obls := some (.obl l (oblSubS s.ρ e)) :: s.obls } out s' →
      Q (.cmd (.cmd (mk l e md)) :: rest) s (.cmd (.cmd (mk l (renM' s.ρ e) md)) :: out) s')
    (ite : ∀ {tss ess md s t sT sU e out s'}, ssaList tss s = .ok (t, sT) → Q tss s t sT →
      undoTo s.trailLen sT = .ok ((), sU) → ssaList ess sU = .ok (e, s') → Q ess sU e s' →
      (t = [] → out = e) → (t ≠ [] → e = [] → out = t) →
      (t ≠ [] → e ≠ [] → out = [.ite .nondet t e md]) → Q [.ite .nondet tss ess md] s out s')
    (typeDecl : ∀ {tc md rest s out s'}, Q rest s out s' → Q (.typeDecl tc md :: rest) s out s')
    {ss : PStmts P} (h : ssaList ss s = .ok (out, s')) : Q ss s out s' := by
  induction ss using ssaList.induct generalizing s s' out
  all_goals simp only [ssaList, SM.bind_iff, SM.pure_iff, SM.get_bind, SM.modify_bind, WP.bind,
    pushObl] at h
  case case1 => exact h.1 ▸ h.2 ▸ nil s
  case case2 _ _ _ _ _ ih | case3 _ _ _ _ ih =>
    obtain ⟨p, s1, h1, r, _, hr, rfl, rfl⟩ := h
    first | exact initDet h1 (ih hr) | exact initNondet h1 (ih hr)
  case case4 _ _ _ _ ih | case5 _ _ _ ih =>
    obtain ⟨ty, s1, hT, p, s2, hA, r, _, hr, rfl, rfl⟩ := h
    obtain rfl := (curTy_ok hT).1
    first | exact setDet hT hA (ih hr) | exact setNondet hT hA (ih hr)
  case case6 _ l a md ih =>
    obtain ⟨r, _, hr, h⟩ := h
    split at h <;> rename_i hb <;> obtain ⟨rfl, rfl⟩ := SM.pure_iff.1 h <;>
      simpa [hb] using assume (l := l) (a := a) (md := md) (ih hr)
  case case7 _ _ _ _ ih | case8 _ _ _ _ ih =>
    obtain ⟨r, _, hr, rfl, rfl⟩ := h
    exact check (by simp) hr (ih hr)
  case case9 _ _ _ _ hr _ _ =>
    rw [ite_eq_left hr] at h
    nomatch h
  case case10 rest tss ess md hr ihT ihE =>
    obtain rfl : rest = [] := by simpa using hr
    simp only [ite_eq_right hr, SM.bind_iff, SM.get_bind] at h
    obtain ⟨t, sT, hT, _, sU, hU, e, _, hE, h⟩ := h
    rcases t with _ | ⟨a, t⟩ <;> rcases e with _ | ⟨b, e⟩ <;> cases h <;>
      exact ite hT (ihT hT) hU hE (ihE hE) (by simp) (by simp) (by simp)
  case case11 _ _ _ ih => exact typeDecl (ih h)
  all_goals nomatch h
omit iW in
/-- Recording a choice-record entry frames the state. -/
private theorem SFrame.push (s : SSt P) (o : Option (LogEntry P)) :
    SFrame s { s with obls := o :: s.obls } :=
  SFrame.of_eq rfl (Nat.le_refl _) ⟨[o], rfl⟩ rfl rfl rfl

include iLId in
/-- `sFresh` frames the state. -/
theorem sFresh_frame (h : sFresh x s = .ok (y, s')) : SFrame s s' := by
  obtain ⟨j, hj, -, -, rfl⟩ := sFresh_ok h
  exact SFrame.of_eq rfl (Nat.le_succ_of_le hj) ⟨[], rfl⟩ rfl rfl rfl

include iLId in
/-- `assignVal` frames the state. -/
theorem assignVal_frame (h : assignVal x ty e s = .ok ((o, v), s')) : SFrame s s' := by
  grind [SFrame.refl, assignVal_ok, sFresh_frame]

omit iW in
/-- Undoing, after a run from `s`, the bindings logged since `s` gives back the lookups, the
    log and its length of `s`. -/
theorem undoTo_frame {s sT sU : SSt P} {u : Unit} (hT : SFrame s sT)
    (h : undoTo s.trailLen sT = .ok (u, sU)) : SFrame s sU ∧ ∀ x : P.Ident, sU.ρ[x]? = s.ρ[x]? := by
  obtain ⟨ha, hn, ho, ext, ht, hk, hu⟩ := hT
  obtain rfl := undoTo_ok h
  rw [hk, ht, Nat.add_sub_cancel_left, ← Nat.add_zero ext.length, undoGo_append]
  exact ⟨⟨ha, hn, ho, [], rfl, rfl, hu⟩, hu⟩

include iLId in
/-- **The traversal frames the state** (`SFrame`): it keeps the avoided names, advances the
    counter, only adds choice-record entries, and only extends the undo log, by bindings whose
    undoing gives back the lookups it started from. -/
theorem ssaList_frame (ss : PStmts P) : ∀ {s s' : SSt P} {out : PStmts P},
    ssaList ss s = .ok (out, s') → SFrame s s' := fun h =>
  ssaList_ind SFrame.refl (fun h1 ih => (assignVal_frame h1).trans ((SFrame.defd _ _ _).trans ih))
    (fun h1 ih => (sFresh_frame h1).trans ((SFrame.defd _ _ _).trans ih))
    (fun _ h1 ih => (assignVal_frame h1).trans ((SFrame.bound _ _ _).trans ih))
    (fun _ h1 ih => (sFresh_frame h1).trans ((SFrame.bound _ _ _).trans ih)) id
    (fun _ _ ih => (SFrame.push _ _).trans ih)
    (fun _ hT hU _ hE _ _ _ => (undoTo_frame hT hU).1.trans hE) id h

/-- The entry mapping of the SSA phase: each name the entry renaming `ρ0` renames to its entry
    name, typed by `tys`. -/
@[expose] def entryMap (tys : Tys P) (ρ0 : Ren P) : Std.HashMap P.Ident (SVal P) :=
  ρ0.foldr (fun p ρ => ρ.insert p.1 (SVal.name p.2 (tys.get? p.1))) ∅

/-- The SSA phase is the traversal of the guarded program from the entry mapping. -/
theorem ssaBody_ok {st : FreshSt P} (h : ssaBody st ρ0 lay = .ok so) :
    ∃ s1, ssaList lay ⟨st.next, st.avoid, entryMap st.tys ρ0, [], 0, {}, []⟩ = .ok (so.out, s1) ∧
      so.obls = s1.obls.reverse := by
  obtain ⟨⟨out, s1⟩, hr, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact ⟨s1, hr, rfl⟩

/-- The traversal of a list of obligations is a list of obligations. -/
private theorem ssaList_obls (ss : PStmts P) : ∀ {s s' : SSt P} {out : PStmts P},
    ssaList ss s = .ok (out, s') → ss.all Stmt.isCheck = true → out.all Stmt.isCheck = true := by
  intro s s' out h
  refine ssaList_ind (fun _ _ => rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;> intros <;>
    (try rcases ‹_ ∨ _› with rfl | rfl) <;> grind [Stmt.isCheck]

/-- A straight-line statement of the flat translation: an `init` or an `assume`. -/
private def Stmt.IsLetOrAssume : Stmt P (CmdExt P) → Prop
  | .cmd (.cmd (.init _ _ _ _)) | .cmd (.cmd (.assume _ _ _)) => True
  | _ => False

omit iDE iBE iHB iHF iSF iHI iHa iHFs in
/-- An `init` or an `assume` in front of a list in tree form, with only `assert`s and `cover`s
    after every `assert`, only `init`, `assume`, `assert`, `cover` and `ite *`, and no loop, keeps
    these facts. -/
private theorem shape_cons {c : PStmt P} (hc : Stmt.IsLetOrAssume c)
    (h : Block.treeForm out = true ∧ Block.onlyChecksAfterAssert out = true ∧
      Block.passiveForm out = true ∧ Block.noLoops out = true) :
    Block.treeForm (c :: out) = true ∧ Block.onlyChecksAfterAssert (c :: out) = true ∧
      Block.passiveForm (c :: out) = true ∧ Block.noLoops (c :: out) = true := match c, hc with
  | .cmd (.cmd (.init ..)), _ | .cmd (.cmd (.assume ..)), _ => by
    simpa [Block.treeForm, Block.passiveForm, Block.onlyChecksAfterAssert, Block.noLoops_cons,
      Stmt.noLoops_cmd] using h

/-- The shape of the traversal's output on a list in tree form with only `assert`s and `cover`s
    after every `assert`: in tree form, with only `assert`s and `cover`s after every `assert`,
    with only `init`, `assume`, `assert`, `cover` and `ite *`, and without loops. -/
private theorem ssaList_shape (ss : PStmts P) : ∀ {s s' : SSt P} {out : PStmts P},
    ssaList ss s = .ok (out, s') → Block.treeForm ss = true →
    Block.onlyChecksAfterAssert ss = true → Block.treeForm out = true ∧
      Block.onlyChecksAfterAssert out = true ∧ Block.passiveForm out = true ∧
      Block.noLoops out = true := by
  intro s s' out h
  refine ssaList_ind (fun _ _ _ => by
      simp [Block.treeForm, Block.passiveForm, Block.onlyChecksAfterAssert, Block.noLoops_nil])
    (fun hA ih hg ho => ?_) (fun _ ih hg ho => ?_) (fun _ hA ih hg ho => ?_)
    (fun _ _ ih hg ho => ?_) (fun ih hg ho => ?_) (fun hmk hr ih hg ho => ?_)
    (fun {_ _ _ _ t _ _ e _ _} _ ihT _ _ ihE h1 h2 h3 hg ho => ?_)
    (fun _ hg => by simp [Block.treeForm] at hg) h
  case refine_6 =>
    rcases hmk with rfl | rfl <;>
      simp only [Block.treeForm, Block.onlyChecksAfterAssert, Block.passiveForm, Block.noLoops_cons,
        Stmt.noLoops_cmd, Bool.true_and] at hg ho ⊢
    · have h := ih hg (Block.onlyChecksAfterAssert_of_all_isCheck ho)
      exact ⟨h.1, ssaList_obls _ hr ho, h.2.2⟩
    · exact ih hg ho
  case refine_7 =>
    simp only [Block.treeForm, Block.onlyChecksAfterAssert, List.isEmpty_nil, Bool.true_and,
      Bool.and_true, Bool.and_eq_true] at hg ho
    have hT := ihT hg.1 ho.1
    have hE := ihE hg.2 ho.2
    by_cases ht : t = [] <;> by_cases he : e = [] <;>
      simp_all [Block.treeForm, Block.passiveForm, Block.onlyChecksAfterAssert, Block.noLoops_cons,
        Stmt.noLoops_ite, Block.noLoops_nil]
  all_goals simp only [Block.treeForm, Block.onlyChecksAfterAssert] at hg ho
  case' refine_1 | refine_3 =>
    rcases assignVal_ok hA with ⟨_, _, -, -, rfl, -⟩ | ⟨_, -, rfl, -⟩ | ⟨_, -, rfl, -⟩
  case' refine_5 => split
  all_goals first | exact ih hg ho | exact shape_cons trivial (ih hg ho)

/-! ## Folding -/

/-! ## Well-scopedness -/

/-- The names the current value `o` of `x` reads are in `Dd`: its variable, the name defined for
    its literal, or `x` itself when unmapped. -/
@[expose] def SNames (Dd : List P.Ident) (x : P.Ident) : Option (SVal P) → Prop
  | some (.name y _) => y ∈ Dd
  | some (.lit _ m) => ∃ y, m = some y ∧ y ∈ Dd
  | none => x ∈ Dd

omit iDE iBE iHB iHF iSF iHI iHa iHFs in
/-- `SNames` survives adding names. -/
private theorem SNames.mono (hs : Dd ⊆ Dd') :
    ∀ {o : Option (SVal P)}, SNames Dd x o → SNames Dd' x o := fun {o} h => by
  rcases o with _ | (_ | _) <;> grind [SNames]

omit iBE iLB iHI iHa in
/-- The free variables of `e` under the substitution `g` are in `Dd` when, for every free
    variable `x` of `e`, the free variables of its image are in `Dd`, or `x` is when `g` leaves
    it unsubstituted. -/
private theorem substFn_fv {Dd : List P.Ident} {e : P.Expr} {g : P.Ident → Option P.Expr}
    (hA : ∀ x ∈ HasFvars.getFvars e, ∀ y ∈ ((g x).map HasFvars.getFvars).getD [x], y ∈ Dd) :
    ∀ y ∈ HasFvars.getFvars (WPOps.substFn e g), y ∈ Dd := by
  intro y hy
  rw [WPLang.substFn_eq e g _ fun x hx => (Map.find?_filterMap_self g _ x hx).symm] at hy
  rcases WPLang.getFvars_substFvars _ _ _ hy with ⟨h1, h2⟩ | ⟨x, v, h1, h2, h3⟩
  · exact hA y h1 y (by simp_all [Map.find?_filterMap_self])
  · exact hA x h1 y (by simp_all [Map.find?_filterMap_self])
include iLFvs in
omit iLB iHI in
/-- The free variables of `e` with every name replaced by its current value are names its free
    variables read. -/
private theorem renM_fv (e : P.Expr) (hA : ∀ x ∈ HasFvars.getFvars e, SNames Dd x ρ[x]?) :
    ∀ y ∈ HasFvars.getFvars (renM ρ e), y ∈ Dd := substFn_fv fun x hx y hy => by
  have h := hA x hx
  rcases hρ : ρ[x]? with _ | ⟨z, ty⟩ | ⟨_ | _, m⟩ <;>
    grind [SNames, SVal.expr, HasFvar.eq_of_mem_getFvars_mkVar, WPLang.getFvars_tt,
      WPLang.getFvars_ff]

include iLFvs in
omit iLB iHI in
/-- The free variables of the folded `e` are names the free variables of `e` read. -/
private theorem foldE_fv (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    (∀ x ∈ HasFvars.getFvars e, SNames Dd x ρ[x]?) →
      ∀ y ∈ HasFvars.getFvars (foldE ρ e), y ∈ Dd := by
  fun_induction foldE ρ e <;> intro hA y hy <;> (try obtain rfl := WPLang.iteView?_eq ‹_›) <;>
    grind [WPLang.getFvars_ite, renM_fv]

omit iHB iHF iSF iHI iHFs in
/-- The entry mapping maps each name the entry renaming renames to its entry name, typed by
    `tys`, and no other name. -/
theorem entryMap_lookup (tys : Tys P) (ρ0 : Ren P) (x : P.Ident) :
    (entryMap tys ρ0)[x]? = (ρ0.find? (·.1 == x)).map fun p => SVal.name p.2 (tys.get? x) := by
  induction ρ0 <;> grind [entryMap]

include iLFvs in
omit iHI in
/-- The free variables of an emitted obligation condition are names the free variables of the
    condition read. -/
private theorem renM'_fv (e : P.Expr) (hA : ∀ x ∈ HasFvars.getFvars e, SNames Dd x ρ[x]?) :
    ∀ y ∈ HasFvars.getFvars (renM' ρ e), y ∈ Dd := substFn_fv fun x hx y hy => by
  have h := hA x hx
  rcases hρ : ρ[x]? with _ | ⟨z, ty⟩ | ⟨b, _ | m⟩ <;>
    grind [SNames, oblVar, HasFvar.eq_of_mem_getFvars_mkVar]

omit iHB iHF iSF iHI iHFs in
/-- `SNames` after binding `x`: on `x` from the new value, on the other names of `V` from
    before. -/
private theorem SNames.assign {V : List P.Ident} (hs : Dd ⊆ Dd') (hx : SNames Dd' x (some v))
    (hold : ∀ y ∈ V, y ≠ x → SNames Dd y ρ[y]?) : ∀ y ∈ V, SNames Dd' y (ρ.insert x v)[y]? :=
  fun y hy => by by_cases h : x = y <;> grind [SNames.mono hs]

include iLId iLFvs in
/-- The well-scopedness of the traversal's output: from names `Dd` its fresh names avoid, when
    the current values of the free variables of the list read only names of `Dd`. -/
private theorem ssaList_wellScoped (ss : PStmts P) : ∀ {s s' : SSt P} {out : PStmts P},
    ssaList ss s = .ok (out, s') → ∀ {Dd : List P.Ident}, NamesOK s.avoid.toList Dd s.next →
    (∀ x ∈ Block.freeVars ss, SNames Dd x s.ρ[x]?) → Block.readsDefined Dd out = true := by
  intro s s' out h
  refine no_implicit_lambda% (ssaList_ind (fun _ _ _ _ => by simp [Block.readsDefined])
    ?initDet ?initNondet ?setDet ?setNondet ?_ ?_ ?_ ?_ h)
  case' initDet => intro x _ e _ rest s _ _ _ _ _ h1 ih Dd hN hA
  case' setDet => intro x e _ rest s _ _ _ _ _ _ _ h1 ih Dd hN hA
  case initDet | setDet =>
    have hfe : ∀ y ∈ HasFvars.getFvars e, SNames Dd y s.ρ[y]? := fun y hy =>
      hA y (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy])
    have hold : ∀ y ∈ Block.freeVars rest, y ≠ x → SNames Dd y s.ρ[y]? := fun y hy hne =>
      hA y (by simp [Block.freeVars, Stmt.freeVars, hy, hne])
    rcases assignVal_ok h1 with ⟨b, _, -, hf, rfl, rfl⟩ | ⟨y, hy, rfl, rfl, rfl⟩ | ⟨_, hf, rfl, rfl⟩
    case inr.inl => exact ih hN (SNames.assign (List.Subset.refl _)
      (foldE_fv _ e hfe y (WPLang.getFvar_getFvars hy)) hold)
    all_goals
      obtain ⟨j, hj, rfl, hy, rfl⟩ := sFresh_ok hf
      have hr := ih (hN.add_fresh _ hj) (SNames.assign (List.subset_cons_self _ _)
        (by first | exact .head _ | exact ⟨_, rfl, .head _⟩) hold)
      (try cases b) <;> simp +contextual [Block.readsDefined, mkInit, hN.fresh_not_mem hj hy, hr,
        WPLang.getFvars_tt, WPLang.getFvars_ff, foldE_fv _ e hfe]
  case' initNondet => intro x _ _ rest s _ _ _ _ h1 ih Dd hN hA
  case' setNondet => intro x _ rest s _ _ _ _ _ _ h1 ih Dd hN hA
  case initNondet | setNondet =>
    obtain ⟨j, hj, rfl, hy, rfl⟩ := sFresh_ok h1
    have hr := ih (hN.add_fresh _ hj) (SNames.assign (List.subset_cons_self _ _) (.head _)
      fun z hz hne => hA z (by simp [Block.freeVars, Stmt.freeVars, hz, hne]))
    simp [Block.readsDefined, mkInit, hN.fresh_not_mem hj hy, hr]
  · intro l a md rest s out s' ih Dd hN hA
    have hr := ih hN fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    have hf := foldE_fv s.ρ a fun y hy =>
      hA y (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy])
    split <;> simp_all [Block.readsDefined]
  · intro mk l e md rest s out s' hmk _ ih Dd hN hA
    rcases hmk with rfl | rfl <;>
      simp +contextual [Block.readsDefined,
        ih hN fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy]),
        renM'_fv e fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, mem_exprFV, hy])]
  · intro tss ess md s t sT sU e out s' hT ihT hU _ ihE h1 h2 h3 Dd hN hA
    obtain ⟨⟨ha, hn, -⟩, hρ⟩ := undoTo_frame (ssaList_frame _ hT) hU
    have rT := ihT hN fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    have rE := ihE (fun y hy b j hj he => ha ▸ hN y hy b j (Nat.le_trans hn hj) he) fun y hy =>
      hρ y ▸ hA y (by simp [Block.freeVars, Stmt.freeVars, hy])
    rcases t with _ | ⟨a, t⟩ <;> rcases e with _ | ⟨b, e⟩ <;> simp_all [Block.readsDefined]
  · intro tc md rest s out s' ih Dd hN hA
    exact ih hN fun y hy => hA y (by simp [Block.freeVars, Stmt.freeVars, hy])

/-! ## The entry renaming -/

omit iDE iHB iHF iSF iHI iHa iHFs in
/-- The current name of a renamed name is the target of one of its pairs. -/
theorem Ren.get_mem {ρ : Ren P} (hx : x ∈ ρ.map (·.1)) : ∃ q ∈ ρ, ρ.get x = q.2 := by
  grind [Ren.get, List.find?_eq_none, List.mem_of_find?_eq_some]

/-- Renaming each name of `l` to a fresh name (`f`, from the counter `n`, outside `A`) gives
    targets that are fresh names with counters from `m` below the final counter, outside `A`,
    when the pairs of `ρ` have such targets; the counter does not decrease; the keys are those of
    `ρ` and the names of `l`. -/
private theorem entryFresh_spec (A : AvoidSet P) (m : Nat) (f : Ren P × Nat → P.Ident → Ren P × Nat)
    (hf : ∀ ρ n x, ∃ k, n ≤ k ∧ f (ρ, n) x = (Ren.set ρ x (freshName (WPOps.name x) k), k + 1) ∧
      freshName (P := P) (WPOps.name x) k ∉ A.toList) :
    ∀ (l : List P.Ident) (ρ : Ren P) (n : Nat), m ≤ n →
      (∀ q ∈ ρ, ∃ b j, m ≤ j ∧ j < n ∧ q.2 = freshName b j ∧ q.2 ∉ A.toList) →
      n ≤ (l.foldl f (ρ, n)).2 ∧
      (∀ q ∈ (l.foldl f (ρ, n)).1,
        (∃ b j, m ≤ j ∧ j < (l.foldl f (ρ, n)).2 ∧ q.2 = freshName b j ∧ q.2 ∉ A.toList) ∧
          (q.1 ∈ l ∨ q.1 ∈ ρ.map (·.1))) ∧
      ∀ x, x ∈ l ∨ x ∈ ρ.map (·.1) → x ∈ (l.foldl f (ρ, n)).1.map (·.1)
  | [], ρ, n, _, hρ => ⟨Nat.le_refl _, fun q hq => ⟨hρ q hq, .inr (List.mem_map_of_mem hq)⟩,
      fun _ hx => hx.resolve_left nofun⟩
  | z :: l, ρ, n, hm, hρ => by
    obtain ⟨j, hj, he, hA⟩ := hf ρ n z
    simp only [List.foldl_cons, he]
    obtain ⟨h1, h2, h3⟩ := entryFresh_spec A m f hf l
      (Ren.set ρ z (freshName (WPOps.name z) j)) (j + 1) (by omega) (by grind [Ren.set])
    refine ⟨by omega, fun q hq => ⟨(h2 q hq).1, ?_⟩, fun x hx => h3 x ?_⟩ <;> grind [Ren.set]

omit iDE iHB iHF iSF iHI iHa iHFs in
/-- Renaming each `a` of `al` to the current name of its `x`, renamed by `ρ`, keeps every target
    a target of `ρ`; the keys are those of `ρ` and the names `a`. -/
private theorem entryAlias_spec (Q : P.Ident → Prop) :
    ∀ (al : List (P.Ident × P.Ident)) (ρ : Ren P), (∀ q ∈ al, q.2 ∈ ρ.map (·.1)) →
      (∀ q ∈ ρ, Q q.2) →
      (∀ q ∈ al.foldl (fun (ρ : Ren P) (q : P.Ident × P.Ident) => Ren.set ρ q.1 (Ren.get ρ q.2)) ρ,
        Q q.2 ∧ (q.1 ∈ al.map (·.1) ∨ q.1 ∈ ρ.map (·.1))) ∧
      ∀ x, x ∈ al.map (·.1) ∨ x ∈ ρ.map (·.1) → x ∈ (al.foldl
        (fun (ρ : Ren P) (q : P.Ident × P.Ident) => Ren.set ρ q.1 (Ren.get ρ q.2)) ρ).map (·.1)
  | [], ρ, _, hρ => ⟨fun q hq => ⟨hρ q hq, .inr (List.mem_map_of_mem hq)⟩,
      fun _ hx => hx.resolve_left nofun⟩
  | (a, x) :: al, ρ, hal, hρ => by
    obtain ⟨q0, hq0, hg⟩ := Ren.get_mem (hal (a, x) List.mem_cons_self)
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := entryAlias_spec Q al (Ren.set ρ a (Ren.get ρ x))
      (by grind [Ren.set]) (by grind [Ren.set])
    refine ⟨fun q hq => ⟨(h1 q hq).1, ?_⟩, fun y hy => h2 y ?_⟩ <;> grind [Ren.set]

include iLId in
/-- **The entry renaming.**  When every `(a, x)` of `al` has `x` in `xs`, `ssaEntryRen A xs al n`
    does not decrease the counter, every target is a fresh name `freshName b j` with `n ≤ j`
    below the final counter, outside `A`, and its keys are exactly the names of `xs` and the
    names `a` of `al`. -/
theorem ssaEntryRen_spec (A : AvoidSet P) (xs : List P.Ident) (al : List (P.Ident × P.Ident))
    (n : Nat) (hal : ∀ q ∈ al, q.2 ∈ xs) :
    n ≤ (ssaEntryRen A xs al n).2 ∧
      (∀ q ∈ (ssaEntryRen A xs al n).1,
        (∃ b j, n ≤ j ∧ j < (ssaEntryRen A xs al n).2 ∧ q.2 = freshName b j ∧
          q.2 ∉ A.toList) ∧ (q.1 ∈ xs ∨ q.1 ∈ al.map (·.1))) ∧
      ∀ x, x ∈ xs ∨ x ∈ al.map (·.1) → x ∈ (ssaEntryRen A xs al n).1.map (·.1) := by
  unfold ssaEntryRen
  obtain ⟨h1, h2, h3⟩ := entryFresh_spec A n (fun (r : Ren P × Nat) x =>
      let f := freshIn A (WPOps.name x) r.2
      (Ren.set r.1 x f.1, f.2)) (fun ρ n x =>
        (freshIn_spec A (WPOps.name x) n).imp fun _ ⟨hk, hle, hav⟩ => ⟨hle, by rw [hk],
          by simpa [AvoidSet.contains, AvoidSet.toList] using hav⟩)
    xs [] n (Nat.le_refl _) nofun
  obtain ⟨h4, h5⟩ := entryAlias_spec (fun y => ∃ b j, n ≤ j ∧ j < _ ∧ y = freshName b j ∧
      y ∉ A.toList) al _ (fun q hq => h3 _ (.inl (hal q hq))) fun q hq => (h2 q hq).1
  refine ⟨h1, fun q hq => ⟨(h4 q hq).1, ?_⟩, fun x hx => h5 x ?_⟩ <;> grind

include iLId in
/-- Every name of `D` of the form of a fresh name the traversal may introduce after the entry
    renaming is avoided, when each name of `D` is an entry name or not of the form of a fresh
    name. -/
theorem ssaEntryRen_namesOK (A : AvoidSet P) (xs : List P.Ident) (al : List (P.Ident × P.Ident))
    (hal : ∀ q ∈ al, q.2 ∈ xs) {D : List P.Ident}
    (hD : ∀ y ∈ D, y ∈ (ssaEntryRen A xs al 0).1.map (·.2) ∨ ∀ b j, y ≠ freshName b j) :
    NamesOK A.toList D (ssaEntryRen A xs al 0).2 := fun y hy b j hj he => by
  rcases hD y hy with hy | hy
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    obtain ⟨⟨b', j', -, hj', hb, -⟩, -⟩ := (ssaEntryRen_spec A xs al 0 hal).2.1 q hq
    exact absurd (freshName_counter_inj (hb.symm.trans he)) (by omega)
  · exact absurd he (hy b j)

/-- A successful run of `ssaEntry` is `ssaBody` from the entry renaming and the counter after
    it, avoiding `inputAvoid G tys lay`. -/
theorem ssaEntry_ok {G : IdSet P} {tys : Tys P} {xs : List P.Ident} {al : List (P.Ident × P.Ident)}
    (h : ssaEntry G tys xs al lay = .ok (ρ0, so)) :
    ρ0 = (ssaEntryRen (inputAvoid G tys lay) xs al 0).1 ∧
      ssaBody ⟨(ssaEntryRen (inputAvoid G tys lay) xs al 0).2, inputAvoid G tys lay, tys⟩ ρ0 lay =
        .ok so := by
  obtain ⟨so', hb, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact ⟨rfl, hb⟩

/-- **Shape of the SSA output.**  On a guarded program in tree form with only `assert`s and
    `cover`s after every `assert`, the output of the SSA phase is in tree form (`Block.treeForm`:
    every `ite *` last in its list, no loop), has only `assert`s and `cover`s after every `assert`
    (`Block.onlyChecksAfterAssert`), has only `init`, `assume`, `assert`, `cover` and `ite *`
    (`Block.passiveForm`), and has no loop at any depth (`Block.noLoops`). -/
theorem ssaBody_shape {st : FreshSt P} {ρ0 : Ren P} {lay : PStmts P} {so : SOut P}
    (hg : Block.treeForm lay = true) (ho : Block.onlyChecksAfterAssert lay = true)
    (h : ssaBody st ρ0 lay = .ok so) :
    Block.treeForm so.out = true ∧ Block.onlyChecksAfterAssert so.out = true ∧
      Block.passiveForm so.out = true ∧ Block.noLoops so.out = true :=
  (ssaBody_ok h).elim fun _ ⟨h1, _⟩ => ssaList_shape lay h1 hg ho

include iLId iLFvs in
/-- **Well-scopedness of the SSA output.**  On a guarded program whose free variables are names of
    `xs` or of the aliases `al` (each `(a, x)` with `x` in `xs`), the output of `ssaEntry` is
    syntactically well scoped from the entry names. -/
theorem ssaEntry_wellScoped {G : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P} {so : SOut P}
    (h : ssaEntry G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (hfv : ∀ x ∈ Block.freeVars lay, x ∈ xs ∨ x ∈ al.map (·.1)) :
    Block.readsDefined (ρ0.map (·.2)) so.out = true := by
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  refine ssaList_wellScoped _ h1 (ssaEntryRen_namesOK _ _ _ hal fun y hy => .inl hy) fun x hx => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ((ssaEntryRen_spec _ xs al 0 hal).2.2 x (hfv x hx))
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
    ((List.find?_isSome (p := (·.1 == q.1))).2 ⟨q, hq, beq_self_eq_true _⟩)
  rw [entryMap_lookup, hp]
  exact List.mem_map_of_mem (List.mem_of_find?_eq_some hp)


/-! ## Facts for the initial-environment gate -/

include iLId in
/-- The outcomes of `assignVal x ty e`: the state keeps its mapping and does not decrease its
    counter; the value has the Boolean type or `ty`; the output is empty or the `init` of a fresh
    name with the base of `x` and a counter at least the current one, of the Boolean type or
    `ty`, with a Boolean literal or the folded `e` as value. -/
theorem assignVal_facts (h : assignVal x ty e s = .ok ((o, v), s')) :
    s'.ρ = s.ρ ∧ s.next ≤ s'.next ∧ (v.ty? = some HasBool.boolTy ∨ v.ty? = some ty) ∧
    (o = [] ∨ ∃ j ty' e', s.next ≤ j ∧ (ty' = HasBool.boolTy ∨ ty' = ty) ∧
      (e' = tt ∨ e' = ff ∨ e' = foldE s.ρ e) ∧
        o = [mkInit (freshName (baseOf x) j) ty' (.det e')]) := by
  rcases assignVal_ok h with ⟨b, _, -, hf, rfl, rfl⟩ | ⟨y, -, rfl, rfl, rfl⟩ | ⟨_, hf, rfl, rfl⟩
  · obtain ⟨j, hj, rfl, -, rfl⟩ := sFresh_ok hf
    exact ⟨rfl, Nat.le_succ_of_le hj, .inl rfl, .inr ⟨j, _, _, hj, .inl rfl,
      by cases b <;> simp, rfl⟩⟩
  · exact ⟨rfl, Nat.le_refl _, .inr rfl, .inl rfl⟩
  · obtain ⟨j, hj, rfl, -, rfl⟩ := sFresh_ok hf
    exact ⟨rfl, Nat.le_succ_of_le hj, .inr rfl, .inr ⟨j, ty, _, hj, .inr rfl, .inr (.inr rfl), rfl⟩⟩

include iLId iLFvs in
/-- On a guarded program whose free variables are names of `xs` or of the aliases `al` (each
    `(a, x)` with `x` in `xs`), the output of `ssaEntry` is syntactically well scoped from the
    entry names of the free variables. -/
theorem ssaEntry_wellScopedFV {G : IdSet P} {tys : Tys P} {xs : List P.Ident}
    {al : List (P.Ident × P.Ident)} {lay : PStmts P} {ρ0 : Ren P} {so : SOut P}
    (h : ssaEntry G tys xs al lay = .ok (ρ0, so)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (hfv : ∀ x ∈ Block.freeVars lay, x ∈ xs ∨ x ∈ al.map (·.1)) :
    Block.readsDefined ((Block.freeVars lay).map ρ0.get) so.out = true := by
  obtain ⟨rfl, hb⟩ := ssaEntry_ok h
  obtain ⟨s1, h1, -⟩ := ssaBody_ok hb
  have hk := (ssaEntryRen_spec (inputAvoid G tys lay) xs al 0 hal).2.2
  refine ssaList_wellScoped _ h1 (ssaEntryRen_namesOK _ _ _ hal fun y hy => .inl ?_) fun x hx => ?_
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨q, hq, he⟩ := Ren.get_mem (hk x (hfv x hx))
    exact he ▸ List.mem_map_of_mem hq
  · obtain ⟨q, hq, hqx⟩ := List.mem_map.1 (hk x (hfv x hx))
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
      ((List.find?_isSome (p := (·.1 == x))).2 ⟨q, hq, by simp [hqx]⟩)
    rw [entryMap_lookup, hp]
    exact List.mem_map.2 ⟨x, hx, by simp [Ren.get, hp]⟩

include iLId in
/-- When every `(a, x)` of `al` has `x` in `xs`, every target of the entry renaming
    `ssaEntryRen A xs al n` is a fresh name whose base is the name of a name of `xs`. -/
theorem ssaEntryRen_base (A : AvoidSet P) (xs : List P.Ident) (al : List (P.Ident × P.Ident))
    (n : Nat) (hal : ∀ q ∈ al, q.2 ∈ xs) :
    ∀ q ∈ (ssaEntryRen A xs al n).1, ∃ w ∈ xs, ∃ k, q.2 = freshName (WPOps.name w) k := by
  let f := fun (r : Ren P × Nat) x =>
    let f := freshIn A (WPOps.name x) r.2
    (Ren.set r.1 x f.1, f.2)
  have hf (l : List P.Ident) (hl : l ⊆ xs) : ∀ r : Ren P × Nat,
      (∀ q ∈ r.1, ∃ w ∈ xs, ∃ k, q.2 = freshName (WPOps.name w) k) →
      ∀ q ∈ (l.foldl f r).1, ∃ w ∈ xs, ∃ k, q.2 = freshName (WPOps.name w) k := by
    induction l with
    | nil => exact fun _ hr => hr
    | cons z l ih =>
      intro r hr
      obtain ⟨k, hk, -⟩ := freshIn_spec A (WPOps.name z) r.2
      refine ih (fun y hy => hl (.tail _ hy)) _ fun q hq => ?_
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨z, hl (.head _), k, by simp [hk]⟩
      · exact hr q hq
  obtain ⟨-, -, h3⟩ := entryFresh_spec A n f (fun ρ n x =>
      (freshIn_spec A (WPOps.name x) n).imp fun _ ⟨hk, hle, hav⟩ => ⟨hle, by simp [f, hk],
        by simpa [AvoidSet.contains, AvoidSet.toList] using hav⟩)
    xs [] n (Nat.le_refl _) nofun
  exact fun q hq => ((entryAlias_spec (fun y => ∃ w ∈ xs, ∃ k, y = freshName (WPOps.name w) k)
    al _ (fun q hq => h3 _ (.inl (hal q hq))) (hf xs (List.Subset.refl _) ([], n) nofun)).1 q hq).1

omit iHF iSF iHI iHFs in
/-- The current value the entry mapping gives a name the entry renaming renames has the type
    `tys` records for that name. -/
theorem entryMap_ty (tys : Tys P) (ρ0 : Ren P) (x : P.Ident) (hx : x ∈ ρ0.map (·.1)) :
    ((entryMap tys ρ0)[x]?.getD (.name x none)).ty? = tys.get? x := by
  obtain ⟨q, hq, hqx⟩ := List.mem_map.1 hx
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1
    ((List.find?_isSome (p := (·.1 == x))).2 ⟨q, hq, by simp [hqx]⟩)
  rw [entryMap_lookup, hp]
  rfl

end -- public section

end WP
end Imperative

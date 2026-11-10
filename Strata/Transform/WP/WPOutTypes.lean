/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverFacts
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEffects
import Strata.Util.ExceptProps

/-! # The types the guarded program declares

The emitted guarded program declares the types of the `init` items of the WP walk: a known
type, or the type of a name resolved at emission (`emit_tys`). A WP walk declares as known
types only declared types of the walked fragment and the Boolean type, records as declared
types only those and the initial ones, and refers to the type of a name, directly or through a
type reference of a fresh name, only for names that are no variable of the initial types or
that the fragment reads or writes (`TyInv`, `TyOut`, `wpList_tySpec`). Hence every type the output
of `wpEntry` declares is a declared type of the input, the Boolean type, or the type in `tys` of
a variable the input reads or writes (`wpEntry_initTypes`).

Key definitions: `wTyRefs`, `itemTys`, `RefOK`, `TyInv`, `TyOut`, `TySpec`.

Key theorems: `emit_tys`, `wpList_tySpec`, `wpEntry_initTypes`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iHS : HasSubstFvar P] [iHI : HasIdent P]
  [iL : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHV : HasFvars P] [iW : WPOps P]

/-! ## Types of items -/

/-- The type references of the `init` items of a list of guarded items, at any depth. -/
@[expose] def wTyRefs : List (WItem P) → List (TyRef P)
  | [] => []
  | .init _ ty _ :: rest => ty :: wTyRefs rest
  | .branch t e :: rest => wTyRefs t ++ wTyRefs e ++ wTyRefs rest
  | _ :: rest => wTyRefs rest

/-- The declared types of the statements of a list of flat items, at any depth. -/
@[expose] def itemTys : List (Item P) → List P.Ty
  | [] => []
  | .plain s :: rest => Stmt.initTypes s ++ itemTys rest
  | .obls _ cs :: rest => Block.initTypes cs ++ itemTys rest
  | .branch t e :: rest => itemTys t ++ itemTys e ++ itemTys rest

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- The type references of a concatenation are those of its parts. -/
theorem wTyRefs_append : ∀ (a b : List (WItem P)), wTyRefs (a ++ b) = wTyRefs a ++ wTyRefs b
  | [], _ => by simp [wTyRefs]
  | .init _ _ _ :: a, b | .set _ _ :: a, b | .assume _ _ _ :: a, b | .obls _ _ :: a, b => by
    simp [wTyRefs, wTyRefs_append a b]
  | .branch _ _ :: a, b => by simp [wTyRefs, wTyRefs_append a b]

omit iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- Merging adjacent obligation runs keeps the declared types of the items. -/
theorem mergeObls_tys : ∀ (l : List (Item P)), ∀ ty ∈ itemTys (mergeObls l), ty ∈ itemTys l :=
  fun l => by
  fun_induction mergeObls l with
  | case2 cs rest r cs' rest' hm ih =>
    simp only [hm, itemTys] at ih
    grind [itemTys, Block.initTypes_append]
  | _ => (try cases ‹Item P›) <;> grind [itemTys]

omit iDE iBE iLB iHS iHI iL iHa iHV in
/-- Every declared type of the nesting of flat items is one of the items. -/
theorem nest_tys : ∀ (l : List (Item P)), ∀ ty ∈ Block.initTypes (nest l), ty ∈ itemTys l
  | [], ty, h => by simp [nest, Block.initTypes] at h
  | .plain _ :: rest, ty, h | .obls _ _ :: rest, ty, h => by
    have hr : ∀ r : Option (RE P), Block.initTypes (reachPre r) = [] := by
      rintro (_ | (_ | _ | _ | _)) <;> rfl
    simp only [nest, nestCons] at h
    split at h <;> grind [itemTys, nest_tys rest ty, Block.initTypes, Stmt.initTypes,
      Block.initTypes_append]
  | .branch t e :: rest, ty, h => by
    simp only [nest, nestCons] at h
    split at h <;> grind [itemTys, nest_tys t ty, nest_tys e ty, Block.initTypes, Stmt.initTypes]
  termination_by l => sizeOf l

/-- A resolved type reference: a known type, or the type `tyOfName` gives the name. -/
@[expose] def RefTy (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (ty : P.Ty) :
    TyRef P → Prop
  | .known ty' => ty' = ty
  | .of y => tyOfName T Y y = .ok ty

omit iDE iLB iHS iHI iL iHV in
/-- Every declared type of resolved items resolves a type reference of the items. -/
theorem resolveItems_tys {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} :
    ∀ (l : List (WItem P)) (items : List (Item P)), resolveItems T Y l = .ok items →
      ∀ ty ∈ itemTys items, ∃ t ∈ wTyRefs l, RefTy T Y ty t
  | [], _, rfl => fun ty h => by simp [itemTys] at h
  | it :: rest, items, h => by
    simp only [resolveItems, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := h
    have ih := resolveItems_tys rest r hr
    intro ty hty
    have hc : ∀ c : CmdExt P, Stmt.initTypes (.cmd c : PStmt P) = CmdExt.initTypes c :=
      fun _ => rfl
    have hm : ∀ x ty e, Stmt.initTypes (mkInit (P := P) x ty e) = [ty] := fun _ _ _ => rfl
    rcases hit : it with ⟨x, _ | ty', e⟩ | ⟨x, e⟩ | ⟨l, e, md⟩ | ⟨rc, cs⟩ | ⟨t, e⟩ <;>
      simp only [resolveItem, resolveOE, Except.bind_is_ok, Except.pure_is_ok, hit,
        exists_eq_left'] at ha
    rotate_right
    · obtain ⟨t', ht, e', he, rfl⟩ := ha
      have iht := resolveItems_tys t t' ht ty
      have ihe := resolveItems_tys e e' he ty
      grind [itemTys, wTyRefs]
    rotate_right
    · obtain ⟨cs', hcs, rfl⟩ := ha
      have hno : ∀ (cs : List (Bool × String × WExpr P × MetaData P)) (cs' : PStmts P),
          cs.mapM (fun (isCover, l, e, md) => do
            let e ← resolveE T Y e
            pure (if isCover then (.cmd (.cmd (.cover l e md)) : PStmt P)
              else .cmd (.cmd (.assert l e md)))) = .ok cs' → Block.initTypes cs' = [] := by
        intro cs
        induction cs with
        | nil => intro cs' h; cases h; rfl
        | cons c cs ih =>
          intro cs' h
          simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at h
          obtain ⟨c', ⟨e', -, rfl⟩, cs'', hcs, rfl⟩ := h
          split <;> simp [Block.initTypes, ih cs'' hcs, Stmt.initTypes, HasInitTypesImp.initTypes,
            CmdExt.initTypes, Cmd.initTypes]
      simp only [itemTys, hno cs cs' hcs, List.nil_append] at hty
      grind [wTyRefs]
    case' init.of => obtain ⟨ty0, h0, _, -, rfl⟩ := ha
    all_goals try obtain ⟨_, -, rfl⟩ := ha
    all_goals
      simp only [itemTys, List.mem_append, hm, hc, CmdExt.initTypes, Cmd.initTypes,
        List.mem_singleton, List.not_mem_nil, false_or] at hty
      first
        | exact (ih ty hty).imp fun t h => ⟨by simp [wTyRefs, h.1], h.2⟩
        | rcases hty with rfl | hty
          · first | (simp [wTyRefs, RefTy]; done) | simp [wTyRefs, RefTy, h0]
          · exact (ih ty hty).imp fun t h => ⟨by simp [wTyRefs, h.1], h.2⟩
  termination_by l => sizeOf l
  decreasing_by all_goals subst_vars; simp_wf; omega

omit iLB iHS iHI iL iHV in
/-- **The declared types of the emitted guarded program** resolve type references of the items
    of the rope. -/
theorem emit_tys {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
    {s : Rope (WItem P)} {lay : PStmts P} (h : emit T Y s = .ok lay) :
    ∀ ty ∈ Block.initTypes lay, ∃ t ∈ wTyRefs s.toList, RefTy T Y ty t := by
  obtain ⟨items, hi, ⟨⟩⟩ := (Except.bind_is_ok _ _ _).1 h
  exact fun ty hty => resolveItems_tys _ _ hi ty (mergeObls_tys _ ty (nest_tys _ ty hty))

/-! ## The type facts of a walk -/

section
variable (K V : List P.Ident) (Θ : P.Ty → Prop) (T0 : Std.HashMap P.Ident P.Ty)

/-- A type reference allowed in the output of a walk: a known type satisfying `Θ`, or the type
    of a name that is in `V` when it is in `K`. -/
@[expose] def RefOK : TyRef P → Prop
  | .known ty => Θ ty
  | .of y => y ∈ K → y ∈ V

/-- The type facts of a walk state `st`, for the names `K` (the variables of the initial types)
    avoided by fresh names, the names `V` allowed among them, the allowed types `Θ` and the
    initial declared types `T0`: the Boolean type is allowed; the names of `K` are avoided and
    are no recorded renaming; a declared type is allowed or the initial one; the target of a
    type reference and of a carried merge is in `V` when it is in `K`. -/
structure TyInv (st : WSt P) : Prop where
  bool : Θ HasBool.boolTy
  av : ∀ k ∈ K, st.avoid.contains k = true
  nm : ∀ x n : P.Ident, st.nm[x]? = some n → n ∉ K
  tys : ∀ (k : P.Ident) (ty : P.Ty), st.tys[k]? = some ty → Θ ty ∨ T0[k]? = some ty
  tyOf : ∀ k z : P.Ident, st.tyOf[k]? = some z → z ∈ K → z ∈ V
  car : ∀ (j : Nat) (q : P.Ident × WExpr P × P.Ident), q ∈ st.carries.getD j [] → q.1 ∈ K →
    q.1 ∈ V

/-- The type facts of a walk result `r`: its output holds only allowed type references
    (`RefOK`), and every name it assigns is in `V` when it is in `K`. -/
structure TyOut (r : WRes P) : Prop where
  refs : ∀ t ∈ wTyRefs r.out.toList, RefOK K V Θ t
  A : ∀ n : P.Ident, r.A.contains n = true → n ∈ K → n ∈ V

/-- The type property of the walk `m` of a fragment `ss`: every run from a state with the type
    facts, of a fragment whose declared types are allowed, whose variables of `K` it reads or
    writes are in `V`, and which declares no name of `K`, ends in a state with the type facts
    and has a result with the type facts. -/
@[expose] def TySpec (m : WM P (WRes P)) (ss : PStmts P) : Prop :=
  ∀ st r st', m.run st = .ok (r, st') → TyInv K V Θ T0 st →
    (∀ ty ∈ Block.initTypes ss, Θ ty) → (∀ x ∈ Block.freeVars ss, x ∈ K → x ∈ V) →
    (∀ x ∈ K, x ∉ stmtsInits ss) → TyInv K V Θ T0 st' ∧ TyOut K V Θ r
end

section
variable {K V : List P.Ident} {Θ : P.Ty → Prop} {T0 : Std.HashMap P.Ident P.Ty}
  {st st' : WSt P} {x n : P.Ident}

omit iL iW in
/-- A state with the avoided names of a state `st` with the type facts, whose renamings are those
    of `st` or names `st` does not avoid, and whose declared types, type references and carried
    merges are those of `st` or allowed ones, has the type facts. -/
theorem TyInv.step (h : TyInv K V Θ T0 st) (ha : st'.avoid = st.avoid)
    (hn : ∀ x n : P.Ident, st'.nm[x]? = some n → st.nm[x]? = some n ∨ st.avoid.contains n = false)
    (ht : ∀ (k : P.Ident) ty, st'.tys[k]? = some ty → st.tys[k]? = some ty ∨ Θ ty)
    (ho : ∀ k z : P.Ident, st'.tyOf[k]? = some z → st.tyOf[k]? = some z ∨ (z ∈ K → z ∈ V))
    (hc : ∀ (j : Nat) (q : P.Ident × WExpr P × P.Ident), q ∈ st'.carries.getD j [] →
      q ∈ st.carries.getD j [] ∨ (q.1 ∈ K → q.1 ∈ V)) :
    TyInv K V Θ T0 st' :=
  ⟨h.bool, fun k hk => ha ▸ h.av k hk,
    fun x n hx hnK => (hn x n hx).elim (h.nm x n · hnK) fun hf => by
      simp [h.av n hnK] at hf,
    fun k ty hk => (ht k ty hk).elim (h.tys k ty) .inl,
    fun k z hk => (ho k z hk).elim (h.tyOf k z) id,
    fun j q hq => (hc j q hq).elim (h.car j q) id⟩

omit iDE iLB iHB iHF iHS iHI iL iHV iW in
/-- A value of a hash map after an insertion of a value satisfying `Q` is a value before it or
    satisfies `Q`. -/
theorem getElem?_insert_or {α β : Type} [BEq α] [Hashable α] [LawfulBEq α] {m : Std.HashMap α β}
    {a : α} {b : β} {Q : β → Prop} (hb : Q b) :
    ∀ (k : α) (v : β), (m.insert a b)[k]? = some v → m[k]? = some v ∨ Q v := fun k v h => by
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · exact .inr (Option.some.inj h ▸ hb)
  · exact .inl h

/-- A run of `wName x` keeps the type facts and returns `x` or a name not in `K`. -/
theorem wName_ty (h : (wName x).run st = .ok (n, st')) (hi : TyInv K V Θ T0 st) :
    TyInv K V Θ T0 st' ∧ (n ∈ K → n = x) := by
  obtain ⟨k, hk, -, hav⟩ := freshIn_spec st.avoid (baseOf x) st.next
  rcases wName_cases h with ⟨h1, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
  · exact ⟨hi, fun hn => absurd hn (hi.nm x n h1)⟩
  · exact ⟨hi, fun _ => rfl⟩
  rw [hk]
  refine ⟨hi.step rfl (fun y m hm => ?_) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h), fun hm => by simp [hi.av _ hm] at hav⟩
  exact (getElem?_insert_or (Q := fun m => st.avoid.contains m = false) hav y m hm)

/-- A run of `wDecl x` keeps the type facts. -/
theorem wDecl_ty (h : (wDecl x).run st = .ok (n, st')) (hi : TyInv K V Θ T0 st) :
    TyInv K V Θ T0 st' := by
  obtain ⟨n1, s1, h1⟩ := wName_ok x st
  cases (wDecl_run h1).symm.trans h
  have hs := (wName_ty h1 hi).1
  exact hs.step rfl (fun y m hm => .inl (by grind))
    (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)

/-- A run of `wRen e` keeps the type facts. -/
theorem wRen_ty {e : P.Expr} {p : WExpr P × List P.Ident} (h : (wRen e).run st = .ok (p, st'))
    (hi : TyInv K V Θ T0 st) : TyInv K V Θ T0 st' := by
  obtain ⟨we, rd⟩ := p
  obtain ⟨-, -, hs, -⟩ := wRen_run h
  have hw := wRen_walk h
  rw [hs]
  exact hi.step rfl (fun y m hm => (hw.nm y m (hs ▸ hm)).imp_right fun ⟨_, _, _, h, _⟩ => h)
    (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)

omit iL iW in
/-- A run of `liveAdd xs` keeps the type facts. -/
theorem liveAdd_ty {xs : List P.Ident} {u : Unit} (h : (liveAdd xs).run st = .ok (u, st'))
    (hi : TyInv K V Θ T0 st) : TyInv K V Θ T0 st' := by
  obtain ⟨_, _, rfl, -⟩ := liveAdd_step h
  exact hi.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h)

omit iL iW in
/-- A run of `wFreshBool b` keeps the type facts. -/
theorem wFreshBool_ty {b : String} (h : (wFreshBool b).run st = .ok (n, st'))
    (hi : TyInv K V Θ T0 st) : TyInv K V Θ T0 st' := by
  cases (wFreshBool_run b st).symm.trans h
  exact hi.step rfl (fun _ _ h => .inl h) (getElem?_insert_or hi.bool) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h)

omit iL in
/-- A run of `wFreshLike y` for a name `y` in `V` when it is in `K` keeps the type facts. -/
theorem wFreshLike_ty {y : P.Ident} (h : (wFreshLike y).run st = .ok (n, st'))
    (hi : TyInv K V Θ T0 st) (hy : y ∈ K → y ∈ V) : TyInv K V Θ T0 st' := by
  cases (wFreshLike_run y st).symm.trans h
  exact hi.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (getElem?_insert_or hy)
    (fun _ _ h => .inl h)

omit iL in
/-- A run of `saveRestore xs` for names `xs` in `V` when they are in `K` keeps the type facts;
    its saves, copies and restores hold only references to the types of names of `xs`, and its
    copy pairs pair names of `xs`. -/
theorem saveRestore_ty {xs : List P.Ident}
    {r : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) × List (P.Ident × P.Ident)}
    (h : (saveRestore xs).run st = .ok (r, st')) (hi : TyInv K V Θ T0 st)
    (hx : ∀ y ∈ xs, y ∈ K → y ∈ V) : TyInv K V Θ T0 st' ∧
      (∀ t ∈ wTyRefs (r.1.toList ++ r.2.1.toList ++ r.2.2.1.toList), RefOK K V Θ t) ∧
      ∀ p ∈ r.2.2.2, p.1 ∈ xs := by
  unfold saveRestore at h
  obtain ⟨b, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  obtain ⟨ha, hn, ht, hc, ho, hr, hp⟩ := wm_forIn_inv (fun S (b : Rope (WItem P) × Rope (WItem P) ×
      Rope (WItem P) × List (P.Ident × P.Ident)) (s : WSt P) => s.avoid = st.avoid ∧
      s.nm = st.nm ∧ s.tys = st.tys ∧ s.carries = st.carries ∧
      (∀ k z : P.Ident, s.tyOf[k]? = some z → st.tyOf[k]? = some z ∨ z ∈ S) ∧
      (∀ t ∈ wTyRefs (b.1.toList ++ b.2.1.toList ++ b.2.2.1.toList), ∃ y ∈ S, t = .of y) ∧
      ∀ p ∈ b.2.2.2, p.1 ∈ S) _ (by
        intro S y b s b' s' ⟨ha, hn, ht, hc, ho, hr, hp⟩ hb
        obtain ⟨a, s1, h1, hb⟩ := wm_run_bind_ok hb
        obtain ⟨c, s2, h2, hb⟩ := wm_run_bind_ok hb
        cases hb
        cases (wFreshLike_run y s).symm.trans h1
        cases (wFreshLike_run y _).symm.trans h2
        refine ⟨_, rfl, ha, hn, ht, hc, fun k z h => ?_, fun t h => ?_, fun p h => ?_⟩
        · grind
        · simp only [Rope.toList_app, Rope.toList_one, wTyRefs_append, wTyRefs, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false, List.append_nil] at h hr ⊢
          grind
        · grind) xs [] _ st _ _
    ⟨rfl, rfl, rfl, rfl, fun _ _ h => .inl h, by simp [Rope.toList_nil, wTyRefs], by simp⟩ hl
  refine ⟨hi.step ha (fun _ _ h => .inl (hn ▸ h)) (fun _ _ h => .inl (ht ▸ h))
    (fun k z h => (ho k z h).imp_right (hx z ·)) (fun _ _ h => .inl (hc ▸ h)),
    fun t h => ?_, hp⟩
  obtain ⟨y, hy, rfl⟩ := hr t h
  exact hx y hy

omit iL iW in
/-- A result without output and assigned names has the type facts. -/
theorem tyOut_nil {r : WRes P} (ho : r.out = .nil) (hA : r.A = {}) : TyOut K V Θ r :=
  ⟨by simp [ho, Rope.toList_nil, wTyRefs], by simp [hA]⟩

omit iL iW in
/-- A state whose declared types are those of a state with the type facts or allowed, the live set
    aside, has the type facts. -/
private theorem TyInv.tys_live {s : WSt P} {T : Std.HashMap P.Ident P.Ty}
    (l : Std.HashMap P.Ident Nat) (hs : TyInv K V Θ T0 s)
    (ht : ∀ (k : P.Ident) ty, T[k]? = some ty → s.tys[k]? = some ty ∨ Θ ty) :
    TyInv K V Θ T0 { s with tys := T, live := l } :=
  hs.step rfl (fun _ _ h => .inl h) ht (fun _ _ h => .inl h) (fun _ _ h => .inl h)

omit iL iW in
/-- A result with allowed type references and no assigned name has the type facts. -/
private theorem tyOut_noA {r : WRes P} (h1 : ∀ t ∈ wTyRefs r.out.toList, RefOK K V Θ t)
    (h2 : r.A = {}) : TyOut K V Θ r := ⟨h1, by simp [h2]⟩

omit iDE iHB iHF iHS iHI iL iHV iW in
/-- The only name of a singleton set is in `V` when it is in `K`, if its element is. -/
private theorem single_ok {n : P.Ident} (hn : n ∈ K → n ∈ V) :
    ∀ m : P.Ident, (Std.HashSet.ofList [n]).contains m = true → m ∈ K → m ∈ V := fun m hm => by
  simp only [Std.HashSet.contains_ofList, List.contains_cons, List.contains_nil, Bool.or_false,
    beq_iff_eq] at hm
  exact hm ▸ hn

/-- Inverts a successful run of a straight-line step of the WP walk in the hypothesis `h`. -/
local macro "ty_inv " h:ident : tactic => `(tactic| simp only [Bool.not_true, Bool.not_false,
  Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_get,
  StateT.run_set, StateT.run_pure, Except.bind_is_ok, Except.pure_is_ok, Except.ok.injEq,
  Prod.mk.injEq, exists_eq_left', liveDel, wFresh_run, wFreshBool_run] at $h:ident)

/-- The walk of a command has the type property. -/
theorem tySpec_cmd (κ : RE P) (d : Nat) (f : Bool) (c : CmdExt P) :
    TySpec K V Θ T0 (wpStmt κ d f (.cmd c)) [.cmd c] := by
  intro st a st' h hi hΘ hV hK
  unfold wpStmt at h
  rcases c with ((⟨x, ty, e | _, md⟩ | ⟨x, e | _, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩ | ⟨l, e, md⟩) |
    ⟨p, args, md⟩)
  all_goals try cases h
  all_goals cases f <;> ty_inv h
  all_goals try (obtain ⟨rfl, rfl⟩ := h; exact ⟨hi, tyOut_nil rfl rfl⟩)
  case' init.det.true =>
    have hθ : Θ ty := hΘ ty (by simp [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes,
      CmdExt.initTypes, Cmd.initTypes])
    obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, h⟩ := h
    have i2 := wDecl_ty h2 (wRen_ty h1 hi)
    split at h <;> ty_inv h <;> obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
    · exact ⟨liveAdd_ty h3 (TyInv.tys_live _ i2 (getElem?_insert_or hθ)), tyOut_noA (by
        simp [Rope.toList_one, wTyRefs, RefOK, hθ]) rfl⟩
    · refine ⟨liveAdd_ty h3 (i2.step rfl (fun _ _ h => .inl h) (fun k v h =>
        (getElem?_insert_or hθ k v h).elim (getElem?_insert_or hθ k v) .inr)
        (fun _ _ h => .inl h) (fun _ _ h => .inl h)), tyOut_noA (by
        simp [Rope.toList_one, Rope.toList_app, wTyRefs, RefOK, hθ]) rfl⟩
  case' init.nondet.true =>
    have hθ : Θ ty := hΘ ty (by simp [Block.initTypes, Stmt.initTypes, HasInitTypesImp.initTypes,
      CmdExt.initTypes, Cmd.initTypes])
    obtain ⟨⟨n, s1⟩, h1, rfl, rfl⟩ := h
    exact ⟨TyInv.tys_live _ (wDecl_ty h1 hi) (getElem?_insert_or hθ), tyOut_noA (by
      simp [Rope.toList_one, wTyRefs, RefOK, hθ]) rfl⟩
  case' set.det.true =>
    obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨n, s2⟩, h2, h⟩ := h
    obtain ⟨i2, hn⟩ := wName_ty h2 (wRen_ty h1 hi)
    have hx : n ∈ K → n ∈ V :=
      fun h => hn h ▸ hV x (by simp [Block.freeVars, Stmt.freeVars]) (hn h ▸ h)
    split at h <;> ty_inv h
    · obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      exact ⟨liveAdd_ty h3 (TyInv.tys_live _ i2 fun _ _ h => .inl h),
        ⟨by simp [Rope.toList_one, wTyRefs], single_ok hx⟩⟩
    · obtain ⟨⟨u, s3⟩, h3, ⟨u', s4⟩, h4, rfl, rfl⟩ := h
      exact ⟨liveAdd_ty h4 (liveAdd_ty h3 i2), ⟨by simp [Rope.toList_one, wTyRefs], single_ok hx⟩⟩
  case' set.nondet.true =>
    obtain ⟨⟨n, s1⟩, h1, ⟨y, s2⟩, h2, h⟩ := h
    obtain ⟨i1, hn⟩ := wName_ty h1 hi
    have hx : n ∈ K → n ∈ V :=
      fun h => hn h ▸ hV x (by simp [Block.freeVars, Stmt.freeVars]) (hn h ▸ h)
    have i2 := wFreshLike_ty h2 i1 hx
    split at h <;> ty_inv h
    · obtain ⟨rfl, rfl⟩ := h
      refine ⟨TyInv.tys_live _ i2 fun _ _ h => .inl h, ⟨fun t ht => ?_, single_ok hx⟩⟩
      simp only [Rope.toList_app, Rope.toList_one, List.cons_append, List.nil_append, wTyRefs,
        List.mem_cons, List.not_mem_nil, or_false] at ht
      exact ht ▸ hx
    · obtain ⟨⟨u, s3⟩, h3, rfl, rfl⟩ := h
      refine ⟨liveAdd_ty h3 i2, ⟨fun t ht => ?_, single_ok hx⟩⟩
      simp only [Rope.toList_app, Rope.toList_one, List.cons_append, List.nil_append, wTyRefs,
        List.mem_cons, List.not_mem_nil, or_false] at ht
      exact ht ▸ hx
  all_goals
    obtain ⟨⟨⟨we, rd⟩, s1⟩, h1, ⟨u, s2⟩, h2, rfl, rfl⟩ := h
    exact ⟨liveAdd_ty h2 (wRen_ty h1 hi), tyOut_noA (by simp [Rope.toList_one, wTyRefs]) rfl⟩

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- The items of `setReach κ X` hold no type reference. -/
theorem setReach_refs (κ : RE P) (X : WExpr P) : wTyRefs (setReach κ X).toList = [] := by
  cases κ <;> simp [setReach, Rope.toList_nil, Rope.toList_one, wTyRefs]

omit iL in
/-- The walk of an `exit` has the type property. -/
theorem tySpec_exit (κ : RE P) (d : Nat) (f : Bool) (l : String) (md : MetaData P) :
    TySpec K V Θ T0 (wpStmt κ d f (.exit l md)) [.exit l md] := by
  intro st a st' h hi _ _ _
  unfold wpStmt at h
  cases κ <;> ty_inv h <;> (try split at h) <;> cases f <;> (try ty_inv h)
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := h
       exact ⟨hi.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
         (fun _ _ h => .inl h), tyOut_noA (by simp [setReach_refs, Rope.toList_nil, wTyRefs]) rfl⟩)
    | (obtain ⟨⟨u, s1⟩, h1, rfl, rfl⟩ := h
       exact ⟨liveAdd_ty h1 (hi.step rfl (fun _ _ h => .inl h) (getElem?_insert_or hi.bool)
         (fun _ _ h => .inl h) (fun _ _ h => .inl h)), tyOut_noA (by
           simp [Rope.toList_app, Rope.toList_one, setReach_refs, wTyRefs, RefOK,
             hi.bool]) rfl⟩)

omit iL in
/-- The walk of a statement that is not a command, an `exit`, a block or a deterministic `ite`
    has the type property. -/
theorem tySpec_other (κ : RE P) (d : Nat) (f : Bool) (s : PStmt P)
    (hs : (∀ c, s ≠ .cmd c) ∧ (∀ l md, s ≠ .exit l md) ∧ (∀ l b md, s ≠ .block l b md) ∧
      ∀ c t e md, s ≠ .ite (.det c) t e md) : TySpec K V Θ T0 (wpStmt κ d f s) [s] := by
  intro st a st' h hi _ _ _
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold wpStmt at h
  rcases s with _ | _ | ⟨_ | c, t, e, md⟩ | _ | _ | _ <;>
    first | exact absurd rfl (h4 _ _ _ _) | cases h | simp at h1 h2 h3
  exact ⟨hi, tyOut_nil rfl rfl⟩

omit iL in
/-- The walk of the empty list has the type property. -/
theorem tySpec_nil (κ : RE P) (d : Nat) (fEnd : Bool) :
    TySpec K V Θ T0 (wpList κ d fEnd []) [] := fun _ _ _ h hi _ _ _ => by
  simp only [wpList, StateT.run_pure] at h
  cases h
  exact ⟨hi, tyOut_nil rfl rfl⟩

omit iL in
/-- The walk of `s :: rest` has the type property when the walks of `s` (for every obligation
    bit) and of `rest` have it. -/
theorem tySpec_cons {κ : RE P} {d : Nat} {fEnd : Bool} {s : PStmt P} {rest : PStmts P}
    (hs : ∀ f, TySpec K V Θ T0 (wpStmt κ d f s) [s])
    (hr : TySpec K V Θ T0 (wpList κ d fEnd rest) rest) :
    TySpec K V Θ T0 (wpList κ d fEnd (s :: rest)) (s :: rest) := by
  intro st R st' h hi hΘ hV hK
  obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_run_cons h
  have hKs : ∀ x ∈ K, x ∉ stmtsInits [s] ∧ x ∉ stmtsInits rest := fun x hx => by
    simpa [stmtsInits_cons_eq s rest] using hK x hx
  have hTs : ∀ x ∈ K, x ∉ Stmt.topInits s := fun x hx ht => (hKs x hx).1 (by
    rcases s with ((_ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _ <;>
      simp_all [Stmt.topInits, stmtsInits])
  obtain ⟨i1, o1⟩ := hr st r st1 h1 hi (fun ty h => hΘ ty (by simp [Block.initTypes, h]))
    (fun x hx hk => hV x (fv_tail hx (hTs x hk)) hk) (fun x hx => (hKs x hx).2)
  obtain ⟨i2, o2⟩ := hs _ st1 a st2 h2 i1 (fun ty h => hΘ ty (by simp_all [Block.initTypes]))
    (fun x hx hk => hV x (fv_head hx) hk) (fun x hx => (hKs x hx).1)
  rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
  · exact ⟨i2, o2⟩
  · exact ⟨i2.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h), o2⟩
  · refine ⟨i2, fun t ht => ?_, fun n hn => ?_⟩
    · simp only [WRes.combine, Rope.toList_app, wTyRefs_append, List.mem_append] at ht
      exact ht.elim (o2.refs t) (o1.refs t)
    · simp only [WRes.combine, unionSet_contains, Bool.or_eq_true] at hn
      exact hn.elim (o2.A n) (o1.A n)

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- Appending `set` items to a rope adds no type reference. -/
theorem foldl_set_refs {α : Type} (g : α → P.Ident) (v : α → Option (WExpr P)) :
    ∀ (L : List α) (s : Rope (WItem P)),
      wTyRefs (L.foldl (fun acc x => acc.app (.one (.set (g x) (v x)))) s).toList =
        wTyRefs s.toList
  | [], _ => rfl
  | x :: L, s => by
    simp [foldl_set_refs g v L, Rope.toList_app, Rope.toList_one, wTyRefs_append, wTyRefs]

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- A state whose carried merges are those of a state with the type facts, at the entry of a
    block or at its exit, has the type facts when it is otherwise unchanged. -/
private theorem carries_sub {C C' : Std.HashMap Nat (List (P.Ident × WExpr P × P.Ident))}
    (hC : C' = C.insert (d + 1) [] ∨ C' = C.erase (d + 1)) :
    ∀ (j : Nat) (q : P.Ident × WExpr P × P.Ident), q ∈ C'.getD j [] →
      q ∈ C.getD j [] ∨ (q.1 ∈ K → q.1 ∈ V) := fun j q h => .inl (by
  rcases hC with rfl | rfl <;> simp only [Std.HashMap.getD_insert, Std.HashMap.getD_erase] at h <;>
    split at h <;> simp_all)

omit iL in
/-- The walk of a block has the type property when the walks of its body (at the next depth,
    under every context) have it. -/
theorem tySpec_block {κ : RE P} {d : Nat} {f : Bool} {l : String} {body : PStmts P}
    (md : MetaData P) (hB : ∀ κB, TySpec K V Θ T0 (wpList κB (d + 1) f body) body) :
    TySpec K V Θ T0 (wpStmt κ d f (.block l body md)) [.block l body md] := by
  intro st a st' h hi hΘ hV hK
  unfold wpStmt at h
  ty_inv h
  have hb : ∀ κB, ∀ s0 B s1, (wpList κB (d + 1) f body).run s0 = .ok (B, s1) →
      TyInv K V Θ T0 s0 → TyInv K V Θ T0 s1 ∧ TyOut K V Θ B := fun κB s0 B s1 h1 hi0 =>
    hB κB s0 B s1 h1 hi0 (fun ty h => hΘ ty (by simpa [Block.initTypes, Stmt.initTypes] using h))
      (fun x hx => hV x (by simpa [Block.freeVars, Stmt.freeVars] using hx))
      (fun x hx h => hK x hx (by simpa [stmtsInits] using h))
  have hA : ∀ {B : WRes P} {s1 : WSt P}, TyInv K V Θ T0 s1 → TyOut K V Θ B → ∀ n : P.Ident,
      (((s1.carries.getD (d + 1) []).filter fun x => !s1.dead.contains x.2.2).foldl
        (fun s x => s.insert x.1) B.A).contains n = true → n ∈ K → n ∈ V := fun i1 o1 n hn =>
    (foldl_insert_fst (fun _ _ => rfl) hn).elim (o1.A n) fun ⟨q, hq, he⟩ =>
      he ▸ i1.car _ q (List.mem_filter.1 hq).1
  split at h
  all_goals ty_inv h
  all_goals obtain ⟨⟨B, s1⟩, h1, ⟨u, s2⟩, h2, rfl, rfl⟩ := h
  · obtain ⟨i1, o1⟩ := hb _ _ B s1 h1 (hi.step rfl (fun _ _ h => .inl h)
      (getElem?_insert_or hi.bool) (fun _ _ h => .inl h) (carries_sub (.inl rfl)))
    refine ⟨liveAdd_ty h2 (i1.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h) (carries_sub (.inr rfl))), fun t ht => ?_, hA i1 o1⟩
    have hite : ∀ {c : Prop} [Decidable c] {Y : Rope (WItem P)},
        t ∈ wTyRefs (if c then Rope.nil else Y).toList → t ∈ wTyRefs Y.toList := fun h => by
      split at h
      · simp [Rope.toList_nil, wTyRefs] at h
      · exact h
    replace ht := hite ht
    simp only [Rope.toList_app, Rope.toList_one, wTyRefs_append, foldl_set_refs, Rope.toList_nil,
      wTyRefs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | ht
    · exact hi.bool
    · exact o1.refs t ht
    · split at ht <;> (try split at ht) <;> simp [Rope.toList_nil, Rope.toList_one, wTyRefs] at ht
  · obtain ⟨i1, o1⟩ := hb _ _ B s1 h1 (hi.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h) (carries_sub (.inl rfl)))
    refine ⟨liveAdd_ty h2 (i1.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h) (carries_sub (.inr rfl))), fun t ht => ?_, hA i1 o1⟩
    simp only [Rope.toList_app, wTyRefs_append, foldl_set_refs, Rope.toList_nil, wTyRefs,
      List.mem_append, List.not_mem_nil, or_false] at ht
    refine ht.elim (o1.refs t) fun ht => ?_
    split at ht <;> (try split at ht) <;> simp [Rope.toList_nil, setReach_refs, wTyRefs] at ht

/-- The walk of a real branch has the type property when the walks of its arms (under `top`,
    no obligation following them) have it. -/
theorem tySpec_iteReal {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : TySpec K V Θ T0 (wpList .top d false tss) tss)
    (hE : TySpec K V Θ T0 (wpList .top d false ess) ess) :
    TySpec K V Θ T0 (wpIteReal κ d c tss ess) [.ite (.det c) tss ess md] := by
  intro st a st' h hi hΘ hV hK
  unfold wpIteReal at h
  ty_inv h
  have hΘ' : ∀ ty, ty ∈ Block.initTypes tss ∨ ty ∈ Block.initTypes ess → Θ ty := fun ty h =>
    hΘ ty (by simpa [Block.initTypes, Stmt.initTypes] using h)
  have hV' : ∀ x, x ∈ Block.freeVars tss ∨ x ∈ Block.freeVars ess → x ∈ K → x ∈ V := fun x h =>
    hV x (by rcases h with h | h <;> simp [Block.freeVars, Stmt.freeVars, h])
  have hK' : ∀ x ∈ K, x ∉ stmtsInits tss ∧ x ∉ stmtsInits ess := fun x hx => by
    simpa [stmtsInits] using hK x hx
  obtain ⟨⟨E, s2⟩, h2, ⟨T, s4⟩, h4, h⟩ := h
  obtain ⟨i2, o2⟩ := hE _ E s2 h2 (hi.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h) (fun _ _ h => .inl h)) (fun ty h => hΘ' ty (.inr h))
    (fun x h => hV' x (.inr h)) (fun x hx => (hK' x hx).2)
  obtain ⟨i4, o4⟩ := hT _ T s4 h4 (i2.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h) (fun _ _ h => .inl h)) (fun ty h => hΘ' ty (.inl h))
    (fun x h => hV' x (.inl h)) (fun x hx => (hK' x hx).1)
  split at h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨i4.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (fun _ _ h => .inl h), tyOut_nil rfl rfl⟩
  ty_inv h
  obtain ⟨⟨⟨wc, rdc⟩, s7⟩, h7, ⟨u, s9⟩, h9, rfl, rfl⟩ := h
  have i7 := wRen_ty h7 (i4.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h) (fun _ _ h => .inl h))
  refine ⟨liveAdd_ty h9 (i7.step rfl (fun _ _ h => .inl h)
    (getElem?_insert_or i7.bool) (fun _ _ h => .inl h) (fun _ _ h => .inl h)), fun t ht => ?_,
    fun n hn => ?_⟩
  · split at ht <;> (try split at ht) <;>
      simp only [Rope.toList_app, Rope.toList_one, wTyRefs, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, List.cons_append, List.nil_append] at ht
    all_goals refine ht.elim (fun h => h ▸ i7.bool) fun ht => ?_
    all_goals first
      | exact ht.elim (o4.refs t) (o2.refs t)
      | exact o4.refs t ht
      | exact o2.refs t ht
  · simp only [unionSet_contains, Bool.or_eq_true] at hn
    exact hn.elim (o4.A n) (o2.A n)

omit iL iW in
/-- An optional draw of a Boolean name keeps the type facts. -/
theorem optDraw_ty {b : String} {s s' : WSt P} {o : Option P.Ident} (h : OptDraw b s s' o)
    (hi : TyInv K V Θ T0 s) : TyInv K V Θ T0 s' := by
  cases o with
  | none => exact (show s' = s from h) ▸ hi
  | some x => exact wFreshBool_ty h hi

omit iDE iBE iLB iHB iHF iHS iHI iL iHa iHV iW in
/-- A type reference of the items of a flattened list is one of the items of an element. -/
theorem mem_wTyRefs_flatMap {α : Type} {f : α → List (WItem P)} {t : TyRef P} :
    ∀ {L : List α}, t ∈ wTyRefs (L.flatMap f) → ∃ x ∈ L, t ∈ wTyRefs (f x)
  | [], h => by simp [wTyRefs] at h
  | x :: L, h => by
    rw [List.flatMap_cons, wTyRefs_append, List.mem_append] at h
    exact h.elim (fun h => ⟨x, .head _, h⟩) fun h =>
      (mem_wTyRefs_flatMap h).imp fun _ ⟨h1, h2⟩ => ⟨.tail _ h1, h2⟩

omit iDE iHB iHF iHS iHI iL iHV iW in
/-- An element of an interset of hash sets is in the first one. -/
private theorem mem_interSet_left' {a b : Std.HashSet P.Ident} {y : P.Ident}
    (h : y ∈ interSet a b) : a.contains y = true := by
  simp only [interSet, Std.HashSet.fold_eq_foldl_toList, ← List.foldl_filter] at h
  split at h <;> simp_all

/-- The walk of a laid-out `ite` has the type property when the walks of its arms (at the same
    depth, under every context, an obligation following them) have it. -/
theorem tySpec_iteLaid {κ : RE P} {d : Nat} {c : P.Expr} {tss ess : PStmts P} (md : MetaData P)
    (hT : ∀ κ', TySpec K V Θ T0 (wpList κ' d true tss) tss)
    (hE : ∀ κ', TySpec K V Θ T0 (wpList κ' d true ess) ess) :
    TySpec K V Θ T0 (wpIteLaid κ d c tss ess) [.ite (.det c) tss ess md] := by
  intro st a st' h hi hΘ hV hK
  have hΘ' : ∀ ty, ty ∈ Block.initTypes tss ∨ ty ∈ Block.initTypes ess → Θ ty := fun ty h =>
    hΘ ty (by simpa [Block.initTypes, Stmt.initTypes] using h)
  have hV' : ∀ x, x ∈ Block.freeVars tss ∨ x ∈ Block.freeVars ess → x ∈ K → x ∈ V := fun x h =>
    hV x (by rcases h with h | h <;> simp [Block.freeVars, Stmt.freeVars, h])
  have hK' : ∀ x ∈ K, x ∉ stmtsInits tss ∧ x ∉ stmtsInits ess := fun x hx => by
    simpa [stmtsInits] using hK x hx
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc h5 h6 h7 h8 h9 hgm _ hqm _
    hrm _ hEnd => ?_
  have i3 := wFreshBool_ty h3 (wFreshBool_ty h2 (wRen_ty h1 hi))
  have i4 : TyInv K V Θ T0 s4 := by
    rcases hc with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, x, -, -, hx⟩
    iterate 2 exact i3
    exact wFreshBool_ty hx i3
  obtain ⟨i5, o5⟩ := hE κE s4 E s5 h5 i4 (fun ty h => hΘ' ty (.inr h))
    (fun x h => hV' x (.inr h)) (fun x hx => (hK' x hx).2)
  obtain ⟨i6, o6⟩ := hT (.name rT) s5 T s6 h6 i5 (fun ty h => hΘ' ty (.inl h))
    (fun x h => hV' x (.inl h)) (fun x hx => (hK' x hx).1)
  obtain ⟨i7, r7, p7⟩ := saveRestore_ty h7 i6 fun y hy =>
    o6.A y (mem_interSet_left' (List.mem_ite_nil_left.1 hy).2)
  obtain ⟨i8, r8, p8⟩ := saveRestore_ty h8 i7 fun y hy => o6.A y (fold_filter_mem hy)
  obtain ⟨i9, r9, p9⟩ := saveRestore_ty h9 i8 fun y hy => o5.A y (fold_filter_mem hy)
  have i12 := optDraw_ty hrm (optDraw_ty hqm (optDraw_ty hgm i9))
  have hcar : ∀ (e1 e2 : WExpr P) C (j : Nat) (q : P.Ident × WExpr P × P.Ident),
      q ∈ (carryIns e2 (carryOf s6 cpsE E.tgt.max?) (carryIns e1 (carryOf s6 cpsT T.tgt.max?) C
        T.tgt.max?) E.tgt.max?).getD j [] → q ∈ C.getD j [] ∨ (q.1 ∈ K → q.1 ∈ V) := by
    intro e1 e2 C j q hq
    obtain ⟨n2, e2', hn2⟩ := carryIns_getD e2 (carryOf s6 cpsE E.tgt.max?) _ E.tgt.max? j
    obtain ⟨n1, e1', hn1⟩ := carryIns_getD e1 (carryOf s6 cpsT T.tgt.max?) C T.tgt.max? j
    rw [e2', e1', List.mem_append, List.mem_append] at hq
    rcases hq with hq | hq | hq
    · obtain ⟨-, p, hp, rfl⟩ := hn2 q hq
      exact .inr (o5.A p.1 (fold_filter_mem (p9 p (carryOf_sub hp))))
    · obtain ⟨-, p, hp, rfl⟩ := hn1 q hq
      exact .inr (o6.A p.1 (fold_filter_mem (p8 p (carryOf_sub hp))))
    · exact .inl hq
  rcases hEnd with ⟨-, rfl, rfl⟩ | ⟨-, h15, rfl⟩
  · exact ⟨i12.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h) (fun _ _ h => .inl h)
      (hcar _ _ _), tyOut_nil rfl rfl⟩
  refine ⟨liveAdd_ty h15 (i12.step rfl (fun _ _ h => .inl h) (fun _ _ h => .inl h)
    (fun _ _ h => .inl h) (hcar _ _ _)), fun t ht => ?_, fun n hn => ?_⟩
  · rw [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil, List.nil_append,
      List.singleton_append] at ht
    simp only [wTyRefs, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact i12.bool
    replace ht := mem_wTyRefs_flatMap ht
    obtain ⟨X, hX, ht⟩ := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl := hX
    all_goals first
      | exact o6.refs t ht
      | exact o5.refs t ht
      | (apply r7 t; simp [wTyRefs_append, ht]; done)
      | (apply r8 t; simp [wTyRefs_append, ht]; done)
      | (apply r9 t; simp [wTyRefs_append, ht]; done)
      | (rw [foldl_set_refs] at ht; simp [Rope.toList_nil, wTyRefs] at ht)
      | ((repeat' split at ht) <;>
          simp only [Rope.toList_nil, Rope.toList_one, wTyRefs, setReach_refs, List.mem_cons,
            List.not_mem_nil, or_false] at ht <;>
          (subst ht; exact i12.bool))
  · simp only [unionSet_contains, Bool.or_eq_true] at hn
    rcases hn with hn | hn <;> split at hn
    all_goals first | exact o6.A n hn | exact o5.A n hn | simp at hn

end

section
variable {K V : List P.Ident} {Θ : P.Ty → Prop} {T0 : Std.HashMap P.Ident P.Ty}

omit iL in
mutual
/-- Every statement-list walk has the type property. -/
theorem wpList_tySpec [LawfulHasIdent P] :
    ∀ (ss : PStmts P) (κ : RE P) (d : Nat) (fEnd : Bool),
      TySpec K V Θ T0 (wpList κ d fEnd ss) ss
  | [], κ, d, fEnd => tySpec_nil κ d fEnd
  | s :: rest, κ, d, fEnd =>
    tySpec_cons (fun f => wpStmt_tySpec s κ d f) (wpList_tySpec rest κ d fEnd)
/-- Every statement walk has the type property. -/
theorem wpStmt_tySpec [LawfulHasIdent P] :
    ∀ (s : PStmt P) (κ : RE P) (d : Nat) (f : Bool), TySpec K V Θ T0 (wpStmt κ d f s) [s]
  | .cmd c, κ, d, f => tySpec_cmd κ d f c
  | .exit l md, κ, d, f => tySpec_exit κ d f l md
  | .block l body md, κ, d, f => tySpec_block md fun κB => wpList_tySpec body κB (d + 1) f
  | .ite (.det c) tss ess md, κ, d, f => by
    cases f <;> simp only [wpStmt, Bool.false_eq_true, ↓reduceIte]
    · exact tySpec_iteReal md (wpList_tySpec tss .top d false) (wpList_tySpec ess .top d false)
    · exact tySpec_iteLaid md (fun κ' => wpList_tySpec tss κ' d true)
        (fun κ' => wpList_tySpec ess κ' d true)
  | .ite .nondet _ _ _, κ, d, f | .loop _ _ _ _ _, κ, d, f | .typeDecl _ _, κ, d, f =>
    tySpec_other κ d f _ ⟨nofun, nofun, nofun, nofun⟩
end

end

/-- **The types the output of the WP phase declares.**  For a loop-free list `ss` well scoped
    (`Block.WellScoped`) from a scope `S` containing the variables of `tys`, every type an `init`
    of the output of `wpEntry` declares is a declared type of `ss`, the Boolean type, or the type in
    `tys` of a variable that `ss` reads or writes (`Block.freeVars`). -/
theorem wpEntry_initTypes {G : IdSet P} {tys : Tys P} {ss : PStmts P} {w : WOut P}
    (h : wpEntry G tys ss = .ok w) {Lc S : List P.Ident} (hwf : Block.WellScoped Lc S ss)
    (hS : ∀ x ∈ tys.map (·.1), x ∈ S) :
    ∀ ty ∈ Block.initTypes w.lay, ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy ∨
      ∃ x ∈ Block.freeVars ss, tys.get? x = some ty := by
  simp only [wpEntry, wpBody, StateT.run, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, hrun, lay, hlay, rfl⟩ := h
  have hget : ∀ (l : Tys P) x,
      (l.foldr (fun (x, ty) m => m.insert x ty) {} : Std.HashMap P.Ident P.Ty)[x]? = l.get? x := by
    intro l x
    induction l <;> grind [Tys.get?]
  have hkey : ∀ x ty, tys.get? x = some ty → x ∈ tys.map (·.1) := by
    intro x ty hx
    simp only [Tys.get?, Option.map_eq_some_iff] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp, by simpa using List.find?_some hp⟩
  obtain ⟨i1, o1⟩ := wpList_tySpec (K := tys.map (·.1)) (V := Block.freeVars ss)
    (Θ := fun ty => ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy)
    (T0 := tys.foldr (fun (x, ty) m => m.insert x ty) {}) ss .top 0 false _ r st1 hrun
    ⟨.inr rfl, fun k hk => by grind [inputAvoid, AvoidSet.contains, IdSet.ofList],
      fun _ _ h => by simp at h, fun k ty h => .inr h, fun _ _ h => by simp at h,
      fun _ _ h => by simp at h⟩
    (fun ty h => .inl h) (fun x hx _ => hx) (fun x hx => wfl_inits_disjoint S ss hwf x (hS x hx))
  have hz : ∀ z ty, (z ∈ tys.map (·.1) → z ∈ Block.freeVars ss) → st1.tys[z]? = some ty →
      ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy ∨
        ∃ x ∈ Block.freeVars ss, tys.get? x = some ty :=
    fun z ty hok hzt => (i1.tys z ty hzt).elim (·.elim .inl (.inr ∘ .inl)) fun h0 =>
      .inr (.inr ⟨z, hok (hkey z ty (hget tys z ▸ h0)), hget tys z ▸ h0⟩)
  intro ty hty
  obtain ⟨t, ht, hr⟩ := emit_tys hlay ty hty
  have hok := o1.refs t ht
  cases t with
  | known ty' =>
    cases (hr : ty' = ty)
    exact (hok : _ ∨ _).elim .inl (.inr ∘ .inl)
  | of y =>
    change tyOfName st1.tys st1.tyOf y = .ok ty at hr
    unfold tyOfName at hr
    split at hr
    · exact hz y ty hok (by simp_all [pure, Except.pure])
    · split at hr
      · rename_i hb
        cases hr
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
        obtain ⟨z, hz1, hz2⟩ := hb
        exact hz z ty (i1.tyOf y z hz1) hz2
      · cases hr

end -- public section

end WP
end Imperative

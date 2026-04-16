/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.Denote.LExprDenoteConstrs
import all Strata.DL.Lambda.TypeFactoryWF

/-!
## Syntactic Equality Soundness

Proves that the syntactic `eql` function is sound: if `eql` returns `some true`
the denotations are equal, and if it returns `some false` they differ.

- `eql_true_implies_denote_eq` — `eql = some true` implies equal denotations
- `eql_false_implies_denote_ne` — `eql = some false` implies distinct denotations
-/

namespace Lambda

variable {T : LExprParams}
variable (tcInterp : TyConstrInterp)
variable (opInterp : OpInterp tcInterp)
variable (fvarVal : FreeVarVal T tcInterp)
variable (vt : TyVarVal)

section
variable [DecidableEq T.IDMeta] [Inhabited T.mono.base.IDMeta]

/-! ## `eqModuloMeta` soundness -/

theorem eqModuloMeta_true_implies_denote_eq
    {Δ : List LMonoTy}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (bvarVal : BVarVal tcInterp vt Δ)
    (h₁ : LExpr.HasTypeA Δ e₁ τ)
    (h₂ : LExpr.HasTypeA Δ e₂ τ)
    (heql : LExpr.eqModuloMeta e₁ e₂ = true)
    : LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt bvarVal e₂ τ h₂ := by
    unfold LExpr.eqModuloMeta at heql
    have heq: (e₁.eraseMetadata = e₂.eraseMetadata) := by
      unfold BEq.beq instBEqLExprOfIdentifier at heql
      simp at heql
      rw[LExpr.beq_eq] at heql
      exact heql
    rw[denote_replaceMetadata _ _ _ _ bvarVal (fun _ => ()) h₁]
    rw[denote_replaceMetadata _ _ _ _ bvarVal (fun _ => ()) h₂]
    unfold LExpr.eraseMetadata at heq
    generalize replaceMetadata_HasTypeA (fun _ => ()) h₁ = ht₁
    generalize e₁.replaceMetadata (fun _ => ()) = e₁' at *
    subst heq
    rfl

/-! ## `denoteConst` injectivity -/

/-- For non-real constants of the same type, `denoteConst` is injective:
distinct constants of the same type have distinct denotations. -/
theorem denoteConst_injective
    (c1 c2 : LConst)
    (hty : c1.ty = c2.ty)
    (heq : (hty ▸ denoteConst tcInterp vt c1 : TyDenote tcInterp vt c2.ty) =
            denoteConst tcInterp vt c2)
    : c1 = c2 := by
  cases c1 <;> cases c2 <;> simp only [LConst.ty] at hty <;> try contradiction
  case intConst.intConst =>
    rename_i i1 i2 hty_orig
    have hty_rfl : hty_orig = rfl := by rfl
    rw [hty_rfl] at heq
    simp only [denoteConst] at heq
    exact congrArg _ heq
  case strConst.strConst =>
    rename_i s1 s2 hty_orig
    have hty_rfl : hty_orig = rfl := by rfl
    rw [hty_rfl] at heq
    simp only [denoteConst] at heq
    exact congrArg _ heq
  case realConst.realConst =>
    rename_i r1 r2 hty_orig
    have hty_rfl : hty_orig = rfl := by rfl
    rw [hty_rfl] at heq
    simp only [denoteConst] at heq
    exact congrArg _ heq
  case boolConst.boolConst =>
    rename_i b1 b2 hty_orig
    have hty_rfl : hty_orig = rfl := by rfl
    rw [hty_rfl] at heq
    simp only [denoteConst] at heq
    exact congrArg _ heq
  case bitvecConst.bitvecConst =>
    rename_i n1 b1 n2 b2
    simp only [LMonoTy.bitvec.injEq] at hty
    subst hty
    simp only [denoteConst] at heq
    exact congrArg _ heq

/-! ## `eqlCombine` helpers -/

/-- If foldl of eqlCombine returns `some true`, the initial accumulator was `some true`. -/
theorem foldl_eqlCombine_init_true
    {l : List α}
    {f : α → Option Bool}
    {init : Option Bool}
    (h : List.foldl (fun acc x => LExpr.eqlCombine acc (f x)) init l = some true)
    : init = some true := by
  induction l generalizing init with
  | nil => simpa using h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    have := ih h
    unfold LExpr.eqlCombine at this
    split at this <;> simp_all

/-- If foldl of eqlCombine starting from `none` returns `some false`,
then some element of the list maps to `some false`. -/
theorem foldl_eqlCombine_none_to_false
    {l : List α}
    {f : α → Option Bool}
    (h : List.foldl (fun acc x => LExpr.eqlCombine acc (f x)) none l = some false)
    : ∃ (i : Nat) (a : α), l[i]? = some a ∧ f a = some false := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldl_cons] at h
    match hfx : f x with
    | some false =>
      exact ⟨0, x, List.getElem?_cons_zero .. , hfx⟩
    | some true =>
      have hsimp : LExpr.eqlCombine none (some true) = none := by unfold LExpr.eqlCombine; rfl
      rw [hfx, hsimp] at h
      have ⟨i', a, ha, hfa⟩ := ih h
      exact ⟨i' + 1, a, by simp [ha], hfa⟩
    | none =>
      have hsimp : LExpr.eqlCombine none none = none := by unfold LExpr.eqlCombine; rfl
      rw [hfx, hsimp] at h
      have ⟨i', a, ha, hfa⟩ := ih h
      exact ⟨i' + 1, a, by simp [ha], hfa⟩

/-- If `g` preserves `.val`, then foldl over `(l.map g).zip l2` equals
foldl over `l.zip l2` for any function that only accesses `.val`. -/
theorem foldl_zip_map_subtype_eq
    {α β γ : Type _} {P Q : α → Prop}
    (l : List { x : α // P x }) (l2 : List β)
    (g : { x : α // P x } → { x : α // Q x })
    (f : γ → α → β → γ)
    (init : γ)
    (hg : ∀ x, (g x).val = x.val)
    : List.foldl (fun acc x => f acc x.1.val x.2) init ((l.map g).zip l2) =
      List.foldl (fun acc x => f acc x.1.val x.2) init (l.zip l2) := by
  induction l generalizing l2 init with
  | nil => rfl
  | cons a rest ih =>
    cases l2 with
    | nil => rfl
    | cons b rest2 =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [hg a]
      exact ih rest2 _

/-- If foldl eqlCombine over `attach.zip` returns `some true`, then each
individual pair has `eql = some true`. -/
theorem eqlCombine_attach_zip_all_true
    {F : @Factory T}
    {args1 args2 : List (LExpr T.mono)}
    (h : List.foldl (fun acc x =>
      LExpr.eqlCombine acc (LExpr.eql F x.1.val x.snd)) (some true) (args1.attach.zip args2) = some true)
    (i : Nat) (a1 a2 : LExpr T.mono)
    (ha1 : args1[i]? = some a1) (ha2 : args2[i]? = some a2)
    : LExpr.eql F a1 a2 = some true := by
  induction args1 generalizing args2 i with
  | nil => simp at ha1
  | cons x1 rest1 ih_ind =>
    cases args2 with
    | nil => simp at ha2
    | cons x2 rest2 =>
      simp only [List.attach_cons, List.zip_cons_cons, List.foldl_cons] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero] at ha1 ha2
        cases ha1; cases ha2
        have hinit := foldl_eqlCombine_init_true h
        unfold LExpr.eqlCombine at hinit
        split at hinit <;> try contradiction
        assumption
      | succ n =>
        simp only [List.getElem?_cons_succ] at ha1 ha2
        have hinit := foldl_eqlCombine_init_true h
        rw [hinit] at h
        have heq := foldl_zip_map_subtype_eq rest1.attach rest2
            (fun x => ⟨x.val, List.mem_cons_of_mem x1 x.property⟩)
            (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b))
            (some true) (fun _ => rfl)
        simp only [heq] at h
        exact ih_ind h n ha1 ha2


/-- If the eql foldl returns `some true` and each element of args1 satisfies
the IH (eql true → denote eq), then pointwise denotations are equal. -/
theorem eql_foldl_implies_denote_eq_pointwise
    {F : @Factory T}
    {args1 args2 : List (LExpr T.mono)}
    (argTys : List LMonoTy)
    (ih : ∀ a1 ∈ args1, ∀ a2 fvarVal'
      {τ : LMonoTy} (ht1 : LExpr.HasTypeA [] a1 τ) (ht2 : LExpr.HasTypeA [] a2 τ),
      OpsConsistent F a1 → OpsConsistent F a2 →
      LExpr.eql F a1 a2 = some true →
        LExpr.denote tcInterp opInterp fvarVal' vt .nil a1 τ ht1 =
        LExpr.denote tcInterp opInterp fvarVal' vt .nil a2 τ ht2)
    (hoc₁ : ∀ a ∈ args1, OpsConsistent F a)
    (hoc₂ : ∀ a ∈ args2, OpsConsistent F a)
    (heql_fold : List.foldl (fun acc x =>
      LExpr.eqlCombine acc (LExpr.eql F x.1.val x.snd)) (some true) (args1.attach.zip args2) = some true)
    : ∀ (i : Nat) (a1 a2 : LExpr T.mono) (τ : LMonoTy),
      args1[i]? = some a1 → args2[i]? = some a2 → argTys[i]? = some τ →
      ∀ (ht1 : LExpr.HasTypeA [] a1 τ) (ht2 : LExpr.HasTypeA [] a2 τ),
      LExpr.denote tcInterp opInterp fvarVal vt .nil a1 τ ht1 =
      LExpr.denote tcInterp opInterp fvarVal vt .nil a2 τ ht2 := by
  intro i a1 a2 τ ha1 ha2 hτ ht1 ht2
  have hmem1 : a1 ∈ args1 := List.mem_iff_getElem?.mpr ⟨i, ha1⟩
  have hmem2 : a2 ∈ args2 := List.mem_iff_getElem?.mpr ⟨i, ha2⟩
  have heql_i := eqlCombine_attach_zip_all_true heql_fold i a1 a2 ha1 ha2
  exact ih a1 hmem1 a2 fvarVal ht1 ht2 (hoc₁ a1 hmem1) (hoc₂ a2 hmem2) heql_i

/-! ## Main `eql` soundness theorems -/

/-- If `eql` returns `some true`, then the denotations are equal.
Restricted to the empty bound-variable context since `varOpen` (used in
the lambda case) does not shift de Bruijn indices. -/
theorem eql_true_implies_denote_eq
    {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hoc₁ : OpsConsistent F e₁)
    (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F)
    (hcwf : Factory.ConstrWellFormed F tf)
    (heql : LExpr.eql F e₁ e₂ = some true)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ =
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
    fun_induction LExpr.eql F e₁ e₂ generalizing τ fvarVal with
    | case1 e1 e2 hmod => -- eqModuloMeta = true
      exact eqModuloMeta_true_implies_denote_eq tcInterp opInterp fvarVal vt .nil h₁ h₂ hmod
    | case2 => contradiction -- const vs const, realConst vs realConst: none ≠ some true
    | case3 m1 c1 m2 c2 _he hnotreal hnotmod => -- const vs const, non-real
      split at heql
      · contradiction
      · have hceq : c1 = c2 := by grind
        subst hceq
        rfl
    | case4 => contradiction -- abs vs abs, ty1 ≠ ty2: some false ≠ some true
    | case5 m1 pn1 ty1 body1 m2 pn2 ty2 body2 htyeq hclosed hnotmod ih =>
      -- abs vs abs, same type, both closed, varOpen recurse
      have hty : ty1 = ty2 := by simp [bne_iff_ne] at htyeq; exact htyeq
      subst hty
      -- Invert h₁ to get aty, rty, and body typing
      -- ty1 must be some aty for HasTypeA to hold
      cases ty1 with
      | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
      | some aty =>
        have ⟨rty1, hτ1, hbody1⟩ := HasTypeA.abs_inv h₁
        have ⟨rty2, hτ2, hbody2⟩ := HasTypeA.abs_inv h₂
        have hrty : rty1 = rty2 := by
          have ha: LMonoTy.arrow aty rty1 = LMonoTy.arrow aty rty2 := by
            rw [← hτ1, ← hτ2]
          cases ha; rfl
        subst hrty
        subst hτ1
        -- Unfold denote on both abs expressions
        rw [denote_abs .nil hbody1 h₁]
        rw [denote_abs .nil hbody2 h₂]
        -- Goal: (fun x => denote ... body1 ...) = (fun x => denote ... body2 ...)
        funext x
        -- Define fvarVal' that maps "x" to x
        let fvarVal' : FreeVarVal T tcInterp := fun name sort =>
          if h : name = ⟨"x", default⟩ ∧ sort = LMonoTy.substTyVars vt aty
          then h.2 ▸ x
          else fvarVal name sort
        -- Step 1: bodies are closed
        have hclosed1 : body1.closed = true := by grind
        have hclosed2 : body2.closed = true := by grind
        -- Step 2: change fvarVal to fvarVal' (bodies closed, fvarVal irrelevant)
        have hext1 := @denote_closed_fvarVal_irrel _ tcInterp opInterp vt _ _ _ fvarVal fvarVal' (.cons x .nil) hclosed1 hbody1 hbody1
        have hext2 := @denote_closed_fvarVal_irrel _ tcInterp opInterp vt _ _ _ fvarVal fvarVal' (.cons x .nil) hclosed2 hbody2 hbody2
        rw [hext1, hext2]
        -- Step 3: fvarVal' maps "x" to x
        have hfv'x : fvarVal' ⟨"x", default⟩ (LMonoTy.substTyVars vt aty) = x := by
          simp [fvarVal']
        -- Step 4: use varOpen_denote to convert to denote of varOpen'd bodies
        have hvo1 := varOpen_denote (x := ⟨"x", default⟩) tcInterp opInterp fvarVal' vt hbody1 (varOpen_HasTypeA hbody1)
        have hvo2 := varOpen_denote (x := ⟨"x", default⟩) tcInterp opInterp fvarVal' vt hbody2 (varOpen_HasTypeA hbody2)
        -- hvo1 : denote fvarVal' bvarVal (varOpen body1) = denote fvarVal' (cons (fvarVal' "x" ...) bvarVal) body1
        -- rewrite fvarVal' "x" ... = x
        rw [hfv'x] at hvo1 hvo2
        -- Now hvo1 : denote fvarVal' bvarVal (varOpen body1) = denote fvarVal' (cons x bvarVal) body1
        rw [← hvo1, ← hvo2]
        -- Goal: denote fvarVal' bvarVal (varOpen body1) = denote fvarVal' bvarVal (varOpen body2)
        -- Step 5: apply IH (propagate OpsConsistent through varOpen)
        exact ih fvarVal' (varOpen_HasTypeA hbody1) (varOpen_HasTypeA hbody2)
          (OpsConsistent_varOpen (show OpsConsistent F body1 from hoc₁))
          (OpsConsistent_varOpen (show OpsConsistent F body2 from hoc₂)) heql
    | case6 => contradiction -- abs vs abs, not both closed: none ≠ some true
    | case7 => contradiction -- const vs abs: some false ≠ some true
    | case8 => contradiction -- abs vs const: some false ≠ some true
    | case9 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hnotconstr =>
      -- constructor apps, not both isConstr: none ≠ some true
      have heql' : none = some true := by rw [hcall1, hcall2] at heql; simp [hnotconstr] at heql
      contradiction
    | case10 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hisconstr hdiffname =>
      -- constructor apps, different names: some false ≠ some true
      have heql' : some false = some true := by
        rw [hcall1, hcall2] at heql; simp [hisconstr, hdiffname] at heql
      contradiction
    | case11 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hisconstr hsamename _ _ _ _ ih_args =>
      -- same constructor, fold over args
      -- Step 1: use callOfLFunc_denote on both sides
      obtain ⟨argTys1, ty_op1, m1, name1, h_args1, hty_op1, h_callee1, hdenote1⟩ :=
        callOfLFunc_denote tcInterp opInterp fvarVal vt hcall1 h₁
      obtain ⟨argTys2, ty_op2, m2, name2, h_args2, hty_op2, h_callee2, hdenote2⟩ :=
        callOfLFunc_denote tcInterp opInterp fvarVal vt hcall2 h₂
      -- Step 2: establish name1.name = name2.name
      obtain ⟨_, name1', _, hcallee1', hget1⟩ := Factory.callOfLFunc_getElem? hcall1
      obtain ⟨_, name2', _, hcallee2', hget2⟩ := Factory.callOfLFunc_getElem? hcall2
      -- Connect name1' to name1 via callee equality
      rw [h_callee1] at hcallee1'; cases hcallee1'
      rw [h_callee2] at hcallee2'; cases hcallee2'
      -- Now hget1 : F[name1.name]? = some f1, hget2 : F[name2.name]? = some f2
      have hname1 := Factory.getElem?_name hget1  -- f1.name.name = name1.name
      have hname2 := Factory.getElem?_name hget2  -- f2.name.name = name2.name
      have hsamename' : f1.name.name = f2.name.name := by
        simp [bne_iff_ne] at hsamename; exact hsamename
      have hnames_eq : name1.name = name2.name := by rw [← hname1, ← hname2, hsamename']
      -- Step 3: f1 = f2 (same key in the factory)
      have hf_eq : f1 = f2 := by
        have h := hnames_eq ▸ hget2
        rw [hget1] at h
        exact Option.some.inj h
      subst hf_eq
      rw [hdenote1, hdenote2]
      rw [hnames_eq]
      have hlen1 := h_args1.length_eq.symm.trans (Factory.callOfLFunc_arity hcall1)
      have hlen2 := h_args2.length_eq.symm.trans (Factory.callOfLFunc_arity hcall2)
      have hlen : argTys1.length = argTys2.length := by omega
      subst hty_op1; subst hty_op2
      -- Step 4: simplify heql to get the foldl
      split at heql
      · rename_i _ args1' f1' _ args2' f2' heq1' heq2'
        rw [hcall1] at heq1'; cases heq1'
        rw [hcall2] at heq2'; cases heq2'
        simp at heql
        obtain ⟨hconstr, heql_fold⟩ := heql
        -- Extract OpsConsistent for arguments from the top-level OpsConsistent
        have hoc_args1 := OpsConsistent_callOfLFunc_args hoc₁ hcall1
        have hoc_args2 := OpsConsistent_callOfLFunc_args hoc₂ hcall2
        have hargTys := constr_callOfLFunc_argTys_eq'
          hcall1 hcall2 h_args1 h_args2
          hoc₁ hoc₂ hfwf hcwf hconstr
          ⟨m1, name1, h_callee1⟩ ⟨m2, name2, h_callee2⟩
        subst hargTys
        -- Goal: denoteArgs ... args1 argTys1 h_args1 = denoteArgs ... args2 argTys1 h_args2
        congr 1
        have hpw := eql_foldl_implies_denote_eq_pointwise tcInterp opInterp fvarVal vt
          argTys1 ih_args hoc_args1 hoc_args2 heql_fold
        exact denoteArgs_eq_of_denote_eq tcInterp opInterp fvarVal vt .nil h_args1 h_args2 hpw
      · contradiction
    | case12 e1 e2 hnotmod hnotconst hnotabs hnotconstabs hnotabsconst hnotbothcall =>
      -- callOfLFunc doesn't match both: none ≠ some true
      split at heql
      · have := hnotbothcall _ _ _ _ _ _ ‹_› ‹_›
        contradiction
      · contradiction

/-- If foldl eqlCombine over `attach.zip` returns `some false`, then some
individual pair has `eql = some false`. -/
theorem eqlCombine_attach_zip_some_false
    {F : @Factory T}
    {args1 args2 : List (LExpr T.mono)}
    (h : List.foldl (fun acc x =>
      LExpr.eqlCombine acc (LExpr.eql F x.1.val x.snd)) (some true) (args1.attach.zip args2) = some false)
    : ∃ (i : Nat) (a1 a2 : LExpr T.mono),
        args1[i]? = some a1 ∧ args2[i]? = some a2 ∧
        a1 ∈ args1 ∧
        LExpr.eql F a1 a2 = some false := by
  induction args1 generalizing args2 with
  | nil => simp at h
  | cons x1 rest1 ih =>
    cases args2 with
    | nil => simp at h
    | cons x2 rest2 =>
      simp only [List.attach_cons, List.zip_cons_cons, List.foldl_cons] at h
      have heqlcomb_true : ∀ v, LExpr.eqlCombine (some true) v = v := by
        intro v; unfold LExpr.eqlCombine; cases v with | none => rfl | some b => cases b <;> rfl
      rw [heqlcomb_true] at h
      match heql : LExpr.eql F x1 x2 with
      | some false =>
        exact ⟨0, x1, x2, List.getElem?_cons_zero .., List.getElem?_cons_zero ..,
               List.mem_cons_self .., heql⟩
      | some true =>
        rw [heql] at h
        have heq := foldl_zip_map_subtype_eq rest1.attach rest2
            (fun x => ⟨x.val, List.mem_cons_of_mem x1 x.property⟩)
            (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b))
            (some true) (fun _ => rfl)
        simp only [heq] at h
        have ⟨i', a1, a2, ha1, ha2, hmem, hfeql⟩ := ih h
        exact ⟨i' + 1, a1, a2, by simp [ha1], by simp [ha2],
               List.mem_cons_of_mem _ hmem, hfeql⟩
      | none =>
        rw [heql] at h
        have heq := foldl_zip_map_subtype_eq rest1.attach rest2
            (fun x => ⟨x.val, List.mem_cons_of_mem x1 x.property⟩)
            (fun acc a b => LExpr.eqlCombine acc (LExpr.eql F a b))
            none (fun _ => rfl)
        simp only [heq] at h
        have ⟨j, p, hj, hfeql⟩ := foldl_eqlCombine_none_to_false h
        refine ⟨j + 1, p.1.val, p.2, ?_, ?_, List.mem_cons_of_mem _ p.1.property, hfeql⟩
        · simp only [List.getElem?_cons_succ]; grind
        · simp only [List.getElem?_cons_succ]; grind

/-- If `eql` returns `some false`, then the denotations are not equal.
Restricted to the empty bound-variable context (same as `eql_true`). -/
theorem eql_false_implies_denote_ne
    {F : @Factory T} {tf : @TypeFactory T.IDMeta}
    {e₁ e₂ : LExpr T.mono} {τ : LMonoTy}
    (h₁ : LExpr.HasTypeA [] e₁ τ)
    (h₂ : LExpr.HasTypeA [] e₂ τ)
    (hoc₁ : OpsConsistent F e₁)
    (hoc₂ : OpsConsistent F e₂)
    (hfwf : FactoryWF F)
    (hcwf : Factory.ConstrWellFormed F tf)
    (htfwf : TypeFactoryWF tf)
    (heql : LExpr.eql F e₁ e₂ = some false)
    (hConstrIC : ConstrInterpConsistent tcInterp opInterp F)
    : LExpr.denote tcInterp opInterp fvarVal vt .nil e₁ τ h₁ ≠
      LExpr.denote tcInterp opInterp fvarVal vt .nil e₂ τ h₂ := by
  fun_induction LExpr.eql F e₁ e₂ generalizing τ fvarVal with
  | case1 e1 e2 hmod => -- eqModuloMeta = true → returns some true
    simp at heql
  | case2 => contradiction -- const/const, realConst → returns none
  | case3 m1 c1 m2 c2 _he hnotreal hnotmod => -- const/const, non-real
    split at heql
    · contradiction
    · have hneq : c1 ≠ c2 := by grind
      have hty1 : τ = c1.ty := by cases h₁; rfl
      have hty2 : τ = c2.ty := by cases h₂; rfl
      have htyeq : c1.ty = c2.ty := by rw [← hty1, ← hty2]
      intro heq
      have hdenote_eq : (htyeq ▸ denoteConst tcInterp vt c1 : TyDenote tcInterp vt c2.ty) =
          denoteConst tcInterp vt c2 := by
        subst hty1
        rw [denote_const tcInterp opInterp fvarVal vt .nil h₁,
            denote_const tcInterp opInterp fvarVal vt .nil h₂] at heq
        grind
      exact hneq (denoteConst_injective tcInterp vt c1 c2 htyeq hdenote_eq)
  | case4 m1 pn1 ty1 body1 m2 pn2 ty2 body2 htyneq hnotmod => -- abs/abs, ty1 ≠ ty2
    -- Vacuous: HasTypeA forces ty1 = ty2
    have htyneq' : ty1 ≠ ty2 := by simp [bne_iff_ne] at htyneq; exact htyneq
    exfalso
    apply htyneq'
    cases h₁ with | abs hbody1 => cases h₂ with | abs hbody2 => rfl
  | case5 m1 pn1 ty1 body1 m2 pn2 ty2 body2 htyeq hclosed hnotmod ih =>
    -- abs/abs, same type, both closed, recurse returns some false
    have hty : ty1 = ty2 := by simp [bne_iff_ne] at htyeq; exact htyeq
    subst hty
    cases ty1 with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some aty =>
      have ⟨rty1, hτ1, hbody1⟩ := HasTypeA.abs_inv h₁
      have ⟨rty2, hτ2, hbody2⟩ := HasTypeA.abs_inv h₂
      have hrty : rty1 = rty2 := by
        have ha : LMonoTy.arrow aty rty1 = LMonoTy.arrow aty rty2 := by rw [← hτ1, ← hτ2]
        cases ha; rfl
      subst hrty; subst hτ1
      rw [denote_abs .nil hbody1 h₁, denote_abs .nil hbody2 h₂]
      intro habs_eq
      -- Apply IH on varOpen'd bodies
      have hih := ih fvarVal (varOpen_HasTypeA hbody1) (varOpen_HasTypeA hbody2)
        (OpsConsistent_varOpen (show OpsConsistent F body1 from hoc₁))
        (OpsConsistent_varOpen (show OpsConsistent F body2 from hoc₂)) heql
      apply hih
      have hvo1 := varOpen_denote (x := ⟨"x", default⟩) tcInterp opInterp fvarVal vt hbody1 (varOpen_HasTypeA hbody1)
      have hvo2 := varOpen_denote (x := ⟨"x", default⟩) tcInterp opInterp fvarVal vt hbody2 (varOpen_HasTypeA hbody2)
      rw [hvo1, hvo2]
      exact congrFun habs_eq _
  | case6 => contradiction -- abs/abs, not both closed → returns none
  | case7 m1 c m2 pn ty body => -- const/abs → vacuous (base type ≠ arrow type)
    exfalso
    have hty1 : τ = c.ty := by cases h₁; rfl
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₂) (by simp [LExpr.typeCheck])
    | some aty =>
      have ⟨rty, hty2, _⟩ := HasTypeA.abs_inv h₂
      rw [hty1] at hty2
      cases c <;> simp [LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.string, LMonoTy.real, LMonoTy.arrow] at hty2
  | case8 m1 pn ty body m2 c => -- abs/const → vacuous
    exfalso
    have hty2 : τ = c.ty := by cases h₂; rfl
    cases ty with
    | none => exact absurd (LExpr.HasTypeA_to_typeCheck h₁) (by simp [LExpr.typeCheck])
    | some aty =>
      have ⟨rty, hty1, _⟩ := HasTypeA.abs_inv h₁
      rw [hty2] at hty1
      cases c <;> simp [LConst.ty, LMonoTy.int, LMonoTy.bool, LMonoTy.string, LMonoTy.real, LMonoTy.arrow] at hty1
  | case9 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hnotconstr =>
    -- both callOfLFunc, not both isConstr → returns none
    rw [hcall1, hcall2] at heql; simp [hnotconstr] at heql
  | case10 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hisconstr hdiffname =>
    -- Different constructors
    have hconstr1 : f1.isConstr = true := by simp at hisconstr; exact hisconstr.1
    have hconstr2 : f2.isConstr = true := by simp at hisconstr; exact hisconstr.2
    have hdiff : f1.name.name ≠ f2.name.name := by simp [bne_iff_ne] at hdiffname; exact hdiffname
    exact callOfLFunc_constr_disjoint_denote tcInterp opInterp fvarVal vt
      h₁ h₂ hcall1 hcall2 hconstr1 hconstr2 hdiff hoc₁ hoc₂ hfwf hcwf htfwf hConstrIC
  | case11 e1 e2 hnotmod callee1 args1 f1 callee2 args2 f2 hcall1 hcall2 hisconstr hsamename _ _ _ _ ih_args =>
    -- Same constructor, fold returns some false
    have hconstr1 : f1.isConstr = true := by simp at hisconstr; exact hisconstr.1
    have hconstr2 : f2.isConstr = true := by simp at hisconstr; exact hisconstr.2
    have hsamename' : f1.name.name = f2.name.name := by simp [bne_iff_ne] at hsamename; exact hsamename
    -- Establish f1 = f2
    obtain ⟨_, name1, _, hcallee1, hget1⟩ := Factory.callOfLFunc_getElem? hcall1
    obtain ⟨_, name2, _, hcallee2, hget2⟩ := Factory.callOfLFunc_getElem? hcall2
    have hname1 := Factory.getElem?_name hget1
    have hname2 := Factory.getElem?_name hget2
    have hnames_eq : name1.name = name2.name := by rw [← hname1, ← hname2, hsamename']
    have hf_eq : f1 = f2 := by
      have h := hnames_eq ▸ hget2; rw [hget1] at h; exact Option.some.inj h
    subst hf_eq
    -- By injectivity, equal denotes implies equal arg denotes
    intro heq_denote
    have hinj := callOfLFunc_constr_injective_denote tcInterp opInterp fvarVal vt
      h₁ h₂ hcall1 hcall2 hconstr1 hoc₁ hoc₂ hfwf hcwf hConstrIC heq_denote
    -- Extract an arg pair with eql = some false
    rw [hcall1, hcall2] at heql
    simp at heql
    obtain ⟨_, heql_fold⟩ := heql
    obtain ⟨i, a1, a2, ha1, ha2, hmem1, heql_i⟩ :=
      eqlCombine_attach_zip_some_false heql_fold
    -- Get arg typing from callOfLFunc_denote
    obtain ⟨argTys1, ty_op1, m_op1, name_op1, h_args1, hty_op1, hcallee_op1, _⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall1 h₁
    obtain ⟨argTys2, ty_op2, m_op2, name_op2, h_args2, hty_op2, hcallee_op2, _⟩ :=
      callOfLFunc_denote tcInterp opInterp fvarVal vt hcall2 h₂
    obtain ⟨σ, hσ, ha1_ty⟩ := List.Forall₂.getElem?_some h_args1 ha1
    obtain ⟨σ', hσ', ha2_ty⟩ := List.Forall₂.getElem?_some h_args2 ha2
    -- Get argTys1 = argTys2
    have hargTys_eq : argTys1 = argTys2 :=
      constr_callOfLFunc_argTys_eq' hcall1 hcall2 h_args1 h_args2 hoc₁ hoc₂ hfwf hcwf hconstr1
        ⟨m_op1, name_op1, hty_op1 ▸ hcallee_op1⟩
        ⟨m_op2, name_op2, hty_op2 ▸ hcallee_op2⟩
    have hσ_eq : σ = σ' := by rw [hargTys_eq] at hσ; rw [hσ] at hσ'; exact Option.some.inj hσ'
    subst hσ_eq
    -- IH gives denote a1 ≠ denote a2, injectivity gives equality: contradiction
    have hoc_args1 := OpsConsistent_callOfLFunc_args hoc₁ hcall1
    have hoc_args2 := OpsConsistent_callOfLFunc_args hoc₂ hcall2
    have hmem2 : a2 ∈ args2 := by rw [List.mem_iff_getElem?]; exact ⟨i, ha2⟩
    have hne := ih_args a1 hmem1 a2 fvarVal ha1_ty ha2_ty (hoc_args1 a1 hmem1) (hoc_args2 a2 hmem2) heql_i
    exact hne (hinj i a1 a2 σ ha1 ha2 ha1_ty ha2_ty)
  | case12 e1 e2 hnotmod hnotconst hnotabs hnotconstabs hnotabsconst hnotbothcall =>
    -- callOfLFunc doesn't match both → returns none
    split at heql
    · have := hnotbothcall _ _ _ _ _ _ ‹_› ‹_›; contradiction
    · contradiction

end

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WP
public import Strata.Transform.Passive.Lang
public import Strata.Transform.Passive.SimulationProps
public import Strata.Transform.Passive.WellTyped
import Strata.DL.Imperative.BigStep.SemProps
import Strata.Util.ExceptProps

/-! # Evaluation of the resolved expressions of the guarded program

Inversions of `resolveE`, which resolves the expressions (`WExpr`) of the guarded program, and
the evaluation of what it returns: a loop-free expression with its renaming evaluates like the
original in a store where each renamed variable holds the value of its target, and the
expressions built from a reach context (`kExpr`, `kIte`, `kAnd`, `kImp`) or from Boolean
operands (`WExpr.not`, `WExpr.or`, `WExpr.and`, `disjW`) evaluate to the expected value when
the context holds or fails (`RE.Holds`, `RE.Fails`) or the operands evaluate to `tt` or `ff`.

Key theorems: `resolveE_ite`, `resolveE_user_eq`, `ev_resolveE_user`, `ev_kExpr_holds`,
`ev_kExpr_fails`, `ev_kIte_holds`, `ev_kIte_fails`, `ev_disjW_tt`, `ev_disjW_ff`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iB : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iBo : HasBool P] [iFv : HasFvar P] [iSu : HasSubstFvar P] [iId : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iFs : HasFvars P]
  [iW : WPLang P] [iIL : WPIteLang P]
  [iLV : LawfulHasVal P] [iOp : HasOps P] [iLF : LawfulHasFvar P] [iLFs : LawfulHasFvars P]
omit iIL
omit iLB iId iLI iLV iOp iLF iLFs

variable {F : P.Factory} {σ : SemanticStore P} {tys : Std.HashMap P.Ident P.Ty}
  {tyOf : Std.HashMap P.Ident P.Ident} {x : P.Expr} {κ : RE P} {a b c t e : WExpr P} {v : P.Val}

/-! ## Inversions of resolution -/

/-- A Boolean literal resolves to `tt` or `ff`. -/
theorem resolveE_lit (b : Bool) : resolveE tys tyOf (.lit b) = .ok (if b then tt else ff) := rfl

/-- A variable resolves to the variable annotated with a type. -/
theorem resolveE_var {r : P.Ident} (h : resolveE tys tyOf (.var r) = .ok x) :
    ∃ ty, x = HasFvar.mkVar r (some ty) := by grind [resolveE, Except.bind_is_ok, Except.pure_is_ok]

/-- A conditional resolves exactly when its three parts do, to the conditional of their
    resolutions. -/
theorem resolveE_ite :
    resolveE tys tyOf (.ite c t e) = .ok x ↔ ∃ c' t' e', resolveE tys tyOf c = .ok c' ∧
      resolveE tys tyOf t = .ok t' ∧ resolveE tys tyOf e = .ok e' ∧
      x = WPOps.ite c' t' e' := by grind [resolveE, Except.bind_is_ok, Except.pure_is_ok]

include iLB in
/-- The hash map that resolution builds from a renaming `ren`, starting from a map `h0` that
    looks up like the substitution of the entries `acc`, looks up like the substitution of
    `w.reverse ++ acc`, where `w` is `ren` with a type attached to each entry. -/
private theorem foldlM_ren (tys : Std.HashMap P.Ident P.Ty) (tyOf : Std.HashMap P.Ident P.Ident) :
    ∀ (ren : List (P.Ident × P.Ident)) (h0 h : Std.HashMap P.Ident P.Expr)
      (acc : List (P.Ident × P.Ident × Option P.Ty)),
    (∀ x, h0[x]? = Map.find? (acc.map fun (x, y, ty) => (x, HasFvar.mkVar y ty)) x) →
    ren.foldlM (init := h0) (fun h (y, y') => do
      pure (h.insert y (HasFvar.mkVar y' (some (← tyOfName tys tyOf y'))))) = Except.ok h →
    ∃ w : List (P.Ident × P.Ident × Option P.Ty), w.map (fun q => (q.1, q.2.1)) = ren ∧
      ∀ x, h[x]? = Map.find? ((w.reverse ++ acc).map fun (x, y, ty) => (x, HasFvar.mkVar y ty)) x
  | [], h0, h, acc, h0e, hf => ⟨[], rfl, Except.ok.inj hf ▸ h0e⟩
  | (y, y') :: ps, h0, h, acc, h0e, hf => by
    simp only [List.foldlM_cons, bind, Except.bind, pure, Except.pure] at hf
    rcases hty : tyOfName tys tyOf y' with _ | ty <;> simp only [hty, reduceCtorEq] at hf
    obtain ⟨w, hw, hx⟩ := foldlM_ren tys tyOf ps _ h ((y, y', some ty) :: acc)
      (fun x => by simp [Std.HashMap.getElem?_insert, Map.find?, h0e]) hf
    exact ⟨(y, y', some ty) :: w, by simp [hw], by simpa using hx⟩

include iLB in
/-- A loop-free expression `e` with its renaming `ren` resolves to `e` under a substitution
    `wsub` whose entries are entries of `ren` with a type attached, and which renames every
    variable that `ren` renames. -/
theorem resolveE_user_eq {e e' : P.Expr} {ren : List (P.Ident × P.Ident)}
    (h : resolveE tys tyOf (.user e ren) = .ok e') :
    ∃ wsub : List (P.Ident × P.Ident × Option P.Ty), (∀ q ∈ wsub, (q.1, q.2.1) ∈ ren) ∧
      (∀ p ∈ ren, ∃ q ∈ wsub, q.1 = p.1) ∧ e' = substObl wsub e := by
  cases ren with
  | nil => exact ⟨[], nofun, nofun, Except.ok.inj h ▸ (WPLang.substFvars_nil _).symm⟩
  | cons p ps =>
    simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨hm, hf, rfl⟩ := h
    obtain ⟨w, hwr, hw⟩ := foldlM_ren tys tyOf _ {} hm [] (by simp [Map.find?]) hf
    refine ⟨w.reverse, fun q hq => hwr ▸ List.mem_map_of_mem (List.mem_reverse.1 hq),
      fun p hp => ?_, WPLang.substFn_eq _ _ _ fun x _ => by simpa using hw x⟩
    exact (List.mem_map.1 (hwr ▸ hp)).imp fun q ⟨hq, e⟩ => ⟨List.mem_reverse.2 hq, e ▸ rfl⟩

include iLB iOp iLF in
/-- A resolved loop-free expression evaluates in `σL` like the original in `σ`, when each
    entry `(y, y')` of its renaming has `y` defined in `σ` and `y'` holding `y`'s value in
    `σL`, the free variables it does not rename agree, both stores hold values, and the
    factory satisfies the factory laws (`WellFormedSemanticEvalBase`). -/
theorem ev_resolveE_user (hF : WellFormedSemanticEvalBase F) {σL : SemanticStore P}
    (hC : WellFormedStore σ F)
    (hCL : WellFormedStore σL F) {e e' : P.Expr} {ren : List (P.Ident × P.Ident)}
    (h : resolveE tys tyOf (.user e ren) = .ok e')
    (hren : ∀ p ∈ ren, σL p.2 = σ p.1 ∧ (σ p.1).isSome)
    (hrest : ∀ y ∈ exprFV e, (∀ p ∈ ren, p.1 ≠ y) → σL y = σ y) :
    P.eval F σL e' = P.eval F σ e := by
  obtain ⟨wsub, hsub, hcov, rfl⟩ := resolveE_user_eq h
  refine ev_substVars hF hCL hC _ _ (fun k v hk => ?_) fun x hx hn => ?_
  · obtain ⟨⟨k', y, ty⟩, hq, ⟨⟩⟩ := List.mem_map.1 (Map.find?_mem _ _ _ hk)
    exact ⟨y, by cases ty <;> first | exact .inl rfl | exact .inr ⟨_, rfl⟩, hren _ (hsub _ hq)⟩
  · exact hrest x (mem_exprFV.2 hx) fun pr hp hx => (hcov pr hp).elim fun _ ⟨hq, e⟩ =>
      Map.findNone_eq_notmem_mapfst.2 hn (e.trans hx ▸ List.mem_map_of_mem (List.mem_map_of_mem hq))

/-! ## Evaluation of resolved conditions

Each statement assumes that resolution succeeds; an operand is described by the value of
every resolution of it. -/

omit iDE iB iFv iSu iHa iFs iW in
/-- The variables of a reachability condition that holds are Boolean. -/
theorem RE.Holds.bools {r : RE P} (h : r.Holds F σ) :
    ∀ y ∈ RE.vars r, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F) := by
  cases r <;> simp_all [RE.Holds, RE.vars]

/-- The resolutions of the operand `e` evaluate to a Boolean value. -/
@[expose] def ResBool (F : P.Factory) (σ : SemanticStore P) (tys : Std.HashMap P.Ident P.Ty)
    (tyOf : Std.HashMap P.Ident P.Ident) (e : WExpr P) : Prop :=
  ∀ e', resolveE tys tyOf e = .ok e' →
    P.eval F σ e' = some (HasBool.ttVal F) ∨ P.eval F σ e' = some (HasBool.ffVal F)

/-- The resolutions of the operand `e` evaluate to a value of type `ty`. -/
@[expose] def ResTy (F : P.Factory) (σ : SemanticStore P) (tys : Std.HashMap P.Ident P.Ty)
    (tyOf : Std.HashMap P.Ident P.Ident) (e : WExpr P) (ty : P.Ty) : Prop :=
  ∀ e', resolveE tys tyOf e = .ok e' → ∃ w, P.eval F σ e' = some w ∧ HasVal.valueOfTy F w ty

omit iDE iB iFv iSu iHa iFs iW in
/-- A Boolean value has the Boolean type. -/
theorem valueOfTy_of_bool {w : P.Val} (hb : w = HasBool.ttVal F ∨ w = HasBool.ffVal F) :
    HasVal.valueOfTy F w HasBool.boolTy :=
  hb.elim (· ▸ (HasBool.boolIsValOfTy F).1) (· ▸ (HasBool.boolIsValOfTy F).2)

/-- Operands resolving to Boolean values resolve to values of the Boolean type. -/
theorem ResBool.ty {e : WExpr P} (h : ResBool F σ tys tyOf e) :
    ResTy F σ tys tyOf e HasBool.boolTy := fun _ he =>
  (h _ he).elim (fun h => ⟨_, h, valueOfTy_of_bool (.inl rfl)⟩)
    fun h => ⟨_, h, valueOfTy_of_bool (.inr rfl)⟩

include iLB iOp iLF in
/-- **A typed loop-free expression evaluates where its renaming is read.**  The resolution of a
    loop-free expression `e` typed at `ty` (under the typing predicate of `tE`) evaluates in `σL`
    to a value of type `ty` when `σL` relates to a store `σ` as in `ev_resolveE_user` and `σ`
    holds at each annotated free-variable occurrence of `e` a value of the annotated type. -/
theorem resTy_user (tE : TypedEval P) (hF : WellFormedSemanticEvalBase F) {σL : SemanticStore P}
    (hC : WellFormedStore σ F) (hCL : WellFormedStore σL F) {e : P.Expr} {ty : P.Ty}
    {ren : List (P.Ident × P.Ident)} (he : tE.Typ e ty)
    (hren : ∀ p ∈ ren, σL p.2 = σ p.1 ∧ (σ p.1).isSome)
    (hrest : ∀ y ∈ exprFV e, (∀ p ∈ ren, p.1 ≠ y) → σL y = σ y)
    (hval : ∀ p ∈ HasFvars.getTypedFvars e, ∃ v, σ p.1 = some v ∧ HasVal.valueOfTy F v p.2) :
    ResTy F σL tys tyOf (.user e ren) ty := fun _ h =>
  ev_resolveE_user hF hC hCL h hren hrest ▸ tE.eval_of_typed he hval

/-- Operands resolving to values of the Boolean type resolve to Boolean values. -/
theorem ResTy.bool (tE : TypedEval P) {e : WExpr P} (h : ResTy F σ tys tyOf e HasBool.boolTy) :
    ResBool F σ tys tyOf e := fun _ he =>
  (h _ he).elim fun _ ⟨hv, hb⟩ => (tE.valueOfTy_bool hb).imp (hv.trans <| congrArg _ ·)
    (hv.trans <| congrArg _ ·)

include iIL in
/-- A resolved conditional whose condition evaluates to `tt` evaluates like its `then` part,
    when that part's value and the `else` part's values have one type. -/
private theorem ev_res_ite_tt {ty : P.Ty} (h : resolveE tys tyOf (.ite c t e) = .ok x)
    (hc : ∀ c', resolveE tys tyOf c = .ok c' → P.eval F σ c' = some (HasBool.ttVal F))
    (ht : ∀ t', resolveE tys tyOf t = .ok t' → P.eval F σ t' = some v)
    (hv : HasVal.valueOfTy F v ty) (he : ResTy F σ tys tyOf e ty) :
    P.eval F σ x = some v := by
  obtain ⟨c', t', e', hc', ht', he', rfl⟩ := resolveE_ite.1 h
  obtain ⟨w, hw, hwty⟩ := he _ he'
  exact WPIteLang.ev_ite_true (hc _ hc') (ht _ ht') hw hv hwty

include iIL in
/-- A resolved conditional whose condition evaluates to `ff` evaluates like its `else` part,
    when that part's value and the `then` part's values have one type. -/
private theorem ev_res_ite_ff {ty : P.Ty} (h : resolveE tys tyOf (.ite c t e) = .ok x)
    (hc : ∀ c', resolveE tys tyOf c = .ok c' → P.eval F σ c' = some (HasBool.ffVal F))
    (he : ∀ e', resolveE tys tyOf e = .ok e' → P.eval F σ e' = some v)
    (hv : HasVal.valueOfTy F v ty) (ht : ResTy F σ tys tyOf t ty) :
    P.eval F σ x = some v := by
  obtain ⟨c', t', e', hc', ht', he', rfl⟩ := resolveE_ite.1 h
  obtain ⟨w, hw, hwty⟩ := ht _ ht'
  exact WPIteLang.ev_ite_false (hc _ hc') hw (he _ he') hv hwty

omit iOp iLF
omit iDE iB iFv iSu iHa iFs iW iLV in
/-- The variables of a false reachability condition are Boolean, given that the negated variable
    of an `andNeg` condition is. -/
theorem RE.Fails.bools {r : RE P} (h : r.Fails F σ)
    (hb : ∀ q g, r = .andNeg q g → σ g = some (HasBool.ttVal F) ∨ σ g = some (HasBool.ffVal F)) :
    ∀ y ∈ RE.vars r, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F) := by
  cases r <;> simp only [RE.vars, RE.Fails, List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;>
    grind

/-- The resolved literal `true` evaluates to `tt`. -/
private theorem ev_res_true (hF : WellFormedSemanticEvalBase F) (h : resolveE tys tyOf
    (.lit true) = .ok x) :
    P.eval F σ x = some (HasBool.ttVal F) := Except.ok.inj h ▸ hF.val.eval_tt σ

/-- The resolved literal `false` evaluates to `ff`. -/
private theorem ev_res_false (hF : WellFormedSemanticEvalBase F) (h : resolveE tys tyOf
    (.lit false) = .ok x) :
    P.eval F σ x = some (HasBool.ffVal F) := Except.ok.inj h ▸ hF.val.eval_ff σ

/-- A literal resolves to Boolean values. -/
theorem resBool_lit (hF : WellFormedSemanticEvalBase F) (b : Bool) :
    ResBool F σ tys tyOf (.lit b) := fun _ h => by
  cases b
  · exact .inr (ev_res_false hF h)
  · exact .inl (ev_res_true hF h)

include iIL in
/-- `a ∨ b` evaluates like `b` when `a` evaluates to `ff` and `b` to a Boolean. -/
theorem ev_or_ff (hF : WellFormedSemanticEvalBase F) (h : resolveE tys tyOf (a.or b) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ffVal F))
    (hb : ∀ b', resolveE tys tyOf b = .ok b' → P.eval F σ b' = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) : P.eval F σ x = some v :=
  ev_res_ite_ff h ha hb (valueOfTy_of_bool hv) (resBool_lit hF true).ty

include iIL in
/-- `a ∧ b` evaluates like `b` when `a` evaluates to `tt` and `b` to a Boolean. -/
theorem ev_and_tt (hF : WellFormedSemanticEvalBase F) (h : resolveE tys tyOf (a.and b) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ttVal F))
    (hb : ∀ b', resolveE tys tyOf b = .ok b' → P.eval F σ b' = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) : P.eval F σ x = some v :=
  ev_res_ite_tt h ha hb (valueOfTy_of_bool hv) (resBool_lit hF false).ty

include iIL in
/-- `¬ a` evaluates to `ff` when `a` evaluates to `tt`. -/
theorem ev_not_tt (hF : WellFormedSemanticEvalBase F) {a : WExpr P}
    (h : resolveE tys tyOf a.not = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ttVal F)) :
    P.eval F σ x = some (HasBool.ffVal F) := by
  rcases a with _ | _ | ⟨_ | _⟩ | _ <;> first
    | exact ev_res_ite_tt h ha (fun _ => ev_res_false hF) (valueOfTy_of_bool (.inr rfl))
        (resBool_lit hF true).ty
    | exact ev_res_false hF h
    | exact (HasBool.ttVal_ne_ffVal F
        (Option.some.inj ((hF.val.eval_ff σ).symm.trans (ha _ rfl))).symm).elim

include iIL in
/-- `¬ a` evaluates to `tt` when `a` evaluates to `ff`. -/
theorem ev_not_ff (hF : WellFormedSemanticEvalBase F) {a : WExpr P}
    (h : resolveE tys tyOf a.not = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ffVal F)) :
    P.eval F σ x = some (HasBool.ttVal F) := by
  rcases a with _ | _ | ⟨_ | _⟩ | _ <;> first
    | exact ev_res_ite_ff h ha (fun _ => ev_res_true hF) (valueOfTy_of_bool (.inl rfl))
        (resBool_lit hF false).ty
    | exact ev_res_true hF h
    | exact (HasBool.ttVal_ne_ffVal F
        (Option.some.inj ((hF.val.eval_tt σ).symm.trans (ha _ rfl)))).elim

include iIL in
/-- `a ∨ b` evaluates to `tt` when `a` evaluates to `tt` and `b` to a Boolean. -/
theorem ev_or_tt (hF : WellFormedSemanticEvalBase F) {a b : WExpr P} (h : resolveE tys tyOf
    (a.or b) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ttVal F))
    (hb : ResBool F σ tys tyOf b) : P.eval F σ x = some (HasBool.ttVal F) :=
  ev_res_ite_tt h ha (fun _ => ev_res_true hF) (valueOfTy_of_bool (.inl rfl)) hb.ty

include iIL in
/-- `a ∧ b` evaluates to `ff` when `a` evaluates to `ff` and `b` to a Boolean. -/
theorem ev_and_ff (hF : WellFormedSemanticEvalBase F) {a b : WExpr P} (h : resolveE tys tyOf
    (a.and b) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ffVal F))
    (hb : ResBool F σ tys tyOf b) : P.eval F σ x = some (HasBool.ffVal F) :=
  ev_res_ite_ff h ha (fun _ => ev_res_false hF) (valueOfTy_of_bool (.inr rfl)) hb.ty

include iIL in
/-- The disjunction of Boolean operands evaluates to a Boolean. -/
theorem resBool_disjW (hF : WellFormedSemanticEvalBase F) {as : List (WExpr P)}
    (hall : ∀ a ∈ as, ResBool F σ tys tyOf a) : ResBool F σ tys tyOf (disjW as) := by
  induction as using disjW.induct with
  | case1 => exact resBool_lit hF false
  | case2 a => exact hall a List.mem_cons_self
  | case3 a as hne ih =>
    intro x h
    obtain ⟨a', t', d', ha', ht', hd', rfl⟩ := resolveE_ite.1 (disjW.eq_3 a as hne ▸ h)
    have hd := ih (fun c hc => hall c (.tail _ hc)) _ hd'
    rcases hall a List.mem_cons_self a' ha' with hat | haf
    · exact .inl (ev_ite_true_b hat (ev_res_true hF ht') (.inl rfl) hd)
    · rcases hd with hd | hd
      · exact .inl (ev_ite_false_b haf hd (.inl rfl) (.inl (ev_res_true hF ht')))
      · exact .inr (ev_ite_false_b haf hd (.inr rfl) (.inl (ev_res_true hF ht')))

include iIL in
/-- The disjunction of Boolean operands (each evaluating to `tt` or `ff`) evaluates to `tt`
    when one of them evaluates to `tt`. -/
theorem ev_disjW_tt (hF : WellFormedSemanticEvalBase F) {as : List (WExpr P)}
    (hall : ∀ a ∈ as, ∀ a', resolveE tys tyOf a = .ok a' →
      P.eval F σ a' = some (HasBool.ttVal F) ∨ P.eval F σ a' = some (HasBool.ffVal F))
    (hex : ∃ a ∈ as, ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ttVal F))
    (h : resolveE tys tyOf (disjW as) = .ok x) : P.eval F σ x = some (HasBool.ttVal F) := by
  induction as using disjW.induct generalizing x with
  | case1 => exact absurd hex nofun
  | case2 a => exact hex.elim fun _ ⟨ha, h'⟩ => (List.mem_singleton.1 ha ▸ h') _ h
  | case3 a as hne ih =>
    obtain ⟨a', t', d', ha', ht', hd', rfl⟩ := resolveE_ite.1 (disjW.eq_3 a as hne ▸ h)
    have hd := resBool_disjW hF (fun c hc => hall c (.tail _ hc)) _ hd'
    rcases hall a List.mem_cons_self a' ha' with hat | haf
    · exact ev_ite_true_b hat (ev_res_true hF ht') (.inl rfl) hd
    refine ev_ite_false_b haf (ih (fun c hc => hall c (.tail _ hc)) ?_ hd') (.inl rfl)
      (.inl (ev_res_true hF ht'))
    grind [HasBool.ttVal_ne_ffVal]

include iIL in
/-- The disjunction of operands that all evaluate to `ff` evaluates to `ff`. -/
theorem ev_disjW_ff (hF : WellFormedSemanticEvalBase F) {as : List (WExpr P)}
    (hall : ∀ a ∈ as, ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some (HasBool.ffVal F))
    (h : resolveE tys tyOf (disjW as) = .ok x) : P.eval F σ x = some (HasBool.ffVal F) := by
  induction as using disjW.induct generalizing x with
  | case1 => exact ev_res_false hF h
  | case2 a => exact hall a List.mem_cons_self _ h
  | case3 a as hne ih =>
    exact ev_or_ff hF (disjW.eq_3 a as hne ▸ h) (hall a List.mem_cons_self) (fun _ =>
      ih fun c hc => hall c (.tail _ hc)) (.inr rfl)

include iOp iLF
/-- A resolved variable evaluates to its value in a value-valued store. -/
theorem ev_res_var (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {r : P.Ident}
    {v : P.Val}
    (hr : σ r = some v) (h : resolveE tys tyOf (.var r) = .ok x) : P.eval F σ x = some v := by
  obtain ⟨ty, rfl⟩ := resolveE_var h
  exact ev_var hF.var hC hr

/-- A variable holding a Boolean resolves to Boolean values. -/
theorem resBool_var (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {r : P.Ident}
    (hr : σ r = some (HasBool.ttVal F) ∨ σ r = some (HasBool.ffVal F)) :
    ResBool F σ tys tyOf (.var r) := fun _ h => hr.imp (ev_res_var hF hC · h) (ev_res_var hF hC · h)

include iIL in
/-- `ite(κ, t, e)` for a reach context `κ` that holds evaluates like `t`, when the value of `t`
    and the values of `e` have one type. -/
theorem ev_kIte_holds (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Holds F σ) {t e : WExpr P} {v : P.Val} {ty : P.Ty}
    (h : resolveE tys tyOf (kIte κ t e) = .ok x)
    (ht : ∀ t', resolveE tys tyOf t = .ok t' → P.eval F σ t' = some v)
    (hv : HasVal.valueOfTy F v ty) (he : ResTy F σ tys tyOf e ty) :
    P.eval F σ x = some v := by
  cases κ
  · exact ht _ h
  · exact ev_res_ite_tt h (fun _ => ev_res_var hF hC hκ) ht hv he
  · exact ev_res_ite_ff h (fun _ => ev_res_var hF hC hκ) ht hv he
  · exact ev_res_ite_tt h (fun _ => ev_res_var hF hC hκ.1)
      (fun _ h' => ev_res_ite_ff h' (fun _ => ev_res_var hF hC hκ.2) ht hv he) hv he

include iIL in
/-- `ite(κ, t, e)` for a false reach context `κ` evaluates like `e`, when the value of `e` and
    the values of `t` have one type and the variables of `κ` hold Booleans. -/
theorem ev_kIte_fails (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Fails F σ) {t e : WExpr P} {v : P.Val} {ty : P.Ty}
    (h : resolveE tys tyOf (kIte κ t e) = .ok x)
    (he : ∀ e', resolveE tys tyOf e = .ok e' → P.eval F σ e' = some v)
    (hv : HasVal.valueOfTy F v ty) (ht : ResTy F σ tys tyOf t ty)
    (hκb : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
    P.eval F σ x = some v := by
  cases κ <;> simp only [RE.Fails] at hκ
  · exact ev_res_ite_ff h (fun _ => ev_res_var hF hC hκ) he hv ht
  · exact ev_res_ite_tt h (fun _ => ev_res_var hF hC hκ) he hv ht
  · rename_i q g
    have hg := hκb g (by simp [RE.vars])
    have heT : ResTy F σ tys tyOf e ty := fun _ h' => ⟨v, he _ h', hv⟩
    have hie : ResTy F σ tys tyOf (.ite (.var g) e t) ty := fun _ h' => by
      rcases hg with hg | hg
      · exact ⟨v, ev_res_ite_tt h' (fun _ => ev_res_var hF hC hg) he hv ht, hv⟩
      · obtain ⟨c', e', t', -, -, ht', -⟩ := resolveE_ite.1 h'
        obtain ⟨w, hw, hwty⟩ := ht _ ht'
        have hdet : ∀ t'', resolveE tys tyOf t = .ok t'' → t'' = t' :=
          fun _ h'' => Except.ok.inj (h''.symm.trans ht')
        exact ⟨w, ev_res_ite_ff h' (fun _ => ev_res_var hF hC hg)
          (fun _ h'' => hdet _ h'' ▸ hw) hwty heT, hwty⟩
    rcases hκ with ⟨hq, -⟩ | ⟨hq, hg⟩
    · exact ev_res_ite_ff h (fun _ => ev_res_var hF hC hq) he hv hie
    · exact ev_res_ite_tt h (fun _ => ev_res_var hF hC hq)
        (fun _ h' => ev_res_ite_tt h' (fun _ => ev_res_var hF hC hg) he hv ht) hv heT

include iIL in
/-- `κ ∧ a` for a reach context `κ` that holds evaluates like `a`, when `a` is Boolean. -/
theorem ev_kAnd_holds (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Holds F σ) {a : WExpr P} {v : P.Val} (h : resolveE tys tyOf (kAnd κ a) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) : P.eval F σ x = some v :=
  ev_kIte_holds hF hC hκ h ha (valueOfTy_of_bool hv) (resBool_lit hF false).ty

include iIL in
/-- `κ ⟹ a` for a reach context `κ` that holds evaluates like `a`, when `a` is Boolean. -/
theorem ev_kImp_holds (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Holds F σ) {a : WExpr P} {v : P.Val} (h : resolveE tys tyOf (kImp κ a) = .ok x)
    (ha : ∀ a', resolveE tys tyOf a = .ok a' → P.eval F σ a' = some v)
    (hv : v = HasBool.ttVal F ∨ v = HasBool.ffVal F) : P.eval F σ x = some v :=
  ev_kIte_holds hF hC hκ h ha (valueOfTy_of_bool hv) (resBool_lit hF true).ty

include iIL in
/-- The Boolean value of a reach context that holds evaluates to `tt`. -/
theorem ev_kExpr_holds (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Holds F σ) (h : resolveE tys tyOf (kExpr κ) = .ok x) :
    P.eval F σ x = some (HasBool.ttVal F) := by
  cases κ <;> first | exact ev_res_var hF hC hκ h
                    | exact ev_kIte_holds (e := .lit false) hF hC hκ h (fun _ => ev_res_true hF)
                        (valueOfTy_of_bool (.inl rfl)) (resBool_lit hF false).ty

include iIL in
/-- The Boolean value of a false reach context whose variables hold Booleans evaluates to
    `ff`. -/
theorem ev_kExpr_fails (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Fails F σ)
    (hκb : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F))
    (h : resolveE tys tyOf (kExpr κ) = .ok x) : P.eval F σ x = some (HasBool.ffVal F) := by
  cases κ <;> first | exact ev_res_var hF hC hκ h
                    | exact ev_kIte_fails (t := .lit true) hF hC hκ h (fun _ => ev_res_false hF)
                        (valueOfTy_of_bool (.inr rfl)) (resBool_lit hF true).ty hκb

include iIL in
/-- `κ ∧ a` for a false reach context `κ` evaluates to `ff`, when `a` is Boolean and the
    variables of `κ` hold Booleans. -/
theorem ev_kAnd_fails (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Fails F σ)
    {a : WExpr P} (h : resolveE tys tyOf (kAnd κ a) = .ok x) (ha : ResBool F σ tys tyOf a)
    (hκb : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
    P.eval F σ x = some (HasBool.ffVal F) :=
  ev_kIte_fails hF hC hκ h (fun _ => ev_res_false hF) (valueOfTy_of_bool (.inr rfl)) ha.ty hκb

include iIL in
/-- `κ ⟹ a` for a false reach context `κ` evaluates to `tt`, when `a` is Boolean and the
    variables of `κ` hold Booleans. -/
theorem ev_kImp_fails (hF : WellFormedSemanticEvalBase F) (hC : WellFormedStore σ F) {κ : RE P}
    (hκ : κ.Fails F σ)
    {a : WExpr P} (h : resolveE tys tyOf (kImp κ a) = .ok x) (ha : ResBool F σ tys tyOf a)
    (hκb : ∀ y ∈ RE.vars κ, σ y = some (HasBool.ttVal F) ∨ σ y = some (HasBool.ffVal F)) :
    P.eval F σ x = some (HasBool.ttVal F) :=
  ev_kIte_fails hF hC hκ h (fun _ => ev_res_true hF) (valueOfTy_of_bool (.inl rfl)) ha.ty hκb

end -- public section

end WP
end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
# Basic properties of the typed SMT Term semantics

* `Term.typeOf_of_typeCheck` — the syntactic `Term.typeOf` agrees with the type at which a term
  type-checks.
* `Term.denoteTyped_quant_eq` / `_forall_eq_true` / `_exists_eq_true` — cast-free unfoldings of the
  `.quant` case, exposing the binder as a plain `∀`/`∃` over environment extensions.
* `TermType.denoteTyped.inhabited` / `TermType.denoteTyped.instInhabited` — every denoted sort is
  inhabited, given inhabited carriers for the sort constructors.
-/

module

public import Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTyped

namespace Strata.SMT.DenoteTyped

variable {σ : SortInterp} {𝒜 : ArrayTheory}

/-- `Except`-monad analogue of `Option.bind_eq_some_iff`: a bind succeeds with `b` iff the first
    computation succeeds with some `a` and the continuation succeeds with `b` on it. -/
private theorem Except.bind_eq_ok' {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- `Except`-monad analogue of `Option.ite_none_right_eq_some`: an `if` whose else-branch is a
    failure succeeds with `b` iff the condition holds and the then-branch succeeds with `b`. -/
private theorem Except.ite_error_right_eq_ok {ε β : Type} {c : Prop} [Decidable c]
    {x : Except ε β} {e : ε} {b : β} :
    (if c then x else .error e) = .ok b ↔ c ∧ x = .ok b := by
  split <;> simp_all

/-- The syntactic `Term.typeOf` always agrees with the type at which a term type-checks. -/
theorem Term.typeOf_of_typeCheck {ctx : TypedContext} {tm : Term} {τ : TermType}
    (h : Term.typeCheck ctx tm = .ok τ) : Term.typeOf tm = τ := by
  match tm with
  | .prim p =>
    simp only [Term.typeCheck] at h; split at h <;> simp_all [Term.typeOf]
  | .var v =>
    simp only [Term.typeCheck] at h; split at h <;> simp_all [Term.typeOf]
  | .quant k vs tr body =>
    simp only [Term.typeCheck] at h; revert h
    cases Term.typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body with
    | error e => simp [bind, Except.bind]
    | ok tyb =>
      simp only [bind, Except.bind]; intro h'; split at h' <;> simp_all [Term.typeOf]
  | .app .select [a, i] rty =>
    obtain ⟨k, v, _, _, hrty, hτ⟩ := Term.typeCheck_select_inv h
    simp only [Term.typeOf]; subst hτ; exact hrty
  | .app .store [a, i, e] rty =>
    obtain ⟨k, v, _, _, _, hrty, hτ⟩ := Term.typeCheck_store_inv h
    simp only [Term.typeOf]; subst hτ; exact hrty
  | .app op args rty =>
    simp only [Term.typeOf]
    unfold Term.typeCheck at h
    split at h <;>
      simp only [Except.bind_eq_ok', Except.ite_error_right_eq_ok,
        Bool.and_eq_true, beq_iff_eq, Except.ok.injEq, reduceCtorEq] at h <;>
      first
      | grind
      | (obtain ⟨w, _, h⟩ := h
         split at h <;>
           simp only [Except.bind_eq_ok', Except.ite_error_right_eq_ok, Except.ok.injEq,
             reduceCtorEq] at h <;>
           grind)
  | .none ty =>
    have heq := Term.typeCheck_none_inv h
    simp only [Term.typeOf]; exact heq.symm
  | .some t =>
    obtain ⟨τ', ht, hτ⟩ := Term.typeCheck_some_inv h
    subst hτ; simp only [Term.typeOf]; rw [Term.typeOf_of_typeCheck ht]

/-- Every sort denotes an inhabited type, given inhabited carriers for the sort constructors. -/
def TermType.denoteTyped.inhabited (h : ∀ id args, Inhabited (σ id args)) :
    (τ : TermType) → Inhabited (TermType.denoteTyped σ 𝒜 τ)
  | .prim p => by cases p <;> first
      | exact ⟨false⟩ | exact ⟨(0 : Int)⟩ | exact ⟨(0 : BitVec _)⟩ | exact ⟨""⟩ | exact ⟨()⟩
  | .option _ => ⟨none⟩
  | .constr id args => by
    match args with
    | [k, v] =>
      by_cases hid : id = "Array"
      · subst hid
        exact ⟨𝒜.const (TermType.denoteTyped.inhabited h v).default⟩
      · have hred : TermType.denoteTyped σ 𝒜 (.constr id [k, v]) = σ id [k, v] := by
          rw [TermType.denoteTyped]; intro _ _ h' _; exact absurd h' hid
        rw [hred]; exact h id [k, v]
    | [] =>
      have hred : TermType.denoteTyped σ 𝒜 (.constr id []) = σ id [] := by
        rw [TermType.denoteTyped]; intro _ _ _ h'; exact absurd h' (by simp)
      rw [hred]; exact h id []
    | [x] =>
      have hred : TermType.denoteTyped σ 𝒜 (.constr id [x]) = σ id [x] := by
        rw [TermType.denoteTyped]; intro _ _ _ h'; exact absurd h' (by simp)
      rw [hred]; exact h id [x]
    | x :: y :: z :: rest =>
      have hred : TermType.denoteTyped σ 𝒜 (.constr id (x :: y :: z :: rest))
          = σ id (x :: y :: z :: rest) := by
        rw [TermType.denoteTyped]; intro _ _ _ h'; exact absurd h' (by simp)
      rw [hred]; exact h id (x :: y :: z :: rest)
termination_by τ => sizeOf τ
decreasing_by simp_wf; omega

instance TermType.denoteTyped.instInhabited
    [SortInterp.AllInhabited σ] (τ : TermType) : Inhabited (TermType.denoteTyped σ 𝒜 τ) :=
  TermType.denoteTyped.inhabited SortInterp.AllInhabited.inhabited τ

/- ═══════════════════════════════════════════════════════════════════════════
   Cast-free unfoldings of the `.quant` case.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- The `.quant` denotation as a `decide` over the `∀`/`∃`-proposition, cast stripped: the bound
    variables range over an environment extension `ext`, everything else stays at `env`. -/
theorem Term.denoteTyped_quant_eq
    {ctx : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (qk : Strata.SMT.QuantifierKind) (vs : List TermVar) (tr : List (List Term)) (body : Term)
    (h : Term.typeCheck ctx (.quant qk vs tr body) = .ok .bool)
    (hbody : Term.typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body = .ok .bool) :
    Term.denoteTyped ufInterp env divByZero modByZero (.quant qk vs tr body) .bool h
      = @decide (match qk with
          | .all => ∀ (ext : VarEnv σ 𝒜),
              Term.denoteTyped ufInterp (fun v => if _hv : v ∈ vs then ext v else env v)
                divByZero modByZero body .bool hbody = true
          | .exist => ∃ (ext : VarEnv σ 𝒜),
              Term.denoteTyped ufInterp (fun v => if _hv : v ∈ vs then ext v else env v)
                divByZero modByZero body .bool hbody = true)
          (Classical.propDecidable _) := by
  unfold Term.denoteTyped
  simp only [cast_eq]
  rcases htq : Term.typeCheck_quant_inv h with ⟨hbody', _⟩
  cases proof_irrel hbody' hbody
  cases qk <;> rfl

/-- `.all`-binder denotes `true` iff the body denotes `true` under every extension. -/
theorem Term.denoteTyped_forall_eq_true
    {ctx : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int) (vs : List TermVar) (tr : List (List Term)) (body : Term)
    (h : Term.typeCheck ctx (.quant .all vs tr body) = .ok .bool)
    (hbody : Term.typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body = .ok .bool) :
    (Term.denoteTyped ufInterp env divByZero modByZero (.quant .all vs tr body) .bool h = true)
      ↔ ∀ (ext : VarEnv σ 𝒜),
          Term.denoteTyped ufInterp (fun v => if _hv : v ∈ vs then ext v else env v)
            divByZero modByZero body .bool hbody = true := by
  rw [Term.denoteTyped_quant_eq ufInterp env divByZero modByZero .all vs tr body h hbody]
  dsimp only []
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- `.exist`-binder denotes `true` iff the body denotes `true` under some extension. -/
theorem Term.denoteTyped_exists_eq_true
    {ctx : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int) (vs : List TermVar) (tr : List (List Term)) (body : Term)
    (h : Term.typeCheck ctx (.quant .exist vs tr body) = .ok .bool)
    (hbody : Term.typeCheck { ctx with Γ := vs.reverse ++ ctx.Γ } body = .ok .bool) :
    (Term.denoteTyped ufInterp env divByZero modByZero (.quant .exist vs tr body) .bool h = true)
      ↔ ∃ (ext : VarEnv σ 𝒜),
          Term.denoteTyped ufInterp (fun v => if _hv : v ∈ vs then ext v else env v)
            divByZero modByZero body .bool hbody = true := by
  rw [Term.denoteTyped_quant_eq ufInterp env divByZero modByZero .exist vs tr body h hbody]
  dsimp only []
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/- ═══════════════════════════════════════════════════════════════════════════
   Cast-free unfoldings of `Term.denoteTyped`, one per operator.

   Each rewrites `Term.denoteTyped … (.app op …) …` into the corresponding Lean operation on the
   sub-term denotations, with the return-type `cast` made explicit.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- Unfolding lemma for `Term.denoteTyped` on a UF application, exposing `UF.applyDenoteTyped'` on the
    denoted argument `HList`. -/
private theorem Term.denoteTyped_uf {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (uf : UF) (args : List Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core (.uf uf)) args rty) = .ok τ)
    (hargs : Term.typeCheckArgs ctx args uf.args = true) (hout : τ = uf.out) :
    Term.denoteTyped ufInterp env dz mz (.app (.core (.uf uf)) args rty) τ htc
      = cast (by rw [hout])
          (UF.applyDenoteTyped' σ 𝒜 uf.args uf.out (ufInterp uf)
            (Term.denoteTypedArgs ufInterp env dz mz args uf.args hargs)) := by
  unfold Term.denoteTyped
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on `not`. -/
private theorem Term.denoteTyped_not {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .not) [t] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .not) [t] rty) τ htc
      = cast (by rw [(Term.typeCheck_not_inv htc).2])
          (! Term.denoteTyped ufInterp env dz mz t .bool (Term.typeCheck_not_inv htc).1) := by
  simp only [Term.denoteTyped]
  obtain ⟨ht', heq'⟩ := Term.typeCheck_not_inv htc
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on `none`. -/
private theorem Term.denoteTyped_none {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (ty τ : TermType) (htc : Term.typeCheck ctx (.none ty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.none ty) τ htc
      = cast (by rw [Term.typeCheck_none_inv htc]) (none : TermType.denoteTyped σ 𝒜 (.option ty)) := by
  simp only [Term.denoteTyped]

/-- Unfolding lemma for `Term.denoteTyped` on `some`. -/
private theorem Term.denoteTyped_some {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t : Term) (τ : TermType) (htc : Term.typeCheck ctx (.some t) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.some t) τ htc
      = cast (congrArg (TermType.denoteTyped σ 𝒜) (Term.typeCheck_some_inv htc).2.2.symm)
          (some (Term.denoteTyped ufInterp env dz mz t (Term.typeCheck_some_inv htc).1
                  (Term.typeCheck_some_inv htc).2.1)
            : TermType.denoteTyped σ 𝒜 (.option (Term.typeCheck_some_inv htc).1)) := by
  simp only [Term.denoteTyped]
  obtain ⟨τ', ht, heq⟩ := Term.typeCheck_some_inv htc
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on array `select`. -/
private theorem Term.denoteTyped_select {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (a i : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app .select [a, i] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app .select [a, i] rty) τ htc
      = cast (congrArg (TermType.denoteTyped σ SmtArrayTheory) (Term.typeCheck_select_inv htc).2.2.2.2.2.symm)
          ((Term.denoteTyped ufInterp env dz mz a
              (.constr "Array" [(Term.typeCheck_select_inv htc).1, (Term.typeCheck_select_inv htc).2.1])
              (Term.typeCheck_select_inv htc).2.2.1).select
            (Term.denoteTyped ufInterp env dz mz i (Term.typeCheck_select_inv htc).1
              (Term.typeCheck_select_inv htc).2.2.2.1)) := by
  simp only [Term.denoteTyped]
  obtain ⟨k, v, ha, hi, hrty, hτ⟩ := Term.typeCheck_select_inv htc
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on array `store`. -/
private theorem Term.denoteTyped_store {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (a i e : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app .store [a, i, e] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app .store [a, i, e] rty) τ htc
      = cast (congrArg (TermType.denoteTyped σ SmtArrayTheory) (Term.typeCheck_store_inv htc).2.2.2.2.2.2.symm)
          (@SmtArray.store _ _ (Classical.typeDecidableEq _)
            (Term.denoteTyped ufInterp env dz mz a
              (.constr "Array" [(Term.typeCheck_store_inv htc).1, (Term.typeCheck_store_inv htc).2.1])
              (Term.typeCheck_store_inv htc).2.2.1)
            (Term.denoteTyped ufInterp env dz mz i (Term.typeCheck_store_inv htc).1
              (Term.typeCheck_store_inv htc).2.2.2.1)
            (Term.denoteTyped ufInterp env dz mz e (Term.typeCheck_store_inv htc).2.1
              (Term.typeCheck_store_inv htc).2.2.2.2.1)) := by
  simp only [Term.denoteTyped]
  obtain ⟨k, v, ha, hi, he, hrty, hτ⟩ := Term.typeCheck_store_inv htc
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on `eq`, exposing `decide (· = ·)`. -/
private theorem Term.denoteTyped_eq {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .eq) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .eq) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_eq_inv htc).2.2.2])
          (@decide (Term.denoteTyped ufInterp env dz mz t1 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.1
                     = Term.denoteTyped ufInterp env dz mz t2 (Term.typeCheck_eq_inv htc).1 (Term.typeCheck_eq_inv htc).2.2.1)
            (Classical.propDecidable _)) := by
  simp only [Term.denoteTyped]; obtain ⟨τ', h1, h2, heq⟩ := Term.typeCheck_eq_inv htc; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `ite`, exposing the boolean `bif`. -/
private theorem Term.denoteTyped_ite {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (c t e : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .ite) [c, t, e] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .ite) [c, t, e] rty) τ htc
      = bif Term.denoteTyped ufInterp env dz mz c .bool (Term.typeCheck_ite_inv htc).1
        then Term.denoteTyped ufInterp env dz mz t τ (Term.typeCheck_ite_inv htc).2.1
        else Term.denoteTyped ufInterp env dz mz e τ (Term.typeCheck_ite_inv htc).2.2 := by
  simp only [Term.denoteTyped]; obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `and`, exposing `&&`. -/
private theorem Term.denoteTyped_and {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .and) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .and) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inl rfl)).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).1) &&
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `or`, exposing `||`. -/
private theorem Term.denoteTyped_or {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .or) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .or) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1) ||
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `implies`, exposing `!… || …`. -/
private theorem Term.denoteTyped_implies {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .implies) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .implies) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.2])
          ((!(Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1)) ||
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `add`. -/
private theorem Term.denoteTyped_add {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .add) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .add) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inl rfl)).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1) +
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `sub`. -/
private theorem Term.denoteTyped_sub {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .sub) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .sub) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1) -
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `mul`. -/
private theorem Term.denoteTyped_mul {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .mul) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .mul) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1) *
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `le`. -/
private theorem Term.denoteTyped_le {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .le) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .le) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1) ≤
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `lt`. -/
private theorem Term.denoteTyped_lt {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .lt) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .lt) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1) <
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `ge`. -/
private theorem Term.denoteTyped_ge {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .ge) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .ge) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1) ≥
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `gt`. -/
private theorem Term.denoteTyped_gt {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .gt) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .gt) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1) >
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `div`. -/
private theorem Term.denoteTyped_div {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .div) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .div) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2])
          (let v1 := Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1
           let v2 := Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1
           if v2 = 0 then dz v1 else v1 / v2) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `mod`. -/
private theorem Term.denoteTyped_mod {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .mod) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .mod) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2])
          (let v1 := Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1
           let v2 := Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1
           if v2 = 0 then mz v1 else v1 % v2) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int negation. -/
private theorem Term.denoteTyped_neg {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) (dz mz : Int → Int) (t : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .neg) [t] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .neg) [t] rty) τ htc
      = cast (by rw [(Term.typeCheck_intUn_inv htc).2]) (-(Term.denoteTyped ufInterp env dz mz t .int (Term.typeCheck_intUn_inv htc).1)) := by
  simp only [Term.denoteTyped]; obtain ⟨ht, heq⟩ := Term.typeCheck_intUn_inv htc; rfl

/-- `Term.denoteTyped` depends on its `env` argument only up to function equality. -/
private theorem Term.denoteTyped_env_congr {ctx : TypedContext}
    (ufInterp : UFInterp σ 𝒜) (env env' : VarEnv σ 𝒜) (dz mz : Int → Int)
    (tm : Term) (τ : TermType) (htc : Term.typeCheck ctx tm = .ok τ)
    (h : env = env') :
    Term.denoteTyped ufInterp env dz mz tm τ htc = Term.denoteTyped ufInterp env' dz mz tm τ htc := by
  rw [h]

/- ═══════════════════════════════════════════════════════════════════════════
   `Term.typeCheck` monotonicity under UF-context extension.

   The UF-app arm gates on `uf ∈ ctx.ufs` (exact membership), which is monotone under a superset; every
   other arm ignores `ctx.ufs` (recurses / uses `uss`/`Γ` only). So a term well-typed at `ufs` stays
   well-typed (to the same type) at any `ufs' ⊇ ufs`.
   ═══════════════════════════════════════════════════════════════════════════ -/

mutual
theorem typeCheck_ufs_mono {uss : USCtx} {ufs ufs' : UFCtx}
    (hsub : ∀ u ∈ ufs, u ∈ ufs') (Γ : List TermVar) (t : Term) (τ : TermType)
    (h : Term.typeCheck ⟨uss, ufs, Γ⟩ t = .ok τ) :
    Term.typeCheck ⟨uss, ufs', Γ⟩ t = .ok τ := by
  match t with
  | .prim p => simpa only [Term.typeCheck] using h
  | .var v => simpa only [Term.typeCheck] using h
  | .none ty => simpa only [Term.typeCheck] using h
  | .some t1 =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, bind, Except.bind]
      exact h
  | .quant k vs tr body =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨tyb, hb, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub (vs.reverse ++ Γ) body tyb hb, bind, Except.bind]
      revert h
      split <;> intro h <;> rename_i hcond
      · rw [if_pos ?_]
        · exact h
        · simp only [Bool.and_eq_true] at hcond ⊢
          exact ⟨hcond.1, wfTriggers_ufs_mono hsub (vs.reverse ++ Γ) tr hcond.2⟩
      · exact absurd h (by simp)
  | .app (.core (.uf uf)) args rty =>
      simp only [Term.typeCheck] at h ⊢
      split at h
      · rename_i hc
        rw [if_pos ⟨hsub uf hc.1, hc.2⟩]
        split at h
        · rename_i hchk
          simp only [Bool.and_eq_true] at hchk
          obtain ⟨⟨⟨hrty, hargs⟩, hall⟩, hout⟩ := hchk
          rw [if_pos ?_]
          · exact h
          · simp only [Bool.and_eq_true]
            exact ⟨⟨⟨hrty, typeCheckArgs_ufs_mono hsub Γ args uf.args hargs⟩, hall⟩, hout⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | .app (.core .not) [t1] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, bind, Except.bind]
      exact h
  | .app (.core .and) [t1, t2] rty | .app (.core .or) [t1, t2] rty
  | .app (.core .implies) [t1, t2] rty | .app (.core .eq) [t1, t2] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      obtain ⟨ty2, h2, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, typeCheck_ufs_mono hsub Γ t2 ty2 h2,
        bind, Except.bind]
      exact h
  | .app (.core .ite) [c, t1, e] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨tyc, hc, h⟩ := Except.bind_eq_ok'.mp h
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      obtain ⟨tye, he, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ c tyc hc, typeCheck_ufs_mono hsub Γ t1 ty1 h1,
        typeCheck_ufs_mono hsub Γ e tye he, bind, Except.bind]
      exact h
  | .app (.num .neg) [t1] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, bind, Except.bind]
      exact h
  | .app (.num .add) [t1, t2] rty | .app (.num .sub) [t1, t2] rty
  | .app (.num .mul) [t1, t2] rty | .app (.num .div) [t1, t2] rty
  | .app (.num .mod) [t1, t2] rty
  | .app (.num .le) [t1, t2] rty | .app (.num .lt) [t1, t2] rty
  | .app (.num .ge) [t1, t2] rty | .app (.num .gt) [t1, t2] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      obtain ⟨ty2, h2, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, typeCheck_ufs_mono hsub Γ t2 ty2 h2,
        bind, Except.bind]
      exact h
  | .app (.core .distinct) (t1 :: t2 :: ts) rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨ty1, h1, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ t1 ty1 h1, bind, Except.bind]
      revert h
      split <;> intro h <;> rename_i hcond
      · rw [if_pos ?_]
        · exact h
        · simp only [Bool.and_eq_true] at hcond ⊢
          exact ⟨typeCheckArgs_ufs_mono hsub Γ (t2 :: ts) _ hcond.1, hcond.2⟩
      · exact absurd h (by simp)
  | .app .select [a, i] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨tya, ha, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ a tya ha, bind, Except.bind]
      revert h
      split <;> intro h
      · obtain ⟨tyi, hi, h⟩ := Except.bind_eq_ok'.mp h
        simp only [typeCheck_ufs_mono hsub Γ i tyi hi]
        exact h
      · exact absurd h (by simp)
  | .app .store [a, i, e] rty =>
      simp only [Term.typeCheck] at h ⊢
      obtain ⟨tya, ha, h⟩ := Except.bind_eq_ok'.mp h
      simp only [typeCheck_ufs_mono hsub Γ a tya ha, bind, Except.bind]
      revert h
      split <;> intro h
      · obtain ⟨tyi, hi, h⟩ := Except.bind_eq_ok'.mp h
        obtain ⟨tye, he, h⟩ := Except.bind_eq_ok'.mp h
        simp only [typeCheck_ufs_mono hsub Γ i tyi hi, typeCheck_ufs_mono hsub Γ e tye he]
        exact h
      · exact absurd h (by simp)
  -- All remaining `.app` shapes are malformed: an unhandled operator, or a handled operator applied at
  -- the wrong arity. In every case `Term.typeCheck` falls through to its `.error` arm, contradicting a
  -- `.ok` result. A `match` catch-all cannot see the earlier arms' negative constraints, so the concrete
  -- residual shapes are enumerated to let `typeCheck` reduce.
  | .app (.core .not) [] rty | .app (.core .not) (_ :: _ :: _) rty
  | .app (.core .and) [] rty | .app (.core .and) [_] rty | .app (.core .and) (_ :: _ :: _ :: _) rty
  | .app (.core .or) [] rty | .app (.core .or) [_] rty | .app (.core .or) (_ :: _ :: _ :: _) rty
  | .app (.core .implies) [] rty | .app (.core .implies) [_] rty
  | .app (.core .implies) (_ :: _ :: _ :: _) rty
  | .app (.core .eq) [] rty | .app (.core .eq) [_] rty | .app (.core .eq) (_ :: _ :: _ :: _) rty
  | .app (.core .ite) [] rty | .app (.core .ite) [_] rty | .app (.core .ite) [_, _] rty
  | .app (.core .ite) (_ :: _ :: _ :: _ :: _) rty
  | .app (.core .distinct) [] rty | .app (.core .distinct) [_] rty
  | .app (.num .neg) [] rty | .app (.num .neg) (_ :: _ :: _) rty
  | .app (.num .add) [] rty | .app (.num .add) [_] rty | .app (.num .add) (_ :: _ :: _ :: _) rty
  | .app (.num .sub) [] rty | .app (.num .sub) [_] rty | .app (.num .sub) (_ :: _ :: _ :: _) rty
  | .app (.num .mul) [] rty | .app (.num .mul) [_] rty | .app (.num .mul) (_ :: _ :: _ :: _) rty
  | .app (.num .div) [] rty | .app (.num .div) [_] rty | .app (.num .div) (_ :: _ :: _ :: _) rty
  | .app (.num .mod) [] rty | .app (.num .mod) [_] rty | .app (.num .mod) (_ :: _ :: _ :: _) rty
  | .app (.num .le) [] rty | .app (.num .le) [_] rty | .app (.num .le) (_ :: _ :: _ :: _) rty
  | .app (.num .lt) [] rty | .app (.num .lt) [_] rty | .app (.num .lt) (_ :: _ :: _ :: _) rty
  | .app (.num .ge) [] rty | .app (.num .ge) [_] rty | .app (.num .ge) (_ :: _ :: _ :: _) rty
  | .app (.num .gt) [] rty | .app (.num .gt) [_] rty | .app (.num .gt) (_ :: _ :: _ :: _) rty
  | .app .select [] rty | .app .select [_] rty | .app .select (_ :: _ :: _ :: _) rty
  | .app .store [] rty | .app .store [_] rty | .app .store [_, _] rty
  | .app .store (_ :: _ :: _ :: _ :: _) rty
  | .app (.num .rdiv) _ rty | .app (.num .abs) _ rty
  | .app (.bv _) _ rty | .app (.str _) _ rty
  | .app .option_get _ rty | .app (.datatype_op _ _) _ rty =>
      simp [Term.typeCheck] at h

theorem typeCheckArgs_ufs_mono {uss : USCtx} {ufs ufs' : UFCtx}
    (hsub : ∀ u ∈ ufs, u ∈ ufs') (Γ : List TermVar) (ts : List Term) (tys : List TermType)
    (h : Term.typeCheckArgs ⟨uss, ufs, Γ⟩ ts tys = true) :
    Term.typeCheckArgs ⟨uss, ufs', Γ⟩ ts tys = true := by
  match ts, tys with
  | [], [] => simp only [Term.typeCheckArgs]
  | t :: ts, ety :: rest =>
      simp only [Term.typeCheckArgs] at h ⊢
      revert h
      split <;> intro h <;> rename_i hty
      · rename_i ty
        rw [typeCheck_ufs_mono hsub Γ t ty hty]
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨h.1, typeCheckArgs_ufs_mono hsub Γ ts rest h.2⟩
      · exact absurd h (by simp)
  | [], _ :: _ => simp [Term.typeCheckArgs] at h
  | _ :: _, [] => simp [Term.typeCheckArgs] at h

theorem typeCheckAll_ufs_mono {uss : USCtx} {ufs ufs' : UFCtx}
    (hsub : ∀ u ∈ ufs, u ∈ ufs') (Γ : List TermVar) (ts : List Term)
    (h : Term.typeCheckAll ⟨uss, ufs, Γ⟩ ts = true) :
    Term.typeCheckAll ⟨uss, ufs', Γ⟩ ts = true := by
  match ts with
  | [] => simp only [Term.typeCheckAll]
  | t :: ts =>
      simp only [Term.typeCheckAll, Bool.and_eq_true] at h ⊢
      obtain ⟨hsome, hrest⟩ := h
      refine ⟨?_, typeCheckAll_ufs_mono hsub Γ ts hrest⟩
      rcases hok : Term.typeCheck ⟨uss, ufs, Γ⟩ t with _ | ty
      · rw [hok] at hsome; simp [Except.toOption] at hsome
      · rw [typeCheck_ufs_mono hsub Γ t ty hok]; simp [Except.toOption]

theorem wfTriggers_ufs_mono {uss : USCtx} {ufs ufs' : UFCtx}
    (hsub : ∀ u ∈ ufs, u ∈ ufs') (Γ : List TermVar) (trs : List (List Term))
    (h : Term.wfTriggers ⟨uss, ufs, Γ⟩ trs = true) :
    Term.wfTriggers ⟨uss, ufs', Γ⟩ trs = true := by
  match trs with
  | [] => simp only [Term.wfTriggers]
  | group :: rest =>
      simp only [Term.wfTriggers, Bool.and_eq_true] at h ⊢
      exact ⟨typeCheckAll_ufs_mono hsub Γ group h.1, wfTriggers_ufs_mono hsub Γ rest h.2⟩
end

/-- Membership-subset (the hypothesis of `typeCheck_ufs_mono`) for an append extension. -/
theorem typeCheck_ufs_mono_append {uss : USCtx} {ufs tail : UFCtx}
    {Γ : List TermVar} {t : Term} {τ : TermType}
    (h : Term.typeCheck ⟨uss, ufs, Γ⟩ t = .ok τ) :
    Term.typeCheck ⟨uss, ufs ++ tail, Γ⟩ t = .ok τ :=
  typeCheck_ufs_mono (fun _ hu => List.mem_append_left _ hu) Γ t τ h

end Strata.SMT.DenoteTyped

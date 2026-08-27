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
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (uf : UF) (args : List Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core (.uf uf)) args rty) = .ok τ)
    (hargs : Term.typeCheckArgs ctx args uf.args = true) (hout : τ = uf.out) :
    Term.denoteTyped ufInterp env dz mz (.app (.core (.uf uf)) args rty) τ htc
      = cast (by rw [hout])
          (UF.applyDenoteTyped' σ SmtArrayTheory uf.args uf.out (ufInterp uf)
            (Term.denoteTypedArgs ufInterp env dz mz args uf.args hargs)) := by
  unfold Term.denoteTyped
  rfl

/-- Unfolding lemma for `Term.denoteTyped` on `not`. -/
private theorem Term.denoteTyped_not {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
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
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (ty τ : TermType) (htc : Term.typeCheck ctx (.none ty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.none ty) τ htc
      = cast (by rw [Term.typeCheck_none_inv htc]) (none : TermType.denoteTyped σ SmtArrayTheory (.option ty)) := by
  simp only [Term.denoteTyped]

/-- Unfolding lemma for `Term.denoteTyped` on `some`. -/
private theorem Term.denoteTyped_some {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (t : Term) (τ : TermType) (htc : Term.typeCheck ctx (.some t) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.some t) τ htc
      = cast (congrArg (TermType.denoteTyped σ SmtArrayTheory) (Term.typeCheck_some_inv htc).2.2.symm)
          (some (Term.denoteTyped ufInterp env dz mz t (Term.typeCheck_some_inv htc).1
                  (Term.typeCheck_some_inv htc).2.1)
            : TermType.denoteTyped σ SmtArrayTheory (.option (Term.typeCheck_some_inv htc).1)) := by
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
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
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
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (c t e : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .ite) [c, t, e] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .ite) [c, t, e] rty) τ htc
      = bif Term.denoteTyped ufInterp env dz mz c .bool (Term.typeCheck_ite_inv htc).1
        then Term.denoteTyped ufInterp env dz mz t τ (Term.typeCheck_ite_inv htc).2.1
        else Term.denoteTyped ufInterp env dz mz e τ (Term.typeCheck_ite_inv htc).2.2 := by
  simp only [Term.denoteTyped]; obtain ⟨hc, ht, he⟩ := Term.typeCheck_ite_inv htc; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `and`, exposing `&&`. -/
private theorem Term.denoteTyped_and {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .and) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .and) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inl rfl)).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).1) &&
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inl rfl)).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `or`, exposing `||`. -/
private theorem Term.denoteTyped_or {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .or) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .or) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).1) ||
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inl rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on `implies`, exposing `!… || …`. -/
private theorem Term.denoteTyped_implies {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.core .implies) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.core .implies) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.2])
          ((!(Term.denoteTyped ufInterp env dz mz t1 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).1)) ||
           (Term.denoteTyped ufInterp env dz mz t2 .bool (Term.typeCheck_boolBin_inv htc (.inr (.inr rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `add`. -/
private theorem Term.denoteTyped_add {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .add) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .add) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inl rfl)).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).1) +
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inl rfl)).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `sub`. -/
private theorem Term.denoteTyped_sub {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .sub) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .sub) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).1) -
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inl rfl))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `mul`. -/
private theorem Term.denoteTyped_mul {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .mul) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .mul) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.2])
          ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).1) *
           (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inl rfl)))).2.1)) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `le`. -/
private theorem Term.denoteTyped_le {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .le) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .le) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inl rfl)).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).1) ≤
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inl rfl)).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `lt`. -/
private theorem Term.denoteTyped_lt {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .lt) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .lt) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).1) <
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inl rfl))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `ge`. -/
private theorem Term.denoteTyped_ge {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .ge) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .ge) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).1) ≥
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inl rfl)))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `gt`. -/
private theorem Term.denoteTyped_gt {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .gt) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .gt) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.2])
          (decide ((Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).1) >
            (Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intCmp_inv htc (.inr (.inr (.inr rfl)))).2.1))) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `div`. -/
private theorem Term.denoteTyped_div {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .div) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .div) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.2])
          (let v1 := Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).1
           let v2 := Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inl rfl))))).2.1
           if v2 = 0 then dz v1 else v1 / v2) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int `mod`. -/
private theorem Term.denoteTyped_mod {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t1 t2 : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .mod) [t1, t2] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .mod) [t1, t2] rty) τ htc
      = cast (by rw [(Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.2])
          (let v1 := Term.denoteTyped ufInterp env dz mz t1 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).1
           let v2 := Term.denoteTyped ufInterp env dz mz t2 .int (Term.typeCheck_intBin_inv htc (.inr (.inr (.inr (.inr rfl))))).2.1
           if v2 = 0 then mz v1 else v1 % v2) := by
  simp only [Term.denoteTyped]; split; rfl

/-- Unfolding lemma for `Term.denoteTyped` on int negation. -/
private theorem Term.denoteTyped_neg {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env : VarEnv σ SmtArrayTheory) (dz mz : Int → Int) (t : Term) (rty τ : TermType)
    (htc : Term.typeCheck ctx (.app (.num .neg) [t] rty) = .ok τ) :
    Term.denoteTyped ufInterp env dz mz (.app (.num .neg) [t] rty) τ htc
      = cast (by rw [(Term.typeCheck_intUn_inv htc).2]) (-(Term.denoteTyped ufInterp env dz mz t .int (Term.typeCheck_intUn_inv htc).1)) := by
  simp only [Term.denoteTyped]; obtain ⟨ht, heq⟩ := Term.typeCheck_intUn_inv htc; rfl

/-- `Term.denoteTyped` depends on its `env` argument only up to function equality. -/
private theorem Term.denoteTyped_env_congr {ctx : TypedContext}
    (ufInterp : UFInterp σ SmtArrayTheory) (env env' : VarEnv σ SmtArrayTheory) (dz mz : Int → Int)
    (tm : Term) (τ : TermType) (htc : Term.typeCheck ctx tm = .ok τ)
    (h : env = env') :
    Term.denoteTyped ufInterp env dz mz tm τ htc = Term.denoteTyped ufInterp env' dz mz tm τ htc := by
  rw [h]

end Strata.SMT.DenoteTyped

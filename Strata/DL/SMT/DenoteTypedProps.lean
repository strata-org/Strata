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
* `typeCheck_ufs_mono` / `typeCheck_ufs_mono_append` — `Term.typeCheck` is monotone under extending the
  UF context.
* `Term.denoteTyped_congr` — term-equality congruence for `Term.denoteTyped` (equal terms denote equally).
* `Term.denoteTyped_quant_coalesce` — one-step quantifier coalescing: a merged multi-binder denotes as
  the nested single binders.
* `Term.typeCheck_quant_ok_iff` — decomposition of a well-typed quantifier (body/sort/trigger
  obligations plus `τ = bool`).
* `denote_prim_inj` — distinct primitive literals at a base sort have distinct denotations.
* `distinct_typeCheck` — a `distinct` over ≥2 same-base-sort terms type-checks to `bool`.
* `not_someNone_of_base` / `isBase_cases` — base-sort witnesses (a base-typed term is neither
  `.some`/`.none`; the four base SMT sorts).
* `hlist_getElem` — indexing an `HList` over a `List.replicate` argument vector.
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
   Quantifier binder-context congruence and one-step coalescing.
   ═══════════════════════════════════════════════════════════════════════════ -/

/-- `Term.denoteTyped` is invariant under a propositional equality of the typing context (the context
    is only used to type-check; equal contexts give equal denotations, modulo transporting the proof). -/
private theorem Term.denoteTyped_ctx_congr
    {ctx ctx' : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int) (tm : Term) {τ : TermType}
    (hctx : ctx = ctx') (h : Term.typeCheck ctx tm = .ok τ) (h' : Term.typeCheck ctx' tm = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero tm τ h
      = Term.denoteTyped ufInterp env divByZero modByZero tm τ h' := by
  subst hctx; rfl

/-- **One-step quantifier-coalescing transparency** at the `Term.denoteTyped` level: a merged binder over
    `⟨x,ty⟩ :: args2` denotes exactly as the nested binders `⟨x,ty⟩` then `args2`. Triggers are ignored
    by `Term.denoteTyped`, so this is purely about the `combinedEnv` membership reassociation
    (`v ∈ ⟨x,ty⟩::args2` ↔ `v ∈ [⟨x,ty⟩] ∨ v ∈ args2`). -/
theorem Term.denoteTyped_quant_coalesce
    {ctx : TypedContext} (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    (divByZero modByZero : Int → Int)
    (qk : Strata.SMT.QuantifierKind) (x : String) (ty : TermType)
    (tr trM tr2 : List (List Term)) (args2 : List TermVar) (e2 : Term) {τ : TermType}
    (hM : Term.typeCheck ctx (.quant qk ([⟨x, ty⟩] ++ args2) trM e2) = .ok τ)
    (hN : Term.typeCheck ctx (.quant qk [⟨x, ty⟩] tr (.quant qk args2 tr2 e2)) = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero (.quant qk ([⟨x, ty⟩] ++ args2) trM e2) τ hM
      = Term.denoteTyped ufInterp env divByZero modByZero
          (.quant qk [⟨x, ty⟩] tr (.quant qk args2 tr2 e2)) τ hN := by
  have hτb : τ = .bool := (Term.typeCheck_quant_inv hM).2
  subst hτb
  -- Body context equality (as full `TypedContext`s): merged binder's body context
  -- `{ctx with Γ := (⟨x,ty⟩::args2).reverse ++ ctx.Γ}` equals the nested inner's
  -- `{ctx with Γ := args2.reverse ++ (⟨x,ty⟩ :: ctx.Γ)}`.
  have hctx : ({ctx with Γ := ([(⟨x, ty⟩ : TermVar)] ++ args2).reverse ++ ctx.Γ} : TypedContext)
      = {ctx with Γ := args2.reverse ++ ((⟨x, ty⟩ : TermVar) :: ctx.Γ)} := by
    simp [List.append_assoc]
  -- Body typecheck at the merged (shared) context, and its transport to the nested-inner context.
  have hbodyM : Term.typeCheck {ctx with Γ := ([(⟨x, ty⟩ : TermVar)] ++ args2).reverse ++ ctx.Γ} e2
      = .ok .bool := (Term.typeCheck_quant_inv hM).1
  have hbody_e2 : Term.typeCheck {ctx with Γ := args2.reverse ++ ((⟨x, ty⟩ : TermVar) :: ctx.Γ)} e2
      = .ok .bool := hctx ▸ hbodyM
  -- Nested: the outer body `.quant qk args2 tr2 e2` type-checks at `{ctx with Γ := ⟨x,ty⟩ :: ctx.Γ}`.
  have hbodyN : Term.typeCheck {ctx with Γ := [(⟨x, ty⟩ : TermVar)].reverse ++ ctx.Γ}
      (.quant qk args2 tr2 e2) = .ok .bool := (Term.typeCheck_quant_inv hN).1
  -- Merged env vs nested env reassociation (over `VarEnv`, independent of the typing context).
  -- (a) The SAME `ext` for both nested binders reproduces the merged env.
  have hmerge : ∀ (ext : VarEnv σ 𝒜),
      (fun v => if hv : v ∈ args2 then ext v else if hv : v ∈ [(⟨x, ty⟩ : TermVar)] then ext v else env v)
        = (fun v => if hv : v ∈ [(⟨x, ty⟩ : TermVar)] ++ args2 then ext v else env v) := by
    intro ext; funext v
    by_cases ha : v ∈ args2 <;> by_cases hb : v ∈ [(⟨x, ty⟩ : TermVar)] <;>
      simp only [ha, hb, List.mem_append, or_true, or_false,
        dif_pos, dif_neg, not_false_eq_true]
  -- (b) Combining `ext1` (for `[v0]`) and `ext2` (for `args2`) into one `ext` reproduces the nested env.
  have hcombine : ∀ (ext1 ext2 : VarEnv σ 𝒜),
      (fun v => if hv : v ∈ [(⟨x, ty⟩ : TermVar)] ++ args2 then (if v ∈ args2 then ext2 v else ext1 v) else env v)
        = (fun v => if hv : v ∈ args2 then ext2 v else if hv : v ∈ [(⟨x, ty⟩ : TermVar)] then ext1 v else env v) := by
    intro ext1 ext2; funext v
    by_cases ha : v ∈ args2 <;> by_cases hb : v ∈ [(⟨x, ty⟩ : TermVar)] <;>
      simp only [ha, hb, List.mem_append, or_true, or_false,
        dif_pos, dif_neg, if_pos, if_neg, not_false_eq_true]
  -- `Term.denoteTyped` into `Bool`; equal iff equal-as-Prop (`Bool.eq_iff_iff`). Bridge each `qk` case
  -- via the per-kind `_eq_true` corollaries + the env reassociations.
  rw [Bool.eq_iff_iff]
  cases qk with
  | all =>
    rw [Term.denoteTyped_forall_eq_true (hbody := hbodyM)]
    rw [Term.denoteTyped_forall_eq_true (h := hN) (hbody := hbodyN)]
    constructor
    · -- merged ⟹ nested: outer `ext1`, inner `ext2`; apply merged at `combine ext1 ext2`.
      intro hAll ext1
      rw [Term.denoteTyped_forall_eq_true ufInterp _ divByZero modByZero args2 tr2 e2 hbodyN hbody_e2]
      intro ext2
      have h := hAll (fun v => if v ∈ args2 then ext2 v else ext1 v)
      rw [hcombine ext1 ext2] at h
      -- `h` is at body proof `hbodyM` (merged context); goal at `hbody_e2` (nested-inner context) —
      -- equal contexts (`hctx`), so transport.
      rw [Term.denoteTyped_ctx_congr ufInterp _ divByZero modByZero e2 hctx hbodyM hbody_e2] at h
      exact h
    · -- nested ⟹ merged: outer at `ext`, inner at `ext`.
      intro hNest ext
      have h1 := hNest ext
      rw [Term.denoteTyped_forall_eq_true ufInterp _ divByZero modByZero args2 tr2 e2 hbodyN hbody_e2] at h1
      have h2 := h1 ext
      rw [hmerge ext] at h2
      rw [Term.denoteTyped_ctx_congr ufInterp _ divByZero modByZero e2 hctx hbodyM hbody_e2]
      exact h2
  | exist =>
    rw [Term.denoteTyped_exists_eq_true (hbody := hbodyM)]
    rw [Term.denoteTyped_exists_eq_true (h := hN) (hbody := hbodyN)]
    constructor
    · intro ⟨ext, hex⟩
      -- merged witness `ext`; reuse it for both nested binders. Goal env (nested) = merged env via `hmerge`.
      refine ⟨ext, ?_⟩
      rw [Term.denoteTyped_exists_eq_true ufInterp _ divByZero modByZero args2 tr2 e2 hbodyN hbody_e2]
      refine ⟨ext, ?_⟩
      rw [hmerge ext]
      exact (Term.denoteTyped_ctx_congr ufInterp _ divByZero modByZero e2 hctx hbodyM hbody_e2) ▸ hex
    · intro ⟨ext1, hex1⟩
      rw [Term.denoteTyped_exists_eq_true ufInterp _ divByZero modByZero args2 tr2 e2 hbodyN hbody_e2] at hex1
      obtain ⟨ext2, hex2⟩ := hex1
      refine ⟨fun v => if v ∈ args2 then ext2 v else ext1 v, ?_⟩
      rw [Term.denoteTyped_ctx_congr ufInterp _ divByZero modByZero e2 hctx hbodyM hbody_e2]
      rw [hcombine ext1 ext2]
      exact hex2

/-- **Decomposition of a well-typed quantifier.** `.quant qk vs tr body` type-checks at `τ` iff its body
    type-checks at `Bool` (in the binder-extended context), every bound sort is well-formed, every trigger
    pattern type-checks, and `τ = Bool`. `Term.typeCheck` ignores the quantifier kind, so the fact is
    uniform in `qk`. -/
theorem Term.typeCheck_quant_ok_iff {ctx : TypedContext} {qk : Strata.SMT.QuantifierKind}
    {vs : List TermVar} {tr : List (List Term)} {body : Term} {τ : TermType} :
    Term.typeCheck ctx (.quant qk vs tr body) = .ok τ
      ↔ (Term.typeCheck {ctx with Γ := vs.reverse ++ ctx.Γ} body = .ok .bool
          ∧ (vs.all (fun v => TermType.WFSort ctx.uss v.ty)) = true
          ∧ Term.wfTriggers {ctx with Γ := vs.reverse ++ ctx.Γ} tr = true
          ∧ τ = .bool) := by
  constructor
  · intro h
    simp only [Term.typeCheck, bind, Except.bind] at h
    split at h <;> (try split at h) <;> simp_all
  · rintro ⟨hbody, hA, hB, rfl⟩
    simp [Term.typeCheck, bind, Except.bind, hbody, hA, hB]

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

/-! ## `Term.typeCheck` monotonicity under UF-context extension
The UF-app arm gates on `uf ∈ ctx.ufs` (exact membership), which is monotone under a superset; every
other arm ignores `ctx.ufs` (recurses / uses `uss`/`Γ` only). So a term well-typed at `ufs` stays
well-typed (to the same type) at any `ufs' ⊇ ufs`.
-/

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

/- ── `typeCheck` shape lemmas for `distinct` / UF applications. ── -/

/-- A list all type-checking at `ty` type-checks as `distinct`'s argument vector. -/
private theorem distinct_args_tc {ufs : UFCtx} {ty : TermType} :
    ∀ (ts : List Term), (∀ i (hi : i < ts.length), Term.typeCheck ⟨[], ufs, []⟩ ts[i] = .ok ty) →
      Term.typeCheckArgs ⟨[], ufs, []⟩ ts (List.replicate ts.length ty) = true := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t rest ih =>
    intro h
    rw [List.length_cons, List.replicate_succ]
    have h0 : Term.typeCheck ⟨[], ufs, []⟩ t = .ok ty := by have := h 0 (by simp); simpa using this
    simp only [Term.typeCheckArgs, h0, beq_self_eq_true, Bool.true_and]
    exact ih (fun i hi => by have := h (i+1) (by simp only [List.length_cons]; omega); simpa using this)

/-- `distinct` over a `≥2`-element list, all at base sort `ty`, type-checks to `.bool`. -/
theorem distinct_typeCheck {ufs : UFCtx} {ts : List Term} {ty : TermType} {t1 t2 : Term} {rest : List Term}
    (hts : ts = t1 :: t2 :: rest)
    (h : ∀ i (hi : i < ts.length), Term.typeCheck ⟨[], ufs, []⟩ ts[i] = .ok ty) :
    Term.typeCheck ⟨[], ufs, []⟩ (.app (.core .distinct) ts .bool) = .ok .bool := by
  subst hts
  have h1 : Term.typeCheck ⟨[], ufs, []⟩ t1 = .ok ty := by have := h 0 (by simp); simpa using this
  have hargs : Term.typeCheckArgs ⟨[], ufs, []⟩ (t2 :: rest) (List.replicate (t2 :: rest).length ty) = true := by
    apply distinct_args_tc
    intro i hi
    have := h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega); simpa using this
  simp only [Term.typeCheck, h1, bind, Except.bind, hargs, beq_self_eq_true, Bool.and_true, if_true]

/-- Inversion for a UF-application type-check: the args match `uf.args` and the result is `uf.out`. -/
theorem tc_uf_inv {Γ : List TermVar} {ufs : UFCtx} {uf : UF}
    {args : List Term} {rty τ : TermType}
    (h : Term.typeCheck ⟨[], ufs, Γ⟩ (.app (.core (.uf uf)) args rty) = .ok τ) :
    Term.typeCheckArgs ⟨[], ufs, Γ⟩ args uf.args = true ∧ τ = uf.out := by
  simp only [Term.typeCheck] at h
  split at h <;> (try split at h) <;> simp_all

/-- Peel the head off a homogeneous (`List.replicate`) `typeCheckArgs` obligation. -/
private theorem tcArgs_rest {ufs : UFCtx} {Γ : List TermVar} {t : Term} {ts : List Term}
    {ty : TermType}
    (htc : Term.typeCheckArgs ⟨[], ufs, Γ⟩ (t::ts) (ty :: List.replicate ts.length ty) = true) :
    Term.typeCheckArgs ⟨[], ufs, Γ⟩ ts (List.replicate ts.length ty) = true := by
  simp only [Term.typeCheckArgs] at htc
  split at htc
  · rename_i ty' he; simp only [Bool.and_eq_true] at htc; exact htc.2
  · exact absurd htc (by simp)

/- ── Base-sort witnesses. ── -/

/-- The four base SMT sorts a `TermType.isBase` witness ranges over. -/
theorem isBase_cases {τ : TermType} (h : TermType.isBase τ = true) :
    τ = .bool ∨ τ = .int ∨ τ = .string ∨ ∃ n, τ = .bitvec n := by
  cases τ with
  | prim p =>
    cases p with
    | bool => exact Or.inl rfl
    | int => exact Or.inr (Or.inl rfl)
    | string => exact Or.inr (Or.inr (Or.inl rfl))
    | bitvec n => exact Or.inr (Or.inr (Or.inr ⟨n, rfl⟩))
    | _ => simp [TermType.isBase] at h
  | option _ => simp [TermType.isBase] at h
  | constr _ _ => simp [TermType.isBase] at h

/-- A term that type-checks at a base SMT sort is neither a `.some` nor a `.none` (those are options). -/
theorem not_someNone_of_base {ufs : UFCtx} {bvs : TermVarCtx} {t : Term} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true) (h : Term.typeCheck ⟨[], ufs, bvs⟩ t = .ok smtτ') :
    (∀ a, t ≠ .some a) ∧ (∀ ty, t ≠ .none ty) := by
  refine ⟨fun a ha => ?_, fun ty ha => ?_⟩
  · subst ha
    obtain ⟨τ', _, heq⟩ := Term.typeCheck_some_inv h
    rcases isBase_cases hb with rfl | rfl | rfl | ⟨n, rfl⟩ <;> simp_all
  · subst ha
    have heq := Term.typeCheck_none_inv h
    rcases isBase_cases hb with rfl | rfl | rfl | ⟨n, rfl⟩ <;> simp_all

/- ── `Term.denoteTyped` congruence + primitive/variable value lemmas. ── -/

/-- `Term.denoteTyped` respects term equality: equal terms denote equally (the typecheck proof is a `Prop`,
    hence irrelevant). Lets us rewrite the term without hitting the dependent-motive wall that `rw` on
    the raw `if`/`match` inside a `Term.denoteTyped _ … hproof` application would cause. -/
theorem Term.denoteTyped_congr
    {ctx : TypedContext} {ufInterp : UFInterp σ 𝒜} {env : VarEnv σ 𝒜}
    {divByZero modByZero : Int → Int} {t1 t2 : Term} {τ : TermType}
    (heqt : t1 = t2) (h1 : Term.typeCheck ctx t1 = .ok τ) (h2 : Term.typeCheck ctx t2 = .ok τ) :
    Term.denoteTyped ufInterp env divByZero modByZero t1 τ h1
      = Term.denoteTyped ufInterp env divByZero modByZero t2 τ h2 := by
  subst heqt; rfl

/-- `Term.denoteTyped` for a variable is HEq to the environment lookup. -/
theorem SMTTerm_denote_var_heq {Γ : List TermVar} {ufs : UFCtx}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜) {divByZero modByZero : Int → Int}
    (v : TermVar) (τ : TermType) (htc : Term.typeCheck ⟨[], ufs, Γ⟩ (.var v) = .ok τ) :
    HEq (Term.denoteTyped ufInterp env divByZero modByZero (.var v) τ htc) (env v) := by
  unfold Term.denoteTyped
  obtain ⟨hmem, heq⟩ := Term.typeCheck_var_inv htc
  simp only
  exact cast_heq _ _

theorem denote_prim_bool {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) {dz mz : Int → Int}
    {b : Bool} (h : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim (.bool b)) = .ok .bool) :
    Term.denoteTyped ufInterp smtEnv dz mz (.prim (.bool b)) .bool h = b := by
  simp only [Term.denoteTyped]

theorem denote_prim_int {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) {dz mz : Int → Int}
    {i : Int} (h : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim (.int i)) = .ok .int) :
    Term.denoteTyped ufInterp smtEnv dz mz (.prim (.int i)) .int h = i := by
  simp only [Term.denoteTyped]

theorem denote_prim_string {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) {dz mz : Int → Int}
    {s : String} (h : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim (.string s)) = .ok .string) :
    Term.denoteTyped ufInterp smtEnv dz mz (.prim (.string s)) .string h = s := by
  simp only [Term.denoteTyped]

theorem denote_prim_bitvec {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) {dz mz : Int → Int}
    {n : Nat} {bv : BitVec n} (h : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim (.bitvec bv)) = .ok (.bitvec n)) :
    Term.denoteTyped ufInterp smtEnv dz mz (.prim (.bitvec bv)) (.bitvec n) h = bv := by
  simp only [Term.denoteTyped]

/-- Distinct primitive literals (at the same base sort) have distinct denotations. -/
theorem denote_prim_inj {ufs : UFCtx} {bvs : TermVarCtx}
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) {dz mz : Int → Int}
    {p1 p2 : TermPrim} {smtτ' : TermType}
    (hb : TermType.isBase smtτ' = true)
    (h1 : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim p1) = .ok smtτ')
    (h2 : Term.typeCheck ⟨[], ufs, bvs⟩ (.prim p2) = .ok smtτ')
    (hne : (Term.prim p1) ≠ (Term.prim p2)) :
    Term.denoteTyped ufInterp smtEnv dz mz (.prim p1) smtτ' h1
      ≠ Term.denoteTyped ufInterp smtEnv dz mz (.prim p2) smtτ' h2 := by
  intro hcontra
  apply hne
  have e1 := Term.typeCheck_prim_inv h1
  have e2 := Term.typeCheck_prim_inv h2
  rcases isBase_cases hb with rfl | rfl | rfl | ⟨n, rfl⟩
  · obtain ⟨b1, rfl⟩ : ∃ b, p1 = .bool b := by
      cases p1 with
      | bool b => exact ⟨b, rfl⟩
      | _ => simp [TermPrim.typeOf] at e1
    obtain ⟨b2, rfl⟩ : ∃ b, p2 = .bool b := by
      cases p2 with
      | bool b => exact ⟨b, rfl⟩
      | _ => simp [TermPrim.typeOf] at e2
    rw [denote_prim_bool, denote_prim_bool] at hcontra; subst hcontra; rfl
  · obtain ⟨i1, rfl⟩ : ∃ i, p1 = .int i := by
      cases p1 with
      | int i => exact ⟨i, rfl⟩
      | _ => simp [TermPrim.typeOf] at e1
    obtain ⟨i2, rfl⟩ : ∃ i, p2 = .int i := by
      cases p2 with
      | int i => exact ⟨i, rfl⟩
      | _ => simp [TermPrim.typeOf] at e2
    rw [denote_prim_int, denote_prim_int] at hcontra; subst hcontra; rfl
  · obtain ⟨s1, rfl⟩ : ∃ s, p1 = .string s := by
      cases p1 with
      | string s => exact ⟨s, rfl⟩
      | _ => simp [TermPrim.typeOf] at e1
    obtain ⟨s2, rfl⟩ : ∃ s, p2 = .string s := by
      cases p2 with
      | string s => exact ⟨s, rfl⟩
      | _ => simp [TermPrim.typeOf] at e2
    rw [denote_prim_string, denote_prim_string] at hcontra; subst hcontra; rfl
  · obtain ⟨bv1, rfl⟩ : ∃ bv : BitVec n, p1 = .bitvec bv := by
      cases p1 with
      | bitvec bv =>
        rename_i m
        have hmn : m = n := by
          have h' : TermType.bitvec m = TermType.bitvec n := by simpa only [TermPrim.typeOf] using e1.symm
          simpa only [TermType.bitvec, TermType.prim.injEq, TermPrimType.bitvec.injEq] using h'
        subst hmn; exact ⟨bv, rfl⟩
      | _ => simp [TermPrim.typeOf] at e1
    obtain ⟨bv2, rfl⟩ : ∃ bv : BitVec n, p2 = .bitvec bv := by
      cases p2 with
      | bitvec bv =>
        rename_i m
        have hmn : m = n := by
          have h' : TermType.bitvec m = TermType.bitvec n := by simpa only [TermPrim.typeOf] using e2.symm
          simpa only [TermType.bitvec, TermType.prim.injEq, TermPrimType.bitvec.injEq] using h'
        subst hmn; exact ⟨bv, rfl⟩
      | _ => simp [TermPrim.typeOf] at e2
    rw [denote_prim_bitvec, denote_prim_bitvec] at hcontra; subst hcontra; rfl

/- ── HList / distinct transfer helpers. ── -/

theorem hlist_len {α} {f : α → Type} {a : α} : ∀ (n : Nat) (hl : HList f (List.replicate n a)),
    (hlistReplicateToList n hl).length = n := by
  intro n; induction n with
  | zero => intro hl; rfl
  | succ m ih => intro hl; match hl with | .cons x xs => simp [hlistReplicateToList, ih]

theorem hlist_getElem {ufs : UFCtx} {Γ : List TermVar}
    (ufInterp : UFInterp σ 𝒜) (env : VarEnv σ 𝒜)
    {divByZero modByZero : Int → Int}
    (ty : TermType) : ∀ (args : List Term)
    (htc : Term.typeCheckArgs ⟨[], ufs, Γ⟩ args (List.replicate args.length ty) = true)
    (i : Nat) (hi : i < args.length) (htci : Term.typeCheck ⟨[], ufs, Γ⟩ args[i] = .ok ty),
    (hlistReplicateToList args.length
      (Term.denoteTypedArgs ufInterp env divByZero modByZero args (List.replicate args.length ty) htc))[i]'(by rw [hlist_len]; exact hi)
    = Term.denoteTyped ufInterp env divByZero modByZero args[i] ty htci := by
  intro args
  induction args with
  | nil => intro htc i hi htci; simp at hi
  | cons t ts ih =>
    intro htc i hi htci
    match i, hi with
    | 0, _ => rfl
    | j+1, hj =>
      have hjlt : j < ts.length := by simpa using hj
      have htcj : Term.typeCheck ⟨[], ufs, Γ⟩ ts[j] = .ok ty := htci
      have htcrest := tcArgs_rest htc
      have hstep : (hlistReplicateToList (t::ts).length
          (Term.denoteTypedArgs ufInterp env divByZero modByZero (t::ts) (List.replicate (t::ts).length ty) htc))[j+1]'(by rw [hlist_len]; exact hj)
        = (hlistReplicateToList ts.length
            (Term.denoteTypedArgs ufInterp env divByZero modByZero ts (List.replicate ts.length ty) htcrest))[j]'(by rw [hlist_len]; exact hjlt) := rfl
      rw [hstep]; exact ih htcrest j hjlt htcj

end Strata.SMT.DenoteTyped

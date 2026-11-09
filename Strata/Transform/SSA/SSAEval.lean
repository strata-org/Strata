/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSAProps
public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.Shadow
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.BigStep.SemProps

/-! # The evaluator facts of the SSA phase's correctness proofs

The facts about evaluation that the correctness proofs of the SSA phase use, stated over the
relation `EvalsTo F σ e v` ("`e` evaluates to `v`", `CmdSemantics.lean`). The SSA proofs reach
the evaluator only through these facts and through `EvalsTo.det`, `EvalsTo.value` and
`EvalsTo.var` (`CmdSemanticsProps.lean`):

* a literal evaluates to itself (`evalsTo_lit`, `evalsTo_boolLit`);
* renaming an obligation keeps its values (`evalsTo_renM'`);
* folding is a refinement of evaluation (`evalsTo_foldE`);
* an `init` of an unbound name with a value of its type runs (`run_init`).

The two stores of these facts agree on a name `x` under the SSA mapping `ρ` when `x` has a value
`w` in the guarded store `σL` that its current value holds in the obligation store `σS`
(`SHolds`, `SAgree`).

Key theorems: `evalsTo_renM'`, `evalsTo_foldE`, `evalsTo_lit`, `run_init`.

Key definitions: `SHolds`, `SAgree`. -/

namespace Imperative

namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]
  [iOp : HasOps P] [iLFv : LawfulHasFvar P] [iLFvs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iOp iLFv iLFvs
variable {F : P.Factory} {σS σL σ : SemanticStore P} {x : P.Ident} {w : P.Val}
  {ρ : Std.HashMap P.Ident (SVal P)} {l : String} {md : MetaData P}

/-! ## Agreement of the two stores -/

/-- The current value `o` of the name `x` holds `w` in the obligation store `σS`: a variable
    holds `w`, which has the type the variable is annotated with; a literal is `w`, and the
    name defined for it holds `w`; an unmapped name holds `w` itself. -/
@[expose] def SHolds (F : P.Factory) (σS : SemanticStore P) (x : P.Ident) (w : P.Val) :
    Option (SVal P) → Prop
  | some (.name y ty) => σS y = some w ∧ ∀ T, ty = some T → HasVal.valueOfTy F w T
  | some (.lit b m) => w = (if b then HasBool.ttVal F else HasBool.ffVal F) ∧
      ∃ y, m = some y ∧ σS y = some w
  | none => σS x = some w

/-- The guarded store and the obligation store agree on `x` under the mapping `ρ`. -/
@[expose] def SAgree (F : P.Factory) (ρ : Std.HashMap P.Ident (SVal P))
    (σL σS : SemanticStore P) (x : P.Ident) : Prop := ∃ w, σL x = some w ∧ SHolds F σS x w ρ[x]?

/-! ## Evaluation as a relation -/

omit iBE iHI iHa iWL iLV in
/-- A literal evaluates to its value. -/
theorem evalsTo_lit (F : P.Factory) (hF : SSALaws F) (σ : SemanticStore P) (b : Bool) :
    EvalsTo F σ (if b then tt else ff) (if b then HasBool.ttVal F else HasBool.ffVal F) := by
  cases b <;> first | exact hF.val.eval_ff σ | exact hF.val.eval_tt σ

omit iBE iLB iHI iLI iHa iLV in
/-- An expression the language recognizes as the literal `b` evaluates only to `b`. -/
theorem evalsTo_boolLit (hF : SSALaws F) {e : P.Expr} {v : P.Val} {b : Bool}
    (hb : WPOps.boolLit? e = some b) (h : EvalsTo F σ e v) :
    v = if b then HasBool.ttVal F else HasBool.ffVal F :=
  h.det (WPLang.boolLit?_eq hb ▸ evalsTo_lit F hF σ b)

omit iHI iLV in
/-- Substituting, by `g`, for free variables of `e` variables holding their value or the Boolean
    literals equal to it preserves the value of `e`, when the free variables `g` leaves agree. -/
private theorem ev_substFn (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) (e : P.Expr) (g : P.Ident → Option P.Expr)
    (hk : ∀ x ∈ HasFvars.getFvars e, ∀ v, g x = some v →
      (∃ y, (v = HasFvar.mkFvar y ∨ ∃ ty, v = HasFvar.mkTypedFvar y ty) ∧ σS y = σL x ∧
        (σL x).isSome) ∨ (v = tt ∧ σL x = some (HasBool.ttVal F)) ∨
        (v = ff ∧ σL x = some (HasBool.ffVal F)))
    (hn : ∀ x ∈ HasFvars.getFvars e, g x = none → σS x = σL x) :
    P.eval F σS (WPOps.substFn e g) = P.eval F σL e := by
  rw [WPLang.substFn_eq e g _ fun x hx => (Map.find?_filterMap_self g _ x (mem_exprFV.2 hx)).symm]
  refine hF.lits hCS hCL _ e (fun k v hk' => ?_) (fun x hx hn' => hn x hx ?_)
  · obtain ⟨z, hz, hf⟩ := Map.find?_filterMap_some _ _ k v hk'
    cases h : g z <;> grind [mem_exprFV]
  · rwa [Map.find?_filterMap_self _ _ x (mem_exprFV.2 hx)] at hn'

omit iHI iHa iLV in
/-- Two expressions that are the same variable or the same literal have the same value. -/
private theorem sameValue_ev (hF : SSALaws F) (hC : WellFormedStore σ F) {a b : P.Expr}
    (h : sameValue a b = true) : P.eval F σ a = P.eval F σ b := by
  unfold sameValue at h
  repeat' split at h <;> grind [hF.var a, hF.var b, → WPLang.boolLit?_eq]

omit iHI iLV in
/-- **Folding is a refinement.**  Under agreement on the free variables of `e`, the folded
    expression evaluates to `v` whenever `e` does (an `ite` whose branches fold to the same
    value may have a value when its condition has none). -/
theorem evalsTo_foldE (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    ∀ {v : P.Val}, (∀ x ∈ HasFvars.getFvars e, SAgree F ρ σL σS x) → EvalsTo F σL e v →
      EvalsTo F σS (foldE ρ e) v := by
  unfold EvalsTo
  fun_induction foldE ρ e <;> intro v hA he
  case case5 e _ =>
    refine (ev_substFn hF hCL hCS e _ (fun x hx w hw => ?_) fun x hx hn => ?_).trans he
    all_goals obtain ⟨w, h1, h2⟩ := hA x hx
    · rcases h : ρ[x]? with _ | (⟨y, _ | ty⟩ | ⟨_ | _, m⟩) <;>
        grind [SHolds, SVal.expr, HasFvar.mkVar]
    · simp_all [SHolds]
  all_goals
    obtain rfl := WPLang.iteView?_eq ‹_›
    have hA' := fun x hx => hA x ((WPLang.getFvars_ite _ _ _ x).2 hx)
  case case1 c t f c' hb ihc ihb _ | case2 c t f c' hb ihc ihb _ =>
    rcases WPLang.ev_ite_inv he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    all_goals first
      | exact ihb (fun x hx => hA' x (by simp [hx])) h2
      | have hc := ihc (fun x hx => hA' x (.inl hx)) h1
        simp only [c'] at hb
        simp_all [WPLang.boolLit?_eq hb, hF.val.eval_tt, hF.val.eval_ff, HasBool.ttVal_ne_ffVal,
          (HasBool.ttVal_ne_ffVal F).symm]
  case case3 c t f c' _ t' f' hs _ iht ihf _ =>
    rcases WPLang.ev_ite_inv he with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact iht (fun x hx => hA' x (.inr (.inl hx))) h2
    · exact (sameValue_ev hF hCS hs).trans (ihf (fun x hx => hA' x (.inr (.inr hx))) h2)
  case case4 c t f c' _ t' f' _ ihc iht ihf _ =>
    exact WPLang.ev_ite_congr he (fun _ => ihc fun x hx => hA' x (.inl hx))
      (fun _ => iht fun x hx => hA' x (.inr (.inl hx)))
      (fun _ => ihf fun x hx => hA' x (.inr (.inr hx)))

omit iBE iHI iHa iWL iLV in
/-- An `init` of an unbound name with a value of its type, to which its initializer evaluates
    when it has one, runs from a store to the store updated at the name. -/
theorem run_init (hF : SSALaws F) {ty : P.Ty} {e : ExprOrNondet P} {v : P.Val}
    (h0 : σ x = none) (hty : HasVal.valueOfTy F v ty)
    (he : ∀ e', e = .det e' → EvalsTo F σ e' v) :
    BRun F [mkInit x ty e] σ [] (.normal (SemanticStore.update σ x v)) := by
  obtain ⟨u1, u2⟩ := update_facts σ x v
  refine BRun.cons_normal (evs1 := []) (evs2 := []) (BRunS.cmd ?_) .nil
  cases e <;> constructor <;> first | exact he _ rfl | exact ⟨h0, u1, u2⟩ | exact hF.var | exact hty

omit iHF iSF iHI iHFs iLV in
/-- The variable an obligation reads for `x` holds the value of `x`; with no such variable, `x`
    itself holds it. -/
theorem oblVar_holds (h : SHolds F σS x w ρ[x]?) :
    match oblVar ρ x with
    | some (y, _) => σS y = some w
    | none => σS x = some w := by
  rcases hρ : ρ[x]? with _ | (_ | ⟨_, _ | _⟩) <;> grind [oblVar, SHolds]

omit iHI iLI iLV in
/-- Renaming an obligation's free variables to the variables it reads for them (`renM'`) keeps
    its values, when the two stores agree on its free variables. -/
theorem evalsTo_renM' (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) {e : P.Expr} {v : P.Val}
    (hA : ∀ x ∈ HasFvars.getFvars e, SAgree F ρ σL σS x) :
    EvalsTo F σS (renM' ρ e) v ↔ EvalsTo F σL e v := by
  refine iff_of_eq (congrArg (· = some v) (ev_substFn hF hCL hCS _ _ (fun x hx v hv => ?_)
    (fun x hx hn => ?_)))
  · obtain ⟨w, hw, ho⟩ := Exists.imp (fun _ => And.imp_right oblVar_holds) (hA x hx)
    rcases hov : oblVar ρ x with _ | ⟨y, _ | ty⟩ <;> simp only [hov, Option.map] at hv ho <;>
      grind [HasFvar.mkVar]
  · obtain ⟨w, hw, ho⟩ := Exists.imp (fun _ => And.imp_right oblVar_holds) (hA x hx)
    rcases hov : oblVar ρ x with _ | ⟨y, ty⟩ <;> simp_all

end -- public section

end WP
end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSAProps
public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.Shadow
import Strata.DL.Imperative.CmdSemanticsProps
public import Strata.DL.Imperative.Logic.TraceRelationsProps

/-! # The evaluator facts of the SSA phase's correctness proofs

The facts about evaluation that the correctness proofs of the SSA phase use, stated over the
relation `EvalsTo F σ e v` ("`e` evaluates to `v`"), so that every other proof reaches the
evaluator only through them:

* evaluation is deterministic (`EvalsTo.det`), its results are values (`EvalsTo.value`), a
  variable evaluates to its value in the store (`EvalsTo.var`), and a literal to itself
  (`evalsTo_lit`, `EvalsTo.boolLit`);
* renaming an obligation keeps its values (`evalsTo_renM'`);
* folding is a refinement of evaluation (`evalsTo_foldE`);
* an `init` of an unbound name with a value of its type runs (`run_init`);
* the steps of deterministic `init` and `set` evaluate their initializer
  (`evalE_init_det_evalsTo`, `evalE_set_det_evalsTo`), and command steps keep stores
  well formed (`evalE_wellFormed`);
* a condition holds under evaluation to `true` when it evaluates to `true`
  (`evalInterp_holds_iff`); an assumption, an assertion or a cover of the obligation program is
  a counterpart of the guarded program's under `Event.WeakensAssume` (`weakensAssume_assume`,
  `weakensAssume_check`), and a failing assertion or cover carries over (`failsAt_transfer`);

The two stores of these facts agree on a name `x` under the SSA mapping `ρ` when `x` has a value
`w` in the guarded store `σL` that its current value holds in the obligation store `σS`
(`SHolds`, `SAgree`).

Key theorems: `EvalsTo.det`, `evalsTo_renM'`, `evalsTo_foldE`, `evalsTo_lit`, `run_init`,
`evalInterp_holds_iff`, `weakensAssume_assume`, `weakensAssume_check`, `failsAt_transfer`.

Key definitions: `EvalsTo`, `SHolds`, `SAgree`. -/

namespace Imperative

namespace WP

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iLI : LawfulHasIdent P] [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]
  [iOp : HasOps P] [iLFv : LawfulHasFvar P] [iLFvs : LawfulHasFvars P] [iLV : LawfulHasVal P]
omit iOp iLFv iLFvs
variable {F : P.Factory} {σS σL σ : SemanticStore P} {x : P.Ident} {w : P.Expr}
  {ρ : Std.HashMap P.Ident (SVal P)} {l : String} {md : MetaData P}

/-! ## Agreement of the two stores -/

/-- The current value `o` of the name `x` holds `w` in the obligation store `σS`: a variable
    holds `w`, which has the type the variable is annotated with; a literal is `w`, and the
    name defined for it holds `w`; an unmapped name holds `w` itself. -/
@[expose] def SHolds (F : P.Factory) (σS : SemanticStore P) (x : P.Ident) (w : P.Expr) :
    Option (SVal P) → Prop
  | some (.name y ty) => σS y = some w ∧ ∀ T, ty = some T → HasVal.valueOfTy F w T
  | some (.lit b m) => w = (if b then tt else ff) ∧ ∃ y, m = some y ∧ σS y = some w
  | none => σS x = some w

/-- The guarded store and the obligation store agree on `x` under the mapping `ρ`. -/
@[expose] def SAgree (F : P.Factory) (ρ : Std.HashMap P.Ident (SVal P))
    (σL σS : SemanticStore P) (x : P.Ident) : Prop := ∃ w, σL x = some w ∧ SHolds F σS x w ρ[x]?

/-! ## Evaluation as a relation -/

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- The expression `e` evaluates to `v` under the factory `F` in the store `σ`.  An expression
    with no value (a stuck evaluation) is one with `¬ ∃ v, EvalsTo F σ e v`. -/
@[expose] def EvalsTo (F : P.Factory) (σ : SemanticStore P) (e v : P.Expr) : Prop :=
  P.eval F σ e = some v

omit iDE iBE iLB iHB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- **Evaluation is deterministic.** -/
theorem EvalsTo.det {e v v' : P.Expr} (h : EvalsTo F σ e v) (h' : EvalsTo F σ e v') : v = v' :=
  Option.some.inj (h.symm.trans h')

omit iBE iLB iHI iLI iHa iWL iLV in
/-- The value of an expression in a well-formed store is a value. -/
theorem EvalsTo.value (hF : SSALaws F) (hC : WellFormedStore σ F) {e v : P.Expr}
    (h : EvalsTo F σ e v) : HasVal.value F v :=
  ev_value hF.val hC h

omit iBE iLB iHI iLI iHa iWL iLV in
/-- A variable evaluates, in a well-formed store, to the value the store gives it. -/
theorem EvalsTo.var (hF : SSALaws F) (hC : WellFormedStore σ F) {e v : P.Expr} {y : P.Ident}
    (hy : HasFvar.getFvar e = some y) (h : EvalsTo F σ e v) : σ y = some v :=
  (hF.var e y σ hC hy).symm.trans h

omit iBE iHI iHa iWL in
/-- A literal evaluates to itself. -/
theorem evalsTo_lit (F : P.Factory) (hF : SSALaws F) (σ : SemanticStore P) (b : Bool) :
    EvalsTo F σ (if b then tt else ff) (if b then tt else ff) := by
  cases b <;> first | exact ev_ff hF.val σ | exact ev_tt hF.val σ

omit iBE iLB iHI iLI iHa in
/-- An expression the language recognizes as the literal `b` evaluates only to `b`. -/
theorem EvalsTo.boolLit (hF : SSALaws F) {e v : P.Expr} {b : Bool}
    (hb : WPOps.boolLit? e = some b) (h : EvalsTo F σ e v) : v = if b then tt else ff :=
  h.det (WPLang.boolLit?_eq hb ▸ evalsTo_lit F hF σ b)

omit iHI iLV in
/-- Substituting, by `g`, for free variables of `e` variables holding their value or the Boolean
    literals equal to it preserves the value of `e`, when the free variables `g` leaves agree. -/
private theorem ev_substFn (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) (e : P.Expr) (g : P.Ident → Option P.Expr)
    (hk : ∀ x ∈ HasFvars.getFvars e, ∀ v, g x = some v →
      (∃ y, (v = HasFvar.mkFvar y ∨ ∃ ty, v = HasFvar.mkTypedFvar y ty) ∧ σS y = σL x ∧
        (σL x).isSome) ∨ (v = tt ∧ σL x = some tt) ∨ (v = ff ∧ σL x = some ff))
    (hn : ∀ x ∈ HasFvars.getFvars e, g x = none → σS x = σL x) :
    ev F σS (WPOps.substFn e g) = ev F σL e := by
  rw [WPLang.substFn_eq e g _ fun x hx => (Map.find?_filterMap_self g _ x (mem_exprFV.2 hx)).symm]
  refine hF.lits hCS hCL _ e (fun k v hk' => ?_) (fun x hx hn' => hn x hx ?_)
  · obtain ⟨z, hz, hf⟩ := Map.find?_filterMap_some _ _ k v hk'
    cases h : g z <;> grind [mem_exprFV]
  · rwa [Map.find?_filterMap_self _ _ x (mem_exprFV.2 hx)] at hn'

omit iHI iHa iLV in
/-- Two expressions that are the same variable or the same literal have the same value. -/
private theorem sameValue_ev (hF : SSALaws F) (hC : WellFormedStore σ F) {a b : P.Expr}
    (h : sameValue a b = true) : ev F σ a = ev F σ b := by
  unfold sameValue at h
  repeat' split at h <;> grind [hF.var a, hF.var b, → WPLang.boolLit?_eq]

omit iHI in
/-- **Folding is a refinement.**  Under agreement on the free variables of `e`, the folded
    expression evaluates to `v` whenever `e` does (an `ite` whose branches fold to the same
    value may have a value when its condition has none). -/
theorem evalsTo_foldE (hF : SSALaws F) (hCL : WellFormedStore σL F)
    (hCS : WellFormedStore σS F) (ρ : Std.HashMap P.Ident (SVal P)) (e : P.Expr) :
    ∀ {v : P.Expr}, (∀ x ∈ HasFvars.getFvars e, SAgree F ρ σL σS x) → EvalsTo F σL e v →
      EvalsTo F σS (foldE ρ e) v := by
  unfold EvalsTo
  fun_induction foldE ρ e <;> intro v hA he
  case case5 e _ =>
    refine (ev_substFn hF hCL hCS e _ (fun x hx w hw => ?_) fun x hx hn => ?_).trans he
    all_goals obtain ⟨w, h1, h2⟩ := hA x hx
    · rcases h : ρ[x]? with _ | (⟨y, _ | ty⟩ | ⟨_ | _, m⟩) <;> grind [SHolds, SVal.expr, var]
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
        simp_all [WPLang.boolLit?_eq hb, ev_tt hF.val, ev_ff hF.val, tt_ne_ff', ff_ne_tt']
  case case3 c t f c' _ t' f' hs _ iht ihf _ =>
    rcases WPLang.ev_ite_inv he with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact iht (fun x hx => hA' x (.inr (.inl hx))) h2
    · exact (sameValue_ev hF hCS hs).trans (ihf (fun x hx => hA' x (.inr (.inr hx))) h2)
  case case4 c t f c' _ t' f' _ ihc iht ihf _ =>
    rcases WPLang.ev_ite_inv he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact WPLang.ev_ite_true (ihc (fun x hx => hA' x (.inl hx)) h1)
        (iht (fun x hx => hA' x (.inr (.inl hx))) h2)
    · exact WPLang.ev_ite_false (ihc (fun x hx => hA' x (.inl hx)) h1)
        (ihf (fun x hx => hA' x (.inr (.inr hx))) h2)

omit iBE iHI iHa iWL iLV in
/-- An `init` of an unbound name with a value of its type, to which its initializer evaluates
    when it has one, runs from a store to the store updated at the name. -/
theorem run_init (hF : SSALaws F) {ty : P.Ty} {e : ExprOrNondet P} {v : P.Expr}
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
    (hCS : WellFormedStore σS F) {e v : P.Expr}
    (hA : ∀ x ∈ HasFvars.getFvars e, SAgree F ρ σL σS x) :
    EvalsTo F σS (renM' ρ e) v ↔ EvalsTo F σL e v := by
  refine iff_of_eq (congrArg (· = some v) (ev_substFn hF hCL hCS _ _ (fun x hx v hv => ?_)
    (fun x hx hn => ?_)))
  · obtain ⟨w, hw, ho⟩ := Exists.imp (fun _ => And.imp_right oblVar_holds) (hA x hx)
    rcases hov : oblVar ρ x with _ | ⟨y, _ | ty⟩ <;> simp only [hov, Option.map] at hv ho <;>
      grind [var]
  · obtain ⟨w, hw, ho⟩ := Exists.imp (fun _ => And.imp_right oblVar_holds) (hA x hx)
    rcases hov : oblVar ρ x with _ | ⟨y, ty⟩ <;> simp_all

/-! ## Command steps -/

omit iDE iBE iLB iSF iHI iLI iHa iHFs iWL iLV in
/-- A deterministic `init x := e` step evaluates `e` to a value `v` of type `ty`, defines the
    undefined `x` as `v`, leaves the other variables unchanged and emits no event. -/
theorem evalE_init_det_evalsTo {σ1 : SemanticStore P} {ty : P.Ty} {e : P.Expr}
    {evs : List (Event P)} (h : EvalE F σ (.cmd (.init x ty (.det e) md)) σ1 evs) :
    ∃ v, EvalsTo F σ e v ∧ σ x = none ∧ σ1 x = some v ∧ (∀ y, x ≠ y → σ1 y = σ y) ∧
      evs = [] ∧ HasVal.valueOfTy F v ty :=
  evalE_init_det_inv_typed h

omit iDE iBE iLB iSF iHI iLI iHa iHFs iWL iLV in
/-- A deterministic `set x := e` step evaluates `e` to a value `v` of the stored type of `x`,
    updates `x` to `v`, leaves the other variables unchanged and emits no event. -/
theorem evalE_set_det_evalsTo {σ1 : SemanticStore P} {e : P.Expr} {evs : List (Event P)}
    (h : EvalE F σ (.cmd (.set x (.det e) md)) σ1 evs) :
    ∃ v, EvalsTo F σ e v ∧ HasVal.valueOfStoredTy (P := P) F σ x v ∧ σ1 x = some v ∧
      (∀ y, x ≠ y → σ1 y = σ y) ∧ evs = [] :=
  evalE_set_det_inv h

omit iBE iLB iHI iLI iHa iWL in
/-- A command step from a well-formed store leads to a well-formed store. -/
theorem evalE_wellFormed (hF : SSALaws F) {c : Cmd P} {σ1 : SemanticStore P}
    {evs : List (Event P)} (h : EvalE F σ (.cmd c) σ1 evs) (hC : WellFormedStore σ F) :
    WellFormedStore σ1 F :=
  evalCmdE_storeWellDefined hF.val h hC

/-! ## Events under evaluation to `true` -/

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- A condition holds under evaluation to `true` exactly when it evaluates to `true`. -/
theorem evalInterp_holds_iff {w : (evalInterp (P := P)).World} {a : EventArg P} :
    evalInterp.holds w a ↔ EvalsTo a.factory a.store a.expr HasBool.tt := .rfl

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- An assumption of the obligation store whose condition evaluates to `true` whenever the
    guarded assumption's does is its counterpart under evaluation to `true`. -/
theorem weakensAssume_assume {a a' : P.Expr}
    (h : EvalsTo F σL a HasBool.tt → EvalsTo F σS a' HasBool.tt) :
    Event.WeakensAssume evalInterp
      (.assume { factory := F, store := σL, label := l, expr := a, metadata := md })
      (.assume { factory := F, store := σS, label := l, expr := a', metadata := md }) :=
  ⟨rfl, rfl, fun _ => h⟩

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- An assertion (a cover) of the obligation store whose condition evaluates to the values of
    the guarded one's is its counterpart under evaluation to `true`. -/
theorem weakensAssume_check {E : EventArg P → Event P} (hE : E = .assert ∨ E = .cover)
    {e e' : P.Expr} (h : ∀ v, EvalsTo F σS e' v ↔ EvalsTo F σL e v) :
    Event.WeakensAssume evalInterp
      (E { factory := F, store := σL, label := l, expr := e, metadata := md })
      (E { factory := F, store := σS, label := l, expr := e', metadata := md }) := by
  rcases hE with rfl | rfl <;> exact ⟨rfl, rfl, fun _ => (h _).symm⟩

omit iDE iBE iLB iHF iSF iHI iLI iHa iHFs iWL iLV in
/-- A failing occurrence of the target `t` by an assertion (a cover) of the guarded store has
    the target's label and condition, and the assertion (cover) of the obligation store with a
    condition evaluating to the same values is a failing occurrence of its own label and
    condition. -/
theorem failsAt_transfer {E : EventArg P → Event P} (hE : E = .assert ∨ E = .cover)
    {t : AssertId P} {e e' : P.Expr} (h : ∀ v, EvalsTo F σS e' v ↔ EvalsTo F σL e v)
    (hf : FailsAt t (E { factory := F, store := σL, label := l, expr := e, metadata := md })) :
    l = t.label ∧ e = t.expr ∧
      FailsAt ⟨l, e'⟩
        (E { factory := F, store := σS, label := l, expr := e', metadata := md }) := by
  rcases hE with rfl | rfl <;> exact ⟨hf.1, hf.2.1, rfl, rfl, (h _).2 hf.2.2⟩

end -- public section

end WP
end Imperative

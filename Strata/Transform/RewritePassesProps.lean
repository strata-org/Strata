/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwdProps
public import Strata.DL.Imperative.BigStep.SemProps
public import Strata.Transform.DeadDefElimProps
import all Strata.Transform.DeadDefElim
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Factory

/-! # Facts shared by the correctness proofs of the rewrite passes

The correctness proofs of guard forwarding, the inlining, guard propagation, the constructor fold
and the rewrite loop share:

* the value-typing and scope predicates of guard forwarding, which the inlining's walk reuses:
  having a common type (`SameTy`), the laws of the expression language the proofs use
  (`GuardFwdLaws`), the scope invariant (`ScopeInv`, `scopeInv_empty`), the guard map holding in
  a store (`GCons`), and the value of a forwarded candidate (`cand_sem`, `ite_sameTy`);
* the transitivity of the output relation of the erasure of unread definitions
  (`Core.GuardFwd.ddOut_trans`);
* that an extension of a factory keeps its functions (`Core.DefInline.addFactory_get`);
* the procedure bodies of the program transform every pass runs
  (`Core.Program.mapStructuredBodies_mem`, `Core.Program.mapStructuredBodies_proc`).

Key definitions: `Imperative.GuardFwd.SameTy`, `Imperative.GuardFwd.GuardFwdLaws`,
`Imperative.GuardFwd.ScopeInv`, `Imperative.GuardFwd.GCons`.

Key theorems: `Imperative.GuardFwd.cand_sem`, `Imperative.GuardFwd.scopeInv_empty`,
`Core.GuardFwd.ddOut_trans`, `Core.DefInline.addFactory_get`,
`Core.Program.mapStructuredBodies_mem`, `Core.Program.mapStructuredBodies_proc`. -/

namespace Imperative
namespace GuardFwd

open WP BigStep

public section

variable {P : PureExpr}

/-- The values `a` and `b` have a common type. -/
@[expose] def SameTy [HasVal P] (F : P.Factory) (a b : P.Val) : Prop :=
  ∃ ty, HasVal.valueOfTy F a ty ∧ HasVal.valueOfTy F b ty

/-- The variable bindings `o` and `o'` are equal, or values of a common type. -/
@[expose] def SameTyO [HasVal P] (F : P.Factory) (o o' : Option P.Val) : Prop :=
  o = o' ∨ ∃ a b, o = some a ∧ o' = some b ∧ SameTy F a b

/-- Having a common type is symmetric. -/
theorem SameTy.symm [HasVal P] {F : P.Factory} {a b : P.Val} (h : SameTy F a b) : SameTy F b a :=
  h.imp fun _ h => ⟨h.2, h.1⟩

/-- Having a common type is transitive, for a lawful typed-value predicate. -/
theorem SameTy.trans [HasVal P] [LawfulHasVal P] {F : P.Factory} {a b c : P.Val}
    (h1 : SameTy F a b) (h2 : SameTy F b c) : SameTy F a c :=
  h1.elim fun t1 ⟨ha, hb⟩ => h2.elim fun t2 ⟨hb2, hc⟩ =>
    ⟨t1, ha, LawfulHasVal.valueOfTy_congr F b c t1 t2 hb hb2 hc⟩

/-- Projecting a store `σ1` that keeps the variables defined in `σ` through `σ` gives `σ`. -/
theorem projectStore_keep {σ σ1 : SemanticStore P}
    (hk : ∀ x, (σ x).isSome → σ1 x = σ x) : projectStore σ σ1 = σ :=
  funext fun x => by by_cases hx : (σ x).isSome <;> simp_all [projectStore]

variable [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [HasSubstFvar P] [WPLang P]
  [GuardOps P]

/-- **The laws of guard forwarding.**  What the correctness proof of guard forwarding needs from
    the factory `F`, beyond the laws of `WPLang`: the laws for variables, values and congruence,
    substitution of expressions holding the values of the substituted variables, the existence of
    a type for every value, the preservation of a value's type when the free variables are given
    values of the same types, the evaluation of a conditional under strict evaluation (every
    part has a value, both arms of the same type), and the evaluation of an equality of a
    variable with itself. -/
structure GuardFwdLaws (F : P.Factory) : Prop where
  /-- Variables evaluate to their value in a well-formed store. -/
  var : WellFormedSemanticEvalVar (P := P) F
  /-- Results are values, and the Boolean literals evaluate to the Boolean values. -/
  val : WellFormedSemanticEvalVal (P := P) F
  /-- Evaluation depends only on the free variables. -/
  congr : WellFormedSemanticEvalExprCongr (P := P) F
  /-- Substituting expressions holding the values of the substituted variables preserves
      evaluation. -/
  subst : WellFormedSemanticEvalSubstExprs (P := P) F
  /-- Every value has a type. -/
  typed : ∀ {σ : SemanticStore P} {e : P.Expr} {v : P.Val}, P.eval F σ e = some v →
    ∃ ty, HasVal.valueOfTy F v ty
  /-- Giving the free variables values of the same types keeps a value of the same type. -/
  retype : ∀ {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Val}, WellFormedStore σ F →
    WellFormedStore σ' F → (∀ x ∈ HasFvars.getFvars e, SameTyO F (σ x) (σ' x)) →
    P.eval F σ e = some v → ∃ v', P.eval F σ' e = some v' ∧ SameTy F v v'
  /-- A value of the Boolean type is `true` or `false`. -/
  bool_cases : ∀ {w : P.Val}, SameTy F w (HasBool.ttVal F) →
    w = HasBool.ttVal F ∨ w = HasBool.ffVal F
  /-- A conditional with a value: its parts have values, the condition a Boolean one, the arms
      values of a common type, and its value is the arm the condition selects. -/
  ite_parts : ∀ {σ : SemanticStore P} {c t f : P.Expr} {v : P.Val},
    P.eval F σ (WPOps.ite c t f) = some v →
    ∃ wc wt wf, P.eval F σ c = some wc ∧ P.eval F σ t = some wt ∧ P.eval F σ f = some wf ∧
      SameTy F wc (HasBool.ttVal F) ∧ SameTy F wt wf ∧
      (wc = HasBool.ttVal F → v = wt) ∧ (wc = HasBool.ffVal F → v = wf)
  /-- A conditional whose parts have values, the condition a Boolean one and the arms values of a
      common type, has the value of the arm the condition selects. -/
  ite_build : ∀ {σ : SemanticStore P} {c t f : P.Expr} {wc wt wf : P.Val},
    P.eval F σ c = some wc → P.eval F σ t = some wt → P.eval F σ f = some wf →
    SameTy F wc (HasBool.ttVal F) → SameTy F wt wf →
    ∃ v, P.eval F σ (WPOps.ite c t f) = some v ∧
      (wc = HasBool.ttVal F → v = wt) ∧ (wc = HasBool.ffVal F → v = wf)
  /-- An equality of a variable defined in a well-formed store with itself is `true`. -/
  eq_refl : ∀ {σ : SemanticStore P} {e a b : P.Expr} {x : P.Ident},
    GuardOps.eqView? e = some (a, b) → HasFvar.getFvar a = some x → HasFvar.getFvar b = some x →
    WellFormedStore σ F → (σ x).isSome → P.eval F σ e = some (HasBool.ttVal F)

/-- A value is of its own type. -/
theorem GuardFwdLaws.refl {F : P.Factory} (hL : GuardFwdLaws F) {σ : SemanticStore P}
    {e : P.Expr} {v : P.Val} (h : P.eval F σ e = some v) : SameTy F v v :=
  (hL.typed h).imp fun _ h => ⟨h, h⟩

variable [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P]

/-- **The scope invariant** in the store `σ`: every name of the scope is defined in `σ`; every
    recorded right-hand side `d` of a name `y` evaluates to the value of `y`, and each of its free
    variables is in the scope or defined by no `init` of the list (`ini`). -/
@[expose] def ScopeInv (F : P.Factory) (ini : Std.HashSet P.Ident) (σ : SemanticStore P)
    (sc : Scope P) : Prop :=
  (∀ x, sc.contains x = true → (σ x).isSome) ∧
  ∀ y d, sc[y]? = some (some d) → (∃ v, σ y = some v ∧ P.eval F σ d = some v) ∧
    ∀ z ∈ HasFvars.getFvars d, sc.contains z = true ∨ ini.contains z = false

/-- The guard map `K` holds in the store `σ`: every known guard has its value. -/
@[expose] def GCons (F : P.Factory) (σ : SemanticStore P) (K : Guards P) : Prop :=
  ∀ g b, K[g]? = some b → σ g = some (if b then HasBool.ttVal F else HasBool.ffVal F)

variable {F : P.Factory} {ini : Std.HashSet P.Ident} {σ : SemanticStore P} {sc : Scope P}

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [LawfulBEq P.Ident] [LawfulHasVal P]
  [HasSubstFvar P] [WPLang P] [GuardOps P] in
/-- A guard map with the lookups of one that holds holds. -/
theorem GCons.congr {K K' : Guards P} (hK : ∀ x : P.Ident, K'[x]? = K[x]?) (h : GCons F σ K) :
    GCons F σ K' := fun g b hg => h g b ((hK g).symm.trans hg)

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [LawfulHasVal P] [HasSubstFvar P]
  [WPLang P] [GuardOps P] in
/-- A guard map that holds, extended by a guard with its value, holds. -/
theorem GCons.insert {K : Guards P} {g : P.Ident} {b : Bool} (h : GCons F σ K)
    (hg : σ g = some (if b then HasBool.ttVal F else HasBool.ffVal F)) :
    GCons F σ (K.insert g b) := fun g' b' h' => by
  rw [Std.HashMap.getElem?_insert] at h'
  split at h'
  · simpa [eq_of_beq ‹_›, ← Option.some.inj h'] using hg
  · exact h g' b' h'

omit [DecidableEq P.Ident] [HasFvar P] [HasFvars P] [LawfulHasVal P] [HasSubstFvar P]
  [WPLang P] [GuardOps P] in
/-- The empty guard map holds. -/
theorem GCons.empty : GCons F σ (∅ : Guards P) := fun _ _ h => by simp at h

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasVal P] in
/-- A value of a conditional is of the type of its `then` arm's value. -/
theorem ite_sameTy (hL : GuardFwdLaws F) {wc wt wf v : P.Val}
    (hb : SameTy F wc (HasBool.ttVal F)) (htf : SameTy F wt wf) (ht : P.eval F σ t = some wt)
    (h1 : wc = HasBool.ttVal F → v = wt) (h2 : wc = HasBool.ffVal F → v = wf) :
    SameTy F v wt :=
  (hL.bool_cases hb).elim (fun h => (h1 h).symm ▸ hL.refl ht) fun h => (h2 h).symm ▸ htf.symm

omit [LawfulBEq P.Ident] in
/-- A candidate has a value of the type of the variable's value, and that value when the guard
    map holds. -/
theorem cand_sem (hL : GuardFwdLaws F) (hC : WellFormedStore σ F) (hI : ScopeInv F ini σ sc)
    {K : Guards P} {y : P.Ident} {r : P.Expr} (h : cand sc K y = some r) :
    ∃ v w, σ y = some v ∧ P.eval F σ r = some w ∧ SameTy F v w ∧ (GCons F σ K → w = v) := by
  unfold cand at h
  split at h <;> try cases h
  rename_i d hd
  obtain ⟨⟨v, hy, hdv⟩, -⟩ := hI.2 y d hd
  split at h
  · exact Option.some.inj h ▸ ⟨v, v, hy, hdv, hL.refl hdv, fun _ => rfl⟩
  split at h <;> try cases h
  rename_i c a b hcab
  split at h <;> try cases h
  rename_i g hg
  rw [WPLang.iteView?_eval hcab] at hdv
  obtain ⟨wc, wa, wb, hc, ha, hb', hbt, hab, h1, h2⟩ := hL.ite_parts hdv
  have hcg : σ g = some wc := (hL.var c g σ hC hg).symm.trans hc
  split at h <;> cases h
  · refine ⟨v, wa, hy, ha, ite_sameTy hL hbt hab ha h1 h2, fun hK => ?_⟩
    exact (h1 (by simpa using hcg.symm.trans (hK g true ‹_›))).symm
  · refine ⟨v, wb, hy, hb', (ite_sameTy hL hbt hab ha h1 h2).trans hab, fun hK => ?_⟩
    exact (h2 (by simpa using hcg.symm.trans (hK g false ‹_›))).symm

omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [HasSubstFvar P] [WPLang P] [LawfulHasVal P]
  [GuardOps P] in
/-- The empty scope satisfies the scope invariant. -/
theorem scopeInv_empty : ScopeInv F ini σ ({} : Scope P) :=
  ⟨fun _ h => by simp at h, fun _ _ h => by simp at h⟩

end -- public section

end GuardFwd
end Imperative

namespace Core

public section

namespace GuardFwd

open Core.DeadDefElim

/-- The output relation of the dead-definition phase is transitive. -/
theorem ddOut_trans : IsTransitive DDOut := fun _ _ _ ⟨f1, s1⟩ ⟨f2, s2⟩ =>
  ⟨f2.trans f1, s2.trans s1⟩

end GuardFwd

namespace DefInline

/-- An extension of a factory keeps every function of it. -/
theorem addFactory_get {F G fac : Lambda.Factory CoreLParams} {n : String}
    {fn : Lambda.LFunc CoreLParams} (h : F.addFactory G = .ok fac)
    (hn : F[n]? = some fn) : fac[n]? = some fn := by
  rw [Lambda.Factory.getElem?_addFactory h, hn, Option.some_or]

end DefInline

/-- **`Program.mapStructuredBodies f` rewrites each procedure body by `f`**: for a procedure `q`
    of `prog` with structured body `ss`, its output contains the procedure with body `f ss`. -/
theorem Program.mapStructuredBodies_mem {f : Statements → Statements}
    {changed : Statements → Statements → Bool} {prog : Program} {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    {opq : Bool} (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (f ss) opq } md ∈
      (prog.mapStructuredBodies f changed).2.decls := by
  simp only [Program.mapStructuredBodies, List.map_map, List.mem_map]
  exact ⟨_, hq, by simp [Decl.mapStructuredBody, hb]⟩

/-- **Every procedure of the output of `Program.mapStructuredBodies f` comes from a procedure of
    its input** with the same header and metadata; when it has a structured body `ss'`, the
    procedure of the input has a structured body `ss` with `ss' = f ss`. -/
theorem Program.mapStructuredBodies_proc {f : Statements → Statements}
    {changed : Statements → Statements → Bool} {prog : Program} {q' : Procedure}
    {md : Imperative.MetaData Expression}
    (hq : Decl.proc q' md ∈ (prog.mapStructuredBodies f changed).2.decls) :
    ∃ q, Decl.proc q md ∈ prog.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧ ss' = f ss := by
  simp only [Program.mapStructuredBodies, List.map_map, List.mem_map, Function.comp_apply] at hq
  obtain ⟨_ | _ | _ | _ | ⟨q, md₀⟩ | _ | _, hd, heq⟩ := hq
  all_goals simp only [Decl.mapStructuredBody, reduceCtorEq] at heq
  split at heq
  · rename_i ss o hb
    cases heq
    refine ⟨q, hd, rfl, fun ss' o' hb' => ?_⟩
    simp only [Imperative.Body.structured.injEq] at hb'
    obtain ⟨rfl, rfl⟩ := hb'
    exact ⟨ss, hb, rfl⟩
  all_goals
    cases heq
    exact ⟨_, hd, rfl, fun ss' o' hb' => by simp_all⟩

end -- public section

end Core

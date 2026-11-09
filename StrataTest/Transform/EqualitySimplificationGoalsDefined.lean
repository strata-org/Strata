/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.EqualitySimplificationCorrect

/-! ## A real body whose goals have values

The theorems of `Strata.Transform.EqualitySimplificationCorrect` take as premise that a
body's goals have values in the stores it reaches (`GoalsDefined`). This file proves that
premise for the body of the `literalPgm` fixture of
`StrataTest/Languages/Core/Examples/EqualitySimplification.lean`, as type checking leaves
it (checked there against the fixture), in every store that binds its parameters `n : int`
and `s : string`:

```
assume n == 3;
assume s == "ab";
assert [intFolds]: int.gt(int.add(n, 1), 3);
assert [stringFolds]: str.len(str.concat(s, "c")) == 3;
```

Key theorems: `literal_goalsDefined`. -/

namespace Core.EqualitySimplification.GoalsDefinedTest

open Lambda Imperative Imperative.BigStep Imperative.BigStep.GoalRewrite

public abbrev intTy : LMonoTy := .tcons "int" []
public abbrev strTy : LMonoTy := .tcons "string" []
public abbrev boolTy : LMonoTy := .tcons "bool" []
public abbrev arr (a b : LMonoTy) : LMonoTy := .tcons "arrow" [a, b]

public abbrev n : Expression.Expr := .fvar () ⟨"n", ()⟩ (some intTy)
public abbrev s : Expression.Expr := .fvar () ⟨"s", ()⟩ (some strTy)

/-- `int.gt(int.add(n, 1), 3)`, as type checking annotates it. -/
public abbrev intGoal : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Gt", ()⟩ (some (arr intTy (arr intTy boolTy))))
    (.app () (.app () (.op () ⟨"Int.Add", ()⟩ (some (arr intTy (arr intTy intTy)))) n)
      (.intConst () 1)))
    (.intConst () 3)

/-- `str.len(str.concat(s, "c")) == 3`, as type checking annotates it. -/
public abbrev strGoal : Expression.Expr :=
  .eq () (.app () (.op () ⟨"Str.Length", ()⟩ (some (arr strTy intTy)))
      (.app () (.app () (.op () ⟨"Str.Concat", ()⟩ (some (arr strTy (arr strTy strTy)))) s)
        (.strConst () "c")))
    (.intConst () 3)

/-- The body of `literalPgm`, for any labels and metadata. -/
public abbrev body (l₁ l₂ l₃ l₄ : String) (m₁ m₂ m₃ m₄ : MetaData Expression) : Statements :=
  [.cmd (.cmd (.assume l₁ (.eq () n (.intConst () 3)) m₁)),
   .cmd (.cmd (.assume l₂ (.eq () s (.strConst () "ab")) m₂)),
   .cmd (.cmd (.assert l₃ intGoal m₃)),
   .cmd (.cmd (.assert l₄ strGoal m₄))]

variable {Fs : Expression.Factory} {σ : SemanticStore Expression}

/-- A goal whose annotation in `σ` has type `bool` and whose variables `σ` binds has a
    value. -/
private theorem has_value {e : Expression.Expr}
    (hd : ValStore.Defines (T := CoreLParams) σ Fs.model.tcInterp e)
    (ht : (e.annotateFvars (ValStore.ann (T := CoreLParams) σ)).HasTypeA [] .bool) :
    ∃ v, Expression.eval Fs σ e = some v :=
  ⟨_, (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mpr ⟨hd, .bool, ht, rfl, rfl⟩⟩

/-- **The goals of `literalPgm` have values** in every reach from a store that binds `n` to
    an integer and `s` to a string of the runtime factory's model. -/
theorem literal_goalsDefined {l₁ l₂ l₃ l₄ : String} {m₁ m₂ m₃ m₄ : MetaData Expression}
    {vn vs : SemValue} (hn : σ ⟨"n", ()⟩ = some vn) (hvn : vn.tc = Fs.model.tcInterp)
    (hsn : vn.sort = .int) (hs : σ ⟨"s", ()⟩ = some vs) (hvs : vs.tc = Fs.model.tcInterp)
    (hss : vs.sort = .tcons "string" []) :
    GoalsDefined Fs (body l₁ l₂ l₃ l₄ m₁ m₂ m₃ m₄) σ := by
  have hann_n : ValStore.ann (T := CoreLParams) σ ⟨"n", ()⟩ = some intTy := by
    simp [ValStore.ann, hn, hsn, LSort.toMonoTy, LSort.toMonoTy.map]
  have hann_s : ValStore.ann (T := CoreLParams) σ ⟨"s", ()⟩ = some strTy := by
    simp [ValStore.ann, hs, hss, LSort.toMonoTy, LSort.toMonoTy.map]
  have hint : ∃ v, Expression.eval Fs σ intGoal = some v := by
    refine has_value (fun x hx => ?_) ?_
    · simp only [LExpr.LExpr.getVars, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; exact ⟨_, hn, hvn⟩
    · simp only [LExpr.annotateFvars, hann_n]
      exact .app (.app .op (.app (.app .op .fvar) .const)) .const
  have hstr : ∃ v, Expression.eval Fs σ strGoal = some v := by
    refine has_value (fun x hx => ?_) ?_
    · simp only [LExpr.LExpr.getVars, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; exact ⟨_, hs, hvs⟩
    · simp only [LExpr.annotateFvars, hann_s]
      exact .eq (.app .op (.app (.app .op .fvar) .const)) .const
  -- Each statement is a command, and the commands keep the store, so every event of a
  -- reach is an assumption or an assertion of one of the two goals, in `σ`.
  have hev : ∀ L, BReach Fs (body l₁ l₂ l₃ l₄ m₁ m₂ m₃ m₄) σ L → ∀ x ∈ L,
      (∃ a, x = .assume a) ∨ x.condition.factory = Fs ∧ x.condition.store = σ ∧
        (x.condition.expr = intGoal ∨ x.condition.expr = strGoal) := by
    intro L hL x hx
    cases hL with
    | here h =>
      cases h with | cmd h =>
      cases h; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; exact .inl ⟨_, hx⟩
    | later h1 h2 =>
      cases h1 with | cmd h1 =>
      cases h1
      cases h2 with
      | here h =>
        cases h with | cmd h =>
        cases h; simp only [List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx <;> exact .inl ⟨_, hx⟩
      | later h1 h2 =>
        cases h1 with | cmd h1 =>
        cases h1
        cases h2 with
        | here h =>
          cases h with | cmd h =>
          cases h; simp only [List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with hx | hx | hx
          · exact .inl ⟨_, hx⟩
          · exact .inl ⟨_, hx⟩
          · subst hx; exact .inr ⟨rfl, rfl, .inl rfl⟩
        | later h1 h2 =>
          cases h1 with | cmd h1 =>
          cases h1
          cases h2 with
          | here h =>
            cases h with | cmd h =>
            cases h; simp only [List.cons_append, List.nil_append,
              List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with hx | hx | hx | hx
            · exact .inl ⟨_, hx⟩
            · exact .inl ⟨_, hx⟩
            · subst hx; exact .inr ⟨rfl, rfl, .inl rfl⟩
            · subst hx; exact .inr ⟨rfl, rfl, .inr rfl⟩
          | later h1 h2 =>
            cases h2
  intro evs ev hr hna
  rcases hev _ hr ev (by simp) with ⟨a, rfl⟩ | ⟨hf, hst, hg | hg⟩
  · exact absurd rfl (hna a)
  · rw [hf, hst, hg]; exact hint
  · rw [hf, hst, hg]; exact hstr

/-! ## Checking operator consistency

`opsConsistentB` decides a sufficient condition for `Lambda.OpsConsistentR`: every operator
the factory knows is annotated at the instance of its signature that `LFunc.opTypeSubst`
computes. The fixture tests use it to check the operator premises of the equality
simplification theorems on real programs. -/

/-- Every operator of `e` that `F` knows is annotated at the instance of its signature that
    `LFunc.opTypeSubst` computes. -/
public def opsConsistentB (F : Lambda.Factory CoreLParams) : Expression.Expr → Bool
  | e@(.op _ name ty) =>
    match F[name.name]?, ty with
    | none, _ => true
    | some fn, some t =>
      match LFunc.opTypeSubst fn e with
      | some S => decide (t = (LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst S)
      | none => false
    | some _, none => false
  | .app _ f a => opsConsistentB F f && opsConsistentB F a
  | .abs _ _ _ b => opsConsistentB F b
  | .ite _ c t f => opsConsistentB F c && opsConsistentB F t && opsConsistentB F f
  | .eq _ a b => opsConsistentB F a && opsConsistentB F b
  | .quant _ _ _ _ tr b => opsConsistentB F tr && opsConsistentB F b
  | .const .. | .bvar .. | .fvar .. => true

/-- `opsConsistentB` is sound for `Lambda.OpsConsistentR`. -/
public theorem opsConsistentR_of_opsConsistentB {F : Lambda.Factory CoreLParams} :
    ∀ {e : Expression.Expr}, opsConsistentB F e = true → Lambda.OpsConsistentR F e
  | .const .., _ => .const
  | .bvar .., _ => .bvar
  | .fvar .., _ => .fvar
  | .op m name ty, h => by
    unfold opsConsistentB at h
    rcases hfn : F[name.name]? with _ | fn
    · exact .op_notin hfn
    · rw [hfn] at h
      rcases ty with _ | t
      · cases h
      · simp only at h
        rcases hS : LFunc.opTypeSubst fn (.op m name (some t)) with _ | S
        · rw [hS] at h; cases h
        · rw [hS] at h
          exact .op_in hfn (of_decide_eq_true h)
  | .app .., h => by
    simp only [opsConsistentB, Bool.and_eq_true] at h
    exact .app (opsConsistentR_of_opsConsistentB h.1) (opsConsistentR_of_opsConsistentB h.2)
  | .abs .., h => by
    simp only [opsConsistentB] at h
    exact .abs (opsConsistentR_of_opsConsistentB h)
  | .ite .., h => by
    simp only [opsConsistentB, Bool.and_eq_true] at h
    exact .ite (opsConsistentR_of_opsConsistentB h.1.1) (opsConsistentR_of_opsConsistentB h.1.2)
      (opsConsistentR_of_opsConsistentB h.2)
  | .eq .., h => by
    simp only [opsConsistentB, Bool.and_eq_true] at h
    exact .eq (opsConsistentR_of_opsConsistentB h.1) (opsConsistentR_of_opsConsistentB h.2)
  | .quant .., h => by
    simp only [opsConsistentB, Bool.and_eq_true] at h
    exact .quant (opsConsistentR_of_opsConsistentB h.1) (opsConsistentR_of_opsConsistentB h.2)

/-! ## Near misses of the operator premise

These satisfy the operator premise and fold to something with a value, yet have no value
themselves, so the one-way folding conditions say nothing about them: `Int.Add` at its own
signature applied to a Boolean, and a beta redex whose argument has the wrong type. -/

/-- `Int.Add` at its signature `int → int → int`, applied to `true` and `2`. -/
public abbrev wrongArg : Expression.Expr :=
  .app () (.app () (.op () ⟨"Int.Add", ()⟩ (some (arr intTy (arr intTy intTy))))
    (.boolConst () true)) (.intConst () 2)

/-- `(fun (y : bool) => y) 3`. -/
public abbrev wrongBeta : Expression.Expr :=
  .app () (.abs () "y" (some boolTy) (.bvar () 0)) (.intConst () 3)

/-- `wrongArg` has no value in any runtime factory and store: `true` is no integer. -/
public theorem wrongArg_no_value (Fs : Expression.Factory) (σ : SemanticStore Expression) :
    Expression.eval Fs σ wrongArg = none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro v h
  obtain ⟨-, τ, hτ, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp h
  simp only [LExpr.annotateFvars] at hτ
  cases hτ with
  | app hfn _ =>
    cases hfn with
    | app hop harg =>
      cases hop
      have := (LExpr.HasTypeA_iff_typeCheck _ _ _).mp harg
      simp [LExpr.typeCheck, LConst.ty, intTy, LMonoTy.bool] at this

/-- `wrongBeta` has no value in any runtime factory and store: `3` is no Boolean. -/
public theorem wrongBeta_no_value (Fs : Expression.Factory) (σ : SemanticStore Expression) :
    Expression.eval Fs σ wrongBeta = none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro v h
  obtain ⟨-, τ, hτ, -⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp h
  simp only [LExpr.annotateFvars] at hτ
  cases hτ with
  | app hfn harg =>
    cases hfn
    have := (LExpr.HasTypeA_iff_typeCheck _ _ _).mp harg
    simp [LExpr.typeCheck, LConst.ty, boolTy, LMonoTy.int] at this

end Core.EqualitySimplification.GoalsDefinedTest

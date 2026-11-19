/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Expr
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.Transform.Simplify.Expr
import all Strata.DL.Lambda.FactoryProps
public import Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.Assumptions

/-! # The factory Simplify folds with

Simplify folds against `withoutInline carriers F`: the factory `F` with some functions'
`inline` attribute replaced by `inlineIfAllValues` (`stripInline`). Only the attributes
change, and nothing in the denotational semantics reads an attribute, so the two factories
have the same functions for every purpose but folding.

Key results: the two factories look up the same functions up to attributes
(`withoutInline_getElem?`, `withoutInline_callOfLFunc`), an expression's operators are
consistent with one exactly when with the other (`opsConsistent_withoutInline`), and a model
of `F` is a model of the fold factory (`Interp.withoutInline`). -/

namespace Core.Simplify

open Lambda

public section

/-- `stripInline` changes only the attributes. -/
theorem stripInline_eq (c : List String) (fn : LFunc CoreLParams) :
    ∃ attr, stripInline c fn = { fn with attr := attr } := by
  unfold stripInline stripInlineFunc
  split
  · exact ⟨fn.attr, rfl⟩
  · exact ⟨_, rfl⟩

/-- Weakening `inline` keeps a function's name. -/
@[simp] theorem stripInline_name (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).name = fn.name := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's inputs. -/
@[simp] theorem stripInline_inputs (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).inputs = fn.inputs := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's output type. -/
@[simp] theorem stripInline_output (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).output = fn.output := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's body. -/
@[simp] theorem stripInline_body (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).body = fn.body := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's concrete evaluator. -/
@[simp] theorem stripInline_concreteEval (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).concreteEval = fn.concreteEval := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps whether a function is a constructor. -/
@[simp] theorem stripInline_isConstr (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).isConstr = fn.isConstr := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's axioms. -/
@[simp] theorem stripInline_axioms (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).axioms = fn.axioms := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- Weakening `inline` keeps a function's type arguments. -/
@[simp] theorem stripInline_typeArgs (c : List String) (fn : LFunc CoreLParams) :
    (stripInline c fn).typeArgs = fn.typeArgs := by
  obtain ⟨_, h⟩ := stripInline_eq c fn; rw [h]

/-- **A lookup in the fold factory** is the lookup in `F`, stripped. -/
theorem withoutInline_getElem? (c : List String) (F : Lambda.Factory CoreLParams) (f : String) :
    (withoutInline c F)[f]? = (F[f]?).map (stripInline c) := by
  have hnodup : ((F.toArray.map (stripInline c)).toList.map (·.name.name)).Nodup := by
    rw [Array.toList_map, List.map_map]
    have : (fun x => x.name.name) ∘ stripInline c = (·.name.name) := by
      funext fn; simp
    rw [this]
    exact Factory.name_nodup F
  cases hF : F[f]? with
  | some fn =>
    have hname : fn.name.name = f := Factory.getElem?_name hF
    have hmem : fn ∈ F.toArray := by
      obtain ⟨g, hg, hgn⟩ := Array.mem_map.mp
        ((Factory.mem_iff_mem_names F f).mp (Factory.getElem?_some_implies_mem hF))
      have h1 := Factory.getElem?_of_mem_toArray F g hg
      rw [hgn, hF] at h1
      cases h1; exact hg
    have hget := Factory.get?_ofArray_of_mem (Array.mem_map_of_mem (f := stripInline c) hmem) hnodup
    simp only [stripInline_name, hname] at hget
    simpa [withoutInline] using hget
  | none =>
    cases hW : (withoutInline c F)[f]? with
    | none => rfl
    | some g =>
      exfalso
      have hm := Factory.getElem?_some_implies_mem hW
      obtain ⟨g', hg', hgn⟩ := Array.mem_map.mp ((Factory.mem_iff_mem_names _ f).mp hm)
      have hg'' := Factory.ofArray_mem hg'
      obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.mp hg''
      have hget := Factory.getElem?_of_mem_toArray F fn hfn
      simp only [stripInline_name] at hgn
      rw [hgn, hF] at hget
      cases hget

/-- A function of the fold factory is a function of `F`, stripped. -/
theorem withoutInline_mem_toArray {c : List String} {F : Lambda.Factory CoreLParams}
    {g : LFunc CoreLParams} (h : g ∈ (withoutInline c F).toArray) :
    ∃ fn ∈ F.toArray, g = stripInline c fn := by
  obtain ⟨fn, hfn, rfl⟩ := Array.mem_map.mp (Factory.ofArray_mem h)
  exact ⟨fn, hfn, rfl⟩

/-- A function of `F`, stripped, is a function of the fold factory. -/
theorem stripInline_mem_withoutInline {c : List String} {F : Lambda.Factory CoreLParams}
    {fn : LFunc CoreLParams} (h : fn ∈ F.toArray) :
    stripInline c fn ∈ (withoutInline c F).toArray := by
  have hget : (withoutInline c F)[fn.name.name]? = some (stripInline c fn) := by
    rw [withoutInline_getElem?, Factory.getElem?_of_mem_toArray F fn h]; rfl
  exact Factory.getElem?_is_some_implies_mem hget

/-- The fold factory has the names of `F`. -/
theorem withoutInline_mem (c : List String) (F : Lambda.Factory CoreLParams) (f : String) :
    f ∈ withoutInline c F ↔ f ∈ F := by
  rw [Factory.mem_iff_getElem?_isSome, Factory.mem_iff_getElem?_isSome,
    withoutInline_getElem?, Option.isSome_map]

/-- The fold factory's function under a name is `F`'s, stripped. -/
theorem withoutInline_getElem (c : List String) (F : Lambda.Factory CoreLParams) (f : String)
    (h : f ∈ withoutInline c F) :
    (withoutInline c F)[f] = stripInline c (F[f]'((withoutInline_mem c F f).mp h)) := by
  obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp
    ((Factory.mem_iff_getElem?_isSome F f).mp ((withoutInline_mem c F f).mp h))
  have hW : (withoutInline c F)[f]? = some (stripInline c fn) := by
    rw [withoutInline_getElem?, hfn]; rfl
  rw [Factory.getElem?_some_getElem hW, Factory.getElem?_some_getElem hfn]

/-- A call resolves in the fold factory to the function it resolves to in `F`, stripped. -/
theorem withoutInline_callOfLFunc (c : List String) (F : Lambda.Factory CoreLParams)
    (e : Expression.Expr) (aPA : Bool) :
    (withoutInline c F).callOfLFunc e aPA =
      (F.callOfLFunc e aPA).map (fun t => (t.1, t.2.1, stripInline c t.2.2)) := by
  unfold Factory.callOfLFunc
  obtain ⟨op, args⟩ := getLFuncCall e
  cases op with
  | op m name ty =>
    simp only [withoutInline_getElem?]
    cases F[name.name]? with
    | none => rfl
    | some fn =>
      simp only [Option.map_some, stripInline_inputs]
      split <;> rfl
  | _ => rfl

/-- Operator annotations are consistent with the fold factory exactly when they are with the
    original: `stripInline` keeps every function's type. -/
theorem opsConsistent_withoutInline (c : List String) (F : Lambda.Factory CoreLParams) :
    ∀ e : Expression.Expr, OpsConsistent (withoutInline c F) e ↔ OpsConsistent F e := by
  intro e
  induction e with
  | op m o ty =>
    simp only [OpsConsistent]
    rw [withoutInline_getElem?]
    cases F[o.name]? with
    | none => rfl
    | some fn =>
      obtain ⟨a, h⟩ := stripInline_eq c fn
      simp only [Option.map_some, h]
      rfl
  | app _ _ _ ih₁ ih₂ => simp only [OpsConsistent, ih₁, ih₂]
  | abs _ _ _ _ ih => simp only [OpsConsistent, ih]
  | ite _ _ _ _ ih₁ ih₂ ih₃ => simp only [OpsConsistent, ih₁, ih₂, ih₃]
  | eq _ _ _ ih₁ ih₂ => simp only [OpsConsistent, ih₁, ih₂]
  | quant _ _ _ _ _ _ ih₁ ih₂ => simp only [OpsConsistent, ih₁, ih₂]
  | const | bvar | fvar => simp only [OpsConsistent]

section Interp

variable {c : List String} {F : Lambda.Factory CoreLParams}
  {tc : TyConstrInterp} {op : OpInterp tc}

/-- Every function body and concrete evaluator of the fold factory is consistent with an
    interpretation `F`'s are consistent with. -/
private theorem interpConsistent_withoutInline (h : Factory.InterpConsistent tc op F) :
    Factory.InterpConsistent tc op (withoutInline c F) := by
  unfold Factory.InterpConsistent at h ⊢
  refine ⟨fun f hf body hb => ?_, fun f hf ceval hc => ?_⟩
  · rw [withoutInline_getElem c F f hf] at hb ⊢
    rw [stripInline_body] at hb
    obtain ⟨a, he⟩ := stripInline_eq c (F[f]'((withoutInline_mem c F f).mp hf))
    rw [he]
    exact h.1 f _ body hb
  · rw [withoutInline_getElem c F f hf] at hc ⊢
    rw [stripInline_concreteEval] at hc
    obtain ⟨a, he⟩ := stripInline_eq c (F[f]'((withoutInline_mem c F f).mp hf))
    rw [he]
    exact h.2 f _ ceval hc

/-- The fold factory's constructors are interpreted as `F`'s. -/
private theorem constrInterpConsistent_withoutInline (h : ConstrInterpConsistent tc op F) :
    ConstrInterpConsistent tc op (withoutInline c F) where
  constr_disjoint := by
    intro f1 f2 h1 h2 hc1 hc2 hne
    obtain ⟨g1, hg1, rfl⟩ := withoutInline_mem_toArray h1
    obtain ⟨g2, hg2, rfl⟩ := withoutInline_mem_toArray h2
    obtain ⟨a1, he1⟩ := stripInline_eq c g1
    obtain ⟨a2, he2⟩ := stripInline_eq c g2
    rw [he1] at hc1 hne ⊢
    rw [he2] at hc2 hne ⊢
    exact h.constr_disjoint g1 g2 hg1 hg2 hc1 hc2 hne
  constr_injective := by
    intro f hf hc
    obtain ⟨g, hg, rfl⟩ := withoutInline_mem_toArray hf
    obtain ⟨a, he⟩ := stripInline_eq c g
    rw [he] at hc ⊢
    exact h.constr_injective g hg hc
  constr_induction := by
    intro P hstep s v hs
    have hsort : ∀ {s}, (withoutInline c F).IsDatatypeSort s → F.IsDatatypeSort s := by
      intro s ⟨g, hg, hgc, vt, hgs⟩
      obtain ⟨fn, hfn, rfl⟩ := withoutInline_mem_toArray hg
      exact ⟨fn, hfn, by simpa using hgc, vt, by simpa using hgs⟩
    refine h.constr_induction P ?_ s v (hsort hs)
    intro f hf hfc vt args hall
    obtain ⟨a, he⟩ := stripInline_eq c f
    have hmem := stripInline_mem_withoutInline (c := c) hf
    rw [he] at hmem
    exact hstep { f with attr := a } hmem hfc vt args
      (HList.All.imp (fun _ _ hx hs' => hx (hsort hs')) hall)

/-- The fold factory's axioms are `F`'s. -/
private theorem axiomsSatisfied_withoutInline (h : Factory.AxiomsSatisfied tc op F) :
    Factory.AxiomsSatisfied tc op (withoutInline c F) := by
  unfold Factory.AxiomsSatisfied at h ⊢
  intro f hf ax hax
  rw [withoutInline_getElem c F f hf, stripInline_axioms] at hax
  exact h f _ ax hax

/-- **A model of `F` is a model of the fold factory**: nothing an interpretation is asked to
    satisfy reads a function's attributes. -/
def Interp.withoutInline (c : List String) (M : Interp F) : Interp (withoutInline c F) where
  tcInterp := M.tcInterp
  opInterp := M.opInterp
  allInhabited := M.allInhabited
  interpConsistent := interpConsistent_withoutInline M.interpConsistent
  axiomsSatisfied := axiomsSatisfied_withoutInline M.axiomsSatisfied
  constrConsistent := constrInterpConsistent_withoutInline M.constrConsistent

end Interp

end

end Core.Simplify

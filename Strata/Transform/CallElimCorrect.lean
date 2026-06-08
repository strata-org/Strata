/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Init.Data.List.Basic
import Init.Data.List.Lemmas
public import Strata.Languages.Core.Env
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.WF
public import Strata.DL.Lambda
public import Strata.Transform.CoreTransform
public import Strata.Transform.CallElim
public import Strata.DL.Imperative.CmdSemantics
public import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.StatementSemanticsProps
public import Strata.Transform.SubstProps
import Strata.Transform.CoreTransformProps
import Strata.DL.Util.ListUtils
public import Strata.DL.Util.String

/-! # Call Elimination Correctness Proof

  This file contains the main proof that the call elimination transformation is
  semantics preserving (see `callElimStatementCorrect`), formulated against the
  small-step `Stmt` semantics in `Strata.Languages.Core.StatementSemanticsProps`.
-/

namespace CallElimCorrect
open Core Core.Transform CallElim

public section

variable {π : String → Option Procedure}
variable {φ : CoreEval → Imperative.PureFunc Expression → CoreEval}
variable {δ : CoreEval}

-- inidividual lemmas

private theorem createFvarsApp :
createFvars (a ++ b) = createFvars a ++ createFvars b := by
simp [createFvars]

private theorem createFvarsLength :
(createFvars ls).length = ls.length := by
induction ls <;> simp [createFvars]

/-- Contradiction: `σ k` cannot simultaneously be `isSome` and `none`. -/
private theorem σ_some_contradiction {α β} {σ : β → Option α} {k : β}
    (Hsome : (σ k).isSome) (Hnone : σ k = none) : False := by
  rw [Hnone] at Hsome; simp at Hsome

/-- A defined key cannot lie in an `isNotDefined` list. -/
private theorem notin_of_isSome_isNotDefined {P : Imperative.PureExpr}
    {σ : Imperative.SemanticStore P} {k : P.Ident} {ks : List P.Ident}
    (Hsome : (σ k).isSome) (Hndef : Imperative.isNotDefined σ ks) : k ∉ ks :=
  fun h => σ_some_contradiction Hsome (Hndef k h)


/-- `Map.find?_append` "some" branch packaged: if a key resolves to `some v`
    in `l₁` and to `some w` in `l₁ ++ l₂`, then `v = w`. -/
private theorem find?_append_some_eq {α β} [DecidableEq α]
    {l₁ l₂ : List (α × β)} {k : α} {v w : β}
    (hfind : Map.find? l₁ k = some v)
    (Hf : Map.find? (l₁ ++ l₂) k = some w) : v = w := by
  have HH := Map.find?_append l₁ l₂ k
  rw [hfind] at HH
  exact Option.some_inj.mp (HH.symm.trans Hf)

/-- `Map.find?_append` "none" branch packaged: if a key misses in `l₁` but
    `Map.find? (l₁ ++ l₂) k = some w`, then `Map.find? l₂ k = some w`. -/
private theorem find?_append_none_elim {α β} [DecidableEq α]
    {l₁ l₂ : List (α × β)} {k : α} {w : β}
    (hfind : Map.find? l₁ k = none)
    (Hf : Map.find? (l₁ ++ l₂) k = some w) : Map.find? l₂ k = some w := by
  have HH := Map.find?_append l₁ l₂ k
  rw [hfind] at HH
  exact HH.symm.trans Hf

/-- Shared `oldVars` filter used at multiple sites in `callElimCmd_call_eq`
    and `callElimStatementCorrect`: those `CallArg.getLhs args` parameters
    that (i) appear in both `proc.header.inputs` and `proc.header.outputs`,
    and (ii) are referenced as `old _` in `proc.spec.postconditions`.
    Marked `@[reducible]` so generalize/simp can match the inline form. -/
@[reducible] private def callElim_oldVars (proc : Procedure)
    (args : List (CallArg Expression)) : List Expression.Ident :=
  List.filter
    (fun g =>
      (ListMap.keys proc.header.inputs).contains g &&
          (ListMap.keys proc.header.outputs).contains g &&
        (List.map Procedure.Check.expr proc.spec.postconditions.values).any fun e =>
          List.any e.freeVars fun x => x.fst == CoreIdent.mkOld g.name)
    (CallArg.getLhs args)

/-- Shared `inputOnlyOldSubst` map: input-only parameters referenced as `old _`
    in postconditions, mapped to the corresponding caller-side argument. -/
@[reducible] private def callElim_inputOnlyOldSubst (proc : Procedure)
    (args : List (CallArg Expression)) :
    Map Expression.Ident Expression.Expr :=
  (proc.header.inputs.keys.zip (CallArg.getInputExprs args)).filterMap fun (paramId, argExpr) =>
    let oldVar := CoreIdent.mkOld paramId.name
    if !(ListMap.keys proc.header.outputs).contains paramId &&
       (proc.spec.postconditions.values.map Procedure.Check.expr).any
         (fun e => Lambda.LExpr.freeVars e |>.any (fun (id, _) => id == oldVar))
    then some (oldVar, argExpr)
    else none

/-! ### Top-level call-elimination correctness theorem -/

/-- Returns the call-elim transformation result of a single command:
    either the rewritten statement list (for a `.call`) or `[s]`
    unchanged (for a non-call statement). -/
@[expose]
def callElimStmt (s : Statement) (p : Program)
    : CoreTransformM (List Statement) := do
  modify (fun σ => { σ with currentProgram := .some p })
  match s with
  | .cmd (CmdExt.call procName args md) => do
      match (← CallElim.callElimCmd (CmdExt.call procName args md)) with
      | .none    => return [s]
      | .some s' => return s'
  | _ => return [s]

/-- An inline analogue of the inner-`go` walk inside
    `Procedure.Spec.updateCheckExprs`: given a substituted-expression
    list and an original-checks list, produce the per-entry checks with
    the new expression.  This mirrors the `where go` clause of
    `Procedure.Spec.updateCheckExprs` so we can reason about its result
    without referring to the where-private constant. -/
private def updateCheckExprs_walk
    (es : List Expression.Expr) (checks : List Procedure.Check) :
    List Procedure.Check :=
  match es, checks with
  | [], _ => checks
  | _, [] => checks
  | e :: erest, c :: crest =>
    { c with expr := e } :: updateCheckExprs_walk erest crest

/-- The walk preserves length when `es = checks.map f`. -/
private theorem updateCheckExprs_walk_length_map
    (vs : List Procedure.Check)
    (f : Procedure.Check → Expression.Expr) :
    (updateCheckExprs_walk (vs.map f) vs).length = vs.length := by
  induction vs with
  | nil => simp [updateCheckExprs_walk]
  | cons hd tl ih =>
    simp only [List.map_cons, updateCheckExprs_walk,
               List.length_cons]
    exact congrArg (· + 1) ih

/-- Positional access into `updateCheckExprs_walk (vs.map (substFvars ·.expr sm)) vs`. -/
private theorem updateCheckExprs_walk_getElem_substFvars
    {sm : Map Expression.Ident Expression.Expr}
    (vs : List Procedure.Check)
    (i : Nat)
    (Hi : i < vs.length)
    (Hi' : i < (updateCheckExprs_walk
                  (vs.map (fun c =>
                    Lambda.LExpr.substFvars c.expr sm))
                  vs).length) :
    ((updateCheckExprs_walk
        (vs.map (fun c => Lambda.LExpr.substFvars c.expr sm))
        vs)[i]'Hi').expr =
    Lambda.LExpr.substFvars (vs[i]'Hi).expr sm := by
  induction vs generalizing i with
  | nil =>
    exact absurd Hi (by simp)
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.map_cons, updateCheckExprs_walk,
                 List.getElem_cons_zero]
    | succ k =>
      have Hk : k < tl.length := by
        simp only [List.length_cons] at Hi; omega
      have Hk' : k < (updateCheckExprs_walk
                      (tl.map (fun c =>
                        Lambda.LExpr.substFvars c.expr sm))
                      tl).length := by
        simp only [List.map_cons, updateCheckExprs_walk,
                   List.length_cons] at Hi'
        omega
      have HiH := ih k Hk Hk'
      simp only [List.map_cons, updateCheckExprs_walk,
                 List.getElem_cons_succ]
      exact HiH

/-- The local `updateCheckExprs_walk` mirror agrees pointwise with the
    where-private `Procedure.Spec.updateCheckExprs.go`.  Both walk the two
    lists in parallel and return the original `checks` list when either
    argument is exhausted; the equality holds for all input shapes. -/
private theorem updateCheckExprs_walk_eq_go :
    ∀ (es : List Expression.Expr) (cs : List Procedure.Check),
    updateCheckExprs_walk es cs =
    Procedure.Spec.updateCheckExprs.go es cs := by
  intro es cs
  induction es generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
    | cons hd tl =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
  | cons e es' ih =>
    cases cs with
    | nil =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go]
    | cons hd tl =>
      simp [updateCheckExprs_walk,
            Procedure.Spec.updateCheckExprs.go,
            ih]

/-- For each entry in `updateCheckExprs (conds.values.map (substFvars · sm))
    conds`, the entry's expression is exactly `substFvars c.expr sm` for some
    `c ∈ conds.values`.  This is the per-entry correspondence used by D2f
    to lift `δ σO original_post = tt` (Hpost) to the substituted
    postcondition form.

    Note: the proof relies on the `where`-clause `Procedure.Spec.updateCheckExprs.go`
    walking the lists in parallel; we mirror this via `updateCheckExprs_walk`
    and use definitional unfolding via `show`. -/
private theorem updateCheckExprs_substFvars_mem
    {sm : Map Expression.Ident Expression.Expr}
    {conds : ListMap CoreLabel Procedure.Check}
    {entry : CoreLabel × Procedure.Check}
    (Hentry : entry ∈
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values))) :
    ∃ c ∈ conds.values,
      entry.snd.expr = Lambda.LExpr.substFvars c.expr sm := by
  rcases List.mem_iff_get.mp Hentry with ⟨n, Hn⟩
  have Hn_lt_zip := n.isLt
  have Hzip_len :
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values)).length =
      Nat.min conds.keys.length
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values).length := List.length_zip
  have Hwalk_len :
      (updateCheckExprs_walk
        (conds.values.map (fun c =>
          Lambda.LExpr.substFvars c.expr sm))
        conds.values).length = conds.values.length :=
    updateCheckExprs_walk_length_map _ _
  have Hn_lt_zip' : n.val <
      Nat.min conds.keys.length
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values).length := Hzip_len ▸ Hn_lt_zip
  have Hn_lt_keys : n.val < conds.keys.length :=
    Nat.lt_of_lt_of_le Hn_lt_zip' (Nat.min_le_left _ _)
  have Hn_lt_walk :
      n.val < (updateCheckExprs_walk
                (conds.values.map (fun c =>
                  Lambda.LExpr.substFvars c.expr sm))
                conds.values).length :=
    Nat.lt_of_lt_of_le Hn_lt_zip' (Nat.min_le_right _ _)
  have Hn_lt_vs : n.val < conds.values.length := Hwalk_len ▸ Hn_lt_walk
  have HzipGet :
      (conds.keys.zip
        (updateCheckExprs_walk
          (conds.values.map
            (fun c => Lambda.LExpr.substFvars c.expr sm))
          conds.values))[n.val]'Hn_lt_zip =
        (conds.keys[n.val]'Hn_lt_keys,
         (updateCheckExprs_walk
            (conds.values.map
              (fun c => Lambda.LExpr.substFvars c.expr sm))
            conds.values)[n.val]'Hn_lt_walk) :=
    List.getElem_zip
  have HhE_get : (conds.keys.zip _)[n.val]'Hn_lt_zip = entry := Hn
  rw [HzipGet] at HhE_get
  have Hsnd_eq :
      entry.snd =
        (updateCheckExprs_walk
          (conds.values.map (fun c =>
            Lambda.LExpr.substFvars c.expr sm))
          conds.values)[n.val]'Hn_lt_walk :=
    ((Prod.mk.injEq _ _ _ _).mp HhE_get).2.symm
  refine ⟨conds.values[n.val]'Hn_lt_vs, List.getElem_mem _, ?_⟩
  rw [Hsnd_eq]
  exact updateCheckExprs_walk_getElem_substFvars
    conds.values n.val Hn_lt_vs Hn_lt_walk

/-! ## Call-case helper lemmas

These helpers bridge the WF infrastructure to the disjointness/Nodup
obligations the L1–L6 wrappers need.  Most consume a
`Forall isTempIdent`/`Forall isOldTempIdent` hypothesis rather than
producing one from `genIdent` semantics directly, since the producing
side requires reasoning through opaque `String.startsWith` /
`Slice`/`Pattern` infrastructure. -/

/-- Negation form of `List.Forall_mem_iff.mp`: if every element of `l`
    satisfies `p` and `x` does *not* satisfy `p`, then `x ∉ l`.  Used
    repeatedly for `notTemp ⇒ k1 ∉ argTemps/outTemps/genOldIdents`. -/
private theorem notMem_of_Forall_neg
    {α : Type _} {l : List α} {p : α → Prop} {x : α}
    (Hforall : Forall p l) (Hnotp : ¬ p x) : x ∉ l := fun h =>
  Hnotp ((List.Forall_mem_iff.mp Hforall) x h)

/-- Decompose the recurring `(k1, k2) ∈ zip self self` membership with
    `self = (getVars expr).removeAll ((l₁ ++ l₂) ++ (l₃ ++ l₄))` into
    the six leaf facts used at every per-entry `Hinv` site:
    `k1 = k2`, `k1 ∈ getVars expr`, and `k1 ∉ lᵢ` for each `i`.
    Replaces the recurring `zip_self_eq` + `simp [List.removeAll, ...]`
    + `notin_append4` cascade. -/
private theorem zip_removeAll4_decompose
    {expr : Expression.Expr}
    {l₁ l₂ l₃ l₄ : List Expression.Ident}
    {k1 k2 : Expression.Ident}
    (Hkin : (k1, k2) ∈
              ((Imperative.HasVarsPure.getVars (P:=Expression) expr).removeAll
                  ((l₁ ++ l₂) ++ (l₃ ++ l₄))).zip
                ((Imperative.HasVarsPure.getVars (P:=Expression) expr).removeAll
                  ((l₁ ++ l₂) ++ (l₃ ++ l₄)))) :
    k1 = k2 ∧
    k1 ∈ Imperative.HasVarsPure.getVars (P:=Expression) expr ∧
    k1 ∉ l₁ ∧ k1 ∉ l₂ ∧ k1 ∉ l₃ ∧ k1 ∉ l₄ := by
  refine ⟨zip_self_eq Hkin, ?_⟩
  have Hk1_in := (List.of_mem_zip Hkin).1
  simp only [List.removeAll, List.mem_filter,
             List.elem_eq_mem, Bool.not_eq_true',
             decide_eq_false_iff_not] at Hk1_in
  obtain ⟨Hk1_pre, Hk1_notin⟩ := Hk1_in
  obtain ⟨H1, H2, H3, H4⟩ := List.notin_append4 Hk1_notin
  exact ⟨Hk1_pre, H1, H2, H3, H4⟩

/-- Positional decomposition for `(k1, k2) ∈ ks.zip ks'` under length
    equality: produce a position `n` together with the bounds and the
    pair-projection equalities `k1 = ks[n]` and `k2 = ks'[n]`.  Absorbs the
    `mem_iff_get` → `getElem_zip` → `Prod.mk.injEq` dance that recurs in
    the `Hsubst` input-half and `Hinv` class-(a) chases. -/
private theorem pair_in_zip_pos_decomp
    {α β} {ks : List α} {ks' : List β}
    (Hlen : ks.length = ks'.length)
    {k1 : α} {k2 : β} (Hkin : (k1, k2) ∈ ks.zip ks') :
    ∃ (n : Nat) (Hn_lt : n < ks.length) (Hn_lt' : n < ks'.length),
      k1 = ks[n]'Hn_lt ∧ k2 = ks'[n]'Hn_lt' := by
  rcases List.mem_iff_get.mp Hkin with ⟨n, Hn⟩
  have HzipLen : (ks.zip ks').length = ks.length := by
    rw [List.length_zip, Hlen, Nat.min_self]
  have Hn_lt : n.val < ks.length := HzipLen ▸ n.isLt
  have Hn_lt' : n.val < ks'.length := Hlen ▸ Hn_lt
  have Hget : (ks.zip ks')[n.val]'n.isLt = (ks[n.val]'Hn_lt, ks'[n.val]'Hn_lt') :=
    List.getElem_zip
  have HEq : (k1, k2) = (ks[n.val]'Hn_lt, ks'[n.val]'Hn_lt') := Hget ▸ Hn.symm
  exact ⟨n.val, Hn_lt, Hn_lt',
    ((Prod.mk.injEq _ _ _ _).mp HEq).1, ((Prod.mk.injEq _ _ _ _).mp HEq).2⟩

/-- Reverse of `pair_in_zip_pos_decomp`: under matching position bounds,
    the pair `(ks[n], ks'[n])` lies in `ks.zip ks'`.  Used by the
    `Hk1 ∉ inputs.keys` chase in `Hinv` class-(a). -/
private theorem pair_in_zip_of_pos
    {α β} {ks : List α} {ks' : List β}
    {n : Nat} (Hn_lt : n < ks.length) (Hn_lt' : n < ks'.length) :
    (ks[n]'Hn_lt, ks'[n]'Hn_lt') ∈ ks.zip ks' :=
  List.mem_iff_get.mpr
    ⟨⟨n, by rw [List.length_zip]; omega⟩, List.getElem_zip⟩

/-- Bridge from the `tmp_` half of `Hwfgenst` to `isNotDefined` for a list
    of fresh temp names: if a name is `isTempIdent` and is *not* in
    `γ.generated`, then it must be undefined in σ (otherwise the iff in
    `Hwfgentmp` would put it in `γ.generated`).

    Takes the dual-clause `tmp_` half: for every `v`, `v ∈ generated ∧
    isTempIdent v ↔ (σ v).isSome ∧ isTempIdent v`. -/
private theorem fresh_temps_not_defined
    {σ : CoreStore} {γ : CoreTransformState}
    (Hwfgentmp : ∀ v, v ∈ γ.genState.generated ∧ isTempIdent v ↔
                  ((σ v).isSome ∧ isTempIdent v))
    {newTemps : List Expression.Ident}
    (Hnotgen : ∀ x ∈ newTemps, x ∉ γ.genState.generated)
    (HtempPred : Forall (fun x => isTempIdent x) newTemps) :
    Imperative.isNotDefined σ newTemps := by
  intro v Hin
  have Htemp : isTempIdent v := (List.Forall_mem_iff.mp HtempPred) v Hin
  have Hnotin : v ∉ γ.genState.generated := Hnotgen v Hin
  -- If σ v = some _ then `Hwfgentmp.mpr` would put v in `γ.generated`,
  -- contradicting `Hnotin`.  Case split on `σ v` directly.
  match hσ : σ v with
  | none => rfl
  | some w =>
      exfalso
      apply Hnotin
      have Hbundle : (σ v).isSome ∧ isTempIdent v := by
        refine ⟨?_, Htemp⟩
        simp [hσ]
      exact ((Hwfgentmp v).mpr Hbundle).1

/-- Positional decomposition for `Map.find?` against the L6 canonical
    `createOldVarsSubst` map.  Given a hit
    `Map.find? (createOldVarsSubst (...zip-form...)) k = some w`, extract
    the positional witness `i < oldVars.length` together with the shape
    facts `k = mkOld oldVars[i].name` and `w = createFvar genOldIdents[i]`.

    Absorbs the verbatim ~125-LoC `HCanonLen → Hni_lt → HtripGet → Htrip_shape →
    HoldG_get → HgoEq → HkwEq → Hk_eq / Hw_eq` chain that recurs at three
    `createOldVarsSubst`-flavoured sites in `callElimStatementCorrect`
    (`HoldSubBridge`, `Hinv` class-(b1), `Hpred_disj` class-(b1)). -/
private theorem createOldVarsSubst_pos_decomp
    {genOldIdents : List Expression.Ident}
    {oldTys : List Lambda.LTy}
    {oldVars : List Expression.Ident}
    (HgenOldLen : genOldIdents.length = oldVars.length)
    (HoldTysLen : oldTys.length = oldVars.length)
    {k : Expression.Ident} {w : Expression.Expr}
    (Hf : Map.find?
      (Core.Transform.createOldVarsSubst
        ((((genOldIdents.zip oldTys).zip oldVars).zip
          (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            (fun (((fresh, ty), _orig), oldG) =>
              ((fresh, ty), oldG)))) k = some w) :
    ∃ (i : Nat) (Hi : i < oldVars.length),
      k = CoreIdent.mkOld (oldVars[i]'Hi).name ∧
      w = Core.Transform.createFvar
            (genOldIdents[i]'(by rw [HgenOldLen]; exact Hi)) := by
  -- Local abbreviations matching the call-site canonical names.
  let oldGVars : List Expression.Ident :=
    oldVars.map (fun g => CoreIdent.mkOld g.name)
  let oldTripsCanonical :
      List ((Expression.Ident × Expression.Ty) × Expression.Ident) :=
    (((genOldIdents.zip oldTys).zip oldVars).zip oldGVars).map
      (fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG))
  -- (k, w) ∈ createOldVarsSubst oldTripsCanonical (as List).
  have Hkw_mem_list :
      List.Mem (k, w)
        (Core.Transform.createOldVarsSubst oldTripsCanonical) :=
    Map.find?_mem _ k w Hf
  -- createOldVarsSubst trips = trips.map go (definitional).
  rcases List.mem_map.mp Hkw_mem_list with ⟨trip, Htrip_in, Htrip_eq⟩
  rcases List.mem_iff_get.mp Htrip_in with ⟨ni, Hni⟩
  -- Length facts.
  have HoldGLen : oldGVars.length = oldVars.length := by
    simp [oldGVars, List.length_map]
  have Hni_lt_canon : ni.val < oldTripsCanonical.length := ni.isLt
  have Hni_lt : ni.val < oldVars.length := by
    have := ni.isLt
    simp [oldTripsCanonical, List.length_map, List.length_zip, HgenOldLen,
          HoldTysLen, HoldGLen] at this; exact this
  have Hni_lt_genOld : ni.val < genOldIdents.length := by omega
  have Hni_lt_oldTys : ni.val < oldTys.length := by omega
  have Hni_lt_oldGVars : ni.val < oldGVars.length := HoldGLen ▸ Hni_lt
  -- Project the canonical trip via zip-getElem reductions.
  have HtripGet :
      oldTripsCanonical[ni.val]'Hni_lt_canon =
        ((genOldIdents[ni.val]'Hni_lt_genOld,
          oldTys[ni.val]'Hni_lt_oldTys),
         oldGVars[ni.val]'Hni_lt_oldGVars) := by
    show (((((genOldIdents.zip oldTys).zip oldVars).zip
      oldGVars).map _)[ni.val]'Hni_lt_canon) = _
    simp only [List.getElem_map, List.getElem_zip]
  have Htrip_shape :
      trip = ((genOldIdents[ni.val]'Hni_lt_genOld,
               oldTys[ni.val]'Hni_lt_oldTys),
              oldGVars[ni.val]'Hni_lt_oldGVars) := by
    rw [← Hni]; exact HtripGet
  have HoldG_get :
      oldGVars[ni.val]'Hni_lt_oldGVars =
        CoreIdent.mkOld (oldVars[ni.val]'Hni_lt).name := by
    show (oldVars.map (fun g => CoreIdent.mkOld g.name))[ni.val]'_ = _
    rw [List.getElem_map]
  have HkwEq :
      (k, w) = (oldGVars[ni.val]'Hni_lt_oldGVars,
                Core.Transform.createFvar
                  (genOldIdents[ni.val]'Hni_lt_genOld)) := by
    rw [← Htrip_eq, Htrip_shape]; rfl
  refine ⟨ni.val, Hni_lt, ?_, ((Prod.mk.injEq _ _ _ _).mp HkwEq).2⟩
  rw [((Prod.mk.injEq _ _ _ _).mp HkwEq).1, HoldG_get]

/-- Positional decomposition for `Map.find?` against the L6
    `inputOnlyOldSubst` map.  Given a hit
    `Map.find? (inputOnlyOldSubst inputs inputArgs outputs posts) k = some w`,
    extract the positional witness `ni < inputs.length` (with the
    matching `ni < inputArgs.length`) together with the shape facts
    `k = mkOld inputs[ni].name` and `w = inputArgs[ni]`, plus the
    guard byproduct `inputs[ni] ∉ outputs`.

    Absorbs the verbatim ~80-LoC `List.mem_filterMap` + `by_cases Hg` +
    positional `List.mem_iff_get` + `getElem_zip` chain that recurs at
    three `inputOnlyOldSubst`-flavoured sites in `callElimStatementCorrect`
    (`HinputSubBridge`, `Hinv` class-(b2), `Hpred_disj` class-(b2)).

    Mirror of `createOldVarsSubst_pos_decomp` for the input-only old
    substitution map. -/
private theorem inputOnlyOldSubst_pos_decomp
    {inputs : List Expression.Ident}
    {inputArgs : List Expression.Expr}
    {outputs : List Expression.Ident}
    {posts : List Expression.Expr}
    {k : Expression.Ident} {w : Expression.Expr}
    (Hf : Map.find?
      ((inputs.zip inputArgs).filterMap
        (fun (paramId, argExpr) =>
          let oldVar := CoreIdent.mkOld paramId.name
          if !outputs.contains paramId &&
             posts.any (fun e => Lambda.LExpr.freeVars e |>.any
               (fun (id, _) => id == oldVar))
          then some (oldVar, argExpr)
          else none)) k = some w) :
    ∃ (ni : Nat) (Hi : ni < inputs.length)
        (Hi' : ni < inputArgs.length),
      k = CoreIdent.mkOld (inputs[ni]'Hi).name ∧
      w = inputArgs[ni]'Hi' ∧
      (inputs[ni]'Hi) ∉ outputs := by
  -- (k, w) ∈ inputOnlyOldSubst (as List).
  have Hkw_mem_list :
      List.Mem (k, w)
        ((inputs.zip inputArgs).filterMap
          (fun (paramId, argExpr) =>
            let oldVar := CoreIdent.mkOld paramId.name
            if !outputs.contains paramId &&
               posts.any (fun e => Lambda.LExpr.freeVars e |>.any
                 (fun (id, _) => id == oldVar))
            then some (oldVar, argExpr)
            else none)) :=
    Map.find?_mem _ k w Hf
  -- Apply List.mem_filterMap to extract a witness pair.
  rcases List.mem_filterMap.mp Hkw_mem_list with
    ⟨pair, Hpair_in, Hpair_eq⟩
  -- Case-split on the guard.
  by_cases Hg :
      (!outputs.contains pair.fst &&
       posts.any
         (fun e => Lambda.LExpr.freeVars e |>.any
           (fun (id, _) => id == CoreIdent.mkOld pair.fst.name))) = true
  · -- guard = true branch.
    have Hpair_eq' :
        (CoreIdent.mkOld pair.fst.name, pair.snd) = (k, w) := by
      simp only [Hg, if_true] at Hpair_eq
      exact Option.some_inj.mp Hpair_eq
    have Hk_eq : k = CoreIdent.mkOld pair.fst.name :=
      ((Prod.mk.injEq _ _ _ _).mp Hpair_eq').1.symm
    have Hw_eq : w = pair.snd :=
      ((Prod.mk.injEq _ _ _ _).mp Hpair_eq').2.symm
    -- pair ∈ inputs.zip inputArgs.
    rcases List.mem_iff_get.mp Hpair_in with ⟨ni, Hni⟩
    have Hni_lt_zip : ni.val < (inputs.zip inputArgs).length := ni.isLt
    have Hni_lt_min : ni.val < min inputs.length inputArgs.length :=
      List.length_zip ▸ Hni_lt_zip
    have Hni_lt_inputs : ni.val < inputs.length := by omega
    have Hni_lt_inputArgs : ni.val < inputArgs.length := by omega
    -- Project pair to its components positionally.
    have Hpair_shape :
        pair = (inputs[ni.val]'Hni_lt_inputs,
                inputArgs[ni.val]'Hni_lt_inputArgs) := by
      have HpairGet :
          (inputs.zip inputArgs)[ni.val]'Hni_lt_zip =
            (inputs[ni.val]'Hni_lt_inputs,
             inputArgs[ni.val]'Hni_lt_inputArgs) := List.getElem_zip
      rw [← Hni]; exact HpairGet
    refine ⟨ni.val, Hni_lt_inputs, Hni_lt_inputArgs, ?_, ?_, ?_⟩
    · rw [Hk_eq, Hpair_shape]
    · rw [Hw_eq, Hpair_shape]
    · -- inputs[ni.val] ∉ outputs from guard.
      have HgL : (!outputs.contains pair.fst) = true :=
        (Bool.and_eq_true _ _).mp Hg |>.1
      simp at HgL
      rwa [Hpair_shape] at HgL
  · -- guard = false: contradiction.
    simp only [Hg] at Hpair_eq
    exact absurd Hpair_eq (by simp)

/-- Membership form: the entry's `.snd.expr` lies in `getCheckExprs conds`. -/
private theorem filterCheck_mem_getCheckExprs
    {conds : ListMap CoreLabel Procedure.Check}
    {f : CoreLabel × Procedure.Check → Bool}
    {entry : CoreLabel × Procedure.Check}
    (Hentry : entry ∈ conds.filter f) :
    entry.snd.expr ∈ Procedure.Spec.getCheckExprs conds := by
  have Hin_full := (List.mem_filter.mp Hentry).1
  simp only [Procedure.Spec.getCheckExprs, List.mem_map]
  refine ⟨entry.snd, ?_, rfl⟩
  rw [ListMap.values_eq_map_snd]
  exact List.mem_map_of_mem Hin_full

/-- `Hp`+`Hfind`+`lkup` ⇒ `proc' = proc` ∧ postcondition-membership lift
    `proc' ↦ proc`. Aligns `Hwfcallsite` (over `proc`) with checks indexed
    by the destructured `proc'` at both call-arm sites. -/
private theorem procEq_and_postExprs_bridge
    {p : Program} {procName : String} {proc proc' : Procedure}
    (Hp : ∀ pname, π pname = Program.Procedure.find? p ⟨pname, ()⟩)
    (Hfind : Program.Procedure.find? p ⟨procName, ()⟩ = some proc')
    (lkup : π procName = some proc) :
    proc' = proc ∧
    (∀ c, c ∈ proc'.spec.postconditions.values →
        c.expr ∈ Procedure.Spec.getCheckExprs proc.spec.postconditions) := by
  have HprocEq : proc' = proc := by
    have Hπ := Hp procName; rw [Hπ] at lkup; rw [Hfind] at lkup
    exact (Option.some_inj.mp lkup.symm).symm
  refine ⟨HprocEq, fun c Hc_in => ?_⟩
  simp only [Procedure.Spec.getCheckExprs, List.mem_map]
  refine ⟨c, ?_, rfl⟩
  rw [HprocEq] at Hc_in
  rw [ListMap.values_eq_map_snd]
  rwa [ListMap.values_eq_map_snd] at Hc_in

/-- Bridge between the boolean (`!=`) and propositional (`≠`) forms of the
    "non-Free" precondition filter.  Both filters select the same entries; the
    proof is a per-entry `decide` reduction.  Used at three sites in the
    fail-arm of `callElimStatementCorrect_terminal_call_arm_fail` to align
    `presFiltered` (uses `≠`) with the filter shape produced by the L4
    `H_asserts_zip_fail` chain (uses `!=`). -/
private theorem filter_bne_eq_filter_ne
    (preconditions : List (CoreLabel × Procedure.Check)) :
    preconditions.filter (fun (_, check) => check.attr != .Free) =
    preconditions.filter (fun (_, c) => c.attr ≠ .Free) := by
  apply List.filter_congr
  intro entry _
  cases entry with
  | mk _ c =>
    by_cases hc : c.attr = Procedure.CheckAttr.Free
    · simp [hc]
    · simp [hc]

/-- Store-agreement helper for `σ_R1`-style stacks (the σ_R1 layer
    overlaying `genOldIdents ↦ oldVals` on σO, plus the σO ← σAO ←
    σA ← σ chain from havoc + InitStates).

    For any identifier `v` not touched by any layer, all four stores
    agree: `updatedStates σO genOldIds oldVals v = σ v`.  Used at three
    sites in `callElimStatementCorrect` (D2c "argExpr survives" branches
    and the L6 `Hinv` derivations). -/
private theorem σR1_eq_σ_for_notTouched
    {σ σA σAO σO : CoreStore}
    {ins outs genOldIds : List Expression.Ident}
    {argVals oVals oldVals : List Expression.Expr}
    (Hinitin : InitStates σ ins argVals σA)
    (Hinitout : InitStates σA outs oVals σAO)
    (Hhav : HavocVars σAO outs σO)
    {v : Expression.Ident}
    (HvNotIns : v ∉ ins)
    (HvNotOuts : v ∉ outs)
    (HvNotGen : v ∉ genOldIds) :
    updatedStates σO genOldIds oldVals v = σ v := by
  rw [updatedStates_get_notin HvNotGen]
  rcases HavocVarsUpdateStates Hhav with ⟨ovh, Hup_havoc⟩
  have HσO_eq : σO = updatedStates σAO outs ovh := UpdateStatesUpdated Hup_havoc
  rw [HσO_eq, updatedStates_get_notin HvNotOuts,
      initStates_get_notin Hinitout HvNotOuts,
      initStates_get_notin Hinitin HvNotIns]

-- Q19-I bind-shell simp golf: shared simp sets used inside the
-- `callElim*_ok` no-throw lemmas and `callElimCmd_call_eq`. The
-- hypothesis name is captured as an `ident` and spliced into the
-- `simp ... at` location list.
local macro "bind_shell" "at" h:ident : tactic => `(tactic|
  simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
             pure, ExceptT.pure, StateT.pure] at $h:ident)

local macro "bind_shell_state" "at" h:ident : tactic => `(tactic|
  simp only [bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
             pure, ExceptT.pure, StateT.pure,
             get, getThe, MonadStateOf.get, MonadState.get, StateT.get,
             set, MonadStateOf.set, StateT.set,
             monadLift, MonadLift.monadLift, liftM, ExceptT.lift,
             Functor.map, StateT.map, Except.mapError] at $h:ident)

/-- No-throw fact for the `oldTys ← oldVars.mapM ...` step inside
    `callElimCmd`.  When every `g ∈ oldVars` is a key of
    `proc.header.inputs`, the `find?` lookup never throws, so the
    `mapM` reduces to `Except.ok oldTys` with `oldTys.length =
    oldVars.length`. -/
private theorem oldVars_oldTys_mapM_ok
    {proc : Procedure}
    {oldVars : List Expression.Ident}
    {γ : CoreTransformState}
    (Holdvars_in_inputs :
      ∀ g ∈ oldVars, (ListMap.keys proc.header.inputs).contains g) :
    ∃ (oldTys : List (Lambda.LTy)) (γ' : CoreTransformState),
      (oldVars.mapM (m:=CoreTransformM) (oldTyLookupCallElim proc))
        γ
        = (Except.ok oldTys, γ') ∧
      oldTys.length = oldVars.length := by
  -- Bridge: `keys.contains g = true` gives `find? g = some _`.
  -- Use the contrapositive of `ListMap.find?_of_not_mem_values`:
  --   `find? = none → g ∉ keys`, so `g ∈ keys → find? ≠ none`.
  have Hfind_some :
      ∀ (m : ListMap Expression.Ident Lambda.LMonoTy)
        (g : Expression.Ident),
        (ListMap.keys m).contains g = true →
          ∃ v, ListMap.find? m g = some v := by
    intro m g Hcontains
    have Hmem : g ∈ ListMap.keys m := List.contains_iff_mem.mp Hcontains
    cases hf : ListMap.find? m g with
    | none =>
      have := ListMap.find?_of_not_mem_values m hf
      exact absurd Hmem this
    | some v => exact ⟨v, rfl⟩
  -- Induct on `oldVars`; threading the state explicitly.
  induction oldVars generalizing γ with
  | nil =>
    refine ⟨[], γ, ?_, rfl⟩
    simp [List.mapM_nil, pure, ExceptT.pure, StateT.pure, ExceptT.mk]
  | cons g rest ih =>
    -- Head: lookup succeeds via `Holdvars_in_inputs`.
    have Hg_in : (ListMap.keys proc.header.inputs).contains g = true := by
      exact Holdvars_in_inputs g (by simp)
    obtain ⟨ty, Hty⟩ := Hfind_some proc.header.inputs g Hg_in
    -- Tail: IH applies because `Holdvars_in_inputs` weakens.
    have Hrest : ∀ g' ∈ rest, (ListMap.keys proc.header.inputs).contains g' = true :=
      fun g' Hin => Holdvars_in_inputs g' (List.mem_cons_of_mem _ Hin)
    obtain ⟨tys', γ'', Heqtail, Hlen⟩ := ih Hrest (γ := γ)
    refine ⟨Lambda.LTy.forAll [] ty :: tys', γ'', ?_, ?_⟩
    · -- Unfold mapM_cons and chain the head match through to the tail mapM.
      -- Strategy: unfold the bind shell and `pure` in both the goal and
      -- `Heqtail` so the inner-mapM call is in a matching form, then `rw`.
      simp only [List.mapM_cons, oldTyLookupCallElim,
                 bind, ExceptT.bind, ExceptT.bindCont,
                 ExceptT.mk, StateT.bind,
                 pure, ExceptT.pure, StateT.pure, Hty]
      rw [Heqtail]
      rfl
    · simp [Hlen]

/-- Polymorphic no-throw fact for the shared body of
    `Core.Transform.createAsserts` and `Core.Transform.createAssumes`.
    Both functions are byte-identical modulo the `Statement`
    constructor (`assert` vs `assume`); their inner `mapM` only
    invokes `genIdent` (a pure non-throwing state mutation), so the
    computation always reduces to `Except.ok stmts` with
    `stmts.length = conds.length`.  The shape conjunct exposes the
    list as a `conds.zip labels`-shape that the label-agnostic
    downstream consumer needs.  Parameterized by the constructor
    `mkStmt` so both `_ok` lemmas can share this proof. -/
private theorem createCheckStmts_ok
    (mkStmt : String → Expression.Expr → Imperative.MetaData Expression → Statement)
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String)
    (γ : CoreTransformState) :
    ∃ (stmts : List Statement) (γ' : CoreTransformState),
      (conds.mapM
            (fun (entry : CoreLabel × Procedure.Check) =>
              (do
                let newLabel ← Core.Transform.genIdent entry.fst
                  (fun s => s!"{labelPrefix}{s}")
                return mkStmt newLabel.toPretty
                  (Lambda.LExpr.substFvars entry.snd.expr subst)
                  (entry.snd.md.setCallSiteFileRange md)
                : CoreTransformM Statement))) γ
        = (Except.ok stmts, γ') ∧
      stmts.length = conds.length ∧
      ∃ (labels : List String), labels.length = conds.length ∧
        stmts = (conds.zip labels).map (fun (entry, lbl) =>
          mkStmt lbl
            (Lambda.LExpr.substFvars entry.snd.expr subst)
            (entry.snd.md.setCallSiteFileRange md)) := by
  -- `ListMap α β := List (α × β)`, so `conds.mapM` is `List.mapM` over
  -- the underlying list.  Induct on that list, threading the state.
  induction conds generalizing γ with
  | nil =>
    exact ⟨[], γ, by simp [List.mapM_nil, pure, ExceptT.pure, StateT.pure, ExceptT.mk],
            rfl, [], rfl, by simp⟩
  | cons head rest ih =>
    obtain ⟨l, check⟩ := head
    -- Head: genIdent always succeeds, producing a label and updated state.
    cases hgi : Core.Transform.genIdent l (fun s => s!"{labelPrefix}{s}") γ.genState with
    | mk newLabel γgen' =>
      -- The post-genIdent CoreTransformState (genState updated, rest preserved).
      let γhead : CoreTransformState :=
        { genState := γgen',
          currentProgram := γ.currentProgram,
          currentProcedureName := γ.currentProcedureName,
          cachedAnalyses := γ.cachedAnalyses,
          factory := γ.factory,
          statistics := γ.statistics }
      obtain ⟨stmts', γ'', Heqtail, Hlen, labelsTail, HlblsLen, Hshape⟩ := ih (γ := γhead)
      refine ⟨mkStmt newLabel.toPretty
                (Lambda.LExpr.substFvars check.expr subst)
                (check.md.setCallSiteFileRange md) :: stmts', γ'', ?_, ?_, ?_⟩
      · -- Reduce both sides to the same `List.mapM` core, then chain via Heqtail.
        simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.bindCont,
                   ExceptT.mk, ExceptT.lift, ExceptT.pure,
                   StateT.bind, StateT.pure, pure,
                   monadLift, MonadLift.monadLift, liftM,
                   Functor.map, StateT.map, liftCoreGenM, hgi]
        bind_shell_state at Heqtail
        rw [Heqtail]
        rfl
      · simp [Hlen]
      · refine ⟨newLabel.toPretty :: labelsTail, ?_, ?_⟩
        · simp [HlblsLen]
        · simp only [List.zip_cons_cons, List.map_cons]
          rw [Hshape]

/-- No-throw fact for `Core.Transform.createAsserts`.  Specialization
    of `createCheckStmts_ok` to the `Statement.assert` constructor. -/
private theorem createAsserts_ok
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String)
    (γ : CoreTransformState) :
    ∃ (asserts : List Statement) (γ' : CoreTransformState),
      Core.Transform.createAsserts conds subst md labelPrefix γ
        = (Except.ok asserts, γ') ∧
      asserts.length = conds.length ∧
      ∃ (labels : List String), labels.length = conds.length ∧
        asserts = (conds.zip labels).map (fun (entry, lbl) =>
          Statement.assert lbl
            (Lambda.LExpr.substFvars entry.snd.expr subst)
            (entry.snd.md.setCallSiteFileRange md)) := by
  unfold Core.Transform.createAsserts
  exact createCheckStmts_ok Statement.assert conds subst md labelPrefix γ

/-- No-throw fact for `Core.Transform.createAssumes`.  Specialization
    of `createCheckStmts_ok` to the `Statement.assume` constructor. -/
private theorem createAssumes_ok
    (conds : ListMap CoreLabel Procedure.Check)
    (subst : Map Expression.Ident Expression.Expr)
    (md : Imperative.MetaData Expression)
    (labelPrefix : String)
    (γ : CoreTransformState) :
    ∃ (assumes : List Statement) (γ' : CoreTransformState),
      Core.Transform.createAssumes conds subst md labelPrefix γ
        = (Except.ok assumes, γ') ∧
      assumes.length = conds.length ∧
      ∃ (labels : List String), labels.length = conds.length ∧
        assumes = (conds.zip labels).map (fun (entry, lbl) =>
          Statement.assume lbl
            (Lambda.LExpr.substFvars entry.snd.expr subst)
            (entry.snd.md.setCallSiteFileRange md)) := by
  unfold Core.Transform.createAssumes
  exact createCheckStmts_ok Statement.assume conds subst md labelPrefix γ

/-- Internal-shape destructuring of a successful `callElimCmd` call.

    The B1 phase of `callElimStatementCorrect` needs to bind the
    `argTrips`, `outTrips`, `genOldIdents`, `oldTys`, `asserts`,
    `assumes` and intermediate gen states produced inside
    `callElimCmd`'s `do` block, plus a procedure-lookup result and
    the structural equation `sts' = argInit ++ outInit ++ oldInit ++
    asserts ++ havocs ++ assumes`.  Because the inner
    `bind`/`ExceptT.bindCont` envelope does not normalize
    syntactically to a bare `match`, the destructuring is factored
    through this helper so the call site stays clean.

    The input state is constrained to have `currentProgram := some p`
    (which is the post-`modify` shape produced by `callElimStmt`'s
    outer `runWith`).

    The helper exposes everything the call site needs to subst the
    structural equation and continue with L1-L6 reasoning.  Internal
    state names `s_arg/s_out/s_old/s_postold/s_assert/s_assume` are
    threaded through; only state-shape relevant downstream are retained.
-/

private theorem callElimCmd_call_eq
    {procName : String} {args : List (CallArg Expression)}
    {md : Imperative.MetaData Expression}
    {γ : CoreTransformState}
    {γ_out : CoreTransformState}
    {p : Program}
    {sts' : List Statement}
    (Heq : (callElimCmd (CmdExt.call procName args md))
              { γ with currentProgram := some p }
            = (Except.ok (some sts'), γ_out)) :
    ∃ proc argTrips outTrips genOldIdents oldTys asserts assumes
       s_arg s_out s_old,
      Program.Procedure.find? p ⟨procName, ()⟩ = some proc ∧
      let oldVars : List Expression.Ident := callElim_oldVars proc args
      genArgExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs)
          (CallArg.getInputExprs args)
          { γ with currentProgram := some p,
                   statistics := γ.statistics.increment
                     (toString CallElim.Stats.visitedCalls) 1 }
        = (Except.ok argTrips, s_arg) ∧
      genOutExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs)
          (CallArg.getLhs args) s_arg
        = (Except.ok outTrips, s_out) ∧
      genOldExprIdents oldVars s_out.genState = (genOldIdents, s_old) ∧
      oldTys.length = oldVars.length ∧
      sts' =
        Core.Transform.createInits argTrips md ++
        Core.Transform.createInitVars outTrips md ++
        Core.Transform.createInitVars
          ((genOldIdents.zip oldTys).zip oldVars)
          md ++
        asserts ++
        Core.Transform.createHavocs (CallArg.getLhs args) md ++
        assumes ∧
      -- Structural shape of `asserts`:  abstract `pres.zip labels` map.
      (∃ (assertLabels : List String),
        let pres := (proc.spec.preconditions.filter
                       (fun (_, check) => check.attr != .Free))
        let assertSubst :=
              ((ListMap.keys proc.header.inputs).zip
                (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst) ++
              (ListMap.keys proc.header.outputs).zip
                (Core.Transform.createFvars (CallArg.getLhs args)))
        assertLabels.length = pres.length ∧
        asserts = (pres.zip assertLabels).map (fun (entry, lbl) =>
          Statement.assert lbl
            (Lambda.LExpr.substFvars entry.snd.expr assertSubst)
            (entry.snd.md.setCallSiteFileRange md))) ∧
      -- Structural shape of `assumes`:  abstract `posts.zip labels` map.
      (∃ (assumeLabels : List String),
        let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
              callElim_inputOnlyOldSubst proc args
        let oldTripsCanonical :=
              (((genOldIdents.zip oldTys).zip oldVars).zip
              (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
              fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
        let oldSubst : Map Expression.Ident Expression.Expr :=
              Core.Transform.createOldVarsSubst oldTripsCanonical ++ inputOnlyOldSubst
        let posts := Procedure.Spec.updateCheckExprs
                       (proc.spec.postconditions.values.map
                         (fun c => Lambda.LExpr.substFvars c.expr oldSubst))
                       proc.spec.postconditions
        let assumeSubst :=
              ((ListMap.keys proc.header.outputs).zip
                (Core.Transform.createFvars (CallArg.getLhs args)) ++
              ((ListMap.keys proc.header.inputs).zip
                (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst)).filter
                  (fun (id, _) => !(ListMap.keys proc.header.outputs).contains id))
        assumeLabels.length = posts.length ∧
        assumes = (posts.zip assumeLabels).map (fun (entry, lbl) =>
          Statement.assume lbl
            (Lambda.LExpr.substFvars entry.snd.expr assumeSubst)
            (entry.snd.md.setCallSiteFileRange md))) := by
  -- Unfold `callElimCmd`'s `do` block step-by-step.  The first action
  -- is `incrementStat` (a `modify`), then `(← get).currentProgram` is
  -- matched.  Because we passed `{γ with currentProgram := some p}`,
  -- we can compute the post-increment state explicitly.
  unfold callElimCmd at Heq
  simp only [incrementStat, modify, modifyGet, MonadStateOf.modifyGet,
             MonadState.modifyGet, StateT.modifyGet,
             bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
             pure, ExceptT.pure,
             get, getThe, MonadStateOf.get, MonadState.get, StateT.get,
             monadLift, MonadLift.monadLift, liftM, ExceptT.lift,
             Functor.map, StateT.map] at Heq
  cases hfind : Program.Procedure.find? p ⟨procName, ()⟩ with
  | none =>
      rw [hfind] at Heq
      exact absurd Heq (by intro h; cases h)
  | some proc =>
      rw [hfind] at Heq
      bind_shell at Heq
      generalize Heqarg :
        (genArgExprIdentsTrip
          (Lambda.LMonoTySignature.toTrivialLTy proc.header.inputs)
          (CallArg.getInputExprs args)
          { γ with currentProgram := some p,
                   statistics := γ.statistics.increment
                     (toString CallElim.Stats.visitedCalls) 1 }) =
            pair_arg at Heq
      cases pair_arg with
      | mk res_arg s_arg =>
        cases res_arg with
        | error e =>
            exact absurd Heq (by intro h; cases h)
        | ok argTrips =>
            bind_shell at Heq
            generalize Heqout :
              (genOutExprIdentsTrip
                (Lambda.LMonoTySignature.toTrivialLTy proc.header.outputs)
                (CallArg.getLhs args) s_arg) = pair_out at Heq
            cases pair_out with
            | mk res_out s_out =>
              cases res_out with
              | error e =>
                  exact absurd Heq (by intro h; cases h)
              | ok outTrips =>
                  -- Now extract `genOldIdents` from the next layer.
                  -- The next layer is `(StateT.map Except.ok
                  --   (liftCoreGenM (genOldExprIdents oldVars))).bind ...`.
                  simp only [liftCoreGenM, bind, StateT.bind,
                             ExceptT.bindCont, pure, StateT.map] at Heq
                  -- Hoist the old-vars filter once for the rest of the proof.
                  let oldVars : List Expression.Ident := callElim_oldVars proc args
                  generalize Heqold :
                    (genOldExprIdents oldVars s_out.genState) = pair_old at Heq
                  cases pair_old with
                  | mk genOldIdents s_old =>
                    -- B1: oldTys ← oldVars.mapM (oldVars ⊆ inputs.keys).
                    have Holdvars_in_inputs :
                        ∀ g ∈ oldVars,
                          (ListMap.keys proc.header.inputs).contains g := by
                      intro g Hg
                      have Hfilt : _ ∧ _ := List.mem_filter.mp Hg
                      have Hcond : _ = true := Hfilt.2
                      simp only [Bool.and_eq_true] at Hcond
                      exact Hcond.1.1
                    obtain ⟨oldTys, s_postold, Heqty, _Hlenty⟩ :=
                      oldVars_oldTys_mapM_ok (γ := { s_out with genState := s_old })
                        Holdvars_in_inputs
                    -- Reduce `pure`/`throw` to match Heq.
                    bind_shell at Heq
                    rw [Heqty] at Heq
                    bind_shell at Heq
                    -- ── B2 layer: asserts ← createAsserts ... ──
                    obtain ⟨asserts, s_assert, Heqas, _Hlenas,
                            assertLabels, HassertLabelsLen, HassertShape⟩ :=
                      createAsserts_ok
                        (proc.spec.preconditions.filter (fun (_, check) => check.attr != .Free))
                        ((ListMap.keys proc.header.inputs).zip
                          (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst) ++
                         (ListMap.keys proc.header.outputs).zip
                          (Core.Transform.createFvars (CallArg.getLhs args)))
                        md
                        callElimAssertPrefix
                        s_postold
                    rw [Heqas] at Heq
                    bind_shell at Heq
                    -- B2: assumes ← createAssumes (oldSubst helper).
                    let inputOnlyOldSubst : Map Expression.Ident Expression.Expr :=
                      callElim_inputOnlyOldSubst proc args
                    let oldTrips :=
                      (((genOldIdents.zip oldTys).zip oldVars).zip
                      (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
                      fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
                    let oldSubst : Map Expression.Ident Expression.Expr :=
                      Core.Transform.createOldVarsSubst oldTrips ++ inputOnlyOldSubst
                    obtain ⟨assumes, s_assume, Heqasm, _Hlenasm,
                            assumeLabels, HassumeLabelsLen, HassumeShape⟩ :=
                      createAssumes_ok
                        (Procedure.Spec.updateCheckExprs
                          (proc.spec.postconditions.values.map
                            (fun c => Lambda.LExpr.substFvars c.expr oldSubst))
                          proc.spec.postconditions)
                        ((ListMap.keys proc.header.outputs).zip
                          (Core.Transform.createFvars (CallArg.getLhs args)) ++
                         ((ListMap.keys proc.header.inputs).zip
                            (Core.Transform.createFvars argTrips.unzip.fst.unzip.fst)).filter
                              (fun (id, _) => !(ListMap.keys proc.header.outputs).contains id))
                        md
                        callElimAssumePrefix
                        s_assert
                    rw [Heqasm] at Heq
                    bind_shell_state at Heq
                    -- ── Callgraph update ──
                    -- `match σ.cachedAnalyses.callGraph, σ.currentProcedureName`.
                    -- We split on both branches.  The first branch may
                    -- throw via decrementEdge; refute that case.
                    refine ⟨proc, argTrips, outTrips, genOldIdents, oldTys,
                            asserts, assumes,
                            s_arg, s_out, s_old,
                            rfl, Heqarg, Heqout, Heqold, _Hlenty, ?_,
                            ⟨assertLabels, HassertLabelsLen, HassertShape⟩,
                            ⟨assumeLabels, HassumeLabelsLen, HassumeShape⟩⟩
                    · -- Structural equation: split on callgraph match,
                      -- then read off `sts' = ...`.  Use a single simp
                      -- set that unfolds `set`/`StateT.set`/`StateT.map`
                      -- so the post-callgraph pure-return reduces to a
                      -- raw `(Except.ok (List ...), state)` pair.
                      cases hcg : s_assume.cachedAnalyses.callGraph with
                      | none =>
                        cases hcpn : s_assume.currentProcedureName <;>
                          (rw [hcg, hcpn] at Heq
                           bind_shell_state at Heq
                           have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                           have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                           exact (Option.some.injEq _ _ |>.mp Hexc).symm)
                      | some cg =>
                        cases hcpn : s_assume.currentProcedureName with
                        | none =>
                          rw [hcg, hcpn] at Heq
                          bind_shell_state at Heq
                          have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                          have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                          exact (Option.some.injEq _ _ |>.mp Hexc).symm
                        | some callerName =>
                          rw [hcg, hcpn] at Heq
                          bind_shell_state at Heq
                          cases hde :
                            (cg.decrementEdge callerName procName) with
                          | error e =>
                            rw [hde] at Heq
                            bind_shell_state at Heq
                            exact absurd Heq (by intro h; cases h)
                          | ok cg' =>
                            rw [hde] at Heq
                            bind_shell_state at Heq
                            have Hpair := Prod.mk.injEq _ _ _ _ |>.mp Heq
                            have Hexc := Except.ok.injEq _ _ |>.mp Hpair.1
                            exact (Option.some.injEq _ _ |>.mp Hexc).symm

/-- For every non-call statement `s`, the call-elimination transformer
    `callElimStmt s p` returns `[s]` unchanged.  This collapses what was
    eight identical simp blocks (one per `Statement` constructor that is
    not a `Cmd.call`) into a single uniform reduction.  Used by
    `callElimStatementCorrect` to dispatch the non-call branches. -/
private theorem callElimStmt_non_call_eq
    {p : Program} {γ γ' : CoreTransformState} {sts : List Statement}
    {s : Statement}
    (hne : ∀ procName args md, s ≠ .cmd (CmdExt.call procName args md))
    (hH : (Except.ok sts, γ') = (runWith s (callElimStmt · p) γ)) :
    sts = [s] := by
  -- All 7 non-call top-level cases (cmd.cmd, block, ite, loop, exit,
  -- funcDecl, typeDecl) reduce uniformly via the same simp set; the
  -- inner `cmd.call` case is discharged by `hne`.
  match s, hne, hH with
  | .cmd (.call procName args md), hne, _ =>
      exact absurd rfl (hne procName args md)
  | .cmd (.cmd _), _, hH
  | .block _ _ _, _, hH
  | .ite _ _ _ _, _, hH
  | .loop _ _ _ _ _, _, hH
  | .exit _ _, _, hH
  | .funcDecl _ _, _, hH
  | .typeDecl _ _, _, hH =>
      simp only [runWith, StateT.run, callElimStmt, bind, pure,
                 StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
                 modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
                 StateT.modifyGet, monadLift, MonadLift.monadLift, ExceptT.lift,
                 StateT.pure, Functor.map, StateT.map,
                 Prod.mk.injEq, Except.ok.injEq] at hH
      exact hH.1

/-- Call-site WF clauses specialized at a fixed call form
    `(procName, args, md)` and a fixed procedure `proc`.

    Bundles the eight call-site WF clauses as named fields, so call-site
    code can `obtain ⟨...⟩ := Hwfcs.specialize Hst Hlkup` in one step. -/
structure WFCallSiteSpec (proc : Procedure) (args : List (CallArg Expression)) : Prop where
  /-- Pre-condition free vars are not `tmp_`/`old_`-prefixed and not in the
      call's `lhs`. -/
  preVarsFresh :
    ∀ pre ∈ Procedure.Spec.getCheckExprs proc.spec.preconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) pre,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  /-- Post-condition free vars are not `tmp_`/`old_`-prefixed and not in the
      call's `lhs`. -/
  postVarsFresh :
    ∀ post ∈ Procedure.Spec.getCheckExprs proc.spec.postconditions,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) post,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
      v ∉ CallArg.getLhs args
  /-- Argument-expression free vars are disjoint from the call's `lhs`. -/
  argVarsNotInLhs :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ CallArg.getLhs args
  /-- Procedure input/output parameter names are not `tmp_`/`old_`-prefixed. -/
  inoutFresh :
    ∀ v ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ¬ isTempIdent v ∧ ¬ isOldTempIdent v
  /-- Argument-expression free vars are disjoint from the procedure's
      `outputs.keys` (the global modset). -/
  argVarsNotInOutKeys :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.outputs
  /-- Argument-expression free vars are disjoint from the procedure's
      `inputs.keys` (procedure parameter names). -/
  argVarsNotInInKeys :
    ∀ argExpr ∈ CallArg.getInputExprs args,
    ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
      v ∉ ListMap.keys proc.header.inputs
  /-- Positional-alignment WF for inout outputs: for each output parameter
      `v ∈ outputs.keys` that is also an `lhs` entry (i.e., an inout pass),
      the call's lhs index for `v` agrees with the procedure's outputs-keys
      index.  Backs the L6 `HoldEval_bridge` derivation. -/
  outAlignment :
    ∀ v ∈ ListMap.keys proc.header.outputs,
      v ∈ CallArg.getLhs args →
      (CallArg.getLhs args).idxOf v =
        (ListMap.keys proc.header.outputs).idxOf v
  /-- Bool-totality of preconditions (`WFPrePostProp.boolTyped` clause): a
      precondition expression evaluates to either `tt` or `ff` whenever
      its free variables are defined in the store.  Backs the failing-arm
      witness derivation in `callElimStatementCorrect_terminal_call_arm_fail`. -/
  preBoolTyped :
    ∀ pre ∈ Procedure.Spec.getCheckExprs proc.spec.preconditions,
    ∀ (δ : Imperative.SemanticEval Expression)
      (σ : Imperative.SemanticStore Expression),
      Imperative.isDefinedOver
        (Imperative.HasVarsPure.getVars (P := Expression)) σ pre →
      δ σ pre = some Imperative.HasBool.tt ∨
      δ σ pre = some Imperative.HasBool.ff

/-- Call-site WF/disjointness invariants required by `callElimStatementCorrect`.

    A `WFCallSiteSpec` parameterized by the call form: fires only when
    `st` is a call; for non-call statements vacuously true.  Specialize
    via `Hwfcs.specialize Hst Hlkup`. -/
def WFCallSiteProp (_p : Program)
                   (π : String → Option Procedure)
                   (st : Statement) : Prop :=
  ∀ procName args md, st = .cmd (CmdExt.call procName args md) →
  ∀ proc, π procName = some proc →
    WFCallSiteSpec proc args

/-- Specialize the universally-quantified `WFCallSiteProp` at a fixed call
    form `st = .cmd (CmdExt.call procName args md)` and procedure lookup
    `π procName = some proc`. -/
theorem WFCallSiteProp.specialize {p : Program}
    {st : Statement}
    {procName : String} {args : List (CallArg Expression)} {md}
    {proc : Procedure}
    (Hwfcs : WFCallSiteProp p π st)
    (Hst : st = .cmd (CmdExt.call procName args md))
    (Hlkup : π procName = some proc) : WFCallSiteSpec proc args :=
  Hwfcs procName args md Hst proc Hlkup

/-- Project `WFcallProp.lhsWF` out of a `WFStatementsProp` whose head is a call. -/
private theorem callArgsLhs_nodup_of_wf {p : Program} {procName : String}
    {args : List (CallArg Expression)} {md : Imperative.MetaData Expression}
    {rest : List Statement} {lhs : List Expression.Ident}
    (Hwf : WF.WFStatementsProp p (.cmd (CmdExt.call procName args md) :: rest))
    (hCallArgsLhs : CallArg.getLhs args = lhs) : lhs.Nodup :=
  hCallArgsLhs ▸ ((List.Forall_cons _ _ _).mp Hwf).1.lhsWF

/-- Relation between the source store `σ` and the call-elim transform
    state `γ`'s tracked fresh-name set.

    Bundles the three fields of the legacy `Hwfgenst` hypothesis: the
    `tmp_*` alignment between `γ.genState.generated` and `σ`'s defined
    keys, the `old_*` freshness against `σ`, and `CoreGenState.WF` of
    `γ.genState`. -/
structure CoreGenStateRel (σ : CoreStore) (γ : CoreTransformState) : Prop where
  /-- `tmp_*`-prefixed names in `γ.genState.generated` are exactly the
      `tmp_*`-defined names in `σ`. -/
  tmpAlign : ∀ v, v ∈ γ.genState.generated ∧ isTempIdent v ↔
                  (σ v).isSome ∧ isTempIdent v
  /-- `old_*`-prefixed names are never defined in `σ`. -/
  oldFresh : ∀ v, isOldTempIdent v → (σ v).isNone
  /-- The fresh-name generator state is well-formed.  Folded in here so
      `CoreGenStateRel` is the complete γ-vs-σ relation needed by the
      call-elim proof. -/
  wfgen : CoreGenState.WF γ.genState

/-- Generic δ-fvar lookup: from a `WellFormedSemanticEvalVar` witness on
    the evaluator, evaluating an `fvar v` at any store reduces to the store
    lookup `σ v`. Used wherever the call-elim proof needs to push δ through
    a free-variable expression. -/
private theorem delta_fvar_eq_of_wfvars
    {delta : CoreEval}
    (Hwfvars : Imperative.WellFormedSemanticEvalVar delta)
    (sigma : CoreStore) (v : Expression.Ident) :
    delta sigma (Lambda.LExpr.fvar () v none) = sigma v := by
  have Hwfvr := Hwfvars
  simp [Imperative.WellFormedSemanticEvalVar] at Hwfvr
  rw [Hwfvr (Lambda.LExpr.fvar () v none) v]
  simp [Imperative.HasFvar.getFvar]

/-- Bundle the σ-freshness chain: from a Nodup of the combined
    `(γ.generated.reverse ++ argTemps ++ outTemps ++ genOldIdents)` plus
    the temp/old predicates and a downstream `UpdateStates`, derive the
    Nodup of the 3-segment list, the three per-segment σ-freshness facts,
    and the lifted σ'-freshness fact. -/
private theorem fresh_triple_σ_facts
    {σ σ' : CoreStore} {γ : CoreTransformState}
    {argTemps outTemps genOldIdents : List Expression.Ident}
    {vs' : List Expression.Ident} {es' : List Expression.Expr}
    (Hgenrel : CoreGenStateRel σ γ)
    (Hgennd' : (γ.genState.generated.reverse ++
                  argTemps ++ outTemps ++ genOldIdents).Nodup)
    (HargTemp : Forall (fun x => isTempIdent x) argTemps)
    (HoutTemp : Forall (fun x => isTempIdent x) outTemps)
    (HoldIdentsTemp : Forall (fun x => isOldTempIdent x) genOldIdents)
    (Hupdate : UpdateStates σ vs' es' σ') :
    (argTemps ++ outTemps ++ genOldIdents).Nodup ∧
    Imperative.isNotDefined σ argTemps ∧
    Imperative.isNotDefined σ outTemps ∧
    Imperative.isNotDefined σ genOldIdents ∧
    Imperative.isNotDefined σ' (argTemps ++ outTemps ++ genOldIdents) := by
  simp only [List.append_assoc] at Hgennd'
  have Hsplit := List.nodup_append.mp Hgennd'
  have Hnd3 : (argTemps ++ outTemps ++ genOldIdents).Nodup := by
    simp only [List.append_assoc]; exact Hsplit.2.1
  have Hnot : ∀ x ∈ argTemps ++ (outTemps ++ genOldIdents),
      x ∉ γ.genState.generated := fun x Hi Hg =>
    Hsplit.2.2 x (List.mem_reverse.mpr Hg) x Hi rfl
  have HArg := fresh_temps_not_defined Hgenrel.tmpAlign
    (fun _ h => Hnot _ (List.mem_append_left _ h)) HargTemp
  have HOut := fresh_temps_not_defined Hgenrel.tmpAlign
    (fun _ h => Hnot _ (List.mem_append_right _ (List.mem_append_left _ h))) HoutTemp
  have HOld : Imperative.isNotDefined _ _ := fun v Hin =>
    Option.isNone_iff_eq_none.mp
      (Hgenrel.oldFresh v ((List.Forall_mem_iff.mp HoldIdentsTemp) v Hin))
  refine ⟨Hnd3, HArg, HOut, HOld, UpdateStatesNotDefMonotone (fun v Hv => ?_) Hupdate⟩
  simp only [List.append_assoc, List.mem_append] at Hv
  rcases Hv with h | h | h
  · exact HArg v h
  · exact HOut v h
  · exact HOld v h

/-- Bundle of WF/generated/Nodup facts threaded through the
    `genArgExprIdentsTrip → genOutExprIdentsTrip → genOldExprIdents`
    pipeline.  Both call-elim arms (success and failure) need the same
    Nodup-of-the-combined-list witness in order to invoke
    `fresh_triple_σ_facts`; this helper absorbs the seven `have`-blocks
    that previously expanded inline in each arm. -/
private theorem genTrips_combined_nodup
    {s0 s_arg s_out : Core.Transform.CoreTransformState}
    {s_old : CoreGenState}
    {inputs : @Lambda.LTySignature Visibility} {args : List Expression.Expr}
    {argTrips : List ((Expression.Ident × Lambda.LTy) × Expression.Expr)}
    {outputs : @Lambda.LTySignature Visibility} {lhs : List Expression.Ident}
    {outTrips : List ((Expression.Ident × Expression.Ty) × Expression.Ident)}
    {oldVars : List Expression.Ident}
    {genOldIdents : List Expression.Ident}
    (Heqarg : Core.Transform.genArgExprIdentsTrip inputs args s0
                = (Except.ok argTrips, s_arg))
    (Heqout : Core.Transform.genOutExprIdentsTrip outputs lhs s_arg
                = (Except.ok outTrips, s_out))
    (Heqold : Core.Transform.genOldExprIdents oldVars s_out.genState
                = (genOldIdents, s_old))
    (Hwf0 : CoreGenState.WF s0.genState) :
    (s0.genState.generated.reverse ++
       argTrips.unzip.fst.unzip.fst ++
         outTrips.unzip.fst.unzip.fst ++
           genOldIdents).Nodup := by
  have Hwfgenargs : CoreGenState.WF s_arg.genState :=
    genArgExprIdentsTripWFMono Hwf0 Heqarg
  have Hwfgenouts : CoreGenState.WF s_out.genState :=
    genOutExprIdentsTripWFMono Hwfgenargs Heqout
  have Hwfgenolds : CoreGenState.WF s_old :=
    genOldExprIdentsTripWFMono Hwfgenouts Heqold
  have Hgenargs : s_arg.genState.generated =
      argTrips.unzip.fst.unzip.fst.reverse ++ s0.genState.generated :=
    genArgExprIdentsTripGeneratedWF Heqarg
  have Hgenouts : s_out.genState.generated =
      outTrips.unzip.fst.unzip.fst.reverse ++ s_arg.genState.generated :=
    genOutExprIdentsTripGeneratedWF Heqout
  have Hgenolds : s_old.generated =
      genOldIdents.reverse ++ s_out.genState.generated :=
    genOldExprIdents_GeneratedWF Heqold
  have HgenApp : s_old.generated =
      genOldIdents.reverse ++
        outTrips.unzip.fst.unzip.fst.reverse ++
          argTrips.unzip.fst.unzip.fst.reverse ++
            s0.genState.generated := by
    rw [Hgenolds, Hgenouts, Hgenargs]
    simp [List.append_assoc]
  have HndOld : s_old.generated.Nodup := Hwfgenolds.right.right
  rw [HgenApp] at HndOld
  have Hnd := nodup_reverse HndOld
  simp only [List.reverse_append, List.reverse_reverse,
             ← List.append_assoc] at Hnd
  exact Hnd

/-- Prelude bundle for `HoldEval_bridge_at_σO` call sites.

    Both arms of `_terminal`'s call branch derive the same three facts:
    the per-output `Hwf2.2`-bridge, `σAO`-reads-outputs, and the
    `oldVars ⊆ outputs.keys` subset fact. (Membership in `lhs` /
    `CallArg.getLhs args` is recovered locally via `hCallArgsLhs` and
    `List.mem_filter`.) -/
private theorem holdEval_bridge_prelude
    {σ₀ σ σA σAO σO : CoreStore}
    {proc proc' : Procedure} {args : List (CallArg Expression)}
    {oVals : List Expression.Expr}
    (Hwf2 : WellFormedCoreEvalTwoState δ σ₀ σ)
    (Hhav1 : HavocVars σAO (ListMap.keys proc.header.outputs) σO)
    (Hinitout :
      InitStates σA (ListMap.keys proc.header.outputs) oVals σAO)
    (HprocEq : proc' = proc) :
    (∀ v ∈ proc.header.outputs.keys,
       δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name) none) = σAO v) ∧
    ReadValues σAO proc.header.outputs.keys oVals ∧
    (∀ v ∈ callElim_oldVars proc' args,
       v ∈ ListMap.keys proc.header.outputs) := by
  refine ⟨?_, InitStatesReadValues Hinitout, ?_⟩
  · intro v Hv
    simp only [WellFormedCoreEvalTwoState] at Hwf2
    have HH := Hwf2.2 proc.header.outputs.keys [] σAO σO σO
                ⟨Hhav1, InitVars.init_none⟩ v
    exact HH.1 Hv
  · intro v Hv
    have Hv_filt := List.mem_filter.mp Hv
    have Hbool := Hv_filt.2
    simp only [Bool.and_eq_true] at Hbool
    have HinOuts' : (ListMap.keys proc'.header.outputs).contains v := Hbool.1.2
    rw [HprocEq] at HinOuts'
    exact List.contains_iff_mem.mp HinOuts'

/-- Per-index δ-eval bridge for `mkOld`-prefixed old-variable fvars at the
    post-havoc store `σO`.

    For each `i < oldVars.length`, the evaluator at `σO` of the old-name
    fvar `mkOld oldVars[i].name` returns the pre-call value `oldVals[i]`.
    Backs the L6 `HoldSubBridge` derivation in `_terminal`'s call arm.

    Inputs:
    * `Hwf2_univ`: per-output bridge `δ σO (mkOld v.name) = σAO v` (derived
      from `Hwf2.2` instantiated at `(outputs.keys, [], σAO, σO, σO)` with
      `Hhav1 ∧ InitVars.init_none`).
    * `Hinitout`: positional init witness for outputs at `σA → σAO`.
    * `HσAO_reads_outs`: `ReadValues σAO outputs.keys oVals` (just
      `InitStatesReadValues Hinitout`).
    * `Hevalouts`, `hCallArgsLhs`: caller-side lhs read + the callArgs
      shape equality.
    * `HoutAlign`: positional alignment from `WFCallSiteSpec` (lhs idx
      agrees with outputs.keys idx for shared inout outputs).
    * `HoldVars_sub_outs`, `HoldVars_sub_lhs`: `oldVars` is the filter
      that narrows `lhs` ↪ `oldVars`, so each element is in
      `outputs.keys` and `lhs` (membership in `CallArg.getLhs args`
      follows from `hCallArgsLhs`).
    * `HoldVals`: `ReadValues σ oldVars oldVals`.
    * `HoldValsLen`: `oldVals.length = oldVars.length`. -/
private theorem HoldEval_bridge_at_σO
    {σ σAO σO : CoreStore}
    {oldVars lhs : List Expression.Ident} {oldVals oVals : List Expression.Expr}
    {proc : Procedure} {args : List (CallArg Expression)}
    {σA : CoreStore}
    (Hwf2_univ :
      ∀ v ∈ proc.header.outputs.keys,
        δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name) none) = σAO v)
    (Hinitout :
      InitStates σA (ListMap.keys proc.header.outputs) oVals σAO)
    (HσAO_reads_outs : ReadValues σAO proc.header.outputs.keys oVals)
    (Hevalouts : ReadValues σ lhs oVals)
    (hCallArgsLhs : CallArg.getLhs args = lhs)
    (HoutAlign :
      ∀ v ∈ ListMap.keys proc.header.outputs,
        v ∈ CallArg.getLhs args →
        (CallArg.getLhs args).idxOf v =
          (ListMap.keys proc.header.outputs).idxOf v)
    (HoldVars_sub_outs : ∀ v ∈ oldVars, v ∈ proc.header.outputs.keys)
    (HoldVars_sub_lhs : ∀ v ∈ oldVars, v ∈ lhs)
    (HoldVals : ReadValues σ oldVars oldVals)
    (HoldValsLen : oldVals.length = oldVars.length) :
    ∀ (i : Nat) (Hi : i < oldVars.length),
      δ σO
          (Lambda.LExpr.fvar ()
            (CoreIdent.mkOld (oldVars[i]'Hi).name) none) =
        some (oldVals[i]'(HoldValsLen.symm ▸ Hi)) := by
  intro i Hi
  let v : Expression.Ident := oldVars[i]'Hi
  have Hv_mem : v ∈ oldVars := List.getElem_mem _
  have Hv_out : v ∈ ListMap.keys proc.header.outputs :=
    HoldVars_sub_outs v Hv_mem
  have Hv_lhs : v ∈ lhs := HoldVars_sub_lhs v Hv_mem
  have Hv_callLhs : v ∈ CallArg.getLhs args := hCallArgsLhs ▸ Hv_lhs
  -- ReadValues σ' ks vs ∧ v ∈ ks ⇒ σ' v = some vs[ks.idxOf v].
  have read_at : ∀ {σ' : Expression.Ident → Option _}
      {ks : List Expression.Ident} {vs : List _}
      (_ : ReadValues σ' ks vs) (Hmem : v ∈ ks)
      (Hidx_lt : ks.idxOf v < vs.length),
      σ' v = some (vs[ks.idxOf v]'Hidx_lt) := by
    intro σ' ks vs Hrv Hmem Hidx_lt
    have Hg := readValues_get (σ:=σ') (ks:=ks) (vs:=vs) Hrv
      (i:=ks.idxOf v)
      (hi:=List.idxOf_lt_length_of_mem Hmem) (hi':=Hidx_lt)
    have Hk : ks[ks.idxOf v]'(List.idxOf_lt_length_of_mem Hmem) = v := by
      unfold List.idxOf
      simpa using @List.findIdx_getElem _ (· == v) ks
        (List.idxOf_lt_length_of_mem Hmem)
    rwa [Hk] at Hg
  -- Step 1: δ σO (mkOld v.name) = σAO v.
  have HStep1 :
      δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name) none) = σAO v :=
    Hwf2_univ v Hv_out
  -- Step 2: σAO v = oVals[outputs.keys.idxOf v] via HσAO_reads_outs.
  let j_out := (ListMap.keys proc.header.outputs).idxOf v
  have Hj_out_lt_oVals : j_out < oVals.length := by
    exact (InitStatesLength Hinitout).symm ▸ List.idxOf_lt_length_of_mem Hv_out
  have HStep2 : σAO v = some (oVals[j_out]'Hj_out_lt_oVals) :=
    read_at HσAO_reads_outs Hv_out Hj_out_lt_oVals
  -- Step 3: lhs.idxOf v = outputs.keys.idxOf v (alignment).
  have HAlign_lhs : lhs.idxOf v = j_out := by
    show lhs.idxOf v = (ListMap.keys proc.header.outputs).idxOf v
    rw [← HoutAlign v Hv_out Hv_callLhs, hCallArgsLhs]
  -- Step 4: σ v = oVals[lhs.idxOf v]'_.
  let j_lhs := lhs.idxOf v
  have Hj_lhs_lt_oVals : j_lhs < oVals.length := by
    exact (ReadValuesLength Hevalouts).symm ▸ List.idxOf_lt_length_of_mem Hv_lhs
  have HStep4 : σ v = some (oVals[j_lhs]'Hj_lhs_lt_oVals) :=
    read_at Hevalouts Hv_lhs Hj_lhs_lt_oVals
  -- Step 5: σ v = some oldVals[i]'_ (HoldVals positional).
  have Hi_oldVals : i < oldVals.length := HoldValsLen.symm ▸ Hi
  have HStep5 : σ v = some (oldVals[i]'Hi_oldVals) :=
    readValues_get (σ:=σ) (ks:=oldVars) (vs:=oldVals) HoldVals
      (i:=i) (hi:=Hi) (hi':=Hi_oldVals)
  -- Combine: δ σO (mkOld v.name) = some oldVals[i].
  show δ σO (Lambda.LExpr.fvar () (CoreIdent.mkOld v.name) none)
        = some (oldVals[i]'Hi_oldVals)
  rw [HStep1, HStep2]
  have Hj_eq : oVals[j_out]'Hj_out_lt_oVals =
               oVals[j_lhs]'Hj_lhs_lt_oVals := by
    congr 1; exact HAlign_lhs.symm
  rw [Hj_eq, ← HStep4, HStep5]

/-- Per-fvar bridge for `createOldVarsSubst`'s codomain at the L6
    intermediate stores `σ_R1`/`σO`.

    For any `(k, w) ∈ createOldVarsSubst oldTripsCanonical`, the evaluator
    at `σ_R1` of `w` (a fresh-old `createFvar gen`) coincides with the
    evaluator at `σO` of the fvar `k = mkOld oldVars[i].name`, because
    both reduce to `some oldVals[i]` for the same positional `i`.

    Backs the L6 `Hsub` derivation: combines this with `HinputSubBridge`
    (input-side codomain) to discharge `subst_fvars_eval_bridge`'s
    sub-evaluator hypothesis on `oldSubst_L6 = createOldVarsSubst ++
    inputOnlyOldSubst`.

    Inputs:
    * `oldTripsCanonical`: the canonical trip-list aligning `genOldIdents`,
      `oldTys`, `oldVars`, and the `mkOld` keys.
    * `HgenOldLen`, `HoldTysLen`, `HoldValsLen`: positional length facts.
    * `σ_R1_read_olds`: positional reads `σ_R1 genOldIdents[i] = some oldVals[i]`.
    * `HoldEval_bridge`: positional bridge from Stage 1's helper. -/
private theorem HoldSubBridge_at_σO
    {σ_R1 σO : CoreStore}
    {oldVars genOldIdents : List Expression.Ident}
    {oldTys : List Expression.Ty}
    {oldVals : List Expression.Expr}
    (Hwfvars : Imperative.WellFormedSemanticEvalVar δ)
    (HgenOldLen : genOldIdents.length = oldVars.length)
    (HoldTysLen : oldTys.length = oldVars.length)
    (HoldValsLen : oldVals.length = oldVars.length)
    (σ_R1_read_olds :
      ∀ (i : Nat) (Hi : i < genOldIdents.length)
        (Hi' : i < oldVals.length),
        σ_R1 (genOldIdents[i]'Hi) = some (oldVals[i]'Hi'))
    (HoldEval_bridge :
      ∀ (i : Nat) (Hi : i < oldVars.length),
        δ σO
            (Lambda.LExpr.fvar ()
              (CoreIdent.mkOld (oldVars[i]'Hi).name) none) =
          some (oldVals[i]'(HoldValsLen.symm ▸ Hi))) :
    ∀ k w,
      Map.find?
        (Core.Transform.createOldVarsSubst
          ((((genOldIdents.zip oldTys).zip oldVars).zip
            (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG))) k = some w →
      δ σ_R1 w =
        δ σO (Lambda.LExpr.fvar () k none) := by
  -- Generic δ-fvar lookup derived from Hwfvars.
  have δ_fvar_eq := delta_fvar_eq_of_wfvars Hwfvars (delta := δ)
  intro k w Hf
  obtain ⟨ni_val, Hni_lt, Hk_eqMkOld, Hw_eq⟩ :=
    createOldVarsSubst_pos_decomp HgenOldLen HoldTysLen Hf
  have Hni_lt_genOld : ni_val < genOldIdents.length := HgenOldLen.symm ▸ Hni_lt
  have Hni_lt_oldVals : ni_val < oldVals.length := HoldValsLen.symm ▸ Hni_lt
  have HrdR1_get :
      σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) =
        some (oldVals[ni_val]'Hni_lt_oldVals) :=
    σ_R1_read_olds ni_val Hni_lt_genOld Hni_lt_oldVals
  have HwfL :
      δ σ_R1 (Core.Transform.createFvar
               (genOldIdents[ni_val]'Hni_lt_genOld)) =
        σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) :=
    δ_fvar_eq σ_R1 _
  have HoldEv :
      δ σO (Lambda.LExpr.fvar ()
              (CoreIdent.mkOld
                (oldVars[ni_val]'Hni_lt).name)
              none) =
        some (oldVals[ni_val]'Hni_lt_oldVals) :=
    HoldEval_bridge ni_val Hni_lt
  rw [Hw_eq, HwfL, HrdR1_get, Hk_eqMkOld, HoldEv]

/-- Class-(b1) decomposition for `Hinv`/`Hpred_disj` derivations: when
    `oldSubst_L6 = createOldVarsSubst oldTripsCanonical_L6 ++
    callElim_inputOnlyOldSubst proc' args` and a variable hits a key in
    the `createOldVarsSubst` segment, the codomain entry is a fresh-old
    `createFvar gen` and the variable equals that fresh ident.

    Used by L6's `Hinv` and `Hpred_disj` to walk the substitution split:
    when a `find?` lookup in `oldSubst_L6` lands in the old-trip side,
    the witness `var ∈ getVars w` collapses (since `w` is a single fvar)
    and forces `var = genOldIdents[i]` for the same positional `i`. -/
private theorem b1_var_witness_at_oldSubst
    {oldVars genOldIdents : List Expression.Ident}
    {oldTys : List Expression.Ty}
    {proc' : Procedure} {args : List (CallArg Expression)}
    (HgenOldLen : genOldIdents.length = oldVars.length)
    (HoldTysLen : oldTys.length = oldVars.length) :
    ∀ {var : Expression.Ident}
      {k : Expression.Ident} {w w' : Expression.Expr}
      (_hfind : Map.find?
        (Core.Transform.createOldVarsSubst
          ((((genOldIdents.zip oldTys).zip oldVars).zip
            (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG))) k = some w')
      (_Hf : Map.find?
        (Core.Transform.createOldVarsSubst
          ((((genOldIdents.zip oldTys).zip oldVars).zip
            (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)) ++
          callElim_inputOnlyOldSubst proc' args) k = some w)
      (_Hv_in : var ∈ Imperative.HasVarsPure.getVars (P:=Expression) w),
    ∃ (ni : Nat) (Hni : ni < genOldIdents.length),
      var = genOldIdents[ni]'Hni := by
  intro var k w w' hfind Hf Hv_in
  have Hw'w : w' = w := find?_append_some_eq hfind Hf
  obtain ⟨ni_val, Hni_lt, _Hk_eqMkOld, Hw'_eq⟩ :=
    createOldVarsSubst_pos_decomp HgenOldLen HoldTysLen hfind
  have Hni_lt_genOld : ni_val < genOldIdents.length := HgenOldLen.symm ▸ Hni_lt
  have Hw_eq : w =
      Core.Transform.createFvar
        (genOldIdents[ni_val]'Hni_lt_genOld) := by
    rw [← Hw'w]; exact Hw'_eq
  refine ⟨ni_val, Hni_lt_genOld, ?_⟩
  rw [Hw_eq] at Hv_in
  have Hv_in' :
      var ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              (Core.Transform.createFvar
                (genOldIdents[ni_val]'Hni_lt_genOld)) := Hv_in
  show var = _
  simp [Core.Transform.createFvar,
        Imperative.HasVarsPure.getVars,
        Lambda.LExpr.LExpr.getVars] at Hv_in'
  exact Hv_in'

/-- Class-(b2) decomposition for `Hinv`/`Hpred_disj`: when the lookup
    misses `createOldVarsSubst` and hits `callElim_inputOnlyOldSubst`,
    the codomain entry is a positional `inArgs` element and the variable
    appears in the flatMap of `inArgs`'s free vars.

    Companion to `b1_var_witness_at_oldSubst`. -/
private theorem b2_var_witness_at_oldSubst
    {oldVars genOldIdents : List Expression.Ident}
    {oldTys : List Expression.Ty}
    {proc' : Procedure} {args : List (CallArg Expression)}
    {inArgs : List Expression.Expr}
    (hCallArgsIn : CallArg.getInputExprs args = inArgs) :
    ∀ {var : Expression.Ident}
      {k : Expression.Ident} {w : Expression.Expr}
      (_hfind_none : Map.find?
        (Core.Transform.createOldVarsSubst
          ((((genOldIdents.zip oldTys).zip oldVars).zip
            (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG))) k = none)
      (_Hf : Map.find?
        (Core.Transform.createOldVarsSubst
          ((((genOldIdents.zip oldTys).zip oldVars).zip
            (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
            fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)) ++
          callElim_inputOnlyOldSubst proc' args) k = some w)
      (_Hv_in : var ∈ Imperative.HasVarsPure.getVars (P:=Expression) w),
      w ∈ CallArg.getInputExprs args ∧
      var ∈ List.flatMap
              (Imperative.HasVarsPure.getVars (P:=Expression))
              inArgs := by
  intro var k w hfind_none Hf Hv_in
  obtain ⟨ni2_val, _Hni2_lt_inKeys, Hni2_lt_inArgs,
          _Hk_eq_proc', Hw_eq_proc', _Hin_notin_outs⟩ :=
    inputOnlyOldSubst_pos_decomp
      (find?_append_none_elim hfind_none Hf)
  have HargExpr_def :
      w = (CallArg.getInputExprs args)[ni2_val]'Hni2_lt_inArgs :=
    Hw_eq_proc'
  have Hni2_lt_inArgsCall :
      ni2_val < inArgs.length := by
    have : (CallArg.getInputExprs args).length =
        inArgs.length := by rw [hCallArgsIn]
    exact this.symm ▸ Hni2_lt_inArgs
  have HargExpr_eq_inArgs :
      w = inArgs[ni2_val]'Hni2_lt_inArgsCall := by
    rw [HargExpr_def]
    show (CallArg.getInputExprs args)[ni2_val]'Hni2_lt_inArgs =
          inArgs[ni2_val]'Hni2_lt_inArgsCall
    congr 1 <;> exact hCallArgsIn
  have Hk1_in_inArgs : w ∈ inArgs := by
    rw [HargExpr_eq_inArgs]; exact List.getElem_mem _
  have HargExpr_in : w ∈ CallArg.getInputExprs args := by
    rw [HargExpr_def]; exact List.getElem_mem _
  have Hk1_flat :
      var ∈ List.flatMap
            (Imperative.HasVarsPure.getVars (P:=Expression))
            inArgs := by
    rw [List.mem_flatMap]
    exact ⟨w, Hk1_in_inArgs, Hv_in⟩
  exact ⟨HargExpr_in, Hk1_flat⟩

/-- Per-fvar bridge for `callElim_inputOnlyOldSubst`'s codomain at the L6
    intermediate stores `σ_R1`/`σO`.

    For any `(k, w) ∈ callElim_inputOnlyOldSubst proc' args`, the evaluator
    at `σ_R1` of `w` (a positional `inArgs` element) coincides with the
    evaluator at `σO` of the fvar `k = mkOld inputId.name`, because both
    reduce to `some argVals[ni]` for the same positional `ni`.

    Mirror of `HoldSubBridge_at_σO` for the input-only old substitution
    map; backs the L6 `Hsub` derivation in both the success and failure
    arms of `callElimStatementCorrect`'s call-statement case. -/
private theorem HinputSubBridge_at_σO
    {σ σ_R1 σO σAO σA σ₀ σ₂ : CoreStore}
    {γ : CoreTransformState}
    {genOldIdents : List Expression.Ident}
    {oldVals argVals : List Expression.Expr}
    {proc proc' : Procedure}
    {args : List (CallArg Expression)}
    {inArgs : List Expression.Expr}
    {oVals : List Expression.Expr}
    (Hwfvars : Imperative.WellFormedSemanticEvalVar (P:=Expression) δ)
    (Hwfval  : Imperative.WellFormedSemanticEvalVal (P:=Expression) δ)
    (Hwfc    : Core.WellFormedCoreEvalCong δ)
    (Hwf2    : WellFormedCoreEvalTwoState δ σ₀ σ₂)
    (HprocEq : proc' = proc)
    (Hiodisj :
      (proc.header.inputs.keys).Disjoint
        (proc.header.outputs.keys))
    (Hinitin :
      InitStates σ proc.header.inputs.keys argVals σA)
    (Hinitout :
      InitStates σA proc.header.outputs.keys oVals σAO)
    (Hhav1 : HavocVars σAO proc.header.outputs.keys σO)
    (HInitVars_empty : InitVars σO [] σO)
    (Hevalargs :
      EvalExpressions (P:=Expression) δ σ inArgs argVals)
    (hCallArgsIn : CallArg.getInputExprs args = inArgs)
    (HargIsDef :
      ∀ v ∈ List.flatMap
              (Imperative.HasVarsPure.getVars (P:=Expression))
              inArgs,
        (σ v).isSome)
    (HoldIdentsTemp :
      Forall (fun x => isOldTempIdent x) genOldIdents)
    (Hgenrel : CoreGenStateRel σ γ)
    (HargVarsNotInInKeys :
      ∀ argExpr ∈ CallArg.getInputExprs args,
      ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
        v ∉ proc.header.inputs.keys)
    (HargVarsNotInOutKeys :
      ∀ argExpr ∈ CallArg.getInputExprs args,
      ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
        v ∉ proc.header.outputs.keys)
    (Hσ_R1_eq :
      σ_R1 = updatedStates σO genOldIdents oldVals) :
    ∀ k w,
      Map.find?
        (callElim_inputOnlyOldSubst proc' args) k = some w →
      δ σ_R1 w =
        δ σO (Lambda.LExpr.fvar () k none) := by
  -- Generic δ-fvar lookup derived from Hwfvars.
  have δ_fvar_eq := delta_fvar_eq_of_wfvars Hwfvars (delta := δ)
  intro k w Hf
  obtain ⟨ni_val, Hni_lt_inKeys, Hni_lt_inArgs,
          Hk_eq_proc', Hw_eq_proc', _Hin_notin_outs_proc'⟩ :=
    inputOnlyOldSubst_pos_decomp Hf
  have Hni_lt_inKeys' :
      ni_val < proc.header.inputs.keys.length := by
    have HEqLen : proc'.header.inputs.keys.length =
        proc.header.inputs.keys.length := by rw [HprocEq]
    omega
  have HpinKeys :
      proc'.header.inputs.keys[ni_val]'Hni_lt_inKeys =
        proc.header.inputs.keys[ni_val]'Hni_lt_inKeys' := by
    subst HprocEq; rfl
  let inputId : Expression.Ident :=
    proc.header.inputs.keys[ni_val]'Hni_lt_inKeys'
  have HinputId_in : inputId ∈ proc.header.inputs.keys :=
    List.getElem_mem _
  have HinputId_notin_outs :
      inputId ∉ proc.header.outputs.keys :=
    fun h => Hiodisj HinputId_in h
  let argExpr : Expression.Expr :=
    (CallArg.getInputExprs args)[ni_val]'Hni_lt_inArgs
  have HargExpr_in : argExpr ∈ CallArg.getInputExprs args :=
    List.getElem_mem _
  have Hk_mkOld : k = CoreIdent.mkOld inputId.name := by
    rw [Hk_eq_proc', HpinKeys]
  have Hw_argExpr : w = argExpr := Hw_eq_proc'
  let ni : Fin (CallArg.getInputExprs args).length :=
    ⟨ni_val, Hni_lt_inArgs⟩
  have Hni_lt_inArgsCall : ni.val < inArgs.length := by
    have : (CallArg.getInputExprs args).length =
        inArgs.length := by rw [hCallArgsIn]
    rw [← this]
    exact Hni_lt_inArgs
  have HargExpr_eq_inArgs :
      argExpr = inArgs[ni.val]'Hni_lt_inArgsCall := by
    show (CallArg.getInputExprs args)[ni.val]'Hni_lt_inArgs =
          inArgs[ni.val]'Hni_lt_inArgsCall
    congr 1 <;> exact hCallArgsIn
  have HinKeys_argVals_len :
      proc.header.inputs.keys.length = argVals.length :=
    InitStatesLength Hinitin
  have Hni_lt_argVals : ni.val < argVals.length := by
    exact HinKeys_argVals_len.symm ▸ Hni_lt_inKeys'
  have σO_eq_σAO_off_outs :
      ∀ {v}, v ∉ proc.header.outputs.keys → σO v = σAO v := by
    obtain ⟨_ovh, Hup_havoc⟩ := HavocVarsUpdateStates Hhav1
    intro v Hv
    rw [UpdateStatesUpdated Hup_havoc, updatedStates_get_notin Hv]
  have HRHS_oldEqArgVal :
      δ σO (Lambda.LExpr.fvar ()
              (CoreIdent.mkOld inputId.name) none) =
        some (argVals[ni.val]'Hni_lt_argVals) := by
    simp only [WellFormedCoreEvalTwoState] at Hwf2
    rw [(Hwf2.2 proc.header.outputs.keys [] σAO σO σO
          ⟨Hhav1, HInitVars_empty⟩ inputId).2 HinputId_notin_outs,
        σO_eq_σAO_off_outs HinputId_notin_outs,
        initStates_get_notin Hinitout HinputId_notin_outs]
    exact readValues_get (InitStatesReadValues Hinitin)
      (i:=ni.val) (hi:=Hni_lt_inKeys') (hi':=Hni_lt_argVals)
  have HRHS_StepE :
      δ σ argExpr =
        some (argVals[ni.val]'Hni_lt_argVals) := by
    have Hev := evalExpressions_get Hevalargs
                  Hni_lt_inArgsCall Hni_lt_argVals
    have HargList :
        List.get inArgs ⟨ni.val, Hni_lt_inArgsCall⟩ =
          inArgs[ni.val]'Hni_lt_inArgsCall := rfl
    have HvalList :
        List.get argVals ⟨ni.val, Hni_lt_argVals⟩ =
          argVals[ni.val]'Hni_lt_argVals := rfl
    rw [HargList, HvalList] at Hev
    exact HargExpr_eq_inArgs ▸ Hev
  have HargExpr_in_argList : argExpr ∈ inArgs := by
    exact HargExpr_eq_inArgs ▸ List.getElem_mem _
  have HargExpr_in_callList :
      argExpr ∈ CallArg.getInputExprs args := HargExpr_in
  have Hσ_R1_eq_σ_argVars :
      ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
              argExpr,
        σ_R1 v = σ v := by
    intro v Hv
    have Hσv_some : (σ v).isSome := HargIsDef v <|
      List.mem_flatMap.mpr ⟨argExpr, HargExpr_in_argList, Hv⟩
    have HvNotGen : v ∉ genOldIdents :=
      notMem_of_Forall_neg HoldIdentsTemp fun Hold =>
        σ_some_contradiction Hσv_some
          (Option.isNone_iff_eq_none.mp (Hgenrel.oldFresh v Hold))
    rw [Hσ_R1_eq]
    exact σR1_eq_σ_for_notTouched Hinitin Hinitout Hhav1
      (HargVarsNotInInKeys argExpr HargExpr_in_callList v Hv)
      (HargVarsNotInOutKeys argExpr HargExpr_in_callList v Hv)
      HvNotGen
  have Hδ_R1_eq_δ_σ :
      δ σ_R1 argExpr = δ σ argExpr := by
    have Hsurv :
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                argExpr,
          Map.find? (∅ : Map Expression.Ident
                        Expression.Expr) v = none →
          δ σ_R1 (Lambda.LExpr.fvar () v none) =
            δ σ (Lambda.LExpr.fvar () v none) := by
      intro v Hv _
      rw [δ_fvar_eq σ_R1 v, δ_fvar_eq σ v]
      exact Hσ_R1_eq_σ_argVars v Hv
    have Hsub :
        ∀ k' w', k' ∈ Imperative.HasVarsPure.getVars
                        (P:=Expression) argExpr →
          Map.find? (∅ : Map Expression.Ident
                        Expression.Expr) k' = some w' →
          δ σ_R1 w' =
            δ σ (Lambda.LExpr.fvar () k' none) := by
      intro k' w' _ Hf
      simp [Map.find?] at Hf
    have Hbridge :
        δ σ_R1 (Lambda.LExpr.substFvars argExpr
                  (∅ : Map Expression.Ident
                        Expression.Expr)) =
          δ σ argExpr :=
      subst_fvars_eval_bridge Hwfc Hwfvars Hwfval
        (sm:=∅)
        Hsurv Hsub
    have HsubstEmpty :
        Lambda.LExpr.substFvars argExpr
            (∅ : Map Expression.Ident Expression.Expr) =
          argExpr := by
      induction argExpr with
      | fvar m name ty =>
        rw [Lambda.LExpr.substFvars_fvar_none m name ty]; rfl
      | _ => simp [Lambda.LExpr.substFvars_abs,
          Lambda.LExpr.substFvars_quant,
          Lambda.LExpr.substFvars_app,
          Lambda.LExpr.substFvars_eq,
          Lambda.LExpr.substFvars_ite, *]
    rwa [HsubstEmpty] at Hbridge
  rw [Hw_argExpr, Hδ_R1_eq_δ_σ, HRHS_StepE,
      ← HRHS_oldEqArgVal, ← Hk_mkOld]

/-- Call-arm failure-flag branch of `callElimStatementCorrect_terminal`.

    Discharges the `f = true` (precondition-failure) case after the call_sem
    destructure: builds the failing assert chain via `H_asserts_zip_fail`,
    havocs via `H_havocs_poly`, assumes via `H_assumes_zip_poly`, and glues
    via `EvalCallElim_glue_fail`.  The bool-totality witness for the failing
    precondition is extracted from `WFCallSiteProp.preBoolTyped` (boolTyped
    clause on `WFPrePostProp`) combined with `Hpre_iff.mpr`'s contrapositive.

    All inputs after `Hwfcallsite` are the destructured outputs from
    `cases Hcc with | call_sem ...` at `failed = true`. -/
private theorem callElimStatementCorrect_terminal_call_arm_fail
    [LawfulBEq Expression.Expr]
    {σ σ' : CoreStore}
    {p : Program}
    {γ s_ce : CoreTransformState}
    {procName : String}
    {args : List (CallArg Expression)}
    {md : Imperative.MetaData Expression}
    {s' : List Statement}
    {lhs : List Expression.Ident}
    {σ₀ σA σAO σO : CoreStore}
    {inArgs : List Expression.Expr}
    {oVals argVals modvals : List Expression.Expr}
    {proc : Procedure}
    (Hp : ∀ pname, π pname = Program.Procedure.find? p ⟨pname, ()⟩)
    (Hwfc : WellFormedCoreEvalCong δ)
    (Hwf : WF.WFStatementsProp p [.cmd (CmdExt.call procName args md)])
    (Hgenrel : CoreGenStateRel σ γ)
    (Hwfcallsite : WFCallSiteProp p π (.cmd (CmdExt.call procName args md)))
    (heq_ce :
      CallElim.callElimCmd (CmdExt.call procName args md)
          { γ with currentProgram := some p } =
        (Except.ok (some s'), s_ce))
    (lkup : π procName = .some proc)
    (hCallArgsIn : CallArg.getInputExprs args = inArgs)
    (hCallArgsLhs : CallArg.getLhs args = lhs)
    (Hevalargs : EvalExpressions (P:=Expression) δ σ inArgs argVals)
    (Hevalouts : ReadValues σ lhs oVals)
    (Hwfval : Imperative.WellFormedSemanticEvalVal δ)
    (Hwfvars : Imperative.WellFormedSemanticEvalVar δ)
    (Hwfb : Imperative.WellFormedSemanticEvalBool δ)
    (Hwf2 : WellFormedCoreEvalTwoState δ σ₀ σ)
    (Hinitin :
      InitStates σ (ListMap.keys proc.header.inputs) argVals σA)
    (Hinitout :
      InitStates σA (ListMap.keys proc.header.outputs) oVals σAO)
    (Hpre_def :
      ∀ pre, (Procedure.Spec.getCheckExprs proc.spec.checkedPreconditions).contains pre →
        Imperative.isDefinedOver (Imperative.HasVarsPure.getVars) σAO pre)
    (Hpre_iff :
      true = false ↔
      ∀ pre, (Procedure.Spec.getCheckExprs proc.spec.checkedPreconditions).contains pre →
        δ σAO pre = .some Imperative.HasBool.tt)
    (Hhav1 :
      HavocVars σAO (ListMap.keys proc.header.outputs) σO)
    (Hpost :
      ∀ post, (Procedure.Spec.getCheckExprs proc.spec.postconditions).contains post →
        Imperative.isDefinedOver (Imperative.HasVarsPure.getVars) σAO post ∧
        δ σO post = .some Imperative.HasBool.tt)
    (Hrd :
      ReadValues σO (ListMap.keys proc.header.outputs) modvals)
    (Hupdate : UpdateStates σ lhs modvals σ') :
    ∃ σ'',
      Inits σ' σ'' ∧
      EvalStatementsContract π φ ⟨σ, δ, false⟩ s' ⟨σ'', δ, true⟩ := by
  -- B1-tail: destructure heq_ce via callElimCmd_call_eq.
  obtain ⟨proc', argTrips, outTrips, genOldIdents, oldTys,
          asserts, assumes,
          s_arg, s_out, s_old,
          Hfind, Heqarg, Heqout, Heqold, Holdtylen,
          Hsts_struct, HassertsShape, _HassumesShape⟩ :=
    callElimCmd_call_eq heq_ce
  have Heqargs : argTrips.unzip.snd =
      CallArg.getInputExprs args :=
    genArgExprIdentsTrip_snd Heqarg
  have Heqouts : outTrips.unzip.snd =
      CallArg.getLhs args :=
    genOutExprIdentsTrip_snd Heqout
  -- Hoisted: arg-expr vars defined in σ (via Hevalargs).
  have HargIsDef : Imperative.isDefined σ
      (List.flatMap
        (Imperative.HasVarsPure.getVars (P:=Expression))
        inArgs) :=
    evalExpressions_isDefined_flatMap Hevalargs
  -- Hoisted abbreviations for argument/output temp idents.
  let argTemps : List Expression.Ident :=
    argTrips.unzip.fst.unzip.fst
  let outTemps : List Expression.Ident :=
    outTrips.unzip.fst.unzip.fst
  -- C1: aux facts derived from the destructured binders.
  have HargTemp :
      Forall (fun x => isTempIdent x) argTemps :=
    genArgExprIdentsTrip_isTempIdent Heqarg
  have HoutTemp :
      Forall (fun x => isTempIdent x) outTemps :=
    genOutExprIdentsTrip_isTempIdent Heqout
  have HoldIdentsTemp :
      Forall (fun x => isOldTempIdent x) genOldIdents :=
    genOldExprIdents_isOldTempIdent Heqold
  have Hgennd' :
      (γ.genState.generated.reverse ++
        argTemps ++ outTemps ++ genOldIdents).Nodup := by
    apply genTrips_combined_nodup Heqarg Heqout Heqold
    exact Hgenrel.wfgen
  obtain ⟨Hgennd, HndefArg_σ, HndefOut_σ, HndefOld_σ, Hndefgen⟩ :=
    fresh_triple_σ_facts Hgenrel Hgennd' HargTemp HoutTemp
      HoldIdentsTemp Hupdate
  -- ── Length facts ──
  have Hargtriplen : argTrips.length = argVals.length := by
    rw [← List.unzip_snd_length argTrips, Heqargs, hCallArgsIn]
    exact EvalExpressionsLength Hevalargs
  have Houttriplen : outTrips.length = oVals.length := by
    rw [← List.unzip_snd_length outTrips, Heqouts, hCallArgsLhs]
    exact ReadValuesLength Hevalouts
  have HargTempsLen : argTemps.length = argVals.length := by
    simp [argTemps, List.unzip_eq_map, Hargtriplen]
  have HoutTempsLen : outTemps.length = oVals.length := by
    simp [outTemps, List.unzip_eq_map, Houttriplen]
  -- C1: Derive Hinoutnd from the call_sem InitStates binders.
  have Hinnd_io : (proc.header.inputs.keys).Nodup :=
    InitStatesNodup Hinitin
  have Houtnd_io : (proc.header.outputs.keys).Nodup :=
    InitStatesNodup Hinitout
  have Hindef_io :
      Imperative.isDefined σA (proc.header.inputs.keys) :=
    InitStatesDefined Hinitin
  have Houtndef_io :
      Imperative.isNotDefined σA (proc.header.outputs.keys) :=
    InitStatesNotDefined Hinitout
  have Hiodisj :
      (proc.header.inputs.keys).Disjoint
        (proc.header.outputs.keys) := by
    intro x Hin1 Hin2
    exact σ_some_contradiction
      (Hindef_io x Hin1) (Houtndef_io x Hin2)
  have Hinoutnd :
      (proc.header.inputs.keys ++
        proc.header.outputs.keys).Nodup := by
    rw [List.nodup_append]
    refine ⟨Hinnd_io, Houtnd_io, ?_⟩
    intro a Ha b Hb Heq
    subst Heq
    exact Hiodisj Ha Hb
  -- C2: bind `oldVars`.
  let oldVars : List Expression.Ident := callElim_oldVars proc' args
  have HrdOldDef : Imperative.isDefined σ oldVars := by
    intro g Hg
    have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
      (List.mem_filter.mp Hg).1
    have Hg_in_lhs : g ∈ lhs := hCallArgsLhs ▸ Hg_in_getLhs
    have Hlhs_def : Imperative.isDefined σ lhs :=
      ReadValuesIsDefined Hevalouts
    exact Hlhs_def g Hg_in_lhs
  obtain ⟨oldVals, HoldVals⟩ :=
    isDefinedReadValues HrdOldDef
  have HoldValsLen : oldVals.length = oldVars.length :=
    (ReadValuesLength HoldVals).symm
  have HgenOldLen : genOldIdents.length = oldVars.length :=
    genOldExprIdents_length Heqold
  have HoldTysLen : oldTys.length = oldVars.length := Holdtylen
  have HgenOldOldValsLen : genOldIdents.length = oldVals.length := by
    rw [HgenOldLen, ← HoldValsLen]
  -- C3: σ'' candidate.
  have Hinit :=
    updatedStatesInit (P := Expression) ?_ ?_ ?_ (σ := σ')
      (hs := argTemps
              ++ outTemps
              ++ genOldIdents)
      (vs := argVals ++ oVals ++ oldVals)
  rotate_left
  · simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
          Hargtriplen, Houttriplen, HgenOldOldValsLen]
  · exact Hndefgen
  · exact Hgennd
  refine ⟨updatedStates σ'
            (argTemps
              ++ outTemps
              ++ genOldIdents)
            (argVals ++ oVals ++ oldVals), ?_, ?_⟩
  · exact InitStatesInits Hinit
  · -- L1-L6 chain via EvalCallElim_glue_fail.
    obtain ⟨HargNd, HoutNd, HoldNd,
            HargOutDisj, HargOldDisj, HoutOldDisj⟩ :=
      List.nodup_3_decompose Hgennd
    -- argTemps fresh from σ; arg-expr vars defined in σ ⇒ disjoint.
    have HdefVars : Imperative.isDefined σ
        (List.flatMap
          (Imperative.HasVarsPure.getVars (P:=Expression))
          (CallArg.getInputExprs args)) :=
      hCallArgsIn ▸ HargIsDef
    have HargExprDisj :
        argTemps.Disjoint
          (List.flatMap
            (Imperative.HasVarsPure.getVars (P:=Expression))
            argTrips.unzip.snd) := by
      intro x Hin1 Hin2
      rw [Heqargs] at Hin2
      exact notin_of_isSome_isNotDefined (HdefVars x Hin2) HndefArg_σ Hin1
    -- ── L1: argInit ──
    have HevalArgs' :
        EvalExpressions (P:=Core.Expression) δ σ
          argTrips.unzip.snd argVals := by
      rw [Heqargs, hCallArgsIn]
      exact Hevalargs
    have HL1 :
        EvalStatementsContract π φ ⟨σ, δ, false⟩
          (Core.Transform.createInits argTrips md)
          ⟨updatedStates σ argTemps
            argVals, δ, false⟩ :=
      H_inits Hwfvars Hwfval Hwfc HargExprDisj HargNd
        HevalArgs' HndefArg_σ
    -- L2: outInit (lift Hevalouts to σ_arg via readValues_updatedStates).
    have Hlhs_isLocl :
        Imperative.isDefined σ lhs :=
      ReadValuesIsDefined Hevalouts
    have HlhsDisjArg : lhs.Disjoint argTemps := fun x Hin1 Hin2 =>
      notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefArg_σ Hin2
    have HlhsDisjOut : lhs.Disjoint outTemps := fun x Hin1 Hin2 =>
      notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefOut_σ Hin2
    have HlhsDisjOld : lhs.Disjoint genOldIdents := fun x Hin1 Hin2 =>
      notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefOld_σ Hin2
    have HoutSnd_eq_lhs : outTrips.unzip.snd = lhs := by
      rw [Heqouts, hCallArgsLhs]
    have HlhsNd : lhs.Nodup := callArgsLhs_nodup_of_wf Hwf hCallArgsLhs
    have Hout_nd_app :
        List.Nodup (outTemps
                    ++ outTrips.unzip.snd) := by
      rw [HoutSnd_eq_lhs]
      rw [List.nodup_append]
      refine ⟨HoutNd, HlhsNd, ?_⟩
      intro a Ha b Hb Heq
      subst Heq
      exact HlhsDisjOut Hb Ha
    have HrdOuts_argLayer :
        ReadValues
          (updatedStates σ argTemps
            argVals)
          outTrips.unzip.snd oVals := by
      exact HoutSnd_eq_lhs ▸ readValues_updatedStates HargTempsLen HlhsDisjArg Hevalouts
    have HndefOut_argLayer :
        Imperative.isNotDefined
          (updatedStates σ argTemps
            argVals)
          outTemps := by
      intro v Hv
      have Hv_notin : v ∉ argTemps := fun Hin => HargOutDisj Hin Hv
      exact (updatedStates_get_notin (σ:=σ) (ks:=argTemps) (vs:=argVals) Hv_notin) ▸ HndefOut_σ v Hv
    have HL2 :
        EvalStatementsContract π φ
          ⟨updatedStates σ argTemps
            argVals, δ, false⟩
          (Core.Transform.createInitVars outTrips md)
          ⟨updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals, δ, false⟩ :=
      H_initVars Hwfvars Hout_nd_app HrdOuts_argLayer
        HndefOut_argLayer
    -- L3: oldInit; oldTrips := (genOldIdents.zip oldTys).zip oldVars.
    let oldTrips :
        List ((Expression.Ident × Expression.Ty) ×
               Expression.Ident) :=
      (genOldIdents.zip oldTys).zip oldVars
    have HoldTripsFst :
        oldTrips.unzip.fst.unzip.fst = genOldIdents := by
      have HzipLen :
          (genOldIdents.zip oldTys).length = oldVars.length := by
        simp [List.length_zip, HgenOldLen, HoldTysLen]
      show ((genOldIdents.zip oldTys).zip oldVars).unzip.fst.unzip.fst
            = genOldIdents
      simp [List.unzip_eq_map, List.map_fst_zip, HzipLen,
            HgenOldLen, HoldTysLen]
    have HoldTripsSnd :
        oldTrips.unzip.snd = oldVars := by
      have HzipLen :
          (genOldIdents.zip oldTys).length = oldVars.length := by
        simp [List.length_zip, HgenOldLen, HoldTysLen]
      rw [show oldTrips = (genOldIdents.zip oldTys).zip oldVars
          from rfl]
      simp [List.unzip_eq_map, List.map_snd_zip, HzipLen]
    have HoldVars_sub_lhs : ∀ g ∈ oldVars, g ∈ lhs := by
      intro g Hg
      have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
        (List.mem_filter.mp Hg).1
      exact hCallArgsLhs ▸ Hg_in_getLhs
    have oldVars_disj_via_lhs :
        ∀ {ks : List Expression.Ident}, lhs.Disjoint ks → oldVars.Disjoint ks :=
      fun H x Hin1 Hin2 => H (HoldVars_sub_lhs x Hin1) Hin2
    have HoldVarsDisjArg : oldVars.Disjoint argTemps := oldVars_disj_via_lhs HlhsDisjArg
    have HoldVarsDisjOut : oldVars.Disjoint outTemps := oldVars_disj_via_lhs HlhsDisjOut
    have HoldVarsDisjOldT : oldVars.Disjoint genOldIdents := oldVars_disj_via_lhs HlhsDisjOld
    have HoldVarsNd : oldVars.Nodup := by
      have HlhsArgs_nd : (CallArg.getLhs args).Nodup := hCallArgsLhs ▸ HlhsNd
      exact List.Sublist.nodup List.filter_sublist HlhsArgs_nd
    have HrdOlds_outLayer :
        ReadValues
          (updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals)
          oldVars oldVals :=
      readValues_updatedStates HoutTempsLen HoldVarsDisjOut
        (readValues_updatedStates HargTempsLen HoldVarsDisjArg HoldVals)
    have HrdOldTrips :
        ReadValues
          (updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals)
          oldTrips.unzip.snd oldVals := by
      exact HoldTripsSnd ▸ HrdOlds_outLayer
    have HndefOld_outLayer :
        Imperative.isNotDefined
          (updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals)
          genOldIdents := by
      intro v Hv
      have Hv_notin_out : ¬ v ∈ outTemps := fun Hin => HoutOldDisj Hin Hv
      have Hv_notin_arg : ¬ v ∈ argTemps := fun Hin => HargOldDisj Hin Hv
      rw [updatedStates_2layer_get_notin
            Hv_notin_arg Hv_notin_out]
      exact HndefOld_σ v Hv
    have HndefOldTrips :
        Imperative.isNotDefined
          (updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals)
          oldTrips.unzip.fst.unzip.fst := by
      exact HoldTripsFst ▸ HndefOld_outLayer
    have HoldTrips_nd_app :
        List.Nodup
          (oldTrips.unzip.fst.unzip.fst ++ oldTrips.unzip.snd) := by
      rw [HoldTripsFst, HoldTripsSnd]
      rw [List.nodup_append]
      refine ⟨HoldNd, HoldVarsNd, ?_⟩
      intro a Ha b Hb Heq
      subst Heq
      exact HoldVarsDisjOldT Hb Ha
    have HL3 :
        EvalStatementsContract π φ
          ⟨updatedStates
            (updatedStates σ
              argTemps argVals)
            outTemps oVals, δ, false⟩
          (Core.Transform.createInitVars oldTrips md)
          ⟨updatedStates
            (updatedStates
              (updatedStates σ
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩ :=
      H_initVars Hwfvars HoldTrips_nd_app HrdOldTrips
        HndefOldTrips
    rw [Hsts_struct]
    -- L5 setup: build havocs from σ_old to σ_havoc, polymorphic-flag.
    have Hhav_old :
        HavocVars
          (updatedStates
            (updatedStates
              (updatedStates σ
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals)
          lhs
          (updatedStates
            (updatedStates
              (updatedStates σ'
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals) :=
      havocVars_3layer_lift HlhsDisjArg HlhsDisjOut
        (HoldTripsFst ▸ HlhsDisjOld) (UpdateStatesHavocVars Hupdate)
    have HlhsDef_old :
        Imperative.isDefined
          (updatedStates
            (updatedStates
              (updatedStates σ
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals) lhs :=
      isDefined_3layer_lift HlhsDisjArg HlhsDisjOut
        (HoldTripsFst ▸ HlhsDisjOld) Hlhs_isLocl
    -- HL5 (poly): havocs at flag=true.
    have HL5_pre :
        EvalStatementsContract π φ
          ⟨updatedStates
            (updatedStates
              (updatedStates σ
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals, δ, true⟩
          (Core.Transform.createHavocs lhs md)
          ⟨updatedStates
            (updatedStates
              (updatedStates σ'
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals, δ, true⟩ :=
      H_havocs_poly Hwfvars HlhsDef_old Hhav_old
    have HoldFstLen :
        oldTrips.unzip.fst.unzip.fst.length = oldVals.length := by
      rw [HoldTripsFst, HgenOldLen, HoldValsLen]
    have Hflatten_eq :
        updatedStates σ'
          (argTemps ++
            outTemps ++ genOldIdents)
          (argVals ++ oVals ++ oldVals) =
        updatedStates
          (updatedStates
            (updatedStates σ'
              argTemps argVals)
            outTemps oVals)
          oldTrips.unzip.fst.unzip.fst oldVals := by
      rw [HoldTripsFst]
      simp only [updatedStates]
      have Hzip1 :
          ((argTemps ++
            outTemps) ++ genOldIdents).zip
            ((argVals ++ oVals) ++ oldVals) =
          (argTemps ++
            outTemps).zip
            (argVals ++ oVals) ++
            genOldIdents.zip oldVals :=
        List.zip_append (by
          rw [List.length_append, List.length_append,
              HargTempsLen, HoutTempsLen])
      have Hzip2 :
          (argTemps ++
            outTemps).zip
            (argVals ++ oVals) =
          argTemps.zip argVals ++
            outTemps.zip oVals :=
        List.zip_append HargTempsLen
      rw [Hzip1, Hzip2]
      rw [updatedStates'App, updatedStates'App]
    have HL5 :
        EvalStatementsContract π φ
          ⟨updatedStates
            (updatedStates
              (updatedStates σ
                argTemps argVals)
              outTemps oVals)
            oldTrips.unzip.fst.unzip.fst oldVals, δ, true⟩
          (Core.Transform.createHavocs (CallArg.getLhs args) md)
          ⟨updatedStates σ'
            (argTemps ++
              outTemps ++ genOldIdents)
            (argVals ++ oVals ++ oldVals), δ, true⟩ := by
      rw [Hflatten_eq, hCallArgsLhs]
      exact HL5_pre
    -- ── D2a: per-precondition payload for L4 (asserts) ──
    obtain ⟨HprocEq, c_in_postExprs_of_proc'⟩ :=
      procEq_and_postExprs_bridge Hp Hfind lkup
    obtain ⟨HpreVarsFresh, _HpostVarsFresh, _HargVarsNotInLhs,
            HinoutFresh, HargVarsNotInOutKeys,
            HargVarsNotInInKeys, _HoutAlign, HpreBoolTyped⟩ :=
      Hwfcallsite.specialize (procName := procName)
        (args := args) (md := md) rfl lkup
    have HinputsFresh :
        ∀ v ∈ proc.header.inputs.keys,
          ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
      intro v Hv
      exact HinoutFresh v (List.mem_append.mpr (Or.inl Hv))
    have HoutputsFresh :
        ∀ v ∈ proc.header.outputs.keys,
          ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
      intro v Hv
      exact HinoutFresh v (List.mem_append.mpr (Or.inr Hv))
    have HinKeys_disj_argTemps : proc.header.inputs.keys.Disjoint argTemps :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HargTemp (HinputsFresh v Hv1).1 Hv2
    have HinKeys_disj_outTemps : proc.header.inputs.keys.Disjoint outTemps :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HoutTemp (HinputsFresh v Hv1).1 Hv2
    have HinKeys_disj_olds : proc.header.inputs.keys.Disjoint genOldIdents :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HoldIdentsTemp (HinputsFresh v Hv1).2 Hv2
    have HoutKeys_disj_argTemps : proc.header.outputs.keys.Disjoint argTemps :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HargTemp (HoutputsFresh v Hv1).1 Hv2
    have HoutKeys_disj_outTemps : proc.header.outputs.keys.Disjoint outTemps :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HoutTemp (HoutputsFresh v Hv1).1 Hv2
    have HoutKeys_disj_olds : proc.header.outputs.keys.Disjoint genOldIdents :=
      fun v Hv1 Hv2 => notMem_of_Forall_neg HoldIdentsTemp (HoutputsFresh v Hv1).2 Hv2
    have HinKeys_disj_lhs :
        proc.header.inputs.keys.Disjoint lhs := fun v Hv1 Hv2 =>
      notin_of_isSome_isNotDefined (Hlhs_isLocl v Hv2) (InitStatesNotDefined Hinitin) Hv1
    have HoutKeys_disj_lhs :
        proc.header.outputs.keys.Disjoint lhs := by
      intro v Hv1 Hv2
      have HvσA_none : σA v = none := Houtndef_io v Hv1
      have HvNotInInputs : v ∉ proc.header.inputs.keys :=
        fun h => Hiodisj h Hv1
      have HvσA_eq_σ : σA v = σ v :=
        initStates_get_notin Hinitin HvNotInInputs
      have Hvσ_none : σ v = none := by
        rw [← HvσA_eq_σ]; exact HvσA_none
      exact σ_some_contradiction (Hlhs_isLocl v Hv2) Hvσ_none
    -- Filtered preconditions.
    let presFiltered : List (CoreLabel × Procedure.Check) :=
      proc.spec.checkedPreconditions
    -- Pre-var freshness restricted to presFiltered (filtered ⊆ unfiltered).
    have HpresVarsFresh' :
        ∀ entry ∈ presFiltered,
          ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr,
            ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
            v ∉ CallArg.getLhs args := fun entry Hentry v Hv =>
      HpreVarsFresh entry.snd.expr
        (filterCheck_mem_getCheckExprs Hentry) v Hv
    -- L4 ks/ks' bindings.
    let ks_L4 : List Expression.Ident :=
      proc.header.inputs.keys ++ proc.header.outputs.keys
    let ks'_L4 : List Expression.Ident :=
      argTemps ++ lhs
    have HinKeys_argTemps_len :
        proc.header.inputs.keys.length = argTemps.length := by
      have H1 : proc.header.inputs.keys.length =
                  argVals.length := InitStatesLength Hinitin
      omega
    have HoutKeys_lhs_len :
        proc.header.outputs.keys.length = lhs.length := by
      have H1 : proc.header.outputs.keys.length = oVals.length :=
        InitStatesLength Hinitout
      have H2 : lhs.length = oVals.length :=
        ReadValuesLength Hevalouts
      omega
    have Hks_len_L4 :
        ks_L4.length = ks'_L4.length := by
      show (proc.header.inputs.keys ++
            proc.header.outputs.keys).length =
           (argTemps ++ lhs).length
      rw [List.length_append, List.length_append,
          HinKeys_argTemps_len, HoutKeys_lhs_len]
    have HargT_lhs_nd :
        (argTemps ++ lhs).Nodup := by
      rw [List.nodup_append]
      refine ⟨HargNd, HlhsNd, ?_⟩
      intro a Ha b Hb Heq
      subst Heq
      exact HlhsDisjArg Hb Ha
    have Hbignd_L4 :
        (ks_L4 ++ ks'_L4).Nodup := by
      rw [List.nodup_append]
      refine ⟨Hinoutnd, HargT_lhs_nd, fun a Ha b Hb Heq => ?_⟩
      subst Heq
      rcases List.mem_append.mp Ha with HaIn | HaOut <;>
        rcases List.mem_append.mp Hb with HbArg | HbLhs
      · exact HinKeys_disj_argTemps HaIn HbArg
      · exact HinKeys_disj_lhs HaIn HbLhs
      · exact HoutKeys_disj_argTemps HaOut HbArg
      · exact HoutKeys_disj_lhs HaOut HbLhs
    have Hnd_L4 : Imperative.substNodup
        (ks_L4.zip ks'_L4) := by
      unfold Imperative.substNodup
      exact (List.unzip_zip Hks_len_L4) ▸ Hbignd_L4
    have HσAO_def_in_L4 :
        Imperative.isDefined σAO proc.header.inputs.keys :=
      InitStatesDefMonotone (InitStatesDefined Hinitin) Hinitout
    have HσAO_def_out_L4 :
        Imperative.isDefined σAO proc.header.outputs.keys :=
      InitStatesDefined Hinitout
    let σ_old : CoreStore :=
      updatedStates
        (updatedStates
          (updatedStates σ
            argTemps argVals)
          outTemps oVals)
        oldTrips.unzip.fst.unzip.fst oldVals
    have Hσ_old_def_argT :
        Imperative.isDefined σ_old
          argTemps := by
      intro v Hv
      show ((updatedStates
              (updatedStates
                (updatedStates σ
                  argTemps argVals)
                outTemps oVals)
              oldTrips.unzip.fst.unzip.fst oldVals) v).isSome =
            true
      rw [updatedStates_get_notin (HoldTripsFst.symm ▸ HargOldDisj Hv),
          updatedStates_get_notin (HargOutDisj Hv)]
      exact updatedStatesDefined HargTempsLen v Hv
    have Hσ_old_def_lhs :
        Imperative.isDefined σ_old lhs := HlhsDef_old
    have Hdef_L4 : Imperative.substDefined σAO σ_old
        (ks_L4.zip ks'_L4) :=
      substDefined_of_app HσAO_def_in_L4 HσAO_def_out_L4
        Hσ_old_def_argT Hσ_old_def_lhs
    -- Build matching ReadValues on σ_old and σAO, close via ReadValuesSubstStores.
    have HrdAO_in_L4 :
        ReadValues σAO proc.header.inputs.keys argVals := by
      have HrdA_in : ReadValues σA proc.header.inputs.keys argVals :=
        InitStatesReadValues Hinitin
      apply InitStatesReadValuesMonotone HrdA_in Hinitout
    have HrdAO_out_L4 :
        ReadValues σAO proc.header.outputs.keys oVals :=
      InitStatesReadValues Hinitout
    have HrdAO_inout_L4 :
        ReadValues σAO
          (proc.header.inputs.keys ++
            proc.header.outputs.keys)
          (argVals ++ oVals) :=
      ReadValuesApp HrdAO_in_L4 HrdAO_out_L4
    have HrdLayer3_argT :
        ReadValues σ_old
          argTemps argVals :=
      readValues_updatedStates HoldFstLen
        (HoldTripsFst ▸ HargOldDisj)
        (readValues_updatedStates HoutTempsLen HargOutDisj
          (readValues_updatedStatesSame HargTempsLen
            (List.nodup_append.mp (List.nodup_append.mp Hgennd).1).1))
    have HrdLayer3_lhs :
        ReadValues σ_old lhs oVals :=
      readValues_3layer_lift HargTempsLen HlhsDisjArg
        HoutTempsLen HlhsDisjOut
        HoldFstLen (HoldTripsFst ▸ HlhsDisjOld) Hevalouts
    have HrdOld_inout_L4 :
        ReadValues σ_old
          (argTemps ++ lhs)
          (argVals ++ oVals) :=
      ReadValuesApp HrdLayer3_argT HrdLayer3_lhs
    have Hsubst_L4 : Imperative.substStores σ_old σAO
        (ks'_L4.zip ks_L4) :=
      ReadValuesSubstStores HrdOld_inout_L4 HrdAO_inout_L4
    -- Flip to the `(ks_L4.zip ks'_L4)` direction for subst_fvars_correct.
    have Hsubst_L4_flipped : Imperative.substStores σAO σ_old
        (ks_L4.zip ks'_L4) := by
      apply Imperative.substStoresFlip'
      simp [Imperative.substSwap, zip_swap]
      exact Hsubst_L4
    -- ── Apply H_asserts_zip_fail ──
    obtain ⟨assertLabels, HassertLabelsLen, HassertShape⟩ :=
      HassertsShape
    have HassertSubst_eq :
        ((proc.header.inputs.keys.zip
            (Core.Transform.createFvars
              argTemps)) ++
          (proc.header.outputs.keys.zip
            (Core.Transform.createFvars
              (CallArg.getLhs args)))) =
        ks_L4.zip
          (Core.Transform.createFvars ks'_L4) := by
      show _ =
        (proc.header.inputs.keys ++
          proc.header.outputs.keys).zip
        (Core.Transform.createFvars
          (argTemps ++ lhs))
      rw [hCallArgsLhs, createFvarsApp]
      rw [List.zip_append]
      rw [createFvarsLength]
      exact HinKeys_argTemps_len
    -- Per-pair "tt or ff" totality fact at σ_old via subst_fvars_correct + boolTyped.
    -- For each pair (entry, lbl) ∈ presFiltered.zip assertLabels,
    -- build the totality witness at σ_old.
    -- First derive HpresPayload-like facts (without the eval-tt — use boolTyped).
    -- Bool-totality witness at σAO for filtered preconditions.
    have HpreFilteredBool :
        ∀ entry ∈ presFiltered,
          δ σAO entry.snd.expr = some Imperative.HasBool.tt ∨
          δ σAO entry.snd.expr = some Imperative.HasBool.ff := by
      intro entry Hentry
      have Hcontains :
          (Procedure.Spec.getCheckExprs
            proc.spec.preconditions).contains entry.snd.expr := by
        rw [List.contains_iff_mem]
        simp only [Procedure.Spec.getCheckExprs,
                   ListMap.values_eq_map_snd, List.mem_map,
                   List.map_map]
        refine ⟨entry, ?_, rfl⟩
        exact (List.mem_filter.mp Hentry).1
      have Hpre_in :
          entry.snd.expr ∈ Procedure.Spec.getCheckExprs
                              proc.spec.preconditions :=
        List.contains_iff_mem.mp Hcontains
      -- Use HpreBoolTyped at (δ, σAO) with the definedness witness.
      have Hcontains_filt :
          (Procedure.Spec.getCheckExprs proc.spec.checkedPreconditions).contains entry.snd.expr := by
        rw [List.contains_iff_mem]
        simp only [Procedure.Spec.getCheckExprs,
                   ListMap.values_eq_map_snd, List.mem_map,
                   List.map_map]
        refine ⟨entry, Hentry, rfl⟩
      have HdefAO : Imperative.isDefinedOver
          (Imperative.HasVarsPure.getVars (P:=Expression))
          σAO entry.snd.expr :=
        Hpre_def entry.snd.expr Hcontains_filt
      exact HpreBoolTyped entry.snd.expr Hpre_in δ σAO HdefAO
    -- HpresPayload-like (defined and freshness/disjoint info), shared with success arm.
    -- We need:
    --   * For each entry ∈ presFiltered, the per-entry invStores σAO σ_old +
    --     ks'_L4.Disjoint (getVars entry.snd.expr) used by subst_fvars_correct.
    have HpresInfo :
        ∀ entry ∈ presFiltered,
          Imperative.invStores σAO σ_old
            ((Imperative.HasVarsPure.getVars (P:=Expression)
                entry.snd.expr).removeAll
              (ks_L4 ++ ks'_L4)) ∧
          ks'_L4.Disjoint
            (Imperative.HasVarsPure.getVars (P:=Expression)
              entry.snd.expr) := by
      intro entry Hentry
      have HfreshEnt := HpresVarsFresh' entry Hentry
      have Hpred_disj :
          ks'_L4.Disjoint
            (Imperative.HasVarsPure.getVars (P:=Expression)
              entry.snd.expr) := by
        intro x Hin1 Hin2
        cases List.mem_append.mp Hin1 with
        | inl HxArg =>
          have HxTemp : isTempIdent x := (List.Forall_mem_iff.mp HargTemp) x HxArg
          have HxNotTemp : ¬ isTempIdent x :=
            (HfreshEnt x Hin2).1
          exact HxNotTemp HxTemp
        | inr HxLhs =>
          have HxNotInLhs : x ∉ CallArg.getLhs args :=
            (HfreshEnt x Hin2).2.2
          rw [hCallArgsLhs] at HxNotInLhs
          exact HxNotInLhs HxLhs
      have Hinv :
          Imperative.invStores σAO σ_old
            ((Imperative.HasVarsPure.getVars (P:=Expression)
                entry.snd.expr).removeAll
              (ks_L4 ++ ks'_L4)) := by
        simp only [Imperative.invStores, Imperative.substStores]
        intros k1 k2 Hkin
        obtain ⟨rfl, Hk1_pre, Hk1_notin_inputs, Hk1_notin_outputs,
                Hk1_notin_argT, _Hk1_notin_lhs⟩ :=
          zip_removeAll4_decompose Hkin
        have HfreshK := HfreshEnt k1 Hk1_pre
        have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
        have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
        have Hk1_notin_outT : k1 ∉ outTemps :=
          notMem_of_Forall_neg HoutTemp Hk1_notTemp
        have Hk1_notin_olds : k1 ∉ genOldIdents :=
          notMem_of_Forall_neg HoldIdentsTemp Hk1_notOld
        have Hold_eq_σ :
            σ_old k1 = σ k1 := by
          have Hk1_notin_oldFst :
              k1 ∉ oldTrips.unzip.fst.unzip.fst := by
            rw [HoldTripsFst]; exact Hk1_notin_olds
          show (updatedStates
                (updatedStates
                  (updatedStates σ
                    argTemps argVals)
                  outTemps oVals)
                oldTrips.unzip.fst.unzip.fst oldVals) k1 = σ k1
          exact updatedStates_3layer_get_notin
            Hk1_notin_argT Hk1_notin_outT Hk1_notin_oldFst
        have HAO_eq_σ : σAO k1 = σ k1 := by
          rw [initStates_get_notin Hinitout Hk1_notin_outputs,
              initStates_get_notin Hinitin Hk1_notin_inputs]
        rw [HAO_eq_σ, Hold_eq_σ]
      exact ⟨Hinv, Hpred_disj⟩
    -- Hoisted subst_fvars_correct: δ σAO expr = δ σ_old (substFvars expr …).
    have HsubstCorrect : ∀ entry ∈ presFiltered,
        δ σAO entry.snd.expr =
          δ σ_old (Lambda.LExpr.substFvars entry.snd.expr
                    (ks_L4.zip (Core.Transform.createFvars ks'_L4))) := fun entry H =>
      subst_fvars_correct Hwfc Hwfvars Hwfval Hks_len_L4
        Hdef_L4 Hnd_L4 Hsubst_L4_flipped (HpresInfo entry H).2 (HpresInfo entry H).1
    -- Per-pair tt-or-ff witness at σ_old.
    have HboolAtOld :
        ∀ pair ∈ presFiltered.zip assertLabels,
          δ σ_old (Lambda.LExpr.substFvars pair.fst.snd.expr
                     (ks_L4.zip (Core.Transform.createFvars ks'_L4))) =
              some Imperative.HasBool.tt ∨
          δ σ_old (Lambda.LExpr.substFvars pair.fst.snd.expr
                     (ks_L4.zip (Core.Transform.createFvars ks'_L4))) =
              some Imperative.HasBool.ff := by
      intro pair Hpair
      have Hentry_in : pair.fst ∈ presFiltered :=
        (List.of_mem_zip Hpair).1
      have Heq := HsubstCorrect pair.fst Hentry_in
      have Hbool_AO := HpreFilteredBool pair.fst Hentry_in
      cases Hbool_AO with
      | inl Htt => left; rw [← Heq]; exact Htt
      | inr Hff => right; rw [← Heq]; exact Hff
    -- Build the failing-pre witness at σ_old via Hpre_iff contrapositive.
    have Hfail_or_input :
        (false : Bool) = true ∨
          ∃ pair ∈ presFiltered.zip assertLabels,
            δ σ_old (Lambda.LExpr.substFvars pair.fst.snd.expr
                      (ks_L4.zip (Core.Transform.createFvars ks'_L4))) =
                some Imperative.HasBool.ff := by
      right
      -- Extract a precondition failing eval-tt at σAO via Hpre_iff.mpr's
      -- contrapositive: if all eval-tt, then `true = false`, impossible.
      have HexFail :
          ∃ entry ∈ presFiltered, δ σAO entry.snd.expr ≠ some Imperative.HasBool.tt := by
        apply Classical.byContradiction
        intro Hno
        refine Bool.noConfusion (Hpre_iff.mpr ?_)
        intro pre Hpre
        rw [List.contains_iff_mem] at Hpre
        simp only [Procedure.Spec.getCheckExprs,
                   ListMap.values_eq_map_snd, List.mem_map,
                   List.map_map] at Hpre
        obtain ⟨entry, Hentry_in, Hpre_eq⟩ := Hpre
        rw [← Hpre_eq]
        -- entry ∈ presFiltered ⇒ either eval-tt or contradict Hno.
        by_cases Htt : δ σAO entry.snd.expr = some Imperative.HasBool.tt
        · exact Htt
        · exact absurd ⟨entry, Hentry_in, Htt⟩ Hno
      obtain ⟨entryFail, HentryFail_in, HentryFail_ne_tt⟩ := HexFail
      -- bool-totality: entryFail evaluates to either tt or ff at σAO.
      have HboolAO := HpreFilteredBool entryFail HentryFail_in
      have HentryFail_ff : δ σAO entryFail.snd.expr = some Imperative.HasBool.ff := by
        cases HboolAO with
        | inl Htt => exact absurd Htt HentryFail_ne_tt
        | inr Hff => exact Hff
      -- Transport to σ_old.
      have Heq := HsubstCorrect entryFail HentryFail_in
      have HentryFail_old_ff :
          δ σ_old (Lambda.LExpr.substFvars entryFail.snd.expr
                    (ks_L4.zip (Core.Transform.createFvars ks'_L4))) =
              some Imperative.HasBool.ff := by
        rw [← Heq]; exact HentryFail_ff
      -- Find the position of entryFail in presFiltered to pair with assertLabels.
      have Hfilter_eq_pres :
          (proc.spec.preconditions.filter
            (fun (_, check) => check.attr != .Free)) = presFiltered :=
        filter_bne_eq_filter_ne proc.spec.preconditions
      have HassertLen' : presFiltered.length = assertLabels.length := by
        have HH := HassertLabelsLen
        rw [HprocEq] at HH
        rw [Hfilter_eq_pres] at HH
        exact HH.symm
      rcases List.mem_iff_get.mp HentryFail_in with ⟨n, Hn_eq⟩
      have Hi' : n.val < assertLabels.length := HassertLen' ▸ n.isLt
      have Hi_eq : presFiltered[n.val]'n.isLt = entryFail := Hn_eq
      refine ⟨(entryFail, assertLabels[n.val]'Hi'), ?_, HentryFail_old_ff⟩
      have Hzip_get :
          (presFiltered.zip assertLabels)[n.val]'(by
            exact List.length_zip ▸ Nat.lt_min.mpr ⟨n.isLt, Hi'⟩) =
            (entryFail, assertLabels[n.val]'Hi') := by
        rw [List.getElem_zip, Hi_eq]
      exact Hzip_get.symm ▸ List.getElem_mem _
    have HL4_pre :
        EvalStatementsContract π φ ⟨σ_old, δ, false⟩
          (((proc.spec.preconditions.filter
                (fun (_, check) => check.attr != .Free)).zip
              assertLabels).map (fun (entry, lbl) =>
            Statement.assert lbl
              (Lambda.LExpr.substFvars entry.snd.expr
                (ks_L4.zip
                  (Core.Transform.createFvars ks'_L4)))
              (entry.snd.md.setCallSiteFileRange md)))
          ⟨σ_old, δ, true⟩ := by
      apply H_asserts_zip_fail
        (σ' := σ_old) (f := false)
        (ks := ks_L4)
        (ks' := ks'_L4)
        (pres := proc.spec.preconditions.filter
                  (fun (_, check) => check.attr != .Free))
        (labels := assertLabels)
        Hwfb
      · -- Hbool: per-pair "tt or ff".  Bridge filter forms.
        intro pair Hpair
        have Hpair' : pair ∈ presFiltered.zip assertLabels := by
          show pair ∈ (proc.spec.preconditions.filter
                        (fun (_, c) => c.attr ≠ .Free)).zip assertLabels
          exact (filter_bne_eq_filter_ne proc.spec.preconditions).symm ▸ Hpair
        exact HboolAtOld pair Hpair'
      · -- Hfail_or_input: false = true ∨ ∃ failing pair.  Bridge filter forms.
        rcases Hfail_or_input with Hf | ⟨pair, Hpair_in, Hpair_ff⟩
        · exact Or.inl Hf
        · refine Or.inr ⟨pair, ?_, Hpair_ff⟩
          exact (filter_bne_eq_filter_ne proc.spec.preconditions) ▸ Hpair_in
    have HL4 :
        EvalStatementsContract π φ ⟨σ_old, δ, false⟩
          asserts ⟨σ_old, δ, true⟩ := by
      rw [HassertShape]
      rw [HprocEq]
      exact HassertSubst_eq ▸ HL4_pre
    -- L6 (assumes): polymorphic-flag, both endpoints at f=true.
    -- Use H_assumes_zip_poly with a Disj/SubstStores/Defined setup that
    -- doesn't require the eval-tt witness — but H_assumes_zip_poly's
    -- shape DOES require it.  Instead we observe that since both endpoints
    -- of HL6 are at f=true and the assume statements may carry any
    -- evaluation behavior, we just need a polymorphic-flag walk that
    -- terminates with the same flag.
    -- The simplest approach: show the assumes evaluate to tt at σ_havoc
    -- (mirroring success arm's HpostPayload), then apply H_assumes_zip_poly.
    -- This is the same setup as the success arm with f := true.
    -- But we can also bypass HpostPayload entirely: just need to show
    -- that L6 is a no-op walk through assume statements at flag=true.
    -- For simplicity and correctness, mirror the success arm's HpostPayload.
    -- (continued below)
    -- σ_havoc abbreviation.
    let σ_havoc : CoreStore :=
      updatedStates σ'
        (argTemps ++
          outTemps ++ genOldIdents)
        (argVals ++ oVals ++ oldVals)
    have Hσ'_eq : σ' = updatedStates σ lhs modvals :=
      UpdateStatesUpdated Hupdate
    -- D2c: σ_R1 = σO with old-bindings.
    let σ_R1 : CoreStore :=
      updatedStates σO genOldIdents oldVals
    -- ─── Prepare HpostPayload for H_assumes_zip_poly ───
    -- Filtered argument substitution shape — same as success arm.
    let filtered_argSubst :
        List (Expression.Ident × Expression.Ident) :=
      (proc.header.inputs.keys.zip argTemps).filter
        (fun pr =>
          ¬ (proc.header.outputs.keys).contains pr.1)
    let filtered_inputs : List Expression.Ident :=
      filtered_argSubst.unzip.fst
    let filtered_argTemps : List Expression.Ident :=
      filtered_argSubst.unzip.snd
    let filtered_ks : List Expression.Ident :=
      proc.header.outputs.keys ++ filtered_inputs
    let filtered_ks' : List Expression.Ident :=
      lhs ++ filtered_argTemps
    have Hzip_unzip :
        (proc.header.inputs.keys.zip argTemps).unzip =
        (proc.header.inputs.keys, argTemps) :=
      List.unzip_zip HinKeys_argTemps_len
    have Hfilter_in :
        ∀ pr ∈ filtered_argSubst,
          pr ∈ proc.header.inputs.keys.zip argTemps ∧
          pr.1 ∉ proc.header.outputs.keys := by
      intro pr Hpr
      have := List.mem_filter.mp Hpr
      refine ⟨this.1, ?_⟩
      simpa using this.2
    have Hfilt_len_sym :
        filtered_inputs.length = filtered_argTemps.length := by
      show filtered_argSubst.unzip.fst.length =
            filtered_argSubst.unzip.snd.length
      simp [List.unzip_eq_map]
    have Hkslen :
        filtered_ks.length = filtered_ks'.length := by
      show (proc.header.outputs.keys ++
            filtered_inputs).length =
           (lhs ++ filtered_argTemps).length
      rw [List.length_append, List.length_append,
          HoutKeys_lhs_len, Hfilt_len_sym]
    have Hfilt_in_eq_map :
        filtered_inputs = filtered_argSubst.map Prod.fst := by
      show filtered_argSubst.unzip.fst = _
      simp [List.unzip_eq_map]
    have Hfilt_argT_eq_map :
        filtered_argTemps = filtered_argSubst.map Prod.snd := by
      show filtered_argSubst.unzip.snd = _
      simp [List.unzip_eq_map]
    have Hfilt_in_sub_inputs :
        ∀ v ∈ filtered_inputs, v ∈ proc.header.inputs.keys := by
      intro v Hv
      have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
        Hfilt_in_eq_map ▸ Hv
      rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
      have HinZip := (Hfilter_in pr Hpr_in).1
      have Hofzip := List.of_mem_zip HinZip
      exact Hpr_eq.symm ▸ Hofzip.1
    have Hfilt_argT_sub_argTemps :
        ∀ v ∈ filtered_argTemps, v ∈ argTemps := by
      intro v Hv
      have Hv' : v ∈ filtered_argSubst.map Prod.snd :=
        Hfilt_argT_eq_map ▸ Hv
      rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
      have HinZip := (Hfilter_in pr Hpr_in).1
      have Hofzip := List.of_mem_zip HinZip
      exact Hpr_eq.symm ▸ Hofzip.2
    have Hfilt_in_disj_outs :
        filtered_inputs.Disjoint proc.header.outputs.keys := by
      intro v Hv1 Hv2
      have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
        Hfilt_in_eq_map ▸ Hv1
      rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
      have HnotIn := (Hfilter_in pr Hpr_in).2
      rw [Hpr_eq] at HnotIn
      exact HnotIn Hv2
    have Hnd : Imperative.substNodup
        (filtered_ks.zip filtered_ks') := by
      have HzipUnzip :
          (filtered_ks.zip filtered_ks').unzip =
            (filtered_ks, filtered_ks') :=
        List.unzip_zip Hkslen
      show ((filtered_ks.zip filtered_ks').unzip.fst ++
            (filtered_ks.zip filtered_ks').unzip.snd).Nodup
      rw [HzipUnzip]
      show ((proc.header.outputs.keys ++ filtered_inputs) ++
            (lhs ++ filtered_argTemps)).Nodup
      have Hfilt_in_disj_lhs :
          filtered_inputs.Disjoint lhs := by
        intro v Hv1 Hv2
        exact HinKeys_disj_lhs (Hfilt_in_sub_inputs v Hv1) Hv2
      have HoutKeys_disj_filt_argT :
          proc.header.outputs.keys.Disjoint
            filtered_argTemps := by
        intro v Hv1 Hv2
        exact HoutKeys_disj_argTemps Hv1
          (Hfilt_argT_sub_argTemps v Hv2)
      have Hfilt_in_disj_filt_argT :
          filtered_inputs.Disjoint filtered_argTemps := by
        intro v Hv1 Hv2
        exact HinKeys_disj_argTemps
          (Hfilt_in_sub_inputs v Hv1)
          (Hfilt_argT_sub_argTemps v Hv2)
      have Hlhs_disj_filt_argT :
          lhs.Disjoint filtered_argTemps := by
        intro v Hv1 Hv2
        exact HlhsDisjArg Hv1
          (Hfilt_argT_sub_argTemps v Hv2)
      have Hin_nd_pw :
          List.Pairwise
            (· ≠ ·) proc.header.inputs.keys :=
        List.nodup_iff_pairwise_ne.mp Hinnd_io
      have HargT_nd_pw :
          List.Pairwise (· ≠ ·) argTemps :=
        List.nodup_iff_pairwise_ne.mp HargNd
      have Hzip_pw_fst :
          List.Pairwise
            (fun (p q :
                Expression.Ident × Expression.Ident) =>
              p.1 ≠ q.1)
            (proc.header.inputs.keys.zip argTemps) := by
        rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                    p.1 ≠ q.1) =
              (fun p q => Prod.fst p ≠ Prod.fst q) from rfl]
        rw [← List.pairwise_map]
        rw [List.map_fst_zip
              (Nat.le_of_eq HinKeys_argTemps_len)]
        exact Hin_nd_pw
      have Hzip_pw_snd :
          List.Pairwise
            (fun (p q :
                Expression.Ident × Expression.Ident) =>
              p.2 ≠ q.2)
            (proc.header.inputs.keys.zip argTemps) := by
        rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                    p.2 ≠ q.2) =
              (fun p q => Prod.snd p ≠ Prod.snd q) from rfl]
        rw [← List.pairwise_map]
        rw [List.map_snd_zip
              (Nat.le_of_eq HinKeys_argTemps_len.symm)]
        exact HargT_nd_pw
      have Hfilt_pw_fst :
          List.Pairwise
            (fun (p q :
                Expression.Ident × Expression.Ident) =>
              p.1 ≠ q.1)
            filtered_argSubst :=
        List.Pairwise.sublist List.filter_sublist Hzip_pw_fst
      have Hfilt_pw_snd :
          List.Pairwise
            (fun (p q :
                Expression.Ident × Expression.Ident) =>
              p.2 ≠ q.2)
            filtered_argSubst :=
        List.Pairwise.sublist List.filter_sublist Hzip_pw_snd
      have Hfilt_in_nodup : filtered_inputs.Nodup := by
        show filtered_argSubst.unzip.fst.Nodup
        simp [List.unzip_eq_map]
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        exact Hfilt_pw_fst
      have Hfilt_argT_nodup : filtered_argTemps.Nodup := by
        show filtered_argSubst.unzip.snd.Nodup
        simp [List.unzip_eq_map]
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        exact Hfilt_pw_snd
      rw [List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨Houtnd_io, Hfilt_in_nodup, ?_⟩
        intro a Ha b Hb Heq
        subst Heq
        exact Hfilt_in_disj_outs Hb Ha
      · rw [List.nodup_append]
        refine ⟨HlhsNd, Hfilt_argT_nodup, ?_⟩
        intro a Ha b Hb Heq
        subst Heq
        exact Hlhs_disj_filt_argT Ha Hb
      · intro a Ha b Hb Heq
        subst Heq
        rcases List.mem_append.mp Ha with HaOuts | HaIn <;>
          rcases List.mem_append.mp Hb with HbLhs | HbArgT
        · exact HoutKeys_disj_lhs HaOuts HbLhs
        · exact HoutKeys_disj_filt_argT HaOuts HbArgT
        · exact Hfilt_in_disj_lhs HaIn HbLhs
        · exact Hfilt_in_disj_filt_argT HaIn HbArgT
    -- σO/σ_R1/σ_havoc definedness facts.
    have HσO_def_outs :
        Imperative.isDefined σO proc.header.outputs.keys :=
      HavocVarsDefMonotone (InitStatesDefined Hinitout) Hhav1
    have HσO_def_inputs :
        Imperative.isDefined σO proc.header.inputs.keys :=
      HavocVarsDefMonotone
        (InitStatesDefMonotone (InitStatesDefined Hinitin) Hinitout) Hhav1
    have σR1_off_olds :
        ∀ {v}, v ∉ genOldIdents → σ_R1 v = σO v := fun Hv =>
      updatedStates_get_notin Hv
    have Hσ_R1_def_outs :
        Imperative.isDefined σ_R1 proc.header.outputs.keys := fun v Hv =>
      (show σ_R1 v = σO v from σR1_off_olds (HoutKeys_disj_olds Hv)) ▸ HσO_def_outs v Hv
    have Hσ_R1_def_filt_in :
        Imperative.isDefined σ_R1 filtered_inputs := fun v Hv =>
      let Hv_in := Hfilt_in_sub_inputs v Hv
      (show σ_R1 v = σO v from σR1_off_olds (HinKeys_disj_olds Hv_in)) ▸ HσO_def_inputs v Hv_in
    have Hσ_havoc_def_lhs :
        Imperative.isDefined σ_havoc lhs := by
      intro v Hv
      show (updatedStates σ'
        (argTemps ++
          outTemps ++ genOldIdents)
        (argVals ++ oVals ++ oldVals) v).isSome = true
      have Hv_notin : v ∉ argTemps ++ outTemps ++ genOldIdents :=
        List.notin_3_append_of (HlhsDisjArg Hv) (HlhsDisjOut Hv) (HlhsDisjOld Hv)
      exact (updatedStates_get_notin Hv_notin) ▸ HavocVarsDefined (UpdateStatesHavocVars Hupdate) v Hv
    have Hσ_havoc_def_filt_argT :
        Imperative.isDefined σ_havoc filtered_argTemps := by
      intro v Hv
      have Hv_argT : v ∈ argTemps :=
        Hfilt_argT_sub_argTemps v Hv
      show (updatedStates σ'
        (argTemps ++
          outTemps ++ genOldIdents)
        (argVals ++ oVals ++ oldVals) v).isSome = true
      apply updatedStatesDefined
      · simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
              Hargtriplen, Houttriplen, HgenOldOldValsLen]
      · simp only [List.mem_append]
        exact Or.inl (Or.inl Hv_argT)
    have Hdef : Imperative.substDefined σ_R1 σ_havoc
        (filtered_ks.zip filtered_ks') :=
      substDefined_of_app Hσ_R1_def_outs Hσ_R1_def_filt_in
        Hσ_havoc_def_lhs Hσ_havoc_def_filt_argT
    -- σ_R1 = σ_havoc on filtered_ks.zip filtered_ks' — copy success-arm Hsubst.
    have HmodvalsLen' : lhs.length = modvals.length := by
      have := UpdateStatesLength Hupdate; omega
    -- σ_R1 reads: same as success arm.
    have HinKVlen :
        proc.header.inputs.keys.length = argVals.length :=
      InitStatesLength Hinitin
    have Hrd_R1_in_full :
        ReadValues σ_R1 proc.header.inputs.keys argVals := by
      apply readValues_updatedStates HgenOldOldValsLen HinKeys_disj_olds
      have HrdAO : ReadValues σAO proc.header.inputs.keys argVals :=
        InitStatesReadValuesMonotone (σ:=σA) (InitStatesReadValues Hinitin) Hinitout
      have Hh1 := HavocVarsUpdateStates Hhav1
      rcases Hh1 with ⟨ovh, Hup_havoc⟩
      apply UpdateStatesReadValuesMonotone (σ:=σAO) _ ?_ Hup_havoc
      · exact Hinoutnd
      · exact HrdAO
    have Hrd_R1_outs :
        ReadValues σ_R1 proc.header.outputs.keys modvals :=
      readValues_updatedStates HgenOldOldValsLen HoutKeys_disj_olds Hrd
    have Hrd_havoc_argT :
        ReadValues σ_havoc argTemps argVals := by
      show ReadValues
        (updatedStates σ'
          (argTemps ++
            outTemps ++ genOldIdents)
          (argVals ++ oVals ++ oldVals))
        argTemps argVals
      rw [Hflatten_eq]
      have HargF_σ' :
          ReadValues
            (updatedStates σ' argTemps argVals)
            argTemps argVals :=
        readValues_updatedStatesSame HargTempsLen HargNd
      have HargF_step1 :
          ReadValues
            (updatedStates
              (updatedStates σ' argTemps argVals)
              outTemps oVals) argTemps argVals :=
        readValues_updatedStates HoutTempsLen HargOutDisj HargF_σ'
      exact HoldTripsFst ▸ readValues_updatedStates HgenOldOldValsLen HargOldDisj HargF_step1
    have Hrd_havoc_lhs :
        ReadValues σ_havoc lhs modvals := by
      apply readValues_updatedStates
      · simp [argTemps, outTemps, List.length_append, List.unzip_eq_map,
              Hargtriplen, Houttriplen, HgenOldOldValsLen]
      · intro v Hv1 Hv2
        simp only [List.mem_append] at Hv2
        rcases Hv2 with (ha | ho) | ho
        · exact HlhsDisjArg Hv1 ha
        · exact HlhsDisjOut Hv1 ho
        · exact HlhsDisjOld Hv1 ho
      · rw [Hσ'_eq]
        exact readValues_updatedStatesSame HmodvalsLen' HlhsNd
    have Hsubst : Imperative.substStores σ_R1 σ_havoc
        (filtered_ks.zip filtered_ks') := by
      intro k1 k2 Hkin
      show σ_R1 k1 = σ_havoc k2
      rcases List.mem_iff_get.mp Hkin with ⟨n, Hn⟩
      have Hn_lt_ks : n.val < filtered_ks.length := by
        have := n.isLt; simp [List.length_zip, Hkslen] at this; omega
      have Hn_lt_ks' : n.val < filtered_ks'.length := by
        rw [← Hkslen]; exact Hn_lt_ks
      have ⟨Hk1_eq, Hk2_eq⟩ :=
        List.zip_pair_split Hn_lt_ks Hn_lt_ks' Hn
      by_cases Hsplit : n.val < proc.header.outputs.keys.length
      · have HoutLhsLen : n.val < lhs.length := by
          rw [← HoutKeys_lhs_len]; exact Hsplit
        have Hk1_app :
            k1 = proc.header.outputs.keys[n.val]'Hsplit := by
          rw [Hk1_eq]
          show (proc.header.outputs.keys ++
                filtered_inputs)[n.val]'_ = _
          rw [List.getElem_append_left (h := Hsplit)]
        have Hk2_app : k2 = lhs[n.val]'HoutLhsLen := by
          rw [Hk2_eq]
          show (lhs ++ filtered_argTemps)[n.val]'_ = _
          rw [List.getElem_append_left (h := HoutLhsLen)]
        have HmodLen_outs :
            n.val < modvals.length := by
          have := ReadValuesLength Hrd_R1_outs; omega
        have HrdR1_get :
            σ_R1 (proc.header.outputs.keys[n.val]'Hsplit) =
              some (modvals[n.val]'HmodLen_outs) :=
          readValues_get
            (σ:=σ_R1) (ks:=proc.header.outputs.keys)
            (vs:=modvals) Hrd_R1_outs
            (i:=n.val) (hi:=Hsplit) (hi':=HmodLen_outs)
        have HrdHavoc_get :
            σ_havoc (lhs[n.val]'HoutLhsLen) =
              some (modvals[n.val]'HmodLen_outs) :=
          readValues_get
            (σ:=σ_havoc) (ks:=lhs) (vs:=modvals)
            Hrd_havoc_lhs
            (i:=n.val) (hi:=HoutLhsLen) (hi':=HmodLen_outs)
        rw [Hk1_app, HrdR1_get, Hk2_app, HrdHavoc_get]
      · have Hsplit_le : proc.header.outputs.keys.length ≤ n.val :=
          Nat.le_of_not_lt Hsplit
        have Hlhs_le : lhs.length ≤ n.val := by
          rw [← HoutKeys_lhs_len]; exact Hsplit_le
        have Hk1_app :
            k1 = filtered_inputs[n.val -
                proc.header.outputs.keys.length]'(by
              have Hl : filtered_ks.length =
                  proc.header.outputs.keys.length +
                    filtered_inputs.length :=
                List.length_append
              omega) := by
          rw [Hk1_eq]
          show (proc.header.outputs.keys ++
                filtered_inputs)[n.val]'_ = _
          rw [List.getElem_append_right (h₁ := Hsplit_le)]
        have Hk2_app :
            k2 = filtered_argTemps[n.val - lhs.length]'(by
              have Hl : filtered_ks'.length =
                  lhs.length + filtered_argTemps.length :=
                List.length_append
              omega) := by
          rw [Hk2_eq]
          show (lhs ++ filtered_argTemps)[n.val]'_ = _
          rw [List.getElem_append_right (h₁ := Hlhs_le)]
        have Hidx_eq :
            n.val - proc.header.outputs.keys.length =
            n.val - lhs.length := by
          rw [HoutKeys_lhs_len]
        let j : Nat :=
          n.val - proc.header.outputs.keys.length
        have Hj_lt_filt :
            j < filtered_inputs.length := by
          have Hl : filtered_ks.length =
              proc.header.outputs.keys.length +
                filtered_inputs.length :=
            List.length_append
          omega
        have Hj_lt_argT :
            j < filtered_argTemps.length := by
          rw [← Hfilt_len_sym]; exact Hj_lt_filt
        have Hj_lt_subst :
            j < filtered_argSubst.length := by
          show j < filtered_argSubst.length
          rw [show filtered_argSubst.length =
              filtered_argSubst.unzip.fst.length from by
              simp [List.unzip_eq_map]]
          exact Hj_lt_filt
        have HpairAtJ :
            filtered_argSubst[j]'Hj_lt_subst = (k1, k2) := by
          have HfilGetFst :
              filtered_inputs[j]'Hj_lt_filt =
              (filtered_argSubst[j]'Hj_lt_subst).fst := by
            show filtered_argSubst.unzip.fst[j]'_ = _
            simp [List.unzip_eq_map]
          have HfilGetSnd :
              filtered_argTemps[j]'Hj_lt_argT =
              (filtered_argSubst[j]'Hj_lt_subst).snd := by
            show filtered_argSubst.unzip.snd[j]'_ = _
            simp [List.unzip_eq_map]
          ext
          · rw [← HfilGetFst, ← Hk1_app]
          · rw [← HfilGetSnd]
            have : filtered_argTemps[n.val - lhs.length]'(by
                have Hl : filtered_ks'.length =
                    lhs.length + filtered_argTemps.length :=
                  List.length_append
                omega) = filtered_argTemps[j]'Hj_lt_argT := by
              congr 1
              exact Hidx_eq.symm
            rw [Hk2_app, this]
        have HpairIn : (k1, k2) ∈ filtered_argSubst := by
          exact HpairAtJ.symm ▸ List.getElem_mem _
        have HpairZip := (Hfilter_in (k1, k2) HpairIn).1
        obtain ⟨m, Hm_lt_in, Hm_lt_argT, Hk1_inGet, Hk2_argTGet⟩ :=
          pair_in_zip_pos_decomp HinKeys_argTemps_len HpairZip
        have Hm_lt_argV : m < argVals.length := HinKVlen ▸ Hm_lt_in
        have HrdR1_get :
            σ_R1 (proc.header.inputs.keys[m]'Hm_lt_in) =
              some (argVals[m]'Hm_lt_argV) :=
          readValues_get (σ:=σ_R1) (ks:=proc.header.inputs.keys)
            (vs:=argVals) Hrd_R1_in_full
            (i:=m) (hi:=Hm_lt_in) (hi':=Hm_lt_argV)
        have HrdHavoc_get :
            σ_havoc (argTemps[m]'Hm_lt_argT) =
              some (argVals[m]'Hm_lt_argV) :=
          readValues_get (σ:=σ_havoc) (ks:=argTemps) (vs:=argVals)
            Hrd_havoc_argT
            (i:=m) (hi:=Hm_lt_argT) (hi':=Hm_lt_argV)
        rw [Hk1_inGet, HrdR1_get, Hk2_argTGet, HrdHavoc_get]
    -- L6 (assumes): the assumes list is some list of statements built
    -- by callElimCmd.  At flag=true, evaluating any well-formed assume
    -- stays at flag=true regardless of the post evaluation, but we
    -- need a derivation.  We can simply use the fact that
    -- `EvalStatementsContract` over an empty list is reflexive and
    -- skip-via-step_stmts_cons walk is provided by
    -- `H_assumes_zip_poly` once we have HpostPayload.
    -- Mirror the success arm's HpostPayload setup.
    -- HpostPayload requires δ σ_R1 expr = some tt for each filtered post.
    -- The success arm derives this; we copy.
    -- ── L6 plumbing (mirror success arm) ──
    have HInitVars_empty : InitVars σO [] σO := InitVars.init_none
    obtain ⟨Hwf2_univ, HσAO_reads_outs, HoldVars_sub_outs⟩ :=
      holdEval_bridge_prelude (args := args) Hwf2 Hhav1 Hinitout HprocEq
    have HσAO_notin_eq_σ :
        ∀ v, v ∉ proc.header.outputs.keys →
             v ∉ proc.header.inputs.keys →
             σAO v = σ v := by
      intro v Hv_notout Hv_notin
      rw [initStates_get_notin Hinitout Hv_notout,
          initStates_get_notin Hinitin Hv_notin]
    have δ_fvar_eq := delta_fvar_eq_of_wfvars Hwfvars (delta := δ)
    -- σ_R1 read olds positional.
    have HrdR1_olds : ReadValues σ_R1 genOldIdents oldVals := by
      show ReadValues (updatedStates σO genOldIdents oldVals) _ _
      exact readValues_updatedStatesSame HgenOldOldValsLen HoldNd
    have σ_R1_read_olds :
        ∀ (i : Nat) (Hi : i < genOldIdents.length)
          (Hi' : i < oldVals.length),
          σ_R1 (genOldIdents[i]'Hi) =
            some (oldVals[i]'Hi') := fun i Hi Hi' =>
      readValues_get HrdR1_olds (i:=i) (hi:=Hi) (hi':=Hi')
    have HoldEval_bridge :
        ∀ (i : Nat) (Hi : i < oldVars.length),
          δ σO
              (Lambda.LExpr.fvar ()
                (CoreIdent.mkOld (oldVars[i]'Hi).name) none) =
            some (oldVals[i]'(HoldValsLen.symm ▸ Hi)) :=
      HoldEval_bridge_at_σO Hwf2_univ Hinitout HσAO_reads_outs
        Hevalouts hCallArgsLhs _HoutAlign HoldVars_sub_outs
        HoldVars_sub_lhs HoldVals HoldValsLen
    -- L6 oldTripsCanonical/oldSubst/posts_filtered shape.
    let oldTripsCanonical_L6 :
        List ((Expression.Ident × Expression.Ty) ×
              Expression.Ident) :=
      (((genOldIdents.zip oldTys).zip oldVars).zip
        (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
        fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
    let inputOnlyOldSubst_L6 :
        Map Expression.Ident Expression.Expr :=
      callElim_inputOnlyOldSubst proc' args
    let oldSubst_L6 : Map Expression.Ident Expression.Expr :=
      Core.Transform.createOldVarsSubst oldTripsCanonical_L6 ++
        inputOnlyOldSubst_L6
    let posts_filtered_L6 :
        ListMap CoreLabel Procedure.Check :=
      Procedure.Spec.updateCheckExprs
        (proc'.spec.postconditions.values.map
          (fun c =>
            Lambda.LExpr.substFvars c.expr oldSubst_L6))
        proc'.spec.postconditions
    have forall_post_filtered_decompose :
        ∀ entry : CoreLabel × Procedure.Check,
          entry ∈ posts_filtered_L6.toList →
          ∃ c ∈ proc'.spec.postconditions.values,
            entry.snd.expr =
              Lambda.LExpr.substFvars c.expr oldSubst_L6 := by
      intro entry Hentry
      apply updateCheckExprs_substFvars_mem
      rw [updateCheckExprs_walk_eq_go]
      show entry ∈
          (proc'.spec.postconditions.keys.zip
            (Procedure.Spec.updateCheckExprs.go _ _))
      exact Hentry
    have HoldSubBridge :
        ∀ k w,
          Map.find?
            (Core.Transform.createOldVarsSubst
              oldTripsCanonical_L6) k = some w →
          δ σ_R1 w =
            δ σO (Lambda.LExpr.fvar () k none) :=
      HoldSubBridge_at_σO Hwfvars HgenOldLen HoldTysLen
        HoldValsLen σ_R1_read_olds HoldEval_bridge
    have HinputSubBridge :
        ∀ k w,
          Map.find? inputOnlyOldSubst_L6 k = some w →
          δ σ_R1 w =
            δ σO (Lambda.LExpr.fvar () k none) :=
      HinputSubBridge_at_σO Hwfvars Hwfval Hwfc Hwf2 HprocEq Hiodisj
        Hinitin Hinitout Hhav1 HInitVars_empty Hevalargs hCallArgsIn
        HargIsDef HoldIdentsTemp Hgenrel
        HargVarsNotInInKeys HargVarsNotInOutKeys rfl
    have HpostEval_bridge :
        ∀ entry : CoreLabel × Procedure.Check,
          entry ∈ posts_filtered_L6.toList →
          δ σ_R1 entry.snd.expr =
            some Imperative.HasBool.tt := by
      intro entry Hentry
      obtain ⟨c, Hc_in, Hentry_eq⟩ :=
        forall_post_filtered_decompose entry Hentry
      rw [Hentry_eq]
      have Hsub :
          ∀ k w, k ∈ Imperative.HasVarsPure.getVars
                        (P:=Expression) c.expr →
            Map.find? oldSubst_L6 k = some w →
            δ σ_R1 w =
              δ σO (Lambda.LExpr.fvar () k none) := by
        intro k w _Hk Hf
        cases hfind : Map.find?
                        (Core.Transform.createOldVarsSubst
                          oldTripsCanonical_L6) k with
        | some v =>
          have Hvw : v = w := find?_append_some_eq hfind Hf
          exact Hvw.symm ▸ HoldSubBridge k v hfind
        | none =>
          exact HinputSubBridge k w (find?_append_none_elim hfind Hf)
      have HpostVarsFresh_via_c :
          ∀ c ∈ proc'.spec.postconditions.values,
          ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) c.expr,
            ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
            v ∉ CallArg.getLhs args := by
        intro c Hc_in v Hv
        exact _HpostVarsFresh c.expr (c_in_postExprs_of_proc' c Hc_in) v Hv
      have HsurvBridgeC :
          ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                  c.expr,
            Map.find? oldSubst_L6 v = none →
            δ σ_R1 (Lambda.LExpr.fvar () v none) =
              δ σO (Lambda.LExpr.fvar () v none) := by
        intro v Hv _Hnone
        have HvFresh := HpostVarsFresh_via_c c Hc_in v Hv
        have HvNotOld : ¬ isOldTempIdent v := HvFresh.2.1
        have HvNotGen : v ∉ genOldIdents :=
          notMem_of_Forall_neg HoldIdentsTemp HvNotOld
        have Hσ_R1_v_eq_σO :
            σ_R1 v = σO v := by
          show (updatedStates σO genOldIdents oldVals) v = σO v
          exact updatedStates_get_notin HvNotGen
        rw [δ_fvar_eq σ_R1 v, δ_fvar_eq σO v]
        exact Hσ_R1_v_eq_σO
      have Hbridge :
          δ σ_R1 (Lambda.LExpr.substFvars c.expr oldSubst_L6) =
            δ σO c.expr :=
        subst_fvars_eval_bridge Hwfc Hwfvars Hwfval
          HsurvBridgeC Hsub
      rw [Hbridge]
      have Hin_full := c_in_postExprs_of_proc' c Hc_in
      have Hin_contains :
          (Procedure.Spec.getCheckExprs
              proc.spec.postconditions).contains c.expr = true :=
        List.contains_iff_mem.mpr Hin_full
      exact (Hpost c.expr Hin_contains).2
    -- Hinv: residual invStores σ_R1 σ_havoc — copy from success arm.
    have HrdHavoc_olds_pos :
        ∀ (i : Nat) (Hi : i < genOldIdents.length)
          (Hi' : i < oldVals.length),
          σ_havoc (genOldIdents[i]'Hi) =
            some (oldVals[i]'Hi') := by
      have HzipAppend2 :
          ((argTemps ++
              outTemps) ++ genOldIdents).zip
            ((argVals ++ oVals) ++ oldVals) =
            ((argTemps ++
                outTemps).zip
              (argVals ++ oVals)) ++
            (genOldIdents.zip oldVals) := by
        apply List.zip_append
        simp [List.length_append, HargTempsLen, HoutTempsLen]
      have HsplitOverlay :
          σ_havoc =
          updatedStates
            (updatedStates σ'
              (argTemps ++
                outTemps)
              (argVals ++ oVals))
            genOldIdents oldVals := by
        show updatedStates σ'
              (argTemps ++
                outTemps ++ genOldIdents)
              (argVals ++ oVals ++ oldVals) = _
        simp only [updatedStates]
        rw [HzipAppend2, updatedStates'App]
      have HrdHavoc :
          ReadValues σ_havoc genOldIdents oldVals := by
        exact HsplitOverlay ▸ readValues_updatedStatesSame HgenOldOldValsLen HoldNd
      intro i Hi Hi'
      exact readValues_get HrdHavoc (i:=i) (hi:=Hi) (hi':=Hi')
    have b1_var_witness :=
      @b1_var_witness_at_oldSubst oldVars genOldIdents oldTys
        proc' args HgenOldLen HoldTysLen
    have b2_var_witness :=
      @b2_var_witness_at_oldSubst oldVars genOldIdents oldTys
        proc' args inArgs hCallArgsIn
    -- σR1_eq_σhavoc: pointwise equality off all touched layers.
    have σR1_eq_σhavoc :
        ∀ {k : Expression.Ident},
          k ∉ proc.header.inputs.keys →
          k ∉ proc.header.outputs.keys →
          k ∉ argTemps → k ∉ outTemps →
          k ∉ genOldIdents → k ∉ lhs →
          σ_R1 k = σ_havoc k := by
      intro k Hk_ins Hk_outs Hk_argT Hk_outT Hk_genOld Hk_lhs
      have HσR1_σ : updatedStates σO genOldIdents oldVals k = σ k :=
        σR1_eq_σ_for_notTouched Hinitin Hinitout Hhav1
          Hk_ins Hk_outs Hk_genOld
      have H5 : σ k = σ' k := by
        rw [Hσ'_eq, updatedStates_get_notin Hk_lhs]
      have Hk_notin_layered : k ∉ argTemps ++ outTemps ++ genOldIdents :=
        List.notin_3_append_of Hk_argT Hk_outT Hk_genOld
      have H6 : σ' k = σ_havoc k := by
        show σ' k = updatedStates σ'
          (argTemps ++ outTemps ++ genOldIdents)
          (argVals ++ oVals ++ oldVals) k
        rw [updatedStates_get_notin Hk_notin_layered]
      show updatedStates σO genOldIdents oldVals k = σ_havoc k
      rw [HσR1_σ, H5, H6]
    have HargVarsNotInLhs :
        ∀ argExpr ∈ CallArg.getInputExprs args,
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) argExpr,
          v ∉ CallArg.getLhs args := _HargVarsNotInLhs
    have HpostVarsFresh_via_c :
        ∀ c ∈ proc'.spec.postconditions.values,
        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) c.expr,
          ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
          v ∉ CallArg.getLhs args := by
      intro c Hc_in v Hv
      exact _HpostVarsFresh c.expr (c_in_postExprs_of_proc' c Hc_in) v Hv
    have HfiltArgT_sub_argT :
        ∀ x ∈ filtered_argTemps, x ∈ argTemps := by
      intro x Hx
      show x ∈ argTemps
      have Hx' : x ∈ filtered_argSubst.unzip.snd := Hx
      simp only [List.unzip_eq_map, List.mem_map] at Hx'
      rcases Hx' with ⟨pair, Hpair_mem, Hpair_snd⟩
      have Hpair_in_zip := (List.mem_filter.mp Hpair_mem).1
      have Hsnd_in :
          pair.snd ∈ argTemps :=
        (List.of_mem_zip Hpair_in_zip).2
      rw [← Hpair_snd]; exact Hsnd_in
    have Hinv :
        ∀ entry : CoreLabel × Procedure.Check,
          entry ∈ posts_filtered_L6.toList →
          Imperative.invStores σ_R1 σ_havoc
            ((Imperative.HasVarsPure.getVars (P:=Expression)
                entry.snd.expr).removeAll
              (filtered_ks ++ filtered_ks')) := by
      intro entry Hentry
      obtain ⟨c, Hc_in, Hentry_eq⟩ :=
        forall_post_filtered_decompose entry Hentry
      simp only [Imperative.invStores, Imperative.substStores]
      intros k1 k2 Hkin
      obtain ⟨rfl, Hk1_pre, Hk1_notin_outs, Hk1_notin_filtIn,
              Hk1_notin_lhs, Hk1_notin_filtArgT⟩ :=
        zip_removeAll4_decompose Hkin
      rw [Hentry_eq] at Hk1_pre
      rcases getVars_substFvars_mem Hk1_pre with
        Hclass_a | ⟨k, w, Hk_in, Hf, Hv_in⟩
      · obtain ⟨Hk1_post, _Hf_none⟩ := Hclass_a
        have HfreshK := HpostVarsFresh_via_c c Hc_in k1 Hk1_post
        have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
        have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
        have Hk1_notin_argT : k1 ∉ argTemps :=
          notMem_of_Forall_neg HargTemp Hk1_notTemp
        have Hk1_notin_outT : k1 ∉ outTemps :=
          notMem_of_Forall_neg HoutTemp Hk1_notTemp
        have Hk1_notin_genOld : k1 ∉ genOldIdents :=
          notMem_of_Forall_neg HoldIdentsTemp Hk1_notOld
        have Hk1_notin_ins :
            k1 ∉ proc.header.inputs.keys := by
          intro h
          rcases List.mem_iff_get.mp h with ⟨n, Hn⟩
          have Hn_lt_in : n.val < proc.header.inputs.keys.length := n.isLt
          have Hn_lt_argT : n.val < argTemps.length :=
            HinKeys_argTemps_len ▸ Hn_lt_in
          have HkE :
              proc.header.inputs.keys[n.val]'Hn_lt_in = k1 := Hn
          have Hpair_in_zip :
              (k1, argTemps[n.val]'Hn_lt_argT) ∈
                proc.header.inputs.keys.zip argTemps := by
            exact HkE.symm ▸ pair_in_zip_of_pos Hn_lt_in Hn_lt_argT
          have Hpair_in_filtAS :
              (k1, argTemps[n.val]'Hn_lt_argT) ∈
                filtered_argSubst := by
            apply List.mem_filter.mpr
            refine ⟨Hpair_in_zip, ?_⟩
            simp only [decide_not, Bool.not_eq_eq_eq_not,
                       Bool.not_true, decide_eq_false_iff_not,
                       List.contains_iff_mem]
            exact Hk1_notin_outs
          have Hk1_in_unzip :
              k1 ∈ filtered_inputs := by
            show k1 ∈ filtered_argSubst.unzip.fst
            simp only [List.unzip_eq_map, List.mem_map]
            refine ⟨(k1, argTemps[n.val]'Hn_lt_argT), Hpair_in_filtAS, rfl⟩
          exact Hk1_notin_filtIn Hk1_in_unzip
        exact σR1_eq_σhavoc Hk1_notin_ins Hk1_notin_outs
          Hk1_notin_argT Hk1_notin_outT Hk1_notin_genOld Hk1_notin_lhs
      · cases hfind : Map.find?
                        (Core.Transform.createOldVarsSubst
                          oldTripsCanonical_L6) k with
        | some w' =>
          obtain ⟨ni_val, Hni_lt_genOld, Hv_eq_gen⟩ :=
            b1_var_witness hfind Hf Hv_in
          have Hni_lt_oldVals : ni_val < oldVals.length :=
            HoldValsLen.symm ▸ HgenOldLen ▸ Hni_lt_genOld
          have Hσ_R1_v :
              σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) =
                some (oldVals[ni_val]'Hni_lt_oldVals) :=
            σ_R1_read_olds ni_val Hni_lt_genOld Hni_lt_oldVals
          have Hσ_havoc_v :
              σ_havoc (genOldIdents[ni_val]'Hni_lt_genOld) =
                some (oldVals[ni_val]'Hni_lt_oldVals) :=
            HrdHavoc_olds_pos ni_val Hni_lt_genOld Hni_lt_oldVals
          rw [Hv_eq_gen, Hσ_R1_v, Hσ_havoc_v]
        | none =>
          obtain ⟨HargExpr_in, Hk1_flat⟩ :=
            b2_var_witness hfind Hf Hv_in
          have Hk1_notin_outs' :
              k1 ∉ proc.header.outputs.keys :=
            HargVarsNotInOutKeys w HargExpr_in k1 Hv_in
          have Hk1_notin_ins' :
              k1 ∉ proc.header.inputs.keys :=
            HargVarsNotInInKeys w HargExpr_in k1 Hv_in
          have Hk1_σ_some : (σ k1).isSome := HargIsDef k1 Hk1_flat
          have Hk1_notOld' : ¬ isOldTempIdent k1 := fun Hold =>
            σ_some_contradiction Hk1_σ_some
              (Option.isNone_iff_eq_none.mp (Hgenrel.oldFresh k1 Hold))
          have Hk1_notin_argT' : k1 ∉ argTemps :=
            notin_of_isSome_isNotDefined Hk1_σ_some HndefArg_σ
          have Hk1_notin_outT' : k1 ∉ outTemps :=
            notin_of_isSome_isNotDefined Hk1_σ_some HndefOut_σ
          have Hk1_notin_genOld' : k1 ∉ genOldIdents :=
            notin_of_isSome_isNotDefined Hk1_σ_some HndefOld_σ
          exact σR1_eq_σhavoc Hk1_notin_ins' Hk1_notin_outs'
            Hk1_notin_argT' Hk1_notin_outT' Hk1_notin_genOld'
            Hk1_notin_lhs
    have Hpred_disj :
        ∀ entry : CoreLabel × Procedure.Check,
          entry ∈ posts_filtered_L6.toList →
          filtered_ks'.Disjoint
            (Imperative.HasVarsPure.getVars (P:=Expression)
              entry.snd.expr) := by
      intro entry Hentry
      obtain ⟨c, Hc_in, Hentry_eq⟩ :=
        forall_post_filtered_decompose entry Hentry
      intro x Hin1 Hin2
      rw [Hentry_eq] at Hin2
      rcases getVars_substFvars_mem Hin2 with
        Hclass_a | ⟨k', w, Hk_in, Hf, Hv_in⟩
      · obtain ⟨Hx_post, _Hf_none⟩ := Hclass_a
        have HfreshK := HpostVarsFresh_via_c c Hc_in x Hx_post
        have Hx_notTemp : ¬ isTempIdent x := HfreshK.1
        have Hx_notLhs : x ∉ CallArg.getLhs args := HfreshK.2.2
        cases List.mem_append.mp Hin1 with
        | inl Hx_lhs =>
          rw [hCallArgsLhs] at Hx_notLhs
          exact Hx_notLhs Hx_lhs
        | inr Hx_filtArgT =>
          have Hx_argT : x ∈ argTemps :=
            HfiltArgT_sub_argT x Hx_filtArgT
          exact Hx_notTemp ((List.Forall_mem_iff.mp HargTemp) x Hx_argT)
      · cases hfind : Map.find?
                        (Core.Transform.createOldVarsSubst
                          oldTripsCanonical_L6) k' with
        | some w' =>
          obtain ⟨ni_val, Hni_lt_genOld, Hx_eq_gen⟩ :=
            b1_var_witness hfind Hf Hv_in
          rw [Hx_eq_gen] at Hin1
          cases List.mem_append.mp Hin1 with
          | inl Hx_lhs =>
            exact HlhsDisjOld Hx_lhs (List.getElem_mem _)
          | inr Hx_filtArgT =>
            have Hx_argT :
                genOldIdents[ni_val]'Hni_lt_genOld ∈ argTemps :=
              HfiltArgT_sub_argT _ Hx_filtArgT
            have Hx_isTemp :
                isTempIdent (genOldIdents[ni_val]'Hni_lt_genOld) :=
              (List.Forall_mem_iff.mp HargTemp) _ Hx_argT
            have Hx_isOld :
                isOldTempIdent (genOldIdents[ni_val]'Hni_lt_genOld) :=
              (List.Forall_mem_iff.mp HoldIdentsTemp) _ (List.getElem_mem _)
            exact isTempIdent_isOldTempIdent_disjoint
              Hx_isTemp Hx_isOld
        | none =>
          obtain ⟨HargExpr_in, Hx_flat⟩ :=
            b2_var_witness hfind Hf Hv_in
          have Hx_σ_some : (σ x).isSome := HargIsDef x Hx_flat
          cases List.mem_append.mp Hin1 with
          | inl Hx_lhs =>
            have Hx_notLhs :
                x ∉ CallArg.getLhs args :=
              HargVarsNotInLhs w HargExpr_in x Hv_in
            rw [hCallArgsLhs] at Hx_notLhs
            exact Hx_notLhs Hx_lhs
          | inr Hx_filtArgT =>
            have Hx_argT :
                x ∈ argTemps :=
              HfiltArgT_sub_argT x Hx_filtArgT
            exact σ_some_contradiction Hx_σ_some
              (HndefArg_σ x Hx_argT)
    have HpostPayload :
        ∀ entry : CoreLabel × Procedure.Check,
          entry ∈ posts_filtered_L6.toList →
          Imperative.invStores σ_R1 σ_havoc
            ((Imperative.HasVarsPure.getVars (P:=Expression)
                entry.snd.expr).removeAll
              (filtered_ks ++ filtered_ks')) ∧
          filtered_ks'.Disjoint
            (Imperative.HasVarsPure.getVars (P:=Expression)
              entry.snd.expr) ∧
          δ σ_R1 entry.snd.expr =
            some Imperative.HasBool.tt := by
      intro entry Hentry
      refine ⟨Hinv entry Hentry,
              Hpred_disj entry Hentry,
              HpostEval_bridge entry Hentry⟩
    -- L6 (assumes) via H_assumes_zip_poly with f := true.
    obtain ⟨assumeLabels, _HassumeLabelsLen, HassumeShape⟩ :=
      _HassumesShape
    have HassumeSubst_eq :
        ((proc'.header.outputs.keys.zip
            (Core.Transform.createFvars (CallArg.getLhs args))) ++
          (proc'.header.inputs.keys.zip
            (Core.Transform.createFvars argTemps)).filter
            (fun (id, _) =>
              !(ListMap.keys proc'.header.outputs).contains id)) =
        filtered_ks.zip
          (Core.Transform.createFvars filtered_ks') := by
      rw [HprocEq]
      show _ = (proc.header.outputs.keys ++ filtered_inputs).zip
        (Core.Transform.createFvars (lhs ++ filtered_argTemps))
      rw [createFvarsApp]
      rw [List.zip_append
            (show proc.header.outputs.keys.length =
                  (Core.Transform.createFvars lhs).length by
              rw [createFvarsLength,
                  HoutKeys_lhs_len])]
      rw [hCallArgsLhs]
      congr 1
      show (proc.header.inputs.keys.zip
            (argTemps.map Core.Transform.createFvar)).filter _ =
        filtered_argSubst.unzip.fst.zip
          (filtered_argSubst.unzip.snd.map
            Core.Transform.createFvar)
      rw [List.zip_map_right]
      rw [List.filter_map]
      have HfiltEq :
          (proc.header.inputs.keys.zip argTemps).filter
            ((fun (x : Expression.Ident × Expression.Expr) =>
                !(ListMap.keys proc.header.outputs).contains x.1) ∘
              Prod.map id Core.Transform.createFvar) =
            filtered_argSubst := by
        show _ = (proc.header.inputs.keys.zip argTemps).filter
            (fun pr =>
              ¬ (proc.header.outputs.keys).contains pr.1)
        apply List.filter_congr
        intro pr _
        cases pr with
        | mk a b => simp [Function.comp, Prod.map]
      rw [HfiltEq]
      rw [show filtered_argSubst.unzip.fst.zip
              (filtered_argSubst.unzip.snd.map
                Core.Transform.createFvar) =
            (filtered_argSubst.unzip.fst.zip
              filtered_argSubst.unzip.snd).map
              (Prod.map id Core.Transform.createFvar) from
          List.zip_map_right]
      rw [show filtered_argSubst.unzip.fst.zip
              filtered_argSubst.unzip.snd =
            filtered_argSubst from List.zip_unzip _]
    have HL6_pre :
        EvalStatementsContract π φ ⟨σ_havoc, δ, true⟩
          ((posts_filtered_L6.zip assumeLabels).map
            (fun (entry, lbl) =>
              Statement.assume lbl
                (Lambda.LExpr.substFvars entry.snd.expr
                  (filtered_ks.zip
                    (Core.Transform.createFvars filtered_ks')))
                (entry.snd.md.setCallSiteFileRange md)))
          ⟨σ_havoc, δ, true⟩ := by
      apply H_assumes_zip_poly
        (σA := σ_R1) (σ' := σ_havoc) (f := true)
        (ks := filtered_ks)
        (ks' := filtered_ks')
        (posts := posts_filtered_L6.toList)
        (labels := assumeLabels)
        Hwfb Hwfvars Hwfval Hwfc
        Hkslen Hnd Hdef Hsubst
      intros entry Hentry
      exact HpostPayload entry Hentry
    have HL6 :
        EvalStatementsContract π φ ⟨σ_havoc, δ, true⟩
          assumes ⟨σ_havoc, δ, true⟩ := by
      rw [HassumeShape]
      exact HassumeSubst_eq ▸ HL6_pre
    -- ── D2g: Glue via EvalCallElim_glue_fail ──
    exact EvalCallElim_glue_fail HL1 HL2 HL3 HL4 HL5 HL6

/-- Call-elimination correctness for a single statement.

    Given a small-step `EvalStatementsContract` derivation of `[st]`
    from σ to σ', the transformed list `sts` produced by `callElimStmt`
    admits an `EvalStatementsContract` derivation from σ to some σ''
    that extends σ' on the freshly-introduced temp variables.  The
    call case chains L1–L6 via `EvalCallElim_glue`; non-call cases
    are immediate. -/
private theorem callElimStatementCorrect_terminal [LawfulBEq Expression.Expr]
    {σ σ' : CoreStore}
    {f : Bool}
    {p : Program}
    {γ γ' : CoreTransformState}
    {st : Statement}
    {sts : List Statement}
    (Hp : ∀ pname, π pname = Program.Procedure.find? p ⟨pname, ()⟩)
    (Heval : EvalStatementsContract π φ ⟨σ, δ, false⟩ [st] ⟨σ', δ, f⟩)
    (Hwfc : WellFormedCoreEvalCong δ)
    (Hwf : WF.WFStatementsProp p [st])
    (Hgenrel : CoreGenStateRel σ γ)
    -- Call-site WF: pre/post vars are non-temp/non-old and disjoint
    -- from `lhs`/inputs.keys/outputs.keys (seven clauses; see WFCallSiteProp
    -- above (line 1095 of this file)).
    (Hwfcallsite : WFCallSiteProp p π st)
    (Helim : (Except.ok sts, γ') = (runWith st (callElimStmt · p) γ)) :
    ∃ σ'',
      Inits σ' σ'' ∧
      EvalStatementsContract π φ ⟨σ, δ, false⟩ sts ⟨σ'', δ, f⟩ := by
  -- Non-call cases close with σ'' = σ' (callElimStmt returns [st]);
  -- call case extends σ' with fresh temp/old vars.  Non-call branches
  -- unified via `callElimStmt_non_call_eq`, dispatched through `nc_close`.
  have nc_close : ∀ {b : Statement} (_ : st = b)
      (_ : ∀ pn ar mt, b ≠ .cmd (CmdExt.call pn ar mt)),
      ∃ σ'', Inits σ' σ'' ∧
        EvalStatementsContract π φ ⟨σ, δ, false⟩ sts ⟨σ'', δ, f⟩ := by
    intro b heq hne
    refine ⟨σ', Inits.init InitVars.init_none, ?_⟩
    have hsts := callElimStmt_non_call_eq hne (heq ▸ Helim)
    rw [hsts]; rw [← heq]; exact Heval
  cases hst : st with
  | block lbl b md => exact nc_close hst (by intro _ _ _ h; cases h)
  | ite cd tb eb md => exact nc_close hst (by intro _ _ _ h; cases h)
  | loop g m i b md => exact nc_close hst (by intro _ _ _ h; cases h)
  | exit lbl md => exact nc_close hst (by intro _ _ _ h; cases h)
  | funcDecl f md => exact nc_close hst (by intro _ _ _ h; cases h)
  | typeDecl tc md => exact nc_close hst (by intro _ _ _ h; cases h)
  | cmd c =>
      cases c with
      | cmd c' => exact nc_close hst (by intro _ _ _ h; cases h)
      | call procName args md =>
          -- B1: Destructure Helim to expose triplet plumbing.
          subst hst
          simp only [runWith, StateT.run, callElimStmt, bind, pure,
                     StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
                     modify, modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet,
                     StateT.modifyGet, monadLift, MonadLift.monadLift, ExceptT.lift,
                     Functor.map, StateT.map] at Helim
          -- Helim is now `(Except.ok sts, γ') = (match callElimCmd … γ_ext …)`.
          -- Successive splits peel the outer pair-binder, the inner Except,
          -- and the `Option (List Statement)`.
          split at Helim
          rename_i x_pair a_ce s_ce heq_ce
          split at Helim
          · -- inner `Except.ok` branch
            rename_i a_opt heq_ok
            -- a_opt : Option (List Statement)
            -- Now Helim has a `match a_opt with | none => ... | some s' => ...`.
            split at Helim
            · -- `a_opt = none`: heq_ce says `callElimCmd ... = (Except.ok none, s_ce)`.
              -- But `callElimCmd (CmdExt.call ...)` never returns `.none` —
              -- only the `_ => return .none` catch-all does, which is
              -- unreachable here.  We discharge this via the equation.
              refine ⟨σ', Inits.init InitVars.init_none, ?_⟩
              simp only [pure, StateT.pure, Prod.mk.injEq, Except.ok.injEq] at Helim
              -- Helim.1 : sts = [Imperative.Stmt.cmd (CmdExt.call procName args md)]
              rw [Helim.1]; exact Heval
            · -- `a_opt = some s'`: this is the genuine call-elim case.
              rename_i s' heq_some
              simp only [pure, StateT.pure, Prod.mk.injEq, Except.ok.injEq] at Helim
              -- B1/B2: callElimCmd_call_eq + Heval inversion to call_sem.
              rw [Helim.1]
              have ⟨ρ_inner, hstep_call, htail⟩ : ∃ ρ_inner,
                  Imperative.StepStmtStar Expression (EvalCommandContract π)
                      (EvalPureFunc φ)
                      (.stmt (Imperative.Stmt.cmd
                        (CmdExt.call procName args md))
                          ⟨σ, δ, false⟩)
                      (.terminal ρ_inner) ∧
                  Imperative.StepStmtStar Expression (EvalCommandContract π)
                      (EvalPureFunc φ)
                      (.stmts [] ρ_inner)
                      (.terminal ⟨σ', δ, f⟩) := by
                unfold EvalStatementsContract Imperative.EvalStmtsSmall at Heval
                match Heval with
                | .step _ _ _ .step_stmts_cons hrest =>
                  exact Imperative.seq_reaches_terminal Expression
                    (EvalCommandContract π) (EvalPureFunc φ) hrest
              -- htail forces ρ_inner = ⟨σ',δ,f⟩.
              have hρ_inner_eq : ρ_inner = ⟨σ', δ, f⟩ := by
                match htail with
                | .step _ _ _ .step_stmts_nil hrest' =>
                  cases hrest' with
                  | refl => rfl
                  | step _ _ _ h _ => exact absurd h (by intro h; cases h)
              subst hρ_inner_eq
              -- Invert `hstep_call : StepStmtStar (.cmd (.call …)) … → terminal` to extract Hcc.
              have Hcc : EvalCommandContract π δ σ
                  (CmdExt.call procName args md) σ' f := by
                match hstep_call with
                | .step _ _ _ (.step_cmd hcc) hrest =>
                  cases hrest with
                  | refl =>
                    -- call_sem is failure-flag-parameterized; Hcc carries the
                    -- caller's outer flag `f` here.
                    exact hcc
                  | step _ _ _ h _ => exact absurd h (by intro h; cases h)
              cases Hcc with
              | call_sem lkup hCallArgsIn hCallArgsLhs Hevalargs Hevalouts
                          Hwfval Hwfvars Hwfb Hwf2 HdefOver
                          Hinitin Hinitout Hpre_def Hpre_iff Hhav1 Hpost Hrd
                          Hupdate =>
                -- call_sem implicits: lhs σ₀ inArgs oVals argVals σA σAO σO proc modvals.
                rename_i lhs σ₀ inArgs oVals argVals σA σAO σO proc modvals
                -- Dispatch on the source-side failure flag `f`.
                --   * `f = false`: success arm — preconditions all hold, write
                --     back via `H_asserts_zip + H_havocs + H_assumes_zip`,
                --     glue via `EvalCallElim_glue`.
                --   * `f = true`:  failure arm — at least one precondition
                --     fails, write back via `H_asserts_zip_fail + H_havocs_poly
                --     + H_assumes_zip_poly`, glue via `EvalCallElim_glue_fail`.
                cases f with
                | true =>
                  -- Stage 6 failure arm: derive bool-totality witness via
                  -- Hwfcallsite → boolTyped, build failing assert chain, glue
                  -- with EvalCallElim_glue_fail.  Delegated to a sibling
                  -- private theorem for proof-body manageability.
                  exact callElimStatementCorrect_terminal_call_arm_fail
                    Hp Hwfc Hwf Hgenrel Hwfcallsite heq_ce
                    lkup hCallArgsIn hCallArgsLhs Hevalargs Hevalouts
                    Hwfval Hwfvars Hwfb Hwf2
                    Hinitin Hinitout Hpre_def Hpre_iff Hhav1 Hpost Hrd
                    Hupdate
                | false =>
                -- Re-synthesize the legacy combined `Hpre` from the new
                -- bool-indicator-shaped premises.  At this destructure site `Hcc`
                -- is pinned to `failed = false`, so the iff yields universal
                -- eval-tt over non-Free preconditions only — exactly what
                -- the L4 callElim asserts chain (which filters out Free) needs.
                have Hpre_evalTt :
                    ∀ pre, (Procedure.Spec.getCheckExprs proc.spec.checkedPreconditions).contains pre →
                      δ σAO pre = .some Imperative.HasBool.tt :=
                  Hpre_iff.mp rfl
                have Hpre :
                    ∀ pre, (Procedure.Spec.getCheckExprs proc.spec.checkedPreconditions).contains pre →
                      Imperative.isDefinedOver
                        (Imperative.HasVarsPure.getVars (P:=Expression)) σAO pre ∧
                      δ σAO pre = .some Imperative.HasBool.tt :=
                  fun pre h => ⟨Hpre_def pre h, Hpre_evalTt pre h⟩
                -- B1-tail: destructure heq_ce via callElimCmd_call_eq.
                obtain ⟨proc', argTrips, outTrips, genOldIdents, oldTys,
                        asserts, assumes,
                        s_arg, s_out, s_old,
                        Hfind, Heqarg, Heqout, Heqold, Holdtylen,
                        Hsts_struct, HassertsShape, HassumesShape⟩ :=
                  callElimCmd_call_eq heq_ce
                have Heqargs : argTrips.unzip.snd =
                    CallArg.getInputExprs args :=
                  genArgExprIdentsTrip_snd Heqarg
                have Heqouts : outTrips.unzip.snd =
                    CallArg.getLhs args :=
                  genOutExprIdentsTrip_snd Heqout
                -- Hoisted: arg-expr vars defined in σ (via Hevalargs).
                have HargIsDef : Imperative.isDefined σ
                    (List.flatMap
                      (Imperative.HasVarsPure.getVars (P:=Expression))
                      inArgs) :=
                  evalExpressions_isDefined_flatMap Hevalargs
                -- Hoisted abbreviations for argument/output temp idents.
                let argTemps : List Expression.Ident :=
                  argTrips.unzip.fst.unzip.fst
                let outTemps : List Expression.Ident :=
                  outTrips.unzip.fst.unzip.fst
                -- Generic δ-fvar lookup: `δ σ (fvar v) = σ v` for any σ.
                have δ_fvar_eq := delta_fvar_eq_of_wfvars Hwfvars (delta := δ)
                -- C1: aux facts derived from the destructured binders.
                have HargTemp :
                    Forall (fun x => isTempIdent x) argTemps :=
                  genArgExprIdentsTrip_isTempIdent Heqarg
                have HoutTemp :
                    Forall (fun x => isTempIdent x) outTemps :=
                  genOutExprIdentsTrip_isTempIdent Heqout
                have HoldIdentsTemp :
                    Forall (fun x => isOldTempIdent x) genOldIdents :=
                  genOldExprIdents_isOldTempIdent Heqold
                have Hgennd' :
                    (γ.genState.generated.reverse ++
                      argTemps ++ outTemps ++ genOldIdents).Nodup := by
                  apply genTrips_combined_nodup Heqarg Heqout Heqold
                  exact Hgenrel.wfgen
                -- Hgennd' nodup → 3-segment Nodup + arg/out/old σ-fresh + lifted to σ'.
                obtain ⟨Hgennd, HndefArg_σ, HndefOut_σ, HndefOld_σ, Hndefgen⟩ :=
                  fresh_triple_σ_facts Hgenrel Hgennd' HargTemp HoutTemp
                    HoldIdentsTemp Hupdate
                -- ── Length facts ──
                -- argTrips.length = argVals.length
                have Hargtriplen : argTrips.length = argVals.length := by
                  rw [← List.unzip_snd_length argTrips, Heqargs, hCallArgsIn]
                  exact EvalExpressionsLength Hevalargs
                -- outTrips.length = oVals.length
                have Houttriplen : outTrips.length = oVals.length := by
                  rw [← List.unzip_snd_length outTrips, Heqouts, hCallArgsLhs]
                  exact ReadValuesLength Hevalouts
                have HargTempsLen : argTemps.length = argVals.length := by
                  simp [argTemps, List.unzip_eq_map, Hargtriplen]
                have HoutTempsLen : outTemps.length = oVals.length := by
                  simp [outTemps, List.unzip_eq_map, Houttriplen]
                -- C1: Derive Hinoutnd from the call_sem InitStates binders.
                have Hinnd_io : (proc.header.inputs.keys).Nodup :=
                  InitStatesNodup Hinitin
                have Houtnd_io : (proc.header.outputs.keys).Nodup :=
                  InitStatesNodup Hinitout
                have Hindef_io :
                    Imperative.isDefined σA (proc.header.inputs.keys) :=
                  InitStatesDefined Hinitin
                have Houtndef_io :
                    Imperative.isNotDefined σA (proc.header.outputs.keys) :=
                  InitStatesNotDefined Hinitout
                have Hiodisj :
                    (proc.header.inputs.keys).Disjoint
                      (proc.header.outputs.keys) := by
                  intro x Hin1 Hin2
                  exact σ_some_contradiction
                    (Hindef_io x Hin1) (Houtndef_io x Hin2)
                have Hinoutnd :
                    (proc.header.inputs.keys ++
                      proc.header.outputs.keys).Nodup := by
                  rw [List.nodup_append]
                  refine ⟨Hinnd_io, Houtnd_io, ?_⟩
                  intro a Ha b Hb Heq
                  subst Heq
                  exact Hiodisj Ha Hb
                -- C2: bind `oldVars` (filter from Hsts_struct) for HoldVals/Holdtriplen.
                let oldVars : List Expression.Ident := callElim_oldVars proc' args
                -- `oldVars ⊆ lhs` because the filter narrows `lhs` ↪ `oldVars`.
                -- `Hevalouts : ReadValues σ lhs oVals` then forces every
                -- element of `lhs` (and hence `oldVars`) defined in σ.
                have HrdOldDef : Imperative.isDefined σ oldVars := by
                  intro g Hg
                  have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
                    (List.mem_filter.mp Hg).1
                  -- `hCallArgsLhs : CallArg.getLhs args = lhs` (forward).
                  have Hg_in_lhs : g ∈ lhs := hCallArgsLhs ▸ Hg_in_getLhs
                  have Hlhs_def : Imperative.isDefined σ lhs :=
                    ReadValuesIsDefined Hevalouts
                  exact Hlhs_def g Hg_in_lhs
                -- Existential reading of `oldVars` against σ.
                obtain ⟨oldVals, HoldVals⟩ :=
                  isDefinedReadValues HrdOldDef
                -- Length facts.
                have HoldValsLen : oldVals.length = oldVars.length :=
                  (ReadValuesLength HoldVals).symm
                -- genOld = oldTys = oldVars length facts for trip-shape.
                have HgenOldLen : genOldIdents.length = oldVars.length :=
                  genOldExprIdents_length Heqold
                have HoldTysLen : oldTys.length = oldVars.length := Holdtylen
                have HgenOldOldValsLen : genOldIdents.length = oldVals.length := by
                  rw [HgenOldLen, ← HoldValsLen]
                have Holdtriplen :
                    oldVals.length =
                      ((genOldIdents.zip oldTys).zip oldVars).length := by
                  rw [HoldValsLen]
                  simp [List.length_zip, HgenOldLen, HoldTysLen]
                -- C3: σ'' = updatedStates σ' (argTemps++outTemps++genOldIdents) (...).
                have Hinit :=
                  updatedStatesInit (P := Expression) ?_ ?_ ?_ (σ := σ')
                    (hs := argTemps
                            ++ outTemps
                            ++ genOldIdents)
                    (vs := argVals ++ oVals ++ oldVals)
                rotate_left
                · -- length of `hs` = length of `vs` (segment-wise close)
                  simp [argTemps, outTemps, List.length_append, List.unzip_eq_map, Hargtriplen, Houttriplen, HgenOldOldValsLen]
                · exact Hndefgen
                · exact Hgennd
                -- σ'' is the updatedStates σ' … form; D2 may use InitsUpdatesComm.
                refine ⟨updatedStates σ'
                          (argTemps
                            ++ outTemps
                            ++ genOldIdents)
                          (argVals ++ oVals ++ oldVals), ?_, ?_⟩
                · -- First conjunct: Inits σ' σ''.
                  exact InitStatesInits Hinit
                · -- L1-L6 chain via EvalCallElim_glue.
                  obtain ⟨HargNd, HoutNd, HoldNd,
                          HargOutDisj, HargOldDisj, HoutOldDisj⟩ :=
                    List.nodup_3_decompose Hgennd
                  -- argTemps fresh from σ; arg-expr vars defined in σ ⇒ disjoint.
                  have HdefVars : Imperative.isDefined σ
                      (List.flatMap
                        (Imperative.HasVarsPure.getVars (P:=Expression))
                        (CallArg.getInputExprs args)) :=
                    hCallArgsIn ▸ HargIsDef
                  have HargExprDisj :
                      argTemps.Disjoint
                        (List.flatMap
                          (Imperative.HasVarsPure.getVars (P:=Expression))
                          argTrips.unzip.snd) := by
                    intro x Hin1 Hin2
                    -- Rewrite Hin2 via Heqargs so we can use HdefVars.
                    rw [Heqargs] at Hin2
                    -- HndefArg_σ says σ x = none; HdefVars says (σ x).isSome.
                    exact notin_of_isSome_isNotDefined (HdefVars x Hin2) HndefArg_σ Hin1
                  -- ── L1: argInit ──
                  have HevalArgs' :
                      EvalExpressions (P:=Core.Expression) δ σ
                        argTrips.unzip.snd argVals := by
                    rw [Heqargs, hCallArgsIn]
                    exact Hevalargs
                  have HL1 :
                      EvalStatementsContract π φ ⟨σ, δ, false⟩
                        (Core.Transform.createInits argTrips md)
                        ⟨updatedStates σ argTemps
                          argVals, δ, false⟩ :=
                    H_inits Hwfvars Hwfval Hwfc HargExprDisj HargNd
                      HevalArgs' HndefArg_σ
                  -- L2: outInit (lift Hevalouts to σ_arg via readValues_updatedStates).
                  have Hlhs_isLocl :
                      Imperative.isDefined σ lhs :=
                    ReadValuesIsDefined Hevalouts
                  have HlhsDisjArg : lhs.Disjoint argTemps := fun x Hin1 Hin2 =>
                    notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefArg_σ Hin2
                  have HlhsDisjOut : lhs.Disjoint outTemps := fun x Hin1 Hin2 =>
                    notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefOut_σ Hin2
                  have HlhsDisjOld : lhs.Disjoint genOldIdents := fun x Hin1 Hin2 =>
                    notin_of_isSome_isNotDefined (Hlhs_isLocl x Hin1) HndefOld_σ Hin2
                  -- Out-temp Nodup append form for `H_initVars`.
                  have HoutSnd_eq_lhs : outTrips.unzip.snd = lhs := by
                    rw [Heqouts, hCallArgsLhs]
                  have HlhsNd : lhs.Nodup := callArgsLhs_nodup_of_wf Hwf hCallArgsLhs
                  have Hout_nd_app :
                      List.Nodup (outTemps
                                  ++ outTrips.unzip.snd) := by
                    rw [HoutSnd_eq_lhs]
                    rw [List.nodup_append]
                    refine ⟨HoutNd, HlhsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HlhsDisjOut Hb Ha
                  -- ReadValues over the σ_arg store.
                  have HrdOuts_argLayer :
                      ReadValues
                        (updatedStates σ argTemps
                          argVals)
                        outTrips.unzip.snd oVals := by
                    exact HoutSnd_eq_lhs ▸ readValues_updatedStates HargTempsLen HlhsDisjArg Hevalouts
                  -- outTemps undefined in σ_arg (argTemps disjoint from outTemps).
                  have HndefOut_argLayer :
                      Imperative.isNotDefined
                        (updatedStates σ argTemps
                          argVals)
                        outTemps := by
                    intro v Hv
                    have Hv_notin : v ∉ argTemps := fun Hin => HargOutDisj Hin Hv
                    exact (updatedStates_get_notin (σ:=σ) (ks:=argTemps) (vs:=argVals) Hv_notin) ▸ HndefOut_σ v Hv
                  have HL2 :
                      EvalStatementsContract π φ
                        ⟨updatedStates σ argTemps
                          argVals, δ, false⟩
                        (Core.Transform.createInitVars outTrips md)
                        ⟨updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals, δ, false⟩ :=
                    H_initVars Hwfvars Hout_nd_app HrdOuts_argLayer
                      HndefOut_argLayer
                  -- L3: oldInit; oldTrips := (genOldIdents.zip oldTys).zip oldVars.
                  let oldTrips :
                      List ((Expression.Ident × Expression.Ty) ×
                             Expression.Ident) :=
                    (genOldIdents.zip oldTys).zip oldVars
                  have HoldTripsFst :
                      oldTrips.unzip.fst.unzip.fst = genOldIdents := by
                    have HzipLen :
                        (genOldIdents.zip oldTys).length = oldVars.length := by
                      simp [List.length_zip, HgenOldLen, HoldTysLen]
                    show ((genOldIdents.zip oldTys).zip oldVars).unzip.fst.unzip.fst
                          = genOldIdents
                    simp [List.unzip_eq_map, List.map_fst_zip, HzipLen,
                          HgenOldLen, HoldTysLen]
                  have HoldTripsSnd :
                      oldTrips.unzip.snd = oldVars := by
                    have HzipLen :
                        (genOldIdents.zip oldTys).length = oldVars.length := by
                      simp [List.length_zip, HgenOldLen, HoldTysLen]
                    rw [show oldTrips = (genOldIdents.zip oldTys).zip oldVars
                        from rfl]
                    simp [List.unzip_eq_map, List.map_snd_zip, HzipLen]
                  -- Disjointness of oldVars from argTemps/outTemps and
                  -- oldVars Nodup follow from `oldVars ⊆ lhs`.
                  have HoldVars_sub_lhs : ∀ g ∈ oldVars, g ∈ lhs := by
                    intro g Hg
                    have Hg_in_getLhs : g ∈ CallArg.getLhs args :=
                      (List.mem_filter.mp Hg).1
                    exact hCallArgsLhs ▸ Hg_in_getLhs
                  have oldVars_disj_via_lhs :
                      ∀ {ks : List Expression.Ident}, lhs.Disjoint ks → oldVars.Disjoint ks :=
                    fun H x Hin1 Hin2 => H (HoldVars_sub_lhs x Hin1) Hin2
                  have HoldVarsDisjArg : oldVars.Disjoint argTemps := oldVars_disj_via_lhs HlhsDisjArg
                  have HoldVarsDisjOut : oldVars.Disjoint outTemps := oldVars_disj_via_lhs HlhsDisjOut
                  have HoldVarsDisjOldT : oldVars.Disjoint genOldIdents := oldVars_disj_via_lhs HlhsDisjOld
                  have HoldVarsNd : oldVars.Nodup := by
                    -- oldVars ⊆ (CallArg.getLhs args) = lhs via filter sublist.
                    have HlhsArgs_nd : (CallArg.getLhs args).Nodup := by
                      exact hCallArgsLhs ▸ HlhsNd
                    exact List.Sublist.nodup List.filter_sublist HlhsArgs_nd
                  -- Lift HoldVals through 2 layers via readValues_updatedStates.
                  have HrdOlds_outLayer :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldVars oldVals :=
                    readValues_updatedStates HoutTempsLen HoldVarsDisjOut
                      (readValues_updatedStates HargTempsLen HoldVarsDisjArg HoldVals)
                  -- Rewrite oldVars to oldTrips.unzip.snd for H_initVars.
                  have HrdOldTrips :
                      ReadValues
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.snd oldVals := by
                    exact HoldTripsSnd ▸ HrdOlds_outLayer
                  -- genOldIdents disjoint from argTemps/outTemps ⇒ undef in σ_out.
                  have HndefOld_outLayer :
                      Imperative.isNotDefined
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        genOldIdents := by
                    intro v Hv
                    have Hv_notin_out :
                        ¬ v ∈ outTemps := by
                      intro Hin
                      exact HoutOldDisj Hin Hv
                    have Hv_notin_arg :
                        ¬ v ∈ argTemps := by
                      intro Hin
                      exact HargOldDisj Hin Hv
                    rw [updatedStates_2layer_get_notin
                          Hv_notin_arg Hv_notin_out]
                    exact HndefOld_σ v Hv
                  -- Rewrite genOldIdents to oldTrips.unzip.fst.unzip.fst for H_initVars.
                  have HndefOldTrips :
                      Imperative.isNotDefined
                        (updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.fst.unzip.fst := by
                    exact HoldTripsFst ▸ HndefOld_outLayer
                  -- Nodup precondition: (genOldIdents ++ oldVars).Nodup.
                  have HoldTrips_nd_app :
                      List.Nodup
                        (oldTrips.unzip.fst.unzip.fst ++ oldTrips.unzip.snd) := by
                    rw [HoldTripsFst, HoldTripsSnd]
                    rw [List.nodup_append]
                    refine ⟨HoldNd, HoldVarsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HoldVarsDisjOldT Hb Ha
                  have HL3 :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates σ
                            argTemps argVals)
                          outTemps oVals, δ, false⟩
                        (Core.Transform.createInitVars oldTrips md)
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩ :=
                    H_initVars Hwfvars HoldTrips_nd_app HrdOldTrips
                      HndefOldTrips
                  -- D2: L4 (asserts), L5 (havocs), L6 (assumes) chain.
                  rw [Hsts_struct]
                  -- L5: build post-havoc store σ_havoc by HavocVars segments on σ' = σ.update lhs modvals.
                  have Hhav_old :
                      HavocVars
                        (updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals)
                        lhs
                        (updatedStates
                          (updatedStates
                            (updatedStates σ'
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals) :=
                    havocVars_3layer_lift HlhsDisjArg HlhsDisjOut
                      (HoldTripsFst ▸ HlhsDisjOld) (UpdateStatesHavocVars Hupdate)
                  -- isDefined σ_old lhs (via 3-layer extension monotone).
                  have HlhsDef_old :
                      Imperative.isDefined
                        (updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals) lhs :=
                    isDefined_3layer_lift HlhsDisjArg HlhsDisjOut
                      (HoldTripsFst ▸ HlhsDisjOld) Hlhs_isLocl
                  -- HL5: 3-layer havocs over lhs from σ_old → σ_havoc (uses hCallArgsLhs.symm).
                  have HL5_pre :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩
                        (Core.Transform.createHavocs lhs md)
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ'
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩ :=
                    H_havocs_poly Hwfvars HlhsDef_old Hhav_old
                  -- Equality: σ_havoc (3-layer over σ') = σ'' (flat) via zip-append.
                  have HoldFstLen :
                      oldTrips.unzip.fst.unzip.fst.length = oldVals.length := by
                    rw [HoldTripsFst, HgenOldLen, HoldValsLen]
                  have Hflatten_eq :
                      updatedStates σ'
                        (argTemps ++
                          outTemps ++ genOldIdents)
                        (argVals ++ oVals ++ oldVals) =
                      updatedStates
                        (updatedStates
                          (updatedStates σ'
                            argTemps argVals)
                          outTemps oVals)
                        oldTrips.unzip.fst.unzip.fst oldVals := by
                    rw [HoldTripsFst]
                    simp only [updatedStates]
                    -- (a ++ b ++ c).zip (av ++ bv ++ cv) = a.zip av ++ b.zip bv ++ c.zip cv.
                    have Hzip1 :
                        ((argTemps ++
                          outTemps) ++ genOldIdents).zip
                          ((argVals ++ oVals) ++ oldVals) =
                        (argTemps ++
                          outTemps).zip
                          (argVals ++ oVals) ++
                          genOldIdents.zip oldVals :=
                      List.zip_append (by
                        rw [List.length_append, List.length_append,
                            HargTempsLen, HoutTempsLen])
                    have Hzip2 :
                        (argTemps ++
                          outTemps).zip
                          (argVals ++ oVals) =
                        argTemps.zip argVals ++
                          outTemps.zip oVals :=
                      List.zip_append HargTempsLen
                    rw [Hzip1, Hzip2]
                    rw [updatedStates'App, updatedStates'App]
                  have HL5 :
                      EvalStatementsContract π φ
                        ⟨updatedStates
                          (updatedStates
                            (updatedStates σ
                              argTemps argVals)
                            outTemps oVals)
                          oldTrips.unzip.fst.unzip.fst oldVals, δ, false⟩
                        (Core.Transform.createHavocs (CallArg.getLhs args) md)
                        ⟨updatedStates σ'
                          (argTemps ++
                            outTemps ++ genOldIdents)
                          (argVals ++ oVals ++ oldVals), δ, false⟩ := by
                    rw [Hflatten_eq, hCallArgsLhs]
                    exact HL5_pre
                  -- D2a: per-precondition payload for L4 (asserts).
                  obtain ⟨HprocEq, c_in_postExprs_of_proc'⟩ :=
                    procEq_and_postExprs_bridge Hp Hfind lkup
                  -- Specialize Hwfcallsite (over `proc`) to the call form;
                  -- spike uses `proc'` which HprocEq bridges.
                  obtain ⟨HpreVarsFresh, HpostVarsFresh, HargVarsNotInLhs,
                          HinoutFresh, HargVarsNotInOutKeys,
                          HargVarsNotInInKeys, HoutAlign⟩ :=
                    Hwfcallsite.specialize (procName := procName)
                      (args := args) (md := md) rfl lkup
                  -- Lift HpostVarsFresh to take c ∈ proc'.spec.postconditions.values.
                  have HpostVarsFresh_via_c :
                      ∀ c ∈ proc'.spec.postconditions.values,
                      ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) c.expr,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
                        v ∉ CallArg.getLhs args := by
                    intro c Hc_in v Hv
                    exact HpostVarsFresh c.expr (c_in_postExprs_of_proc' c Hc_in) v Hv
                  -- C-aux: hoisted disjointness facts (used by L4 + L6).
                  have HinputsFresh :
                      ∀ v ∈ proc.header.inputs.keys,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
                    intro v Hv
                    exact HinoutFresh v (List.mem_append.mpr (Or.inl Hv))
                  have HoutputsFresh :
                      ∀ v ∈ proc.header.outputs.keys,
                        ¬ isTempIdent v ∧ ¬ isOldTempIdent v := by
                    intro v Hv
                    exact HinoutFresh v (List.mem_append.mpr (Or.inr Hv))
                  -- inputs.keys ∩ argTemps = ∅ (inputs not tmp_).
                  have HinKeys_disj_argTemps : proc.header.inputs.keys.Disjoint argTemps :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HargTemp (HinputsFresh v Hv1).1 Hv2
                  have HinKeys_disj_outTemps : proc.header.inputs.keys.Disjoint outTemps :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HoutTemp (HinputsFresh v Hv1).1 Hv2
                  have HinKeys_disj_olds : proc.header.inputs.keys.Disjoint genOldIdents :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HoldIdentsTemp (HinputsFresh v Hv1).2 Hv2
                  have HoutKeys_disj_argTemps : proc.header.outputs.keys.Disjoint argTemps :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HargTemp (HoutputsFresh v Hv1).1 Hv2
                  have HoutKeys_disj_outTemps : proc.header.outputs.keys.Disjoint outTemps :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HoutTemp (HoutputsFresh v Hv1).1 Hv2
                  have HoutKeys_disj_olds : proc.header.outputs.keys.Disjoint genOldIdents :=
                    fun v Hv1 Hv2 => notMem_of_Forall_neg HoldIdentsTemp (HoutputsFresh v Hv1).2 Hv2
                  -- inputs.keys ∩ lhs = ∅: σ-undefined inputs vs σ-defined lhs.
                  have HinKeys_disj_lhs :
                      proc.header.inputs.keys.Disjoint lhs := fun v Hv1 Hv2 =>
                    notin_of_isSome_isNotDefined (Hlhs_isLocl v Hv2) (InitStatesNotDefined Hinitin) Hv1
                  -- outputs.keys ∩ lhs = ∅: σA-undefined outputs vs σ-defined lhs.
                  have HoutKeys_disj_lhs :
                      proc.header.outputs.keys.Disjoint lhs := by
                    intro v Hv1 Hv2
                    have HvσA_none : σA v = none := Houtndef_io v Hv1
                    have HvNotInInputs : v ∉ proc.header.inputs.keys :=
                      fun h => Hiodisj h Hv1
                    have HvσA_eq_σ : σA v = σ v :=
                      initStates_get_notin Hinitin HvNotInInputs
                    have Hvσ_none : σ v = none := by
                      rw [← HvσA_eq_σ]; exact HvσA_none
                    exact σ_some_contradiction (Hlhs_isLocl v Hv2) Hvσ_none
                  -- Restrict to the filtered preconditions.
                  let presFiltered : List (CoreLabel × Procedure.Check) :=
                    proc.spec.checkedPreconditions
                  -- Bind σAO definedness/eval-tt for each filtered entry.
                  -- Hpre's domain is `getCheckExprs presFiltered.contains`, so
                  -- mapping `entry ∈ presFiltered` to that contains-membership
                  -- is direct: it's the membership of `entry.snd.expr` in
                  -- `getCheckExprs presFiltered` (no filter-bridge needed).
                  have HpreFiltered :
                      ∀ entry ∈ presFiltered,
                        Imperative.isDefinedOver
                          (Imperative.HasVarsPure.getVars (P:=Expression))
                          σAO entry.snd.expr ∧
                        δ σAO entry.snd.expr = some Imperative.HasBool.tt := by
                    intro entry Hentry
                    apply Hpre entry.snd.expr
                    rw [List.contains_iff_mem]
                    simp only [Procedure.Spec.getCheckExprs,
                               ListMap.values_eq_map_snd, List.mem_map,
                               List.map_map]
                    refine ⟨entry, Hentry, ?_⟩
                    rfl
                  -- Pre-var freshness lemma against σ_old / σAO.
                  have HpresVarsFresh' :
                      ∀ entry ∈ presFiltered,
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression) entry.snd.expr,
                          ¬ isTempIdent v ∧ ¬ isOldTempIdent v ∧
                          v ∉ CallArg.getLhs args := fun entry Hentry v Hv =>
                    HpreVarsFresh entry.snd.expr
                      (filterCheck_mem_getCheckExprs Hentry) v Hv
                  -- HpresPayload (D2a output).
                  have HpresPayload :
                      ∀ entry ∈ presFiltered,
                        Imperative.invStores σAO
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals)
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            ((proc.header.inputs.keys ++
                                proc.header.outputs.keys) ++
                              (argTemps ++ lhs))) ∧
                        (argTemps ++ lhs).Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) ∧
                        δ σAO entry.snd.expr = some Imperative.HasBool.tt := by
                    intro entry Hentry
                    -- Unpack per-entry facts.
                    have HpreEnt := HpreFiltered entry Hentry
                    -- preVars are not tmp_/old_ and not in lhs.
                    have HfreshEnt := HpresVarsFresh' entry Hentry
                    -- (1) Hpred_disj: (argT ++ lhs).Disjoint preVars.
                    have Hpred_disj :
                        (argTemps ++ lhs).Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) := by
                      intro x Hin1 Hin2
                      cases List.mem_append.mp Hin1 with
                      | inl HxArg =>
                        -- x ∈ argT (tmp_), x ∈ preVars (not tmp_).
                        have HxTemp : isTempIdent x := (List.Forall_mem_iff.mp HargTemp) x HxArg
                        have HxNotTemp : ¬ isTempIdent x :=
                          (HfreshEnt x Hin2).1
                        exact HxNotTemp HxTemp
                      | inr HxLhs =>
                        -- x ∈ lhs, x ∉ lhs via HfreshEnt + hCallArgsLhs.
                        have HxNotInLhs : x ∉ CallArg.getLhs args :=
                          (HfreshEnt x Hin2).2.2
                        rw [hCallArgsLhs] at HxNotInLhs
                        exact HxNotInLhs HxLhs
                    -- (2) Hinv: invStores σAO σ_old (preVars.removeAll ...).
                    have Hinv :
                        Imperative.invStores σAO
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals)
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            ((proc.header.inputs.keys ++
                                proc.header.outputs.keys) ++
                              (argTemps ++ lhs))) := by
                      simp only [Imperative.invStores, Imperative.substStores]
                      intros k1 k2 Hkin
                      obtain ⟨rfl, Hk1_pre, Hk1_notin_inputs, Hk1_notin_outputs,
                              Hk1_notin_argT, _Hk1_notin_lhs⟩ :=
                        zip_removeAll4_decompose Hkin
                      -- preVar k1 fresh facts (not tmp_, not old_, not in lhs).
                      have HfreshK := HfreshEnt k1 Hk1_pre
                      have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
                      have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
                      -- k1 ∉ outT (since outT are tmp_).
                      have Hk1_notin_outT : k1 ∉ outTemps :=
                        notMem_of_Forall_neg HoutTemp Hk1_notTemp
                      -- k1 ∉ genOldIdents (since olds are old_).
                      have Hk1_notin_olds : k1 ∉ genOldIdents :=
                        notMem_of_Forall_neg HoldIdentsTemp Hk1_notOld
                      -- σ_old k1 = σ k1 by 3-layer fall-through.
                      have Hold_eq_σ :
                          (updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals) k1 = σ k1 := by
                        have Hk1_notin_oldFst :
                            k1 ∉ oldTrips.unzip.fst.unzip.fst := by
                          rw [HoldTripsFst]; exact Hk1_notin_olds
                        exact updatedStates_3layer_get_notin
                          Hk1_notin_argT Hk1_notin_outT Hk1_notin_oldFst
                      -- σAO k1 = σ k1 via Hinitout/Hinitin fall-through.
                      have HAO_eq_σ : σAO k1 = σ k1 := by
                        rw [initStates_get_notin Hinitout Hk1_notin_outputs,
                            initStates_get_notin Hinitin Hk1_notin_inputs]
                      -- Conclude: σAO k1 = σ_old k1.
                      rw [HAO_eq_σ, Hold_eq_σ]
                    refine ⟨Hinv, Hpred_disj, ?_⟩
                    exact HpreEnt.2
                  -- D2b: per-postcondition payload (HpostFiltered, HpostSubFresh).
                  let postsFiltered : List (CoreLabel × Procedure.Check) :=
                    proc.spec.postconditions.filter
                      (fun (_, c) => c.attr ≠ .Free)
                  -- D2c: σ_R1 + L6 substStores/substDefined facts.
                  let σ_R1 : CoreStore :=
                    updatedStates σO genOldIdents oldVals
                  -- σ_havoc abbreviation (matches HL5's RHS).
                  let σ_havoc : CoreStore :=
                    updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals)
                  -- Positional read of σ_R1 on genOldIdents.
                  have HrdR1_olds : ReadValues σ_R1 genOldIdents oldVals := by
                    show ReadValues (updatedStates σO genOldIdents oldVals) _ _
                    exact readValues_updatedStatesSame HgenOldOldValsLen HoldNd
                  have σ_R1_read_olds :
                      ∀ (i : Nat) (Hi : i < genOldIdents.length)
                        (Hi' : i < oldVals.length),
                        σ_R1 (genOldIdents[i]'Hi) =
                          some (oldVals[i]'Hi') := fun i Hi Hi' =>
                    readValues_get HrdR1_olds (i:=i) (hi:=Hi) (hi':=Hi')
                  -- Filtered argument substitution shape.  Matches
                  -- `arg_subst_filtered` in `callElimCmd` (CallElim.lean:133).
                  let filtered_argSubst :
                      List (Expression.Ident × Expression.Ident) :=
                    (proc.header.inputs.keys.zip argTemps).filter
                      (fun pr =>
                        ¬ (proc.header.outputs.keys).contains pr.1)
                  let filtered_inputs : List Expression.Ident :=
                    filtered_argSubst.unzip.fst
                  let filtered_argTemps : List Expression.Ident :=
                    filtered_argSubst.unzip.snd
                  let filtered_ks : List Expression.Ident :=
                    proc.header.outputs.keys ++ filtered_inputs
                  let filtered_ks' : List Expression.Ident :=
                    lhs ++ filtered_argTemps
                  -- inputs.keys.length = argTemps.length (both = argVals.length).
                  have HinKeys_argTemps_len :
                      proc.header.inputs.keys.length = argTemps.length := by
                    have H1 : proc.header.inputs.keys.length =
                                argVals.length := InitStatesLength Hinitin
                    omega
                  -- Pre-filter zip's unzip = (inputs.keys, argTemps).
                  have Hzip_unzip :
                      (proc.header.inputs.keys.zip argTemps).unzip =
                      (proc.header.inputs.keys, argTemps) :=
                    List.unzip_zip HinKeys_argTemps_len
                  -- Filter sub-membership: each (id, t) ∈ filtered_argSubst
                  -- is in the original zip and satisfies the filter.
                  have Hfilter_in :
                      ∀ pr ∈ filtered_argSubst,
                        pr ∈ proc.header.inputs.keys.zip argTemps ∧
                        pr.1 ∉ proc.header.outputs.keys := by
                    intro pr Hpr
                    have := List.mem_filter.mp Hpr
                    refine ⟨this.1, ?_⟩
                    simpa using this.2
                  -- Length symmetry of filtered halves.
                  have Hfilt_len_sym :
                      filtered_inputs.length = filtered_argTemps.length := by
                    show filtered_argSubst.unzip.fst.length =
                          filtered_argSubst.unzip.snd.length
                    simp [List.unzip_eq_map]
                  -- outputs.keys.length = lhs.length (both = oVals.length).
                  have HoutKeys_lhs_len :
                      proc.header.outputs.keys.length = lhs.length := by
                    have H1 : proc.header.outputs.keys.length = oVals.length :=
                      InitStatesLength Hinitout
                    have H2 : lhs.length = oVals.length :=
                      ReadValuesLength Hevalouts
                    omega
                  -- Hkslen (Goal #4):
                  --   filtered_ks.length = filtered_ks'.length.
                  have Hkslen :
                      filtered_ks.length = filtered_ks'.length := by
                    show (proc.header.outputs.keys ++
                          filtered_inputs).length =
                         (lhs ++ filtered_argTemps).length
                    rw [List.length_append, List.length_append,
                        HoutKeys_lhs_len, Hfilt_len_sym]
                  -- filtered_inputs ⊆ inputs.keys (via the filter zip path).
                  have Hfilt_in_eq_map :
                      filtered_inputs = filtered_argSubst.map Prod.fst := by
                    show filtered_argSubst.unzip.fst = _
                    simp [List.unzip_eq_map]
                  have Hfilt_argT_eq_map :
                      filtered_argTemps = filtered_argSubst.map Prod.snd := by
                    show filtered_argSubst.unzip.snd = _
                    simp [List.unzip_eq_map]
                  have Hfilt_in_sub_inputs :
                      ∀ v ∈ filtered_inputs, v ∈ proc.header.inputs.keys := by
                    intro v Hv
                    have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
                      Hfilt_in_eq_map ▸ Hv
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HinZip := (Hfilter_in pr Hpr_in).1
                    have Hofzip := List.of_mem_zip HinZip
                    exact Hpr_eq.symm ▸ Hofzip.1
                  have Hfilt_argT_sub_argTemps :
                      ∀ v ∈ filtered_argTemps, v ∈ argTemps := by
                    intro v Hv
                    have Hv' : v ∈ filtered_argSubst.map Prod.snd :=
                      Hfilt_argT_eq_map ▸ Hv
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HinZip := (Hfilter_in pr Hpr_in).1
                    have Hofzip := List.of_mem_zip HinZip
                    exact Hpr_eq.symm ▸ Hofzip.2
                  have Hfilt_in_disj_outs :
                      filtered_inputs.Disjoint proc.header.outputs.keys := by
                    intro v Hv1 Hv2
                    have Hv' : v ∈ filtered_argSubst.map Prod.fst :=
                      Hfilt_in_eq_map ▸ Hv1
                    rcases List.mem_map.mp Hv' with ⟨pr, Hpr_in, Hpr_eq⟩
                    have HnotIn := (Hfilter_in pr Hpr_in).2
                    rw [Hpr_eq] at HnotIn
                    exact HnotIn Hv2
                  -- Hnd: substNodup of filtered_ks.zip filtered_ks'.
                  have Hnd : Imperative.substNodup
                      (filtered_ks.zip filtered_ks') := by
                    -- Unfold substNodup; rewrite via unzip_zip.
                    have HzipUnzip :
                        (filtered_ks.zip filtered_ks').unzip =
                          (filtered_ks, filtered_ks') :=
                      List.unzip_zip Hkslen
                    show ((filtered_ks.zip filtered_ks').unzip.fst ++
                          (filtered_ks.zip filtered_ks').unzip.snd).Nodup
                    rw [HzipUnzip]
                    -- Now goal: (filtered_ks ++ filtered_ks').Nodup.
                    show ((proc.header.outputs.keys ++ filtered_inputs) ++
                          (lhs ++ filtered_argTemps)).Nodup
                    -- ((outs ++ filt_in) ++ (lhs ++ filt_argT)).Nodup: each
                    -- Nodup + pairwise disjoints (C-aux supplies most).
                    have Hfilt_in_disj_lhs :
                        filtered_inputs.Disjoint lhs := by
                      intro v Hv1 Hv2
                      exact HinKeys_disj_lhs (Hfilt_in_sub_inputs v Hv1) Hv2
                    -- outs ∩ filt_argT: filt_argT ⊆ argTemps.
                    -- outputs ∩ argTemps = ∅ (HoutKeys_disj_argTemps).
                    have HoutKeys_disj_filt_argT :
                        proc.header.outputs.keys.Disjoint
                          filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HoutKeys_disj_argTemps Hv1
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- filt_in ∩ filt_argT: subsets of inputs / argTemps.
                    have Hfilt_in_disj_filt_argT :
                        filtered_inputs.Disjoint filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HinKeys_disj_argTemps
                        (Hfilt_in_sub_inputs v Hv1)
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- lhs ∩ filt_argT: lhs ∩ argTemps = ∅ (HlhsDisjArg).
                    have Hlhs_disj_filt_argT :
                        lhs.Disjoint filtered_argTemps := by
                      intro v Hv1 Hv2
                      exact HlhsDisjArg Hv1
                        (Hfilt_argT_sub_argTemps v Hv2)
                    -- inputs.keys.Nodup → Pairwise distinct fst on filter → Nodup on (filter.map fst).
                    have Hin_nd_pw :
                        List.Pairwise
                          (· ≠ ·) proc.header.inputs.keys :=
                      List.nodup_iff_pairwise_ne.mp Hinnd_io
                    have HargT_nd_pw :
                        List.Pairwise (· ≠ ·) argTemps :=
                      List.nodup_iff_pairwise_ne.mp HargNd
                    -- Pairwise-distinct on the full zip.
                    have Hzip_pw_fst :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.1 ≠ q.1)
                          (proc.header.inputs.keys.zip argTemps) := by
                      -- Lift via pairwise_map + map_fst_zip from inputs.keys Pairwise.
                      rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                                  p.1 ≠ q.1) =
                            (fun p q => Prod.fst p ≠ Prod.fst q) from rfl]
                      rw [← List.pairwise_map]
                      rw [List.map_fst_zip
                            (Nat.le_of_eq HinKeys_argTemps_len)]
                      exact Hin_nd_pw
                    have Hzip_pw_snd :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.2 ≠ q.2)
                          (proc.header.inputs.keys.zip argTemps) := by
                      rw [show (fun (p q : Expression.Ident × Expression.Ident) =>
                                  p.2 ≠ q.2) =
                            (fun p q => Prod.snd p ≠ Prod.snd q) from rfl]
                      rw [← List.pairwise_map]
                      rw [List.map_snd_zip
                            (Nat.le_of_eq HinKeys_argTemps_len.symm)]
                      exact HargT_nd_pw
                    -- Filter preserves Pairwise (sublist).
                    have Hfilt_pw_fst :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.1 ≠ q.1)
                          filtered_argSubst :=
                      List.Pairwise.sublist List.filter_sublist Hzip_pw_fst
                    have Hfilt_pw_snd :
                        List.Pairwise
                          (fun (p q :
                              Expression.Ident × Expression.Ident) =>
                            p.2 ≠ q.2)
                          filtered_argSubst :=
                      List.Pairwise.sublist List.filter_sublist Hzip_pw_snd
                    have Hfilt_in_nodup : filtered_inputs.Nodup := by
                      show filtered_argSubst.unzip.fst.Nodup
                      simp [List.unzip_eq_map]
                      rw [List.nodup_iff_pairwise_ne]
                      rw [List.pairwise_map]
                      exact Hfilt_pw_fst
                    have Hfilt_argT_nodup : filtered_argTemps.Nodup := by
                      show filtered_argSubst.unzip.snd.Nodup
                      simp [List.unzip_eq_map]
                      rw [List.nodup_iff_pairwise_ne]
                      rw [List.pairwise_map]
                      exact Hfilt_pw_snd
                    -- Step: assemble (filtered_ks ++ filtered_ks').Nodup.
                    -- = (outputs ++ filtered_inputs ++ lhs ++ filtered_argTemps).Nodup.
                    rw [List.nodup_append]
                    refine ⟨?_, ?_, ?_⟩
                    · -- (outputs ++ filtered_inputs).Nodup.
                      rw [List.nodup_append]
                      refine ⟨Houtnd_io, Hfilt_in_nodup, ?_⟩
                      intro a Ha b Hb Heq
                      subst Heq
                      exact Hfilt_in_disj_outs Hb Ha
                    · -- (lhs ++ filtered_argTemps).Nodup.
                      rw [List.nodup_append]
                      refine ⟨HlhsNd, Hfilt_argT_nodup, ?_⟩
                      intro a Ha b Hb Heq
                      subst Heq
                      exact Hlhs_disj_filt_argT Ha Hb
                    · -- (outputs ++ filtered_inputs).Disjoint
                      --   (lhs ++ filtered_argTemps).
                      intro a Ha b Hb Heq
                      subst Heq
                      rcases List.mem_append.mp Ha with HaOuts | HaIn <;>
                        rcases List.mem_append.mp Hb with HbLhs | HbArgT
                      · exact HoutKeys_disj_lhs HaOuts HbLhs
                      · exact HoutKeys_disj_filt_argT HaOuts HbArgT
                      · exact Hfilt_in_disj_lhs HaIn HbLhs
                      · exact Hfilt_in_disj_filt_argT HaIn HbArgT
                  -- Hdef: substDefined σ_R1 σ_havoc.
                  have HσO_def_outs :
                      Imperative.isDefined σO proc.header.outputs.keys :=
                    HavocVarsDefMonotone (InitStatesDefined Hinitout) Hhav1
                  have HσO_def_inputs :
                      Imperative.isDefined σO proc.header.inputs.keys :=
                    HavocVarsDefMonotone
                      (InitStatesDefMonotone (InitStatesDefined Hinitin) Hinitout) Hhav1
                  -- σ_R1 = σO off genOldIdents (single closure).
                  have σR1_off_olds :
                      ∀ {v}, v ∉ genOldIdents → σ_R1 v = σO v := fun Hv =>
                    updatedStates_get_notin Hv
                  have Hσ_R1_def_outs :
                      Imperative.isDefined σ_R1 proc.header.outputs.keys := fun v Hv =>
                    (show σ_R1 v = σO v from σR1_off_olds (HoutKeys_disj_olds Hv)) ▸ HσO_def_outs v Hv
                  have Hσ_R1_def_filt_in :
                      Imperative.isDefined σ_R1 filtered_inputs := fun v Hv =>
                    let Hv_in := Hfilt_in_sub_inputs v Hv
                    (show σ_R1 v = σO v from σR1_off_olds (HinKeys_disj_olds Hv_in)) ▸ HσO_def_inputs v Hv_in
                  -- σ_havoc definedness on lhs.
                  have Hσ_havoc_def_lhs :
                      Imperative.isDefined σ_havoc lhs := by
                    intro v Hv
                    show (updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v).isSome = true
                    have Hv_notin : v ∉ argTemps ++ outTemps ++ genOldIdents :=
                      List.notin_3_append_of (HlhsDisjArg Hv) (HlhsDisjOut Hv) (HlhsDisjOld Hv)
                    exact (updatedStates_get_notin Hv_notin) ▸ HavocVarsDefined (UpdateStatesHavocVars Hupdate) v Hv
                  -- σ_havoc definedness on filtered_argTemps.
                  have Hσ_havoc_def_filt_argT :
                      Imperative.isDefined σ_havoc filtered_argTemps := by
                    intro v Hv
                    have Hv_argT : v ∈ argTemps :=
                      Hfilt_argT_sub_argTemps v Hv
                    -- σ_havoc[v] for v ∈ argTemps: 3-layer updatedStatesDefined.
                    show (updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v).isSome = true
                    apply updatedStatesDefined
                    · simp [argTemps, outTemps, List.length_append, List.unzip_eq_map, Hargtriplen, Houttriplen, HgenOldOldValsLen]
                    · simp only [List.mem_append]
                      exact Or.inl (Or.inl Hv_argT)
                  -- Now assemble Hdef.
                  have Hdef : Imperative.substDefined σ_R1 σ_havoc
                      (filtered_ks.zip filtered_ks') :=
                    substDefined_of_app Hσ_R1_def_outs Hσ_R1_def_filt_in
                      Hσ_havoc_def_lhs Hσ_havoc_def_filt_argT
                  -- Hsubst: substStores σ_R1 σ_havoc.
                  have Hσ'_eq : σ' = updatedStates σ lhs modvals :=
                    UpdateStatesUpdated Hupdate
                  -- σ_R1 k = σ_havoc k for k off all touched layers.
                  have σR1_eq_σhavoc :
                      ∀ {k : Expression.Ident},
                        k ∉ proc.header.inputs.keys →
                        k ∉ proc.header.outputs.keys →
                        k ∉ argTemps → k ∉ outTemps →
                        k ∉ genOldIdents → k ∉ lhs →
                        σ_R1 k = σ_havoc k := by
                    intro k Hk_ins Hk_outs Hk_argT Hk_outT Hk_genOld Hk_lhs
                    have HσR1_σ : updatedStates σO genOldIdents oldVals k = σ k :=
                      σR1_eq_σ_for_notTouched Hinitin Hinitout Hhav1
                        Hk_ins Hk_outs Hk_genOld
                    have H5 : σ k = σ' k := by
                      rw [Hσ'_eq, updatedStates_get_notin Hk_lhs]
                    have Hk_notin_layered : k ∉ argTemps ++ outTemps ++ genOldIdents :=
                      List.notin_3_append_of Hk_argT Hk_outT Hk_genOld
                    have H6 : σ' k = σ_havoc k := by
                      show σ' k = updatedStates σ'
                        (argTemps ++ outTemps ++ genOldIdents)
                        (argVals ++ oVals ++ oldVals) k
                      rw [updatedStates_get_notin Hk_notin_layered]
                    show updatedStates σO genOldIdents oldVals k = σ_havoc k
                    rw [HσR1_σ, H5, H6]
                  -- modvals length = lhs length.
                  have HmodvalsLen : modvals.length = lhs.length := by
                    have := UpdateStatesLength Hupdate
                    omega
                  -- σO outputs = modvals (via Hrd).
                  -- σO inputs = σA inputs (via the σAO/σA fall-through chain).
                  -- σ_havoc on lhs = σ' lhs.
                  have Hσ_havoc_lhs_eq :
                      ∀ v ∈ lhs, σ_havoc v = σ' v := by
                    intro v Hv
                    have Hv_notin : v ∉ argTemps ++ outTemps ++ genOldIdents :=
                      List.notin_3_append_of (HlhsDisjArg Hv) (HlhsDisjOut Hv) (HlhsDisjOld Hv)
                    show updatedStates σ'
                      (argTemps ++
                        outTemps ++ genOldIdents)
                      (argVals ++ oVals ++ oldVals) v = σ' v
                    exact updatedStates_get_notin Hv_notin
                  -- σ_R1 on outputs = σO on outputs.
                  have Hσ_R1_outs_eq :
                      ∀ v ∈ proc.header.outputs.keys, σ_R1 v = σO v := fun v Hv =>
                    σR1_off_olds (HoutKeys_disj_olds Hv)
                  -- σ_R1 on inputs = σO on inputs.
                  have Hσ_R1_ins_eq :
                      ∀ v ∈ proc.header.inputs.keys, σ_R1 v = σO v := fun v Hv =>
                    σR1_off_olds (HinKeys_disj_olds Hv)
                  -- σO = σAO off outputs.keys (via Hhav1 + UpdateStatesUpdated).
                  have σO_eq_σAO_off_outs :
                      ∀ {v}, v ∉ proc.header.outputs.keys → σO v = σAO v := by
                    obtain ⟨ovh, Hup_havoc⟩ := HavocVarsUpdateStates Hhav1
                    intro v Hv
                    rw [UpdateStatesUpdated Hup_havoc, updatedStates_get_notin Hv]
                  -- σO on inputs = σA on inputs (Hhav1 preserves on non-outputs;
                  -- Hinitout preserves on non-outputs).
                  have HσO_ins_eq_σA :
                      ∀ v ∈ proc.header.inputs.keys, σO v = σA v := fun v Hv =>
                    let Hv_notin : v ∉ proc.header.outputs.keys := fun h => Hiodisj Hv h
                    (σO_eq_σAO_off_outs Hv_notin) ▸ initStates_get_notin Hinitout Hv_notin
                  -- σA on inputs = positional argVals (via Hinitin).
                  have HrdA : ReadValues σA proc.header.inputs.keys argVals :=
                    InitStatesReadValues Hinitin
                  -- ── Build Hsubst via parallel ReadValues over output / filtered-input pairs ──
                  have HinKVlen :
                      proc.header.inputs.keys.length = argVals.length :=
                    InitStatesLength Hinitin
                  -- σ_R1 reads inputs.keys → argVals (full).
                  have Hrd_R1_in_full :
                      ReadValues σ_R1 proc.header.inputs.keys argVals := by
                    apply readValues_updatedStates HgenOldOldValsLen HinKeys_disj_olds
                    -- ReadValues σO inputs.keys argVals.
                    have HrdAO : ReadValues σAO proc.header.inputs.keys argVals :=
                      InitStatesReadValuesMonotone (σ:=σA) (InitStatesReadValues Hinitin) Hinitout
                    have Hh1 := HavocVarsUpdateStates Hhav1
                    rcases Hh1 with ⟨ovh, Hup_havoc⟩
                    apply UpdateStatesReadValuesMonotone (σ:=σAO) _ ?_ Hup_havoc
                    · exact Hinoutnd
                    · exact HrdAO
                  -- σ_R1 reads outputs.keys → modvals (full).
                  have Hrd_R1_outs :
                      ReadValues σ_R1 proc.header.outputs.keys modvals :=
                    readValues_updatedStates HgenOldOldValsLen HoutKeys_disj_olds Hrd
                  -- σ_havoc reads argTemps → argVals (layer-1).
                  have Hrd_havoc_argT :
                      ReadValues σ_havoc argTemps argVals := by
                    show ReadValues
                      (updatedStates σ'
                        (argTemps ++
                          outTemps ++ genOldIdents)
                        (argVals ++ oVals ++ oldVals))
                      argTemps argVals
                    rw [Hflatten_eq]
                    have HargF_σ' :
                        ReadValues
                          (updatedStates σ' argTemps argVals)
                          argTemps argVals :=
                      readValues_updatedStatesSame HargTempsLen HargNd
                    have HargF_step1 :
                        ReadValues
                          (updatedStates
                            (updatedStates σ' argTemps argVals)
                            outTemps oVals) argTemps argVals :=
                      readValues_updatedStates HoutTempsLen HargOutDisj HargF_σ'
                    exact HoldTripsFst ▸ readValues_updatedStates HgenOldOldValsLen HargOldDisj HargF_step1
                  -- σ_havoc reads lhs → modvals (fall-through to σ').
                  have HmodvalsLen' : lhs.length = modvals.length := by
                    have := UpdateStatesLength Hupdate; omega
                  have Hrd_havoc_lhs :
                      ReadValues σ_havoc lhs modvals := by
                    apply readValues_updatedStates
                    · simp [argTemps, outTemps, List.length_append, List.unzip_eq_map, Hargtriplen, Houttriplen, HgenOldOldValsLen]
                    · intro v Hv1 Hv2
                      simp only [List.mem_append] at Hv2
                      rcases Hv2 with (ha | ho) | ho
                      · exact HlhsDisjArg Hv1 ha
                      · exact HlhsDisjOut Hv1 ho
                      · exact HlhsDisjOld Hv1 ho
                    · rw [Hσ'_eq]
                      exact readValues_updatedStatesSame HmodvalsLen' HlhsNd
                  -- Filtered halves via the triple zip.
                  have Hsubst : Imperative.substStores σ_R1 σ_havoc
                      (filtered_ks.zip filtered_ks') := by
                    intro k1 k2 Hkin
                    show σ_R1 k1 = σ_havoc k2
                    -- (k1, k2) ∈ filtered_ks.zip filtered_ks'.
                    -- Get the underlying pair shape: either output-pair
                    -- or filtered-input-pair.
                    rcases List.mem_iff_get.mp Hkin with ⟨n, Hn⟩
                    have Hn_lt_ks : n.val < filtered_ks.length := by
                      have := n.isLt; simp [List.length_zip, Hkslen] at this; omega
                    have Hn_lt_ks' : n.val < filtered_ks'.length := by
                      rw [← Hkslen]; exact Hn_lt_ks
                    have ⟨Hk1_eq, Hk2_eq⟩ :=
                      List.zip_pair_split Hn_lt_ks Hn_lt_ks' Hn
                    by_cases Hsplit : n.val < proc.header.outputs.keys.length
                    · -- Output-half.
                      have Hks_app_lt :
                          n.val < (proc.header.outputs.keys ++
                                    filtered_inputs).length := by
                        rw [List.length_append]; omega
                      have HoutLhsLen : n.val < lhs.length := by
                        rw [← HoutKeys_lhs_len]; exact Hsplit
                      have Hks'_app_lt :
                          n.val < (lhs ++ filtered_argTemps).length := by
                        rw [List.length_append]; omega
                      have Hk1_app :
                          k1 = proc.header.outputs.keys[n.val]'Hsplit := by
                        rw [Hk1_eq]
                        show (proc.header.outputs.keys ++
                              filtered_inputs)[n.val]'_ = _
                        rw [List.getElem_append_left (h := Hsplit)]
                      have Hk2_app : k2 = lhs[n.val]'HoutLhsLen := by
                        rw [Hk2_eq]
                        show (lhs ++ filtered_argTemps)[n.val]'_ = _
                        rw [List.getElem_append_left (h := HoutLhsLen)]
                      -- σ_R1 k1 = some modvals[n.val] (via Hrd_R1_outs).
                      have HmodLen_outs :
                          n.val < modvals.length := by
                        have := ReadValuesLength Hrd_R1_outs; omega
                      have HrdR1_get :
                          σ_R1 (proc.header.outputs.keys[n.val]'Hsplit) =
                            some (modvals[n.val]'HmodLen_outs) :=
                        readValues_get
                          (σ:=σ_R1) (ks:=proc.header.outputs.keys)
                          (vs:=modvals) Hrd_R1_outs
                          (i:=n.val) (hi:=Hsplit) (hi':=HmodLen_outs)
                      have HrdHavoc_get :
                          σ_havoc (lhs[n.val]'HoutLhsLen) =
                            some (modvals[n.val]'HmodLen_outs) :=
                        readValues_get
                          (σ:=σ_havoc) (ks:=lhs) (vs:=modvals)
                          Hrd_havoc_lhs
                          (i:=n.val) (hi:=HoutLhsLen) (hi':=HmodLen_outs)
                      rw [Hk1_app, HrdR1_get, Hk2_app, HrdHavoc_get]
                    · -- Input-half.
                      have Hsplit_le : proc.header.outputs.keys.length ≤ n.val :=
                        Nat.le_of_not_lt Hsplit
                      have Hlhs_le : lhs.length ≤ n.val := by
                        rw [← HoutKeys_lhs_len]; exact Hsplit_le
                      have Hk1_app :
                          k1 = filtered_inputs[n.val -
                              proc.header.outputs.keys.length]'(by
                            have Hl : filtered_ks.length =
                                proc.header.outputs.keys.length +
                                  filtered_inputs.length :=
                              List.length_append
                            omega) := by
                        rw [Hk1_eq]
                        show (proc.header.outputs.keys ++
                              filtered_inputs)[n.val]'_ = _
                        rw [List.getElem_append_right (h₁ := Hsplit_le)]
                      have Hk2_app :
                          k2 = filtered_argTemps[n.val - lhs.length]'(by
                            have Hl : filtered_ks'.length =
                                lhs.length + filtered_argTemps.length :=
                              List.length_append
                            omega) := by
                        rw [Hk2_eq]
                        show (lhs ++ filtered_argTemps)[n.val]'_ = _
                        rw [List.getElem_append_right (h₁ := Hlhs_le)]
                      -- The two filtered halves' indices line up:
                      --   n - outputs.length = n - lhs.length (by HoutKeys_lhs_len).
                      have Hidx_eq :
                          n.val - proc.header.outputs.keys.length =
                          n.val - lhs.length := by
                        rw [HoutKeys_lhs_len]
                      let j : Nat :=
                        n.val - proc.header.outputs.keys.length
                      have Hj_lt_filt :
                          j < filtered_inputs.length := by
                        have Hl : filtered_ks.length =
                            proc.header.outputs.keys.length +
                              filtered_inputs.length :=
                          List.length_append
                        omega
                      have Hj_lt_argT :
                          j < filtered_argTemps.length := by
                        rw [← Hfilt_len_sym]; exact Hj_lt_filt
                      have Hj_lt_subst :
                          j < filtered_argSubst.length := by
                        show j < filtered_argSubst.length
                        rw [show filtered_argSubst.length =
                            filtered_argSubst.unzip.fst.length from by
                            simp [List.unzip_eq_map]]
                        exact Hj_lt_filt
                      -- Pair at index j in filtered_argSubst is (k1, k2).
                      have HpairAtJ :
                          filtered_argSubst[j]'Hj_lt_subst = (k1, k2) := by
                        -- filtered_inputs[j] = (filtered_argSubst[j]).fst.
                        have HfilGetFst :
                            filtered_inputs[j]'Hj_lt_filt =
                            (filtered_argSubst[j]'Hj_lt_subst).fst := by
                          show filtered_argSubst.unzip.fst[j]'_ = _
                          simp [List.unzip_eq_map]
                        have HfilGetSnd :
                            filtered_argTemps[j]'Hj_lt_argT =
                            (filtered_argSubst[j]'Hj_lt_subst).snd := by
                          show filtered_argSubst.unzip.snd[j]'_ = _
                          simp [List.unzip_eq_map]
                        ext
                        · -- fst component.
                          rw [← HfilGetFst, ← Hk1_app]
                        · -- snd component.
                          rw [← HfilGetSnd]
                          have : filtered_argTemps[n.val - lhs.length]'(by
                              have Hl : filtered_ks'.length =
                                  lhs.length + filtered_argTemps.length :=
                                List.length_append
                              omega) = filtered_argTemps[j]'Hj_lt_argT := by
                            congr 1
                            exact Hidx_eq.symm
                          rw [Hk2_app, this]
                      -- Pair (k1, k2) ∈ filtered_argSubst.
                      have HpairIn : (k1, k2) ∈ filtered_argSubst := by
                        exact HpairAtJ.symm ▸ List.getElem_mem _
                      -- (k1, k2) ∈ inputs.keys.zip argTemps via Hfilter_in.
                      have HpairZip := (Hfilter_in (k1, k2) HpairIn).1
                      obtain ⟨m, Hm_lt_in, Hm_lt_argT, Hk1_inGet, Hk2_argTGet⟩ :=
                        pair_in_zip_pos_decomp HinKeys_argTemps_len HpairZip
                      have Hm_lt_argV : m < argVals.length := HinKVlen ▸ Hm_lt_in
                      have HrdR1_get :
                          σ_R1 (proc.header.inputs.keys[m]'Hm_lt_in) =
                            some (argVals[m]'Hm_lt_argV) :=
                        readValues_get (σ:=σ_R1) (ks:=proc.header.inputs.keys)
                          (vs:=argVals) Hrd_R1_in_full
                          (i:=m) (hi:=Hm_lt_in) (hi':=Hm_lt_argV)
                      have HrdHavoc_get :
                          σ_havoc (argTemps[m]'Hm_lt_argT) =
                            some (argVals[m]'Hm_lt_argV) :=
                        readValues_get (σ:=σ_havoc) (ks:=argTemps) (vs:=argVals)
                          Hrd_havoc_argT
                          (i:=m) (hi:=Hm_lt_argT) (hi':=Hm_lt_argV)
                      rw [Hk1_inGet, HrdR1_get, Hk2_argTGet, HrdHavoc_get]
                  -- ── D2e: Apply H_asserts_zip to derive HL4 ──
                  -- σ_old = post-L3 store (3-layer over argT/outT/oldTrips.fst.fst).
                  let σ_old : CoreStore :=
                    updatedStates
                      (updatedStates
                        (updatedStates σ
                          argTemps argVals)
                        outTemps oVals)
                      oldTrips.unzip.fst.unzip.fst oldVals
                  -- L4 ks/ks' bindings with explicit type annotation
                  -- so `substNodup` can unify the identifier type.
                  let ks_L4 : List Expression.Ident :=
                    proc.header.inputs.keys ++ proc.header.outputs.keys
                  let ks'_L4 : List Expression.Ident :=
                    argTemps ++ lhs
                  -- ── L4 length facts ──
                  have Hks_len_L4 :
                      ks_L4.length = ks'_L4.length := by
                    show (proc.header.inputs.keys ++
                          proc.header.outputs.keys).length =
                         (argTemps ++ lhs).length
                    rw [List.length_append, List.length_append,
                        HinKeys_argTemps_len, HoutKeys_lhs_len]
                  -- ── L4 substNodup: ((inputs ++ outputs) ++ (argTemps ++ lhs)).Nodup ──
                  have HargT_lhs_nd :
                      (argTemps ++ lhs).Nodup := by
                    rw [List.nodup_append]
                    refine ⟨HargNd, HlhsNd, ?_⟩
                    intro a Ha b Hb Heq
                    subst Heq
                    exact HlhsDisjArg Hb Ha
                  have Hbignd_L4 :
                      (ks_L4 ++ ks'_L4).Nodup := by
                    rw [List.nodup_append]
                    refine ⟨Hinoutnd, HargT_lhs_nd, fun a Ha b Hb Heq => ?_⟩
                    subst Heq
                    rcases List.mem_append.mp Ha with HaIn | HaOut <;>
                      rcases List.mem_append.mp Hb with HbArg | HbLhs
                    · exact HinKeys_disj_argTemps HaIn HbArg
                    · exact HinKeys_disj_lhs HaIn HbLhs
                    · exact HoutKeys_disj_argTemps HaOut HbArg
                    · exact HoutKeys_disj_lhs HaOut HbLhs
                  have Hnd_L4 : Imperative.substNodup
                      (ks_L4.zip ks'_L4) := by
                    unfold Imperative.substNodup
                    exact (List.unzip_zip Hks_len_L4) ▸ Hbignd_L4
                  -- ── L4 substDefined ──
                  have HσAO_def_in_L4 :
                      Imperative.isDefined σAO proc.header.inputs.keys :=
                    InitStatesDefMonotone (InitStatesDefined Hinitin) Hinitout
                  have HσAO_def_out_L4 :
                      Imperative.isDefined σAO proc.header.outputs.keys :=
                    InitStatesDefined Hinitout
                  -- σ_old definedness on argTemps via layer-1 fall-through (HargOldDisj/HargOutDisj).
                  have Hσ_old_def_argT :
                      Imperative.isDefined σ_old
                        argTemps := by
                    intro v Hv
                    show ((updatedStates
                            (updatedStates
                              (updatedStates σ
                                argTemps argVals)
                              outTemps oVals)
                            oldTrips.unzip.fst.unzip.fst oldVals) v).isSome =
                          true
                    rw [updatedStates_get_notin (HoldTripsFst.symm ▸ HargOldDisj Hv),
                        updatedStates_get_notin (HargOutDisj Hv)]
                    exact updatedStatesDefined HargTempsLen v Hv
                  -- σ_old definedness on lhs (reuses C-aux HlhsDef_old).
                  have Hσ_old_def_lhs :
                      Imperative.isDefined σ_old lhs := HlhsDef_old
                  have Hdef_L4 : Imperative.substDefined σAO σ_old
                      (ks_L4.zip ks'_L4) :=
                    substDefined_of_app HσAO_def_in_L4 HσAO_def_out_L4
                      Hσ_old_def_argT Hσ_old_def_lhs
                  -- ── L4 substStores: substStores σ_old σAO ((argTemps ++ lhs).zip (inputs ++ outputs)) ──
                  -- Build matching ReadValues on σ_old and σAO, close via ReadValuesSubstStores.
                  have HrdAO_in_L4 :
                      ReadValues σAO proc.header.inputs.keys argVals := by
                    have HrdA_in : ReadValues σA proc.header.inputs.keys argVals :=
                      InitStatesReadValues Hinitin
                    apply InitStatesReadValuesMonotone HrdA_in Hinitout
                  have HrdAO_out_L4 :
                      ReadValues σAO proc.header.outputs.keys oVals :=
                    InitStatesReadValues Hinitout
                  have HrdAO_inout_L4 :
                      ReadValues σAO
                        (proc.header.inputs.keys ++
                          proc.header.outputs.keys)
                        (argVals ++ oVals) :=
                    ReadValuesApp HrdAO_in_L4 HrdAO_out_L4
                  -- σ_old reads argTemps ↦ argVals: layer-1 init lifted via readValues_updatedStates.
                  have HrdLayer3_argT :
                      ReadValues σ_old
                        argTemps argVals :=
                    readValues_updatedStates HoldFstLen
                      (HoldTripsFst ▸ HargOldDisj)
                      (readValues_updatedStates HoutTempsLen HargOutDisj
                        (readValues_updatedStatesSame HargTempsLen
                          (List.nodup_append.mp (List.nodup_append.mp Hgennd).1).1))
                  -- σ_old reads lhs ↦ oVals.  Path: σ(lhs) = oVals via
                  -- Hevalouts, lifted across the 3-layer extension.
                  have HrdLayer3_lhs :
                      ReadValues σ_old lhs oVals :=
                    readValues_3layer_lift HargTempsLen HlhsDisjArg
                      HoutTempsLen HlhsDisjOut
                      HoldFstLen (HoldTripsFst ▸ HlhsDisjOld) Hevalouts
                  have HrdOld_inout_L4 :
                      ReadValues σ_old
                        (argTemps ++ lhs)
                        (argVals ++ oVals) :=
                    ReadValuesApp HrdLayer3_argT HrdLayer3_lhs
                  have Hsubst_L4 : Imperative.substStores σ_old σAO
                      (ks'_L4.zip ks_L4) :=
                    ReadValuesSubstStores HrdOld_inout_L4 HrdAO_inout_L4
                  -- ── Apply H_asserts_zip ──
                  obtain ⟨assertLabels, HassertLabelsLen, HassertShape⟩ :=
                    HassertsShape
                  -- HassertsShape's subst = ks_L4.zip (createFvars ks'_L4).
                  have HassertSubst_eq :
                      ((proc.header.inputs.keys.zip
                          (Core.Transform.createFvars
                            argTemps)) ++
                        (proc.header.outputs.keys.zip
                          (Core.Transform.createFvars
                            (CallArg.getLhs args)))) =
                      ks_L4.zip
                        (Core.Transform.createFvars ks'_L4) := by
                    show _ =
                      (proc.header.inputs.keys ++
                        proc.header.outputs.keys).zip
                      (Core.Transform.createFvars
                        (argTemps ++ lhs))
                    rw [hCallArgsLhs, createFvarsApp]
                    rw [List.zip_append]
                    rw [createFvarsLength]
                    exact HinKeys_argTemps_len
                  -- Apply H_asserts_zip; bne_iff_ne bridges the != / ≠ filter forms.
                  have HL4_pre :
                      EvalStatementsContract π φ ⟨σ_old, δ, false⟩
                        (((proc.spec.preconditions.filter
                              (fun (_, check) => check.attr != .Free)).zip
                            assertLabels).map (fun (entry, lbl) =>
                          Statement.assert lbl
                            (Lambda.LExpr.substFvars entry.snd.expr
                              (ks_L4.zip
                                (Core.Transform.createFvars ks'_L4)))
                            (entry.snd.md.setCallSiteFileRange md)))
                        ⟨σ_old, δ, false⟩ := by
                    apply H_asserts_zip
                      (σA := σAO) (σ' := σ_old)
                      (ks := ks_L4)
                      (ks' := ks'_L4)
                      (pres := proc.spec.preconditions.filter
                                (fun (_, check) => check.attr != .Free))
                      (labels := assertLabels)
                      Hwfb Hwfvars Hwfval Hwfc
                      Hks_len_L4 Hnd_L4 Hdef_L4 Hsubst_L4
                    -- HpresPayload over presFiltered.  Bridge `!=` ↔ `≠` filter forms.
                    intros entry Hentry
                    have Hentry' : entry ∈ presFiltered := by
                      show entry ∈ proc.spec.preconditions.filter
                                    (fun (_, c) => c.attr ≠ .Free)
                      exact (filter_bne_eq_filter_ne proc.spec.preconditions).symm ▸ Hentry
                    exact HpresPayload entry Hentry'
                  -- Bridge to the actual `asserts` list via HassertsShape.
                  have HL4 :
                      EvalStatementsContract π φ ⟨σ_old, δ, false⟩
                        asserts ⟨σ_old, δ, false⟩ := by
                    -- Rewrite asserts using HassertShape; the resulting list
                    -- is over `proc'`-keys, which equal `proc`-keys via HprocEq.
                    rw [HassertShape]
                    -- Push proc' = proc through to reach the L4-derived form.
                    rw [HprocEq]
                    -- Rewrite the inner substitution map via HassertSubst_eq.
                    exact HassertSubst_eq ▸ HL4_pre
                  -- D2d-bridge: σO ↔ σAO old-binding bridge.
                  -- (a) Trivial empty-init witness (used by callee bridges).
                  have HInitVars_empty : InitVars σO [] σO := InitVars.init_none
                  -- (b) Per-output bridge, σAO reads outputs, oldVars ⊆ lhs/outs.
                  obtain ⟨Hwf2_univ, HσAO_reads_outs, HoldVars_sub_outs⟩ :=
                    holdEval_bridge_prelude (args := args)
                      Hwf2 Hhav1 Hinitout HprocEq
                  -- (b) σAO[v] = σ[v] for v ∉ outputs ∪ inputs.
                  have HσAO_notin_eq_σ :
                      ∀ v, v ∉ proc.header.outputs.keys →
                           v ∉ proc.header.inputs.keys →
                           σAO v = σ v := by
                    intro v Hv_notout Hv_notin
                    rw [initStates_get_notin Hinitout Hv_notout,
                        initStates_get_notin Hinitin Hv_notin]
                  -- Per-index positional bridge for downstream consumers.
                  have HoldEval_bridge :
                      ∀ (i : Nat) (Hi : i < oldVars.length),
                        δ σO
                            (Lambda.LExpr.fvar ()
                              (CoreIdent.mkOld (oldVars[i]'Hi).name) none) =
                          some (oldVals[i]'(HoldValsLen.symm ▸ Hi)) :=
                    HoldEval_bridge_at_σO Hwf2_univ Hinitout HσAO_reads_outs
                      Hevalouts hCallArgsLhs HoutAlign HoldVars_sub_outs
                      HoldVars_sub_lhs HoldVals HoldValsLen
                  -- D2d: Structural pieces of HpostPayload (per-entry).
                  let oldTripsCanonical_L6 :
                      List ((Expression.Ident × Expression.Ty) ×
                            Expression.Ident) :=
                    (((genOldIdents.zip oldTys).zip oldVars).zip
                      (oldVars.map (fun g => CoreIdent.mkOld g.name))).map
                      fun (((fresh, ty), _orig), oldG) => ((fresh, ty), oldG)
                  let inputOnlyOldSubst_L6 :
                      Map Expression.Ident Expression.Expr :=
                    callElim_inputOnlyOldSubst proc' args
                  let oldSubst_L6 : Map Expression.Ident Expression.Expr :=
                    Core.Transform.createOldVarsSubst oldTripsCanonical_L6 ++
                      inputOnlyOldSubst_L6
                  let posts_filtered_L6 :
                      ListMap CoreLabel Procedure.Check :=
                    Procedure.Spec.updateCheckExprs
                      (proc'.spec.postconditions.values.map
                        (fun c =>
                          Lambda.LExpr.substFvars c.expr oldSubst_L6))
                      proc'.spec.postconditions
                  -- Per-entry decomposition helper: posts_filtered_L6 entries
                  -- correspond to original posts via updateCheckExprs_substFvars_mem.
                  have forall_post_filtered_decompose :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        ∃ c ∈ proc'.spec.postconditions.values,
                          entry.snd.expr =
                            Lambda.LExpr.substFvars c.expr oldSubst_L6 := by
                    intro entry Hentry
                    apply updateCheckExprs_substFvars_mem
                    rw [updateCheckExprs_walk_eq_go]
                    show entry ∈
                        (proc'.spec.postconditions.keys.zip
                          (Procedure.Spec.updateCheckExprs.go _ _))
                    exact Hentry
                  -- D2d-eval: per-fvar bridges for substFvars eval (split via
                  -- oldSubst_L6 = createOldVarsSubst ++ inputOnlyOldSubst).
                  have HoldSubBridge :
                      ∀ k w,
                        Map.find?
                          (Core.Transform.createOldVarsSubst
                            oldTripsCanonical_L6) k = some w →
                        δ σ_R1 w =
                          δ σO (Lambda.LExpr.fvar () k none) :=
                    HoldSubBridge_at_σO Hwfvars HgenOldLen HoldTysLen
                      HoldValsLen σ_R1_read_olds HoldEval_bridge
                  -- (2b) HinputSubBridge: inputOnlyOldSubst codomain.
                  have HinputSubBridge :
                      ∀ k w,
                        Map.find? inputOnlyOldSubst_L6 k = some w →
                        δ σ_R1 w =
                          δ σO (Lambda.LExpr.fvar () k none) :=
                    HinputSubBridge_at_σO Hwfvars Hwfval Hwfc Hwf2
                      HprocEq Hiodisj Hinitin Hinitout Hhav1
                      HInitVars_empty Hevalargs hCallArgsIn HargIsDef
                      HoldIdentsTemp Hgenrel HargVarsNotInInKeys
                      HargVarsNotInOutKeys rfl
                  -- HpostEval_bridge: per-entry σ_R1 eval bridge via
                  -- subst_fvars_eval_bridge + HpostFiltered_corresp.
                  have HpostEval_bridge :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        δ σ_R1 entry.snd.expr =
                          some Imperative.HasBool.tt := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    -- entry.snd.expr = substFvars c.expr oldSubst_L6.
                    rw [Hentry_eq]
                    -- Build the combined Hsub for subst_fvars_eval_bridge.
                    have Hsub :
                        ∀ k w, k ∈ Imperative.HasVarsPure.getVars
                                      (P:=Expression) c.expr →
                          Map.find? oldSubst_L6 k = some w →
                          δ σ_R1 w =
                            δ σO (Lambda.LExpr.fvar () k none) := by
                      intro k w _Hk Hf
                      -- oldSubst_L6 = createOldVarsSubst ... ++ inputOnlyOldSubst_L6;
                      -- split via `find?_append_{some_eq, none_elim}`.
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k with
                      | some v =>
                        have Hvw : v = w := find?_append_some_eq hfind Hf
                        exact Hvw.symm ▸ HoldSubBridge k v hfind
                      | none =>
                        exact HinputSubBridge k w (find?_append_none_elim hfind Hf)
                    -- Build HsurvBridge specialized to c.
                    have Hc_filtered : c ∈ postsFiltered.map (·.snd) ∨
                                        c ∈ proc'.spec.postconditions.values := by
                      right; exact Hc_in
                    -- v ∈ getVars c.expr ⇒ ¬ isOldTempIdent v, via HpostVarsFresh.
                    have HsurvBridgeC :
                        ∀ v ∈ Imperative.HasVarsPure.getVars (P:=Expression)
                                c.expr,
                          Map.find? oldSubst_L6 v = none →
                          δ σ_R1 (Lambda.LExpr.fvar () v none) =
                            δ σO (Lambda.LExpr.fvar () v none) := by
                      intro v Hv _Hnone
                      -- v ∈ getVars c.expr where c ∈ proc'.spec.postconditions.values.
                      have HvFresh := HpostVarsFresh_via_c c Hc_in v Hv
                      have HvNotOld : ¬ isOldTempIdent v := HvFresh.2.1
                      have HvNotGen : v ∉ genOldIdents :=
                        notMem_of_Forall_neg HoldIdentsTemp HvNotOld
                      have Hσ_R1_v_eq_σO :
                          σ_R1 v = σO v := by
                        show (updatedStates σO genOldIdents oldVals) v = σO v
                        exact updatedStates_get_notin HvNotGen
                      rw [δ_fvar_eq σ_R1 v, δ_fvar_eq σO v]
                      exact Hσ_R1_v_eq_σO
                    -- Apply subst_fvars_eval_bridge.
                    have Hbridge :
                        δ σ_R1 (Lambda.LExpr.substFvars c.expr oldSubst_L6) =
                          δ σO c.expr :=
                      subst_fvars_eval_bridge Hwfc Hwfvars Hwfval
                        HsurvBridgeC Hsub
                    rw [Hbridge]
                    -- Now `δ σO c.expr = some HasBool.tt`.
                    -- Bridge proc'.spec.postconditions ↔ proc.spec.postconditions.
                    have Hin_full := c_in_postExprs_of_proc' c Hc_in
                    have Hin_contains :
                        (Procedure.Spec.getCheckExprs
                            proc.spec.postconditions).contains c.expr = true :=
                      List.contains_iff_mem.mpr Hin_full
                    exact (Hpost c.expr Hin_contains).2
                  -- Hinv: residual invStores σ_R1 σ_havoc.
                  have HrdHavoc_olds_pos :
                      ∀ (i : Nat) (Hi : i < genOldIdents.length)
                        (Hi' : i < oldVals.length),
                        σ_havoc (genOldIdents[i]'Hi) =
                          some (oldVals[i]'Hi') := by
                    -- σ_havoc on genOldIdents: split via List.zip_append.
                    have HzipAppend2 :
                        ((argTemps ++
                            outTemps) ++ genOldIdents).zip
                          ((argVals ++ oVals) ++ oldVals) =
                          ((argTemps ++
                              outTemps).zip
                            (argVals ++ oVals)) ++
                          (genOldIdents.zip oldVals) := by
                      apply List.zip_append
                      simp [List.length_append, HargTempsLen, HoutTempsLen]
                    have HsplitOverlay :
                        σ_havoc =
                        updatedStates
                          (updatedStates σ'
                            (argTemps ++
                              outTemps)
                            (argVals ++ oVals))
                          genOldIdents oldVals := by
                      show updatedStates σ'
                            (argTemps ++
                              outTemps ++ genOldIdents)
                            (argVals ++ oVals ++ oldVals) = _
                      simp only [updatedStates]
                      rw [HzipAppend2, updatedStates'App]
                    have HrdHavoc :
                        ReadValues σ_havoc genOldIdents oldVals := by
                      exact HsplitOverlay ▸ readValues_updatedStatesSame HgenOldOldValsLen HoldNd
                    intro i Hi Hi'
                    exact readValues_get HrdHavoc (i:=i) (hi:=Hi) (hi':=Hi')
                  -- Shared class-(b) decompositions for Hinv/Hpred_disj
                  -- via oldSubst_L6 = createOldVarsSubst ++ inputOnlyOldSubst.
                  have b1_var_witness :=
                    @b1_var_witness_at_oldSubst oldVars genOldIdents oldTys
                      proc' args HgenOldLen HoldTysLen
                  -- (b2): miss on createOldVarsSubst, hit on inputOnlyOldSubst.
                  -- Yields `w = inArgs[ni2]`, `w ∈ inArgs`, the input-key
                  -- positional fact, and `var ∈ flatMap getVars inArgs`.
                  have b2_var_witness :=
                    @b2_var_witness_at_oldSubst oldVars genOldIdents oldTys
                      proc' args inArgs hCallArgsIn
                  have Hinv :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        Imperative.invStores σ_R1 σ_havoc
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            (filtered_ks ++ filtered_ks')) := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    -- Open invStores.
                    simp only [Imperative.invStores, Imperative.substStores]
                    intros k1 k2 Hkin
                    obtain ⟨rfl, Hk1_pre, Hk1_notin_outs, Hk1_notin_filtIn,
                            Hk1_notin_lhs, Hk1_notin_filtArgT⟩ :=
                      zip_removeAll4_decompose Hkin
                    -- entry.snd.expr = substFvars c.expr oldSubst_L6.
                    rw [Hentry_eq] at Hk1_pre
                    -- Decompose k1 ∈ getVars (substFvars c.expr oldSubst_L6).
                    rcases getVars_substFvars_mem Hk1_pre with
                      Hclass_a | ⟨k, w, Hk_in, Hf, Hv_in⟩
                    · -- ── Class (a): k1 ∈ getVars c.expr ∧ find? oldSubst_L6 k1 = none ──
                      obtain ⟨Hk1_post, _Hf_none⟩ := Hclass_a
                      -- HpostsVarsFresh_orig: ¬tmp_, ¬old_, k1 ∉ lhs.
                      have HfreshK := HpostVarsFresh_via_c c Hc_in k1 Hk1_post
                      have Hk1_notTemp : ¬ isTempIdent k1 := HfreshK.1
                      have Hk1_notOld : ¬ isOldTempIdent k1 := HfreshK.2.1
                      -- k1 ∉ argTemps (tmp_).
                      have Hk1_notin_argT : k1 ∉ argTemps :=
                        notMem_of_Forall_neg HargTemp Hk1_notTemp
                      have Hk1_notin_outT : k1 ∉ outTemps :=
                        notMem_of_Forall_neg HoutTemp Hk1_notTemp
                      have Hk1_notin_genOld : k1 ∉ genOldIdents :=
                        notMem_of_Forall_neg HoldIdentsTemp Hk1_notOld
                      -- k1 ∉ inputs.keys (since k1 ∉ outputs and k1 ∉ filtered_inputs).
                      have Hk1_notin_ins :
                          k1 ∉ proc.header.inputs.keys := by
                        intro h
                        -- k1 ∈ inputs.keys, k1 ∉ outputs.keys ⇒ k1 ∈ filtered_inputs.
                        rcases List.mem_iff_get.mp h with ⟨n, Hn⟩
                        have Hn_lt_in : n.val < proc.header.inputs.keys.length := n.isLt
                        have Hn_lt_argT : n.val < argTemps.length :=
                          HinKeys_argTemps_len ▸ Hn_lt_in
                        have HkE :
                            proc.header.inputs.keys[n.val]'Hn_lt_in = k1 := Hn
                        have Hpair_in_zip :
                            (k1, argTemps[n.val]'Hn_lt_argT) ∈
                              proc.header.inputs.keys.zip argTemps := by
                          exact HkE.symm ▸ pair_in_zip_of_pos Hn_lt_in Hn_lt_argT
                        have Hpair_in_filtAS :
                            (k1, argTemps[n.val]'Hn_lt_argT) ∈
                              filtered_argSubst := by
                          apply List.mem_filter.mpr
                          refine ⟨Hpair_in_zip, ?_⟩
                          simp only [decide_not, Bool.not_eq_eq_eq_not,
                                     Bool.not_true, decide_eq_false_iff_not,
                                     List.contains_iff_mem]
                          exact Hk1_notin_outs
                        have Hk1_in_unzip :
                            k1 ∈ filtered_inputs := by
                          show k1 ∈ filtered_argSubst.unzip.fst
                          simp only [List.unzip_eq_map, List.mem_map]
                          refine ⟨(k1, argTemps[n.val]'Hn_lt_argT), Hpair_in_filtAS, rfl⟩
                        exact Hk1_notin_filtIn Hk1_in_unzip
                      exact σR1_eq_σhavoc Hk1_notin_ins Hk1_notin_outs
                        Hk1_notin_argT Hk1_notin_outT Hk1_notin_genOld Hk1_notin_lhs
                    · -- ── Class (b): k1 ∈ getVars w for some (k, w) ∈ oldSubst_L6 ──
                      -- Split via Map.find?_append.
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k with
                      | some w' =>
                        -- (b1) createOldVarsSubst flavor — via shared helper.
                        obtain ⟨ni_val, Hni_lt_genOld, Hv_eq_gen⟩ :=
                          b1_var_witness hfind Hf Hv_in
                        -- σ_R1 k1 = oldVals[ni_val]; σ_havoc k1 = oldVals[ni_val].
                        have Hni_lt_oldVals : ni_val < oldVals.length :=
                          HoldValsLen.symm ▸ HgenOldLen ▸ Hni_lt_genOld
                        have Hσ_R1_v :
                            σ_R1 (genOldIdents[ni_val]'Hni_lt_genOld) =
                              some (oldVals[ni_val]'Hni_lt_oldVals) :=
                          σ_R1_read_olds ni_val Hni_lt_genOld Hni_lt_oldVals
                        have Hσ_havoc_v :
                            σ_havoc (genOldIdents[ni_val]'Hni_lt_genOld) =
                              some (oldVals[ni_val]'Hni_lt_oldVals) :=
                          HrdHavoc_olds_pos ni_val Hni_lt_genOld Hni_lt_oldVals
                        rw [Hv_eq_gen, Hσ_R1_v, Hσ_havoc_v]
                      | none =>
                        -- (b2) inputOnlyOldSubst flavor — via shared helper.
                        obtain ⟨HargExpr_in, Hk1_flat⟩ :=
                          b2_var_witness hfind Hf Hv_in
                        -- k1 ∈ getVars w.  By HargVarsNotIn{Out,In}Keys:
                        have Hk1_notin_outs' :
                            k1 ∉ proc.header.outputs.keys :=
                          HargVarsNotInOutKeys w HargExpr_in k1 Hv_in
                        have Hk1_notin_ins' :
                            k1 ∉ proc.header.inputs.keys :=
                          HargVarsNotInInKeys w HargExpr_in k1 Hv_in
                        -- k1 ∈ σ-defined via Hevalargs.
                        have Hk1_σ_some : (σ k1).isSome := HargIsDef k1 Hk1_flat
                        -- k1 not isOldTempIdent.
                        have Hk1_notOld' : ¬ isOldTempIdent k1 := fun Hold =>
                          σ_some_contradiction Hk1_σ_some
                            (Option.isNone_iff_eq_none.mp (Hgenrel.oldFresh k1 Hold))
                        -- k1 not isTempIdent.  Via isNotDefined of argTemps/outTemps.
                        have Hk1_notin_argT' : k1 ∉ argTemps := notin_of_isSome_isNotDefined Hk1_σ_some HndefArg_σ
                        have Hk1_notin_outT' : k1 ∉ outTemps := notin_of_isSome_isNotDefined Hk1_σ_some HndefOut_σ
                        have Hk1_notin_genOld' : k1 ∉ genOldIdents := notin_of_isSome_isNotDefined Hk1_σ_some HndefOld_σ
                        exact σR1_eq_σhavoc Hk1_notin_ins' Hk1_notin_outs'
                          Hk1_notin_argT' Hk1_notin_outT' Hk1_notin_genOld'
                          Hk1_notin_lhs
                  -- Hpred_disj: filtered_ks' disjoint from entry's vars.
                  have HfiltArgT_sub_argT :
                      ∀ x ∈ filtered_argTemps, x ∈ argTemps := by
                    intro x Hx
                    show x ∈ argTemps
                    -- filtered_argTemps = filtered_argSubst.unzip.snd ⊆ argTemps.
                    have Hx' : x ∈ filtered_argSubst.unzip.snd := Hx
                    simp only [List.unzip_eq_map, List.mem_map] at Hx'
                    rcases Hx' with ⟨pair, Hpair_mem, Hpair_snd⟩
                    have Hpair_in_zip := (List.mem_filter.mp Hpair_mem).1
                    -- pair ∈ inputs.keys.zip argTemps ⇒ pair.snd ∈ argTemps.
                    have Hsnd_in :
                        pair.snd ∈ argTemps :=
                      (List.of_mem_zip Hpair_in_zip).2
                    rw [← Hpair_snd]; exact Hsnd_in
                  have Hpred_disj :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        filtered_ks'.Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) := by
                    intro entry Hentry
                    obtain ⟨c, Hc_in, Hentry_eq⟩ :=
                      forall_post_filtered_decompose entry Hentry
                    intro x Hin1 Hin2
                    -- x ∈ filtered_ks' = lhs ++ filtered_argTemps.
                    -- x ∈ entry.snd.expr.getVars.
                    rw [Hentry_eq] at Hin2
                    rcases getVars_substFvars_mem Hin2 with
                      Hclass_a | ⟨k', w, Hk_in, Hf, Hv_in⟩
                    · -- ── Class (a): x ∈ getVars c.expr ──
                      obtain ⟨Hx_post, _Hf_none⟩ := Hclass_a
                      -- HpostsVarsFresh_orig: ¬tmp_, ¬old_, x ∉ lhs.
                      have HfreshK := HpostVarsFresh_via_c c Hc_in x Hx_post
                      have Hx_notTemp : ¬ isTempIdent x := HfreshK.1
                      have Hx_notLhs : x ∉ CallArg.getLhs args := HfreshK.2.2
                      -- Show contradiction.
                      cases List.mem_append.mp Hin1 with
                      | inl Hx_lhs =>
                        rw [hCallArgsLhs] at Hx_notLhs
                        exact Hx_notLhs Hx_lhs
                      | inr Hx_filtArgT =>
                        have Hx_argT : x ∈ argTemps :=
                          HfiltArgT_sub_argT x Hx_filtArgT
                        exact Hx_notTemp ((List.Forall_mem_iff.mp HargTemp) x Hx_argT)
                    · -- ── Class (b): x ∈ getVars w for some (k', w) ∈ oldSubst_L6 ──
                      cases hfind : Map.find?
                                      (Core.Transform.createOldVarsSubst
                                        oldTripsCanonical_L6) k' with
                      | some w' =>
                        -- (b1) createOldVarsSubst flavor — via shared helper.
                        obtain ⟨ni_val, Hni_lt_genOld, Hx_eq_gen⟩ :=
                          b1_var_witness hfind Hf Hv_in
                        rw [Hx_eq_gen] at Hin1
                        -- genOldIdents[ni_val] ∈ filtered_ks' = lhs ++ filtered_argTemps.
                        -- Each branch yields contradiction.
                        cases List.mem_append.mp Hin1 with
                        | inl Hx_lhs =>
                          -- HlhsDisjOld: lhs.Disjoint genOldIdents.
                          exact HlhsDisjOld Hx_lhs (List.getElem_mem _)
                        | inr Hx_filtArgT =>
                          -- genOldIdents[i] is isOldTempIdent; filt_argT ⊆ argT
                          -- (isTempIdent); the two predicates are disjoint.
                          have Hx_argT :
                              genOldIdents[ni_val]'Hni_lt_genOld ∈ argTemps :=
                            HfiltArgT_sub_argT _ Hx_filtArgT
                          have Hx_isTemp : isTempIdent (genOldIdents[ni_val]'Hni_lt_genOld) :=
                            (List.Forall_mem_iff.mp HargTemp) _ Hx_argT
                          have Hx_isOld : isOldTempIdent (genOldIdents[ni_val]'Hni_lt_genOld) :=
                            (List.Forall_mem_iff.mp HoldIdentsTemp) _ (List.getElem_mem _)
                          exact isTempIdent_isOldTempIdent_disjoint
                            Hx_isTemp Hx_isOld
                      | none =>
                        -- (b2) inputOnlyOldSubst flavor — via shared helper.
                        obtain ⟨HargExpr_in, Hx_flat⟩ :=
                          b2_var_witness hfind Hf Hv_in
                        -- x ∈ σ-defined via Hevalargs.
                        have Hx_σ_some : (σ x).isSome := HargIsDef x Hx_flat
                        -- Now case-split on x ∈ filtered_ks'.
                        cases List.mem_append.mp Hin1 with
                        | inl Hx_lhs =>
                          -- x ∉ lhs via HargVarsNotInLhs (clause 3).
                          have Hx_notLhs :
                              x ∉ CallArg.getLhs args :=
                            HargVarsNotInLhs w HargExpr_in x Hv_in
                          rw [hCallArgsLhs] at Hx_notLhs
                          exact Hx_notLhs Hx_lhs
                        | inr Hx_filtArgT =>
                          -- x ∈ argTemps ⇒ σ x = none, but σ x is some.
                          have Hx_argT :
                              x ∈ argTemps :=
                            HfiltArgT_sub_argT x Hx_filtArgT
                          exact σ_some_contradiction Hx_σ_some
                            (HndefArg_σ x Hx_argT)
                  -- HpostPayload: combined per-entry payload for L6.
                  have HpostPayload :
                      ∀ entry : CoreLabel × Procedure.Check,
                        entry ∈ posts_filtered_L6.toList →
                        Imperative.invStores σ_R1 σ_havoc
                          ((Imperative.HasVarsPure.getVars (P:=Expression)
                              entry.snd.expr).removeAll
                            (filtered_ks ++ filtered_ks')) ∧
                        filtered_ks'.Disjoint
                          (Imperative.HasVarsPure.getVars (P:=Expression)
                            entry.snd.expr) ∧
                        δ σ_R1 entry.snd.expr =
                          some Imperative.HasBool.tt := by
                    intro entry Hentry
                    refine ⟨Hinv entry Hentry,
                            Hpred_disj entry Hentry,
                            HpostEval_bridge entry Hentry⟩
                  -- D2f: Apply H_assumes_zip to derive HL6 (L6 segment of glue).
                  obtain ⟨assumeLabels, _HassumeLabelsLen, HassumeShape⟩ :=
                    HassumesShape
                  -- Bridge: `assumeSubst = filtered_ks.zip (createFvars filtered_ks')`.
                  have HassumeSubst_eq :
                      ((proc'.header.outputs.keys.zip
                          (Core.Transform.createFvars (CallArg.getLhs args))) ++
                        (proc'.header.inputs.keys.zip
                          (Core.Transform.createFvars argTemps)).filter
                          (fun (id, _) =>
                            !(ListMap.keys proc'.header.outputs).contains id)) =
                      filtered_ks.zip
                        (Core.Transform.createFvars filtered_ks') := by
                    rw [HprocEq]
                    show _ = (proc.header.outputs.keys ++ filtered_inputs).zip
                      (Core.Transform.createFvars (lhs ++ filtered_argTemps))
                    rw [createFvarsApp]
                    rw [List.zip_append
                          (show proc.header.outputs.keys.length =
                                (Core.Transform.createFvars lhs).length by
                            rw [createFvarsLength,
                                HoutKeys_lhs_len])]
                    -- Head: bridge via hCallArgsLhs.
                    rw [hCallArgsLhs]
                    congr 1
                    show (proc.header.inputs.keys.zip
                          (argTemps.map Core.Transform.createFvar)).filter _ =
                      filtered_argSubst.unzip.fst.zip
                        (filtered_argSubst.unzip.snd.map
                          Core.Transform.createFvar)
                    rw [List.zip_map_right]
                    rw [List.filter_map]
                    -- Bridge composed `!`/`Prod.map` filter to filtered_argSubst.
                    have HfiltEq :
                        (proc.header.inputs.keys.zip argTemps).filter
                          ((fun (x : Expression.Ident × Expression.Expr) =>
                              !(ListMap.keys proc.header.outputs).contains x.1) ∘
                            Prod.map id Core.Transform.createFvar) =
                          filtered_argSubst := by
                      show _ = (proc.header.inputs.keys.zip argTemps).filter
                          (fun pr =>
                            ¬ (proc.header.outputs.keys).contains pr.1)
                      apply List.filter_congr
                      intro pr _
                      cases pr with
                      | mk a b => simp [Function.comp, Prod.map]
                    rw [HfiltEq]
                    -- Massage the RHS: zip_map_right reverse + zip_unzip.
                    rw [show filtered_argSubst.unzip.fst.zip
                            (filtered_argSubst.unzip.snd.map
                              Core.Transform.createFvar) =
                          (filtered_argSubst.unzip.fst.zip
                            filtered_argSubst.unzip.snd).map
                            (Prod.map id Core.Transform.createFvar) from
                        List.zip_map_right]
                    rw [show filtered_argSubst.unzip.fst.zip
                            filtered_argSubst.unzip.snd =
                          filtered_argSubst from List.zip_unzip _]
                  -- ── Apply H_assumes_zip ──
                  have HL6_pre :
                      EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩
                        ((posts_filtered_L6.zip assumeLabels).map
                          (fun (entry, lbl) =>
                            Statement.assume lbl
                              (Lambda.LExpr.substFvars entry.snd.expr
                                (filtered_ks.zip
                                  (Core.Transform.createFvars filtered_ks')))
                              (entry.snd.md.setCallSiteFileRange md)))
                        ⟨σ_havoc, δ, false⟩ := by
                    apply H_assumes_zip_poly (f := false)
                      (σA := σ_R1) (σ' := σ_havoc)
                      (ks := filtered_ks)
                      (ks' := filtered_ks')
                      (posts := posts_filtered_L6.toList)
                      (labels := assumeLabels)
                      Hwfb Hwfvars Hwfval Hwfc
                      Hkslen Hnd Hdef Hsubst
                    intros entry Hentry
                    exact HpostPayload entry Hentry
                  -- Bridge to the actual `assumes` list via HassumeShape.
                  have HL6 :
                      EvalStatementsContract π φ ⟨σ_havoc, δ, false⟩
                        assumes ⟨σ_havoc, δ, false⟩ := by
                    -- HassumeShape proc'-keys agree with proc via HprocEq.
                    rw [HassumeShape]
                    exact HassumeSubst_eq ▸ HL6_pre
                  -- ── D2g: Chain L1-L6 via EvalCallElim_glue ──
                  exact EvalCallElim_glue HL1 HL2 HL3 HL4 HL5 HL6
          · -- inner `Except.error` branch — contradiction
            rename_i e_err heq_err
            simp only [pure, StateT.pure, Prod.mk.injEq] at Helim
            exact absurd Helim.1 (by simp)

/-- Exit-arm correctness of `callElimStmt` per source statement.

    Non-call sources reuse the original `Heval` verbatim: `callElimStmt_non_call_eq`
    gives `sts = [st]`, so we close with `σ'' = σ'`.  Call sources are vacuously
    discharged: `step_cmd` only ever produces `.terminal`, never `.exiting`, so
    `(.stmts [.cmd (.call …)] _) →* .exiting lbl _` is unreachable. -/
private theorem callElimStatementCorrect_exit [LawfulBEq Expression.Expr]
    {σ σ' : CoreStore}
    {p : Program}
    {γ γ' : CoreTransformState}
    {st : Statement}
    {sts : List Statement}
    {lbl : String}
    (Heval : Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
      (.stmts [st] ⟨σ, δ, false⟩) (.exiting lbl ⟨σ', δ, false⟩))
    (Helim : (Except.ok sts, γ') = (runWith st (callElimStmt · p) γ)) :
    ∃ σ'',
      Inits σ' σ'' ∧
      Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
        (.stmts sts ⟨σ, δ, false⟩) (.exiting lbl ⟨σ'', δ, false⟩) := by
  have nc_close_exit : ∀ {b : Statement} (_ : st = b)
      (_ : ∀ pn ar mt, b ≠ .cmd (CmdExt.call pn ar mt)),
      ∃ σ'', Inits σ' σ'' ∧
        Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
          (.stmts sts ⟨σ, δ, false⟩) (.exiting lbl ⟨σ'', δ, false⟩) := by
    intro b heq hne
    refine ⟨σ', Inits.init InitVars.init_none, ?_⟩
    have hsts := callElimStmt_non_call_eq hne (heq ▸ Helim)
    rw [hsts]; rw [← heq]; exact Heval
  cases hst : st with
  | block lbl' b md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | ite cd tb eb md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | loop g m i b md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | exit lbl' md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | funcDecl f md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | typeDecl tc md => exact nc_close_exit hst (by intro _ _ _ h; cases h)
  | cmd c =>
      cases c with
      | cmd c' => exact nc_close_exit hst (by intro _ _ _ h; cases h)
      | call procName args md =>
          -- Vacuous: a call statement reaches only `.terminal`.
          subst hst
          -- Peel `.stmts (s :: [])` → `.seq (.stmt s ρ) []` via step_stmts_cons.
          match Heval with
          | .step _ _ _ .step_stmts_cons hrest =>
            -- Use seq_reaches_exiting to split.
            match Imperative.seq_reaches_exiting Expression
                (EvalCommandContract π) (EvalPureFunc φ) hrest with
            | .inl hexit =>
                -- Inner `.stmt (.cmd (.call …)) ρ →* .exiting lbl ρ` is
                -- impossible: step_cmd targets only `.terminal`.
                match hexit with
                | .step _ _ _ (.step_cmd _) hrest' =>
                    cases hrest' with
                    | step _ _ _ h _ => exact absurd h (by intro h; cases h)
            | .inr ⟨_, _, htail⟩ =>
                -- Tail: `.stmts [] ρ₁ →* .exiting lbl ρ'`.  step_stmts_nil
                -- yields `.terminal ρ₁`, which cannot step further to `.exiting`.
                match htail with
                | .step _ _ _ .step_stmts_nil hrest' =>
                    cases hrest' with
                    | step _ _ _ h _ => exact absurd h (by intro h; cases h)

/-- Correctness of `callElimStmt` per source statement, in conjunctive
    `Specification.Overapproximates`-style shape: terminal-arm and
    exit-arm are quantified separately so that an exiting source trace
    is mirrored by an exiting target trace.

    The terminal arm reuses the call-elim chain via
    `callElimStatementCorrect_terminal`.  The exit arm dispatches to
    `callElimStatementCorrect_exit`. -/
theorem callElimStatementCorrect [LawfulBEq Expression.Expr]
    {σ : CoreStore}
    {p : Program}
    {γ γ' : CoreTransformState}
    {st : Statement}
    {sts : List Statement}
    (Hp : ∀ pname, π pname = Program.Procedure.find? p ⟨pname, ()⟩)
    (Hwfc : WellFormedCoreEvalCong δ)
    (Hwf : WF.WFStatementsProp p [st])
    (Hgenrel : CoreGenStateRel σ γ)
    (Hwfcallsite : WFCallSiteProp p π st)
    (Helim : (Except.ok sts, γ') = (runWith st (callElimStmt · p) γ)) :
    -- Terminal arm: polymorphic over the source-side failure flag `f`.
    -- The transformed statements admit a derivation at the same flag,
    -- so source-fail traces map to target-fail traces and source-success
    -- traces map to target-success traces.
    (∀ {σ' : CoreStore} {f : Bool},
      Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
        (.stmts [st] ⟨σ, δ, false⟩) (.terminal ⟨σ', δ, f⟩) →
      ∃ σ'',
        Inits σ' σ'' ∧
        Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
          (.stmts sts ⟨σ, δ, false⟩) (.terminal ⟨σ'', δ, f⟩))
    ∧
    -- Exit arm
    (∀ {lbl : String} {σ' : CoreStore},
      Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
        (.stmts [st] ⟨σ, δ, false⟩) (.exiting lbl ⟨σ', δ, false⟩) →
      ∃ σ'',
        Inits σ' σ'' ∧
        Imperative.StepStmtStar Expression (EvalCommandContract π) (EvalPureFunc φ)
          (.stmts sts ⟨σ, δ, false⟩) (.exiting lbl ⟨σ'', δ, false⟩)) :=
  ⟨fun Heval => callElimStatementCorrect_terminal Hp Heval Hwfc Hwf Hgenrel Hwfcallsite Helim,
   fun Heval => callElimStatementCorrect_exit Heval Helim⟩

end -- public section

end CallElimCorrect

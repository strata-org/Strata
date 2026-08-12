/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.LiftInternalFuncDecls
public import Strata.Transform.CoreTransformProps
public import Strata.Languages.Core.StatementProps
import all Strata.Transform.LiftInternalFuncDecls

/-! # `LiftInternalFuncDecls` structural metatheory

Structural (syntactic) correctness properties of the `LiftInternalFuncDecls`
pass. After it runs, no procedure body contains a `funcDecl` any longer.
The theorem `run_noFuncDecl` states it.

-- TODO: state and prove the top-level semantic correctness of
-- `LiftInternalFuncDecls` via `Overapproximates` from
-- `Strata/Transform/Specification.lean`.
-/

public section

namespace Core
namespace LiftInternalFuncDecls

open Lambda Imperative
open Core.Transform
open Strata.Util (HMap)

/-! ## Snapshot statements are `funcDecl`-free

At a `funcDecl` site the pass emits, per captured variable, a snapshot
`var $__liftfncl_i := c` — each an `init`, hence a `cmd`. -/

/-- The snapshot `init`s a `funcDecl` is replaced by contain no `funcDecl`. -/
private theorem snapshots_noFuncDecl
    (captured : List (CoreIdent × CoreIdent × LMonoTy)) :
    Block.noFuncDecl (captured.map fun (id, f, mty) =>
      Statement.init f (Lambda.LTy.forAll [] mty) (.det (.fvar () id (some mty))) .empty) = true := by
  induction captured with
  | nil => simp [Block.noFuncDecl]
  | cons x rest ih =>
    obtain ⟨id, f, mty⟩ := x
    simp only [List.map_cons, Block.noFuncDecl, Statement.init, Stmt.noFuncDecl, ih, Bool.and_true]

/-! ## Key lemma: the collecting walk strips every `funcDecl` -/

mutual
/-- Whenever collecting from a statement succeeds, its residual block is
`funcDecl`-free. -/
private theorem collectLiftingFuncsFromStmt_noFuncDecl (s : Statement)
    (σ σ' : CoreTransformState) (lfs : List LiftingFunc) (ss' : List Statement)
    (h : collectLiftingFuncsFromStmt s σ = (Except.ok (lfs, ss'), σ')) :
    Block.noFuncDecl ss' = true := by
  match s with
  | .funcDecl decl md =>
    -- The residual is the snapshot `init`s; case-split on `capturedVars decl`
    -- (which `run` may reject): the `.error` arm throws (contradicting `.ok`),
    -- and the `.ok` arm ends in `pure` of the snapshot `init`s.
    cases hc : capturedVars decl with
    | error e =>
      simp only [collectLiftingFuncsFromStmt, hc] at h
      obtain ⟨_, _, hx, _⟩ := bind_ok_inv _ _ h
      rw [throw_apply] at hx
      injection hx with he _
      nomatch he
    | ok c =>
      simp only [collectLiftingFuncsFromStmt, hc] at h
      obtain ⟨_, _, _, h2⟩ := bind_ok_inv _ _ h
      obtain ⟨captured, _, _, h3⟩ := bind_ok_inv _ _ h2
      rw [pure_apply] at h3
      obtain ⟨⟨_, rfl⟩, _⟩ := h3
      exact snapshots_noFuncDecl captured
  | .block l b md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨pr, σ2, hb, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨lfs0, b'⟩ := pr
    rw [pure_apply] at hk
    obtain ⟨⟨_, rfl⟩, _⟩ := hk
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
    exact collectLiftingFuncsFromBlock_noFuncDecl _ _ _ _ _ hb
  | .ite c t e md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨prt, σ2, ht, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨lt, t'⟩ := prt
    obtain ⟨pre, σ3, he, hk2⟩ := bind_ok_inv _ _ hk
    obtain ⟨le, e'⟩ := pre
    rw [pure_apply] at hk2
    obtain ⟨⟨_, rfl⟩, _⟩ := hk2
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true, Bool.and_eq_true]
    exact ⟨collectLiftingFuncsFromBlock_noFuncDecl _ _ _ _ _ ht,
           collectLiftingFuncsFromBlock_noFuncDecl _ _ _ _ _ he⟩
  | .loop g mea inv b md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨pr, σ2, hb, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨lfs0, b'⟩ := pr
    rw [pure_apply] at hk
    obtain ⟨⟨_, rfl⟩, _⟩ := hk
    simp only [Block.noFuncDecl, Stmt.noFuncDecl, Bool.and_true]
    exact collectLiftingFuncsFromBlock_noFuncDecl _ _ _ _ _ hb
  | .cmd c =>
    simp only [collectLiftingFuncsFromStmt, pure_apply] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    simp [Block.noFuncDecl, Stmt.noFuncDecl]
  | .exit l md =>
    simp only [collectLiftingFuncsFromStmt, pure_apply] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    simp [Block.noFuncDecl, Stmt.noFuncDecl]
  | .typeDecl tc md =>
    simp only [collectLiftingFuncsFromStmt, pure_apply] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    simp [Block.noFuncDecl, Stmt.noFuncDecl]
  termination_by sizeOf s

/-- Whenever collecting from a block succeeds, its residual block is
`funcDecl`-free. -/
private theorem collectLiftingFuncsFromBlock_noFuncDecl (ss : List Statement)
    (σ σ' : CoreTransformState) (lfs : List LiftingFunc) (ss' : List Statement)
    (h : collectLiftingFuncsFromBlock ss σ = (Except.ok (lfs, ss'), σ')) :
    Block.noFuncDecl ss' = true := by
  match ss with
  | [] =>
    simp only [collectLiftingFuncsFromBlock, pure_apply] at h
    obtain ⟨⟨_, rfl⟩, _⟩ := h
    simp [Block.noFuncDecl]
  | s :: rest =>
    simp only [collectLiftingFuncsFromBlock] at h
    obtain ⟨p1, σ2, h1, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨p2, σ3, h2, hk2⟩ := bind_ok_inv _ _ hk
    rw [pure_apply] at hk2
    have ⟨hpair, _⟩ := ok_pair_inj hk2
    have hss : p1.2 ++ p2.2 = ss' := congrArg Prod.snd hpair
    rw [← hss, Block.noFuncDecl_append, Bool.and_eq_true]
    exact ⟨collectLiftingFuncsFromStmt_noFuncDecl s σ σ2 p1.1 p1.2 h1,
           collectLiftingFuncsFromBlock_noFuncDecl rest σ2 σ3 p2.1 p2.2 h2⟩
  termination_by sizeOf ss
end

/-! ## Empty `lfs` means the source was already `funcDecl`-free

If the collecting walk returns an empty list of lifting targets, no `funcDecl`
was encountered, so the *original* block already satisfies `noFuncDecl`.  This
covers the early-exit case in `run` where `lfs.isEmpty`. -/

mutual
private theorem collectLiftingFuncsFromStmt_nil_noFuncDecl (s : Statement)
    (σ σ' : CoreTransformState) (ss' : List Statement)
    (h : collectLiftingFuncsFromStmt s σ = (Except.ok ([], ss'), σ')) :
    Stmt.noFuncDecl s = true := by
  match s with
  | .funcDecl decl md =>
    cases hc : capturedVars decl with
    | error e =>
      simp only [collectLiftingFuncsFromStmt, hc] at h
      obtain ⟨_, _, hx, _⟩ := bind_ok_inv _ _ h
      rw [throw_apply] at hx
      injection hx with he _
      nomatch he
    | ok c =>
      simp only [collectLiftingFuncsFromStmt, hc] at h
      obtain ⟨_, _, _, h2⟩ := bind_ok_inv _ _ h
      obtain ⟨_, _, _, h3⟩ := bind_ok_inv _ _ h2
      rw [pure_apply] at h3
      have ⟨hpair, _⟩ := ok_pair_inj h3
      have hlfs := congrArg Prod.fst hpair
      exact absurd hlfs (List.cons_ne_nil _ _)
  | .block l b md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨⟨lfs0, b'⟩, σ2, hb, hk⟩ := bind_ok_inv _ _ h
    rw [pure_apply] at hk
    have ⟨heq, _⟩ := ok_pair_inj hk
    have hlfs : lfs0 = [] := congrArg Prod.fst heq
    simp only [Stmt.noFuncDecl]
    exact collectLiftingFuncsFromBlock_nil_noFuncDecl b σ σ2 b' (by rw [← hlfs]; exact hb)
  | .ite c t e md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨⟨lt, t'⟩, σ2, ht, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨⟨le, e'⟩, σ3, he, hk2⟩ := bind_ok_inv _ _ hk
    rw [pure_apply] at hk2
    have ⟨heq, _⟩ := ok_pair_inj hk2
    have h_app : lt ++ le = [] := congrArg Prod.fst heq
    have hlt : lt = [] := (List.append_eq_nil_iff.mp h_app).1
    have hle : le = [] := (List.append_eq_nil_iff.mp h_app).2
    simp only [Stmt.noFuncDecl, Bool.and_eq_true]
    exact ⟨collectLiftingFuncsFromBlock_nil_noFuncDecl t σ σ2 t' (by rw [← hlt]; exact ht),
           collectLiftingFuncsFromBlock_nil_noFuncDecl e σ2 σ3 e' (by rw [← hle]; exact he)⟩
  | .loop g mea inv b md =>
    simp only [collectLiftingFuncsFromStmt] at h
    obtain ⟨⟨lfs0, b'⟩, σ2, hb, hk⟩ := bind_ok_inv _ _ h
    rw [pure_apply] at hk
    have ⟨heq, _⟩ := ok_pair_inj hk
    have hlfs : lfs0 = [] := congrArg Prod.fst heq
    simp only [Stmt.noFuncDecl]
    exact collectLiftingFuncsFromBlock_nil_noFuncDecl b σ σ2 b' (by rw [← hlfs]; exact hb)
  | .cmd c =>
    simp [Stmt.noFuncDecl]
  | .exit l md =>
    simp [Stmt.noFuncDecl]
  | .typeDecl tc md =>
    simp [Stmt.noFuncDecl]

private theorem collectLiftingFuncsFromBlock_nil_noFuncDecl (ss : List Statement)
    (σ σ' : CoreTransformState) (ss' : List Statement)
    (h : collectLiftingFuncsFromBlock ss σ = (Except.ok ([], ss'), σ')) :
    Block.noFuncDecl ss = true := by
  match ss with
  | [] =>
    simp [Block.noFuncDecl]
  | s :: rest =>
    simp only [collectLiftingFuncsFromBlock] at h
    obtain ⟨⟨l1, s1⟩, σ2, h1, hk⟩ := bind_ok_inv _ _ h
    obtain ⟨⟨l2, r1⟩, σ3, h2, hk2⟩ := bind_ok_inv _ _ hk
    rw [pure_apply] at hk2
    have ⟨heq, _⟩ := ok_pair_inj hk2
    have h_app : l1 ++ l2 = [] := congrArg Prod.fst heq
    have hl1 : l1 = [] := (List.append_eq_nil_iff.mp h_app).1
    have hl2 : l2 = [] := (List.append_eq_nil_iff.mp h_app).2
    simp only [Block.noFuncDecl, Bool.and_eq_true]
    exact ⟨collectLiftingFuncsFromStmt_nil_noFuncDecl s σ σ2 s1 (by rw [← hl1]; exact h1),
           collectLiftingFuncsFromBlock_nil_noFuncDecl rest σ2 σ3 r1 (by rw [← hl2]; exact h2)⟩
end

/-! ## Top-level theorem: `run` eliminates all `funcDecl`s from procedure bodies

This is the advertised structural invariant of the lift pass: after `run`
completes, every procedure in the output program has a `funcDecl`-free structured
body.  The remaining `Decl.func`s (lifted functions) have no body to check. -/

/-- The structural invariant: every `.proc` decl in the list has a `funcDecl`-free
structured body (procedures with CFG bodies are vacuously fine).  Helper for the
per-decl / foldlM decomposition of `run_noFuncDecl`; the exported theorem inlines
this predicate. -/
private def DeclsNoFuncDecl (ds : List Decl) : Prop :=
  ∀ proc md, Decl.proc proc md ∈ ds →
    ∀ ss, proc.body = .structured ss → Block.noFuncDecl ss = true

private theorem DeclsNoFuncDecl.nil : DeclsNoFuncDecl [] := by
  intro _ _ h; exact absurd h List.not_mem_nil

private theorem DeclsNoFuncDecl.append {xs ys : List Decl}
    (hx : DeclsNoFuncDecl xs) (hy : DeclsNoFuncDecl ys) : DeclsNoFuncDecl (xs ++ ys) := by
  intro proc md hmem ss hss
  rcases List.mem_append.mp hmem with h | h
  · exact hx proc md h ss hss
  · exact hy proc md h ss hss

private theorem DeclsNoFuncDecl.singleton_of_notProc {d : Decl}
    (hd : ∀ proc md, d ≠ Decl.proc proc md) : DeclsNoFuncDecl [d] := by
  intro proc md hmem ss hss
  simp only [List.mem_singleton] at hmem
  exact absurd hmem.symm (hd proc md)

/-- A single `.proc` decl with a CFG body trivially satisfies the invariant
(the hypothesis `proc.body = .structured ss` cannot hold). -/
private theorem DeclsNoFuncDecl.singleton_proc_cfg {proc : Procedure} {md : MetaData Expression}
    (hcfg : ∀ ss, proc.body ≠ .structured ss) :
    DeclsNoFuncDecl [Decl.proc proc md] := by
  intro proc' md' hmem ss hss
  simp only [List.mem_singleton] at hmem
  have hp : proc' = proc := by injection hmem
  subst hp
  exact absurd hss (hcfg ss)

private theorem DeclsNoFuncDecl.singleton_proc_structured
    {proc : Procedure} {md : MetaData Expression} {ss : List Statement}
    (hbody : proc.body = .structured ss) (hnf : Block.noFuncDecl ss = true) :
    DeclsNoFuncDecl [Decl.proc proc md] := by
  intro proc' md' hmem ss' hss'
  simp only [List.mem_singleton] at hmem
  have hp : proc' = proc := by injection hmem
  subst hp
  rw [hbody] at hss'
  have hss_eq : ss = ss' := by injection hss'
  subst hss_eq; exact hnf

/-! ### `hoistProcedure`'s output has `noFuncDecl` proc bodies

We first characterize `hoistProcedure`'s output shape: an array whose only
`.proc` element is at the tail, with body `.structured (Statements.mapExprs _ ss)`
when the input body was `.structured ss` (or `.cfg _` unchanged).  Since
`Statements.mapExprs` preserves `noFuncDecl` (`Statements.noFuncDecl_mapExprs`),
the output proc's body is `noFuncDecl` whenever the input's stripped body was. -/

/-- Every element of an array produced by `Array.map (fun x => Decl.func (f x) .empty)`
    (or similar shape) is a `.func`, not a `.proc`.  Uses the general fact that
    the `Decl.func` constructor's image never contains `Decl.proc`. -/
private theorem map_decl_func_no_proc {α : Type} (arr : Array α)
    (g : α → Function) :
    ∀ d ∈ (arr.map (fun x => Decl.func (g x) .empty)).toList,
      ∀ p m, d ≠ Decl.proc p m := by
  intro d hmem p m
  rw [Array.toList_map, List.mem_map] at hmem
  obtain ⟨x, _, heq⟩ := hmem
  rw [← heq]
  exact Decl.noConfusion

/-- Pure characterization of `buildLiftedDecls`: its output is an array whose
    only `.proc` element is at the tail, wrapping the input `proc` with a
    rewritten body.  All earlier elements are `.func`. -/
private theorem buildLiftedDecls_form
    (proc : Procedure) (md : MetaData Expression)
    (named : Array (LiftingFunc × CoreIdent))
    (extMap : Std.HashMap String (List (CoreIdent × CoreIdent × LMonoTy))) :
    ∃ (funcDecls : Array Decl) (newBody : Procedure.Body),
      buildLiftedDecls proc md named extMap =
        funcDecls.push (Decl.proc { proc with body := newBody } md) ∧
      (∀ d ∈ funcDecls.toList, ∀ p m, d ≠ Decl.proc p m) ∧
      (∀ ss, proc.body = .structured ss →
        ∃ f, newBody = .structured (Statements.mapExprs f ss)) := by
  unfold buildLiftedDecls
  refine ⟨_, _, rfl, ?_, ?_⟩
  · -- Every element of `named.map (fun _ => Decl.func ...)` is a `.func`.
    intro d hmem p m
    rw [Array.toList_map, List.mem_map] at hmem
    obtain ⟨x, _, heq⟩ := hmem
    rw [← heq]; exact Decl.noConfusion
  · -- For a structured input body, `newBody` is `.structured (Statements.mapExprs f ss)`.
    intro ss hss
    -- The substitution function `f` is `fun e => e.substOps opSubstList` where
    -- `opSubstList` is the same as in `buildLiftedDecls`.
    refine ⟨(fun e => e.substOps (HMap.ofList <| named.toList.map fun (lf, newName) =>
      let extCap := extMap.getD lf.decl.name.name []
      let capMtys : List LMonoTy := extCap.map fun (_, _, mty) => mty
      (lf.decl.name, fun oldTy =>
        LExpr.mkApp () (.op () newName (oldTy.map (LMonoTy.mkArrow' · capMtys)))
          (extCap.map fun (_, f, mty) => .fvar () f (some mty))))), ?_⟩
    show (match proc.body with
      | Procedure.Body.structured ss' => Procedure.Body.structured (Statements.mapExprs _ ss')
      | Procedure.Body.cfg _ => proc.body) = _
    rw [hss]

/-- The output of `hoistProcedure` on a structured-body procedure is an array
whose only `.proc` element carries the `Statements.mapExprs`-rewritten body.
This reads off directly from the pure `buildLiftedDecls` characterization above. -/
private theorem hoistProcedure_output_form
    {proc : Procedure} {md : MetaData Expression}
    {lfs : List LiftingFunc} {arr : Array Decl}
    {σ σ' : CoreTransformState}
    (h : hoistProcedure proc md lfs σ = (Except.ok arr, σ')) :
    ∃ (funcDecls : Array Decl) (newBody : Procedure.Body),
      arr = funcDecls.push (Decl.proc { proc with body := newBody } md) ∧
      (∀ d ∈ funcDecls.toList, ∀ p m, d ≠ Decl.proc p m) ∧
      (∀ ss, proc.body = .structured ss →
        ∃ f, newBody = .structured (Statements.mapExprs f ss)) := by
  -- `hoistProcedure` unfolds to two stateful phases (name-minting and
  -- capture-fixed-point) followed by `return (buildLiftedDecls proc md named extMap)`.
  -- Peel the two state binds and the outer `pure` to expose `arr = buildLiftedDecls ...`.
  simp only [hoistProcedure] at h
  obtain ⟨named, σ2, _, h⟩ := bind_ok_inv _ _ h
  obtain ⟨extMap, σ3, _, h⟩ := bind_ok_inv _ _ h
  rw [pure_apply] at h
  have ⟨hpair, _⟩ := ok_pair_inj h
  -- Now `hpair : buildLiftedDecls proc md named extMap = arr`.  The pure
  -- characterization of `buildLiftedDecls` gives the required existentials.
  obtain ⟨funcDecls, newBody, hbld, hfd, hnb⟩ := buildLiftedDecls_form proc md named extMap
  exact ⟨funcDecls, newBody, hpair.symm.trans hbld, hfd, hnb⟩

private theorem hoistProcedure_noFuncDecl
    {proc : Procedure} {md : MetaData Expression}
    {lfs : List LiftingFunc} {arr : Array Decl}
    {σ σ' : CoreTransformState}
    {stripped : List Statement}
    (hbody : proc.body = .structured stripped)
    (hstripped : Block.noFuncDecl stripped = true)
    (h : hoistProcedure proc md lfs σ = (Except.ok arr, σ')) :
    DeclsNoFuncDecl arr.toList := by
  obtain ⟨funcDecls, newBody, harr, hfd, hnb⟩ := hoistProcedure_output_form h
  obtain ⟨f, hnb_eq⟩ := hnb stripped hbody
  subst harr
  simp only [Array.toList_push]
  apply DeclsNoFuncDecl.append
  · -- Every element in `funcDecls.toList` is a `.func`, not a `.proc`.
    intro proc' md' hmem ss hss
    exact absurd rfl (hfd _ hmem proc' md')
  · -- The last element: `Decl.proc { proc with body := newBody } md`.
    apply DeclsNoFuncDecl.singleton_proc_structured
      (ss := Statements.mapExprs f stripped)
    · show ({ proc with body := newBody }).body = _
      simp [hnb_eq]
    · rw [Statements.noFuncDecl_mapExprs]; exact hstripped

/-! ### Per-decl invariant

`processDecl` — the per-decl body of `run`'s foldlM — outputs a list that
satisfies `DeclsNoFuncDecl` whenever it succeeds. -/

private theorem processDecl_noFuncDecl
    {topLevelFuncNames : Std.HashSet String} {decl : Decl}
    {out : List Decl} {σ σ' : CoreTransformState}
    (h : processDecl topLevelFuncNames decl σ = (Except.ok out, σ')) :
    DeclsNoFuncDecl out := by
  cases decl with
  | proc proc md =>
    simp only [processDecl] at h
    -- Split on the body: cfg vs structured.
    match hbody : proc.body with
    | .cfg c =>
      simp only [hbody] at h
      rw [pure_apply] at h
      have ⟨hpair, _⟩ := ok_pair_inj h
      subst hpair
      apply DeclsNoFuncDecl.singleton_proc_cfg
      intro ss hcontra; rw [hbody] at hcontra; exact Procedure.Body.noConfusion hcontra
    | .structured ss =>
      simp only [hbody] at h
      obtain ⟨⟨lfs, stripped⟩, σ2, hstep, hk⟩ := bind_ok_inv _ _ h
      -- Now split on `lfs.isEmpty`.
      by_cases hemp : lfs.isEmpty
      · -- lfs is empty: original decl pushed unchanged.
        simp only [hemp, if_true] at hk
        rw [pure_apply] at hk
        have ⟨hpair, _⟩ := ok_pair_inj hk
        subst hpair
        have hlfs : lfs = [] := List.isEmpty_iff.mp hemp
        subst hlfs
        apply DeclsNoFuncDecl.singleton_proc_structured (ss := ss) hbody
        exact collectLiftingFuncsFromBlock_nil_noFuncDecl ss σ σ2 stripped hstep
      · -- lfs is non-empty: check all guards, then hoistProcedure.
        have hlfs_empty : lfs.isEmpty = false := Bool.eq_false_iff.mpr hemp
        simp only [hlfs_empty, Bool.false_eq_true, if_false] at hk
        have hstripped : Block.noFuncDecl stripped = true :=
          collectLiftingFuncsFromBlock_noFuncDecl ss σ σ2 lfs stripped hstep
        -- Peel off the four guards.  Each has the form `if !X.isEmpty then throw`.
        -- In do-notation an if-without-else is desugared with `else pure PUnit.unit`.
        -- If the guard triggers, `throw` fires and we reach `throw ... = .ok`, contradiction.
        -- Otherwise, `pure PUnit.unit` is bound and we continue.
        -- We peel each guard via a case-split on `X.isEmpty`.
        by_cases hrec : ((lfs.filter (·.decl.isRecursive)).map (·.decl.name.name)).dedup = []
        · by_cases hdup : ((lfs.map (·.decl.name.name)).filter
              (fun n => (lfs.map (·.decl.name.name)).count n > 1)).dedup = []
          · by_cases hcl : ((lfs.map (·.decl.name.name)).filter
                topLevelFuncNames.contains).dedup = []
            · by_cases hlt : Imperative.Block.hasLocalTypeDecl ss = false
              · -- All guards' conditions are empty, so all `!X.isEmpty` are false;
                -- each guard reduces to `pure PUnit.unit`.  What remains, after
                -- peeling the four trivial pure-binds, is the `hoistProcedure` bind.
                simp only [hrec, hdup, hcl, hlt, List.isEmpty_nil, Bool.not_true,
                           Bool.false_eq_true, if_false] at hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨arr, σ3, hh, hkk⟩ := bind_ok_inv _ _ hk
                rw [pure_apply] at hkk
                have ⟨hpair, _⟩ := ok_pair_inj hkk
                subst hpair
                exact hoistProcedure_noFuncDecl (stripped := stripped)
                  (by show ({ proc with body := .structured stripped }).body = _; rfl)
                  hstripped hh
              · -- localTypes present: the fourth guard fires, `throw` reaches `.ok`.
                exfalso
                have hlt_ne : Imperative.Block.hasLocalTypeDecl ss = true := by
                  cases h : Imperative.Block.hasLocalTypeDecl ss
                  · exact absurd h hlt
                  · rfl
                simp only [hrec, hdup, hcl, hlt_ne, List.isEmpty_nil, Bool.not_true,
                           Bool.false_eq_true, if_false, if_true] at hk
                -- Peel three pure-binds, then a `let _ ← throw _` (which is `throw` in monad).
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
                obtain ⟨_, _, hthrow, _⟩ := bind_ok_inv _ _ hk
                rw [throw_apply] at hthrow; injection hthrow with he _; nomatch he
            · exfalso
              have hcl_ne : ((lfs.map (·.decl.name.name)).filter topLevelFuncNames.contains).dedup.isEmpty = false :=
                List.isEmpty_eq_false_iff.mpr hcl
              simp only [hrec, hdup, hcl_ne, List.isEmpty_nil, Bool.not_true, Bool.not_false,
                         Bool.false_eq_true, if_false, if_true] at hk
              obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
              obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
              obtain ⟨_, _, hthrow, _⟩ := bind_ok_inv _ _ hk
              rw [throw_apply] at hthrow; injection hthrow with he _; nomatch he
          · exfalso
            have hdup_ne : ((lfs.map (·.decl.name.name)).filter
                (fun n => (lfs.map (·.decl.name.name)).count n > 1)).dedup.isEmpty = false :=
              List.isEmpty_eq_false_iff.mpr hdup
            simp only [hrec, hdup_ne, List.isEmpty_nil, Bool.not_true, Bool.not_false,
                       Bool.false_eq_true, if_false, if_true] at hk
            obtain ⟨_, _, _, hk⟩ := bind_ok_inv _ _ hk
            obtain ⟨_, _, hthrow, _⟩ := bind_ok_inv _ _ hk
            rw [throw_apply] at hthrow; injection hthrow with he _; nomatch he
        · exfalso
          have hrec_ne : ((lfs.filter (·.decl.isRecursive)).map (·.decl.name.name)).dedup.isEmpty = false :=
            List.isEmpty_eq_false_iff.mpr hrec
          simp only [hrec_ne, Bool.not_false, if_true] at hk
          obtain ⟨_, _, hthrow, _⟩ := bind_ok_inv _ _ hk
          rw [throw_apply] at hthrow; injection hthrow with he _; nomatch he
  | type t md =>
    simp only [processDecl] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair
    apply DeclsNoFuncDecl.singleton_of_notProc
    intro _ _ hc; exact Decl.noConfusion hc
  | ax a md =>
    simp only [processDecl] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair
    apply DeclsNoFuncDecl.singleton_of_notProc
    intro _ _ hc; exact Decl.noConfusion hc
  | distinct n es md =>
    simp only [processDecl] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair
    apply DeclsNoFuncDecl.singleton_of_notProc
    intro _ _ hc; exact Decl.noConfusion hc
  | func f md =>
    simp only [processDecl] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair
    apply DeclsNoFuncDecl.singleton_of_notProc
    intro _ _ hc; exact Decl.noConfusion hc
  | recFuncBlock fs md =>
    simp only [processDecl] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair
    apply DeclsNoFuncDecl.singleton_of_notProc
    intro _ _ hc; exact Decl.noConfusion hc

/-! ### The `foldlM` invariant

If every per-decl step preserves `DeclsNoFuncDecl` on its contribution, then
the whole `foldlM` accumulates a `DeclsNoFuncDecl` output. -/

private theorem run_foldlM_noFuncDecl
    {topLevelFuncNames : Std.HashSet String}
    {decls : List Decl} {acc acc' : Array Decl}
    {σ σ' : CoreTransformState}
    (hacc : DeclsNoFuncDecl acc.toList)
    (h : decls.foldlM (init := acc) (m := CoreTransformM)
           (fun a d => do
             let contrib ← processDecl topLevelFuncNames d
             pure (a ++ contrib.toArray)) σ = (Except.ok acc', σ')) :
    DeclsNoFuncDecl acc'.toList := by
  induction decls generalizing acc σ with
  | nil =>
    simp only [List.foldlM_nil] at h
    rw [pure_apply] at h
    have ⟨hpair, _⟩ := ok_pair_inj h
    subst hpair; exact hacc
  | cons d rest ih =>
    simp only [List.foldlM_cons] at h
    -- `h : (f acc d >>= fun a2 => rest.foldlM f a2) σ = .ok`, where
    -- `f a d = processDecl _ d >>= fun c => pure (a ++ c.toArray)`.
    obtain ⟨acc2, σ2, hstep, hk⟩ := bind_ok_inv _ _ h
    -- `hstep : (processDecl _ d >>= fun c => pure (acc ++ c.toArray)) σ = .ok (acc2, σ2)`.
    obtain ⟨contrib, σ2', hc, hp⟩ := bind_ok_inv _ _ hstep
    rw [pure_apply] at hp
    have ⟨hpair, _⟩ := ok_pair_inj hp
    subst hpair
    apply ih _ hk
    simp only [Array.toList_append]
    apply DeclsNoFuncDecl.append hacc
    exact processDecl_noFuncDecl hc

/-- After `LiftInternalFuncDecls.run`, every procedure's structured body satisfies
`Block.noFuncDecl` — procedures with CFG bodies are vacuously fine.  This is the
structural invariant advertised by the lift pass: downstream transform proofs
can assume `Stmt.noFuncDecl` on procedure bodies. -/
theorem run_noFuncDecl {p p' : Program} {σ σ' : CoreTransformState}
    (h : LiftInternalFuncDecls.run p σ = (Except.ok p', σ')) :
    ∀ proc md, Decl.proc proc md ∈ p'.decls →
      ∀ ss, proc.body = .structured ss → Block.noFuncDecl ss = true := by
  -- Reduce to `DeclsNoFuncDecl p'.decls` (the same statement, packaged), then
  -- discharge via the `foldlM` invariant.
  show DeclsNoFuncDecl p'.decls
  simp only [LiftInternalFuncDecls.run] at h
  obtain ⟨out, σ2, hfold, hret⟩ := bind_ok_inv _ _ h
  rw [pure_apply] at hret
  have ⟨hpair, _⟩ := ok_pair_inj hret
  -- p' = { decls := out.toList }
  have : p'.decls = out.toList := by
    rw [← hpair]
  rw [this]
  exact run_foldlM_noFuncDecl (by simp [DeclsNoFuncDecl.nil]) hfold

end LiftInternalFuncDecls
end Core

end -- public section

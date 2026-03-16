/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelDenote
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelDenoteBridge

/-!
# Soundness: Denotational Interpreter Implies Relational Semantics

If `denoteStmt` returns a result, then `EvalLaurelStmt` has a matching
derivation (and similarly for `denoteBlock`/`denoteArgs`).

Proof strategy: induction on `fuel`, then case-split on the input.
For each constructor, unfold `denoteStmt`, decompose the match chain,
apply IH to sub-calls, and construct the relational derivation.
Helpers for While, StaticCall, and InstanceCall are extracted to
stay within heartbeat limits.
-/

namespace Strata.Laurel

private abbrev MD := Imperative.MetaData Core.Expression

/-! ## Helper lemma for the While case -/

private theorem denoteStmt_sound_while
    {δ : LaurelEval} {π : ProcEnv} {n : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {c : StmtExprMd} {invs : List StmtExprMd} {dec : Option StmtExprMd}
    {body : StmtExprMd}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (md : MD)
    (ih_stmt : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {s₀ : StmtExpr}
      {o₀ : Outcome} {σ₀' : LaurelStore} {h₀' : LaurelHeap} (md₀ : MD),
      denoteStmt δ π n h₀ σ₀ s₀ = some (o₀, σ₀', h₀') →
      EvalLaurelStmt δ π h₀ σ₀ ⟨s₀, md₀⟩ h₀' σ₀' o₀)
    (heval : denoteStmt δ π (n + 1) h σ (.While c invs dec body) = some (o, σ', h')) :
    EvalLaurelStmt δ π h σ ⟨.While c invs dec body, md⟩ h' σ' o := by
  simp only [denoteStmt] at heval
  match hc : denoteStmt δ π n h σ c.val with
  | some (.normal (.vBool true), σ₁, h₁) =>
    simp [hc] at heval
    match hbody : denoteStmt δ π n h₁ σ₁ body.val with
    | some (.normal _, σ₂, h₂) =>
      simp [hbody] at heval
      exact .while_true (ih_stmt c.md hc) (ih_stmt body.md hbody) (ih_stmt md heval)
    | some (.exit label, σ₂, h₂) =>
      simp [hbody] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
      exact .while_exit (ih_stmt c.md hc) (ih_stmt body.md hbody)
    | some (.ret rv, σ₂, h₂) =>
      simp [hbody] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
      exact .while_return (ih_stmt c.md hc) (ih_stmt body.md hbody)
    | none => simp [hbody] at heval
  | some (.normal (.vBool false), σ₁, h₁) =>
    simp [hc] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
    exact .while_false (ih_stmt c.md hc)
  | some (.normal (.vInt _), _, _) => simp [hc] at heval
  | some (.normal (.vString _), _, _) => simp [hc] at heval
  | some (.normal .vVoid, _, _) => simp [hc] at heval
  | some (.normal (.vRef _), _, _) => simp [hc] at heval
  | some (.exit _, _, _) => simp [hc] at heval
  | some (.ret _, _, _) => simp [hc] at heval
  | none => simp [hc] at heval

/-! ## Helper lemma for the StaticCall case -/

private theorem denoteStmt_sound_static_call
    {δ : LaurelEval} {π : ProcEnv} {n : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {callee : Identifier} {args : List StmtExprMd}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (md : MD)
    (ih_stmt : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {s₀ : StmtExpr}
      {o₀ : Outcome} {σ₀' : LaurelStore} {h₀' : LaurelHeap} (md₀ : MD),
      denoteStmt δ π n h₀ σ₀ s₀ = some (o₀, σ₀', h₀') →
      EvalLaurelStmt δ π h₀ σ₀ ⟨s₀, md₀⟩ h₀' σ₀' o₀)
    (ih_args : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {as₀ : List StmtExprMd}
      {vs₀ : List LaurelValue} {σ₀' : LaurelStore} {h₀' : LaurelHeap},
      denoteArgs δ π n h₀ σ₀ as₀ = some (vs₀, σ₀', h₀') →
      EvalStmtArgs δ π h₀ σ₀ as₀ h₀' σ₀' vs₀)
    (heval : denoteStmt δ π (n + 1) h σ (.StaticCall callee args) = some (o, σ', h')) :
    EvalLaurelStmt δ π h σ ⟨.StaticCall callee args, md⟩ h' σ' o := by
  simp only [denoteStmt] at heval
  match hp : π callee with
  | some proc =>
    simp [hp] at heval
    match hargs : denoteArgs δ π n h σ args with
    | some (vals, σ₁, h₁) =>
      simp [hargs] at heval
      match hbind : bindParams proc.inputs vals with
      | some σBound =>
        simp [hbind] at heval
        match hgetb : getBody proc with
        | some body =>
          simp [hgetb] at heval
          match hcall : denoteStmt δ π n h₁ σBound body.val with
          | some (.normal v, _, h₂) =>
            simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .static_call hp (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
          | some (.ret (some v), _, h₂) =>
            simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .static_call_return hp (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
          | some (.ret none, _, h₂) =>
            simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .static_call_return_void hp (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
          | some (.exit _, _, _) => simp [hcall] at heval
          | none => simp [hcall] at heval
        | none => simp [hgetb] at heval
      | none => simp [hbind] at heval
    | none => simp [hargs] at heval
  | none => simp [hp] at heval

/-! ## Helper lemma for the InstanceCall case -/

private theorem denoteStmt_sound_instance_call
    {δ : LaurelEval} {π : ProcEnv} {n : Nat}
    {h : LaurelHeap} {σ : LaurelStore}
    {target : StmtExprMd} {callee : Identifier} {args : List StmtExprMd}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (md : MD)
    (ih_stmt : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {s₀ : StmtExpr}
      {o₀ : Outcome} {σ₀' : LaurelStore} {h₀' : LaurelHeap} (md₀ : MD),
      denoteStmt δ π n h₀ σ₀ s₀ = some (o₀, σ₀', h₀') →
      EvalLaurelStmt δ π h₀ σ₀ ⟨s₀, md₀⟩ h₀' σ₀' o₀)
    (ih_args : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {as₀ : List StmtExprMd}
      {vs₀ : List LaurelValue} {σ₀' : LaurelStore} {h₀' : LaurelHeap},
      denoteArgs δ π n h₀ σ₀ as₀ = some (vs₀, σ₀', h₀') →
      EvalStmtArgs δ π h₀ σ₀ as₀ h₀' σ₀' vs₀)
    (heval : denoteStmt δ π (n + 1) h σ (.InstanceCall target callee args) = some (o, σ', h')) :
    EvalLaurelStmt δ π h σ ⟨.InstanceCall target callee args, md⟩ h' σ' o := by
  simp only [denoteStmt] at heval
  match ht : denoteStmt δ π n h σ target.val with
  | some (.normal (.vRef addr), σ₁, h₁) =>
    simp [ht] at heval
    match hlook : h₁ addr with
    | some (typeName, fields) =>
      simp [hlook] at heval
      match hproc : π (↑(typeName ++ "." ++ callee.text)) with
      | some proc =>
        simp [hproc] at heval
        match hargs : denoteArgs δ π n h₁ σ₁ args with
        | some (vals, σ₂, h₂) =>
          simp [hargs] at heval
          match hbind : bindParams proc.inputs (LaurelValue.vRef addr :: vals) with
          | some σBound =>
            simp [hbind] at heval
            match hgetb : getBody proc with
            | some body =>
              simp [hgetb] at heval
              match hcall : denoteStmt δ π n h₂ σBound body.val with
              | some (.normal v, _, h₃) =>
                simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
                exact .instance_call (ih_stmt target.md ht) hlook hproc
                  (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
              | some (.ret (some v), _, h₃) =>
                simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
                exact .instance_call_return (ih_stmt target.md ht) hlook hproc
                  (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
              | some (.ret none, _, h₃) =>
                simp [hcall] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
                exact .instance_call_return_void (ih_stmt target.md ht) hlook hproc
                  (ih_args hargs) hbind hgetb (ih_stmt body.md hcall)
              | some (.exit _, _, _) => simp [hcall] at heval
              | none => simp [hcall] at heval
            | none => simp [hgetb] at heval
          | none => simp [hbind] at heval
        | none => simp [hargs] at heval
      | none => simp [hproc] at heval
    | none => simp [hlook] at heval
  | some (.normal (.vInt _), _, _) => simp [ht] at heval
  | some (.normal (.vBool _), _, _) => simp [ht] at heval
  | some (.normal (.vString _), _, _) => simp [ht] at heval
  | some (.normal .vVoid, _, _) => simp [ht] at heval
  | some (.exit _, _, _) => simp [ht] at heval
  | some (.ret _, _, _) => simp [ht] at heval
  | none => simp [ht] at heval

/-! ## Main soundness theorems -/

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 4096 in
mutual
theorem denoteStmt_sound
    {δ : LaurelEval} {π : ProcEnv} (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {s : StmtExpr}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (md : MD)
    (heval : denoteStmt δ π fuel h σ s = some (o, σ', h')) :
    EvalLaurelStmt δ π h σ ⟨s, md⟩ h' σ' o := by
  match fuel with
  | 0 => simp [denoteStmt] at heval
  | n + 1 =>
    have ih_stmt : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {s₀ : StmtExpr}
        {o₀ : Outcome} {σ₀' : LaurelStore} {h₀' : LaurelHeap} (md₀ : MD),
        denoteStmt δ π n h₀ σ₀ s₀ = some (o₀, σ₀', h₀') →
        EvalLaurelStmt δ π h₀ σ₀ ⟨s₀, md₀⟩ h₀' σ₀' o₀ :=
      fun md₀ hev => denoteStmt_sound n md₀ hev
    have ih_args : ∀ {h₀ : LaurelHeap} {σ₀ : LaurelStore} {as₀ : List StmtExprMd}
        {vs₀ : List LaurelValue} {σ₀' : LaurelStore} {h₀' : LaurelHeap},
        denoteArgs δ π n h₀ σ₀ as₀ = some (vs₀, σ₀', h₀') →
        EvalStmtArgs δ π h₀ σ₀ as₀ h₀' σ₀' vs₀ :=
      fun hev => denoteArgs_sound n hev
    match s with
    | .LiteralInt _ =>
      simp [denoteStmt] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .literal_int
    | .LiteralBool _ =>
      simp [denoteStmt] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .literal_bool
    | .LiteralString _ =>
      simp [denoteStmt] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .literal_string
    | .Identifier name =>
      simp only [denoteStmt] at heval
      match hlook : σ name.text with
      | some v => simp [hlook] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .identifier hlook
      | none => simp [hlook] at heval
    | .PrimitiveOp op args =>
      simp only [denoteStmt] at heval
      match hargs : denoteArgs δ π n h σ args with
      | some (vals, σ₁, h₁) =>
        simp [hargs] at heval
        match hop : evalPrimOp op vals with
        | some result =>
          simp [hop] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
          exact .prim_op (ih_args hargs) hop
        | none => simp [hop] at heval
      | none => simp [hargs] at heval
    | .IfThenElse c thenBr (some elseBr) =>
      simp only [denoteStmt] at heval
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        simp [hc] at heval; exact .ite_true (ih_stmt c.md hc) (ih_stmt thenBr.md heval)
      | some (.normal (.vBool false), σ₁, h₁) =>
        simp [hc] at heval; exact .ite_false (ih_stmt c.md hc) (ih_stmt elseBr.md heval)
      | some (.normal (.vInt _), _, _) | some (.normal (.vString _), _, _)
      | some (.normal .vVoid, _, _) | some (.normal (.vRef _), _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hc] at heval
    | .IfThenElse c thenBr none =>
      simp only [denoteStmt] at heval
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        simp [hc] at heval; exact .ite_true_no_else (ih_stmt c.md hc) (ih_stmt thenBr.md heval)
      | some (.normal (.vBool false), σ₁, h₁) =>
        simp [hc] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .ite_false_no_else (ih_stmt c.md hc)
      | some (.normal (.vInt _), _, _) | some (.normal (.vString _), _, _)
      | some (.normal .vVoid, _, _) | some (.normal (.vRef _), _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hc] at heval
    | .Block stmts label =>
      simp only [denoteStmt] at heval
      match hblk : denoteBlock δ π n h σ stmts with
      | some (outcome, σ₁, h₁) =>
        simp [hblk] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .block_sem (denoteBlock_sound n hblk) rfl
      | none => simp [hblk] at heval
    | .Exit target =>
      simp [denoteStmt] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .exit_sem
    | .Return (some val) =>
      simp only [denoteStmt] at heval
      match hv : denoteStmt δ π n h σ val.val with
      | some (.normal v, σ₁, h₁) =>
        simp [hv] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .return_some (ih_stmt val.md hv)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hv] at heval
    | .Return none =>
      simp [denoteStmt] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .return_none
    | .While c invs dec body => exact denoteStmt_sound_while md ih_stmt heval
    | .Assign [⟨.Identifier name, tmd⟩] value =>
      simp only [denoteStmt] at heval
      match hv : denoteStmt δ π n h σ value.val with
      | some (.normal v, σ₁, h₁) =>
        simp [hv] at heval
        match hlook : σ₁ name.text with
        | some _ =>
          simp [hlook] at heval
          match hup : updateStore σ₁ name v with
          | some σ₂ =>
            simp [hup] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .assign_single (ih_stmt value.md hv) hlook (updateStore_sound hup)
          | none => simp [hup] at heval
        | none => simp [hlook] at heval
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hv] at heval
    | .Assign [⟨.FieldSelect target fieldName, tmd⟩] value =>
      simp only [denoteStmt] at heval
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        simp [ht] at heval
        match hv : denoteStmt δ π n h₁ σ₁ value.val with
        | some (.normal v, σ₂, h₂) =>
          simp [hv] at heval
          match hw : heapFieldWrite' h₂ addr fieldName.text v with
          | some h₃ =>
            simp [hw] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .assign_field (ih_stmt target.md ht) (ih_stmt value.md hv) (heapFieldWrite_sound hw)
          | none => simp [hw] at heval
        | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hv] at heval
      | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [ht] at heval
    -- Assign: all other LHS patterns return none
    | .Assign [] _ | .Assign (_ :: _ :: _) _ => simp [denoteStmt] at heval
    | .Assign [⟨.LiteralInt _, _⟩] _ | .Assign [⟨.LiteralBool _, _⟩] _
    | .Assign [⟨.LiteralString _, _⟩] _ | .Assign [⟨.PrimitiveOp _ _, _⟩] _
    | .Assign [⟨.IfThenElse _ _ _, _⟩] _ | .Assign [⟨.Block _ _, _⟩] _
    | .Assign [⟨.Exit _, _⟩] _ | .Assign [⟨.Return _, _⟩] _
    | .Assign [⟨.While _ _ _ _, _⟩] _ | .Assign [⟨.Assign _ _, _⟩] _
    | .Assign [⟨.LocalVariable _ _ _, _⟩] _ | .Assign [⟨.Assert _, _⟩] _
    | .Assign [⟨.Assume _, _⟩] _ | .Assign [⟨.StaticCall _ _, _⟩] _
    | .Assign [⟨.New _, _⟩] _ | .Assign [⟨.PureFieldUpdate _ _ _, _⟩] _
    | .Assign [⟨.ReferenceEquals _ _, _⟩] _ | .Assign [⟨.InstanceCall _ _ _, _⟩] _
    | .Assign [⟨.This, _⟩] _ | .Assign [⟨.IsType _ _, _⟩] _
    | .Assign [⟨.AsType _ _, _⟩] _ | .Assign [⟨.Forall _ _ _, _⟩] _
    | .Assign [⟨.Exists _ _ _, _⟩] _ | .Assign [⟨.Old _, _⟩] _
    | .Assign [⟨.Fresh _, _⟩] _ | .Assign [⟨.Assigned _, _⟩] _
    | .Assign [⟨.ProveBy _ _, _⟩] _ | .Assign [⟨.ContractOf _ _, _⟩] _
    | .Assign [⟨.Abstract, _⟩] _ | .Assign [⟨.All, _⟩] _
    | .Assign [⟨.Hole, _⟩] _ => simp [denoteStmt] at heval
    | .LocalVariable name _ty (some init) =>
      simp only [denoteStmt] at heval
      match hv : denoteStmt δ π n h σ init.val with
      | some (.normal v, σ₁, h₁) =>
        simp [hv] at heval
        match hi : initStore σ₁ name v with
        | some σ₂ =>
          simp [hi] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
          have hnone : σ₁ name.text = none := by
            unfold initStore at hi; split at hi <;> simp_all
          exact .local_var_init (ih_stmt init.md hv) hnone (initStore_sound hi)
        | none => simp [hi] at heval
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hv] at heval
    | .LocalVariable name _ty none =>
      simp only [denoteStmt] at heval
      match hi : initStore σ name .vVoid with
      | some σ' =>
        simp [hi] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        have hnone : σ name.text = none := by
          unfold initStore at hi; split at hi <;> simp_all
        exact .local_var_uninit hnone (initStore_sound hi)
      | none => simp [hi] at heval
    | .Assert c =>
      simp only [denoteStmt] at heval
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), σ_c, h_c) =>
        simp [hc] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .assert_true (ih_stmt c.md hc)
      | some (.normal (.vBool false), _, _) | some (.normal (.vInt _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.normal (.vRef _), _, _) | some (.exit _, _, _)
      | some (.ret _, _, _) | none => simp [hc] at heval
    | .Assume c =>
      simp only [denoteStmt] at heval
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), σ_c, h_c) =>
        simp [hc] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .assume_true (ih_stmt c.md hc)
      | some (.normal (.vBool false), _, _) | some (.normal (.vInt _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.normal (.vRef _), _, _) | some (.exit _, _, _)
      | some (.ret _, _, _) | none => simp [hc] at heval
    | .StaticCall callee args => exact denoteStmt_sound_static_call md ih_stmt ih_args heval
    | .New typeName =>
      simp only [denoteStmt] at heval
      match ha : allocHeap h typeName.text with
      | some (addr, h'') =>
        simp [ha] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .new_obj (allocHeap_sound ha)
      | none => simp [ha] at heval
    | .FieldSelect target fieldName =>
      simp only [denoteStmt] at heval
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        simp [ht] at heval
        match hf : heapFieldRead h₁ addr fieldName.text with
        | some v => simp [hf] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
                    exact .field_select (ih_stmt target.md ht) hf
        | none => simp [hf] at heval
      | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [ht] at heval
    | .PureFieldUpdate target fieldName newVal =>
      simp only [denoteStmt] at heval
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        simp [ht] at heval
        match hv : denoteStmt δ π n h₁ σ₁ newVal.val with
        | some (.normal v, σ₂, h₂) =>
          simp [hv] at heval
          match hw : heapFieldWrite' h₂ addr fieldName.text v with
          | some h₃ =>
            simp [hw] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
            exact .pure_field_update (ih_stmt target.md ht) (ih_stmt newVal.md hv) (heapFieldWrite_sound hw)
          | none => simp [hw] at heval
        | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hv] at heval
      | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [ht] at heval
    | .ReferenceEquals lhs rhs =>
      simp only [denoteStmt] at heval
      match hl : denoteStmt δ π n h σ lhs.val with
      | some (.normal (.vRef a), σ₁, h₁) =>
        simp [hl] at heval
        match hr : denoteStmt δ π n h₁ σ₁ rhs.val with
        | some (.normal (.vRef b), σ₂, h₂) =>
          simp [hr] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
          exact .reference_equals (ih_stmt lhs.md hl) (ih_stmt rhs.md hr)
        | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
        | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
        | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hr] at heval
      | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [hl] at heval
    | .InstanceCall target callee args =>
      exact denoteStmt_sound_instance_call md ih_stmt ih_args heval
    | .This =>
      simp only [denoteStmt] at heval
      match hlook : σ "this" with
      | some v => simp [hlook] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .this_sem hlook
      | none => simp [hlook] at heval
    | .IsType target ty =>
      simp only [denoteStmt] at heval
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        simp [ht] at heval
        match hlook : h₁ addr with
        | some (actualType, _) =>
          simp [hlook] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
          exact .is_type (ih_stmt target.md ht) hlook
        | none => simp [hlook] at heval
      | some (.normal (.vInt _), _, _) | some (.normal (.vBool _), _, _)
      | some (.normal (.vString _), _, _) | some (.normal .vVoid, _, _)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [ht] at heval
    | .AsType target _ty =>
      simp only [denoteStmt] at heval
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal v, σ₁, h₁) =>
        simp [ht] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .as_type (ih_stmt target.md ht)
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [ht] at heval
    | .Forall name ty body =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.Forall name ty body) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .forall_sem hd
      | none => simp [hd] at heval
    | .Exists name ty body =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.Exists name ty body) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .exists_sem hd
      | none => simp [hd] at heval
    | .Old val =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.Old val) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .old_sem hd
      | none => simp [hd] at heval
    | .Fresh val =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.Fresh val) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .fresh_sem hd
      | none => simp [hd] at heval
    | .Assigned name =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.Assigned name) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .assigned_sem hd
      | none => simp [hd] at heval
    | .ProveBy value _proof =>
      simp only [denoteStmt] at heval
      exact .prove_by (ih_stmt value.md heval)
    | .ContractOf ct func =>
      simp only [denoteStmt] at heval
      match hd : δ σ (.ContractOf ct func) with
      | some v => simp [hd] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .contract_of hd
      | none => simp [hd] at heval
    | .Abstract | .All | .Hole => simp [denoteStmt] at heval

theorem denoteBlock_sound
    {δ : LaurelEval} {π : ProcEnv} (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {ss : List StmtExprMd}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (heval : denoteBlock δ π fuel h σ ss = some (o, σ', h')) :
    EvalLaurelBlock δ π h σ ss h' σ' o := by
  match fuel with
  | 0 => simp [denoteBlock] at heval
  | n + 1 =>
    match ss with
    | [] => simp [denoteBlock] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .nil
    | [s] =>
      simp only [denoteBlock] at heval
      match hs : denoteStmt δ π n h σ s.val with
      | some (.normal v, σ₁, h₁) =>
        simp [hs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .last_normal (denoteStmt_sound n s.md hs)
      | some (.exit label, σ₁, h₁) =>
        simp [hs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .cons_exit (denoteStmt_sound n s.md hs)
      | some (.ret rv, σ₁, h₁) =>
        simp [hs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .cons_return (denoteStmt_sound n s.md hs)
      | none => simp [hs] at heval
    | s :: s₂ :: rest =>
      simp only [denoteBlock] at heval
      match hs : denoteStmt δ π n h σ s.val with
      | some (.normal v, σ₁, h₁) =>
        simp [hs] at heval
        exact .cons_normal (denoteStmt_sound n s.md hs) (List.cons_ne_nil _ _)
          (denoteBlock_sound n heval)
      | some (.exit label, σ₁, h₁) =>
        simp [hs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .cons_exit (denoteStmt_sound n s.md hs)
      | some (.ret rv, σ₁, h₁) =>
        simp [hs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
        exact .cons_return (denoteStmt_sound n s.md hs)
      | none => simp [hs] at heval

theorem denoteArgs_sound
    {δ : LaurelEval} {π : ProcEnv} (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {as : List StmtExprMd}
    {vs : List LaurelValue} {σ' : LaurelStore} {h' : LaurelHeap}
    (heval : denoteArgs δ π fuel h σ as = some (vs, σ', h')) :
    EvalStmtArgs δ π h σ as h' σ' vs := by
  match fuel with
  | 0 => simp [denoteArgs] at heval
  | n + 1 =>
    match as with
    | [] => simp [denoteArgs] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval; exact .nil
    | e :: es =>
      simp only [denoteArgs] at heval
      match he : denoteStmt δ π n h σ e.val with
      | some (.normal v, σ₁, h₁) =>
        simp [he] at heval
        match hes : denoteArgs δ π n h₁ σ₁ es with
        | some (vs', σ₂, h₂) =>
          simp [hes] at heval; obtain ⟨rfl, rfl, rfl⟩ := heval
          exact .cons (denoteStmt_sound n e.md he) (denoteArgs_sound n hes)
        | none => simp [hes] at heval
      | some (.exit _, _, _) | some (.ret _, _, _) | none => simp [he] at heval
end

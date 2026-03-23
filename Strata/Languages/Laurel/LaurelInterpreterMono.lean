/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter

/-!
# Fuel Monotonicity for the Laurel Interpreter

If the interpreter succeeds with fuel `fuel₁`, it succeeds with any
`fuel₂ ≥ fuel₁` giving the same result.
-/

namespace Strata.Laurel

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
mutual
theorem interpStmt_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {heap : LaurelHeap} {store : LaurelStore} {s : StmtExpr}
    {r : Outcome × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : interpStmt δ π fuel₁ heap store s = some r) :
    interpStmt δ π fuel₂ heap store s = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [interpStmt] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    -- Both sides reduce to `match s with ...` using fuel n (resp. m) for sub-calls
    unfold interpStmt at heval ⊢
    cases s with
    | LiteralInt => exact heval
    | LiteralBool => exact heval
    | LiteralString => exact heval
    | LiteralDecimal => exact heval
    | Identifier name => exact heval
    -- TODO: The AndThen/OrElse/Implies cases below share nearly identical structure
    -- (~43 lines each). Consider extracting a shared tactic or private lemma that
    -- handles the common pattern: case-split on first arg result, apply IH on the
    -- recursive branch, discharge impossible cases. This would reduce ~130 lines to ~50.
    | PrimitiveOp op args =>
      cases op with
      | AndThen =>
        cases args with
        | cons a tail =>
          cases tail with
          | cons b tail₂ =>
            cases tail₂ with
            | nil =>
              match ha : interpStmt δ π n heap store a.val with
              | some (.normal (.vBool true), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]
                exact interpStmt_fuel_mono hle' heval
              | some (.normal (.vBool false), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]; exact heval
              | some (.normal (.vInt _), _, _) => simp [ha] at heval
              | some (.normal (.vString _), _, _) => simp [ha] at heval
              | some (.normal .vVoid, _, _) => simp [ha] at heval
              | some (.normal (.vRef _), _, _) => simp [ha] at heval
              | some (.exit _, _, _) => simp [ha] at heval
              | some (.ret _, _, _) => simp [ha] at heval
              | none => simp [ha] at heval
            | cons c rest =>
              match hargs : interpArgs δ π n heap store (a :: b :: c :: rest) with
              | some (vals, store', h') =>
                have := interpArgs_fuel_mono hle' hargs
                simp [hargs] at heval; simp [this]; exact heval
              | none => simp [hargs] at heval
          | nil =>
            match hargs : interpArgs δ π n heap store [a] with
            | some (vals, store', h') =>
              have := interpArgs_fuel_mono hle' hargs
              simp [hargs] at heval; simp [this]; exact heval
            | none => simp [hargs] at heval
        | nil =>
          match hargs : interpArgs δ π n heap store ([] : List StmtExprMd) with
          | some (vals, store', h') =>
            have := interpArgs_fuel_mono hle' hargs
            simp [hargs] at heval; simp [this]; exact heval
          | none => simp [hargs] at heval
      | OrElse =>
        cases args with
        | cons a tail =>
          cases tail with
          | cons b tail₂ =>
            cases tail₂ with
            | nil =>
              match ha : interpStmt δ π n heap store a.val with
              | some (.normal (.vBool true), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]; exact heval
              | some (.normal (.vBool false), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]
                exact interpStmt_fuel_mono hle' heval
              | some (.normal (.vInt _), _, _) => simp [ha] at heval
              | some (.normal (.vString _), _, _) => simp [ha] at heval
              | some (.normal .vVoid, _, _) => simp [ha] at heval
              | some (.normal (.vRef _), _, _) => simp [ha] at heval
              | some (.exit _, _, _) => simp [ha] at heval
              | some (.ret _, _, _) => simp [ha] at heval
              | none => simp [ha] at heval
            | cons c rest =>
              match hargs : interpArgs δ π n heap store (a :: b :: c :: rest) with
              | some (vals, store', h') =>
                have := interpArgs_fuel_mono hle' hargs
                simp [hargs] at heval; simp [this]; exact heval
              | none => simp [hargs] at heval
          | nil =>
            match hargs : interpArgs δ π n heap store [a] with
            | some (vals, store', h') =>
              have := interpArgs_fuel_mono hle' hargs
              simp [hargs] at heval; simp [this]; exact heval
            | none => simp [hargs] at heval
        | nil =>
          match hargs : interpArgs δ π n heap store ([] : List StmtExprMd) with
          | some (vals, store', h') =>
            have := interpArgs_fuel_mono hle' hargs
            simp [hargs] at heval; simp [this]; exact heval
          | none => simp [hargs] at heval
      | Implies =>
        cases args with
        | cons a tail =>
          cases tail with
          | cons b tail₂ =>
            cases tail₂ with
            | nil =>
              match ha : interpStmt δ π n heap store a.val with
              | some (.normal (.vBool false), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]; exact heval
              | some (.normal (.vBool true), σ₁, h₁) =>
                have := interpStmt_fuel_mono hle' ha
                simp [ha] at heval; simp [this]
                exact interpStmt_fuel_mono hle' heval
              | some (.normal (.vInt _), _, _) => simp [ha] at heval
              | some (.normal (.vString _), _, _) => simp [ha] at heval
              | some (.normal .vVoid, _, _) => simp [ha] at heval
              | some (.normal (.vRef _), _, _) => simp [ha] at heval
              | some (.exit _, _, _) => simp [ha] at heval
              | some (.ret _, _, _) => simp [ha] at heval
              | none => simp [ha] at heval
            | cons c rest =>
              match hargs : interpArgs δ π n heap store (a :: b :: c :: rest) with
              | some (vals, store', h') =>
                have := interpArgs_fuel_mono hle' hargs
                simp [hargs] at heval; simp [this]; exact heval
              | none => simp [hargs] at heval
          | nil =>
            match hargs : interpArgs δ π n heap store [a] with
            | some (vals, store', h') =>
              have := interpArgs_fuel_mono hle' hargs
              simp [hargs] at heval; simp [this]; exact heval
            | none => simp [hargs] at heval
        | nil =>
          match hargs : interpArgs δ π n heap store ([] : List StmtExprMd) with
          | some (vals, store', h') =>
            have := interpArgs_fuel_mono hle' hargs
            simp [hargs] at heval; simp [this]; exact heval
          | none => simp [hargs] at heval
      | _ =>
        match hargs : interpArgs δ π n heap store args with
        | some (vals, store', h') =>
          have := interpArgs_fuel_mono hle' hargs
          simp [hargs] at heval; simp [this]; exact heval
        | none => simp [hargs] at heval
    | IfThenElse c thenBr elseBr =>
      cases elseBr with
      | some elseBr =>
        match hc : interpStmt δ π n heap store c.val with
        | some (.normal (.vBool true), σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact interpStmt_fuel_mono hle' heval
        | some (.normal (.vBool false), σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact interpStmt_fuel_mono hle' heval
        | some (.normal (.vInt _), _, _) => simp [hc] at heval
        | some (.normal (.vString _), _, _) => simp [hc] at heval
        | some (.normal .vVoid, _, _) => simp [hc] at heval
        | some (.normal (.vRef _), _, _) => simp [hc] at heval
        | some (.exit _, _, _) => simp [hc] at heval
        | some (.ret _, _, _) => simp [hc] at heval
        | none => simp [hc] at heval
      | none =>
        match hc : interpStmt δ π n heap store c.val with
        | some (.normal (.vBool true), σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact interpStmt_fuel_mono hle' heval
        | some (.normal (.vBool false), σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]; exact heval
        | some (.normal (.vInt _), _, _) => simp [hc] at heval
        | some (.normal (.vString _), _, _) => simp [hc] at heval
        | some (.normal .vVoid, _, _) => simp [hc] at heval
        | some (.normal (.vRef _), _, _) => simp [hc] at heval
        | some (.exit _, _, _) => simp [hc] at heval
        | some (.ret _, _, _) => simp [hc] at heval
        | none => simp [hc] at heval
    | Block stmts label =>
      match hb : interpBlock δ π n heap store stmts with
      | some (outcome, store', h') =>
        have := interpBlock_fuel_mono hle' hb
        simp [hb] at heval; simp [this]; exact heval
      | none => simp [hb] at heval
    | Exit => exact heval
    | Return val =>
      cases val with
      | some val =>
        match hv : interpStmt δ π n heap store val.val with
        | some (.normal v, store', h') =>
          have := interpStmt_fuel_mono hle' hv
          simp [hv] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hv] at heval
        | some (.ret _, _, _) => simp [hv] at heval
        | none => simp [hv] at heval
      | none => exact heval
    | While c invs dec body =>
      match hc : interpStmt δ π n heap store c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        have hcm := interpStmt_fuel_mono hle' hc
        simp [hc] at heval; simp [hcm]
        match hbody : interpStmt δ π n h₁ σ₁ body.val with
        | some (.normal v, σ₂, h₂) =>
          have := interpStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]
          exact interpStmt_fuel_mono hle' heval
        | some (.exit label, σ₂, h₂) =>
          have := interpStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]; exact heval
        | some (.ret rv, σ₂, h₂) =>
          have := interpStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]; exact heval
        | none => simp [hbody] at heval
      | some (.normal (.vBool false), σ₁, h₁) =>
        have := interpStmt_fuel_mono hle' hc
        simp [hc] at heval; simp [this]; exact heval
      | some (.normal (.vInt _), _, _) => simp [hc] at heval
      | some (.normal (.vString _), _, _) => simp [hc] at heval
      | some (.normal .vVoid, _, _) => simp [hc] at heval
      | some (.normal (.vRef _), _, _) => simp [hc] at heval
      | some (.exit _, _, _) => simp [hc] at heval
      | some (.ret _, _, _) => simp [hc] at heval
      | none => simp [hc] at heval
    | Assign targets value =>
      match targets with
      | [⟨.Identifier name, _⟩] =>
        match hv : interpStmt δ π n heap store value.val with
        | some (.normal v, σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hv
          simp [hv] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hv] at heval
        | some (.ret _, _, _) => simp [hv] at heval
        | none => simp [hv] at heval
      | [⟨.FieldSelect target fieldName, _⟩] =>
        match ht : interpStmt δ π n heap store target.val with
        | some (.normal (.vRef addr), σ₁, h₁) =>
          have htm := interpStmt_fuel_mono hle' ht
          simp [ht] at heval; simp [htm]
          match hv : interpStmt δ π n h₁ σ₁ value.val with
          | some (.normal v, σ₂, h₂) =>
            have := interpStmt_fuel_mono hle' hv
            simp [hv] at heval; simp [this]; exact heval
          | some (.exit _, _, _) => simp [hv] at heval
          | some (.ret _, _, _) => simp [hv] at heval
          | none => simp [hv] at heval
        | some (.normal (.vInt _), _, _) => simp [ht] at heval
        | some (.normal (.vBool _), _, _) => simp [ht] at heval
        | some (.normal (.vString _), _, _) => simp [ht] at heval
        | some (.normal .vVoid, _, _) => simp [ht] at heval
        | some (.exit _, _, _) => simp [ht] at heval
        | some (.ret _, _, _) => simp [ht] at heval
        | none => simp [ht] at heval
      | [] => simp at heval
      | [⟨.LiteralInt _, _⟩] => simp at heval
      | [⟨.LiteralBool _, _⟩] => simp at heval
      | [⟨.LiteralString _, _⟩] => simp at heval
      | [⟨.PrimitiveOp _ _, _⟩] => simp at heval
      | [⟨.IfThenElse _ _ _, _⟩] => simp at heval
      | [⟨.Block _ _, _⟩] => simp at heval
      | [⟨.Exit _, _⟩] => simp at heval
      | [⟨.Return _, _⟩] => simp at heval
      | [⟨.While _ _ _ _, _⟩] => simp at heval
      | [⟨.Assign _ _, _⟩] => simp at heval
      | [⟨.LocalVariable _ _ _, _⟩] => simp at heval
      | [⟨.Assert _, _⟩] => simp at heval
      | [⟨.Assume _, _⟩] => simp at heval
      | [⟨.StaticCall _ _, _⟩] => simp at heval
      | [⟨.New _, _⟩] => simp at heval
      | [⟨.PureFieldUpdate _ _ _, _⟩] => simp at heval
      | [⟨.ReferenceEquals _ _, _⟩] => simp at heval
      | [⟨.InstanceCall _ _ _, _⟩] => simp at heval
      | [⟨.This, _⟩] => simp at heval
      | [⟨.IsType _ _, _⟩] => simp at heval
      | [⟨.AsType _ _, _⟩] => simp at heval
      | [⟨.Forall _ _ _, _⟩] => simp at heval
      | [⟨.Exists _ _ _, _⟩] => simp at heval
      | [⟨.Old _, _⟩] => simp at heval
      | [⟨.Fresh _, _⟩] => simp at heval
      | [⟨.Assigned _, _⟩] => simp at heval
      | [⟨.ProveBy _ _, _⟩] => simp at heval
      | [⟨.ContractOf _ _, _⟩] => simp at heval
      | [⟨.Abstract, _⟩] => simp at heval
      | [⟨.All, _⟩] => simp at heval
      | [⟨.Hole, _⟩] => simp at heval
      | _ :: _ :: _ => simp at heval
    | LocalVariable name ty init =>
      cases init with
      | some init =>
        match hi : interpStmt δ π n heap store init.val with
        | some (.normal v, σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hi
          simp [hi] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hi] at heval
        | some (.ret _, _, _) => simp [hi] at heval
        | none => simp [hi] at heval
      | none => exact heval
    | Assert c =>
      match hc : interpStmt δ π n heap store c.val with
      | some (.normal (.vBool true), _, _) =>
        have := interpStmt_fuel_mono hle' hc
        simp [hc] at heval; simp [this]; exact heval
      | some (.normal (.vBool false), _, _) => simp [hc] at heval
      | some (.normal (.vInt _), _, _) => simp [hc] at heval
      | some (.normal (.vString _), _, _) => simp [hc] at heval
      | some (.normal .vVoid, _, _) => simp [hc] at heval
      | some (.normal (.vRef _), _, _) => simp [hc] at heval
      | some (.exit _, _, _) => simp [hc] at heval
      | some (.ret _, _, _) => simp [hc] at heval
      | none => simp [hc] at heval
    | Assume c =>
      match hc : interpStmt δ π n heap store c.val with
      | some (.normal (.vBool true), _, _) =>
        have := interpStmt_fuel_mono hle' hc
        simp [hc] at heval; simp [this]; exact heval
      | some (.normal (.vBool false), _, _) => simp [hc] at heval
      | some (.normal (.vInt _), _, _) => simp [hc] at heval
      | some (.normal (.vString _), _, _) => simp [hc] at heval
      | some (.normal .vVoid, _, _) => simp [hc] at heval
      | some (.normal (.vRef _), _, _) => simp [hc] at heval
      | some (.exit _, _, _) => simp [hc] at heval
      | some (.ret _, _, _) => simp [hc] at heval
      | none => simp [hc] at heval
    | StaticCall callee args =>
      match hp : π callee with
      | some proc =>
        simp [hp] at heval ⊢
        match hargs : interpArgs δ π n heap store args with
        | some (vals, σ₁, h₁) =>
          have hargm := interpArgs_fuel_mono hle' hargs
          simp [hargs] at heval; simp [hargm]
          match hbind : bindParams proc.inputs vals with
          | some σBound =>
            simp [hbind] at heval ⊢
            match hbody : getBody proc with
            | some body =>
              simp [hbody] at heval ⊢
              match hcall : interpStmt δ π n h₁ σBound body.val with
              | some (.normal v, _, h') =>
                have := interpStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.ret (some v), _, h') =>
                have := interpStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.ret none, _, h') =>
                have := interpStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.exit _, _, _) => simp [hcall] at heval
              | none => simp [hcall] at heval
            | none => simp [hbody] at heval
          | none => simp [hbind] at heval
        | none => simp [hargs] at heval
      | none => simp [hp] at heval
    | New => exact heval
    | FieldSelect target fieldName =>
      match ht : interpStmt δ π n heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have := interpStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [this]; exact heval
      | some (.normal (.vInt _), _, _) => simp [ht] at heval
      | some (.normal (.vBool _), _, _) => simp [ht] at heval
      | some (.normal (.vString _), _, _) => simp [ht] at heval
      | some (.normal .vVoid, _, _) => simp [ht] at heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | PureFieldUpdate target fieldName newVal =>
      match ht : interpStmt δ π n heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have htm := interpStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [htm]
        match hv : interpStmt δ π n h₁ σ₁ newVal.val with
        | some (.normal v, σ₂, h₂) =>
          have := interpStmt_fuel_mono hle' hv
          simp [hv] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hv] at heval
        | some (.ret _, _, _) => simp [hv] at heval
        | none => simp [hv] at heval
      | some (.normal (.vInt _), _, _) => simp [ht] at heval
      | some (.normal (.vBool _), _, _) => simp [ht] at heval
      | some (.normal (.vString _), _, _) => simp [ht] at heval
      | some (.normal .vVoid, _, _) => simp [ht] at heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | ReferenceEquals lhs rhs =>
      match hl : interpStmt δ π n heap store lhs.val with
      | some (.normal (.vRef a), σ₁, h₁) =>
        have hlm := interpStmt_fuel_mono hle' hl
        simp [hl] at heval; simp [hlm]
        match hr : interpStmt δ π n h₁ σ₁ rhs.val with
        | some (.normal (.vRef b), σ₂, h₂) =>
          have := interpStmt_fuel_mono hle' hr
          simp [hr] at heval; simp [this]; exact heval
        | some (.normal (.vInt _), _, _) => simp [hr] at heval
        | some (.normal (.vBool _), _, _) => simp [hr] at heval
        | some (.normal (.vString _), _, _) => simp [hr] at heval
        | some (.normal .vVoid, _, _) => simp [hr] at heval
        | some (.exit _, _, _) => simp [hr] at heval
        | some (.ret _, _, _) => simp [hr] at heval
        | none => simp [hr] at heval
      | some (.normal (.vInt _), _, _) => simp [hl] at heval
      | some (.normal (.vBool _), _, _) => simp [hl] at heval
      | some (.normal (.vString _), _, _) => simp [hl] at heval
      | some (.normal .vVoid, _, _) => simp [hl] at heval
      | some (.exit _, _, _) => simp [hl] at heval
      | some (.ret _, _, _) => simp [hl] at heval
      | none => simp [hl] at heval
    | InstanceCall target callee args =>
      match ht : interpStmt δ π n heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have htm := interpStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [htm]
        match hlook : h₁ addr with
        | some (typeName, _) =>
          simp [hlook] at heval ⊢
          match hproc : π (↑(typeName ++ "." ++ callee.text)) with
          | some proc =>
            simp [hproc] at heval ⊢
            match hargs : interpArgs δ π n h₁ σ₁ args with
            | some (vals, σ₂, h₂) =>
              have hargm := interpArgs_fuel_mono hle' hargs
              simp [hargs] at heval; simp [hargm]
              match hbind : bindParams proc.inputs (LaurelValue.vRef addr :: vals) with
              | some σBound =>
                simp [hbind] at heval ⊢
                match hbody : getBody proc with
                | some body =>
                  simp [hbody] at heval ⊢
                  match hcall : interpStmt δ π n h₂ σBound body.val with
                  | some (.normal v, _, h₃) =>
                    have := interpStmt_fuel_mono hle' hcall
                    simp [hcall] at heval; simp [this]; exact heval
                  | some (.ret (some v), _, h₃) =>
                    have := interpStmt_fuel_mono hle' hcall
                    simp [hcall] at heval; simp [this]; exact heval
                  | some (.ret none, _, h₃) =>
                    have := interpStmt_fuel_mono hle' hcall
                    simp [hcall] at heval; simp [this]; exact heval
                  | some (.exit _, _, _) => simp [hcall] at heval
                  | none => simp [hcall] at heval
                | none => simp [hbody] at heval
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
    | This => exact heval
    | IsType target ty =>
      match ht : interpStmt δ π n heap store target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have := interpStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [this]; exact heval
      | some (.normal (.vInt _), _, _) => simp [ht] at heval
      | some (.normal (.vBool _), _, _) => simp [ht] at heval
      | some (.normal (.vString _), _, _) => simp [ht] at heval
      | some (.normal .vVoid, _, _) => simp [ht] at heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | AsType target ty =>
      match ht : interpStmt δ π n heap store target.val with
      | some (.normal v, σ₁, h₁) =>
        have := interpStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [this]; exact heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | Forall _ _ _ => exact heval
    | Exists _ _ _ => exact heval
    | Old _ => exact heval
    | Fresh _ => exact heval
    | Assigned _ => exact heval
    | ProveBy value proof =>
      exact interpStmt_fuel_mono hle' heval
    | ContractOf _ _ => exact heval
    | Abstract => simp at heval
    | All => simp at heval
    | Hole => simp at heval

theorem interpBlock_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {heap : LaurelHeap} {store : LaurelStore} {ss : List StmtExprMd}
    {r : Outcome × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : interpBlock δ π fuel₁ heap store ss = some r) :
    interpBlock δ π fuel₂ heap store ss = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [interpBlock] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    unfold interpBlock at heval ⊢
    cases ss with
    | nil => exact heval
    | cons s rest =>
      cases rest with
      | nil => exact interpStmt_fuel_mono hle' heval
      | cons s' rest' =>
        match hs : interpStmt δ π n heap store s.val with
        | some (.normal _, σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]
          exact interpBlock_fuel_mono hle' heval
        | some (.exit label, σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]; exact heval
        | some (.ret rv, σ₁, h₁) =>
          have := interpStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]; exact heval
        | none => simp [hs] at heval

theorem interpArgs_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {heap : LaurelHeap} {store : LaurelStore} {as : List StmtExprMd}
    {r : List LaurelValue × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : interpArgs δ π fuel₁ heap store as = some r) :
    interpArgs δ π fuel₂ heap store as = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [interpArgs] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    unfold interpArgs at heval ⊢
    cases as with
    | nil => exact heval
    | cons e es =>
      match he : interpStmt δ π n heap store e.val with
      | some (.normal v, σ₁, h₁) =>
        have hem := interpStmt_fuel_mono hle' he
        simp [he] at heval; simp [hem]
        match hes : interpArgs δ π n h₁ σ₁ es with
        | some (vs, σ₂, h₂) =>
          have := interpArgs_fuel_mono hle' hes
          simp [hes] at heval; simp [this]; exact heval
        | none => simp [hes] at heval
      | some (.exit _, _, _) => simp [he] at heval
      | some (.ret _, _, _) => simp [he] at heval
      | none => simp [he] at heval
end

end Strata.Laurel

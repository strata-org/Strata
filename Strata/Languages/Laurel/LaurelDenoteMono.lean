/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelDenote

/-!
# Fuel Monotonicity for the Denotational Interpreter

If the interpreter succeeds with fuel `fuel₁`, it succeeds with any
`fuel₂ ≥ fuel₁` giving the same result.
-/

namespace Strata.Laurel

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
mutual
theorem denoteStmt_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {h : LaurelHeap} {σ : LaurelStore} {s : StmtExpr}
    {r : Outcome × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : denoteStmt δ π fuel₁ h σ s = some r) :
    denoteStmt δ π fuel₂ h σ s = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [denoteStmt] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    -- Both sides reduce to `match s with ...` using fuel n (resp. m) for sub-calls
    unfold denoteStmt at heval ⊢
    cases s with
    | LiteralInt => exact heval
    | LiteralBool => exact heval
    | LiteralString => exact heval
    | LiteralDecimal => exact heval
    | Identifier name => exact heval
    | PrimitiveOp op args =>
      match hargs : denoteArgs δ π n h σ args with
      | some (vals, σ', h') =>
        have := denoteArgs_fuel_mono hle' hargs
        simp [hargs] at heval; simp [this]; exact heval
      | none => simp [hargs] at heval
    | IfThenElse c thenBr elseBr =>
      cases elseBr with
      | some elseBr =>
        match hc : denoteStmt δ π n h σ c.val with
        | some (.normal (.vBool true), σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact denoteStmt_fuel_mono hle' heval
        | some (.normal (.vBool false), σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact denoteStmt_fuel_mono hle' heval
        | some (.normal (.vInt _), _, _) => simp [hc] at heval
        | some (.normal (.vString _), _, _) => simp [hc] at heval
        | some (.normal .vVoid, _, _) => simp [hc] at heval
        | some (.normal (.vRef _), _, _) => simp [hc] at heval
        | some (.exit _, _, _) => simp [hc] at heval
        | some (.ret _, _, _) => simp [hc] at heval
        | none => simp [hc] at heval
      | none =>
        match hc : denoteStmt δ π n h σ c.val with
        | some (.normal (.vBool true), σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]
          exact denoteStmt_fuel_mono hle' heval
        | some (.normal (.vBool false), σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hc
          simp [hc] at heval; simp [this]; exact heval
        | some (.normal (.vInt _), _, _) => simp [hc] at heval
        | some (.normal (.vString _), _, _) => simp [hc] at heval
        | some (.normal .vVoid, _, _) => simp [hc] at heval
        | some (.normal (.vRef _), _, _) => simp [hc] at heval
        | some (.exit _, _, _) => simp [hc] at heval
        | some (.ret _, _, _) => simp [hc] at heval
        | none => simp [hc] at heval
    | Block stmts label =>
      match hb : denoteBlock δ π n h σ stmts with
      | some (outcome, σ', h') =>
        have := denoteBlock_fuel_mono hle' hb
        simp [hb] at heval; simp [this]; exact heval
      | none => simp [hb] at heval
    | Exit => exact heval
    | Return val =>
      cases val with
      | some val =>
        match hv : denoteStmt δ π n h σ val.val with
        | some (.normal v, σ', h') =>
          have := denoteStmt_fuel_mono hle' hv
          simp [hv] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hv] at heval
        | some (.ret _, _, _) => simp [hv] at heval
        | none => simp [hv] at heval
      | none => exact heval
    | While c invs dec body =>
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), σ₁, h₁) =>
        have hcm := denoteStmt_fuel_mono hle' hc
        simp [hc] at heval; simp [hcm]
        match hbody : denoteStmt δ π n h₁ σ₁ body.val with
        | some (.normal v, σ₂, h₂) =>
          have := denoteStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]
          exact denoteStmt_fuel_mono hle' heval
        | some (.exit label, σ₂, h₂) =>
          have := denoteStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]; exact heval
        | some (.ret rv, σ₂, h₂) =>
          have := denoteStmt_fuel_mono hle' hbody
          simp [hbody] at heval; simp [this]; exact heval
        | none => simp [hbody] at heval
      | some (.normal (.vBool false), σ₁, h₁) =>
        have := denoteStmt_fuel_mono hle' hc
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
        match hv : denoteStmt δ π n h σ value.val with
        | some (.normal v, σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hv
          simp [hv] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hv] at heval
        | some (.ret _, _, _) => simp [hv] at heval
        | none => simp [hv] at heval
      | [⟨.FieldSelect target fieldName, _⟩] =>
        match ht : denoteStmt δ π n h σ target.val with
        | some (.normal (.vRef addr), σ₁, h₁) =>
          have htm := denoteStmt_fuel_mono hle' ht
          simp [ht] at heval; simp [htm]
          match hv : denoteStmt δ π n h₁ σ₁ value.val with
          | some (.normal v, σ₂, h₂) =>
            have := denoteStmt_fuel_mono hle' hv
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
        match hi : denoteStmt δ π n h σ init.val with
        | some (.normal v, σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hi
          simp [hi] at heval; simp [this]; exact heval
        | some (.exit _, _, _) => simp [hi] at heval
        | some (.ret _, _, _) => simp [hi] at heval
        | none => simp [hi] at heval
      | none => exact heval
    | Assert c =>
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), _, _) =>
        have := denoteStmt_fuel_mono hle' hc
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
      match hc : denoteStmt δ π n h σ c.val with
      | some (.normal (.vBool true), _, _) =>
        have := denoteStmt_fuel_mono hle' hc
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
        match hargs : denoteArgs δ π n h σ args with
        | some (vals, σ₁, h₁) =>
          have hargm := denoteArgs_fuel_mono hle' hargs
          simp [hargs] at heval; simp [hargm]
          match hbind : bindParams proc.inputs vals with
          | some σBound =>
            simp [hbind] at heval ⊢
            match hbody : getBody proc with
            | some body =>
              simp [hbody] at heval ⊢
              match hcall : denoteStmt δ π n h₁ σBound body.val with
              | some (.normal v, _, h') =>
                have := denoteStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.ret (some v), _, h') =>
                have := denoteStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.ret none, _, h') =>
                have := denoteStmt_fuel_mono hle' hcall
                simp [hcall] at heval; simp [this]; exact heval
              | some (.exit _, _, _) => simp [hcall] at heval
              | none => simp [hcall] at heval
            | none => simp [hbody] at heval
          | none => simp [hbind] at heval
        | none => simp [hargs] at heval
      | none => simp [hp] at heval
    | New => exact heval
    | FieldSelect target fieldName =>
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have := denoteStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [this]; exact heval
      | some (.normal (.vInt _), _, _) => simp [ht] at heval
      | some (.normal (.vBool _), _, _) => simp [ht] at heval
      | some (.normal (.vString _), _, _) => simp [ht] at heval
      | some (.normal .vVoid, _, _) => simp [ht] at heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | PureFieldUpdate target fieldName newVal =>
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have htm := denoteStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [htm]
        match hv : denoteStmt δ π n h₁ σ₁ newVal.val with
        | some (.normal v, σ₂, h₂) =>
          have := denoteStmt_fuel_mono hle' hv
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
      match hl : denoteStmt δ π n h σ lhs.val with
      | some (.normal (.vRef a), σ₁, h₁) =>
        have hlm := denoteStmt_fuel_mono hle' hl
        simp [hl] at heval; simp [hlm]
        match hr : denoteStmt δ π n h₁ σ₁ rhs.val with
        | some (.normal (.vRef b), σ₂, h₂) =>
          have := denoteStmt_fuel_mono hle' hr
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
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have htm := denoteStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [htm]
        match hlook : h₁ addr with
        | some (typeName, _) =>
          simp [hlook] at heval ⊢
          match hproc : π (↑(typeName ++ "." ++ callee.text)) with
          | some proc =>
            simp [hproc] at heval ⊢
            match hargs : denoteArgs δ π n h₁ σ₁ args with
            | some (vals, σ₂, h₂) =>
              have hargm := denoteArgs_fuel_mono hle' hargs
              simp [hargs] at heval; simp [hargm]
              match hbind : bindParams proc.inputs (LaurelValue.vRef addr :: vals) with
              | some σBound =>
                simp [hbind] at heval ⊢
                match hbody : getBody proc with
                | some body =>
                  simp [hbody] at heval ⊢
                  match hcall : denoteStmt δ π n h₂ σBound body.val with
                  | some (.normal v, _, h₃) =>
                    have := denoteStmt_fuel_mono hle' hcall
                    simp [hcall] at heval; simp [this]; exact heval
                  | some (.ret (some v), _, h₃) =>
                    have := denoteStmt_fuel_mono hle' hcall
                    simp [hcall] at heval; simp [this]; exact heval
                  | some (.ret none, _, h₃) =>
                    have := denoteStmt_fuel_mono hle' hcall
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
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal (.vRef addr), σ₁, h₁) =>
        have := denoteStmt_fuel_mono hle' ht
        simp [ht] at heval; simp [this]; exact heval
      | some (.normal (.vInt _), _, _) => simp [ht] at heval
      | some (.normal (.vBool _), _, _) => simp [ht] at heval
      | some (.normal (.vString _), _, _) => simp [ht] at heval
      | some (.normal .vVoid, _, _) => simp [ht] at heval
      | some (.exit _, _, _) => simp [ht] at heval
      | some (.ret _, _, _) => simp [ht] at heval
      | none => simp [ht] at heval
    | AsType target ty =>
      match ht : denoteStmt δ π n h σ target.val with
      | some (.normal v, σ₁, h₁) =>
        have := denoteStmt_fuel_mono hle' ht
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
      exact denoteStmt_fuel_mono hle' heval
    | ContractOf _ _ => exact heval
    | Abstract => simp at heval
    | All => simp at heval
    | Hole => simp at heval

theorem denoteBlock_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {h : LaurelHeap} {σ : LaurelStore} {ss : List StmtExprMd}
    {r : Outcome × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : denoteBlock δ π fuel₁ h σ ss = some r) :
    denoteBlock δ π fuel₂ h σ ss = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [denoteBlock] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    unfold denoteBlock at heval ⊢
    cases ss with
    | nil => exact heval
    | cons s rest =>
      cases rest with
      | nil => exact denoteStmt_fuel_mono hle' heval
      | cons s' rest' =>
        match hs : denoteStmt δ π n h σ s.val with
        | some (.normal _, σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]
          exact denoteBlock_fuel_mono hle' heval
        | some (.exit label, σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]; exact heval
        | some (.ret rv, σ₁, h₁) =>
          have := denoteStmt_fuel_mono hle' hs
          simp [hs] at heval; simp [this]; exact heval
        | none => simp [hs] at heval

theorem denoteArgs_fuel_mono
    {δ : LaurelEval} {π : ProcEnv} {fuel₁ fuel₂ : Nat}
    {h : LaurelHeap} {σ : LaurelStore} {as : List StmtExprMd}
    {r : List LaurelValue × LaurelStore × LaurelHeap}
    (hle : fuel₁ ≤ fuel₂)
    (heval : denoteArgs δ π fuel₁ h σ as = some r) :
    denoteArgs δ π fuel₂ h σ as = some r := by
  match fuel₁, fuel₂ with
  | 0, _ => simp [denoteArgs] at heval
  | _ + 1, 0 => omega
  | n + 1, m + 1 =>
    have hle' : n ≤ m := by omega
    unfold denoteArgs at heval ⊢
    cases as with
    | nil => exact heval
    | cons e es =>
      match he : denoteStmt δ π n h σ e.val with
      | some (.normal v, σ₁, h₁) =>
        have hem := denoteStmt_fuel_mono hle' he
        simp [he] at heval; simp [hem]
        match hes : denoteArgs δ π n h₁ σ₁ es with
        | some (vs, σ₂, h₂) =>
          have := denoteArgs_fuel_mono hle' hes
          simp [hes] at heval; simp [this]; exact heval
        | none => simp [hes] at heval
      | some (.exit _, _, _) => simp [he] at heval
      | some (.ret _, _, _) => simp [he] at heval
      | none => simp [he] at heval
end

end Strata.Laurel

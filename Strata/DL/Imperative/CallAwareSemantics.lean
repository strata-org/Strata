/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.KleeneStmtSemantics
public import Strata.DL.Imperative.StmtCFGCallSemantics

/-! # Call-aware event-trace CFG and Kleene relations

The generic event-trace relations `StepCFGE` / `StepCFGStarE` (CFGSemantics) and
`StepKleeneE` / `StepKleeneStarE` (KleeneStmtSemantics) instantiated at
`CmdT := CmdExt P`, `EventT := Event P` and the call-aware command relation
`EvalCmdExtE π` (StmtCFGCallSemantics).  A call inside a CFG block or a Kleene
command runs the callee body, structured or CFG, to completion through `BigStepE`.
The generic relations themselves stay call-agnostic. -/

namespace Imperative

public section

/-- One call-aware event-trace CFG step. The CFG and environment are carried
by the source and target configurations. -/
abbrev StepCFGExtE
    {l : Type} [BEq l]
    {P : PureExpr}
    [DecidableEq P.Ident] [HasOldIdent P]
    [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CFGConfig l (CmdExt P) P → List (Event P) → CFGConfig l (CmdExt P) P → Prop :=
  _root_.Imperative.StepCFGE P (EvalCmdExtE π)

/-- Reflexive-transitive call-aware event-trace CFG execution. -/
abbrev StepCFGExtStarE
    {l : Type} [BEq l]
    {P : PureExpr}
    [DecidableEq P.Ident] [HasOldIdent P]
    [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    CFGConfig l (CmdExt P) P → List (Event P) → CFGConfig l (CmdExt P) P → Prop :=
  _root_.Imperative.StepCFGStarE P (EvalCmdExtE π)

/-- One call-aware event-trace Kleene step: the generic `StepKleeneE` driven by
the call-aware command relation `EvalCmdExtE π`. -/
abbrev StepKleeneExtE
    {P : PureExpr}
    [DecidableEq P.Ident] [HasOldIdent P]
    [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    KleeneConfig P (CmdExt P) → List (Event P) → KleeneConfig P (CmdExt P) → Prop :=
  _root_.Imperative.StepKleeneE P (EvalCmdExtE π)

/-- The reflexive-transitive closure of `StepKleeneExtE`. -/
abbrev StepKleeneExtStarE
    {P : PureExpr}
    [DecidableEq P.Ident] [HasOldIdent P]
    [HasBool P] [HasBoolOps P] [HasFvar P] [HasFvars P]
    {Hdr : Type} [DecidableEq Hdr] [Inhabited Hdr] [ProcedureHeader P Hdr]
    (π : String → Option (Procedure P (CmdExt P) Hdr)) :
    KleeneConfig P (CmdExt P) → List (Event P) → KleeneConfig P (CmdExt P) → Prop :=
  _root_.Imperative.StepKleeneStarE P (EvalCmdExtE π)

end

end Imperative

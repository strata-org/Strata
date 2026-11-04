/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Procedure

/-! # Language interfaces for call semantics: `old` identifiers, formal classes and
    call input expressions -/

namespace Imperative

public section

/-- A language's `old`-state identifiers: `mkOld g` is the identifier under which a
    call snapshots the entry value of the inout formal `g`. -/
class HasOldIdent (P : PureExpr) where
  mkOld : P.Ident → P.Ident

namespace Calls

/-- The expressions passed at a call: each `inArg`, plus a variable reference
    (`HasFvar.mkFvar`) for every `inoutArg`. -/
@[expose] def getInputExprs {P : PureExpr} [HasFvar P] (args : List (CallArg P)) :
    List P.Expr :=
  args.filterMap fun
    | .inArg e => some e
    | .inoutArg id => some (HasFvar.mkFvar id)
    | .outArg _ => none

variable {P : PureExpr} [DecidableEq P.Ident] {Hdr : Type} [ProcedureHeader P Hdr]

/-- The inout formals of a header: its input formals that are also output formals,
    in input order.  These are the formals a call snapshots under `old`. -/
@[expose] def inoutParams (h : Hdr) : List P.Ident :=
  (ProcedureHeader.inputParams (P := P) h).filter fun x =>
    (ProcedureHeader.outputParams (P := P) h).contains x

/-- The output-only formals of a header: its output formals that are not input
    formals, in output order.  A call initializes them from the caller's `out`
    actuals. -/
@[expose] def outputOnlyParams (h : Hdr) : List P.Ident :=
  (ProcedureHeader.outputParams (P := P) h).filter fun x =>
    !(ProcedureHeader.inputParams (P := P) h).contains x

end Calls

/-! # Variable and operator analysis for extended commands

`CmdExt P` adds a procedure `call` on top of the base `Cmd P`. These generic
analyses, and the `HasVarsImp` / `HasOpsImp` instances they induce, let the
call-free bridge in `StmtExtendCallBridge(Props)` state for any `P` that
embedding a base command as `CmdExt.cmd` preserves every analysis. -/

section CmdExtVars

variable {P : PureExpr}

/-- Variables read by an extended command: those of the wrapped base command, or
the free variables of a call's input expressions. -/
@[expose] def CmdExt.readVars [HasFvar P] [HasFvars P] (c : CmdExt P) : List P.Ident :=
  match c with
  | .cmd c => Cmd.getVars c
  | .call _ args _ => (Calls.getInputExprs args).flatMap HasFvars.getFvars

/-- Operator/function names referenced by an extended command. -/
@[expose] def CmdExt.getOps [HasFvar P] [HasOps P] (c : CmdExt P) : List P.Ident :=
  match c with
  | .cmd c => Cmd.getOps c
  | .call _ args _ => (Calls.getInputExprs args).flatMap HasOps.getOps

/-- Variables defined (via `init`) by an extended command; a `call` defines
none. -/
@[expose] def CmdExt.definedVars (c : CmdExt P) : List P.Ident :=
  match c with
  | .cmd c => Cmd.definedVars c
  | _ => []

/-- Variables modified by an extended command: those of the wrapped base
command, or the output/inout targets of a `call`. -/
@[expose] def CmdExt.modifiedVars (c : CmdExt P) : List P.Ident :=
  match c with
  | .cmd c => Cmd.modifiedVars c
  | .call _ args _ => CallArg.getLhs args

/-- Variables modified or defined by an extended command (its write-set). -/
@[expose] def CmdExt.modifiedOrDefinedVars (c : CmdExt P) : List P.Ident :=
  CmdExt.definedVars c ++ CmdExt.modifiedVars c

instance (P : PureExpr) [HasFvar P] [HasFvars P] : HasVarsImp P (CmdExt P) where
  definedVars c _ := CmdExt.definedVars c
  modifiedVars := CmdExt.modifiedVars
  readVars := CmdExt.readVars

instance (P : PureExpr) [HasFvar P] [HasOps P] : HasOpsImp P (CmdExt P) where
  getOps := CmdExt.getOps

end CmdExtVars

end

end Imperative

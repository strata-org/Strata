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

end

end Imperative

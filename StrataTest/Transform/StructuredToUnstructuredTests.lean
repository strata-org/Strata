/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.StructuredToUnstructured
import Strata.DL.Lambda.Lambda

/-! ## Tests for loop contract metadata preservation in StructuredToUnstructured -/

section
open Std (ToFormat Format format)
open Lambda.LTy.Syntax
open Imperative (MetaData MetaDataElem)

private abbrev TP : Lambda.LExprParams := ⟨Unit, Unit⟩

private abbrev P : Imperative.PureExpr :=
   { Ident := TP.Identifier,
     Expr := Lambda.LExprT TP.mono,
     Ty := Lambda.LMonoTy,
     ExprMetadata := TP.Metadata,
     TyEnv := @Lambda.TEnv TP.IDMeta,
     TyContext := @Lambda.LContext TP,
     EvalEnv := Lambda.LState TP
     EqIdent := inferInstanceAs (DecidableEq TP.Identifier) }

private abbrev mdB : Lambda.Typed Unit := { underlying := (), type := mty[bool] }

instance : Imperative.HasBool P where
  tt := .const mdB (.boolConst true)
  ff := .const mdB (.boolConst false)
  tt_is_not_ff := by simp
  boolTy := mty[bool]

instance : Imperative.HasIdent P where
  ident s := ⟨s, ()⟩

instance : Imperative.HasFvar P where
  mkFvar := (.fvar mdB · none)
  getFvar | .fvar _ v _ => some v | _ => none

instance : Imperative.HasIntOrder P where
  eq e1 e2 := .eq mdB e1 e2
  lt e1 e2 := .app mdB (.app mdB (.op mdB ⟨"Int.Lt", ()⟩ none) e1) e2
  zero := .intConst mdB 0
  intTy := mty[int]

instance : Imperative.HasNot P where
  not e := .app mdB (.op mdB ⟨"Bool.Not", ()⟩ none) e

instance : Imperative.HasPassiveCmds P (Imperative.Cmd P) where
  assert l e md := .assert l e md
  assume l e md := .assume l e md

instance : Imperative.HasInit P (Imperative.Cmd P) where
  init i ty e md := .init i ty e md

private def mkFvar (name : String) : P.Expr := .fvar mdB ⟨name, ()⟩ none
private def trueExpr : P.Expr := .const mdB (.boolConst true)

private abbrev Stmt' := Imperative.Stmt P (Imperative.Cmd P)
private abbrev CFG' := Imperative.CFG String (Imperative.DetBlock String (Imperative.Cmd P) P)

private def toCFG (ss : List Stmt') : CFG' := Imperative.stmtsToCFG ss

private def findLoopEntry (cfg : CFG') :
    Option (Imperative.DetBlock String (Imperative.Cmd P) P) :=
  cfg.blocks.find? (fun (lbl, _) => lbl.startsWith "loop_entry$") |>.map (·.2)

private def getTransferMd (blk : Imperative.DetBlock String (Imperative.Cmd P) P) :
    MetaData P :=
  match blk.transfer with
  | .condGoto _ _ _ md => md
  | .finish md => md

private def countField (md : MetaData P) (fld : MetaDataElem.Field P) : Nat :=
  md.filter (fun e => e.fld == fld) |>.size

private def loopEntryMd (ss : List Stmt') : MetaData P :=
  match findLoopEntry (toCFG ss) with
  | some blk => getTransferMd blk
  | none => .empty

private def setCmd (name : String) : Imperative.Cmd P :=
  .set ⟨name, ()⟩ (.det (mkFvar name)) .empty

/-! ### Simple loop with one invariant: specLoopInvariant in transfer metadata -/

#guard countField (loopEntryMd [
    .loop (.det trueExpr) none [("inv0", mkFvar "x")] [.cmd (setCmd "x")] .empty
  ]) MetaData.specLoopInvariant == 1

/-! ### Loop with multiple invariants: one entry per invariant -/

#guard countField (loopEntryMd [
    .loop (.det trueExpr) none [("inv_a", mkFvar "a"), ("inv_b", mkFvar "b")]
      [.cmd (setCmd "x")] .empty
  ]) MetaData.specLoopInvariant == 2

/-! ### Loop with decreases measure: specDecreases in metadata -/

#guard countField (loopEntryMd [
    .loop (.det trueExpr) (some (mkFvar "n")) [("inv", mkFvar "x")]
      [.cmd (setCmd "x")] .empty
  ]) MetaData.specDecreases == 1

/-! ### Loop with both invariants and decreases -/

#guard
  let md := loopEntryMd [
    .loop (.det trueExpr) (some (mkFvar "n")) [("inv_a", mkFvar "a"), ("inv_b", mkFvar "b")]
      [.cmd (setCmd "x")] .empty
  ]
  countField md MetaData.specLoopInvariant == 2 &&
  countField md MetaData.specDecreases == 1

/-! ### Loop without contract: no spec metadata in transfer -/

#guard
  let md := loopEntryMd [
    .loop (.det trueExpr) none [] [.cmd (setCmd "x")] .empty
  ]
  countField md MetaData.specLoopInvariant == 0 &&
  countField md MetaData.specDecreases == 0

/-! ### Invariant assert commands still emitted (both behaviors coexist) -/

#guard
  let cfg := toCFG [
    .loop (.det trueExpr) none [("my_inv", mkFvar "x")]
      [.cmd (setCmd "x")] .empty
  ]
  match findLoopEntry cfg with
  | some blk => blk.cmds.any (fun cmd =>
      match cmd with
      | .assert label _ _ => label == "my_inv"
      | _ => false)
  | none => false

/-! ### Nondet loop guard: contract metadata still present -/

#guard
  let md := loopEntryMd [
    .loop .nondet (some (mkFvar "n")) [("inv", mkFvar "x")]
      [.cmd (setCmd "x")] .empty
  ]
  countField md MetaData.specLoopInvariant == 1 &&
  countField md MetaData.specDecreases == 1

end

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelToCoreTranslator
import Lean.Data.AssocList

namespace Strata.Laurel

open Strata.Laurel (TypeEnv)

def mkTy (t : HighType) : HighTypeMd := { val := t, md := default }

def lookupVar (env : TypeEnv) (name : Identifier) : Option HighTypeMd :=
  env.find? (·.1 == name) |>.map (·.2)

mutual

/-- Synthesize the type of an expression -/
partial def synth (env : TypeEnv) (expr : StmtExprMd) : Option HighTypeMd :=
  match expr.val with
  | .Identifier name => lookupVar env name
  | .PrimitiveOp op args =>
    match op, args with
    | .Add, [e1, e2] | .Sub, [e1, e2] | .Mul, [e1, e2] | .Div, [e1, e2] | .Mod, [e1, e2] | .DivT, [e1, e2] | .ModT, [e1, e2] =>
      if check env e1 (mkTy .TInt) && check env e2 (mkTy .TInt) then .some (mkTy .TInt) else .none
    | .Lt, [e1, e2] | .Leq, [e1, e2] | .Gt, [e1, e2] | .Geq, [e1, e2] =>
      if check env e1 (mkTy .TInt) && check env e2 (mkTy .TInt) then .some (mkTy .TInt) else .none
    | .Eq, [e1, e2] | .Neq, [e1, e2] =>
      match synth env e1 with
      | .some ty1 =>
        if check env e2 ty1 then .some (mkTy .TBool) else .none
      | .none => match synth env e2 with
        | .some ty2 =>
          if check env e1 ty2 then .some (mkTy .TBool) else .none
        | .none => .none
    | .And, [e1, e2] | .Or, [e1, e2] | .Implies, [e1, e2] =>
      if check env e1 (mkTy .TBool) && check env e2 (mkTy .TBool) then .some (mkTy .TBool) else .none
    | .StrConcat, [e1, e2] =>
      if check env e1 (mkTy .TString) && check env e2 (mkTy .TString) then .some (mkTy .TString) else .none
    | .Not, [e] =>
      if check env e (mkTy .TBool) then .some (mkTy .TBool) else .none
    | .Neg, [e] => if check env e (mkTy .TInt) then .some (mkTy .TInt) else .none
    | _, _ => panic! s!"Unsupported operation: {repr op}(...)"
  | _ => .none

/-- Check that an expression has the expected type -/
partial def check (env : TypeEnv) (expr : StmtExprMd) (ty : HighTypeMd) : Bool :=
  match (expr.val, ty.val) with
  | (.LiteralBool _, .TBool) => true
  | (.LiteralInt _, .TInt) => true
  | (.LiteralString _, .TString) => true
  | (.Return none, .TVoid) => true
  | (.Return (some e), _) => check env e ty
  | (.IfThenElse cond thenB elseB, _) =>
    check env cond (mkTy .TBool) &&
      check env thenB ty && Option.elim elseB true (check env · ty)
  | (.While cond _ _ body, .TVoid) =>
    check env cond (mkTy .TBool) && check env body ty
  | (.Block stmts _, .TVoid) => stmts.all (check env · ty)
  | (_, _) => match (highEq · ty) <$> synth env expr with
    | some b => b
    | none => false
  end

end Strata.Laurel

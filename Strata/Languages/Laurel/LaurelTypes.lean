/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat
public import Strata.Languages.Laurel.Resolution
import Strata.Util.Tactics

public section

/-
Type computation for Laurel StmtExpr.

All types are determined by annotations on parameters and variable declarations —
no inference is performed.
-/

namespace Strata.Laurel

/--
Compute the HighType of a StmtExpr given a type environment, type definitions, and procedure list.
No inference is performed — all types are determined by annotations on parameters
and variable declarations.
-/
def computeExprType (model : SemanticModel) (expr : StmtExprMd) : HighTypeMd :=
  match _: expr with
  | WithMetadata.mk val md =>
  match _: val with
  -- Literals
  | .LiteralInt _ => ⟨ .TInt, md ⟩
  | .LiteralBool _ => ⟨ .TBool, md ⟩
  | .LiteralString _ => ⟨ .TString, md ⟩
  | .LiteralDecimal _ => ⟨ .TReal, md ⟩
  -- Variables
  | .Identifier id => (model.get id).getType.getD (panic "computeExprType1")
  -- Field access
  | .FieldSelect _ fieldName => (model.get fieldName).getType.getD (panic "computeExprType2")
  -- Pure field update returns the same type as the target
  | .PureFieldUpdate target _ _ => computeExprType model target
  -- Calls — we don't track return types here, so fall back to TVoid
  | .StaticCall callee _ => match model.get callee with
    | .datatypeConstructor t _ => ⟨ .UserDefined t, md, ⟩
    | .parameter p => p.type
    | .staticProcedure proc => match proc.outputs with
      | [singleOutput] => singleOutput.type
      | _ => { val := .TVoid, md := default }
    | .unresolved => { val := .Top, md := default }
    | astNode => panic! s!"static call to {callee} not to a procedure but to a {repr astNode}"
  | .InstanceCall _ _ _ => panic "Not supported InstanceCall"
  -- Operators
  | .PrimitiveOp op args =>
      match args with
      | head :: tail =>
        match op with
        | .Eq | .Neq | .And | .Or | .Not | .Implies | .Lt | .Leq | .Gt | .Geq => ⟨ .TBool, md ⟩
        | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT =>
          match (computeExprType model head).val with
            | .TFloat64  => ⟨ .TFloat64, md ⟩
            | .TReal => ⟨ .TReal, md ⟩
            | .TInt => ⟨ .TInt, md ⟩
            | _ => ⟨ .TCore "unknown", md ⟩
        | .StrConcat => ⟨ .TString, md ⟩
      | _ => ⟨ .TCore "unknown", md ⟩
  -- Control flow
  | .IfThenElse _ thenBranch _ => computeExprType model thenBranch
  | .Block stmts _ => match _blockGetLastResult: stmts.getLast? with
    | some last =>
        have := List.mem_of_getLast? _blockGetLastResult
        computeExprType model last
    | none => ⟨ .TVoid, md ⟩
  -- Statements
  | .LocalVariable _ _ _ => ⟨ .TVoid, md ⟩
  | .While _ _ _ _ => ⟨ .TVoid, md ⟩
  | .Exit _ => ⟨ .TVoid, md ⟩
  | .Return _ => ⟨ .TVoid, md ⟩
  | .Assign _ value => computeExprType model value
  | .Assert _ => ⟨ .TVoid, md ⟩
  | .Assume _ => ⟨ .TVoid, md ⟩
  -- Instance related
  | .New name => ⟨ .UserDefined name, md ⟩
  | .This => panic "'This' not supported" -- would need `this` type from context
  | .ReferenceEquals _ _ => ⟨ .TBool, md ⟩
  | .AsType _ ty => ty
  | .IsType _ _ => ⟨ .TBool, md ⟩
  -- Verification specific
  | .Forall _ _ _ => ⟨ .TBool, md ⟩
  | .Exists _ _ _ => ⟨ .TBool, md ⟩
  | .Assigned _ => ⟨ .TBool, md ⟩
  | .Old v => computeExprType model v
  | .Fresh _ => ⟨ .TBool, md ⟩
  -- Proof related
  | .ProveBy v _ => computeExprType model v
  | .ContractOf _ _ => panic "ContractOf Not supported"
  -- Special
  | .Abstract => panic "Abstract Not supported"
  | .All => panic "All Not supported"
  | .Hole => ⟨ .Top, md ⟩

end Strata.Laurel

end

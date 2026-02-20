/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-
Type computation for Laurel StmtExpr.

All types are determined by annotations on parameters and variable declarations —
no inference is performed.
-/

namespace Strata.Laurel

abbrev TypeEnv := List (Identifier × HighTypeMd)

/--
Look up a field's type in a composite type by name.
-/
def lookupFieldInTypes (types : List TypeDefinition) (typeName : Identifier) (fieldName : Identifier) : Option HighTypeMd :=
  types.findSome? fun td =>
    match td with
    | .Composite ct =>
        if ct.name == typeName then ct.fields.findSome? fun f =>
          if f.name == fieldName then some f.type else none
        else none
    | _ => none

/--
Compute the HighType of a StmtExpr given a type environment and type definitions.
No inference is performed — all types are determined by annotations on parameters
and variable declarations.
-/
def computeExprType (env : TypeEnv) (types : List TypeDefinition) (expr : StmtExprMd) : HighTypeMd :=
  match expr with
  | WithMetadata.mk val md =>
  match val with
  -- Literals
  | .LiteralInt _ => ⟨ .TInt, md ⟩
  | .LiteralBool _ => ⟨ .TBool, md ⟩
  | .LiteralString _ => ⟨ .TString, md ⟩
  -- Variables
  | .Identifier name =>
      match env.find? (fun (n, _) => n == name) with
      | some (_, ty) => ty
      | none => panic s!"Could not find variable {name} in environment"
  -- Field access
  | .FieldSelect target fieldName =>
      match computeExprType env types target with
      | WithMetadata.mk (.UserDefined typeName) _ =>
          match lookupFieldInTypes types typeName fieldName with
          | some ty => ty
          | none => panic s!"Could not find field in type"
      | _ => panic s!"Selecting from a type that's not a composite"
  -- Pure field update returns the same type as the target
  | .PureFieldUpdate target _ _ => computeExprType env types target
  -- Calls — we don't track return types here, so fall back to TVoid
  | .StaticCall _ _ => panic "Not supported StaticCall"
  | .InstanceCall _ _ _ => panic "Not supported InstanceCall"
  -- Operators
  | .PrimitiveOp op _ =>
      match op with
      | .Eq | .Neq | .And | .Or | .Not | .Implies | .Lt | .Leq | .Gt | .Geq => ⟨ .TBool, md ⟩
      | .Neg | .Add | .Sub | .Mul | .Div | .Mod | .DivT | .ModT => ⟨ .TInt, md ⟩
  -- Control flow
  | .IfThenElse _ thenBranch _ => computeExprType env types thenBranch
  | .Block stmts _ => match _blockGetLastResult: stmts.getLast? with
    | some last =>
        have := List.mem_of_getLast? _blockGetLastResult
        computeExprType env types last
    | none => ⟨ .TVoid, md ⟩
  -- Statements (void-typed)
  | .LocalVariable _ _ _ => ⟨ .TVoid, md ⟩
  | .While _ _ _ _ => ⟨ .TVoid, md ⟩
  | .Exit _ => ⟨ .TVoid, md ⟩
  | .Return _ => ⟨ .TVoid, md ⟩
  | .Assign _ _ => ⟨ .TVoid, md ⟩
  | .Assert _ => ⟨ .TVoid, md ⟩
  | .Assume _ => ⟨ .TVoid, md ⟩
  -- Instance related
  | .New name => ⟨ .UserDefined name, md ⟩
  | .This => panic "Not supported" -- would need `this` type from context
  | .ReferenceEquals _ _ => ⟨ .TBool, md ⟩
  | .AsType _ ty => ty
  | .IsType _ _ => ⟨ .TBool, md ⟩
  -- Verification specific
  | .Forall _ _ _ => ⟨ .TBool, md ⟩
  | .Exists _ _ _ => ⟨ .TBool, md ⟩
  | .Assigned _ => ⟨ .TBool, md ⟩
  | .Old v => computeExprType env types v
  | .Fresh _ => ⟨ .TBool, md ⟩
  -- Proof related
  | .ProveBy v _ => computeExprType env types v
  | .ContractOf _ _ => panic "Not supported"
  -- Special
  | .Abstract => panic "Not supported"
  | .All => panic "Not supported"
  | .Hole => panic "Not supported"

end Strata.Laurel

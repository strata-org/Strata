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
  | .Identifier id => (model.get id).getType
  -- Field access
  | .FieldSelect _ fieldName => (model.get fieldName).getType
  -- Pure field update returns the same type as the target
  | .PureFieldUpdate target _ _ => computeExprType model target
  -- Calls — return the declared output type when available, fall back to Unknown otherwise
  | .StaticCall callee _ => match model.get callee with
    | .datatypeConstructor t _ => ⟨ .UserDefined t, md, ⟩
    | .parameter p => p.type
    | .staticProcedure proc => match proc.outputs with
      | [singleOutput] => singleOutput.type
      | _ => { val := HighType.Unknown, md := default }
    | .unresolved => { val := HighType.Unknown, md := default }
    | astNode =>
      dbg_trace s!"BUG: static call to {callee} not to a procedure but to a {repr astNode}"
      default
  | .InstanceCall _ _ _ => default -- TODO: implement
  -- Operators
  | .PrimitiveOp op args =>
      match args with
      | head :: tail =>
        match op with
        | .Eq | .Neq | .And | .Or | .AndThen | .OrElse | .Not | .Implies | .Lt | .Leq | .Gt | .Geq => ⟨ .TBool, md ⟩
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
  | .This => default -- TODO: implement
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
  | .ContractOf _ _ => default -- TODO: implement
  -- Special
  | .Abstract =>default -- TODO: implement
  | .All => default -- TODO: implement
  | .Hole _ typeOption => typeOption.getD  ⟨ HighType.Unknown, md ⟩

/-- Classification of a heap-relevant modifies type. -/
inductive ModifiesTypeKind where
  | composite    -- a single Composite reference (UserDefined)
  | compositeSet -- a Set of Composite references (TSet)

/-- Classify a type as heap-relevant for modifies clauses, or `none` for
non-heap-relevant types. Single source of truth for which types participate
in modifies clauses and heap parameterization. -/
def classifyModifiesHighType : HighType → Option ModifiesTypeKind
  | .UserDefined _ => some .composite
  | .TSet _        => some .compositeSet
  | _              => none

/-- Returns `true` when the given `HighType` is heap-relevant (composite or set
of composite), i.e. the kind of type that appears in modifies clauses and
triggers heap parameterization. -/
def isHeapRelevantType (ty : HighType) : Bool :=
  (classifyModifiesHighType ty).isSome

end Strata.Laurel

end

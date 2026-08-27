/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.SemanticModel

public section

/-
Type computation for Laurel StmtExpr.

All types are determined by annotations on parameters and variable declarations —
no inference is performed.
-/

namespace Strata.Laurel

def getCallType (source : FileRange) (model : SemanticModel) (callee : Identifier): HighTypeMd :=
  match model.get callee with
    | .datatypeConstructor t _ => ⟨ .UserDefined t, source ⟩
    | .datatypeDestructor _ fld => fld.type
    | .parameter p => p.type
    | .staticProcedure proc | .instanceProcedure _ proc => match proc.outputs with
      | [] => { val := .TVoid, source := source }
      | [singleOutput] => singleOutput.type
      | outputs => { val := .MultiValuedExpr (outputs.map (·.type)), source := source }
    -- A coroutine call (`c(args)`) spawns an instance of the coroutine type;
    -- elaboration later retargets this to the `<c>State` composite.
    | .coroutineType proc => ⟨ .UserDefined proc.name, source ⟩
    | .unresolved source => { val := HighType.Unknown, source := source }
    | astNode =>
      dbg_trace s!"BUG: static call to {callee} not to a procedure but to a {repr astNode}"
      default

/-- Type of `resume(target)` — the target coroutine's first `yields` binding.
    `targetTy` types as `.UserDefined <coroutine>`, resolved via the model like
    `getCallType`. `TVoid` when it yields nothing. `Unknown` for an unresolved
    ref or a gradual `Unknown` target (`Synth.resume` already diagnosed / left
    those); a target that resolves to any other concrete kind is a resolver-
    invariant violation, reported as a BUG like `getCallType`. -/
def getResumeType (source : FileRange) (model : SemanticModel) (targetTy : HighTypeMd) : HighTypeMd :=
  match targetTy.val with
  | .Unknown => ⟨ .Unknown, source ⟩
  | .UserDefined ref =>
    match model.get ref with
    | .coroutineType proc => proc.yields.head?.map (·.type) |>.getD ⟨ .TVoid, source ⟩
    | .unresolved source => ⟨ .Unknown, source ⟩
    | astNode =>
      dbg_trace s!"BUG: resume target {ref} not a coroutine but a {repr astNode}"
      default
  | _ =>
    dbg_trace s!"BUG: resume target is not an object type but a {repr targetTy.val}"
    default

/--
Compute the HighType of a StmtExpr given a type environment, type definitions, and procedure list.
No inference is performed — all types are determined by annotations on parameters
and variable declarations.

A bare `yield` types as `Unknown` here: its type is the enclosing coroutine's
first `resumes` binding, and this utility has no enclosing-procedure context.
Resolution types `yield` from `Context.resumeType` instead, so nothing needs it
from here.
-/
def computeExprType (model : SemanticModel) (expr : StmtExprMd) : HighTypeMd :=
  match _: expr with
  | AstNode.mk val source =>
  match _: val with
  -- Literals
  | .LiteralInt _ => ⟨ .TInt, source ⟩
  | .LiteralBool _ => ⟨ .TBool, source ⟩
  | .LiteralString _ => ⟨ .TString, source ⟩
  | .LiteralDecimal _ => ⟨ .TReal, source ⟩
  | .LiteralBv _ width => ⟨ .TBv width, source ⟩
  -- Variables
  | .Var (.Local id) => (model.get id).getType
  | .Var (.Declare _) => ⟨ .TVoid, source ⟩
  -- Field access
  | .Var (.Field _ fieldName) => (model.get fieldName).getType
  -- Pure field update returns the same type as the target
  | .PureFieldUpdate target _ _ => computeExprType model target
  -- Calls — return the declared output type when available, fall back to Unknown otherwise
  | .StaticCall callee _ => getCallType source model callee
  | .InstanceCall _ callee _ => getCallType source model callee
  -- Control flow
  | .IfThenElse _ thenBranch _ => computeExprType model thenBranch
  | .Block stmts _ => match _blockGetLastResult: stmts.getLast? with
    | some last =>
        have := List.mem_of_getLast? _blockGetLastResult
        computeExprType model last
    | none => ⟨ .TVoid, source ⟩
  -- Statements
  | .While _ _ _ _ _ => ⟨ .TVoid, source ⟩
  | .Exit _ => ⟨ .TVoid, source ⟩
  | .Return _ => ⟨ .TVoid, source ⟩
  | .Assign _ value => computeExprType model value
  | .IncrDecr _ _ target =>
    -- The expression's type is the type of the target variable.
    match target.val with
    | .Local id => (model.get id).getType
    | .Field _ fieldName => (model.get fieldName).getType
    | .Declare _ => ⟨ .TVoid, source ⟩  -- shouldn't happen; rejected by translator
  | .CompoundAssign _ target _ =>
    -- Yields the new value, whose type is the target variable's type.
    match target.val with
    | .Local id => (model.get id).getType
    | .Field _ fieldName => (model.get fieldName).getType
    | .Declare _ => ⟨ .TVoid, source ⟩  -- shouldn't happen; rejected by translator
  | .Assert .. => ⟨ .TVoid, source ⟩
  | .Assume _ => ⟨ .TVoid, source ⟩
  | .Throw _ => ⟨ .TVoid, source ⟩
  | .Try _ _ _ => ⟨ .TVoid, source ⟩
  -- Instance related
  -- `new C` has type `C`; `new C<τ…>` has the applied type `C<τ…>` so downstream
  -- (e.g. monomorphization) sees the concrete instantiation.
  | .New name typeArgs =>
    if typeArgs.isEmpty then ⟨ .UserDefined name, source ⟩
    else ⟨ .Applied ⟨ .UserDefined name, source ⟩ typeArgs, source ⟩
  | .This => default -- TODO: implement
  | .ReferenceEquals _ _ => ⟨ .TBool, source ⟩
  | .AsType _ ty => ty
  | .IsType _ _ => ⟨ .TBool, source ⟩
  -- Verification specific
  | .Quantifier _ _ _ _ => ⟨ .TBool, source ⟩
  | .Assigned _ => ⟨ .TBool, source ⟩
  | .Old v _ => computeExprType model v
  | .OldGuarantee v => computeExprType model v
  | .OldRelies v => computeExprType model v
  | .Fresh _ => ⟨ .TBool, source ⟩
  -- Proof related
  | .ProveBy v _ => computeExprType model v
  | .ContractOf _ _ => default -- TODO: implement
  -- Special
  | .Abstract =>default -- TODO: implement
  | .All => default -- TODO: implement
  | .Hole _ typeOption => typeOption.getD  ⟨ HighType.Unknown, source ⟩
  -- `resume(t)` is `t`'s first `yields` binding (see `getResumeType`); `yield`
  -- would be the enclosing coroutine's first `resumes` binding (see above).
  | .Yield => ⟨ .Unknown, source ⟩
  | .Resume target _ => getResumeType source model (computeExprType model target)
  | .HasNext _ => ⟨ .TBool, source ⟩
  -- Snapshot artifact: `Snapshot` is a statement, so it types as `TVoid`.
  | .Snapshot _ => ⟨ .TVoid, source ⟩

/-- Classification of a heap-relevant modifies type. -/
inductive ModifiesTypeKind where
  | composite    -- a single Composite reference (UserDefined)
  | compositeSet -- a Set of Composite references (TSet)

/-- Classify a type as heap-relevant for modifies clauses, or `none` for
non-heap-relevant types. Single source of truth for which types participate
in modifies clauses and heap parameterization. -/
def classifyModifiesHighType : HighType → Option ModifiesTypeKind
  | .UserDefined _ => some .composite
  -- A generic-composite INSTANTIATION (`GHolder<Pair<int,bool>>`) is a composite
  -- reference too: it peels to a `.UserDefined` base. This predicate gates
  -- modifies-clause entry survival + classification at RESOLUTION (isHeapRelevantType,
  -- Resolution.resolveModifiesEntry), which runs BEFORE monomorphization — so a
  -- `modifies g` on a generically-typed var still sees `.Applied` here and would be
  -- wrongly dropped as "non-composite" without this arm. (It does NOT feed heap
  -- parameterization, which keys off write-effects, not this classification; and
  -- monomorphization later collapses the type to plain `.UserDefined` for the
  -- post-mono frame builder.) Matches the sibling `.UserDefined` arm's model-free
  -- fidelity: a generic DATATYPE base would also classify `.composite` here and fail
  -- loud downstream at Core, exactly as a bare datatype var already does.
  | .Applied base _ => match base.val with
    | .UserDefined _ => some .composite
    | _              => none
  | .TSet _        => some .compositeSet
  | _              => none

/-- Returns `true` when the given `HighType` is heap-relevant (composite or set
of composite), i.e. the kind of type that appears in modifies clauses and
triggers heap parameterization. -/
def isHeapRelevantType (ty : HighType) : Bool :=
  (classifyModifiesHighType ty).isSome


end Strata.Laurel

end

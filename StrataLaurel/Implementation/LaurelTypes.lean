/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.SemanticModel

public section

/-
Type computation for Laurel StmtExpr.

All types are determined by annotations on parameters and variable declarations —
no inference is performed.
-/

namespace Strata.Laurel

/-- `declared`, a type in a declaration with type parameters `params`, at the type arguments
    `typeArgs`. Matching by name is sound here, since a declaration's types mention only its own
    parameters. An arity mismatch keeps the declared type rather than a half-applied one. -/
private def instantiateDeclared (params : List Identifier) (typeArgs : List HighTypeMd)
    (declared : HighTypeMd) : HighTypeMd :=
  if params.isEmpty || typeArgs.length != params.length then declared
  else substTypeVars ((params.zip typeArgs).foldl (fun m (p, t) => m.insert p.text t) ∅) declared

/-- A procedure's declared result type at `typeArgs`: `TVoid` with no outputs, the single output's
    type, or a `MultiValuedExpr` of all of them — with the procedure's type parameters
    substituted. -/
def procResultTypeAt (source : FileRange) (proc : Procedure)
    (typeArgs : List HighTypeMd) : HighTypeMd :=
  instantiateDeclared proc.typeArgs typeArgs <| match proc.outputs with
    | [] => { val := .TVoid, source := source }
    | [singleOutput] => singleOutput.type
    | outputs => { val := .MultiValuedExpr (outputs.map (·.type)), source := source }

/-- The type a call has AT THIS CALL SITE. `typeArgs` are the type arguments the call node
    records; pass `[]` for a call shape that carries none. A constructor's type is its datatype
    applied to `typeArgs`, a destructor's is its field's declared type with `typeArgs`
    substituted for the datatype's type parameters, and a procedure's is its declared output
    type with `typeArgs` substituted for the procedure's type parameters. When `typeArgs` is
    empty the constructor stays the bare datatype head: an applied shape with free type variables
    in it would read as a wildcard instead of the arity error we want. -/
def getCallType (source : FileRange) (model : SemanticModel) (callee : Identifier)
    (typeArgs : List HighTypeMd) : HighTypeMd :=
  match model.get callee with
    | .datatypeConstructor t _ =>
      if typeArgs.isEmpty then ⟨ .UserDefined t, source ⟩
      else ⟨ .Applied ⟨ .UserDefined t, source ⟩ typeArgs, source ⟩
    | .datatypeDestructor t fld =>
      let params := match model.get t with
        | .datatypeDefinition dt => dt.typeArgs
        | _ => []
      instantiateDeclared params typeArgs fld.type
    | .parameter p => p.type
    | .staticProcedure proc | .instanceProcedure _ proc =>
      procResultTypeAt source proc typeArgs
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

`lattice?`, when given, types a field at its holder's type and an instance call at the type
arguments it records or its receiver and arguments bind, none of which `model` records.
-/
def computeExprTypeWith (lattice? : Option TypeLattice)
    (model : SemanticModel) (expr : StmtExprMd) : HighTypeMd :=
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
  | .Var (.Stack t) => t.getD ⟨ .Unknown, source ⟩
  -- Field access
  | .Var (.Field target fieldName) =>
    let declared := (model.get fieldName).getType
    match lattice?, model.get fieldName with
    | some lattice, .field declType fld =>
      (lattice.fieldTypeAt declType fld.type (computeExprTypeWith lattice? model target)).getD
        declared
    | _, _ => declared
  -- Pure field update returns the same type as the target
  | .PureFieldUpdate target _ _ => computeExprTypeWith lattice? model target
  -- Calls — the callee's return type at this call site, so a generic callee reports its
  -- instantiation rather than its declared `T`. `ContractPass` types a polymorphic callee's
  -- argument temp from the argument itself and needs that instantiation.
  | .Call none callee _ tyArgs => getCallType source model callee tyArgs
  | .Call (some target) callee args tyArgs =>
    match lattice?, model.get callee with
    | some lattice, .instanceProcedure owner proc =>
      let receiverTy := computeExprTypeWith lattice? model target
      let argTys := receiverTy :: args.attach.map fun ⟨a, _⟩ => computeExprTypeWith lattice? model a
      -- The holder's own type arguments come from the receiver, even when they name the caller's
      -- type variables, which `callSiteTypeSubst` leaves unbound.
      let fromArgs := (callSiteTypeSubst lattice (fun _ => false) (proc.inputs.map (·.type)) argTys).1
      let fromHolder := ((lattice.holderSubst? owner receiverTy).getD {}).fold (·.insert) fromArgs
      let subst := (proc.typeArgs.zip tyArgs).foldl (fun m (a, t) => m.insert a.text t) fromHolder
      let result := procResultTypeAt source proc []
      -- A type parameter neither the call's recorded type arguments nor its receiver and
      -- arguments bind, as a bare `Holder`'s, is not known here.
      if (tvarIdents result.val).any (!subst.contains ·.text) then { result with val := .Unknown }
      else substTypeVars subst result
    | _, _ => getCallType source model callee []
  -- Control flow
  -- A then-branch typed `Unknown`, as a hole is, takes the else-branch's type, as in `Resolution`.
  | .IfThenElse _ thenBranch elseBranch =>
    let thenTy := computeExprTypeWith lattice? model thenBranch
    match thenTy.val, elseBranch with
    | .Unknown, some e => computeExprTypeWith lattice? model e
    | _, _ => thenTy
  | .Block stmts _ _ _ => match _blockGetLastResult: stmts.getLast? with
    | some last =>
        have := List.mem_of_getLast? _blockGetLastResult
        computeExprTypeWith lattice? model last
    | none => ⟨ .TVoid, source ⟩
  -- Statements
  | .While _ _ _ _ _ => ⟨ .TVoid, source ⟩
  | .Goto _ _ => ⟨ .TVoid, source ⟩
  | .Return _ => ⟨ .TVoid, source ⟩
  -- Its target's type, as `Synth.assign` types it.
  | .Assign [⟨.Local id, _⟩] _ => (model.get id).getType
  | .Assign [⟨.Field target fieldName, src⟩] _ =>
    computeExprTypeWith lattice? model ⟨.Var (.Field target fieldName), src⟩
  | .Assign [⟨.Declare ⟨_, some ty⟩, _⟩] _ => ty
  | .Assign _ value => computeExprTypeWith lattice? model value
  | .IncrDecr _ _ target =>
    -- The expression's type is the type of the target variable.
    match target.val with
    | .Local id => (model.get id).getType
    | .Field _ fieldName => (model.get fieldName).getType
    | .Declare _ | .Stack _ => ⟨ .TVoid, source ⟩  -- shouldn't happen; rejected by translator
  | .CompoundAssign _ target _ =>
    -- Yields the new value, whose type is the target variable's type.
    match target.val with
    | .Local id => (model.get id).getType
    | .Field _ fieldName => (model.get fieldName).getType
    | .Declare _ | .Stack _ => ⟨ .TVoid, source ⟩  -- shouldn't happen; rejected by translator
  | .Assert .. => ⟨ .TVoid, source ⟩
  | .Assume _ => ⟨ .TVoid, source ⟩
  | .Throw _ => ⟨ .TVoid, source ⟩
  | .Try _ _ _ => ⟨ .TVoid, source ⟩
  -- Instance related
  | .New name typeArgs => allocatedType name typeArgs source
  | .This => default -- TODO: implement
  | .ReferenceEquals _ _ => ⟨ .TBool, source ⟩
  | .AsType _ ty => ty
  | .IsType _ _ => ⟨ .TBool, source ⟩
  -- Verification specific
  | .Quantifier _ _ _ _ => ⟨ .TBool, source ⟩
  | .Assigned _ => ⟨ .TBool, source ⟩
  | .Old v _ => computeExprTypeWith lattice? model v
  | .OldGuarantee v => computeExprTypeWith lattice? model v
  | .OldRelies v => computeExprTypeWith lattice? model v
  | .Fresh _ => ⟨ .TBool, source ⟩
  -- Proof related
  | .ProveBy v _ => computeExprTypeWith lattice? model v
  | .ContractOf _ _ => default -- TODO: implement
  -- Special
  | .Abstract =>default -- TODO: implement
  | .All => default -- TODO: implement
  | .Hole _ typeOption => typeOption.getD  ⟨ HighType.Unknown, source ⟩
  -- `resume(t)` is `t`'s first `yields` binding (see `getResumeType`); `yield`
  -- would be the enclosing coroutine's first `resumes` binding (see above).
  | .Yield => ⟨ .Unknown, source ⟩
  | .Resume target _ => getResumeType source model (computeExprTypeWith lattice? model target)
  | .HasNext _ => ⟨ .TBool, source ⟩
  -- Snapshot artifact: `Snapshot` is a statement, so it types as `TVoid`.
  | .Snapshot _ => ⟨ .TVoid, source ⟩

/-- `computeExprTypeWith` without a field hint. -/
def computeExprType (model : SemanticModel) (expr : StmtExprMd) : HighTypeMd :=
  computeExprTypeWith none model expr

/-- `ty`, a type in `callee`'s signature, at the instantiation `typeArgs` a call to it records. A
    pass that introduces a local for one of the call's arguments or outputs declares it at this type:
    the callee's declared type variable is the same at every call site, so declaring that would make
    two instantiations collide. -/
def typeAtCall (model : SemanticModel) (callee : Identifier) (typeArgs : List HighTypeMd)
    (ty : HighTypeMd) : HighTypeMd :=
  match model.get callee with
  | .staticProcedure proc | .instanceProcedure _ proc =>
    instantiateDeclared proc.typeArgs typeArgs ty
  | _ => ty

/-- Classification of a heap-relevant modifies type. -/
inductive ModifiesTypeKind where
  | composite    -- a single Composite reference (UserDefined, bare or applied)
  | compositeSet -- a Set of Composite references (TSet)

/-- Classify a type as heap-relevant for modifies clauses, or `none` for non-heap-relevant
types. `isValueTypeName` decides whether a nominal head names a VALUE rather than a heap
reference, which a type's shape alone cannot tell.

An APPLICATION counts: a generic-composite instantiation (`GHolder<Pair<int,bool>>`) is still
a reference, and this runs BEFORE monomorphization, so `modifies g` on a generically-typed var
would otherwise be wrongly dropped as "non-composite". A `.TVar` head is deliberately not
matched: a type parameter has no declaration to ask, and it carries no bound, so whether it
stands for a reference is undecidable here and it is refused conservatively.

`.TSet` has no surface production, so `.compositeSet` is unreachable from source: `Set<C>`
parses as an application of the prelude's `opaque Set<T>` and takes the value arm. -/
def classifyModifiesHighType (isValueTypeName : Identifier → Bool) :
    HighType → Option ModifiesTypeKind
  | .TSet _ => some .compositeSet
  | .UserDefined n
  | .Applied ⟨.UserDefined n, _⟩ _ => if isValueTypeName n then none else some .composite
  | _ => none


end Strata.Laurel

end

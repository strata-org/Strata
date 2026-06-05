/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution

/-!
# Lift Instance Procedures

A Laurel-to-Laurel pass that lifts every instance procedure (a procedure
defined inside a `composite` block) to a top-level static procedure with a
mangled name `<CompositeName>$<methodName>`, then rewrites every call site
that resolved to such an instance procedure to use the lifted name.

After this pass:
- `CompositeType.instanceProcedures` is empty for every composite.
- `program.staticProcedures` contains the lifted procedures.
- Every `InstanceCall` (from `obj#method(args)` surface syntax) points
  at the lifted name. For `InstanceCall`, the receiver is prepended to
  the argument list to match the lifted procedure's `self : <CompositeName>`
  parameter.

The pipeline runs `resolve` again after this pass (`needsResolves := true`)
so the fresh static procedures and the rewritten call sites get bound.
-/

namespace Strata.Laurel

/-! ## uniqueId clearing on cloned procedures

The cloned procedure inherits `Identifier.uniqueId` values from the prior
resolve pass. `defineNameCheckDup` reuses an existing uniqueId, which can
collide across siblings (e.g. two lifted procs both with a `self` parameter
sharing a uid from the original composite scope). We clear every uniqueId
on the clone; the resolution pass that follows will re-assign them.
-/

private def clearIdent (id : Identifier) : Identifier :=
  { id with uniqueId := none }

private def clearHighType (ty : HighTypeMd) : HighTypeMd :=
  match _h: ty.val with
  | .UserDefined name => { ty with val := .UserDefined (clearIdent name) }
  | .TTypedField vt => { ty with val := .TTypedField (clearHighType vt) }
  | .TSet et => { ty with val := .TSet (clearHighType et) }
  | .TMap kt vt => { ty with val := .TMap (clearHighType kt) (clearHighType vt) }
  | .Applied base args =>
    { ty with val := .Applied (clearHighType base) (args.map clearHighType) }
  | .Pure base => { ty with val := .Pure (clearHighType base) }
  | .Intersection tys =>
    { ty with val := .Intersection (tys.map clearHighType) }
  | .MultiValuedExpr tys =>
    { ty with val := .MultiValuedExpr (tys.map clearHighType) }
  | _ => ty
  termination_by sizeOf ty
  decreasing_by
    all_goals (have := AstNode.sizeOf_val_lt ty; simp_all; try omega)
    all_goals (have := List.sizeOf_lt_of_mem ‹_›; simp_all; omega)

private def clearParameter (p : Parameter) : Parameter :=
  { name := clearIdent p.name, type := clearHighType p.type }

/-- Clear `uniqueId` on every Identifier reachable from a `StmtExprMd`.
    Uses `mapStmtExprM` for recursion. -/
private def clearExprIds (expr : StmtExprMd) : StmtExprMd :=
  let oneNode (e : StmtExprMd) : StmtExprMd :=
    match e.val with
    | .Var (.Local name) => { e with val := .Var (.Local (clearIdent name)) }
    | .Var (.Field target name) =>
      { e with val := .Var (.Field target (clearIdent name)) }
    | .Var (.Declare param) =>
      { e with val := .Var (.Declare (clearParameter param)) }
    | .Assign targets value =>
      let targets' := targets.map fun v => match v.val with
        | .Local name => { v with val := .Local (clearIdent name) }
        | .Field target name => { v with val := .Field target (clearIdent name) }
        | .Declare param => { v with val := .Declare (clearParameter param) }
      { e with val := .Assign targets' value }
    | .StaticCall callee args =>
      { e with val := .StaticCall (clearIdent callee) args }
    | .InstanceCall target callee args =>
      { e with val := .InstanceCall target (clearIdent callee) args }
    | .PureFieldUpdate target name newValue =>
      { e with val := .PureFieldUpdate target (clearIdent name) newValue }
    | .New ref => { e with val := .New (clearIdent ref) }
    | .Quantifier mode param trigger body =>
      { e with val := .Quantifier mode (clearParameter param) trigger body }
    | .AsType target ty => { e with val := .AsType target (clearHighType ty) }
    | .IsType target ty => { e with val := .IsType target (clearHighType ty) }
    | .Hole det (some ty) => { e with val := .Hole det (some (clearHighType ty)) }
    | _ => e
  mapStmtExpr oneNode expr

private def clearCondition (c : Condition) : Condition :=
  { c with condition := clearExprIds c.condition }

private def clearBody (body : Body) : Body :=
  match body with
  | .Transparent b => .Transparent (clearExprIds b)
  | .Opaque ps impl modif =>
    .Opaque (ps.map clearCondition) (impl.map clearExprIds) (modif.map clearExprIds)
  | .Abstract ps => .Abstract (ps.map clearCondition)
  | .External => .External

private def clearProcUniqueIds (proc : Procedure) : Procedure :=
  { proc with
    name := clearIdent proc.name
    inputs := proc.inputs.map clearParameter
    outputs := proc.outputs.map clearParameter
    preconditions := proc.preconditions.map clearCondition
    decreases := proc.decreases.map clearExprIds
    invokeOn := proc.invokeOn.map clearExprIds
    body := clearBody proc.body }

/-! ## Lifting + call-site rewriting -/

/-- Rewrite a single node so that any callee resolving to an instance procedure
    is replaced by its lifted name. -/
private def rewriteCallNode (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  match expr.val with
  | .StaticCall callee args =>
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted args }
    | _ => expr
  | .InstanceCall target callee args =>
    -- `obj#method(args)` surface syntax parses to InstanceCall. Flatten it to
    -- a static call against the lifted name, prepending the receiver as the
    -- first argument to match the lifted procedure's `self` parameter.
    match model.get? callee with
    | some (.instanceProcedure typeName _) =>
      let lifted := liftedProcName typeName callee
      { expr with val := .StaticCall lifted (target :: args) }
    | _ => expr
  | _ => expr

/-- Apply call-site rewriting to every expression in a procedure. -/
private def rewriteCallsInProc (model : SemanticModel) (proc : Procedure) : Procedure :=
  let f := mapStmtExpr (rewriteCallNode model)
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (f b)
    | .Opaque ps impl modif =>
      .Opaque (ps.map (·.mapCondition f)) (impl.map f) (modif.map f)
    | .Abstract ps => .Abstract (ps.map (·.mapCondition f))
    | .External => .External
  { proc with
    body := resolveBody proc.body
    preconditions := proc.preconditions.map (·.mapCondition f)
    decreases := proc.decreases.map f
    invokeOn := proc.invokeOn.map f }

/-- Apply call-site rewriting to a constrained type's constraint and witness. -/
private def rewriteCallsInType (model : SemanticModel) (td : TypeDefinition) : TypeDefinition :=
  match td with
  | .Constrained ct =>
    let f := mapStmtExpr (rewriteCallNode model)
    .Constrained { ct with constraint := f ct.constraint, witness := f ct.witness }
  | _ => td

/-- Apply call-site rewriting to a constant's initializer. -/
private def rewriteCallsInConstant (model : SemanticModel) (c : Constant) : Constant :=
  let f := mapStmtExpr (rewriteCallNode model)
  { c with initializer := c.initializer.map f }

public section

/--
Lift every `proc ∈ ct.instanceProcedures` to a top-level static procedure
named `s!"{ct.name.text}${proc.name.text}"` (see `liftedProcName`), rewrite
every call site whose callee resolved to an instance procedure, and clear
`instanceProcedures` on every composite.

The pipeline re-runs `resolve` after this pass so the fresh names get bound.
-/
def liftInstanceProcedures (model : SemanticModel) (program : Program) : Program :=
  -- Step 1: collect lifted clones, with all uniqueIds cleared.
  let liftedProcs : List Procedure :=
    program.types.foldl (init := []) fun acc td =>
      match td with
      | .Composite ct =>
        acc ++ ct.instanceProcedures.map fun proc =>
          let renamed := { proc with name := liftedProcName ct.name proc.name }
          clearProcUniqueIds renamed
      | _ => acc

  if liftedProcs.isEmpty then program else

  -- Step 2: rewrite call sites everywhere they could appear.
  let rewrittenStaticProcs := program.staticProcedures.map (rewriteCallsInProc model)
  let rewrittenLiftedProcs := liftedProcs.map (rewriteCallsInProc model)
  let rewrittenTypes := program.types.map (rewriteCallsInType model)
  let rewrittenConstants := program.constants.map (rewriteCallsInConstant model)

  -- Step 3: clear instanceProcedures on every composite.
  let cleanedTypes := rewrittenTypes.map fun td =>
    match td with
    | .Composite ct => .Composite { ct with instanceProcedures := [] }
    | _ => td

  -- Step 4: append lifted procs.
  { program with
    staticProcedures := rewrittenStaticProcs ++ rewrittenLiftedProcs
    types := cleanedTypes
    constants := rewrittenConstants }

end -- public section

end Strata.Laurel

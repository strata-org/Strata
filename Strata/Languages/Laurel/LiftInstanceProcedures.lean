/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass

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
-/

namespace Strata.Laurel

/-! ## Lifting + call-site rewriting

Lift instance procedures to static scope (e.g., procedure `proc`
of composite type `T` will be lifted to `T$proc`).
Then, rewrite caller-side of `obj#proc` to call the lifted procedure

-/

/-- Top-level name produced for a lifted instance procedure. -/
def liftedProcName (typeName methodName : Identifier) : Identifier :=
  mkId s!"{typeName.text}${methodName.text}"

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

public section

/--
Lift every `proc ∈ ct.instanceProcedures` to a top-level static procedure
named via `liftedProcName`, rewrite call sites that resolved to an instance
procedure, and clear `instanceProcedures` on every composite.
-/
def liftInstanceProcedures (model : SemanticModel) (program : Program) : Program :=
  -- Step 1: collect lifted clones
  let liftedProcs : List Procedure :=
    program.types.foldl (init := []) fun acc td =>
      match td with
      | .Composite ct =>
        acc ++ ct.instanceProcedures.map fun proc =>
          { proc with name := liftedProcName ct.name proc.name }
      | _ => acc

  if liftedProcs.isEmpty then program else

  -- Step 2: rewrite call sites in procedure bodies and constrained-type
  let rewrittenStaticProcs := program.staticProcedures.map (rewriteCallsInProc model)
  let rewrittenLiftedProcs := liftedProcs.map (rewriteCallsInProc model)
  let rewrittenTypes := program.types.map (rewriteCallsInType model)

  -- Step 3: clear instanceProcedures on every composite.
  let cleanedTypes := rewrittenTypes.map fun td =>
    match td with
    | .Composite ct => .Composite { ct with instanceProcedures := [] }
    | _ => td

  -- Step 4: append lifted procs.
  { program with
    staticProcedures := rewrittenStaticProcs ++ rewrittenLiftedProcs
    types := cleanedTypes }

end -- public section

/-- Pipeline pass: lift instance procedures to top-level static procedures
    and rewrite call sites to use the lifted names. -/
public def liftInstanceProceduresPass : LaurelPass where
  name := "LiftInstanceProcedures"
  documentation := "Lifts every procedure declared inside a `composite` block to a top-level static procedure named `<CompositeName>$<methodName>` and rewrites call sites resolved to an instance procedure (including `obj#method(args)` surface syntax) to point at the lifted name. Clears `instanceProcedures` on every composite. Must run before HeapParameterization."
  needsResolves := true
  run := fun p m => (liftInstanceProcedures m p, [], {})

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.UnorderedCore
import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.TransparencyPass

/-!
## Inline Local Variables Pass

Runs after the transparency pass and operates **only on functions** (the
`$asFunction` copies produced by the transparency pass). Function bodies are
pure expressions and cannot contain local variable declarations once they reach
the Core schema translation. This pass eliminates them by inlining.

For each local variable of the form `var <name> := <expr>`, every reference to
`<name>` that occurs after the declaration is replaced with `<expr>`, and the
declaration itself is dropped. The inlined expression is itself inlined first,
so chains like

```
var a := 1;
var b := a + 1;
```

become `b ↦ 1 + 1`.

Because functions are pure, an inlined variable is never reassigned. Any
assignment to such a `<name>` is therefore a user error and emits a diagnostic.
-/

namespace Strata.Laurel

/-- Substitution from an inlined local variable name to the expression it was
    initialized with. Newer bindings are pushed to the front so `List.lookup`
    finds the most recent declaration first. -/
private abbrev InlineSubst := List (Identifier × StmtExprMd)

/-- Diagnostics are accumulated in the state. -/
private abbrev InlineM := StateM (Array DiagnosticModel)

private def emitDiag (d : DiagnosticModel) : InlineM Unit :=
  modify (·.push d)

public section

mutual

/--
Inline local variables within an expression, given the substitution in scope.

Only `Block` nodes introduce new (sequential) scope, so the substitution is not
threaded back out of `inlineExpr`; child expressions simply inherit `subst`.
-/
private partial def inlineExpr (subst : InlineSubst) (expr : StmtExprMd) : InlineM StmtExprMd := do
  let source := expr.source
  match expr.val with
  | .Var (.Local name) =>
    match subst.lookup name with
    | some replacement => return replacement
    | none => return expr
  | .Var (.Field target fieldName) =>
    return ⟨.Var (.Field (← inlineExpr subst target) fieldName), source⟩
  | .Var (.Declare _) => return expr

  | .Block stmts label =>
    let stmts' ← inlineBlockStmts subst stmts
    return ⟨.Block stmts' label, source⟩

  | .Assign targets value =>
    -- An assignment to an inlined local is contradictory: report it.
    for t in targets do
      match t.val with
      | .Local name =>
        if (subst.lookup name).isSome then
          emitDiag (diagnosticFromSource (t.source.orElse fun _ => source)
            s!"cannot assign to '{name.text}': it is an inlined local variable")
      | _ => pure ()
    let targets' ← targets.mapM (inlineVariable subst)
    let value' ← inlineExpr subst value
    return ⟨.Assign targets' value', source⟩

  | .IfThenElse cond th el =>
    let cond' ← inlineExpr subst cond
    let th' ← inlineExpr subst th
    let el' ← el.mapM (inlineExpr subst)
    return ⟨.IfThenElse cond' th' el', source⟩

  | .While cond invs dec body =>
    let cond' ← inlineExpr subst cond
    let invs' ← invs.mapM (inlineExpr subst)
    let dec' ← dec.mapM (inlineExpr subst)
    let body' ← inlineExpr subst body
    return ⟨.While cond' invs' dec' body', source⟩

  | .Return value =>
    return ⟨.Return (← value.mapM (inlineExpr subst)), source⟩

  | .PrimitiveOp op args skipProof =>
    return ⟨.PrimitiveOp op (← args.mapM (inlineExpr subst)) skipProof, source⟩

  | .StaticCall callee args =>
    return ⟨.StaticCall callee (← args.mapM (inlineExpr subst)), source⟩

  | .InstanceCall target callee args =>
    let target' ← inlineExpr subst target
    let args' ← args.mapM (inlineExpr subst)
    return ⟨.InstanceCall target' callee args', source⟩

  | .PureFieldUpdate target fieldName newValue =>
    let target' ← inlineExpr subst target
    let newValue' ← inlineExpr subst newValue
    return ⟨.PureFieldUpdate target' fieldName newValue', source⟩

  | .ReferenceEquals lhs rhs =>
    return ⟨.ReferenceEquals (← inlineExpr subst lhs) (← inlineExpr subst rhs), source⟩

  | .AsType target ty =>
    return ⟨.AsType (← inlineExpr subst target) ty, source⟩

  | .IsType target ty =>
    return ⟨.IsType (← inlineExpr subst target) ty, source⟩

  | .Quantifier mode param trigger body =>
    -- The bound variable shadows any inlined local of the same name.
    let innerSubst := subst.filter (·.1 != param.name)
    let trigger' ← trigger.mapM (inlineExpr innerSubst)
    let body' ← inlineExpr innerSubst body
    return ⟨.Quantifier mode param trigger' body', source⟩

  | .Assigned name =>
    return ⟨.Assigned (← inlineExpr subst name), source⟩

  | .Old value =>
    return ⟨.Old (← inlineExpr subst value), source⟩

  | .Fresh value =>
    return ⟨.Fresh (← inlineExpr subst value), source⟩

  | .Assert cond =>
    return ⟨.Assert { cond with condition := ← inlineExpr subst cond.condition }, source⟩

  | .Assume cond =>
    return ⟨.Assume (← inlineExpr subst cond), source⟩

  | .ProveBy value proof =>
    return ⟨.ProveBy (← inlineExpr subst value) (← inlineExpr subst proof), source⟩

  | .ContractOf ty func =>
    return ⟨.ContractOf ty (← inlineExpr subst func), source⟩

  | .IncrDecr mode op target =>
    return ⟨.IncrDecr mode op (← inlineVariable subst target), source⟩

  -- Leaves: nothing to inline.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .LiteralBv _ _ | .New _ | .This | .Abstract | .All | .Hole .. => return expr

/-- Inline within the target expression of a field variable; other variable
    forms have no sub-expressions to rewrite. -/
private partial def inlineVariable (subst : InlineSubst) (v : VariableMd) : InlineM VariableMd := do
  match v.val with
  | .Field target fieldName =>
    return ⟨.Field (← inlineExpr subst target) fieldName, v.source⟩
  | _ => return v

/--
Process the statements of a block sequentially, threading the substitution.

A `var <name> := <expr>` declaration (`Assign` with a single `Declare` target)
is removed, and `<name>` is bound to the inlined `<expr>` for the remaining
statements. All other statements are inlined under the current substitution.
-/
private partial def inlineBlockStmts (subst : InlineSubst) (stmts : List StmtExprMd) : InlineM (List StmtExprMd) := do
  match stmts with
  | [] => return []
  | stmt :: rest =>
    match stmt.val with
    | .Assign [⟨.Declare param, _⟩] value =>
      let value' ← inlineExpr subst value
      inlineBlockStmts ((param.name, value') :: subst) rest
    | _ =>
      let stmt' ← inlineExpr subst stmt
      let rest' ← inlineBlockStmts subst rest
      return stmt' :: rest'

end

/-- Inline local variables in a single function, returning the rewritten
    procedure and any diagnostics. -/
def inlineLocalVariablesInFunction (proc : Procedure) : Procedure × Array DiagnosticModel :=
  match proc.body with
  | .Transparent body =>
    let (body', diags) := (inlineExpr [] body).run #[]
    ({ proc with body := .Transparent body' }, diags)
  | .Opaque postconds impl modif =>
    match impl with
    | some i =>
      let (i', diags) := (inlineExpr [] i).run #[]
      ({ proc with body := .Opaque postconds (some i') modif }, diags)
    | none => (proc, #[])
  | _ => (proc, #[])

/-- Inline local variables in every function of an `UnorderedCoreWithLaurelTypes`.
    Only `functions` are transformed; `coreProcedures` are left unchanged. -/
def inlineLocalVariablesInFunctions (uc : UnorderedCoreWithLaurelTypes)
    : UnorderedCoreWithLaurelTypes × List DiagnosticModel :=
  let results := uc.functions.map inlineLocalVariablesInFunction
  let functions' := results.map (·.1)
  let diags := results.flatMap (·.2.toList)
  ({ uc with functions := functions' }, diags)

public def inlineLocalVariablesPass : LaurelPass UnorderedCoreWithLaurelTypes UnorderedCoreWithLaurelTypes where
  name := "InlineLocalVariablesPass"
  documentation := "Inlines local variable declarations of the form `var <name> := <expr>` in function bodies. References to the variable after its declaration are replaced with the initializer expression, and the declaration is removed. Assignments to an inlined variable emit a diagnostic. Operates only on functions, which are pure and cannot carry local variable declarations into Core."
  comesAfter := [⟨ transparencyPass.meta, "Inlining of local variables in functions only makes sense after the transparency pass has created the functions"⟩]
  run := fun p _ _ =>
    let (uc, diags) := inlineLocalVariablesInFunctions p
    (uc, diags, {})

end -- public section

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.OrderedProgram
import Strata.Languages.Laurel.DeclGrouping

/-!
# Laurel.Program → Laurel.OrderedProgram

Structural analysis pass that converts a flat `Laurel.Program` into an
`OrderedProgram` with topologically ordered, grouped declarations.
Axiom generation is handled separately by `generateAxioms`.
No expression translation is performed.
-/

namespace Strata.Laurel

/-- Replace occurrences of `Identifier target` with `replacement` in a StmtExpr tree.
    Compares by `uniqueId` to handle shadowing correctly. -/
public partial def substIdentifier (target : Identifier) (replacement : StmtExprMd)
    (expr : StmtExprMd) : StmtExprMd :=
  let md := expr.md
  let go := substIdentifier target replacement
  match expr.val with
  | .Identifier name =>
    if name.uniqueId == target.uniqueId then replacement else expr
  | .PrimitiveOp op args => ⟨.PrimitiveOp op (args.map go), md⟩
  | .StaticCall callee args => ⟨.StaticCall callee (args.map go), md⟩
  | .IfThenElse c t e => ⟨.IfThenElse (go c) (go t) (e.map go), md⟩
  | .Block stmts label => ⟨.Block (stmts.map go) label, md⟩
  | .Forall param trigger body =>
    ⟨.Forall param (trigger.map go) (go body), md⟩
  | .Exists param trigger body =>
    ⟨.Exists param (trigger.map go) (go body), md⟩
  | .Assign targets value => ⟨.Assign (targets.map go) (go value), md⟩
  | .LocalVariable name ty init => ⟨.LocalVariable name ty (init.map go), md⟩
  | .Return v => ⟨.Return (v.map go), md⟩
  | .Assert c => ⟨.Assert (go c), md⟩
  | .Assume c => ⟨.Assume (go c), md⟩
  | .Old v => ⟨.Old (go v), md⟩
  | .Fresh v => ⟨.Fresh (go v), md⟩
  | .ReferenceEquals l r => ⟨.ReferenceEquals (go l) (go r), md⟩
  | .AsType t ty => ⟨.AsType (go t) ty, md⟩
  | .IsType t ty => ⟨.IsType (go t) ty, md⟩
  | .ProveBy v p => ⟨.ProveBy (go v) (go p), md⟩
  | .FieldSelect t f => ⟨.FieldSelect (go t) f, md⟩
  | .PureFieldUpdate t f v => ⟨.PureFieldUpdate (go t) f (go v), md⟩
  | .InstanceCall t callee args => ⟨.InstanceCall (go t) callee (args.map go), md⟩
  | .While c inv dec body =>
    ⟨.While (go c) (inv.map go) (dec.map go) (go body), md⟩
  | .Assigned v => ⟨.Assigned (go v), md⟩
  | .ContractOf ty f => ⟨.ContractOf ty (go f), md⟩
  | _ => expr

/-- Conjoin a list of StmtExpr with `And`. -/
public def conjoin (exprs : List StmtExprMd) (md : MetaData) : StmtExprMd :=
  match exprs with
  | [] => ⟨.LiteralBool true, md⟩
  | [single] => single
  | first :: rest => rest.foldl (fun acc p => ⟨.PrimitiveOp .And [acc, p], md⟩) first

/-- Build `forall p1. forall p2 :: { trigger }. body` as a StmtExpr.
    Trigger is placed on the innermost quantifier. -/
private def buildForallChain (params : List Parameter) (trigger : StmtExprMd)
    (body : StmtExprMd) (md : MetaData) : StmtExprMd :=
  match params with
  | [] => body
  | [p] => ⟨.Forall p (some trigger) body, md⟩
  | p :: rest => ⟨.Forall p none (buildForallChain rest trigger body md), md⟩

/-- Generate a postcondition axiom for a function with ensures clauses.
    Produces: `forall (inputs) :: { f(inputs) } => postconds[result := f(inputs)]` -/
private def mkPostcondAxiom (proc : Procedure) (postconds : List StmtExprMd)
    (resultParam : Parameter) : Option LaurelAxiom :=
  if postconds.isEmpty then none
  else
    let md := proc.md
    let argExprs := proc.inputs.map fun p => ⟨StmtExpr.Identifier p.name, md⟩
    let callExpr : StmtExprMd := ⟨.StaticCall proc.name argExprs, md⟩
    -- Substitute result with f(args) in each postcondition
    let substPosts := postconds.map (substIdentifier resultParam.name callExpr)
    let body := conjoin substPosts md
    let axiomBody := buildForallChain proc.inputs callExpr body md
    some ⟨s!"{proc.name.text}$postcondition", axiomBody, md⟩

/-- Generate an invokeOn axiom for a procedure.
    Produces: `forall (inputs) :: { trigger } => postconds` -/
private def mkInvokeOnAxiom (proc : Procedure) (trigger : StmtExprMd)
    : Option LaurelAxiom :=
  let postconds := match proc.body with
    | .Opaque postconds _ _ => postconds
    | _ => []
  if postconds.isEmpty then none
  else
    let md := proc.md
    let body := conjoin postconds md
    let axiomBody := buildForallChain proc.inputs trigger body md
    some (⟨s!"invokeOn_{proc.name.text}", axiomBody, md⟩ : LaurelAxiom)

/-- Strip postconditions from a Transparent body (after axiom generation). -/
private def stripTransparentPostconds (proc : Procedure) : Procedure :=
  match proc.body with
  | .Transparent body (_ :: _) => { proc with body := .Transparent body [] }
  | _ => proc

/-- Convert a `Laurel.Program` into an `OrderedProgram`. -/
public def toLaurelOrdered (program : Program)
    : OrderedProgram × List DiagnosticModel :=
  -- Emit diagnostics for composite types with instance procedures
  let diagnostics : List DiagnosticModel := program.types.flatMap fun
    | .Composite ct => ct.instanceProcedures.map fun proc =>
        proc.md.toDiagnostic
          s!"Instance procedure '{proc.name.text}' on composite type '{ct.name.text}' is not yet supported"
          DiagnosticType.NotYetImplemented
    | _ => []

  -- Group datatypes by SCC
  let laurelDatatypes := program.types.filterMap fun
    | .Datatype dt => some dt | _ => none
  let datatypeGroups := groupDatatypes laurelDatatypes
  let datatypeDecls := datatypeGroups.map OrderedDecl.datatypes

  -- Constants
  let constantDecls := program.constants.map OrderedDecl.constant

  -- Order and group procedures by SCC
  let sccDecls := computeSccDecls program
  let callableDecls := sccDecls.flatMap fun (procs, isRecursive) =>
    let isFuncSCC := procs.all (·.isFunctional)
    if isFuncSCC then
      [OrderedDecl.funcs procs [] isRecursive]
    else
      procs.map fun proc => OrderedDecl.proc proc []

  (⟨datatypeDecls ++ constantDecls ++ callableDecls⟩, diagnostics)

/-- Populate axioms on an `OrderedProgram`.
    Generates postcondition axioms for functions with `ensures` clauses
    and invokeOn axioms for procedures with triggers. -/
public def generateAxioms (op : OrderedProgram) : OrderedProgram :=
  { decls := op.decls.map fun
    | .funcs procs _ isRec =>
      let axioms := procs.filterMap fun proc =>
        let (postconds, resultParam?) := match proc.body with
          | .Transparent _ posts => (posts, proc.outputs.head?)
          | .Opaque posts _ _ => (posts, proc.outputs.head?)
          | .Abstract posts => (posts, proc.outputs.head?)
          | _ => ([], none)
        resultParam?.bind (mkPostcondAxiom proc postconds ·)
      -- Strip postconditions from transparent bodies after generating axioms
      let procs := procs.map stripTransparentPostconds
      .funcs procs axioms isRec
    | .proc proc _ =>
      let axioms := match proc.invokeOn with
        | some trigger => (mkInvokeOnAxiom proc trigger).toList
        | none => []
      .proc proc axioms
    | other => other }

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.Resolution

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Adding `requires` for constrained-typed inputs (Core handles caller asserts and body assumes)
2. Adding `ensures` for constrained-typed outputs (Core handles body checks and caller assumes)
   - Skipped for `isFunctional` procedures since the Laurel translator does not yet support
     function postconditions. Constrained return types on functions are not checked.
3. Inserting `assert` for local variable init and reassignment of constrained-typed variables
4. Using the witness as default initializer for uninitialized constrained-typed variables
5. Adding a synthetic witness-validation procedure per constrained type
6. Injecting constraints into quantifier bodies (`forall` → `implies`, `exists` → `and`)
7. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType
/-- Map from variable name to its constrained HighType (e.g. UserDefined "nat") -/
abbrev PredVarMap := Std.HashMap String HighType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => resolveBaseType ptMap ct.base.val | none => ty
  | .Applied ctor args =>
    .Applied ctor (args.map fun a => ⟨resolveBaseType ptMap a.val, a.md⟩)
  | _ => ty

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.md⟩

def isConstrainedType (ptMap : ConstrainedTypeMap) (ty : HighType) : Bool :=
  match ty with | .UserDefined name => ptMap.contains name.text | _ => false

/-- All predicates for a type transitively (e.g. evenpos → [(x, x > 0), (x, x % 2 == 0)]) -/
partial def getAllConstraints (ptMap : ConstrainedTypeMap) (ty : HighType)
    : List (Identifier × StmtExprMd) :=
  match ty with
  | .UserDefined name => match ptMap.get? name.text with
    | some ct => (ct.valueName, ct.constraint) :: getAllConstraints ptMap ct.base.val
    | none => []
  | _ => []

/-- Substitute `Identifier old` with `Identifier new` in a constraint expression -/
partial def substId (old new : Identifier) : StmtExprMd → StmtExprMd
  | ⟨.Identifier n, md⟩ => ⟨if n == old then .Identifier new else .Identifier n, md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.map fun a => substId old new a), md⟩
  | ⟨.StaticCall c args, md⟩ =>
    ⟨.StaticCall c (args.map fun a => substId old new a), md⟩
  | ⟨.IfThenElse c t (some el), md⟩ =>
    ⟨.IfThenElse (substId old new c) (substId old new t) (some (substId old new el)), md⟩
  | ⟨.IfThenElse c t none, md⟩ =>
    ⟨.IfThenElse (substId old new c) (substId old new t) none, md⟩
  | ⟨.Block ss sep, md⟩ =>
    ⟨.Block (ss.map fun s => substId old new s) sep, md⟩
  | ⟨.Forall param body, md⟩ =>
    if param.name == old then ⟨.Forall param body, md⟩
    else if param.name == new then
      let fresh : Identifier := mkId (param.name.text ++ "$")
      ⟨.Forall { param with name := fresh } (substId old new (substId param.name fresh body)), md⟩
    else ⟨.Forall param (substId old new body), md⟩
  | ⟨.Exists param body, md⟩ =>
    if param.name == old then ⟨.Exists param body, md⟩
    else if param.name == new then
      let fresh : Identifier := mkId (param.name.text ++ "$")
      ⟨.Exists { param with name := fresh } (substId old new (substId param.name fresh body)), md⟩
    else ⟨.Exists param (substId old new body), md⟩
  | e => e

def mkAsserts (ptMap : ConstrainedTypeMap) (ty : HighType) (varName : Identifier)
    (md : Imperative.MetaData Core.Expression) : List StmtExprMd :=
  (getAllConstraints ptMap ty).map fun (valueName, pred) =>
    ⟨.Assert (substId valueName varName pred), md⟩

private def wrap (stmts : List StmtExprMd) (md : Imperative.MetaData Core.Expression)
    : StmtExprMd :=
  match stmts with | [s] => s | ss => ⟨.Block ss none, md⟩

/-- Inject constraints into a quantifier body for a constrained type -/
private def injectQuantifierConstraint (ptMap : ConstrainedTypeMap) (ty : HighType)
    (varName : Identifier) (body : StmtExprMd) (isForall : Bool) : StmtExprMd :=
  let constraints := getAllConstraints ptMap ty
  match constraints with
  | [] => body
  | _ =>
    let preds := constraints.map fun (vn, pred) => substId vn varName pred
    let conj := preds.tail.foldl (init := preds.head!) fun acc p =>
      ⟨.PrimitiveOp .And [acc, p], body.md⟩
    if isForall then ⟨.PrimitiveOp .Implies [conj, body], body.md⟩
    else ⟨.PrimitiveOp .And [conj, body], body.md⟩

/-- Resolve constrained types in all type positions of an expression -/
def resolveExpr (ptMap : ConstrainedTypeMap) : StmtExprMd → StmtExprMd
  | ⟨.LocalVariable n ty (some init), md⟩ =>
    ⟨.LocalVariable n (resolveType ptMap ty) (some (resolveExpr ptMap init)), md⟩
  | ⟨.LocalVariable n ty none, md⟩ =>
    ⟨.LocalVariable n (resolveType ptMap ty) none, md⟩
  | ⟨.Forall param body, md⟩ =>
    let body' := resolveExpr ptMap body
    let param' := { param with type := resolveType ptMap param.type }
    ⟨.Forall param' (injectQuantifierConstraint ptMap param.type.val param.name body' true), md⟩
  | ⟨.Exists param body, md⟩ =>
    let body' := resolveExpr ptMap body
    let param' := { param with type := resolveType ptMap param.type }
    ⟨.Exists param' (injectQuantifierConstraint ptMap param.type.val param.name body' false), md⟩
  | ⟨.AsType t ty, md⟩ => ⟨.AsType (resolveExpr ptMap t) (resolveType ptMap ty), md⟩
  | ⟨.IsType t ty, md⟩ => ⟨.IsType (resolveExpr ptMap t) (resolveType ptMap ty), md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => resolveExpr ptMap a), md⟩
  | ⟨.StaticCall c args, md⟩ =>
    ⟨.StaticCall c (args.attach.map fun ⟨a, _⟩ => resolveExpr ptMap a), md⟩
  | ⟨.Block ss sep, md⟩ =>
    ⟨.Block (ss.attach.map fun ⟨s, _⟩ => resolveExpr ptMap s) sep, md⟩
  | ⟨.IfThenElse c t (some el), md⟩ =>
    ⟨.IfThenElse (resolveExpr ptMap c) (resolveExpr ptMap t) (some (resolveExpr ptMap el)), md⟩
  | ⟨.IfThenElse c t none, md⟩ =>
    ⟨.IfThenElse (resolveExpr ptMap c) (resolveExpr ptMap t) none, md⟩
  | ⟨.While c inv dec body, md⟩ =>
    ⟨.While (resolveExpr ptMap c) (inv.attach.map fun ⟨i, _⟩ => resolveExpr ptMap i)
            dec (resolveExpr ptMap body), md⟩
  | ⟨.Assign ts v, md⟩ =>
    ⟨.Assign (ts.attach.map fun ⟨t, _⟩ => resolveExpr ptMap t) (resolveExpr ptMap v), md⟩
  | ⟨.Return (some v), md⟩ => ⟨.Return (some (resolveExpr ptMap v)), md⟩
  | ⟨.Return none, md⟩ => ⟨.Return none, md⟩
  | ⟨.Assert c, md⟩ => ⟨.Assert (resolveExpr ptMap c), md⟩
  | ⟨.Assume c, md⟩ => ⟨.Assume (resolveExpr ptMap c), md⟩
  | e => e
termination_by e => sizeOf e
decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt ‹_›; term_by_mem)

/-- Insert asserts for constrained-typed variable init and reassignment -/
abbrev ElimM := StateM PredVarMap

def elimStmt (ptMap : ConstrainedTypeMap)
    (stmt : StmtExprMd) : ElimM (List StmtExprMd) := do
  let md := stmt.md
  match _h : stmt.val with
  | .LocalVariable name ty init =>
    let isPred := isConstrainedType ptMap ty.val
    if isPred then modify fun pv => pv.insert name.text ty.val
    let asserts := if isPred then mkAsserts ptMap ty.val name md else []
    -- Use witness as default initializer for uninitialized constrained variables
    let init' := match init with
      | none => match ty.val with
        | .UserDefined n => (ptMap.get? n.text).map (·.witness)
        | _ => none
      | some _ => init
    pure ([⟨.LocalVariable name ty init', md⟩] ++ asserts)

  -- Single-target only; multi-target assignments are not supported by the Laurel grammar
  | .Assign [target] _ => match target.val with
    | .Identifier name => do
      match (← get).get? name.text with
      | some ty => pure ([stmt] ++ mkAsserts ptMap ty name md)
      | none => pure [stmt]
    | _ => pure [stmt]

  | .Block stmts sep =>
    let stmtss ← stmts.mapM (elimStmt ptMap)
    pure [⟨.Block stmtss.flatten sep, md⟩]

  | .IfThenElse cond thenBr (some elseBr) =>
    let thenSs ← elimStmt ptMap thenBr
    let elseSs ← elimStmt ptMap elseBr
    pure [⟨.IfThenElse cond (wrap thenSs md) (some (wrap elseSs md)), md⟩]
  | .IfThenElse cond thenBr none =>
    let thenSs ← elimStmt ptMap thenBr
    pure [⟨.IfThenElse cond (wrap thenSs md) none, md⟩]

  | .While cond inv dec body =>
    let bodySs ← elimStmt ptMap body
    pure [⟨.While cond inv dec (wrap bodySs md), md⟩]

  | _ => pure [stmt]
termination_by sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals (try have := WithMetadata.sizeOf_val_lt stmt)
  all_goals (try term_by_mem)
  all_goals omega

def elimProc (ptMap : ConstrainedTypeMap) (proc : Procedure) : Procedure :=
  -- Add requires for constrained-typed inputs
  let inputRequires := proc.inputs.flatMap fun p =>
    (getAllConstraints ptMap p.type.val).map fun (vn, pred) =>
      ⟨(substId vn p.name pred).val, p.type.md⟩
  -- Add ensures for constrained-typed outputs (skip for isFunctional — not yet supported)
  let outputEnsures := if proc.isFunctional then [] else proc.outputs.flatMap fun p =>
    (getAllConstraints ptMap p.type.val).map fun (vn, pred) =>
      ⟨(substId vn p.name pred).val, p.type.md⟩
  -- Transform body: insert asserts for local variable init/reassignment
  let initVars : PredVarMap := proc.inputs.foldl (init := {}) fun s p =>
    if isConstrainedType ptMap p.type.val then s.insert p.name.text p.type.val else s
  let body' := match proc.body with
  | .Transparent bodyExpr =>
    let (stmts, _) := (elimStmt ptMap bodyExpr).run initVars
    let body := wrap stmts bodyExpr.md
    if outputEnsures.isEmpty then .Transparent body
    else
      -- Wrap expression body in a Return so it translates correctly as a procedure
      let retBody := if proc.isFunctional then ⟨.Return (some body), bodyExpr.md⟩ else body
      .Opaque outputEnsures (some retBody) []
  | .Opaque postconds impl modif =>
    let impl' := impl.map fun b => wrap ((elimStmt ptMap b).run initVars).1 b.md
    .Opaque (postconds ++ outputEnsures) impl' modif
  | .Abstract postconds => .Abstract (postconds ++ outputEnsures)
  | .External => .External
  -- Resolve all constrained types to base types
  let resolve := resolveExpr ptMap
  let resolveBody : Body → Body := fun body => match body with
    | .Transparent b => .Transparent (resolve b)
    | .Opaque ps impl modif => .Opaque (ps.map resolve) (impl.map resolve) (modif.map resolve)
    | .Abstract ps => .Abstract (ps.map resolve)
    | .External => .External
  { proc with
    body := resolveBody body'
    inputs := proc.inputs.map fun p => { p with type := resolveType ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType ptMap p.type }
    preconditions := (proc.preconditions ++ inputRequires).map resolve }

/-- Create a synthetic procedure that asserts the witness satisfies all constraints -/
private def mkWitnessProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let md := ct.witness.md
  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.LocalVariable witnessId (resolveType ptMap ct.base) (some ct.witness), md⟩
  let asserts := (getAllConstraints ptMap (.UserDefined ct.name)).map fun (vn, pred) =>
    ⟨.Assert (substId vn witnessId pred), md⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Transparent ⟨.Block ([witnessInit] ++ asserts) none, md⟩
    preconditions := []
    isFunctional := false
    determinism := .deterministic none
    decreases := none
    md := md }

/-- Eliminate constrained types from a Laurel program.
    The `witness` field is used as the default initializer for uninitialized
    constrained-typed variables, and is validated via synthetic procedures. -/
def constrainedTypeElim (_model : SemanticModel) (program : Program) : Program × Array DiagnosticModel :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, #[]) else
  -- Report unsupported: isFunctional procedures with constrained return types
  let funcDiags := program.staticProcedures.foldl (init := #[]) fun acc proc =>
    if proc.isFunctional && proc.outputs.any (fun p => isConstrainedType ptMap p.type.val) then
      acc.push (proc.md.toDiagnostic "constrained return types on functions are not yet supported")
    else acc
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc ptMap ct)
    | _ => none
  ({ program with
    staticProcedures := program.staticProcedures.map (elimProc ptMap) ++ witnessProcedures
    types := program.types.filter fun | .Constrained _ => false | _ => true },
   funcDiags)

end Strata.Laurel

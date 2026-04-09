/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelTypes

/-!
# Subscript Elimination

Type-aware pass that desugars `Subscript` nodes based on the target type:
- `Seq<T>`: read → `Sequence.select`, update → `Sequence.update`
- `Array<T>`: read → `Sequence.select(a#$data, i)`,
              update → `Assign [FieldSelect a "$data"] (Sequence.update(a#$data, i, v))`

After this pass, no `Subscript` nodes remain in the program.
-/

namespace Strata.Laurel

open Strata

private def mkCall (name : String) (args : List StmtExprMd) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  ⟨.StaticCall (mkId name) args, md⟩

private def mkFieldSelect (target : StmtExprMd) (field : String) (md : Imperative.MetaData Core.Expression) : StmtExprMd :=
  ⟨.FieldSelect target (mkId field), md⟩

private def isArrayType (model : SemanticModel) (target : StmtExprMd) : Bool :=
  match (computeExprType model target).val with
  | .TArray _ => true
  | _ => false

private def isArrayHighType (ty : HighType) : Bool :=
  match ty with
  | .TArray _ => true
  | _ => false

/-- Redirect Sequence.* args that are Array-typed to use $data field -/
private def redirectArrayArgs (model : SemanticModel) (callee : Identifier)
    (origArgs : List StmtExprMd) (args : List StmtExprMd)
    (md : Imperative.MetaData Core.Expression) : List StmtExprMd :=
  if callee.text.startsWith SeqOp.namePrefix then
    args.mapIdx fun i a =>
      if i == 0 && isArrayType model (origArgs[0]!) then mkFieldSelect a SeqOp.dataField md
      else if i == 1 && callee.text == SeqOp.append && origArgs.length > 1 && isArrayType model (origArgs[1]!) then mkFieldSelect a SeqOp.dataField md
      else a
  else args

def elimExpr (model : SemanticModel) : StmtExprMd → StmtExprMd
  | ⟨.Subscript target index none, md⟩ =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    if isArrayType model target then
      mkCall SeqOp.select [mkFieldSelect target' SeqOp.dataField md, index'] md
    else
      mkCall SeqOp.select [target', index'] md
  | ⟨.Subscript target index (some value), md⟩ =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    let value' := elimExpr model value
    if isArrayType model target then
      let data := mkFieldSelect target' SeqOp.dataField md
      ⟨.Assign [mkFieldSelect target' SeqOp.dataField md] (mkCall SeqOp.update [data, index', value'] md), md⟩
    else
      mkCall SeqOp.update [target', index', value'] md
  | ⟨.Block stmts label, md⟩ =>
    let expandStmt : (s : StmtExprMd) → s ∈ stmts → List StmtExprMd := fun stmt _ =>
      match stmt with
      | ⟨.LocalVariable n ty (some initExpr), smd⟩ =>
        if isArrayHighType ty.val && !isArrayType model initExpr then
          let initExpr' := elimExpr model initExpr
          [⟨.LocalVariable n ty (some ⟨.New (mkId arrayCompositeName), smd⟩), smd⟩,
           ⟨.Assign [mkFieldSelect ⟨.Identifier n, smd⟩ SeqOp.dataField smd] initExpr', smd⟩]
        else [elimExpr model stmt]
      | _ => [elimExpr model stmt]
    ⟨.Block (stmts.attach.flatMap fun ⟨s, h⟩ => expandStmt s h) label, md⟩
  | ⟨.IfThenElse c t e, md⟩ =>
    ⟨.IfThenElse (elimExpr model c) (elimExpr model t)
      (match e with | some e => some (elimExpr model e) | none => none), md⟩
  | ⟨.LocalVariable n ty init, md⟩ =>
    ⟨.LocalVariable n ty (match init with | some i => some (elimExpr model i) | none => none), md⟩
  | ⟨.While c invs dec body, md⟩ =>
    ⟨.While (elimExpr model c) (invs.attach.map fun ⟨i, _⟩ => elimExpr model i)
            (match dec with | some d => some (elimExpr model d) | none => none) (elimExpr model body), md⟩
  | ⟨.Assign [⟨.Subscript target index none, smd⟩] value, md⟩ =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    let value' := elimExpr model value
    if isArrayType model target then
      let data := mkFieldSelect target' SeqOp.dataField smd
      ⟨.Assign [mkFieldSelect target' SeqOp.dataField smd] (mkCall SeqOp.update [data, index', value'] smd), md⟩
    else
      -- Seq is immutable — subscript assign is a user error. Downstream will reject.
      ⟨.Assign [mkCall SeqOp.select [target', index'] smd] value', md⟩
  | ⟨.Assign targets value, md⟩ =>
    ⟨.Assign (targets.attach.map fun ⟨t, _⟩ => elimExpr model t) (elimExpr model value), md⟩
  | ⟨.StaticCall callee args, md⟩ =>
    let args' := args.attach.map fun ⟨a, _⟩ => elimExpr model a
    let args' := redirectArrayArgs model callee args args' md
    ⟨.StaticCall callee args', md⟩
  | ⟨.PrimitiveOp op args, md⟩ =>
    ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => elimExpr model a), md⟩
  | ⟨.Return (some v), md⟩ => ⟨.Return (some (elimExpr model v)), md⟩
  | ⟨.Return none, md⟩ => ⟨.Return none, md⟩
  | ⟨.Forall p t body, md⟩ =>
    ⟨.Forall p (match t with | some t => some (elimExpr model t) | none => none) (elimExpr model body), md⟩
  | ⟨.Exists p t body, md⟩ =>
    ⟨.Exists p (match t with | some t => some (elimExpr model t) | none => none) (elimExpr model body), md⟩
  | ⟨.Assert c, md⟩ => ⟨.Assert (elimExpr model c), md⟩
  | ⟨.Assume c, md⟩ => ⟨.Assume (elimExpr model c), md⟩
  | ⟨.Old v, md⟩ => ⟨.Old (elimExpr model v), md⟩
  | ⟨.Fresh v, md⟩ => ⟨.Fresh (elimExpr model v), md⟩
  | ⟨.Assigned v, md⟩ => ⟨.Assigned (elimExpr model v), md⟩
  | ⟨.ProveBy v p, md⟩ => ⟨.ProveBy (elimExpr model v) (elimExpr model p), md⟩
  | ⟨.ReferenceEquals l r, md⟩ => ⟨.ReferenceEquals (elimExpr model l) (elimExpr model r), md⟩
  | ⟨.InstanceCall t c args, md⟩ =>
    ⟨.InstanceCall (elimExpr model t) c (args.attach.map fun ⟨a, _⟩ => elimExpr model a), md⟩
  | ⟨.FieldSelect t f, md⟩ => ⟨.FieldSelect (elimExpr model t) f, md⟩
  | ⟨.PureFieldUpdate t f v, md⟩ => ⟨.PureFieldUpdate (elimExpr model t) f (elimExpr model v), md⟩
  | ⟨.AsType t ty, md⟩ => ⟨.AsType (elimExpr model t) ty, md⟩
  | ⟨.IsType t ty, md⟩ => ⟨.IsType (elimExpr model t) ty, md⟩
  | ⟨.ContractOf ty fn, md⟩ => ⟨.ContractOf ty (elimExpr model fn), md⟩
  | other => other
termination_by expr => expr
decreasing_by all_goals (have := WithMetadata.sizeOf_val_lt ‹_›; term_by_mem)

private def elimBody (model : SemanticModel) (body : Body) : Body :=
  match body with
  | .Transparent b => .Transparent (elimExpr model b)
  | .Opaque posts impl mods =>
    .Opaque (posts.map (elimExpr model)) (impl.map (elimExpr model)) (mods.map (elimExpr model))
  | .Abstract posts => .Abstract (posts.map (elimExpr model))
  | .External => .External

private def elimProcedure (model : SemanticModel) (proc : Procedure) : Procedure :=
  { proc with
    preconditions := proc.preconditions.map (elimExpr model)
    body := elimBody model proc.body
    decreases := proc.decreases.map (elimExpr model)
    invokeOn := proc.invokeOn.map (elimExpr model) }

public def subscriptElim (model : SemanticModel) (program : Program) : Program :=
  -- Always inject the Array composite type. Harmless if unused — just adds
  -- an Array_TypeTag constructor and an Array.$data field to the heap model.
  let arrayComposite : TypeDefinition := .Composite {
    name := mkId arrayCompositeName
    extending := []
    -- $data field uses Seq<int> as placeholder. The element type is erased
    -- (Core's polymorphic type inference handles actual types).
    fields := [{ name := mkId SeqOp.dataField, isMutable := true,
                 type := ⟨.TSeq ⟨.TInt, #[]⟩, #[]⟩ }]
    instanceProcedures := [] }
  let program := { program with types := arrayComposite :: program.types }
  let types' := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures := ct.instanceProcedures.map (elimProcedure model) }
    | other => other
  { program with
    types := types'
    staticProcedures := program.staticProcedures.map (elimProcedure model) }

end Strata.Laurel

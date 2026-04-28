/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelTypes
import Strata.Util.Tactics

/-!
# Subscript Elimination

Type-aware pass that desugars `Subscript` nodes based on the target type:

- `Seq<T>` (immutable): read `s[i]` → `Sequence.select(s, i)`;
  functional update `s[i := v]` → `Sequence.update(s, i, v)`.
- `Array<T>` (mutable, heap-backed): read `a[i]` → `Sequence.select(a#$data, i)`;
  destructive update `a[i] := v` → `a#$data := Sequence.update(a#$data, i, v)`.

Also:
- Rewrites `Array.length(a)` to `Sequence.length(a#$data)`.
- Splits `var a: Array<T> := <init>` (where `init` is a `Seq` literal, not
  another Array) into `var a: Array<T> := new $Array; a#$data := <init>`.
- Conditionally injects the synthetic `$Array` composite (containing a single
  `$data: Seq<T>` field) when the program uses `Array<T>` anywhere.

After this pass, no `Subscript` nodes remain in the program.

Out-of-bounds access is unconstrained by design, matching SMT-LIB semantics.
-/

namespace Strata.Laurel

open Strata

public section

/-! ## Detecting whether `Array<T>` is used anywhere -/

/-- Return `true` if `ty` contains a `TArray` anywhere. -/
partial def containsTArray : HighType → Bool
  | .TArray _ => true
  | .TSet et => containsTArray et.val
  | .TSeq et => containsTArray et.val
  | .TTypedField vt => containsTArray vt.val
  | .TMap kt vt => containsTArray kt.val || containsTArray vt.val
  | .Applied base args => containsTArray base.val || args.any (containsTArray ·.val)
  | .Pure base => containsTArray base.val
  | .Intersection types => types.any (containsTArray ·.val)
  | _ => false

/-- Walk a `StmtExprMd` and return `true` if any embedded `HighType` contains `TArray`. -/
partial def stmtExprUsesTArray (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .LocalVariable _ ty init =>
      containsTArray ty.val || (init.map stmtExprUsesTArray).getD false
  | .Quantifier _ p trig body =>
      containsTArray p.type.val || (trig.map stmtExprUsesTArray).getD false ||
      stmtExprUsesTArray body
  | .AsType t ty => stmtExprUsesTArray t || containsTArray ty.val
  | .IsType t ty => stmtExprUsesTArray t || containsTArray ty.val
  | .Hole _ (some ty) => containsTArray ty.val
  | .IfThenElse c th el =>
      stmtExprUsesTArray c || stmtExprUsesTArray th ||
      (el.map stmtExprUsesTArray).getD false
  | .Block stmts _ => stmts.any stmtExprUsesTArray
  | .While c invs dec body =>
      stmtExprUsesTArray c || invs.any stmtExprUsesTArray ||
      (dec.map stmtExprUsesTArray).getD false || stmtExprUsesTArray body
  | .Return v => (v.map stmtExprUsesTArray).getD false
  | .Assign targets v => targets.any stmtExprUsesTArray || stmtExprUsesTArray v
  | .FieldSelect t _ => stmtExprUsesTArray t
  | .PureFieldUpdate t _ v => stmtExprUsesTArray t || stmtExprUsesTArray v
  | .StaticCall _ args => args.any stmtExprUsesTArray
  | .InstanceCall t _ args => stmtExprUsesTArray t || args.any stmtExprUsesTArray
  | .PrimitiveOp _ args => args.any stmtExprUsesTArray
  | .ReferenceEquals l r => stmtExprUsesTArray l || stmtExprUsesTArray r
  | .Assigned n => stmtExprUsesTArray n
  | .Old v | .Fresh v => stmtExprUsesTArray v
  | .Assert c => stmtExprUsesTArray c.condition
  | .Assume c => stmtExprUsesTArray c
  | .ProveBy v p => stmtExprUsesTArray v || stmtExprUsesTArray p
  | .ContractOf _ f => stmtExprUsesTArray f
  | .Subscript t i u =>
      stmtExprUsesTArray t || stmtExprUsesTArray i ||
      (u.map stmtExprUsesTArray).getD false
  | _ => false

/-- Check whether a parameter's type involves `TArray`. -/
private def parameterUsesTArray (p : Parameter) : Bool := containsTArray p.type.val

/-- Check whether a procedure body involves `TArray`. -/
private def bodyUsesTArray (body : Body) : Bool :=
  match body with
  | .Transparent b => stmtExprUsesTArray b
  | .Opaque posts impl mods =>
      posts.any (stmtExprUsesTArray ·.condition) ||
      (impl.map stmtExprUsesTArray).getD false ||
      mods.any stmtExprUsesTArray
  | .Abstract posts => posts.any (stmtExprUsesTArray ·.condition)
  | .External => false

/-- Check whether a procedure involves `TArray` in signature, contracts, or body. -/
private def procedureUsesTArray (proc : Procedure) : Bool :=
  proc.inputs.any parameterUsesTArray ||
  proc.outputs.any parameterUsesTArray ||
  proc.preconditions.any (stmtExprUsesTArray ·.condition) ||
  (proc.decreases.map stmtExprUsesTArray).getD false ||
  bodyUsesTArray proc.body

/-- Check whether a type definition involves `TArray` in its fields or methods. -/
private def typeDefinitionUsesTArray (td : TypeDefinition) : Bool :=
  match td with
  | .Composite ct =>
      ct.fields.any (fun f => containsTArray f.type.val) ||
      ct.instanceProcedures.any procedureUsesTArray
  | .Constrained ct =>
      containsTArray ct.base.val || stmtExprUsesTArray ct.constraint ||
      stmtExprUsesTArray ct.witness
  | .Datatype dt =>
      dt.constructors.any fun c => c.args.any parameterUsesTArray
  | .Alias ta => containsTArray ta.target.val

/-- Return `true` if the program uses `Array<T>` anywhere. -/
def usesTArray (program : Program) : Bool :=
  program.staticProcedures.any procedureUsesTArray ||
  program.staticFields.any (fun f => containsTArray f.type.val) ||
  program.types.any typeDefinitionUsesTArray ||
  program.constants.any fun c =>
    containsTArray c.type.val || (c.initializer.map stmtExprUsesTArray).getD false

/-! ## Rewrite helpers -/

private def mkCall (name : String) (args : List StmtExprMd) (src : Option FileRange) : StmtExprMd :=
  ⟨.StaticCall (mkId name) args, src⟩

private def mkFieldSelect (target : StmtExprMd) (field : String) (src : Option FileRange) : StmtExprMd :=
  ⟨.FieldSelect target (mkId field), src⟩

/-- Is the expression's computed type an `Array<T>`? -/
private def isArrayType (model : SemanticModel) (target : StmtExprMd) : Bool :=
  match (computeExprType model target).val with
  | .TArray _ => true
  | _ => false

/-- Is the given `HighType` an `Array<T>`? -/
private def isArrayHighType (ty : HighType) : Bool :=
  match ty with
  | .TArray _ => true
  | _ => false

/-! ## Main rewrite

Top-down recursive rewrite. Done top-down (not via `mapStmtExprM`) so that
`.Block` statements can expand 1→N (splitting `var a: Array<T> := <seq>`
initialisations) and `.Assign [.Subscript a i none] v` can be recognised
before the inner `.Subscript` is rewritten into a `Sequence.select` call.
-/

/-- Recursively eliminate Subscript nodes and desugar `Array.length`. -/
def elimExpr (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  let src := expr.source
  match _h : expr.val with
  | .Subscript target index none =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    if isArrayType model target then
      mkCall SeqOp.select [mkFieldSelect target' SeqOp.dataField src, index'] src
    else
      mkCall SeqOp.select [target', index'] src
  | .Subscript target index (some value) =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    let value' := elimExpr model value
    if isArrayType model target then
      -- `a[i := v]` on Array<T>: not supported (the `ValidateSubscriptUsage`
      -- pass has already surfaced a diagnostic for this misuse).
      -- Desugar the read-side to keep downstream typecheck simple.
      let data := mkFieldSelect target' SeqOp.dataField src
      mkCall SeqOp.update [data, index', value'] src
    else
      mkCall SeqOp.update [target', index', value'] src
  | .Block stmts label =>
    -- Top-down: first recurse on each child stmt, then post-process the list
    -- to expand `var a: Array<T> := <seq-init>` into 2 statements.
    let stmts' := stmts.attach.map fun ⟨s, _⟩ => elimExpr model s
    let expanded := stmts'.flatMap fun s =>
      match s.val with
      | .LocalVariable n ty (some initExpr) =>
        -- `initExpr` at this point is already recursively elim'd.
        if isArrayHighType ty.val && !isArrayType model initExpr then
          [⟨.LocalVariable n ty (some ⟨.New (mkId arrayCompositeName), s.source⟩), s.source⟩,
           ⟨.Assign [mkFieldSelect ⟨.Identifier n, s.source⟩ SeqOp.dataField s.source] initExpr,
            s.source⟩]
        else [s]
      | _ => [s]
    ⟨.Block expanded label, src⟩
  | .Assign [⟨.Subscript target index none, ssrc⟩] value =>
    -- `target[index] := value`: on Array<T>, rewrite to `target#$data := Sequence.update(...)`.
    -- On Seq<T> this is a user error; preserve shape so validator can emit a diagnostic.
    let target' := elimExpr model target
    let index' := elimExpr model index
    let value' := elimExpr model value
    if isArrayType model target then
      let data := mkFieldSelect target' SeqOp.dataField ssrc
      ⟨.Assign [mkFieldSelect target' SeqOp.dataField ssrc]
        (mkCall SeqOp.update [data, index', value'] ssrc), src⟩
    else
      -- Seq is immutable — leave as an Assign onto a Sequence.select, which
      -- downstream will reject. Validator (commit 2) emits the helpful message.
      ⟨.Assign [mkCall SeqOp.select [target', index'] ssrc] value', src⟩
  | .Assign targets value =>
    ⟨.Assign (targets.attach.map fun ⟨t, _⟩ => elimExpr model t) (elimExpr model value), src⟩
  | .StaticCall callee args =>
    let args' := args.attach.map fun ⟨a, _⟩ => elimExpr model a
    -- `Array.length(a)` → `Sequence.length(a#$data)`
    if callee.text == arrayLengthName then
      match args' with
      | [a] => mkCall SeqOp.length [mkFieldSelect a SeqOp.dataField src] src
      | _ =>
        -- Wrong arity — leave alone (validator/resolver will flag).
        ⟨.StaticCall callee args', src⟩
    else
      ⟨.StaticCall callee args', src⟩
  | .IfThenElse c t e =>
    ⟨.IfThenElse (elimExpr model c) (elimExpr model t)
      (e.attach.map fun ⟨x, _⟩ => elimExpr model x), src⟩
  | .LocalVariable n ty init =>
    ⟨.LocalVariable n ty (init.attach.map fun ⟨i, _⟩ => elimExpr model i), src⟩
  | .While c invs dec body =>
    ⟨.While (elimExpr model c) (invs.attach.map fun ⟨i, _⟩ => elimExpr model i)
      (dec.attach.map fun ⟨d, _⟩ => elimExpr model d) (elimExpr model body), src⟩
  | .Return v => ⟨.Return (v.attach.map fun ⟨x, _⟩ => elimExpr model x), src⟩
  | .PrimitiveOp op args =>
    ⟨.PrimitiveOp op (args.attach.map fun ⟨a, _⟩ => elimExpr model a), src⟩
  | .Quantifier mode p trig body =>
    ⟨.Quantifier mode p (trig.attach.map fun ⟨t, _⟩ => elimExpr model t) (elimExpr model body), src⟩
  | .Assert c => ⟨.Assert { c with condition := elimExpr model c.condition }, src⟩
  | .Assume c => ⟨.Assume (elimExpr model c), src⟩
  | .Old v => ⟨.Old (elimExpr model v), src⟩
  | .Fresh v => ⟨.Fresh (elimExpr model v), src⟩
  | .Assigned v => ⟨.Assigned (elimExpr model v), src⟩
  | .ProveBy v p => ⟨.ProveBy (elimExpr model v) (elimExpr model p), src⟩
  | .ReferenceEquals l r => ⟨.ReferenceEquals (elimExpr model l) (elimExpr model r), src⟩
  | .InstanceCall t c args =>
    ⟨.InstanceCall (elimExpr model t) c (args.attach.map fun ⟨a, _⟩ => elimExpr model a), src⟩
  | .FieldSelect t f => ⟨.FieldSelect (elimExpr model t) f, src⟩
  | .PureFieldUpdate t f v => ⟨.PureFieldUpdate (elimExpr model t) f (elimExpr model v), src⟩
  | .AsType t ty => ⟨.AsType (elimExpr model t) ty, src⟩
  | .IsType t ty => ⟨.IsType (elimExpr model t) ty, src⟩
  | .ContractOf ty fn => ⟨.ContractOf ty (elimExpr model fn), src⟩
  | _ => expr
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals omega

private def elimBody (model : SemanticModel) (body : Body) : Body :=
  match body with
  | .Transparent b => .Transparent (elimExpr model b)
  | .Opaque posts impl mods =>
    .Opaque (posts.map (·.mapCondition (elimExpr model)))
            (impl.map (elimExpr model)) (mods.map (elimExpr model))
  | .Abstract posts => .Abstract (posts.map (·.mapCondition (elimExpr model)))
  | .External => .External

private def elimProcedure (model : SemanticModel) (proc : Procedure) : Procedure :=
  { proc with
    preconditions := proc.preconditions.map (·.mapCondition (elimExpr model))
    body := elimBody model proc.body
    decreases := proc.decreases.map (elimExpr model)
    invokeOn := proc.invokeOn.map (elimExpr model) }

/-- The synthetic `$Array` composite, containing a single `$data: Seq<int>`
    field.

    The element type is hardcoded as `int`: `Array<T>` with `T ≠ int` is
    currently rejected by `ValidateSubscriptUsage` (diagnostic 4), so in
    practice every program reaching this pass uses only `Array<int>`.
    Relaxing that validator would require deriving the element type here
    (or switching to a per-element-type composite, similar to the
    `BoxSeq_{tag}` constructor pattern in HeapParameterization). -/
private def arrayCompositeDef : TypeDefinition :=
  .Composite {
    name := mkId arrayCompositeName
    extending := []
    fields := [{ name := mkId SeqOp.dataField, isMutable := true,
                 type := ⟨.TSeq ⟨.TInt, none⟩, none⟩ }]
    instanceProcedures := [] }

/-- Eliminate `Subscript` nodes and desugar `Array.length` across a program.
    Conditionally injects the `$Array` synthetic composite when the program
    uses `Array<T>` anywhere. -/
public def subscriptElim (_model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  -- The `$Array` composite is only needed when the program mentions `Array<T>`.
  let program :=
    if usesTArray program then
      { program with types := arrayCompositeDef :: program.types }
    else program
  -- Build a fresh resolution model so that `computeExprType` sees the injected
  -- `$Array` composite. The pipeline's `needsResolves := true` flag will take
  -- care of re-resolving after this pass; but we need the local type lookups
  -- below to already see the new type. We rely on the caller to run `resolve`
  -- again afterwards (driven by `LaurelPass.needsResolves`).
  let model := (resolve program).model
  let types' := program.types.map fun td =>
    match td with
    | .Composite ct =>
      .Composite { ct with instanceProcedures := ct.instanceProcedures.map (elimProcedure model) }
    | other => other
  let program' := { program with
    types := types'
    staticProcedures := program.staticProcedures.map (elimProcedure model) }
  (program', [])

end -- public section
end Strata.Laurel

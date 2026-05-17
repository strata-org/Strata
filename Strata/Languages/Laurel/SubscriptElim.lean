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
- Rewrites `Sequence.fromArray(a)` to `a#$data` (a snapshot read of
  the array's current Seq contents).
- Splits `var a: Array<T> := <init>` (where `init` is a `Seq` literal, not
  another Array) into `var a: Array<T> := new $Array; a#$data := <init>`.
- Conditionally injects the synthetic `$Array` composite (containing a single
  `$data: Seq<T>` field) when the program uses `Array<T>` anywhere.

After this pass, no `Subscript` nodes remain in the program.

Out-of-bounds access produces a verification obligation at the call site:
the Core-level bounds preconditions on `Sequence.select` / `update` / `take` /
`drop` propagate through `PrecondElim`, and the SMT solver is responsible for
discharging them.
-/

namespace Strata.Laurel

open Strata

public section

/-! ## Detecting whether `Array<T>` is used anywhere -/

/-- Return `true` if `ty` contains a `TArray` anywhere.

    Each `HighType` constructor gets its own arm so that adding a new
    constructor produces a missing-cases error rather than silently
    falling through. `Unknown` and `MultiValuedExpr` are explicitly
    `false`: the former is an unresolved-type marker that aborts
    compilation before we'd care whether it contains a TArray, and the
    latter is an internal-only computeExprType output that never carries
    user-declared types. -/
def containsTArray (ty : HighType) : Bool := match _hht : ty with
  | .TArray _ => true
  | .TSet et => containsTArray et.val
  | .TSeq et => containsTArray et.val
  | .TTypedField vt => containsTArray vt.val
  | .TMap kt vt => containsTArray kt.val || containsTArray vt.val
  | .Applied base args => containsTArray base.val || args.attach.any (fun ⟨x, _⟩ => containsTArray x.val)
  | .Pure base => containsTArray base.val
  | .Intersection types => types.attach.any (fun ⟨x, _⟩ => containsTArray x.val)
  | .Unknown | .MultiValuedExpr _ => false
  | .TVoid | .TBool | .TInt | .TFloat64 | .TReal | .TString | .THeap
  | .TBv _ | .UserDefined _ | .TCore _ => false
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  -- Single-child cases.
  all_goals (try (
    have := AstNode.sizeOf_val_lt (‹AstNode HighType› : AstNode HighType)
    omega))
  -- Two-child cases (TMap): need haves for both kt and vt. Use the of_eq
  -- lemmas with the match hypothesis _hht.
  all_goals (try (
    have hk := HighType.sizeOf_tmap_kt_val_lt_of_eq _hht
    have hv := HighType.sizeOf_tmap_vt_val_lt_of_eq _hht
    subst _hht; simp at hk hv; omega))
  -- Applied base case: similar.
  all_goals (try (
    have := HighType.sizeOf_applied_base_val_lt_of_eq _hht
    subst _hht; simp_all; omega))
  -- args.any / types.any: x ∈ list (provided by .attach), recurse on x.val.
  all_goals (
    have mem_h : (‹AstNode HighType› : AstNode HighType) ∈ (‹List (AstNode HighType)› : List (AstNode HighType)) := ‹_›
    have := List.sizeOf_lt_of_mem mem_h
    have := AstNode.sizeOf_val_lt (‹AstNode HighType› : AstNode HighType)
    omega)

/-- Walk a `StmtExprMd` and return `true` if any embedded `HighType` contains `TArray`. -/
def stmtExprUsesTArray (expr : StmtExprMd) : Bool :=
  match _h : expr.val with
  | .Var (.Declare p) => containsTArray p.type.val
  | .Var (.Field t _) => stmtExprUsesTArray t
  | .Var (.Local _) => false
  | .Quantifier _ p trig body =>
      containsTArray p.type.val ||
      (trig.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)) ||
      stmtExprUsesTArray body
  | .AsType t ty => stmtExprUsesTArray t || containsTArray ty.val
  | .IsType t ty => stmtExprUsesTArray t || containsTArray ty.val
  | .Hole _ (some ty) => containsTArray ty.val
  | .IfThenElse c th el =>
      stmtExprUsesTArray c || stmtExprUsesTArray th ||
      (el.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x))
  | .Block stmts _ => stmts.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)
  | .While c invs dec body =>
      stmtExprUsesTArray c ||
      invs.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x) ||
      (dec.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)) ||
      stmtExprUsesTArray body
  | .Return v => v.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)
  | .Assign targets v =>
      targets.attach.any (fun ⟨t, _⟩ => match _htv : t.val with
        | .Declare p => containsTArray p.type.val
        | .Field target _ => stmtExprUsesTArray target
        | .Local _ => false)
      || stmtExprUsesTArray v
  | .PureFieldUpdate t _ v => stmtExprUsesTArray t || stmtExprUsesTArray v
  | .StaticCall _ args => args.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)
  | .InstanceCall t _ args =>
      stmtExprUsesTArray t || args.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)
  | .PrimitiveOp _ args => args.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x)
  | .ReferenceEquals l r => stmtExprUsesTArray l || stmtExprUsesTArray r
  | .Assigned n => stmtExprUsesTArray n
  | .Old v | .Fresh v => stmtExprUsesTArray v
  | .Assert c => stmtExprUsesTArray c.condition
  | .Assume c => stmtExprUsesTArray c
  | .ProveBy v p => stmtExprUsesTArray v || stmtExprUsesTArray p
  | .ContractOf _ f => stmtExprUsesTArray f
  | .Subscript t i u =>
      stmtExprUsesTArray t || stmtExprUsesTArray i ||
      (u.attach.any (fun ⟨x, _⟩ => stmtExprUsesTArray x))
  | _ => false
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  -- Assign-target list, .Field inner
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := Variable.sizeOf_field_target_lt_of_eq _htv
    simp_all; omega))
  -- Top-level .Subscript via _h (target/index/value children)
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _h; omega))

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

/-- Build a `Variable.Field` read as a StmtExpr (expression position). -/
private def mkFieldExpr (target : StmtExprMd) (field : String) (src : Option FileRange) : StmtExprMd :=
  ⟨.Var (.Field target (mkId field)), src⟩

/-- Build a `Variable.Field` as an Assign target (target position). -/
private def mkFieldVariable (target : StmtExprMd) (field : String) (src : Option FileRange) : VariableMd :=
  ⟨.Field target (mkId field), src⟩

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

/-- Build the destructive-update statement for `a[i] := v` on an `Array<T>`:
    `a#$data := Sequence.update(a#$data, i, v)`.

    The arguments are *already-rewritten* children so this helper does not
    recurse — it simply constructs the result shape used by the four
    statement-position dispatch sites in `elimExpr`. -/
private def mkArrayUpdateStmt (target' index' value' : StmtExprMd)
    (src : Option FileRange) : StmtExprMd :=
  let data := mkFieldExpr target' arrayDataField src
  ⟨.Assign [mkFieldVariable target' arrayDataField src]
      (mkCall SeqOp.update [data, index', value'] src), src⟩

/-- Build the two-statement split for `var a: Array<T> := <init>` where
    `init` is a non-Array (i.e. needs the synthetic `$Array` allocation):
    `var a: Array<T> := new $Array; a#$data := <init>`.

    The arguments are *already-rewritten* (`initExpr'` is the rewritten
    initialiser); this helper does not recurse. Used by the four
    statement-position dispatch sites in `elimExpr`. -/
private def mkArrayInitSplit (param : Parameter) (dsrc : Option FileRange)
    (initExpr' : StmtExprMd) (src : Option FileRange) : List StmtExprMd :=
  [⟨.Assign [⟨.Declare param, dsrc⟩] ⟨.New (mkId arrayCompositeName), src⟩, src⟩,
   ⟨.Assign [mkFieldVariable ⟨.Var (.Local param.name), src⟩ arrayDataField src]
      initExpr', src⟩]

/-! ## Main rewrite

Top-down recursive rewrite. Done top-down (not via `mapStmtExprM`) so that
`.Block` statements can expand 1→N (splitting `var a: Array<T> := <seq>`
initialisations) and `.Assign [.Subscript a i none] v` can be recognised
before the inner `.Subscript` is rewritten into a `Sequence.select` call.
-/

/-- Recursively eliminate Subscript nodes and desugar `Array.length`.
    Statement-position handling (for `.Subscript t i (some v)` and
    `.Assign [.Declare _] init` shapes that need 1→N expansion or Array-
    specific rewriting) is inlined at the `.Block`, `.IfThenElse`, and
    `.While` arms. -/
def elimExpr (model : SemanticModel) (expr : StmtExprMd) : StmtExprMd :=
  let src := expr.source
  match _h : expr.val with
  | .Subscript target index none =>
    let target' := elimExpr model target
    let index' := elimExpr model index
    if isArrayType model target then
      mkCall SeqOp.select [mkFieldExpr target' arrayDataField src, index'] src
    else
      mkCall SeqOp.select [target', index'] src
  | .Subscript target index (some value) =>
    -- Expression-position update: `s := s[i := v]`. Desugars to Sequence.update.
    -- Statement-position `a[i] := v` (same AST shape) is intercepted earlier
    -- by `elimStmt` — at every statement-position container — so it never
    -- reaches this arm.
    let target' := elimExpr model target
    let index' := elimExpr model index
    let value' := elimExpr model value
    if isArrayType model target then
      -- `a[i := v]` on Array<T>: not supported (the `ValidateSubscriptUsage`
      -- pass has already surfaced a diagnostic for this misuse).
      -- Desugar the read-side to keep downstream typecheck simple.
      let data := mkFieldExpr target' arrayDataField src
      mkCall SeqOp.update [data, index', value'] src
    else
      mkCall SeqOp.update [target', index', value'] src
  | .Block stmts label =>
    -- Statement-position handling inlined for termination. Each `s ∈ stmts`:
    --   * `.Subscript t i (some v)`: destructive update. Array → field-update
    --     statement; Seq → empty block (validator has already reported).
    --   * `.Assign [⟨.Declare p, _⟩] init` with Array p and non-Array init:
    --     split into `var a: Array := new $Array; a.$data := init`.
    --   * otherwise: walk via elimExpr.
    ⟨.Block (stmts.attach.flatMap fun ⟨s, _⟩ => match _hsub : s.val with
      | .Subscript target index (some value) =>
        if isArrayType model target then
          [mkArrayUpdateStmt (elimExpr model target) (elimExpr model index)
                             (elimExpr model value) s.source]
        else
          -- Seq<T>: user error. COUPLING: `ValidateSubscriptUsage` MUST
          -- have reported a `msgSeqDestructiveUpdate` diagnostic first.
          [⟨.Block [] none, s.source⟩]
      | .Assign [⟨.Declare param, dsrc⟩] initExpr =>
        let initExpr' := elimExpr model initExpr
        if isArrayHighType param.type.val && !isArrayType model initExpr then
          mkArrayInitSplit param dsrc initExpr' s.source
        else
          [⟨.Assign [⟨.Declare param, dsrc⟩] initExpr', s.source⟩]
      | _ => [elimExpr model s]) label, src⟩
  | .Assign targets value =>
    -- Assign targets are VariableMd; we only need to recurse into .Field sub-expressions.
    let targets' := targets.attach.map fun ⟨t, _⟩ => match _htv : t.val with
      | .Field subTarget fieldName => (⟨.Field (elimExpr model subTarget) fieldName, t.source⟩ : VariableMd)
      | .Local _ | .Declare _ => t
    ⟨.Assign targets' (elimExpr model value), src⟩
  | .StaticCall callee args =>
    let args' := args.attach.map fun ⟨a, _⟩ => elimExpr model a
    -- `Array.length(a)` → `Sequence.length(a#$data)` — only when `a` is an Array<T>.
    -- When the argument is not an Array (a user error caught by the validator),
    -- replace the call with `0` so downstream Core type checking doesn't emit
    -- confusing unification errors on top of the validator's helpful message.
    if callee.text == arrayLengthName then
      match args' with
      | [a] =>
        if isArrayType model a then
          mkCall SeqOp.length [mkFieldExpr a arrayDataField src] src
        else
          ⟨.LiteralInt 0, src⟩
      | _ =>
        -- Wrong arity — leave alone (validator/resolver will flag).
        ⟨.StaticCall callee args', src⟩
    else if callee.text == sequenceFromArrayName then
      -- `Sequence.fromArray(a)` → `a#$data` — only when `a` is an Array<T>.
      -- When the argument is not an Array the validator has flagged it; we
      -- rewrite defensively to `Sequence.empty()` so Core type checking
      -- does not add confusing follow-on errors.
      match args' with
      | [a] =>
        if isArrayType model a then
          mkFieldExpr a arrayDataField src
        else
          mkCall SeqOp.empty [] src
      | _ =>
        ⟨.StaticCall callee args', src⟩
    else
      ⟨.StaticCall callee args', src⟩
  | .IfThenElse c t e =>
    -- Statement-position branches: handle `.Subscript t i (some v)` and
    -- `.Assign [.Declare _] init` shapes inline, same pattern as the
    -- `.Block` arm but as a single StmtExprMd (wrapping multi-stmt in Block).
    let t' : StmtExprMd := match _hsub : t.val with
      | .Subscript target index (some value) =>
        if isArrayType model target then
          mkArrayUpdateStmt (elimExpr model target) (elimExpr model index)
                            (elimExpr model value) t.source
        else
          ⟨.Block [] none, t.source⟩
      | .Assign [⟨.Declare param, dsrc⟩] initExpr =>
        let initExpr' := elimExpr model initExpr
        if isArrayHighType param.type.val && !isArrayType model initExpr then
          ⟨.Block (mkArrayInitSplit param dsrc initExpr' t.source) none, t.source⟩
        else
          ⟨.Assign [⟨.Declare param, dsrc⟩] initExpr', t.source⟩
      | _ => elimExpr model t
    let e' : Option StmtExprMd := e.attach.map fun ⟨y, _⟩ => match _hsub : y.val with
      | .Subscript target index (some value) =>
        if isArrayType model target then
          mkArrayUpdateStmt (elimExpr model target) (elimExpr model index)
                            (elimExpr model value) y.source
        else
          ⟨.Block [] none, y.source⟩
      | .Assign [⟨.Declare param, dsrc⟩] initExpr =>
        let initExpr' := elimExpr model initExpr
        if isArrayHighType param.type.val && !isArrayType model initExpr then
          ⟨.Block (mkArrayInitSplit param dsrc initExpr' y.source) none, y.source⟩
        else
          ⟨.Assign [⟨.Declare param, dsrc⟩] initExpr', y.source⟩
      | _ => elimExpr model y
    ⟨.IfThenElse (elimExpr model c) t' e', src⟩
  | .While c invs dec body =>
    let body' : StmtExprMd := match _hsub : body.val with
      | .Subscript target index (some value) =>
        if isArrayType model target then
          mkArrayUpdateStmt (elimExpr model target) (elimExpr model index)
                            (elimExpr model value) body.source
        else
          ⟨.Block [] none, body.source⟩
      | .Assign [⟨.Declare param, dsrc⟩] initExpr =>
        let initExpr' := elimExpr model initExpr
        if isArrayHighType param.type.val && !isArrayType model initExpr then
          ⟨.Block (mkArrayInitSplit param dsrc initExpr' body.source) none, body.source⟩
        else
          ⟨.Assign [⟨.Declare param, dsrc⟩] initExpr', body.source⟩
      | _ => elimExpr model body
    ⟨.While (elimExpr model c) (invs.attach.map fun ⟨i, _⟩ => elimExpr model i)
      (dec.attach.map fun ⟨d, _⟩ => elimExpr model d) body', src⟩
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
  | .Var (.Field t f) => ⟨.Var (.Field (elimExpr model t) f), src⟩
  | .PureFieldUpdate t f v => ⟨.PureFieldUpdate (elimExpr model t) f (elimExpr model v), src⟩
  | .AsType t ty => ⟨.AsType (elimExpr model t) ty, src⟩
  | .IsType t ty => ⟨.IsType (elimExpr model t) ty, src⟩
  | .ContractOf ty fn => ⟨.ContractOf ty (elimExpr model fn), src⟩
  -- Leaves: no StmtExprMd children that need eliminating.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise this walker will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => expr
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  -- For subTarget inside .Assign target list .Field — uses the match
  -- hypothesis _htv : t.val = Variable.Field ...
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := Variable.sizeOf_field_target_lt_of_eq _htv
    simp_all; omega))
  -- For target/index/value inside .Subscript at the top level (expression
  -- position) — uses the match hypothesis _h : expr.val = .Subscript ...
  all_goals (try (have := StmtExpr.sizeOf_subscript_target_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_index_lt_of_eq _h; omega))
  all_goals (try (have := StmtExpr.sizeOf_subscript_value_lt_of_eq _h; omega))
  -- For target/index/value inside .Subscript at statement position (inside
  -- a Block/If/While stmt) — uses the inner match hypothesis _hsub.
  -- Two sub-cases:
  --   Block: `s ∈ stmts` needs List.sizeOf_lt_of_mem.
  --   If/While branch: direct field, no list membership.
  -- We try both formulations.
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_target_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := StmtExpr.sizeOf_subscript_target_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_index_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := StmtExpr.sizeOf_subscript_index_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_subscript_value_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := StmtExpr.sizeOf_subscript_value_lt_of_eq _hsub
    simp_all; omega))
  -- For initExpr inside .Assign [.Declare _] initExpr in Block / branch.
  all_goals (try (
    have := List.sizeOf_lt_of_mem ‹_›
    have := StmtExpr.sizeOf_assign_value_lt_of_eq _hsub
    simp_all; omega))
  all_goals (try (
    have := StmtExpr.sizeOf_assign_value_lt_of_eq _hsub
    simp_all; omega))

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
    fields := [{ name := mkId arrayDataField, isMutable := true,
                 type := ⟨.TSeq ⟨.TInt, none⟩, none⟩ }]
    instanceProcedures := [] }

/-- Eliminate `Subscript` nodes and desugar `Array.length` across a program.
    Conditionally injects the `$Array` synthetic composite when the program
    uses `Array<T>` anywhere.

    The `_model` parameter is accepted to satisfy `LaurelPass.run`'s
    `Program → SemanticModel → ...` signature but is intentionally unused:
    the caller's model predates our `$Array` injection, and `elimProcedure`'s
    `computeExprType` queries need a model that includes the synthetic
    composite's `$data` field. We therefore rebuild the model via `resolve`
    below. The pipeline's `needsResolves := true` flag re-resolves after
    this pass for all downstream consumers. -/
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
    staticProcedures := program.staticProcedures.map (elimProcedure model)
    constants := program.constants.map fun c =>
      { c with initializer := c.initializer.map (elimExpr model) } }
  (program', [])

end -- public section
end Strata.Laurel

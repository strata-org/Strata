/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.GlobalVarAnalysis
import StrataLaurel.Implementation.HeapParameterization
import Strata.Util.Tactics

/-!
# Constrained Type Elimination

A Laurel-to-Laurel pass that eliminates constrained types by:
1. Generating a constraint procedure per constrained type (e.g. `nat$constraint(x: int): bool`)
2. Adding `requires constraintProc(param)` for constrained-typed inputs
3. Adding `ensures constraintProc(result)` for constrained-typed outputs
4. Inserting `assert constraintProc(var)` for local variable init and reassignment
5. Assuming the constraint for uninitialized constrained-typed variables (havoc + assume) and holes
6. Adding a synthetic witness-validation procedure per constrained type
7. Injecting constraint procedure calls into quantifier bodies (`forall` → `implies`, `exists` → `and`)
8. Resolving all constrained type references to their base types
-/

namespace Strata.Laurel

open Strata

abbrev ConstrainedTypeMap := Std.HashMap String ConstrainedType

def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Constrained ct => m.insert ct.name.text ct | _ => m

partial def resolveBaseType (ptMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  -- Resolve every constrained `UserDefined` type to its base, recursing through
  -- all component types via the generic `HighType.mapType` traversal.
  ty.mapType fun
    | .UserDefined name => match ptMap.get? name.text with
      | some ct => resolveBaseType ptMap ct.base.val
      | none => .UserDefined name
    | t => t

def resolveType (ptMap : ConstrainedTypeMap) (ty : HighTypeMd) : HighTypeMd :=
  ⟨resolveBaseType ptMap ty.val, ty.source⟩

abbrev DatatypeMap := Std.HashMap String DatatypeDefinition

def buildDatatypeMap (types : List TypeDefinition) : DatatypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with | .Datatype dt => m.insert dt.name.text dt | _ => m

structure CteCtx where
  ptMap : ConstrainedTypeMap
  dtMap : DatatypeMap := {}
  mixed : Std.HashSet String := {}
  aliased : Std.HashSet String := {}

private def conjoin (src : FileRange) : List StmtExprMd → Option StmtExprMd
  | [] => none
  | e :: es => some (es.foldl (fun acc x => ⟨.StaticCall (mkId Operation.And.procName) [acc, x] [], src⟩) e)

partial def constraintAtoms (cx : CteCtx) (ty : HighType) (ref : StmtExprMd)
    (src : FileRange) : List (Bool × StmtExprMd) :=
  match ty with
  | .UserDefined name =>
    match cx.ptMap.get? name.text with
    | some ct => [(ct.free, ⟨.StaticCall (mkId s!"{name.text}$constraint") [ref] [], src⟩)]
    | none => []
  | .Applied base args =>
    match base.val with
    | .UserDefined dtName =>
      match cx.dtMap.get? dtName.text with
      | some dt =>
        if !dt.constrainedArgsSupported cx.dtMap.get? || dt.typeArgs.length != args.length then [] else
        let subst : Std.HashMap String HighTypeMd :=
          (dt.typeArgs.zip args).foldl (fun m (p, a) => m.insert p.text a) {}
        dt.constructors.flatMap fun ctor =>
          let tester : StmtExprMd := ⟨.StaticCall (mkId (dt.testerName ctor)) [ref] [], src⟩
          let generic := ctor.args.filter fun p =>
            p.type.val.mentionedNames.any fun n => dt.typeArgs.any (·.text == n)
          let inner := generic.flatMap fun p =>
            let read : StmtExprMd := ⟨.StaticCall (mkId (dt.unsafeDestructorName p)) [ref] [], src⟩
            constraintAtoms cx (substTypeVars subst p.type).val read src
          [false, true].filterMap fun free =>
            (conjoin src ((inner.filter (·.1 == free)).map (·.2))).map fun body =>
              (free, ⟨.StaticCall (mkId Operation.Implies.procName) [tester, body] [], src⟩)
      | none => []
    | _ => []
  | _ => []

def constraintCallForExpr (cx : CteCtx) (ty : HighType)
    (ref : StmtExprMd) (src : FileRange) (only : Option Bool := none) : Option StmtExprMd :=
  conjoin src ((constraintAtoms cx ty ref src).filter (fun a => only.all (· == a.1)) |>.map (·.2))

def constraintCallFor (cx : CteCtx) (ty : HighType)
    (varName : Identifier) (src : FileRange) (only : Option Bool := none) : Option StmtExprMd :=
  constraintCallForExpr cx ty ⟨.Var (.Local varName), src⟩ src only

def conditionsForExpr (cx : CteCtx) (ty : HighType) (ref : StmtExprMd)
    (src : FileRange) : List Condition :=
  (constraintCallForExpr cx ty ref src (only := some false)).toList.map (fun c => { condition := c }) ++
  (constraintCallForExpr cx ty ref src (only := some true)).toList.map
    (fun c => { condition := c, mode := .Assume })

def conditionsFor (cx : CteCtx) (ty : HighType) (varName : Identifier)
    (src : FileRange) : List Condition :=
  conditionsForExpr cx ty ⟨.Var (.Local varName), src⟩ src

/-- Generate a constraint procedure for a constrained type.
    For nested types, the procedure calls the parent's constraint procedure. -/
def mkConstraintProc (ptMap : ConstrainedTypeMap) (ct : ConstrainedType) : Procedure :=
  let baseType := resolveType ptMap ct.base
  let src := ct.constraint.source
  let bodyExpr: StmtExprMd := match ct.base.val with
    | .UserDefined parent =>
      if ptMap.contains parent.text then
        let paramId := { ct.valueName with uniqueId := none }
        let paramRef : StmtExprMd :=
          { val := .Var (.Local paramId), source := src }
        let parentCall : StmtExprMd :=
          { val := .StaticCall (mkId s!"{parent.text}$constraint") [paramRef] [], source := src }
        { val := .StaticCall (mkId Operation.And.procName) [ct.constraint, parentCall] [], source := src }
      else ct.constraint
    | _ => ct.constraint
  { name := mkId s!"{ct.name.text}$constraint"
    inputs := [{ name := ct.valueName, type := baseType }]
    outputs := [{ name := mkId resultOutputName, type := { val := .TBool, source := src } }]
    body := .Transparent { val := .Block [
      { val := .Assign [{ val := .Local (mkId resultOutputName), source := src }] bodyExpr, source := src },
      { val := .Return [], source := src }] none [] none, source := src }
    decreases := none
    preconditions := [] }

def resolveVariable (ptMap : ConstrainedTypeMap) (v : VariableMd) : VariableMd :=
  match v.val with
  | .Declare param => ⟨.Declare { param with type := param.type.map (resolveType ptMap ·) }, v.source⟩
  | _ => v

/-- Resolve constrained types in type positions and inject constraint calls into quantifier bodies.
    Recursion into StmtExprMd children is handled by `mapStmtExpr`. -/
def resolveExprNode (cx : CteCtx) (expr : StmtExprMd) : StmtExprMd :=
  let source := expr.source

  match expr.val with
  | .Assign targets value =>
    ⟨.Assign (targets.map (resolveVariable cx.ptMap)) value, source⟩
  | .Var (.Declare param) =>
    ⟨.Var (.Declare { param with type := param.type.map (resolveType cx.ptMap ·) }), source⟩
  | .Quantifier mode param trigger body =>
    let param' := { param with type := resolveType cx.ptMap param.type }
    -- With bottom-up traversal, `body` is already recursed into. The newly
    -- created operator call won't be visited again, which is safe because
    -- `c` (from `constraintCallFor`) is a StaticCall with Identifier leaves
    -- that don't need further resolution.
    let combiner := match mode with | .Forall => Operation.Implies | .Exists => Operation.And
    let injected := match constraintCallFor cx param.type.val param.name (src := source) with
      | some c => ⟨.StaticCall (mkId combiner.procName) [c, body] [], source⟩
      | none => body
    ⟨.Quantifier mode param' trigger injected, source⟩
  | .AsType t ty =>
    match ty.val with
    | .UserDefined name =>
      if cx.ptMap.contains name.text then ⟨.StaticCall (downcastProcName name) [t] [], source⟩
      else ⟨.AsType t (resolveType cx.ptMap ty), source⟩
    | _ => ⟨.AsType t (resolveType cx.ptMap ty), source⟩
  | .IsType t ty =>
    match constraintCallForExpr cx ty.val t source with
    | some c => c
    | none => ⟨.IsType t (resolveType cx.ptMap ty), source⟩
  -- `Resolution.Check.holeNone` records the expected type on an untyped hole in check
  -- position. Resolve that annotation together with the surrounding declaration so no
  -- constrained type remains after this pass. This applies to both hole kinds.
  | .Hole det ty => ⟨.Hole det (ty.map (resolveType cx.ptMap ·)), source⟩
  | _ => expr

/-- Per-node constrained-type elimination, applied bottom-up (with flattening)
    by `mapStmtExprFlattenM`. `resultUsed` is `true` when the node occupies a
    value position.

    - Uninitialized constrained declaration `var x: T;` → assume its constraint.
    - Assignment to constrained target(s) → emit the assignment followed by an
      `assert T$constraint(<read-back>)` per constrained target. The constraint
      is checked on a *read-back* of the target rather than on the RHS, so the
      RHS is evaluated exactly once. In value position the read-back is also
      appended as the final statement, so the resulting value-block evaluates to
      the assigned value (this covers expression-position assignments such as
      `y := (x := -1) + 1`); in statement position it is omitted.
    - A hole of a constrained type in a value position → a fresh local bound to the hole,
      with the constraint assumed on it as for an uninitialized declaration. A copy of the
      hole would not do: each occurrence of a hole is its own value.
    - All other nodes are returned unchanged; the traversal handles recursion. -/
def elimNode (cx : CteCtx) (model : SemanticModel)
    (resultUsed : Bool) (node : StmtExprMd) : StateM Nat (List StmtExprMd) := do
  let source := node.source
  match node.val with
  | .Var (.Declare ⟨name, some ty⟩) =>
    let check := (constraintCallFor cx ty.val name (src := source) (only := some false)).toList.map
      fun c => ⟨.Assume c, source⟩
    return [node] ++ check
  | .Assign targets _value =>
    let asserts: List StmtExprMd := targets.filterMap (fun target =>
      let ref : StmtExprMd := VariableMd.toReadbackExpr target
      (constraintCallForExpr cx (computeExprType model ref).val ref (src := source) (only := some false)).map
        (⟨.Assert · none, source⟩))
    let suffix := match targets with
      | [single] => if resultUsed then [VariableMd.toReadbackExpr single] else []
      | _ => []
    return [node] ++ asserts ++ suffix
  | .Var (.Field _ fieldName) =>
    -- Constrained field read → `{ assume T$constraint(read); read }`.
    -- `elimCompositeType` lowers the declared type to its base without restating the
    -- predicate on READ, while the range OBLIGATION still lands at the destination
    -- (`ensures` on a constrained output, `assert` on a constrained local) --
    -- unprovable rather than imprecise: without this assume, `return self#x` on an
    -- `int32` field cannot discharge its own `int32` postcondition.
    --
    -- ASSUMED, not asserted, resting on the DECLARED type as a standing fact about
    -- every value read out of the field (as `.Declare` above does for an
    -- uninitialized local), NOT on write coverage: a fresh composite's fields are
    -- never assigned, yet a read is assumed in range (measured). Writes are covered
    -- anyway -- `.Assign` checks each, and `IncrDecr` / `CompoundAssign` lower to
    -- `.Assign` first (LaurelCompilationPipeline runs
    -- eliminateIncrDecrAndCompoundAssign before constrainedTypeElim). The fact fails for a
    -- heap field of `mixedHeapFields`, so nothing is assumed there.
    --
    -- On the READ: hoisting to the enclosing statement could reference a local that
    -- statement declares. The duplicated read is pure (`readField(heap, obj, field)`);
    -- `.Assign` needs a read-back because its RHS may not be. Bottom-up traversal
    -- leaves the copy inside the assume unvisited, as `.Quantifier` relies on too.
    --
    -- Field reads only: a datatype destructor read (`MkCell(v).val`) has no checked
    -- write, so the `Datatype` branch over-approximates.
    if cx.mixed.contains fieldName.text then
      if !cx.aliased.contains fieldName.text then return [node] else
      match constraintCallForExpr cx (computeExprType model node).val node (src := source) (only := some true) with
      | some c =>
        let summary := "the value read from a field that another generic instantiation shares has its declared type"
        return [⟨.Assert c (some summary), source⟩, node]
      | none => return [node]
    else
    match constraintCallForExpr cx (computeExprType model node).val node (src := source) with
    | some c => return [⟨.Assume c, source⟩, node]
    | none => return [node]
  | .Hole _ (some ty) =>
    if !resultUsed || (constraintCallFor cx ty.val (mkId "") (src := source) (only := some false)).isNone then
      return [node]
    let n ← modifyGet fun n => (n, n + 1)
    let h := mkId s!"$constrainedHole{n}"
    let decl : StmtExprMd := ⟨.Assign [⟨.Declare ⟨h, some ty⟩, source⟩] node, source⟩
    let assume := (constraintCallFor cx ty.val h (src := source) (only := some false)).toList.map
      fun c => ⟨.Assume c, source⟩
    return [decl] ++ assume ++ [⟨.Var (.Local h), source⟩]
  | _ => return [node]

/-- Apply `elimNode` across a body via the flattening, `resultUsed`-aware
    traversal. A procedure body is a statement, so the top-level `resultUsed`
    is `false`. -/
def elimStmts (cx : CteCtx) (model : SemanticModel) (body : StmtExprMd) : StmtExprMd :=
  (mapStmtExprFlattenM (fun _ _ => pure none) (elimNode cx model) false body).run' 0

/-- Assert each constrained output's constraint where a transparent body exits without
    having just assigned it: before a `return` that does not directly follow an assignment
    to an output, which is already asserted, and after the body for the path that falls
    off its end. -/
private def addExitChecks (cx : CteCtx) (outputs : List Parameter)
    (body : StmtExprMd) : StmtExprMd :=
  let checks (at? : Option FileRange) : List StmtExprMd := outputs.filterMap fun p =>
    let src := at?.getD p.type.source
    (constraintCallFor cx p.type.val p.name (src := src) (only := some false)).map (⟨.Assert · none, src⟩)
  let assignsOutput (s : StmtExprMd) : Bool := match s.val with
    | .Assign [⟨.Local n, _⟩] _ =>
      outputs.any fun p => p.name.text == n.text && p.name.uniqueId == n.uniqueId
    | _ => false
  let guardReturns (stmts : List StmtExprMd) : List StmtExprMd :=
    (stmts.foldl (init := (([] : List StmtExprMd), false)) fun (acc, justAssigned) s =>
      match s.val with
      | .Return [] =>
        (acc ++ (if justAssigned then [] else checks (some s.source)) ++ [s], false)
      | .Assert .. => (acc ++ [s], justAssigned)
      | _ => (acc ++ [s], assignsOutput s)).1
  let guardBranch (b : StmtExprMd) : StmtExprMd := match b.val with
    | .Return [] => ⟨.Block (checks (some b.source) ++ [b]) none [] none, b.source⟩
    | _ => b
  let guard (e : StmtExprMd) : StmtExprMd := match e.val with
    | .Block stmts label invs dec => ⟨.Block (guardReturns stmts) label invs dec, e.source⟩
    | .IfThenElse c t el => ⟨.IfThenElse c (guardBranch t) (el.map guardBranch), e.source⟩
    | _ => e
  let body' := mapStmtExpr guard body
  let endsInReturn (stmts : List StmtExprMd) : Bool := match stmts.getLast? with
    | some ⟨.Return _, _⟩ => true
    | _ => false
  match body'.val with
  | .Block stmts none [] none =>
    if endsInReturn stmts then body' else ⟨.Block (stmts ++ checks none) none [] none, body'.source⟩
  | .Return _ => ⟨.Block (checks (some body'.source) ++ [body']) none [] none, body'.source⟩
  | _ => ⟨.Block (body' :: checks none) none [] none, body'.source⟩

def elimProc (cx : CteCtx) (model : SemanticModel)
    (proc : Procedure) : Procedure :=
  let inputRequires : List Condition := proc.inputs.flatMap fun p =>
    conditionsFor cx p.type.val p.name p.type.source
  let outputEnsures : List Condition := proc.outputs.flatMap fun p =>
    conditionsFor cx p.type.val p.name p.type.source
  let body' := match proc.body with
  -- A transparent body stays transparent: demoting it to `.Opaque` to carry
  -- `outputEnsures` would hide the body callers need to reason about the value
  -- produced. `.Transparent` has nowhere to put a postcondition, so the outputs'
  -- type constraints are asserted where the body exits instead.
  | .Transparent bodyExpr =>
    let constrained := proc.outputs.filter fun p =>
      (constraintCallFor cx p.type.val p.name (src := p.type.source) (only := some false)).isSome
    if constrained.isEmpty then .Transparent (elimStmts cx model bodyExpr) else
    let body := elimStmts cx model bodyExpr
    .Transparent (addExitChecks cx constrained body)
  -- Output type-constraints go FIRST, before the user's own `ensures`. The order
  -- matters: ContractPass gives `$post_i` the `ensures` clauses before it, so a user
  -- postcondition is well-formed given its outputs' type constraints --
  -- `returns (r: nonzero)` with `ensures 10 / r > 1` needs `r != 0`. Appended
  -- instead, the constraint would come too late to be assumed.
  | .Opaque postconds impl modif =>
    let impl' := impl.map (elimStmts cx model)
    .Opaque (outputEnsures ++ postconds) impl' modif
  | .Abstract postconds => .Abstract (outputEnsures ++ postconds)
  | .External => .External
  let resolve := mapStmtExpr (resolveExprNode cx)
  let proc := { proc with
    body := body'
    inputs := proc.inputs.map fun p => { p with type := resolveType cx.ptMap p.type }
    outputs := proc.outputs.map fun p => { p with type := resolveType cx.ptMap p.type }
    -- Prepend the generated input type-constraint requires, for the same ordering
    -- reason as `outputEnsures` above: `$pre_i` sees the `requires` clauses before
    -- it, so `(x: nonzero)` with `requires 10 / x > 1` needs `x != 0`.
    preconditions := inputRequires ++ proc.preconditions }
  mapProcedureM (m := Id) resolve proc

private def mkWitnessProc (cx : CteCtx) (ct : ConstrainedType) : Procedure :=
  let src := ct.witness.source

  let witnessId : Identifier := mkId "$witness"
  let witnessInit : StmtExprMd :=
    ⟨.Assign [⟨.Declare ⟨witnessId, some (resolveType cx.ptMap ct.base)⟩, src⟩] ct.witness, src⟩
  let assumeBase : List StmtExprMd :=
    (constraintCallFor cx ct.base.val witnessId (src := src) (only := some true)).toList.map
      (⟨.Assume ·, src⟩)
  let assert : StmtExprMd :=
    ⟨.Assert (constraintCallFor cx (.UserDefined ct.name) witnessId (src := src)).get! none, src⟩
  { name := mkId s!"$witness_{ct.name.text}"
    inputs := []
    outputs := []
    body := .Opaque [] (some ⟨.Block ([witnessInit] ++ assumeBase ++ [assert]) none [] none, src⟩) []
    preconditions := []
    decreases := none }

/-- The heap fields whose location another heap field shares at a different type, as the
    instantiations of a generic composite do. No instantiation may rely on such a field's
    constraint, as one object can be both: through `D<S> extends Box<S>, Box<int>` at
    `S := int8`, a `Box<int>` view sets a `Box<int8>`'s `v` to 1000. A type stored in another
    box, as `bool` is, is no exception: the `int` read off a `bool` box is one value, so two
    bounds assumed of it may contradict. -/
private def descendantTags (ptMap : ConstrainedTypeMap) (owner : String) : List String :=
  match ptMap.get? owner with
  | some ct =>
    if !ct.free then [] else
    foldStmtExpr (fun e acc => match e.val with
      | .StaticCall callee [] _ => if callee.text.endsWith "_TypeTag" then callee.text :: acc else acc
      | _ => acc) [] ct.constraint
  | none => []

private def aliasedHeapFields (ptMap : ConstrainedTypeMap) (heapFields : List HeapField) :
    Std.HashSet String :=
  let owner (f : HeapField) : String :=
    ptMap.fold (init := "") fun best name ct =>
      if ct.free && f.name.text.startsWith (name ++ ".") && name.length > best.length then name else best
  heapFields.foldl (init := {}) fun s f =>
    if heapFields.any fun g => g.location.text == f.location.text && !highEq g.type f.type &&
        (descendantTags ptMap (owner f)).any (descendantTags ptMap (owner g)).contains
    then s.insert f.name.text else s

private def mkDowncastProc (cx : CteCtx) (ct : ConstrainedType) : Option Procedure :=
  match resolveType cx.ptMap ct.base |>.val with
  | .UserDefined b =>
    if b.text != compositeTypeName.text then none else
    let src := ct.name.source
    let compositeTy : HighTypeMd := ⟨.UserDefined compositeTypeName, src⟩
    let pRef : StmtExprMd := ⟨.Var (.Local "p"), src⟩
    (constraintCallForExpr cx (.UserDefined ct.name) pRef src).map fun condition =>
      { name := downcastProcName ct.name, typeArgs := [],
        inputs := [{ name := "p", type := compositeTy }],
        outputs := [{ name := "r", type := compositeTy }],
        preconditions := [{ condition }],
        decreases := none,
        body := .Transparent ⟨.Block [⟨.Assign [⟨.Local "r", src⟩] pRef, src⟩] none [] none, src⟩ }
  | _ => none

private def mixedHeapFields (heapFields : List HeapField) : Std.HashSet String :=
  heapFields.foldl (init := {}) fun s f =>
    if heapFields.any fun g => g.location.text == f.location.text && !highEq g.type f.type
    then s.insert f.name.text else s

/-- `ContractPass` turns an `invokeOn` trigger plus `ensures` into

      forall (r: int) { r#C.f } => T$constraint(r#C.f)

    `elimNode` already restates this at each read, as a value-block
    `{ assume T$constraint(read); read }`. A value-block needs a statement position, so
    it reaches neither a loop invariant nor across a call -- a caller of a transparent
    procedure sees the body as an expression. The axiom is a proposition, so it holds in
    both.

    Built as `invokeOn` + `ensures` rather than by populating `Procedure.axioms`
    directly, so the heap read reaches `HeapParameterization` in an ordinary spec
    field of a procedure that has a parameter to thread `$heap` through. Written
    straight into `axioms` here, the read is in a slot no pass threads the heap into
    and Core fails with `Cannot find this fvar in the context! $heap`.

    Triggered on the field read itself, so it instantiates where a read appears
    rather than for every object of type `C`. Quantified over the `int` reference
    rather than a `Composite`: z3 does not instantiate a trigger that applies the
    `Composite` selector to a bound variable.

    The composite and field names are joined with `$`, not `_`: a `_` separator makes
    `A_b.c` and `A.b_c` mint the same name, and underscores are common enough in real
    names for that to collide in ordinary code. `$` only collides for a name that itself
    contains `$`, which the duplicate-definition diagnostic already tells the author to
    rename, and matches `MonomorphizeComposites`' `$aN$` tags.

    Core quantifies `r` over every reference, and heap fields sharing a location share its
    storage: the first's axiom holds for all, and a field of `mixedHeapFields` has none. -/
private def mkHeapFieldConstraintProc (cx : CteCtx) (f : HeapField) : Option Procedure :=
  if cx.mixed.contains f.name.text then none else
  let src := f.name.source
  let refName : Identifier := mkId "$r"
  let fieldRead : StmtExprMd := ⟨.Var (.Field ⟨.Var (.Local refName), src⟩ f.name), src⟩
  (constraintCallForExpr cx f.type.val fieldRead (src := src) (only := some false)).map fun constraint =>
    { name := mkId s!"$fieldConstraint_{f.name.text.replace "." "$"}"
      inputs := [{ name := refName, type := ⟨.TInt, src⟩ }]
      outputs := []
      body := .Opaque [{ condition := constraint }] none []
      preconditions := []
      decreases := none
      invokeOn := some fieldRead }

/-- Eliminate constrained types within a composite type definition: resolve
    constrained field types to their base types and run constrained type
    elimination on the composite's instance procedures.

    This is necessary because `constrainedTypeElim` removes the constrained type
    definitions from the program. Any reference to a constrained type left inside
    a composite (e.g. a `count: nat` field) would otherwise dangle and fail to
    resolve in later passes and the final Core translation. -/
def elimCompositeType (cx : CteCtx) (model : SemanticModel)
    (ct : CompositeType) (prepare : Procedure → Procedure := id) : CompositeType :=
  { ct with
    fields := ct.fields.map fun f => { f with type := resolveType cx.ptMap f.type }
    instanceProcedures := ct.instanceProcedures.map (elimProc cx model ∘ prepare) }

private def procedureHasEffect (ids : Std.HashSet Nat) (proc : Procedure) : Bool :=
  proc.name.uniqueId.any ids.contains

/-- Preserve constrained-global invariants while globals are still represented
    as fields. Readers require a valid incoming value; writers additionally
    guarantee a valid outgoing value. -/
private def addConstrainedGlobalConditions (cx : CteCtx)
    (effects : GlobalEffectsByProcId) (fields : List Field)
    (proc : Procedure) : Procedure :=
  let (requires, ensures) := fields.foldl (init := ([], []))
    fun (requires, ensures) field =>
      let qualifiedName := { field.name with text := s!"$static.{field.name.text}" }
      let reference : StmtExprMd := ⟨.Var (.Local qualifiedName), field.name.source⟩
      let condition := conditionsForExpr cx field.type.val reference field.type.source
      if condition.isEmpty then (requires, ensures) else
      let readers := match field.name.uniqueId with
        | some id => effects.readers.getD id {}
        | none => {}
      let writers := match field.name.uniqueId with
        | some id => effects.writers.getD id {}
        | none => {}
      let requires := if procedureHasEffect readers proc || procedureHasEffect writers proc then
        requires ++ condition else requires
      let ensures := if procedureHasEffect writers proc then
        ensures ++ condition else ensures
      (requires, ensures)
  let checkedEnsures := ensures.filter (·.mode != .Assume)
  let body := if ensures.isEmpty then proc.body else match proc.body with
    | .Transparent implementation =>
      if checkedEnsures.isEmpty then proc.body
      else .Opaque ensures (some implementation) []
    | .Opaque posts implementation modifies =>
        .Opaque (posts ++ ensures) implementation modifies
    | .Abstract posts => .Abstract (posts ++ ensures)
    | .External => .External
  { proc with preconditions := requires ++ proc.preconditions, body }

public def constrainedTypeElim (model : SemanticModel) (program : LaurelProgram)
    : LaurelProgram × List Message :=
  let ptMap := buildConstrainedTypeMap program.types
  if ptMap.isEmpty then (program, []) else
  let cx : CteCtx :=
    { ptMap, dtMap := buildDatatypeMap program.types, mixed := mixedHeapFields program.heapFields,
      aliased := aliasedHeapFields ptMap program.heapFields }
  let constraintProcs := program.types.filterMap fun
    | .Constrained ct => some (mkConstraintProc ptMap ct) | _ => none
  let witnessProcedures := program.types.filterMap fun
    | .Constrained ct => some (mkWitnessProc cx ct) | _ => none
  let downcastProcedures := program.types.filterMap fun
    | .Constrained ct => mkDowncastProc cx ct | _ => none
  let firstAtLocation := (program.heapFields.foldl (init := (([] : List HeapField), ({} : Std.HashSet String)))
    fun (acc, seen) f =>
      if seen.contains f.location.text then (acc, seen) else (acc ++ [f], seen.insert f.location.text)).1
  let fieldAxiomProcedures := firstAtLocation.filterMap (mkHeapFieldConstraintProc cx)
  let instanceProcedures := program.types.flatMap fun
    | .Composite composite => composite.instanceProcedures
    | _ => []
  let allProcedures := program.staticProcedures ++ instanceProcedures
  let effects := computeGlobalEffectsByProcId model allProcedures program.staticFields
  let addGlobalConditions :=
    addConstrainedGlobalConditions cx effects program.staticFields
  let prepared := program.staticProcedures.map addGlobalConditions
  (mapLaurelProgramHighTypes (resolveType ptMap) { program with
    staticProcedures := constraintProcs ++
      prepared.map (elimProc cx model)
                        ++ witnessProcedures ++ fieldAxiomProcedures ++ downcastProcedures
    staticFields := program.staticFields.map fun field =>
      { field with
        type := resolveType ptMap field.type
        initializer := field.initializer.map (mapStmtExpr (resolveExprNode cx)) }
    heapFields := program.heapFields.map fun field =>
      { field with type := resolveType ptMap field.type }
    types := program.types.filterMap fun
      | .Constrained _ => none
      | .Composite ct =>
          some (.Composite (elimCompositeType cx model ct addGlobalConditions))
      | .Datatype dt =>
        -- Resolve constrained types used as datatype constructor field
        -- types (e.g. `int32` -> `int`). Without this, the constrained
        -- type reference dangles after its definition is dropped below,
        -- and the Laurel-to-Core translator cannot resolve it.
        -- This lowers the field *type* only; the range predicate is not
        -- re-asserted on field reads, so field range constraints are
        -- intentionally over-approximated away (a `MkCell(out_of_range).val`
        -- read is not caught) — matching bare-parameter and `elimCompositeType`
        -- handling.
        some (.Datatype { dt with constructors := dt.constructors.map fun c =>
          { c with args := c.args.map fun p =>
            { p with type := resolveType ptMap p.type } } })
      | other => some other },
   [])

/-- Pipeline pass: constrained type elimination. -/
public def constrainedTypeElimPass : LaurelPass := .onUnordered {
  name := "ConstrainedTypeElim"
  unsupported := [
      NodeKind.LaurelProgram.staticFunctions.cons,
      NodeKind.StmtExpr.Return.value.some
    ]
  creates := [NodeKind.LaurelProgram.staticProcedures.cons, NodeKind.StmtExpr.StaticCall]
  removes := [NodeKind.TypeDefinition.Constrained, NodeKind.StmtExpr.IsType, NodeKind.StmtExpr.AsType]
  documentation := "Eliminates constrained types by replacing them with their base types and generating constraint-checking procedures and witness procedures. A free constraint is assumed wherever a value of its type enters and never asserted. Type tests against constrained types are rewritten to call the generated constraint procedure, and casts to a `downcast$T` helper that requires it."
  needsResolves := true }
  fun _ p m =>
    let (p', diags) := constrainedTypeElim m p
    (p', diags, {})

end Strata.Laurel

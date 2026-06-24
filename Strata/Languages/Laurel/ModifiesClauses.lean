/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.LaurelTypes

/-
Modifies clause transformation (Laurel → Laurel).

Transforms procedures with modifies clauses by generating a frame condition
and conjoining it with the postcondition. After this pass, the modifies list
is cleared since its semantics have been absorbed into the postcondition.

This pass should run after heap parameterization, which has already:
- Added explicit heap parameter ($heap as inout)
- Transformed field accesses to readField/updateField calls
- Collected field constants

The frame condition is field-granular: each allocated (object, field) pair not
named in the modifies clause is preserved across the call. A clause may name a
whole object (all its fields may change) or a single field `o#f` (only that
field of `o` may change).

Generates:
  forall $obj: Composite, $fld: Field =>
    $obj < old($heap).nextReference && notModified($obj, $fld) ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)

where notModified($obj, $fld) conjoins, per entry:
- `$obj != e`                 single object `e`
- `!(select(s, $obj))`        Set `s`
- `!($obj == o && $fld == f)` field `(o, f)`
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/--
A single entry in a modifies clause: a single Composite expression, a Set of
Composite expressions, or a single `(object, field)` pair (field-granular).
-/
inductive ModifiesEntry where
  | single (expr : StmtExprMd)       -- a single Composite reference
  | set (expr : StmtExprMd)          -- a Set Composite expression
  -- field-granular: only `fieldConst` of `objExpr` may change
  | field (objExpr : StmtExprMd) (fieldConst : StmtExprMd)

/--
Recognize a heap-parameterized field read `readField($heap, obj, fieldConst)`
(optionally under one Box destructor), as emitted for a field target like `o#f`.
`fieldConst` is the per-declaring-type `Field` constructor (`A.x` ≠ `B.x`), the
same one `readField` uses — so the soundness gate holds by construction.
-/
def matchModifiesFieldRead (e : StmtExpr) : Option (StmtExprMd × StmtExprMd) :=
  let tryReadField : StmtExpr → Option (StmtExprMd × StmtExprMd) := fun
    | .StaticCall callee [_heap, objExpr, fieldConst] =>
        if callee.text == "readField" then some (objExpr, fieldConst) else none
    | _ => none
  match tryReadField e with
  | some r => some r
  | none =>
    -- Unwrap one Box destructor; gate on `Box` so unrelated unary calls aren't matched.
    match e with
    | .StaticCall callee [arg] => if callee.text.startsWith "Box" then tryReadField arg.val else none
    | _ => none

/--
Classify a heap-relevant type into a `ModifiesEntry`, or `none` for
non-heap-relevant types. Delegates to `classifyModifiesHighType` for the
type classification.
-/
def classifyModifiesType (expr : StmtExprMd) (ty : HighType) : Option ModifiesEntry :=
  match classifyModifiesHighType ty with
  | some .composite    => some (.single expr)
  | some .compositeSet => some (.set expr)
  | none               => none

/--
Extract modifies entries. A field-access target (lowered to a `readField`)
yields a field-granular entry; otherwise it is classified by type. Non-composite
types (e.g. primitive globals) are filtered out — the frame applies to heap objects.
-/
def extractModifiesEntries (model: SemanticModel)
    (modifiesExprs : List StmtExprMd) : List ModifiesEntry :=
  modifiesExprs.filterMap fun expr =>
    -- Soundness: a `.field` entry is only built for a field read of a heap object.
    -- Targets with a non-composite owner are dropped upstream by
    -- filterBodyNonCompositeModifies before heap parameterization.
    match matchModifiesFieldRead expr.val with
    | some (objExpr, fieldConst) => some (.field objExpr fieldConst)
    | none => classifyModifiesType expr (computeExprType model expr).val
/--
Build the "obj is not modified" condition for a single modifies entry as a Laurel StmtExpr.
- For a single Composite `e`: `$obj != e`
- For a Set Composite `e`: `!(select(e, $obj))` i.e. $obj is not in the set
- For a field `(o, f)`: `!($obj == o && $fld == f)` i.e. the quantified
  `($obj, $fld)` pair is not the modified `(object, field)` pair (field-granular)
-/
def buildNotModifiedForEntry (obj : StmtExprMd) (fld : StmtExprMd) (entry : ModifiesEntry) : StmtExprMd :=
  match entry with
  | .single expr =>
    mkMd <| .PrimitiveOp .Neq [obj, expr]
  | .set expr =>
    let membership := mkMd <| .StaticCall "select" [expr, obj]
    mkMd <| .PrimitiveOp .Not [membership]
  | .field objExpr fieldConst =>
    let objEq := mkMd <| .PrimitiveOp .Eq [obj, objExpr]
    let fldEq := mkMd <| .PrimitiveOp .Eq [fld, fieldConst]
    let bothMatch := mkMd <| .PrimitiveOp .And [objEq, fldEq]
    mkMd <| .PrimitiveOp .Not [bothMatch]

/-- Conjoin a list of StmtExprs with `&&`. -/
def conjoinAll (exprs : List StmtExprMd) : StmtExprMd :=
  match exprs with
  | [] => mkMd <| .LiteralBool true
  | [single] => single
  | first :: rest => rest.foldl (fun acc e => mkMd <| .PrimitiveOp .And [acc, e]) first

/--
Build the modifies frame condition as a Laurel StmtExpr.

Generates a single quantified formula:

  forall $obj: Composite, $fld: Field =>
    notModified($obj, $fld) && $obj < old($heap).nextReference ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)

Returns `none` if there are no entries.
-/
def buildModifiesEnsures (proc: Procedure) (model: SemanticModel) (modifiesExprs : List StmtExprMd)
    (heapName : Identifier) : Option StmtExprMd :=
  let entries := extractModifiesEntries model modifiesExprs
  let objName : Identifier := "$modifies_obj"
  let fldName : Identifier := "$modifies_fld"
  let obj := mkMd <| .Var (.Local objName)
  let fld := mkMd <| .Var (.Local fldName)
  let heapIn := mkMd <| .Old (mkMd (.Var (.Local heapName)))
  let heapOut := mkMd <| .Var (.Local heapName)
      -- Build the "obj is allocated" condition: Composite..ref($obj) < old($heap).nextReference
  let heapCounter := mkMd <| .StaticCall "Heap..nextReference!" [heapIn]
  let objRef := mkMd <| .StaticCall "Composite..ref!" [obj]
  let objAllocated := mkMd <| .PrimitiveOp .Lt [objRef, heapCounter]
  let antecedent := if entries.isEmpty
    then objAllocated
    else
      -- Build the "not modified" precondition from all entries
      -- Combine: $obj < old($heap).nextReference && notModified($obj)
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj fld))
      mkMd <| .PrimitiveOp .And [objAllocated, notModified]
  -- Build: readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)
  let readIn := mkMd <| .StaticCall "readField" [heapIn, obj, fld]
  let readOut := mkMd <| .StaticCall "readField" [heapOut, obj, fld]
  let heapUnchanged := mkMd <| .PrimitiveOp .Eq [readIn, readOut]
  -- Build: antecedent ==> heapUnchanged
  let implBody := mkMd <| .PrimitiveOp .Implies [antecedent, heapUnchanged]
  -- Build: forall $obj: Composite, $fld: Field => ...
  let innerForall := mkMd <| .Quantifier .Forall ⟨ fldName, { val := .UserDefined "Field", source := none } ⟩ none implBody
  let outerForall : StmtExprMd := { val := .Quantifier .Forall ⟨ objName, { val := .UserDefined "Composite", source := none } ⟩ none innerForall, source := proc.name.source }
  some outerForall

/--
Check whether a procedure has a `$heap` output parameter,
indicating it mutates the heap.
-/
def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/--
Transform a single procedure: if it has modifies clauses, generate the frame
condition and conjoin it with the postcondition, then clear the modifies list.

If the procedure has `modifies *`, no frame condition is generated (the procedure
may modify anything on the heap), and the modifies list is simply cleared.

If the procedure has a `$heap` but no modifies clause, adds a postcondition
that all allocated objects are preserved between heaps:
  `forall $obj: Composite, $fld: Field => $obj < old($heap).nextReference ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)`

If the modifies clause uses a wildcard (`*`), the frame condition is skipped
entirely — the procedure may modify anything.
-/
def transformModifiesClauses (model: SemanticModel)
    (proc : Procedure) : Except (Array DiagnosticModel) Procedure :=
  match proc.body with
  | .External => .ok proc
  | .Opaque postconds impl modifiesExprs =>
      if hasModifiesWildcard modifiesExprs then
        -- modifies * means the procedure can modify anything; no frame condition
        .ok { proc with body := .Opaque postconds impl [] }
      else if hasHeapOut proc then
        let heapName := heapVarName
        let frameCondition := buildModifiesEnsures proc model modifiesExprs heapName
        let postconds' := match frameCondition with
          | some frame => postconds ++ [{ condition := frame, summary := "modifies clause" }]
          | none => postconds
        .ok { proc with body := .Opaque postconds' impl [] }
      else
        .ok proc
  | _ => .ok proc

/--
Filter non-composite modifies entries from a procedure body, collecting diagnostics
for each filtered entry. This pre-pass ensures that global variables of primitive type
do not incorrectly trigger heap parameterization.
Should run before heap parameterization.
-/
def filterBodyNonCompositeModifies (model : SemanticModel) (body : Body)
    : Body × List DiagnosticModel :=
  match body with
  | .Opaque posts impl mods =>
    let (kept, diags) := mods.foldl (fun (acc, ds) e =>
      -- Shared rejection: drop the entry and emit the "non-composite type" diagnostic.
      let reject := fun (ty : HighType) (kind : String) =>
        (acc, ds ++ [diagnosticFromSource e.source s!"modifies clause {kind} has non-composite type '{formatHighTypeVal ty}' and will be ignored"])
      match e.val with
      | .All => (acc ++ [e], ds)  -- wildcard is always kept
      | .Var (.Field target _) =>
        -- Field target `o#f`: keep when the owner is a heap object (the field's own type is irrelevant).
        let ownerTy := (computeExprType model target).val
        if isHeapRelevantType ownerTy then (acc ++ [e], ds)
        else reject ownerTy "field target"
      | _ =>
        let ty := (computeExprType model e).val
        if isHeapRelevantType ty then (acc ++ [e], ds)
        else reject ty "entry"
    ) ([], [])
    (.Opaque posts impl kept, diags)
  | other => (other, [])

/--
Filter non-composite modifies entries from all procedures in a program,
collecting diagnostics. Should run before heap parameterization so that
the heap parameterization phase remains agnostic to modifies clauses.
-/
def filterNonCompositeModifies (model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  let (staticProcs, staticDiags) := program.staticProcedures.foldl (fun (ps, ds) proc =>
    let (body', bodyDiags) := filterBodyNonCompositeModifies model proc.body
    (ps ++ [{ proc with body := body' }], ds ++ bodyDiags)
  ) ([], [])
  let (types', typeDiags) := program.types.foldl (fun (ts, ds) td =>
    match td with
    | .Composite ct =>
      let (instProcs, instDiags) := ct.instanceProcedures.foldl (fun (ps, ds) proc =>
        let (body', bodyDiags) := filterBodyNonCompositeModifies model proc.body
        (ps ++ [{ proc with body := body' }], ds ++ bodyDiags)
      ) ([], [])
      (ts ++ [.Composite { ct with instanceProcedures := instProcs }], ds ++ instDiags)
    | other => (ts ++ [other], ds)
  ) ([], [])
  ({ program with staticProcedures := staticProcs, types := types' }, staticDiags ++ typeDiags)

/--
Transform a Laurel program: apply modifies clause transformation to all procedures.
This is a Laurel → Laurel pass that should run after heap parameterization.

Always returns the (best-effort) transformed program together with any diagnostics,
so that later passes can continue and report additional errors.
-/
def modifiesClausesTransform (model: SemanticModel) (program : Program) : Program × List DiagnosticModel :=
  let (procs', errors) := program.staticProcedures.foldl (fun (acc, errs) proc =>
    match transformModifiesClauses model proc with
    | .ok proc' => (acc ++ [proc'], errs)
    | .error newErrs => (acc ++ [proc], errs ++ newErrs.toList)
  ) ([], [])
  ({ program with staticProcedures := procs' }, errors)

end -- public section

/-- Pipeline pass: filter non-composite modifies clauses. -/
public def filterNonCompositeModifiesPass : LoweringPass where
  name := "FilterNonCompositeModifies"
  documentation := "Filters modifies clauses that refer to non-composite types (e.g. primitives), which cannot be heap-parameterized. Emits a warning for each removed clause. Should run before heap parameterization so that phase remains agnostic to modifies clauses."
  run := fun p m _ =>
    let (p', diags) := filterNonCompositeModifies m p
    (p', diags, {})

/-- Pipeline pass: translate modifies clauses into ensures clauses. -/
public def modifiesClausesTransformPass : LoweringPass where
  name := "ModifiesClausesTransform"
  documentation := "Translates modifies clauses into additional ensures clauses. The modifies clause of a procedure is translated into a quantified assertion that states objects not mentioned in the modifies clause have their field values preserved between the input and output heap."
  needsResolves := true
  comesAfter := [⟨ heapParameterizationPass.meta, "the modifies pass refers to several types and variables introduced by heap parameterization: Composite, Field, $heap_in, $heap."⟩]
  run := fun p m _ =>
    let (p', diags) := modifiesClausesTransform m p
    (p', diags, {})

end Strata.Laurel

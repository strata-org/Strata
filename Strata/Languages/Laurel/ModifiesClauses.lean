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
Classify a heap-relevant type into a `ModifiesEntry`, or `none` for
non-heap-relevant types. Delegates to `classifyModifiesHighType` for the
type classification.
-/
def classifyModifiesType (expr : StmtExprMd) (ty : HighType) : Option ModifiesEntry :=
  match classifyModifiesHighType ty with
  | some .composite    => some (.single expr)
  | some .compositeSet => some (.set expr)
  | none               => none

/-- Extract modifies entries: a field target `o#f` (kept symbolic by heap
parameterization) becomes a field-granular entry; other entries are classified
by type. Non-heap-relevant entries are dropped during resolution. -/
def extractModifiesEntries (model: SemanticModel)
    (modifiesExprs : List StmtExprMd) : List ModifiesEntry :=
  modifiesExprs.filterMap fun expr =>
    match expr.val with
    -- Field target `o#f`: non-composite owners are already dropped during
    -- resolution, so any field target reaching here owns a heap object.
    | .Var (.Field objExpr fieldName) =>
      (resolveQualifiedFieldName model fieldName).map fun qualifiedName =>
        .field objExpr (mkMd <| .StaticCall qualifiedName [])
    | _ => classifyModifiesType expr (computeExprType model expr).val
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

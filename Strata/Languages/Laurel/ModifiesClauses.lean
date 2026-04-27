/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelTypes
public import Strata.Languages.Core.Verifier
public import Strata.Languages.Laurel.Resolution

/-
Modifies clause transformation (Laurel → Laurel).

Transforms procedures with modifies clauses by generating a frame condition
and conjoining it with the postcondition. After this pass, the modifies list
is cleared since its semantics have been absorbed into the postcondition.

This pass should run after heap parameterization, which has already:
- Added explicit heap parameters ($heap_in, $heap)
- Transformed field accesses to readField/updateField calls
- Collected field constants

The frame condition states: for every object not mentioned in the modifies clause,
all field values are preserved between the input and output heaps.

Generates:
  forall $obj: Composite, $fld: Field =>
    $obj < $heap_in.nextReference && notModified($obj) ==> readField($heap_in, $obj, $fld) == readField($heap, $obj, $fld)

where `notModified($obj)` is the conjunction of `$obj != e` for each single entry `e`,
and `!(select(s, $obj))` for each set entry `s`.
-/

namespace Strata.Laurel

public section

private def mkMd (e : StmtExpr) : StmtExprMd := { val := e, source := none }

/--
A single entry in a modifies clause, either a single Composite expression
or a Set of Composite expressions.
-/
inductive ModifiesEntry where
  | single (expr : StmtExprMd)       -- a single Composite reference
  | set (expr : StmtExprMd)          -- a Set Composite expression

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
Extract modifies entries from the list of modifies StmtExprs, using the type
environment and type definitions to distinguish Composite from Set Composite.
Non-composite types (e.g., global variables of primitive type) are filtered out
since the frame condition only applies to heap objects.
-/
def extractModifiesEntries (model: SemanticModel)
    (modifiesExprs : List StmtExprMd) : List ModifiesEntry :=
  modifiesExprs.filterMap fun expr =>
    classifyModifiesType expr (computeExprType model expr).val
/--
Build the "obj is not modified" condition for a single modifies entry as a Laurel StmtExpr.
- For a single Composite `e`: `$obj != e`
- For a Set Composite `e`: `!(select(e, $obj))` i.e. $obj is not in the set
-/
def buildNotModifiedForEntry (obj : StmtExprMd) (entry : ModifiesEntry) : StmtExprMd :=
  match entry with
  | .single expr =>
    mkMd <| .PrimitiveOp .Neq [obj, expr]
  | .set expr =>
    let membership := mkMd <| .StaticCall "select" [expr, obj]
    mkMd <| .PrimitiveOp .Not [membership]

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
    notModified($obj) && $obj < $heap_in.nextReference ==> readField($heap_in, $obj, $fld) == readField($heap, $obj, $fld)

Returns `none` if there are no entries.
-/
def buildModifiesEnsures (proc: Procedure) (model: SemanticModel) (modifiesExprs : List StmtExprMd)
    (heapInName heapOutName : Identifier) : Option StmtExprMd :=
  let entries := extractModifiesEntries model modifiesExprs
  let objName : Identifier := "$modifies_obj"
  let fldName : Identifier := "$modifies_fld"
  let obj := mkMd <| .Identifier objName
  let fld := mkMd <| .Identifier fldName
  let heapIn := mkMd <| .Identifier heapInName
  let heapOut := mkMd <| .Identifier heapOutName
      -- Build the "obj is allocated" condition: Composite..ref($obj) < $heap_in.nextReference
  let heapCounter := mkMd <| .StaticCall "Heap..nextReference!" [heapIn]
  let objRef := mkMd <| .StaticCall "Composite..ref!" [obj]
  let objAllocated := mkMd <| .PrimitiveOp .Lt [objRef, heapCounter]
  let antecedent := if entries.isEmpty
    then objAllocated
    else
      -- Build the "not modified" precondition from all entries
      -- Combine: $obj < $heap_in.nextReference && notModified($obj)
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj))
      mkMd <| .PrimitiveOp .And [objAllocated, notModified]
  -- Build: readField($heap_in, $obj, $fld) == readField($heap, $obj, $fld)
  let readIn := mkMd <| .StaticCall "readField" [heapIn, obj, fld]
  let readOut := mkMd <| .StaticCall "readField" [heapOut, obj, fld]
  let heapUnchanged := mkMd <| .PrimitiveOp .Eq [readIn, readOut]
  -- Build: antecedent ==> heapUnchanged
  let implBody := mkMd <| .PrimitiveOp .Implies [antecedent, heapUnchanged]
  -- Build: forall $obj: Composite, $fld: Field => ...
  let innerForall := mkMd <| .Quantifier .Forall ⟨ fldName, { val := .TTypedField { val := .TInt, source := none }, source := none } ⟩ none implBody
  let outerForall : StmtExprMd := { val := .Quantifier .Forall ⟨ objName, { val := .UserDefined "Composite", source := none } ⟩ none innerForall, source := none, md := proc.name.md }
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
  `forall $obj: Composite, $fld: Field => $obj < $heap_in.nextReference ==> readField($heap_in, $obj, $fld) == readField($heap, $obj, $fld)`
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
        let heapInName : Identifier := "$heap_in"
        let heapName : Identifier := "$heap"
        let frameCondition := buildModifiesEnsures proc model modifiesExprs heapInName heapName
        let postconds' := match frameCondition with
          | some frame => postconds ++ [{ condition := frame : Condition }]
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
      match e.val with
      | .All => (acc ++ [e], ds)  -- wildcard is always kept
      | _ =>
        let ty := (computeExprType model e).val
        if isHeapRelevantType ty then (acc ++ [e], ds)
        else
          (acc, ds ++ [(fileRangeToCoreMd e.source e.md).toDiagnostic s!"modifies clause entry has non-composite type '{formatHighTypeVal ty}' and will be ignored"])
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
end Strata.Laurel

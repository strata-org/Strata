/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Core.Verifier

/-
Modifies clause transformation (Laurel → Laurel).

Transforms procedures with modifies clauses by generating a frame condition
and conjoining it with the postcondition. After this pass, the modifies list
is cleared since its semantics have been absorbed into the postcondition.

This pass should run after heap parameterization, which has already:
- Added explicit heap parameters ($heap_in, $heap_out)
- Transformed field accesses to readField/updateField calls
- Collected field constants

The frame condition states: for every object not mentioned in the modifies clause,
all field values are preserved between the input and output heaps.

Generates:
  forall $obj: Composite, $fld: Field =>
    $obj < $heap_in.counter && notModified($obj) ==> readField($heap_in, $obj, $fld) == readField($heap_out, $obj, $fld)

where `notModified($obj)` is the conjunction of `$obj != e` for each single entry `e`,
and `!(select(s, $obj))` for each set entry `s`.
-/

namespace Strata.Laurel

private def mkMd (e : StmtExpr) : StmtExprMd := ⟨e, #[]⟩

/--
A single entry in a modifies clause, either a single Composite expression
or a Set of Composite expressions.
-/
inductive ModifiesEntry where
  | single (expr : StmtExprMd)       -- a single Composite reference
  | set (expr : StmtExprMd)          -- a Set Composite expression

/--
Extract modifies entries from the list of modifies StmtExprs, using the type
environment and type definitions to distinguish Composite from Set Composite.
-/
def extractModifiesEntries (env : TypeEnv) (types : List TypeDefinition)
    (modifiesExprs : List StmtExprMd) : List ModifiesEntry :=
  modifiesExprs.map fun expr =>
    match (computeExprType env types expr).val with
    | .TSet _ => .set expr
    | _ => .single expr
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
    notModified($obj) && $obj < $heap_in.counter ==> readField($heap_in, $obj, $fld) == readField($heap_out, $obj, $fld)

Returns `none` if there are no entries.
-/
def buildModifiesEnsures (env : TypeEnv)
    (types : List TypeDefinition) (modifiesExprs : List StmtExprMd)
    (heapInName heapOutName : Identifier) : Option StmtExprMd :=
  let entries := extractModifiesEntries env types modifiesExprs
  if entries.isEmpty then none
  else
    let objName := "$modifies_obj"
    let fldName := "$modifies_fld"
    let obj := mkMd <| .Identifier objName
    let fld := mkMd <| .Identifier fldName
    let heapIn := mkMd <| .Identifier heapInName
    let heapOut := mkMd <| .Identifier heapOutName
    -- Build the "not modified" precondition from all entries
    let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj))
    -- Build the "obj is allocated" condition: $obj < $heap_in.counter
    let heapCounter := mkMd <| .StaticCall "Heap..counter" [heapIn]
    let objAllocated := mkMd <| .PrimitiveOp .Lt [obj, heapCounter]
    -- Combine: $obj < $heap_in.counter && notModified($obj)
    let antecedent := mkMd <| .PrimitiveOp .And [objAllocated, notModified]
    -- Build: readField($heap_in, $obj, $fld) == readField($heap_out, $obj, $fld)
    let readIn := mkMd <| .StaticCall "readField" [heapIn, obj, fld]
    let readOut := mkMd <| .StaticCall "readField" [heapOut, obj, fld]
    let heapUnchanged := mkMd <| .PrimitiveOp .Eq [readIn, readOut]
    -- Build: antecedent ==> heapUnchanged
    let implBody := mkMd <| .PrimitiveOp .Implies [antecedent, heapUnchanged]
    -- Build: forall $obj: Composite, $fld: Field => ...
    let innerForall := mkMd <| .Forall fldName (⟨ .UserDefined "Field", .empty ⟩) implBody
    let outerForall := ⟨ .Forall objName (⟨ .UserDefined "Composite", .empty ⟩) innerForall, modifiesExprs.head!.md ⟩
    some outerForall

/--
Check whether a procedure has a `$heap_out` output parameter,
indicating it mutates the heap.
-/
def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name == "$heap_out")

/--
Transform a single procedure: if it has modifies clauses, generate the frame
condition and conjoin it with the postcondition, then clear the modifies list.

If the procedure has a `$heap_out` but no modifies clause, adds a postcondition
that the heap data is preserved: `Heap..data($heap_in) == Heap..data($heap_out)`.
-/
def transformModifiesClauses (constants : List Constant) (types : List TypeDefinition)
    (proc : Procedure) : Except (Array DiagnosticModel) Procedure :=
  match proc.body with
  | .Opaque postconds impl modifiesExprs =>
      if modifiesExprs.isEmpty then
        -- No modifies clause: if the procedure has a heap out, add a postcondition
        -- that the data part of the heap is preserved (only counter may change).
        if hasHeapOut proc then
          let heapInName := "$heap_in"
          let heapOutName := "$heap_out"
          let heapIn := mkMd <| .Identifier heapInName
          let heapOut := mkMd <| .Identifier heapOutName
          let dataIn := mkMd <| .StaticCall "Heap..data" [heapIn]
          let dataOut := mkMd <| .StaticCall "Heap..data" [heapOut]
          let dataPreserved := ⟨ .PrimitiveOp .Eq [dataIn, dataOut], proc.md ⟩
          let postconds' := postconds ++ [dataPreserved]
          .ok { proc with body := .Opaque postconds' impl [] }
        else
          .ok proc
      else
        let env : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                             proc.outputs.map (fun p => (p.name, p.type)) ++
                             constants.map (fun c => (c.name, c.type))
        let heapInName := "$heap_in"
        let heapOutName := "$heap_out"
        let frameCondition := buildModifiesEnsures env types modifiesExprs heapInName heapOutName
        let postconds' := match frameCondition with
          | some frame => postconds ++ [frame]
          | none => postconds
        .ok { proc with body := .Opaque postconds' impl [] }
  | _ => .ok proc

/--
Transform a Laurel program: apply modifies clause transformation to all procedures.
This is a Laurel → Laurel pass that should run after heap parameterization.

Always returns the (best-effort) transformed program together with any diagnostics,
so that later passes can continue and report additional errors.
-/
def modifiesClausesTransform (program : Program) : Program × Array DiagnosticModel :=
  let (procs', errors) := program.staticProcedures.foldl (fun (acc, errs) proc =>
    match transformModifiesClauses program.constants program.types proc with
    | .ok proc' => (acc ++ [proc'], errs)
    | .error newErrs => (acc ++ [proc], errs ++ newErrs.toList)
  ) ([], [])
  ({ program with staticProcedures := procs' }, errors.toArray)

end Strata.Laurel

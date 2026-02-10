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

For each field constant `fld`, generates:
  forall $obj: Composite =>
    notModified($obj) ==> readField($heap_in, $obj, fld) == readField($heap_out, $obj, fld)

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

For each field constant and the combined modifies entries, generates:

  forall $obj: UserDefined "Composite" =>
    notModified($obj) ==> readField($heap_in, $obj, fld) == readField($heap_out, $obj, fld)

Returns `none` if there are no entries or no field constants.
-/
def buildModifiesEnsures (constants : List Constant) (env : TypeEnv)
    (types : List TypeDefinition) (modifiesExprs : List StmtExprMd)
    (heapInName heapOutName : Identifier) : Option StmtExprMd :=
  let entries := extractModifiesEntries env types modifiesExprs
  if entries.isEmpty then none
  else
    let fieldConstants := constants.filter fun c =>
      match c.type.val with | .TTypedField _ => true | _ => false
    if fieldConstants.isEmpty then none
    else
      let objName := "$modifies_obj"
      let obj := mkMd <| .Identifier objName
      let heapIn := mkMd <| .Identifier heapInName
      let heapOut := mkMd <| .Identifier heapOutName
      -- Build the "not modified" precondition from all entries
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj))
      -- Build one conjunct per field constant
      let perFieldExprs := fieldConstants.filterMap fun fldConst =>
        let fld := mkMd <| .Identifier fldConst.name
        let readIn := mkMd <| .StaticCall "readField" [heapIn, obj, fld]
        let readOut := mkMd <| .StaticCall "readField" [heapOut, obj, fld]
        let heapUnchanged := mkMd <| .PrimitiveOp .Eq [readIn, readOut]
        let implBody := mkMd <| StmtExpr.PrimitiveOp .Implies [notModified, heapUnchanged]
        some ⟨ .Forall objName (⟨ .UserDefined "Composite", .empty ⟩) implBody, modifiesExprs.head!.md ⟩
      match perFieldExprs with
      | [] => none
      | exprs => some (conjoinAll exprs)

/--
Check whether a procedure has a `$heap_out` output parameter,
indicating it mutates the heap.
-/
def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name == "$heap_out")

/--
Transform a single procedure: if it has modifies clauses, generate the frame
condition and conjoin it with the postcondition, then clear the modifies list.

Returns errors if an opaque heap-mutating procedure lacks a modifies clause.
-/
def transformModifiesClauses (constants : List Constant) (types : List TypeDefinition)
    (proc : Procedure) : Except (Array DiagnosticModel) Procedure :=
  match proc.body with
  | .Opaque postconds impl modifiesExprs =>
      if modifiesExprs.isEmpty then
        -- Error: opaque procedure that mutates the heap must have a modifies clause
        if hasHeapOut proc then
          .error #[proc.md.toDiagnostic
            s!"an opaque procedure that mutates the heap must have a modifies clause"]
        else
          .ok proc
      else
        let env : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                             proc.outputs.map (fun p => (p.name, p.type)) ++
                             constants.map (fun c => (c.name, c.type))
        let heapInName := "$heap_in"
        let heapOutName := "$heap_out"
        let frameCondition := buildModifiesEnsures constants env types modifiesExprs heapInName heapOutName
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

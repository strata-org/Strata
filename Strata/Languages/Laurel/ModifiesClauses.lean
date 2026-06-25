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
import Strata.Languages.Laurel.MapStmtExpr

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

Under array theory with only individual refs, callers assume a quantifier-free
(enumerated) frame and the body re-checks the pointwise frame at every exit.
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
Quantified (pointwise) frame: every allocated object the `modifies` clause does not name keeps
all of its field values across the call.

  forall $obj: Composite, $fld: Field =>
    notModified($obj, $fld) && $obj < old($heap).nextReference ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)

Returns `none` if there are no entries.
-/
def buildQuantifiedFrame (proc : Procedure) (entries : List ModifiesEntry)
    (heapIn heapOut : StmtExprMd) : StmtExprMd :=
  let objName : Identifier := "$modifies_obj"
  let fldName : Identifier := "$modifies_fld"
  let obj := mkMd <| .Var (.Local objName)
  let fld := mkMd <| .Var (.Local fldName)
  let heapCounter := mkMd <| .StaticCall "Heap..nextReference!" [heapIn]
  let objRef := mkMd <| .StaticCall "Composite..ref!" [obj]
  let objAllocated := mkMd <| .PrimitiveOp .Lt [objRef, heapCounter]
  let antecedent := if entries.isEmpty
    then objAllocated
    else
      -- Build the "not modified" precondition from all entries
      -- Combine: $obj < old($heap).nextReference && notModified($obj, $fld)
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj fld))
      mkMd <| .PrimitiveOp .And [objAllocated, notModified]
  let readIn := mkMd <| .StaticCall "readField" [heapIn, obj, fld]
  let readOut := mkMd <| .StaticCall "readField" [heapOut, obj, fld]
  let heapUnchanged := mkMd <| .PrimitiveOp .Eq [readIn, readOut]
  let implBody := mkMd <| .PrimitiveOp .Implies [antecedent, heapUnchanged]
  let innerForall := mkMd <| .Quantifier .Forall ⟨ fldName, { val := .UserDefined "Field", source := none } ⟩ none implBody
  { val := .Quantifier .Forall ⟨ objName, { val := .UserDefined "Composite", source := none } ⟩ none innerForall, source := proc.name.source }

/-- Quantifier-free frame: output `data` equals input with only the named rows
overwritten, and `nextReference` is monotone. -/
def buildEnumeratedFrame (proc : Procedure) (entries : List ModifiesEntry)
    (heapIn heapOut : StmtExprMd) : StmtExprMd :=
  let data h := mkMd <| .StaticCall "Heap..data!" [h]
  let nextRef h := mkMd <| .StaticCall "Heap..nextReference!" [h]
  let dataOut := data heapOut
  let modifiedRefs := entries.filterMap fun e => match e with | .single r => some r | _ => none
  let framedData := modifiedRefs.foldr
    (fun ref acc => mkMd <| .StaticCall "update" [acc, ref, mkMd <| .StaticCall "select" [dataOut, ref]])
    (data heapIn)
  let dataPreserved := mkMd <| .PrimitiveOp .Eq [dataOut, framedData]
  let refsMonotone := mkMd <| .PrimitiveOp .Leq [nextRef heapIn, nextRef heapOut]
  { val := .PrimitiveOp .And [dataPreserved, refsMonotone], source := proc.name.source }

/-- True when the `modifies` clause is non-empty and names only individual references
(no set-valued entries), so the enumerated frame applies. -/
def onlyIndividualRefs (entries : List ModifiesEntry) : Bool :=
  !entries.isEmpty && entries.all fun e => match e with | .single _ => true | _ => false

/-- Assert `frame` before every exit of `body` (`return` and body-block `exit`) and at its end. -/
def insertFrameChecks (proc : Procedure) (frame : StmtExprMd) (body : StmtExprMd) : StmtExprMd :=
  let src := proc.name.source
  let check : StmtExprMd := { val := .Assert { condition := frame, summary := "modifies clause" }, source := src }
  let wrap (e : StmtExprMd) : StmtExprMd := { val := .Block [check, e] none, source := e.source }
  let beforeExits := mapStmtExpr (fun e =>
    match e.val with
    | .Return _ => wrap e
    | .Exit l => if l == bodyLabel then wrap e else e
    | _ => e) body
  { val := .Block [beforeExits, check] none, source := src }

/--
Check whether a procedure has a `$heap` output parameter,
indicating it mutates the heap.
-/
def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/-- Build and attach `proc`'s modifies frame, then clear the clause. -/
def transformModifiesClauses (model: SemanticModel)
    (proc : Procedure) (useEnumeratedFrame : Bool) : Except (Array DiagnosticModel) Procedure :=
  match proc.body with
  | .External => .ok proc
  | .Opaque postconds impl modifiesExprs =>
      if hasModifiesWildcard modifiesExprs then
        .ok { proc with body := .Opaque postconds impl [] }
      else if hasHeapOut proc then
        let entries := extractModifiesEntries model modifiesExprs
        let heapIn := mkMd <| .Old (mkMd (.Var (.Local heapVarName)))
        let heapOut := mkMd <| .Var (.Local heapVarName)
        if useEnumeratedFrame && onlyIndividualRefs entries then
          -- Callers assume the quantifier-free frame; the body re-checks the
          -- pointwise frame at every exit.
          let pointwise := buildQuantifiedFrame proc entries heapIn heapOut
          let framePost : Condition :=
            { condition := buildEnumeratedFrame proc entries heapIn heapOut,
              summary := "modifies clause", free := true }
          let impl' := impl.map (insertFrameChecks proc pointwise)
          .ok { proc with body := .Opaque (postconds ++ [framePost]) impl' [] }
        else
          let framePost : Condition :=
            { condition := buildQuantifiedFrame proc entries heapIn heapOut,
              summary := "modifies clause" }
          .ok { proc with body := .Opaque (postconds ++ [framePost]) impl [] }
      else
        .ok proc
  | _ => .ok proc

/--
Transform a Laurel program: apply modifies clause transformation to all procedures.
This is a Laurel → Laurel pass that should run after heap parameterization.

Always returns the (best-effort) transformed program together with any diagnostics,
so that later passes can continue and report additional errors.
-/
def modifiesClausesTransform (model: SemanticModel) (program : Program) (useEnumeratedFrame : Bool) : Program × List DiagnosticModel :=
  let (procs', errors) := program.staticProcedures.foldl (fun (acc, errs) proc =>
    match transformModifiesClauses model proc useEnumeratedFrame with
    | .ok proc' => (acc ++ [proc'], errs)
    | .error newErrs => (acc ++ [proc], errs ++ newErrs.toList)
  ) ([], [])
  ({ program with staticProcedures := procs' }, errors)

end -- public section

/-- Pipeline pass: translate modifies clauses into ensures clauses. -/
public def modifiesClausesTransformPass : LoweringPass where
  name := "ModifiesClausesTransform"
  documentation := "Translate modifies clauses into frame conditions on the contract."
  needsResolves := true
  comesAfter := [⟨ heapParameterizationPass.meta, "the modifies pass refers to several types and variables introduced by heap parameterization: Composite, Field, $heap_in, $heap."⟩]
  run := fun options p m =>
    let (p', diags) := modifiesClausesTransform m p (useEnumeratedFrame := options.enumeratedModifiesClauses)
    (p', diags, {})

end Strata.Laurel

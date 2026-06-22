/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.MapStmtExpr

/-
Modifies clause transformation (Laurel → Laurel), run after heap parameterization:
generate a frame per `modifies` clause and clear it. Under array theory with only
individual refs, callers assume a quantifier-free frame and the body checks it per exit.
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
Pointwise frame: every allocated object the `modifies` clause does not name keeps
all of its field values across the call.

  forall $obj: Composite, $fld: Field =>
    notModified($obj) && $obj < old($heap).nextReference ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)
-/
def buildPointwiseFrame (proc : Procedure) (entries : List ModifiesEntry)
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
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj))
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
    (proc : Procedure) (useEnumeratedFrame : Bool := false) : Except (Array DiagnosticModel) Procedure :=
  match proc.body with
  | .External => .ok proc
  | .Opaque postconds impl modifiesExprs =>
      if hasModifiesWildcard modifiesExprs then
        .ok { proc with body := .Opaque postconds impl [] }
      else if hasHeapOut proc then
        let entries := extractModifiesEntries model modifiesExprs
        let heapIn := mkMd <| .Old (mkMd (.Var (.Local heapVarName)))
        let heapOut := mkMd <| .Var (.Local heapVarName)
        let pointwise := buildPointwiseFrame proc entries heapIn heapOut
        let useEnumerated := useEnumeratedFrame && onlyIndividualRefs entries
        let framePost : Condition :=
          if useEnumerated then
            { condition := buildEnumeratedFrame proc entries heapIn heapOut,
              summary := "modifies clause", free := true }
          else
            { condition := pointwise, summary := "modifies clause" }
        let impl' := if useEnumerated then impl.map (insertFrameChecks proc pointwise) else impl
        .ok { proc with body := .Opaque (postconds ++ [framePost]) impl' [] }
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
          (acc, ds ++ [diagnosticFromSource e.source s!"modifies clause entry has non-composite type '{formatHighTypeVal ty}' and will be ignored"])
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
def modifiesClausesTransform (model: SemanticModel) (program : Program) (useEnumeratedFrame : Bool := false) : Program × List DiagnosticModel :=
  let (procs', errors) := program.staticProcedures.foldl (fun (acc, errs) proc =>
    match transformModifiesClauses model proc useEnumeratedFrame with
    | .ok proc' => (acc ++ [proc'], errs)
    | .error newErrs => (acc ++ [proc], errs ++ newErrs.toList)
  ) ([], [])
  ({ program with staticProcedures := procs' }, errors)

end -- public section

/-- Pipeline pass: filter non-composite modifies clauses. -/
public def filterNonCompositeModifiesPass : LaurelPass where
  name := "FilterNonCompositeModifies"
  documentation := "Filters modifies clauses that refer to non-composite types (e.g. primitives), which cannot be heap-parameterized. Emits a warning for each removed clause. Should run before heap parameterization so that phase remains agnostic to modifies clauses."
  run := fun _ p m =>
    let (p', diags) := filterNonCompositeModifies m p
    (p', diags, {})

/-- Pipeline pass: translate modifies clauses into ensures clauses. -/
public def modifiesClausesTransformPass : LaurelPass where
  name := "ModifiesClausesTransform"
  documentation := "Translate modifies clauses into frame conditions on the contract."
  needsResolves := true
  run := fun options p m =>
    let (p', diags) := modifiesClausesTransform m p (useEnumeratedFrame := options.useArrayTheory)
    (p', diags, {})

end Strata.Laurel

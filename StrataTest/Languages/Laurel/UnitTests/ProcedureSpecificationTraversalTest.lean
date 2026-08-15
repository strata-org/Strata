/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.ConstrainedTypeElim
import Strata.Languages.Laurel.HeapAnalysis
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.LiftInstanceProcedures

import Strata.Languages.Laurel.CoreDefinitionsForLaurel
import Strata.Languages.Laurel.InferHoleTypes
import Strata.Languages.Laurel.EliminateDeterministicHoles
/-!
Focused regressions for compiler traversals over expression-bearing `Procedure`
specifications. These tests intentionally use no file-scope fields: the only fields
are ordinary composite members lowered through the heap.
-/

open Strata

namespace Strata.Laurel

private def md (expr : StmtExpr) : StmtExprMd := ⟨expr, default⟩
private def varMd (v : Variable) : VariableMd := ⟨v, default⟩
private def ty (highType : HighType) : HighTypeMd := ⟨highType, default⟩
private def localExpr (name : String) : StmtExprMd := md (.Var (.Local (mkId name)))
private def param (name : String) (highType : HighType) : Parameter :=
  { name := mkId name, type := ty highType }

private def externalProc (name : String) (inputs : List Parameter)
    (outputs : List Parameter := []) : Procedure :=
  { name := mkId name
    inputs
    outputs
    preconditions := []
    decreases := none
    body := .External }

/-- Prepend Laurel's built-in definitions, as `runLaurelPasses` does.

    Operators are `StaticCall`s to the `$`-prefixed wrapper procedures declared in
    `CoreDefinitionsForLaurel` (`$gt`, `$add`, …), so a hand-built program that
    resolves without the prelude would see every operator as an undefined callee —
    and `InferHoleTypes`, which reads the callee's parameter types to type a hole
    operand, would get nothing. -/
private def withBuiltins (program : Program) : Program :=
  { program with
    staticProcedures := coreDefinitionsForLaurel.staticProcedures ++ program.staticProcedures,
    types := coreDefinitionsForLaurel.types ++ program.types }

private def allProcedures (program : Program) : List Procedure :=
  program.staticProcedures ++ program.types.flatMap fun
    | .Composite composite => composite.instanceProcedures
    | _ => []

private def findProcedure (program : Program) (name : String) : Option Procedure :=
  program.staticProcedures.find? (·.name.text == name)

/-! ## Resolution and constrained-type elimination

Both a static and an instance procedure carry constrained types in a decreases
expression, an invoke-on quantifier, and an axiom quantifier. Resolution must
register both specification-local quantifier binders; constrained-type elimination
must then rewrite every embedded `nat` annotation to `int`.
-/

private def addConstrainedSpecifications (proc : Procedure) : Procedure :=
  -- Embed the constrained `nat` in a quantifier BINDER (`forall(v: nat) => true`) in every
  -- spec position. A quantifier binder is the prelude-free way to carry a constrained-type
  -- annotation into a spec: `v as nat` / `v is nat` resolve as errors (a constrained
  -- type unfolds to its non-composite base `int`, and `is`/`as` are composite-only), so
  -- the annotation rides the binder. ConstrainedTypeElim rewrites the
  -- binder's `nat` to `int` in all three positions (decreases, invoke-on, axiom).
  let quantified (name : String) : StmtExprMd :=
    let binder := param name (.UserDefined (mkId "nat"))
    md (.Quantifier .Forall binder none (md (.LiteralBool true)))
  { proc with
    decreases := some (quantified "decreaseValue")
    invokeOn := some (quantified "triggerValue")
    axioms := [quantified "axiomValue"] }

private def constrainedSpecificationsProgram : Program :=
  let staticProc := addConstrainedSpecifications <|
    externalProc "staticSpecifications" [param "n" (.UserDefined (mkId "nat"))]
  let instanceProc := addConstrainedSpecifications <|
    externalProc "instanceSpecifications"
      [param "self" (.UserDefined (mkId "Holder")),
       param "n" (.UserDefined (mkId "nat"))]
  { staticProcedures := [staticProc]
    staticFields := []
    types := [
      .Constrained {
        name := mkId "nat"
        base := ty .TInt
        valueName := mkId "value"
        constraint := md (.LiteralBool true)
        witness := md (.LiteralInt 0) },
      .Composite {
        name := mkId "Holder"
        extending := []
        fields := []
        instanceProcedures := [instanceProc] }
    ] }

private def specificationsBindersRegistered (model : SemanticModel) (proc : Procedure) : Bool :=
  procedureSpecificationExprs proc
    |>.flatMap (collectStmtExprList fun expr => match expr.val with
      | .Quantifier _ binder _ _ => [binder.name]
      | _ => [])
    |>.all fun name => match model.get? name with
      | some (.quantifierVar registeredName type) =>
          registeredName.uniqueId == name.uniqueId && match type.val with
            | .UserDefined typeName =>
                typeName.text == "nat" && match model.get? typeName with
                  | some (.constrainedType constrained) =>
                      constrained.name.uniqueId == typeName.uniqueId
                  | _ => false
            | _ => false
      | _ => false

private def expressionContainsNat (expr : StmtExprMd) : Bool :=
  anyStmtExpr (fun node =>
    let isNat (t : HighTypeMd) := match t.val with
      | .UserDefined name => name.text == "nat"
      | _ => false
    match node.val with
    | .AsType _ t | .IsType _ t => isNat t
    | .Quantifier _ binder _ _ => isNat binder.type
    | _ => false) expr

private def isIntType (t : HighTypeMd) : Bool :=
  match t.val with
  | .TInt => true
  | _ => false

private def constrainedSpecificationsHasExpectedTypes (proc : Procedure) : Bool :=
  let quantifierBinderIsInt (expr : StmtExprMd) := match expr.val with
    | .Quantifier _ binder _ _ => isIntType binder.type
    | _ => false
  let decreasesIsInt := match proc.decreases with
    | some expr => quantifierBinderIsInt expr
    | none => false
  let invokeOnIsInt := match proc.invokeOn with
    | some expr => quantifierBinderIsInt expr
    | none => false
  let axiomsAreInt := match proc.axioms with
    | [axiomExpr] => quantifierBinderIsInt axiomExpr
    | _ => false
  decreasesIsInt && invokeOnIsInt && axiomsAreInt

private def hasPopulatedSpecificationsShape (proc : Procedure) : Bool :=
  proc.decreases.isSome && proc.invokeOn.isSome && proc.axioms.length == 1

private def checkConstrainedSpecifications : IO Unit := do
  let resolved := resolve constrainedSpecificationsProgram
  let originalProcedures := allProcedures resolved.program
  let lowered := (constrainedTypeElim resolved.model resolved.program).1
  let loweredProcedures := (allProcedures lowered).filter fun proc =>
    proc.name.text == "staticSpecifications" || proc.name.text == "instanceSpecifications"
  let hasLoweredInstance := lowered.types.any fun
    | .Composite composite => !composite.instanceProcedures.isEmpty
    | _ => false
  IO.println s!"resolution errors: {resolved.errors.size}"
  IO.println s!"specifications binders registered: {
    originalProcedures.length == 2 &&
      originalProcedures.all fun proc =>
        hasPopulatedSpecificationsShape proc && specificationsBindersRegistered resolved.model proc}"
  IO.println s!"specifications constrained types eliminated: {
    loweredProcedures.length == 2 && loweredProcedures.all fun proc =>
      hasPopulatedSpecificationsShape proc && constrainedSpecificationsHasExpectedTypes proc &&
        (procedureSpecificationExprs proc).all fun expr => !expressionContainsNat expr}"
  IO.println s!"instance procedure covered: {hasLoweredInstance}"

/--
info: resolution errors: 0
specifications binders registered: true
specifications constrained types eliminated: true
instance procedure covered: true
-/
#guard_msgs in
#eval checkConstrainedSpecifications

/-! ## Heap-effect classification and heap lowering

A read-only procedure and a heap-writing procedure each mention a composite
field only in decreases/invoke-on/axiom specifications. The analysis must classify
those reads, and both heap-parameterization branches must eliminate the field
syntax from every specification expression.
-/

private def fieldRead (owner field : String) : StmtExprMd :=
  md (.Var (.Field (localExpr owner) (mkId field)))

private def addHeapSpecifications (proc : Procedure) : Procedure :=
  -- Park the composite field-read `cell#value` directly in every spec position. `is` is
  -- composite-target-only, so an `is int` over the field read resolves as an error; the
  -- bare field read carries the same heap-effect + field-syntax that this test exercises
  -- heap-parameterization lowering on.
  let value := fieldRead "cell" "value"
  { proc with
    decreases := some value
    invokeOn := some value
    axioms := [value] }

private def effectExpr (callee : String) : StmtExprMd :=
  md (.StaticCall (mkId callee) [fieldRead "cell" "value"])

private def effectProcedure (body : Body) : Procedure :=
  { name := mkId "effectProcedure"
    inputs := []
    outputs := []
    preconditions := [{ condition := effectExpr "precondition" }]
    decreases := some (effectExpr "decreases")
    invokeOn := some (effectExpr "invokeOn")
    axioms := [effectExpr "axiom"]
    body }

private def hasExpectedEffects (expectedCallees : List String) (proc : Procedure) : Bool :=
  let result := analyzeProc proc
  result.readsHeapDirectly &&
    result.callees.length == expectedCallees.length &&
    expectedCallees.all fun name => result.callees.any (·.text == name)

#guard hasExpectedEffects
  ["transparent", "precondition", "decreases", "invokeOn", "axiom"]
  (effectProcedure (.Transparent (effectExpr "transparent")))

#guard hasExpectedEffects
  ["postcondition", "implementation", "modifies", "precondition", "decreases", "invokeOn", "axiom"]
  (effectProcedure (.Opaque
    [{ condition := effectExpr "postcondition" }]
    (some (effectExpr "implementation"))
    [{ targets := [effectExpr "modifies"] }]))

#guard hasExpectedEffects
  ["postcondition", "precondition", "decreases", "invokeOn", "axiom"]
  (effectProcedure (.Abstract [{ condition := effectExpr "postcondition" }]))

#guard hasExpectedEffects
  ["precondition", "decreases", "invokeOn", "axiom"]
  (effectProcedure .External)

private def opaqueModifiesResult : AnalysisResult :=
  analyzeProc {
    name := mkId "opaqueModifies"
    inputs := []
    outputs := []
    preconditions := []
    decreases := none
    body := .Opaque [] none [{ targets := [localExpr "cell"] }] }

#guard opaqueModifiesResult.readsHeapDirectly
#guard opaqueModifiesResult.writesHeapDirectly
#guard opaqueModifiesResult.callees.isEmpty

private def heapSpecificationsProgram : Program :=
  let cellParam := param "cell" (.UserDefined (mkId "Cell"))
  let reader := addHeapSpecifications (externalProc "reader" [cellParam])
  let assignment := md (.Assign
    [varMd (.Field (localExpr "cell") (mkId "value"))]
    (md (.LiteralInt 1)))
  let writer := addHeapSpecifications {
    externalProc "writer" [cellParam] with
    body := .Opaque [] (some assignment) [{ targets := [localExpr "cell"] }] }
  { staticProcedures := [reader, writer]
    staticFields := []
    types := [.Composite {
      name := mkId "Cell"
      extending := []
      fields := [{ name := mkId "value", isMutable := true, type := ty .TInt }]
      instanceProcedures := [] }] }

private def specificationsHasFieldRead (proc : Procedure) : Bool :=
  (procedureSpecificationExprs proc).any fun expr =>
    anyStmtExpr (fun node => match node.val with
      | .Var (.Field _ _) => true
      | _ => false) expr

private def isExpectedHeapRead (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .StaticCall unbox [read] =>
      unbox.text == "$Box..intVal!" && match read.val with
        | .StaticCall readField [heap, receiver, field] =>
            readField.text == "readField" &&
              (match heap.val with
              | .Var (.Local name) => name.text == "$heap"
              | _ => false) &&
              (match receiver.val with
              | .Var (.Local name) => name.text == "cell"
              | _ => false) &&
              (match field.val with
              | .StaticCall name [] => name.text == "Cell.value"
              | _ => false)
        | _ => false
  | _ => false

private def heapSpecificationsHasExpectedValues (proc : Procedure) : Bool :=
  let decreasesIsExpected := match proc.decreases with
    | some expr => isExpectedHeapRead expr
    | none => false
  let invokeOnIsExpected := match proc.invokeOn with
    | some expr => isExpectedHeapRead expr
    | none => false
  let axiomsAreExpected := match proc.axioms with
    | [axiomExpr] => isExpectedHeapRead axiomExpr
    | _ => false
  decreasesIsExpected && invokeOnIsExpected && axiomsAreExpected

private def checkHeapSpecifications : IO Unit := do
  let resolved := resolve heapSpecificationsProgram
  let readerBefore := (findProcedure resolved.program "reader").get!
  let writerBefore := (findProcedure resolved.program "writer").get!
  let readerAnalysis := analyzeProc readerBefore
  let writerAnalysis := analyzeProc writerBefore
  let specificationsBase := { readerBefore with
    body := .External, preconditions := [], decreases := none, invokeOn := none, axioms := [] }
  let fieldExpr := readerBefore.decreases.get!
  let preconditionAnalysis := analyzeProc {
    specificationsBase with preconditions := [{ condition := fieldExpr }] }
  let decreasesAnalysis := analyzeProc { specificationsBase with decreases := some fieldExpr }
  let invokeOnAnalysis := analyzeProc {
    specificationsBase with invokeOn := readerBefore.invokeOn }
  let axiomAnalysis := analyzeProc { specificationsBase with axioms := readerBefore.axioms }
  let everySpecificationsFieldRead :=
    [preconditionAnalysis, decreasesAnalysis, invokeOnAnalysis, axiomAnalysis].all fun result =>
      result.readsHeapDirectly && !result.writesHeapDirectly
  let lowered ← IO.ofExcept (heapParameterization resolved.model resolved.program)
  let readerAfter := (findProcedure lowered "reader").get!
  let writerAfter := (findProcedure lowered "writer").get!
  -- The heap is a file-scope global, threaded into signatures by
  -- `GlobalParameterization`. This pass declares the global and rewrites field
  -- accesses -- including those in specifications, which is what this test is
  -- about -- but adds no parameters, so a `$heap` param here would be a bug.
  -- Threading itself is covered by GlobalParameterizationTest and end to end.
  let hasHeapParam (proc : Procedure) :=
    proc.inputs.any (·.name.text == "$heap") || proc.outputs.any (·.name.text == "$heap")
  let heapGlobalDeclared := lowered.staticFields.any (·.name.text == "$heap")
  IO.println s!"resolution errors: {resolved.errors.size}"
  IO.println s!"reader classified: {
    readerAnalysis.readsHeapDirectly && !readerAnalysis.writesHeapDirectly &&
      everySpecificationsFieldRead}"
  IO.println s!"writer classified: {writerAnalysis.readsHeapDirectly && writerAnalysis.writesHeapDirectly}"
  IO.println s!"heap global declared: {heapGlobalDeclared}"
  IO.println s!"reader specifications lowered: {!hasHeapParam readerAfter &&
    !specificationsHasFieldRead readerAfter &&
    heapSpecificationsHasExpectedValues readerAfter}"
  IO.println s!"writer specifications lowered: {!hasHeapParam writerAfter &&
    !specificationsHasFieldRead writerAfter &&
    heapSpecificationsHasExpectedValues writerAfter}"

/--
info: resolution errors: 0
reader classified: true
writer classified: true
heap global declared: true
reader specifications lowered: true
writer specifications lowered: true
-/
#guard_msgs in
#eval checkHeapSpecifications

/-! ## Calls in heap-aware specifications

Heap-reading calls remain ordinary calls with an added heap argument. Calls to
heap-writing procedures must also remain calls in specifications: executable
lowering would synthesize an assignment block and obscure the source-level
"procedure call in a contract" diagnostic.
-/

private def specificationCallProgram : Program :=
  let cellParam := param "cell" (.UserDefined (mkId "Cell"))
  let mutator := {
    externalProc "mutator" [cellParam] [param "$result" .TInt] with
    body := .Opaque [] none [{ targets := [fieldRead "cell" "value"] }] }
  let reader := {
    externalProc "heapReader" [cellParam] [param "$result" .TInt] with
    body := .Opaque [] (some (fieldRead "cell" "value")) [] }
  let writerCall := md (.StaticCall (mkId "mutator") [localExpr "cell"])
  let readerCall := md (.StaticCall (mkId "heapReader") [localExpr "cell"])
  let caller := {
    externalProc "specificationCaller" [cellParam] with
    decreases := some writerCall
    invokeOn := some readerCall
    axioms := [writerCall, readerCall]
    body := .Opaque [] none [] }
  { staticProcedures := [mutator, reader, caller]
    staticFields := []
    types := [.Composite {
      name := mkId "Cell"
      extending := []
      fields := [{ name := mkId "value", isMutable := true, type := ty .TInt }]
      instanceProcedures := [] }] }

/-- A call in a specification is left as an ordinary call over its source arguments.
    The `$heap` argument is appended later, by `GlobalParameterization`; what matters
    here is that traversing a specification neither drops the call nor rewrites it
    into something impure. -/
private def isHeapAwareCall (calleeName : String) (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .StaticCall callee [cell] =>
      callee.text == calleeName &&
        (match cell.val with
        | .Var (.Local name) => name.text == "cell"
        | _ => false)
  | _ => false

private def containsAssignment (expr : StmtExprMd) : Bool :=
  anyStmtExpr (fun node => match node.val with
    | .Assign _ _ => true
    | _ => false) expr

private def impureSpecificationCallProgram : Program :=
  let cellParam := param "cell" (.UserDefined (mkId "Cell"))
  let mutator := {
    externalProc "mutator" [cellParam] [param "$result" .TInt] with
    body := .Opaque [] none [{ targets := [fieldRead "cell" "value"] }] }
  let writerCall := md (.StaticCall (mkId "mutator") [localExpr "cell"])
  let caller := {
    externalProc "caller" [cellParam] [param "$result" .TInt] with
    decreases := some writerCall
    axioms := [writerCall]
    body := .Opaque [] (some (md (.LiteralInt 0))) [] }
  { staticProcedures := [mutator, caller]
    staticFields := []
    types := [.Composite {
      name := mkId "Cell"
      extending := []
      fields := [{ name := mkId "value", isMutable := true, type := ty .TInt }]
      instanceProcedures := [] }] }

private def checkSpecificationCalls : IO Unit := do
  let resolved := resolve specificationCallProgram
  let lowered ← IO.ofExcept (heapParameterization resolved.model resolved.program)
  let caller := (findProcedure lowered "specificationCaller").get!
  let callsRemainPure := match caller.decreases, caller.invokeOn, caller.axioms with
    | some writerMeasure, some readerTrigger, [writerAxiom, readerAxiom] =>
        isHeapAwareCall "mutator" writerMeasure &&
          isHeapAwareCall "heapReader" readerTrigger &&
          isHeapAwareCall "mutator" writerAxiom &&
          isHeapAwareCall "heapReader" readerAxiom &&
          [writerMeasure, readerTrigger, writerAxiom, readerAxiom].all
            fun expr => !containsAssignment expr
    | _, _, _ => false
  let (_, diagnostics, _, _) ← translateWithLaurel {} impureSpecificationCallProgram
  let messages := diagnostics.map fun diagnostic => (Std.format diagnostic.message).pretty
  let reportsSourceCall := messages.any
    (·.contains "calling multi-output procedure 'mutator'")
  let reportsSyntheticAssignment := messages.any
    (·.contains "destructive assignments are not supported in transparent bodies or contracts")
  IO.println s!"writer call diagnostics: {resolved.errors.size == 2}"
  IO.println s!"specification calls remain pure: {callsRemainPure}"
  IO.println s!"source call diagnostic preserved: {reportsSourceCall && !reportsSyntheticAssignment}"

/--
info: writer call diagnostics: true
specification calls remain pure: true
source call diagnostic preserved: true
-/
#guard_msgs in
#eval checkSpecificationCalls

/-! ## Lifted calls in instance-procedure axioms

An axiom attached to an instance procedure calls a sibling instance procedure.
After lifting, the axiom must contain a static call to the mangled target and
must pass `self` as its first argument.
-/

private def instanceAxiomProgram : Program :=
  let selfParam := param "self" (.UserDefined (mkId "Cell"))
  let predicate := externalProc "predicate" [selfParam] [param "$result" .TBool]
  let owner := {
    externalProc "owner" [selfParam] with
    axioms := [md (.InstanceCall (localExpr "self") (mkId "predicate") [])] }
  { staticProcedures := []
    staticFields := []
    types := [.Composite {
      name := mkId "Cell"
      extending := []
      fields := []
      instanceProcedures := [predicate, owner] }] }

private def liftedAxiomCallIsStatic (proc : Procedure) : Bool :=
  match proc.axioms with
  | [ax] => match ax.val with
    | .StaticCall callee [receiver] =>
        callee.text == "Cell$predicate" && match receiver.val with
          | .Var (.Local self) => self.text == "self"
          | _ => false
    | _ => false
  | _ => false

private def checkLiftedInstanceAxiom : IO Unit := do
  let resolved := resolve instanceAxiomProgram
  let (lifted, _) := liftInstanceProcedures resolved.model resolved.program
  let owner := (findProcedure lifted "Cell$owner").get!
  let instancesCleared := lifted.types.all fun
    | .Composite composite => composite.instanceProcedures.isEmpty
    | _ => true
  IO.println s!"resolution errors: {resolved.errors.size}"
  IO.println s!"instance axiom call rewritten: {liftedAxiomCallIsStatic owner}"
  IO.println s!"instance procedures cleared: {instancesCleared}"

/--
info: resolution errors: 0
instance axiom call rewritten: true
instance procedures cleared: true
-/
#guard_msgs in
#eval checkLiftedInstanceAxiom

/-! ## Empty specifications

Procedures without optional specifications stay specification-free through each
traversal, with one exception: heap lowering synthesizes the free
heap-well-formedness preconditions for composite inputs (one per composite
input) — and *only* those. No traversal introduces any other specification. The
instance procedure is intentionally lifted, so its name and location change
while its (still empty, modulo those synthesized preconditions) specifications
remain unchanged.
-/

private def emptySpecificationsProgram : Program :=
  let cellParam := param "cell" (.UserDefined (mkId "Cell"))
  let assignment := md (.Assign
    [varMd (.Field (localExpr "cell") (mkId "value"))]
    (md (.LiteralInt 1)))
  let staticProc := {
    externalProc "staticEmptySpecifications" [cellParam] with
    body := .Opaque [] (some assignment) [{ targets := [localExpr "cell"] }] }
  let instanceProc := {
    externalProc "instanceEmptySpecifications"
      [param "self" (.UserDefined (mkId "Cell"))]
      [param "$result" .TInt] with
    body := .Transparent (fieldRead "self" "value") }
  { staticProcedures := [staticProc]
    staticFields := []
    types := [
      .Constrained {
        name := mkId "nat"
        base := ty .TInt
        valueName := mkId "value"
        constraint := md (.LiteralBool true)
        witness := md (.LiteralInt 0) },
      .Composite {
        name := mkId "Cell"
        extending := []
        fields := [{ name := mkId "value", isMutable := true, type := ty .TInt }]
        instanceProcedures := [instanceProc] }
    ] }

private def hasEmptySpecifications (proc : Procedure) : Bool :=
  proc.preconditions.isEmpty && proc.decreases.isNone &&
    proc.invokeOn.isNone && proc.axioms.isEmpty

private def isHeapWfPrecond (c : Condition) : Bool :=
  match c.condition.val with
  | .StaticCall lt [lhs, rhs] =>
    lt.text == "$intLt" &&
      (match lhs.val with
       | .StaticCall ref _ => ref.text == "Composite..ref!"
       | _ => false) &&
      (match rhs.val with
       | .StaticCall next _ => next.text == "Heap..nextReference!"
       | _ => false)
  | _ => false

private def addsOnlyHeapWfPreconds (proc : Procedure) (expected : Nat) : Bool :=
  proc.preconditions.length == expected &&
    proc.preconditions.all isHeapWfPrecond &&
    proc.decreases.isNone && proc.invokeOn.isNone && proc.axioms.isEmpty

private def findAnyProcedure (program : Program) (name : String) : Option Procedure :=
  (allProcedures program).find? (·.name.text == name)

private def checkEmptySpecifications : IO Unit := do
  let resolved := resolve emptySpecificationsProgram

  -- The unrelated `nat` declaration ensures this reaches `elimProc` rather than
  -- constrained-type elimination's empty-map fast path.
  let constrained := (constrainedTypeElim resolved.model resolved.program).1
  let staticAfterConstrained :=
    (findAnyProcedure constrained "staticEmptySpecifications").get!
  let instanceAfterConstrained :=
    (findAnyProcedure constrained "instanceEmptySpecifications").get!

  let staticBeforeHeap :=
    (findAnyProcedure resolved.program "staticEmptySpecifications").get!
  let instanceBeforeHeap :=
    (findAnyProcedure resolved.program "instanceEmptySpecifications").get!
  let staticAnalysis := analyzeProc staticBeforeHeap
  let instanceAnalysis := analyzeProc instanceBeforeHeap

  -- Heap parameterization expects instance procedures to have been lifted. The
  -- writer and reader bodies force its write and read branches, respectively.
  let (lifted, _) := liftInstanceProcedures resolved.model resolved.program
  let staticAfterLift :=
    (findAnyProcedure lifted "staticEmptySpecifications").get!
  let instanceAfterLift :=
    (findAnyProcedure lifted "Cell$instanceEmptySpecifications").get!
  let liftedResolved := resolve lifted
  let heapLowered ← IO.ofExcept
    (heapParameterization liftedResolved.model liftedResolved.program)
  let staticAfterHeap :=
    (findAnyProcedure heapLowered "staticEmptySpecifications").get!
  let instanceAfterHeap :=
    (findAnyProcedure heapLowered "Cell$instanceEmptySpecifications").get!
  -- See the note in `checkHeapSpecifications`: this pass declares the `$heap`
  -- global and rewrites field accesses; `GlobalParameterization` turns it into
  -- parameters afterwards, so neither procedure should carry one yet.
  let hasHeapParam (proc : Procedure) :=
    proc.inputs.any (·.name.text == "$heap") || proc.outputs.any (·.name.text == "$heap")

  IO.println s!"resolution errors: {resolved.errors.size}"
  IO.println s!"constrained-type elimination preserves empty specifications: {
    hasEmptySpecifications staticAfterConstrained &&
      hasEmptySpecifications instanceAfterConstrained}"
  IO.println s!"heap analysis reaches writer and reader branches: {
    staticAnalysis.writesHeapDirectly && instanceAnalysis.readsHeapDirectly &&
      !instanceAnalysis.writesHeapDirectly}"
  -- Heap lowering adds one free heap-well-formedness precondition per composite
  -- input. Both procedures take a single `Cell` input (`cell` / `self`), so each
  -- gains exactly one; `$heap` itself is a datatype, not a composite, so it adds
  -- none. Assert that positively — the pass adds exactly those preconditions and
  -- no other specifications.
  IO.println s!"heap lowering adds exactly the heap-wf preconditions: {
    liftedResolved.errors.isEmpty &&
    addsOnlyHeapWfPreconds staticAfterHeap 1 &&
    addsOnlyHeapWfPreconds instanceAfterHeap 1 &&
      !hasHeapParam staticAfterHeap && !hasHeapParam instanceAfterHeap}"
  IO.println s!"instance lifting preserves empty specifications: {
    hasEmptySpecifications staticAfterLift && hasEmptySpecifications instanceAfterLift}"

/--
info: resolution errors: 0
constrained-type elimination preserves empty specifications: true
heap analysis reaches writer and reader branches: true
heap lowering adds exactly the heap-wf preconditions: true
instance lifting preserves empty specifications: true
-/
#guard_msgs in
#eval checkEmptySpecifications

/-! ## Holes in procedure contracts

Hole inference and deterministic-hole elimination must traverse contracts as
well as implementations. The comparison hole models `requires x > <?>`; the
bare requires, axiom, and abstract postcondition additionally pin the Boolean
expected type of proposition-valued positions.
-/

private def contractHoleProgram : Program :=
  let hole := md (.Hole true none)
  let comparison := md (.StaticCall (mkId Operation.Gt.procName) [localExpr "x", hole])
  let decreases := md (.StaticCall (mkId Operation.Add.procName) [localExpr "x", hole])
  let invokeOn := md (.StaticCall (mkId "triggerTarget") [hole])
  let staticProc := {
    externalProc "contractHoles" [param "x" .TInt] with
    preconditions := [{ condition := comparison }, { condition := hole }]
    decreases := some decreases
    invokeOn := some invokeOn
    body := .Opaque [{ condition := hole }] none []
    -- Second axiom: a bool-valued proposition that gives its hole an INT type-context,
    -- via `$gt(<?>, 0)`. `is` is composite-target-only, so a primitive `is int` resolves
    -- as an error. `$gt` is bool-valued yet types the hole `int` through the operator's
    -- parameter, preserving the int-hole count this test pins.
    axioms := [hole, md (.StaticCall (mkId Operation.Gt.procName) [hole, md (.LiteralInt 0)])] }
  let instanceProc := {
    externalProc "instanceContractHoles"
      [param "self" (.UserDefined (mkId "ContractHolder"))] with
    preconditions := [{ condition := hole }]
    body := .Abstract [{ condition := hole }]
    axioms := [hole] }
  { staticProcedures := [externalProc "triggerTarget" [param "value" .TInt], staticProc]
    staticFields := []
    types := [.Composite {
      name := mkId "ContractHolder"
      extending := []
      fields := []
      instanceProcedures := [instanceProc] }] }

private def bodyContractExprs (proc : Procedure) : List StmtExprMd :=
  match proc.body with
  | .Opaque postconditions _ _ | .Abstract postconditions =>
      postconditions.map (·.condition)
  | .Transparent _ | .External => []

private def containsDeterministicHole (expr : StmtExprMd) : Bool :=
  anyStmtExpr (fun node => match node.val with
    | .Hole true _ => true
    | _ => false) expr

private def hasSingleOutputType (expected : HighType) (proc : Procedure) : Bool :=
  match proc.outputs with
  | [output] => output.type.val == expected
  | _ => false


private def isLocalNamed (expected : String) (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .Var (.Local name) => name.text == expected
  | _ => false

private def generatedCallMatches (program : Program) (expectedType : HighType)
    (expectedInput : String) (expr : StmtExprMd) : Bool :=
  match expr.val with
  | .StaticCall callee [argument] =>
      callee.text.startsWith "$hole_" && isLocalNamed expectedInput argument &&
        match findProcedure program callee.text with
        | some generated =>
            generated.inputs.length == 1 &&
              generated.inputs[0]!.name.text == expectedInput &&
              hasSingleOutputType expectedType generated
        | none => false
  | _ => false

private def staticContractPositionsMatch (program : Program) (proc : Procedure) : Bool :=
  match proc.preconditions, proc.decreases, proc.invokeOn, proc.body, proc.axioms with
  | [comparison, bareRequires], some decreases, some invokeOn,
      .Opaque [postcondition] none [], [bareAxiom, typedAxiom] =>
    let comparisonMatches := match comparison.condition.val with
      | .StaticCall callee [lhs, holeCall] =>
          callee.text == Operation.Gt.procName &&
            isLocalNamed "x" lhs && generatedCallMatches program .TInt "x" holeCall
      | _ => false
    let requiresMatches := generatedCallMatches program .TBool "x" bareRequires.condition
    let decreasesMatches := match decreases.val with
      | .StaticCall callee [lhs, holeCall] =>
          callee.text == Operation.Add.procName &&
            isLocalNamed "x" lhs && generatedCallMatches program .TInt "x" holeCall
      | _ => false
    let invokeOnMatches := match invokeOn.val with
      | .StaticCall callee [holeCall] =>
          callee.text == "triggerTarget" && generatedCallMatches program .TInt "x" holeCall
      | _ => false
    let postconditionMatches :=
      generatedCallMatches program .TBool "x" postcondition.condition
    let bareAxiomMatches := generatedCallMatches program .TBool "x" bareAxiom
    let typedAxiomMatches := match typedAxiom.val with
      | .StaticCall callee [holeCall, rhs] =>
          callee.text == Operation.Gt.procName &&
            (match rhs.val with | .LiteralInt 0 => true | _ => false) &&
            generatedCallMatches program .TInt "x" holeCall
      | _ => false
    comparisonMatches && requiresMatches && decreasesMatches && invokeOnMatches &&
      postconditionMatches && bareAxiomMatches && typedAxiomMatches
  | _, _, _, _, _ => false

private def instanceContractPositionsMatch (program : Program) (proc : Procedure) : Bool :=
  match proc.preconditions, proc.decreases, proc.invokeOn, proc.body, proc.axioms with
  | [requires], none, none, .Abstract [postcondition], [axiomExpr] =>
      generatedCallMatches program .TBool "self" requires.condition &&
        generatedCallMatches program .TBool "self" postcondition.condition &&
        generatedCallMatches program .TBool "self" axiomExpr
  | _, _, _, _, _ => false
private def checkContractHoles : IO Unit := do
  let resolved := resolve (withBuiltins contractHoleProgram)
  let (inferred, diagnostics, _) := inferHoleTypes resolved.model resolved.program
  let (eliminated, _) := eliminateDeterministicHoles inferred
  let staticProc := (findProcedure eliminated "contractHoles").get!
  let instanceProc := (findAnyProcedure eliminated "instanceContractHoles").get!
  let staticContracts := procedureSpecificationExprs staticProc ++ bodyContractExprs staticProc
  let instanceContracts := procedureSpecificationExprs instanceProc ++ bodyContractExprs instanceProc
  let contractExprs := staticContracts ++ instanceContracts
  let generated := eliminated.staticProcedures.filter (·.name.text.startsWith "$hole_")
  let intHoles := generated.filter (hasSingleOutputType .TInt)
  let boolHoles := generated.filter (hasSingleOutputType .TBool)
  let positionsAndCallsPreserved :=
    staticContractPositionsMatch eliminated staticProc &&
      instanceContractPositionsMatch eliminated instanceProc
  IO.println s!"resolution errors: {resolved.errors.size}"
  IO.println s!"hole inference diagnostics: {diagnostics.length}"
  IO.println s!"contract positions, call types, and skipProof preserved: {
    positionsAndCallsPreserved}"
  IO.println s!"contract holes eliminated: {
    contractExprs.all fun expr => !containsDeterministicHole expr}"
  IO.println s!"generated hole set preserved: {
    generated.length == 10 && intHoles.length == 4 && boolHoles.length == 6}"

/--
info: resolution errors: 0
hole inference diagnostics: 0
contract positions, call types, and skipProof preserved: true
contract holes eliminated: true
generated hole set preserved: true
-/
#guard_msgs in
#eval checkContractHoles

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.PushOldInward
import Strata.Languages.Laurel.ContractPass
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

private def mkMd (e : StmtExpr) (source : FileRange) : StmtExprMd := { val := e, source }

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

/-- Whether a `throwsOn` case contributes an exceptional heap frame.

A case contributes one only when it names at least one target *and* none of them is the
wildcard. The two exclusions mean the same thing — "this path may change anything" — and
the honest encoding of that is no frame at all, matching how a normal `modifies *` is
handled.

The wildcard has to be excluded *here* rather than left to the frame builder.
`extractModifiesEntries` drops `StmtExpr.All` as non-heap-relevant, so a wildcard that
got this far would reach `buildQuantifiedFrame` as an empty entry list and produce a
frame asserting that *nothing* changed — the exact inverse of what the wildcard means.
On a bodiless procedure that frame is assumed rather than checked, so a caller would
conclude the heap was untouched on a path the callee declared it might change
arbitrarily.

No surface produces a wildcard in a case today (the grammar has no case-frame
wildcard form), but `ThrowsOnBlock.modifies` is public AST and front ends construct
Laurel programs directly rather than through the parser. -/
def caseContributesFrame (blk : ThrowsOnBlock) : Bool :=
  !blk.modifies.isEmpty && !hasModifiesWildcard blk.modifies

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
        .field objExpr (mkMd (.StaticCall qualifiedName []) expr.source)
    | _ => classifyModifiesType expr (computeExprType model expr).val
/--
Build the "obj is not modified" condition for a single modifies entry as a Laurel StmtExpr.
- For a single Composite `e`: `$obj != e`
- For a Set Composite `e`: `!(select(e, $obj))` i.e. $obj is not in the set
- For a field `(o, f)`: `!($obj == o && $fld == f)` i.e. the quantified
  `($obj, $fld)` pair is not the modified `(object, field)` pair (field-granular)
-/
def buildNotModifiedForEntry (obj : StmtExprMd) (fld : StmtExprMd) (entry : ModifiesEntry) (source : FileRange) : StmtExprMd :=
  match entry with
  | .single expr =>
    mkMd (.StaticCall (mkId Operation.Neq.procName) [obj, expr]) source
  | .set expr =>
    let membership := mkMd (.StaticCall "select" [expr, obj]) source
    mkMd (.StaticCall (mkId Operation.Not.procName) [membership]) source
  | .field objExpr fieldConst =>
    let objEq := mkMd (.StaticCall (mkId Operation.Eq.procName) [obj, objExpr]) source
    let fldEq := mkMd (.StaticCall (mkId Operation.Eq.procName) [fld, fieldConst]) source
    let bothMatch := mkMd (.StaticCall (mkId Operation.And.procName) [objEq, fldEq]) source
    mkMd (.StaticCall (mkId Operation.Not.procName) [bothMatch]) source

/-- Conjoin a list of StmtExprs with `&&`. -/
def conjoinAll (exprs : List StmtExprMd) (source : FileRange) : StmtExprMd :=
  match exprs with
  | [] => mkMd (.LiteralBool true) source
  | [single] => single
  | first :: rest =>
    rest.foldl (fun acc e => mkMd (.StaticCall (mkId Operation.And.procName) [acc, e]) source) first

/--
Quantified (pointwise) frame: every allocated object the `modifies` clause does not name keeps
all of its field values across the call.

  forall $obj: Composite, $fld: Field =>
    notModified($obj, $fld) && $obj < old($heap).nextReference ==> readField(old($heap), $obj, $fld) == readField($heap, $obj, $fld)

Returns `none` if there are no entries.
-/
def buildQuantifiedFrame (proc : Procedure) (entries : List ModifiesEntry)
    (heapIn heapOut : StmtExprMd) : StmtExprMd :=
  let src := proc.name.source
  let objName : Identifier := "$modifies_obj"
  let fldName : Identifier := "$modifies_fld"
  let obj := mkMd (.Var (.Local objName)) src
  let fld := mkMd (.Var (.Local fldName)) src
  let heapCounter := mkMd (.StaticCall "Heap..nextReference!" [heapIn]) src
  let objRef := mkMd (.StaticCall "Composite..ref!" [obj]) src
  let objAllocated := mkMd (.StaticCall (mkId Operation.Lt.procName) [objRef, heapCounter]) src
  let antecedent := if entries.isEmpty
    then objAllocated
    else
      -- Build the "not modified" precondition from all entries
      -- Combine: $obj < old($heap).nextReference && notModified($obj, $fld)
      let notModified := conjoinAll (entries.map (buildNotModifiedForEntry obj fld · src)) src
      mkMd (.StaticCall (mkId Operation.And.procName) [objAllocated, notModified]) src
  let readIn := mkMd (.StaticCall "readField" [heapIn, obj, fld]) src
  let readOut := mkMd (.StaticCall "readField" [heapOut, obj, fld]) src
  let heapUnchanged := mkMd (.StaticCall (mkId Operation.Eq.procName) [readIn, readOut]) src
  let implBody := mkMd (.StaticCall (mkId Operation.Implies.procName) [antecedent, heapUnchanged]) src
  let innerForall := mkMd (.Quantifier .Forall ⟨ fldName, { val := .UserDefined "Field", source := src } ⟩ none implBody) src
  { val := .Quantifier .Forall ⟨ objName, { val := .UserDefined "Composite", source := src } ⟩ none innerForall, source := src }

/-- Quantifier-free frame: output `data` equals input with only the named rows
overwritten, and `nextReference` is monotone. -/
def buildEnumeratedFrame (proc : Procedure) (entries : List ModifiesEntry)
    (heapIn heapOut : StmtExprMd) : StmtExprMd :=
  let src := proc.name.source
  let data h := mkMd (.StaticCall "Heap..data!" [h]) src
  let nextRef h := mkMd (.StaticCall "Heap..nextReference!" [h]) src
  let dataOut := data heapOut
  let modifiedRefs := entries.filterMap fun e => match e with | .single r => some r | _ => none
  let framedData := modifiedRefs.foldr
    (fun ref acc => mkMd (.StaticCall "update" [acc, ref, mkMd (.StaticCall "select" [dataOut, ref]) src]) src)
    (data heapIn)
  let dataPreserved := mkMd (.StaticCall (mkId Operation.Eq.procName) [dataOut, framedData]) src
  let refsMonotone := mkMd (.StaticCall (mkId Operation.Leq.procName) [nextRef heapIn, nextRef heapOut]) src
  { val := .StaticCall (mkId Operation.And.procName) [dataPreserved, refsMonotone], source := src }

/-- True when the `modifies` clause is non-empty and names only individual references
(no set-valued entries), so the enumerated frame applies. -/
def onlyIndividualRefs (entries : List ModifiesEntry) : Bool :=
  !entries.isEmpty && entries.all fun e => match e with | .single _ => true | _ => false

/--
Check whether a procedure has a `$heap` output parameter,
indicating it mutates the heap.
-/
def hasHeapOut (proc : Procedure) : Bool :=
  proc.outputs.any (fun p => p.name.text == "$heap")

/-- Build and attach `proc`'s modifies frame, then clear the clause. -/
def transformModifiesClauses (model: SemanticModel)
    (proc : Procedure) (useEnumeratedFrame : Bool) : Except (Array Message) Procedure :=
  match proc.body with
  | .Opaque postconds impl modifiesExprs =>
      -- A throwing procedure (lowered by `EliminateExceptions`) returns a single
      -- `$result : Result<…>`. Its normal `modifies` frame applies only on the
      -- normal (Good) path, so guard it with `Result..isGood($result)`; each
      -- `throwsOn` case frames its own throwing path. All of these frames are
      -- built here rather than in `EliminateExceptions` because they need `$heap`
      -- and the field constants, which only exist after heap parameterization.
      -- The cases' guards and targets have already been heap-transformed.
      -- Names shared with `EliminateExceptions` via `LaurelAST` (a rename that
      -- reached only one of the two passes would desync them silently).
      let src := proc.name.source
      let heapIn := mkMd (.Old (mkMd (.Var (.Local heapVarName)) src)) src
      let heapOut := mkMd (.Var (.Local heapVarName)) src
      let isThrowing := proc.outputs.any (fun o => o.name.text == resultOutputName)
      let resultRef := mkMd (.Var (.Local (mkId resultOutputName))) src
      let isGoodResult := mkMd (.StaticCall (mkId exnResultIsGood) [resultRef]) src
      let isBadResult := mkMd (.StaticCall (mkId exnResultIsBad) [resultRef]) src
      let guardGood (c : StmtExprMd) : StmtExprMd :=
        if isThrowing then
          mkMd (.StaticCall (mkId Operation.Implies.procName) [isGoodResult, c]) src
        else c
      -- One frame per `throwsOn` case: `Result..isBad($result) ∧ Cᵢ ==> <only that
      -- case's targets change>`. Because the cases are independent, a per-thrown-type
      -- frame is expressible — one case each — rather than every exceptional target
      -- being unioned into a single frame. Emitted only for a procedure with a heap
      -- output to frame over, and only for cases that name targets.
      --
      -- Which cases contribute a frame is `caseContributesFrame`; see there for why a
      -- wildcard has to be excluded at this level rather than downstream.
      let excPosts : List Condition :=
        if isThrowing && hasHeapOut proc then
          proc.throwsOn.filterMap fun blk =>
            if !caseContributesFrame blk then none
            else
              let entries := extractModifiesEntries model blk.modifies
              let caseGuard :=
                mkMd (.StaticCall (mkId Operation.And.procName) [isBadResult, blk.guard]) src
              -- Anchor the diagnostic at the procedure name, so a failed exceptional
              -- frame points at the procedure rather than at a source-less
              -- synthesized node.
              some { condition := ⟨ .StaticCall (mkId Operation.Implies.procName)
                       [caseGuard, buildQuantifiedFrame proc entries heapIn heapOut],
                       proc.name.source ⟩,
                     summary := "throwsOn modifies clause",
                     mode := if impl.isNone then ConditionMode.Assume else ConditionMode.Both }
        else []
      -- Exhaustiveness: `Result..isBad($result) ==> (C₁ ∨ … ∨ Cₙ)`. Stating at least
      -- one case is a claim to have enumerated them, so a throwing path matching no
      -- guard is reported here rather than silently escaping every frame above —
      -- where it would be unconstrained, since each frame's antecedent is false on
      -- such a path.
      --
      -- Not emitted when the procedure states no cases: it then claims nothing about
      -- its throwing paths, and an empty disjunction would read as "never throws".
      --
      -- For a bodiless procedure it is assumed rather than checked, like every other
      -- clause there — a declared contract is trusted, and stating the cases *is* the
      -- author's enumeration of them. This is what lets a caller of a bodiless
      -- `throwsOn C { … }` conclude the call throws only under `C`.
      let exhaustivenessPost : List Condition :=
        match proc.throwsOn with
        | blk :: blks =>
          if isThrowing then
            let anyGuard := blks.foldl
              (fun acc b =>
                mkMd (.StaticCall (mkId Operation.Or.procName) [acc, b.guard]) src) blk.guard
            [{ condition := ⟨ .StaticCall (mkId Operation.Implies.procName)
                                [isBadResult, anyGuard], proc.name.source ⟩,
               summary := "throwsOn cases cover every throwing path",
               mode := if impl.isNone then ConditionMode.Assume else ConditionMode.Both }]
          else []
        | [] => []
      let excAll := excPosts ++ exhaustivenessPost
      if hasModifiesWildcard modifiesExprs then
        .ok { proc with body := .Opaque (postconds ++ excAll) impl [], throwsOn := [] }
      else if hasHeapOut proc then
        let entries := extractModifiesEntries model modifiesExprs
        if useEnumeratedFrame && onlyIndividualRefs entries then
          -- Callers assume the quantifier-free frame (assume-only); the body
          -- checks the pointwise frame (assert-only) at every exit, so the
          -- quantified frame is verified but never exposed to callers.
          let enumeratedPost : Condition :=
            { condition := guardGood (buildEnumeratedFrame proc entries heapIn heapOut),
              summary := "modifies clause", mode := ConditionMode.Assume }
          let pointwisePost : Condition :=
            { condition := guardGood (buildQuantifiedFrame proc entries heapIn heapOut),
              summary := "modifies clause", mode := ConditionMode.Assert }
          .ok { proc with body := .Opaque (postconds ++ [enumeratedPost, pointwisePost] ++ excAll) impl [], throwsOn := [] }
        else
          let framePost : Condition :=
            { condition := guardGood (buildQuantifiedFrame proc entries heapIn heapOut),
              summary := "modifies clause" }
          .ok { proc with body := .Opaque (postconds ++ [framePost] ++ excAll) impl [], throwsOn := [] }
      else
        -- No heap to frame, but the exhaustiveness claim is heap-independent.
        .ok { proc with body := .Opaque (postconds ++ exhaustivenessPost) impl modifiesExprs,
                        throwsOn := [] }
  | _ => .ok { proc with throwsOn := [] }

/--
Transform a Laurel program: apply modifies clause transformation to all procedures.
This is a Laurel → Laurel pass that should run after heap parameterization.

Always returns the (best-effort) transformed program together with any diagnostics,
so that later passes can continue and report additional errors.
-/
def modifiesClausesTransform (model: SemanticModel) (program : Program) (useEnumeratedFrame : Bool) : Program × List Message :=
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
  comesBefore := [
    ⟨ contractPass.meta, "The modifies pass creates new postconditions"⟩,
    ⟨ pushOldInwardPass.meta, "The modifies clauses pass uses old already in 'inward' positions, so right now it does not actually need the push inward pass to come after. However, if the implementation of old changes then it's safer if the pass that handles old comes after the modifies pass since it does introduce old."⟩]
  comesAfter := [⟨ heapParameterizationPass.meta, "the modifies pass refers to several types and variables introduced by heap parameterization: Composite, Field, $heap_in, $heap."⟩]
  run := fun options p m =>
    let (p', diags) := modifiesClausesTransform m p (useEnumeratedFrame := options.enumeratedModifiesClauses)
    (p', diags, {})

end Strata.Laurel

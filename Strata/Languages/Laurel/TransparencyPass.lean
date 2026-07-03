/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.CoreGroupingAndOrdering
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.DL.Lambda.TypeFactory

/-!
## Transparency Pass

For each Core procedure, generate a function with the same signature and name
suffixed with `$asFunction`. If a Core procedure is marked as transparent,
attempt to add a body to its function version. In the functional body,
assertions are erased and all calls are to functional versions. If the function
has a body, add a free postcondition to the related procedure that equates the
two.

This IR sits between Laurel and CoreWithLaurelTypes in the pipeline:
  Laurel → UnorderedCoreWithLaurelTypes → CoreWithLaurelTypes → Core
-/

namespace Strata.Laurel

public section

/-- Deep traversal that strips all Assert and Assume nodes from a StmtExpr tree.
    Assert/Assume nodes are replaced with `LiteralBool true`, and Block nodes
    are collapsed by filtering out trivial `LiteralBool true` leftovers. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert .. | .Assume _ => ⟨.LiteralBool true, e.source⟩
    | .Block stmts label =>
      let stmts' := stmts.filter fun s =>
        match s.val with | .LiteralBool true => false | _ => true
      match stmts' with
      | [] => ⟨.LiteralBool true, e.source⟩
      | [s] => if label.isNone then s else ⟨.Block [s] label, e.source⟩
      | _ => ⟨.Block stmts' label, e.source⟩
    | _ => e) expr

/-- Adjust a datatype selector (destructor) name based on the `proof` flag.
    Destructor names contain `..` (e.g. `IntList..head`, `IntList..head!`).
    Tester names also contain `..` but start with `is` after the separator.
    - `proof = true` → use safe selectors (strip `!` suffix)
    - `proof = false` → use unsafe selectors (add `!` suffix) -/
private def adjustSelectorName (name : Identifier) : Identifier :=
  if Lambda.isTesterName name.text then name
  else if Lambda.isDestructorName name.text then
    -- Unsafe: add trailing "!" if not already present
    if name.text.endsWith Lambda.unsafeDestructorSuffix then name
    else { text := name.text ++ Lambda.unsafeDestructorSuffix, source := name.source }
  else name

/-- Rewrite StaticCall callees to their `$asFunction` versions,
    but only for procedures whose names appear in `nonExternalNames`. -/
private def rewriteCallsToFunctional (asFunctionNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .StaticCall callee args =>
      if asFunctionNames.contains callee.text then
        let funcCallee := { callee with text := callee.text ++ "$asFunction", uniqueId := none }
        ⟨.StaticCall funcCallee args, e.source⟩
      else
        let newName := adjustSelectorName callee
        ⟨ .StaticCall newName args, e.source⟩
    | .PrimitiveOp operator arguments _ => ⟨ .PrimitiveOp operator arguments true, e.source⟩
    | _ => e) expr

/-- Narrowly redirect `StaticCall` callees whose names are in `redirectNames`
    to their `$asFunction` versions, leaving everything else (selectors,
    primitive ops, non-redirected calls) untouched. Unlike
    `rewriteCallsToFunctional`, this does not adjust selector names or mark
    primitive ops as proof terms, so it is safe to apply to imperative
    procedure bodies.

    The callee's `uniqueId` is preserved: it still resolves (via the semantic
    model) to the base procedure, whose output type matches the `$asFunction`'s
    return type, so `computeExprType`/`getCallType` continue to type the call
    correctly. The renamed callee text (`X$asFunction`) is not in
    `procedureNames`, so the Laurel→Core translator lowers it as a pure function
    application rather than a procedure call. -/
private def redirectCallsToFunctional (redirectNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .StaticCall callee args =>
      if redirectNames.contains callee.text then
        let funcCallee := { callee with text := callee.text ++ "$asFunction" }
        ⟨.StaticCall funcCallee args, e.source⟩
      else e
    | _ => e) expr

/-- Apply `redirectCallsToFunctional` to a procedure's implementation and
    postcondition expressions. Used in `AnalysisMode.Verify` so that calls to
    transparent, single-output procedures become pure function applications at
    their call sites. -/
private def redirectCallsInProc (redirectNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let r := redirectCallsToFunctional redirectNames
  match proc.body with
  | .Opaque postconds impl modif =>
    { proc with body := .Opaque (postconds.map fun c => { c with condition := r c.condition })
                                (impl.map r) modif }
  | .Transparent body =>
    { proc with body := .Transparent (r body) }
  | .Abstract postconds =>
    { proc with body := .Abstract (postconds.map fun c => { c with condition := r c.condition }) }
  | .External => proc

/-- Rewrite quantifier bodies like function bodies: strip assert/assume and
    rewrite calls to their `$asFunction` variants. This ensures that calls
    inside quantifiers (e.g. in modifies frame conditions) reference the
    pure functional version and are not treated as imperative by later passes. -/
private def rewriteQuantifierBodies (nonExternalNames : Std.HashSet String) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Quantifier mode param trigger body =>
      let body' := rewriteCallsToFunctional nonExternalNames (stripAssertAssume body)
      let trigger' := trigger.map (rewriteCallsToFunctional nonExternalNames)
      ⟨.Quantifier mode param trigger' body', e.source⟩
    | _ => e) expr

/-- Apply quantifier body rewriting to all postconditions and the implementation
    of a procedure. -/
private def rewriteQuantifierBodiesInProc (nonExternalNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let rewrite := rewriteQuantifierBodies nonExternalNames
  match proc.body with
  | .Opaque postconds impl modif =>
    let postconds' := postconds.map fun c => { c with condition := rewrite c.condition }
    let impl' := impl.map rewrite
    { proc with body := .Opaque postconds' impl' modif }
  | .Transparent body =>
    { proc with body := .Transparent (rewrite body) }
  | .Abstract postconds =>
    let postconds' := postconds.map fun c => { c with condition := rewrite c.condition }
    { proc with body := .Abstract postconds' }
  | .External => proc

/-- Build a free postcondition equating the procedure's output to its functional version.
    For a procedure `foo(a, b) returns (r)`, produces:
      `r == foo$asFunction(a, b)` -/
private def mkFreePostcondition (proc : Procedure) : StmtExprMd :=
  let source := proc.name.source
  let funcName := { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
  let inputArgs := proc.inputs.map fun p => (⟨ .Var (.Local p.name), source ⟩ : StmtExprMd)
  let funcCall: StmtExprMd := ⟨ .StaticCall funcName inputArgs, source ⟩
  match proc.outputs with
  | [out] => ⟨ .PrimitiveOp .Eq [⟨ .Var (.Local out.name), source⟩, funcCall], source ⟩
  | _ => ⟨ .LiteralBool true, source ⟩

/-- Create the function copy of a procedure (suffixed `$asFunction`).
    If the procedure is transparent, include a functional body.
    Otherwise the function is opaque. -/
private def mkFunctionCopy (asFunctionNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let hasProcedureTwin := asFunctionNames.contains proc.name.text
  let funcName := if hasProcedureTwin then
    { proc.name with text := proc.name.text ++ "$asFunction", uniqueId := none }
    else proc.name
  let body := match proc.body with
    | .Transparent b => .Transparent (rewriteCallsToFunctional asFunctionNames (if hasProcedureTwin then stripAssertAssume b else b))
    | .Opaque _ _ _ => if hasProcedureTwin then .Opaque [] none [] else proc.body
    | x => x
  { proc with name := funcName, body := body }

/-- Append a free postcondition to a procedure's body postconditions.
    For Opaque and Abstract bodies, the free condition is appended to the
    existing postcondition list. For Transparent bodies, the body is promoted
    to Opaque so the free postcondition can be carried.
    This change in opaqueness is fine since the function copy now carries the transparent semantics. -/
private def addFreePostcondition (proc : Procedure) (freePost : StmtExprMd) : Procedure :=
  match freePost.val with
  | .LiteralBool true => proc  -- trivial, skip
  | _ =>
    let freeCond : Condition := { condition := freePost, mode := ConditionMode.Assume }
    match proc.body with
    | .Opaque postconds impl modif =>
      { proc with body := .Opaque (postconds ++ [freeCond]) impl modif }
    | .Abstract postconds =>
      { proc with body := .Abstract (postconds ++ [freeCond]) }
    | .Transparent body =>
      { proc with body := .Opaque [freeCond] (some body) [] }
    | _ => proc

/--
Transparency pass: translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.

For each procedure:
- Generate a function with the same signature, named `foo$asFunction`
- If transparent, the function gets a functional body (assertions erased, calls to functional versions)
- If the function has a body, add a free postcondition equating the procedure output to the function
-/
def createFunctionsForTransparentBodies (program : Program) (options : LaurelTranslateOptions := {}) : UnorderedCoreWithLaurelTypes :=
  let (toUpdate, _) := program.staticProcedures.partition (fun p => !p.body.isExternal)
  -- A transparent procedure whose body is purely functional (no Assume/Assert
  -- from contract instrumentation) needs only a function copy, not a procedural
  -- twin. This matches the old `isFunctional` behavior for condition helpers.
  let needsProcTwin (p : Procedure) : Bool := match p.body with
    | .Transparent b => blockContainsAssumeOrAssert b
    | _ => true
  let (imperativeProcs, _) := toUpdate.partition needsProcTwin
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  match options.analysisMode with
  | .Execute =>
    -- Concrete execution: keep every procedure as a real procedure (no call
    -- redirection and no free postconditions), so an imperative call is executed
    -- for its imperative meaning rather than folded into a pure twin.
    --
    -- We still emit the `$asFunction` twins and rewrite the *function copies'*
    -- bodies (and any axiom / quantifier references) to call those twins. This is
    -- what keeps a pure context resolvable: a transparent procedure such as
    -- `List_slice` — or a bodiless prelude primitive such as `Any_len` — is
    -- reached from another function body or a `requires`/`ensures` clause, and
    -- after the function/procedure merge those callees are procedures. Rewriting
    -- the call to `<name>$asFunction` turns it back into a pure function
    -- application the schema pass accepts, exactly as before the merge. The
    -- imperative procedure bodies themselves are left untouched (their calls stay
    -- procedure calls), preserving execution semantics.
    let toUpdateNames : Std.HashSet String := imperativeProcs.foldl (fun s p => s.insert p.name.text) {}
    let functions := program.staticProcedures.map (mkFunctionCopy toUpdateNames)
    let coreProcedures := imperativeProcs.map fun proc =>
      let proc := { proc with axioms := proc.axioms.map (rewriteCallsToFunctional toUpdateNames) }
      rewriteQuantifierBodiesInProc toUpdateNames proc
    { functions, coreProcedures, datatypes, constants := program.constants }
  | .Verify | .BothSuboptimally =>
    let toUpdateNames : Std.HashSet String := imperativeProcs.foldl (fun s p => s.insert p.name.text) {}
    -- Names of single-output procedures whose calls can be redirected to their
    -- `$asFunction` version: `mkFreePostcondition` only equates a single output
    -- to the function, and a single function application can only fill one
    -- assignment target. Multi-output procedures are excluded.
    let singleOutputNames : Std.HashSet String :=
      imperativeProcs.foldl (fun s p =>
        if p.outputs.length == 1 && p.body.isTransparent then s.insert p.name.text else s) {}
    -- $asFunction copies for procedures that have a procedural twin;
    -- transparent-only procedures keep their original name.
    let functions := program.staticProcedures.map (mkFunctionCopy toUpdateNames)
    -- Rewrite each procedure's axioms/quantifier bodies to reference the
    -- `$asFunction` twins before we decide which procedures still need the free
    -- postcondition bridge.
    let rewritten := imperativeProcs.map fun proc =>
      let proc := { proc with axioms := proc.axioms.map (rewriteCallsToFunctional toUpdateNames) }
      rewriteQuantifierBodiesInProc toUpdateNames proc
    -- Names whose `$asFunction` twin is referenced by some rewritten axiom or
    -- quantifier body. The axiom/quantifier rewrites above turn a reference to
    -- `P(..)` into `P$asFunction(..)` while goals elsewhere still mention `P(..)`,
    -- so `P` needs the free postcondition `P == P$asFunction(..)` to tie the two
    -- together. This happens for `invokeOn P(x)` (an axiom on the *triggering*
    -- procedure, not on `P`) and for a quantifier trigger `{ P(i) }` inside a
    -- procedure body — so the referenced twins must be gathered across every
    -- procedure's axioms and body, not per-procedure.
    let scanExprForTwins (e : StmtExprMd) : StateM (Std.HashSet String) Unit :=
      foldStmtExprM (fun e =>
        match e.val with
        | .StaticCall callee _ =>
          if callee.text.endsWith "$asFunction" then
            modify (·.insert (callee.text.dropRight "$asFunction".length))
          else pure ()
        | _ => pure ()) e
    let collectTwins : StateM (Std.HashSet String) Unit := do
      for proc in rewritten do
        for ax in proc.axioms do scanExprForTwins ax
        match proc.body with
        | .Opaque postconds impl _ =>
          postconds.forM fun c => scanExprForTwins c.condition
          match impl with | some b => scanExprForTwins b | none => pure ()
        | .Transparent b => scanExprForTwins b
        | .Abstract postconds => postconds.forM fun c => scanExprForTwins c.condition
        | .External => pure ()
    let axiomTwinNames : Std.HashSet String := (collectTwins.run {}).snd
    let coreProcedures := rewritten.map fun proc =>
      match options.analysisMode with
      | .Verify =>
        -- Redirect every call to a single-output twinned procedure to its
        -- `$asFunction` version so calls stay constant-foldable during symbolic
        -- evaluation (instead of producing fresh symbolic outputs via the
        -- procedural twin). Callers of a redirected procedure observe the pure
        -- twin directly, so the free postcondition tying procedure to twin is
        -- unnecessary there.
        --
        -- A procedure still needs the free postcondition when it is *not*
        -- redirected yet its twin is referenced by some rewritten axiom (the
        -- `invokeOn` case): without `P == P$asFunction(..)` the rewritten axiom
        -- can no longer discharge a goal about `P`. Procedures whose twin no
        -- axiom mentions get no bridge, since injecting the uninterpreted twin
        -- equation only weakens the solver (turning refutable goals into unknown).
        let proc := redirectCallsInProc singleOutputNames proc
        if axiomTwinNames.contains proc.name.text && !singleOutputNames.contains proc.name.text then
          addFreePostcondition proc (mkFreePostcondition proc)
        else proc
      | _ =>
        -- `BothSuboptimally`: keep calls as-is and tie each procedure to its
        -- twin via a free postcondition, at the cost of fresh symbolic outputs.
        addFreePostcondition proc (mkFreePostcondition proc)
    { functions, coreProcedures, datatypes, constants := program.constants }
where
  /-- Check if an expression tree contains Assume or Assert statements anywhere.
      The contract pass inserts these for procedures with contracts.

      Uses the generic `anyStmtExpr` combinator so every constructor is
      traversed automatically. A hand-rolled recursion here would miss nodes
      like `Quantifier`, `InstanceCall`, `Old`, and `Fresh`: since the contract
      pass now instruments every contract-bearing procedure, a `requires`-bearing
      helper called from inside such a node produces an `Assert` that a partial
      traversal would not see, so no procedural twin would be generated and the
      schema pass would then reject the embedded assert. -/
  blockContainsAssumeOrAssert (e : StmtExprMd) : Bool :=
    anyStmtExpr (fun n => match n.val with
      | .Assume _ | .Assert .. => true
      | _ => false) e

public def transparencyPass : LaurelPass Laurel.Program UnorderedCoreWithLaurelTypes where
  name := "TransparencyPass"
  comesBefore := [⟨ orderingPass.meta, "Transparency pass creates functions that are not ordered" ⟩]
  documentation := "Translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.
For each procedure:
  - Generate a function with the same signature, named `foo$asFunction`
  - If transparent, the function gets a functional body (assertions erased, calls to functional versions)
  - If the function has a body, add a free postcondition equating the procedure output to the function"
  run := fun opts p _ =>
    (createFunctionsForTransparentBodies p opts, [], {})

end -- public section
end Strata.Laurel

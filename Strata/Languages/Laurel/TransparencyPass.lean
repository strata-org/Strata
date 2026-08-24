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
import Strata.Languages.Laurel.LiftImperativeExpressions
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

/-- Replace a checked arithmetic operator with its unchecked counterpart.
    The checked operators (`intSafeDiv` and friends) carry a `y != 0`
    precondition that Core turns into a proof obligation at every call site.
    Inside a function body that obligation is neither provable nor needed: the
    `$asFunction` twin is a pure mirror of a procedure whose own `requires`
    already discharges the check on the imperative side. So the twin calls the
    unchecked operator. -/
private def adjustSafeOperatorName (name : Identifier) : Identifier :=
  -- The names carry Laurel's reserved `$` prefix, as every prelude procedure does.
  let unchecked := match name.text with
    | "$intSafeDiv" => some "$intDiv"
    | "$intSafeMod" => some "$intMod"
    | "$intSafeDivT" => some "$intDivT"
    | "$intSafeModT" => some "$intModT"
    | _ => none
  match unchecked with
  | some text => { name with text }
  | none => name

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
        let newName := adjustSafeOperatorName (adjustSelectorName callee)
        ⟨ .StaticCall newName args, e.source⟩
    | _ => e) expr

/-- Narrowly redirect `StaticCall` callees whose names are in `redirectNames`
    to their `$asFunction` versions, leaving everything else (selectors,
    operator calls, non-redirected calls) untouched. Unlike
    `rewriteCallsToFunctional`, this does not adjust selector names or swap
    checked operators for unchecked ones, so it is safe to apply to imperative
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

/-- Check if an expression tree contains Assume or Assert statements anywhere.
    The contract pass inserts these for procedures with contracts.

    Uses the generic `anyStmtExpr` combinator so every constructor is traversed
    automatically. A hand-rolled recursion here would miss nodes like
    `Quantifier`, `InstanceCall`, `Old`, and `Fresh`: since the contract pass now
    instruments every contract-bearing procedure, a `requires`-bearing helper
    called from inside such a node produces an `Assert` that a partial traversal
    would not see, so no procedural twin would be generated and the schema pass
    would then reject the embedded assert. -/
private def containsAssertOrAssume (expr : StmtExprMd) : Bool :=
  anyStmtExpr (fun e => match e.val with | .Assert .. | .Assume _ => true | _ => false) expr

/-- Rewrite references to the declaration identified by `boundUid` so they name
    `newName` instead.

    Keyed on `uniqueId` rather than on `.text`: a nested quantifier may rebind the
    same name (`forall(x) => ... forall(x) => ...` is legal Laurel), and a
    text-keyed rewrite would capture the inner binder's references too. Resolution
    runs before this pass, so every `Local` reference carries the `uniqueId` of the
    declaration it resolved to, which distinguishes the two binders. -/
private def renameBoundVarRefs (boundUid : Nat) (newName : Identifier)
    (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Var (.Local name) =>
      if name.uniqueId == some boundUid then ⟨.Var (.Local newName), e.source⟩ else e
    | _ => e) expr

/-- Rewrite quantifier bodies and loop invariants like function bodies: strip
    assert/assume and rewrite calls to their `$asFunction` variants.

    For quantifiers this ensures that calls inside them (e.g. in modifies frame
    conditions) reference the pure functional version and are not treated as
    imperative by later passes.

    Loop invariants (and `decreases`) need the same treatment for a stronger
    reason: they are spec positions evaluated at the loop head, so nothing may be
    hoisted out of them — `LiftImperativeExpressions` leaves them untransformed. A
    procedure call left in an invariant would therefore stay there, where later
    passes cannot represent it. Rewriting it to the pure `$asFunction` twin keeps the
    invariant a pure expression that can stay in place. Without this, a
    `requires`-bearing callee — including the `$div` wrapper behind `/` — makes the
    contract pass inject an `assert` into the invariant, which `stripAssertAssume`
    removes here: the precondition is checked at the call sites that matter, not at
    the loop head.

    When a quantifier body contains assert/assume (a proof procedure), the
    quantifier is preceded by a self-sealing proof block:
    ```
    {
      var $proof_0: bool;
      if $proof_0 then { var $havoc_0: T; <body[x := $havoc_0]>; assume false };
      forall(x: T) => <goal>
    }
    ```
    The nondet if-branch introduces an arbitrary stand-in for the quantifier
    variable, executes the proof body (with its asserts/assumes), then seals with
    `assume false` so nothing leaks into the enclosing path conditions. The
    stand-in is a fresh `$havoc_N` rather than the binder's own name because
    shadowing does not survive lowering to Core; see `rewriteQuantifierBodies`'s
    implementation comment.

    The proof block discharges *only* the obligations written inside the body
    (its `assert` steps, checked for an arbitrary `x`, with the body's `assume`
    steps available as hypotheses). It deliberately establishes nothing about
    the quantifier itself: no `assume forall(x: T) => <goal>` is emitted. Doing
    so would be unsound, because the branch never proves the goal — the goal
    sits in expression position and generates no obligation — so assuming it
    would hand the caller a free axiom (and, being procedure-scoped, would also
    leak to later unrelated asserts). The stripped quantifier is the block's
    value, so the enclosing `assert`/`assume` sees an ordinary quantifier and
    the solver must discharge it on its own merits.

    Because the block only *adds* obligations and assumes nothing, it applies to
    both quantifier modes: checking the body's steps under a havoc'd binder is
    the wellformedness rule for `exists` just as much as for `forall`, and it can
    never make an unprovable goal verify. See the `Quantifiers.lean` tests.

    `emitProofBlocks := false` suppresses the scaffolding entirely, keeping only
    the `stripAssertAssume` + call-rewriting behavior. Used in `AnalysisMode.Execute`,
    where the nondet `$proof_N` guard has no meaningful concrete semantics. -/
private partial def rewriteQuantifierBodiesM (emitProofBlocks : Bool)
    (nonExternalNames : Std.HashSet String) (expr : StmtExprMd) : StateM Nat StmtExprMd :=
  -- Threads a counter so each proof block gets its own guard name. Nested proof
  -- procedures would otherwise both declare `$proof` in the same Core scope
  -- ("Variable $proof of type bool already in context").
  --
  -- The `.Quantifier` case is decided in the *pre* hook, on the body as written
  -- rather than after the children have been rewritten. Deciding bottom-up is
  -- wrong for a directly-nested quantifier (`forall(x) => forall(y) => { assert .. }`):
  -- the inner rewrite would already have replaced the outer's body with its own
  -- proof block, whose `assume false` seal makes `containsAssertOrAssume` fire
  -- again, so the outer would wrap the inner's scaffolding. The outer's
  -- `stripAssertAssume` only removes `.Assert`/`.Assume`, leaving the inner
  -- `var $proof_N`/`var $havoc_N` and `IfThenElse` behind in the goal — an
  -- uninitialized declaration in a transparent position, which the schema pass
  -- rejects with "local variables must have initializers in transparent bodies
  -- or contracts".
  --
  -- Returning `some` from `pre` skips the generic recursion, so this case
  -- recurses explicitly into the *proof body* only (a quantifier nested there
  -- gets its own proof block). The goal is `stripAssertAssume`d, so it holds no
  -- proof steps and needs no proof block of its own.
  mapStmtExprPrePostM (m := StateM Nat)
    (pre := fun e =>
    match e.val with
    | .Quantifier mode param trigger body =>
      let trigger' := trigger.map (rewriteCallsToFunctional nonExternalNames)
      if emitProofBlocks && containsAssertOrAssume body then do
        let n ← modifyGet (fun n => (n, n + 1))
        let body' := rewriteCallsToFunctional nonExternalNames (stripAssertAssume body)
        let strippedQuantifier : StmtExprMd :=
          ⟨.Quantifier mode param trigger' body', e.source⟩
        -- Self-sealing branch: { var $havoc_n: T; <body[x := $havoc_n]>; assume false }
        --
        -- The havoc variable gets a *fresh* name rather than reusing the binder's.
        -- Reusing it would synthesize a declaration that shadows any in-scope local
        -- of the same name, and shadowing does not survive lowering: Core rejects a
        -- re-declaration outright ("Variable x of type int already in context", see
        -- `Strata/DL/Imperative/CmdType.lean`), and no pass renames shadowed locals
        -- apart on the way there. Laurel's Resolution does accept shadowing — it
        -- assigns the two declarations distinct `uniqueId`s — so the clash only
        -- surfaces in Core, which keys its context on the *name*. Reusing the binder
        -- would therefore reject `var x: int := 10; assert forall(x: int) => { .. }`,
        -- source that shadows nothing on its own: the pass would be the sole source
        -- of the shadowing.
        --
        -- If Laurel gains end-to-end shadowing support (a pass that renames
        -- shadowed locals apart before Core, so Resolution's `uniqueId`s are what
        -- the backend keys on), this renaming becomes unnecessary: the havoc could
        -- then just reuse the binder's name, which reads better in dumps. Until
        -- then the fresh name is what keeps the proof block lowerable.
        --
        -- `$`-prefixed names are reserved for pass-synthesized variables (as with
        -- `$proof_n` and the lifting pass's `$cndtn_n`), so they cannot collide with
        -- a user identifier. The counter keeps sibling and nested proof blocks apart.
        let havocName : Identifier := mkId s!"$havoc_{n}"
        -- `Declare` carries a `Parameter?`, whose type annotation is optional. The
        -- quantifier binder's type is always present, so the havoc declaration takes
        -- it: the havoc stands for an arbitrary value of the quantified type. Leaving
        -- the annotation off would instead leave resolution nothing to infer from —
        -- the declaration has no initializer — so it would bind `Unknown` and
        -- diagnose.
        let havocParam : Parameter? := { name := havocName, type := some param.type }
        let varDecl : StmtExprMd := ⟨.Var (.Declare havocParam), e.source⟩
        -- Point the body's references at the renamed declaration. Without this the
        -- body would still name the binder, which is not declared inside the branch.
        let body := match param.name.uniqueId with
          | some uid => renameBoundVarRefs uid havocName body
          | none => body
        -- Recurse into the proof body so a quantifier nested inside it gets its own
        -- proof block. Shares the counter, keeping every guard name distinct.
        let body ← rewriteQuantifierBodiesM emitProofBlocks nonExternalNames body
        let assumeFalse : StmtExprMd := ⟨.Assume ⟨.LiteralBool false, e.source⟩, e.source⟩
        let sealedBody : StmtExprMd := ⟨.Block [varDecl, body, assumeFalse] none, e.source⟩
        -- Nondet guard: var $proof_n: bool; if $proof_n then <sealedBody>
        let guardName : Identifier := mkId s!"$proof_{n}"
        let guardType : HighTypeMd := ⟨.TBool, e.source⟩
        let guardDecl : StmtExprMd := ⟨.Var (.Declare ⟨guardName, guardType⟩), e.source⟩
        let guardRef : StmtExprMd := ⟨.Var (.Local guardName), e.source⟩
        let sealedBranch : StmtExprMd :=
          ⟨.IfThenElse guardRef sealedBody none, e.source⟩
        -- Outer block: { guardDecl; sealedBranch; strippedQuantifier }
        pure (some ⟨.Block [guardDecl, sealedBranch, strippedQuantifier] none, e.source⟩)
      else
        -- No proof steps of its own: strip and rewrite calls, as before. The body is
        -- already fully handled here, so this also returns `some` — recursing would
        -- revisit a `stripAssertAssume`d tree to no effect.
        let body' := rewriteCallsToFunctional nonExternalNames (stripAssertAssume body)
        pure (some ⟨.Quantifier mode param trigger' body', e.source⟩)
    | _ => pure none)
    (post := fun e =>
    match e.val with
    | .While cond invs dec body postTest =>
      let rewriteSpec := fun (s : StmtExprMd) =>
        rewriteCallsToFunctional nonExternalNames (stripAssertAssume s)
      -- Only the invariants and `decreases` are spec positions; `cond` and `body`
      -- are ordinary imperative code and must keep their procedure calls. Runs in
      -- `post`, so `cond`/`body` still get the generic recursion (a quantifier in
      -- either is rewritten as usual) and only the spec positions are stripped.
      pure ⟨.While cond (invs.map rewriteSpec) (dec.map rewriteSpec) body postTest, e.source⟩
    | _ => pure e) expr

/-- Entry point for `rewriteQuantifierBodiesM`, starting the guard counter at 0. -/
private def rewriteQuantifierBodies (emitProofBlocks : Bool) (nonExternalNames : Std.HashSet String)
    (expr : StmtExprMd) : StmtExprMd :=
  (rewriteQuantifierBodiesM emitProofBlocks nonExternalNames expr).run' 0

/-- Apply quantifier body rewriting to all postconditions and the implementation
    of a procedure. See `rewriteQuantifierBodies` for `emitProofBlocks`. -/
private def rewriteQuantifierBodiesInProc (emitProofBlocks : Bool)
    (nonExternalNames : Std.HashSet String) (proc : Procedure) : Procedure :=
  let rewrite := rewriteQuantifierBodies emitProofBlocks nonExternalNames
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
  | [out] => ⟨ .StaticCall (mkId Operation.Eq.procName) [⟨ .Var (.Local out.name), source⟩, funcCall], source ⟩
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
  -- Exception: an `entry`-marked procedure is a concrete-interpretation entry
  -- point, so it must survive as a Core procedure even when its body has no
  -- assertions — otherwise the schema pass's `interpretEntry` metadata is
  -- emitted only on the discarded proc arm and `entryProcedures` sees nothing.
  let needsProcTwin (p : Procedure) : Bool :=
    p.isInterpretEntry || match p.body with
    | .Transparent b => containsAssertOrAssume b
    | _ => true
  let (imperativeProcs, _) := toUpdate.partition needsProcTwin
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  let opaqueTypes := program.types.filterMap fun td => match td with
    | .Opaque ot => some ot
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
    -- No proof blocks: the quantifier proof-procedure scaffolding is a
    -- verification-only construct. Its nondet `$proof_N` guard is an
    -- uninitialized bool with no meaningful concrete semantics, so under
    -- interpretation the branch would be taken (or not) arbitrarily and its
    -- `assume false` seal has nothing to seal. Execute mode therefore uses only
    -- `stripAssertAssume`, without the proof-block scaffolding.
    let coreProcedures := imperativeProcs.map fun proc =>
      let proc := { proc with axioms := proc.axioms.map (rewriteCallsToFunctional toUpdateNames) }
      rewriteQuantifierBodiesInProc (emitProofBlocks := false) toUpdateNames proc
    { functions, coreProcedures, datatypes, opaqueTypes, constants := program.constants }
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
      rewriteQuantifierBodiesInProc (emitProofBlocks := true) toUpdateNames proc
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
            modify (·.insert (callee.text.dropEnd "$asFunction".length).toString)
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
    { functions, coreProcedures, datatypes, opaqueTypes, constants := program.constants }

public def transparencyPass : LaurelPass Laurel.Program UnorderedCoreWithLaurelTypes where
  name := "Transparency"
  -- The quantifier proof-block rewrite introduces fresh declarations (the havoc
  -- variable and the `$proof_N` guard) with no `uniqueId`, so the pipeline must
  -- re-resolve after this pass to bind them.
  needsResolves := true
  comesBefore := [
    ⟨ orderingPass.meta, "The transparency pass creates functions, and ordering can only be done once the Core functions and procedures are known, so the ordering pass needs to come after the transparency one." ⟩,
    ⟨ liftImperativeExpressionsPass.meta, "First, the transparency pass changes some or all calls to procedures into calls to functions. Only calls to procedures need to be lifted, so doing the lifting before the transparency pass would lift all calls, which is unnecessary. Lifting complicates the code so it's better not to do it if not necessary. Secondly, the lifting pass will lift all assertions and assumptions, but the transparency pass removes all assertions and assumptions from functions. If we would lift these before the transparency pass, you would see the remnants of that lifting even though no lifting was necessary for functions." ⟩]
  documentation := "Translate a Laurel program to the UnorderedCoreWithLaurelTypes IR.

This pass has three modes:
- Execute
- Verify
- BothSuboptimally

**BothSuboptimally** mode allows the translated program to be used both for interpretation and for verification, but it won't perform as well when verified, sometimes letting the SMT solver return UNKNOWN instead of SAT. For interpretation it'll execute performantly, but the compilation time will be unnecessarily long since Core functions will be created but not used.

For each procedure, BothSuboptimally mode will:
  - Generate a function with the same signature, named `foo$asFunction`. The procedure and associated function are called a twin.
  - If transparent, the function gets a functional body (assertions erased, all calls are to functional siblings)
  - If the function has a body, add a free postcondition equating the procedure output to the function. This postcondition is called the 'bridge' and it's this bridge that regresses verification performance because it introduces additional quantifiers.

**Execute** mode will create as few procedures as necessary. When interpreting, all calls will be to procedures. Currently execute mode still creates some functions because calls from quantifiers can only be to functions and can't be lifted, but this may change.

**Verify** mode will change all calls to be to functions and no longer generate the bridges between twins. Currently, verify mode still needs some calls to be to procedures, because:
  - We are not yet able to generate function twins for procedures with multiple output parameters
  - There is a bug in Core's partial evaluator that causes its runtime to become exponential when calling bodiless functions.

Since execute mode tries not to generate any functions, it could work well even if the heap is still implicit. Maybe instead of the transparency pass we should define a separate 'Execute' and 'Verify' pass, where only the latter needs to come after the heap encoding.
"

  run := fun opts p _ =>
    (createFunctionsForTransparentBodies p opts, [], {})

end -- public section
end Strata.Laurel

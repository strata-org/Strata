/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange
public import Strata.Languages.Python.PythonDialect

/-!
# Statement Classification and Demand Analysis for PythonSSA

Provides utilities consumed by the Phase 2 SSA translator:

- **Statement classification**: `isSimpleStmt` distinguishes statements that
  can be emitted within a single block from compound statements that require
  control-flow splitting.
- **Demand analysis**: backward dataflow computing exactly which variables
  each block needs as parameters, replacing a conservative all-vars approach.
-/

namespace Strata.Python.Blockify

open Strata.Python (stmt expr withitem)

/-! ## Statement Classification -/

/-- A "simple statement" does not introduce cross-block control flow and can be
    translated to SSA instructions within the current block.

    Criteria:
    - Does NOT contain sub-statement bodies (no if/for/while/try/with)
    - Includes: Assign, AnnAssign, AugAssign, Expr, Assert, Pass,
      Import, ImportFrom, Delete, Global, Nonlocal
    - Also includes control-flow terminators: Return, Raise, Break, Continue.
      These are "simple" in the sense that Phase 1 doesn't decompose them,
      but they END the current block — Phase 2 emits a terminator when it
      encounters one. Any statements after a terminator in the same slice
      are dead code.
    - FunctionDef and ClassDef are simple at module level (they define a
      name binding) but trigger separate function processing. Phase 1 treats
      them as simple for the enclosing scope. -/
public def isSimpleStmt (s : stmt SourceRange) : Bool :=
  match s with
  | .If ..    | .For ..   | .While .. | .Try ..     | .With .. => false
  | .AsyncFor .. | .AsyncWith .. | .TryStar .. | .Match .. => false
  | _ => true

/-- Remove variable names defined by an assignment target from a HashSet.
    Handles Name (erase), Starred (recurse), and Tuple/List (recurse elements).
    Attribute/Subscript targets don't define variable names — they're handled
    by `addTargetReads`. -/
private def removeTargetDefs (acc : Std.HashSet String)
    (e : expr SourceRange) : Std.HashSet String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => acc.erase name
  | .Starred _ value _ => removeTargetDefs acc value
  | .Tuple _ ⟨_, elts⟩ _ => elts.foldl (init := acc) removeTargetDefs
  | .List _ ⟨_, elts⟩ _ => elts.foldl (init := acc) removeTargetDefs
  | _ => acc


/-! ## Demand Analysis

Backward analysis that computes exactly which variables each block needs as
parameters. Replaces the conservative `allVars` approach.

The result is `Array DemandVars` where `result[i]` = sorted variable names
needed by block `i`. Block 0 (entry) always has demand `#[]`.

The analysis mirrors Phase 2's block allocation order so block IDs align.
-/

open Strata.Python (cmpop keyword)

/-- Sorted array of variable names needed by a block. -/
public abbrev DemandVars := Array String

-- Note: Std.HashSet has Union (∪), SDiff (\),  \, .insert, .contains, .fold

/-- Add free variables referenced in an expression to an existing set.
    Used by `addTargetReads` and the While loop case where FV and DA
    computations have conflicting ordering requirements. -/
private partial def addFreeVarsExpr (acc : Std.HashSet String)
    (e : expr SourceRange) : Std.HashSet String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => acc.insert name
  | .BoolOp _ _ ⟨_, values⟩ =>
    values.foldl (init := acc) fun acc v => addFreeVarsExpr acc v
  | .BinOp _ left _ right =>
    addFreeVarsExpr (addFreeVarsExpr acc left) right
  | .UnaryOp _ _ operand => addFreeVarsExpr acc operand
  | .Compare _ left _ ⟨_, comparators⟩ =>
    comparators.foldl (init := addFreeVarsExpr acc left) fun acc c =>
      addFreeVarsExpr acc c
  | .IfExp _ test body orelse =>
    addFreeVarsExpr (addFreeVarsExpr (addFreeVarsExpr acc test) body) orelse
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    let acc := args.foldl (init := addFreeVarsExpr acc f) fun acc a =>
      addFreeVarsExpr acc a
    kwargs.foldl (init := acc) fun acc kw =>
      match kw with | .mk_keyword _ _ v => addFreeVarsExpr acc v
  | .Attribute _ value _ _ => addFreeVarsExpr acc value
  | .Subscript _ value slice _ =>
    addFreeVarsExpr (addFreeVarsExpr acc value) slice
  | .Starred _ value _ => addFreeVarsExpr acc value
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    let acc := keys.foldl (init := acc) fun acc k =>
      match k with
      | .some_expr _ ke => addFreeVarsExpr acc ke
      | _ => acc
    values.foldl (init := acc) fun acc v => addFreeVarsExpr acc v
  | .Set _ ⟨_, elts⟩ =>
    elts.foldl (init := acc) fun acc e => addFreeVarsExpr acc e
  | .List _ ⟨_, elts⟩ _ =>
    elts.foldl (init := acc) fun acc e => addFreeVarsExpr acc e
  | .Tuple _ ⟨_, elts⟩ _ =>
    elts.foldl (init := acc) fun acc e => addFreeVarsExpr acc e
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    let acc := addFreeVarsExpr acc value
    match fmtSpec with | some spec => addFreeVarsExpr acc spec | none => acc
  | .JoinedStr _ ⟨_, values⟩ =>
    values.foldl (init := acc) fun acc v => addFreeVarsExpr acc v
  | .TemplateStr _ ⟨_, values⟩ =>
    values.foldl (init := acc) fun acc v => addFreeVarsExpr acc v
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
    let acc := match lower with | some e => addFreeVarsExpr acc e | none => acc
    let acc := match upper with | some e => addFreeVarsExpr acc e | none => acc
    match step with | some e => addFreeVarsExpr acc e | none => acc
  | _ => acc

/-- Add variables read by an assignment target to a set.
    `Name` targets are definitions (skipped). `Attribute`/`Subscript` targets
    read their object/key. `Tuple`/`List` targets recurse into elements. -/
private def addTargetReads (acc : Std.HashSet String)
    (target : expr SourceRange) : Std.HashSet String :=
  match target with
  | .Name .. => acc  -- simple assignment, no reads
  | .Attribute _ obj _ _ => addFreeVarsExpr acc obj
  | .Subscript _ obj key _ => addFreeVarsExpr (addFreeVarsExpr acc obj) key
  | .Starred _ value _ => addTargetReads acc value
  | .Tuple _ ⟨_, elts⟩ _ | .List _ ⟨_, elts⟩ _ =>
    elts.foldl (init := acc) addTargetReads
  | _ => acc

/-- Demand array built by backward pass. da[0] = last block's demand,
    da[da.size-1] = first allocated block's demand. -/
private abbrev DemandArr := Array DemandVars

private def pushDemand (da : DemandArr) (vars : Std.HashSet String) : DemandArr :=
  da.push (vars.toArray.qsort (· < ·))

/-- Combined backward demand analysis and free variable collection for expressions.
    Single traversal: pushes demand entries for expression blocks (BoolOp, IfExp,
    chained Compare) in reverse block-ID order, and accumulates free variable names
    into `fv`. Returns (updatedFV, updatedDA).

    For block-creating sub-expressions, per-child free vars are isolated with fresh
    accumulators and used for demand computation, then merged into `fv`. -/
private partial def backwardExprBlocks (e : expr SourceRange)
    (liveAfter : Std.HashSet String) (fv : Std.HashSet String) (da : DemandArr)
    : Std.HashSet String × DemandArr :=
  match e with
  | .Name _ ⟨_, name⟩ _ => (fv.insert name, da)

  | .BoolOp _ _ ⟨_, values⟩ =>
    -- FIXME:  This seems really odd.  if values.size < 2 then
    -- it is either 0 or 1.  Is 0 or 1 size even allowed?  Maybe this
    -- should just be an assert!
    if values.size < 2 then
      values.foldl (init := (fv, da)) fun (fv, da) v =>
        backwardExprBlocks v liveAfter fv da
    else
      let n := values.size
      -- Single reverse pass: collect nested block DA, per-value FVs, and
      -- cumulative demands for eval blocks.
      let (cumDemands, allFV, da) := Id.run do
        let mut cumDemands : Array (Std.HashSet String) := #[]
        let mut cumNeeded := liveAfter
        let mut allFV : Std.HashSet String := fv
        let mut da := da
        let mut i := n
        while i > 0 do
          i := i - 1
          if h : i < values.size then
            -- QUe
            let (vfv, da') := backwardExprBlocks values[i] liveAfter {} da
            da := da'
            allFV := allFV ∪ vfv
            -- Accumulate demand for eval block i (used for values[i]..values[n-1])
            cumNeeded := cumNeeded ∪ vfv
            cumDemands := cumDemands.push cumNeeded
        (cumDemands, allFV, da)
      -- cumDemands[0] = demand for last eval block, ..., cumDemands[n-2] = first eval block
      -- Push join block (highest ID)
      let da := pushDemand da liveAfter
      -- Push eval blocks (n-1 of them) in reverse allocation order
      let da := Id.run do
        let mut da := da
        let mut j := 0
        while j < n - 1 do
          if h : j < cumDemands.size then
            da := pushDemand da cumDemands[j]
          j := j + 1
        da
      (allFV, da)

  | .IfExp _ test body orelse =>
    -- Collect per-sub-expression FVs and push nested block demands
    let (orelseFV, da) := backwardExprBlocks orelse liveAfter {} da
    let (bodyFV, da) := backwardExprBlocks body liveAfter {} da
    let (testFV, da) := backwardExprBlocks test liveAfter {} da
    -- Push IfExp's 3 blocks in reverse allocation order: join, else, then
    let da := pushDemand da liveAfter                -- join
    let da := pushDemand da (liveAfter ∪ orelseFV)   -- else
    let da := pushDemand da (liveAfter ∪ bodyFV)     -- then
    (fv ∪ testFV ∪ bodyFV ∪ orelseFV, da)

  | .Compare _ left _ ⟨_, comparators⟩ =>
    if comparators.size <= 1 then
      let (fv, da) := comparators.foldr (init := (fv, da)) fun c (fv, da) =>
        backwardExprBlocks c liveAfter fv da
      backwardExprBlocks left liveAfter fv da
    else
      let n := comparators.size
      -- Single reverse pass: collect nested block DA, cumulative demands, and FVs
      let (cumDemands, allFV, da) := Id.run do
        let mut cumDemands : Array (Std.HashSet String) := #[]
        let mut cumNeeded := liveAfter
        let mut allFV : Std.HashSet String := fv
        let mut da := da
        let mut i := n
        while i > 0 do
          i := i - 1
          if h : i < comparators.size then
            let (cfv, da') := backwardExprBlocks comparators[i] liveAfter {} da
            da := da'
            allFV := allFV ∪ cfv
            cumNeeded := cumNeeded ∪ cfv
            cumDemands := cumDemands.push cumNeeded
        (cumDemands, allFV, da)
      let (leftFV, da) := backwardExprBlocks left liveAfter {} da
      -- Push chained compare blocks: join, then eval blocks
      let da := pushDemand da liveAfter  -- join
      let da := Id.run do
        let mut da := da
        let mut j := 0
        while j < n - 1 do
          if h : j < cumDemands.size then
            da := pushDemand da cumDemands[j]
          j := j + 1
        da
      (allFV ∪ leftFV, da)

  | .BinOp _ left _ right =>
    let (fv, da) := backwardExprBlocks right liveAfter fv da
    backwardExprBlocks left liveAfter fv da
  | .UnaryOp _ _ operand => backwardExprBlocks operand liveAfter fv da
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    let (fv, da) := kwargs.foldr (init := (fv, da)) fun kw (fv, da) =>
      match kw with | .mk_keyword _ _ v => backwardExprBlocks v liveAfter fv da
    let (fv, da) := args.foldr (init := (fv, da)) fun a (fv, da) =>
      backwardExprBlocks a liveAfter fv da
    backwardExprBlocks f liveAfter fv da
  | .Attribute _ value _ _ => backwardExprBlocks value liveAfter fv da
  | .Subscript _ value slice _ =>
    let (fv, da) := backwardExprBlocks slice liveAfter fv da
    backwardExprBlocks value liveAfter fv da
  | .Starred _ value _ => backwardExprBlocks value liveAfter fv da
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    let (fv, da) := values.foldr (init := (fv, da)) fun v (fv, da) =>
      backwardExprBlocks v liveAfter fv da
    keys.foldr (init := (fv, da)) fun k (fv, da) =>
      match k with
      | .some_expr _ ke => backwardExprBlocks ke liveAfter fv da
      | _ => (fv, da)
  | .Set _ ⟨_, elts⟩ =>
    elts.foldr (init := (fv, da)) fun e (fv, da) =>
      backwardExprBlocks e liveAfter fv da
  | .List _ ⟨_, elts⟩ _ =>
    elts.foldr (init := (fv, da)) fun e (fv, da) =>
      backwardExprBlocks e liveAfter fv da
  | .Tuple _ ⟨_, elts⟩ _ =>
    elts.foldr (init := (fv, da)) fun e (fv, da) =>
      backwardExprBlocks e liveAfter fv da
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    let (fv, da) := match fmtSpec with
      | some spec => backwardExprBlocks spec liveAfter fv da
      | none => (fv, da)
    backwardExprBlocks value liveAfter fv da
  | .JoinedStr _ ⟨_, values⟩ =>
    values.foldr (init := (fv, da)) fun v (fv, da) =>
      backwardExprBlocks v liveAfter fv da
  | .TemplateStr _ ⟨_, values⟩ =>
    values.foldr (init := (fv, da)) fun v (fv, da) =>
      backwardExprBlocks v liveAfter fv da
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
    let (fv, da) := match lower with
      | some e => backwardExprBlocks e liveAfter fv da | none => (fv, da)
    let (fv, da) := match upper with
      | some e => backwardExprBlocks e liveAfter fv da | none => (fv, da)
    match step with
      | some e => backwardExprBlocks e liveAfter fv da | none => (fv, da)
  | _ => (fv, da)

/-- Process a simple statement: compute block demands and liveness in one pass.
    Returns (liveBefore, updatedDA). Replaces separate backwardStmtExprBlocks
    + updateLiveness calls to avoid double-traversing expression trees. -/
private partial def processSimpleStmt (s : stmt SourceRange)
    (liveAfter : Std.HashSet String) (da : DemandArr)
    : Std.HashSet String × DemandArr :=
  match s with
  | .Assign _ ⟨_, targets⟩ value _ =>
    -- Two passes required: erase all defs first, then add all reads.
    -- Cannot merge into one pass because CPython assigns targets left-to-right,
    -- so `x[0] = x = expr` reads OLD x (subscript) then defines NEW x (name).
    -- Two-pass ensures reads win: live = (liveAfter \ allDefs) ∪ allReads.
    let live := targets.foldl (init := liveAfter) fun acc t => removeTargetDefs acc t
    let live := targets.foldl (init := live) fun acc t => addTargetReads acc t
    backwardExprBlocks value live live da
  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    let live := removeTargetDefs liveAfter target
    let live := addTargetReads live target
    match value with
    | some v => backwardExprBlocks v live live da
    | none => (live, da)
  | .AugAssign _ target _ value =>
    -- AugAssign reads both target and value; reads win over writes
    let (fv, da) := backwardExprBlocks target liveAfter liveAfter da
    backwardExprBlocks value liveAfter fv da
  | .Import _ ⟨_, aliases⟩ =>
    (aliases.foldl (init := liveAfter) fun acc a => acc.erase (a.asname.getD a.name), da)
  | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
    (aliases.foldl (init := liveAfter) fun acc a => acc.erase (a.asname.getD a.name), da)
  | .Expr _ value => backwardExprBlocks value liveAfter liveAfter da
  | .Return _ ⟨_, value⟩ =>
    match value with
    | some v => backwardExprBlocks v liveAfter liveAfter da
    | none => (liveAfter, da)
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    let (fv, da) := match cause with
      | some e => backwardExprBlocks e liveAfter liveAfter da
      | none => (liveAfter, da)
    match exc with
    | some e => backwardExprBlocks e liveAfter fv da
    | none => (fv, da)
  | .Assert _ test ⟨_, msg⟩ =>
    let (fv, da) := match msg with
      | some m => backwardExprBlocks m liveAfter liveAfter da
      | none => (liveAfter, da)
    backwardExprBlocks test liveAfter fv da
  | .Delete _ ⟨_, targets⟩ =>
    targets.foldr (init := (liveAfter, da)) fun t (fv, da) =>
      backwardExprBlocks t liveAfter fv da
  | _ => (liveAfter, da)

/-- Main demand analysis. Single backward pass over statements.
    Returns `da` where `da[da.size - (i+1)]` = demand for block `i`.
    Block 0 (entry) is always `#[]`. -/
public partial def demandAnalysis (stmts : Array (stmt SourceRange))
    (globals : Std.HashSet String := {})
    : Array DemandVars :=
  let (_, da) := backwardStmts stmts {} #[]
  -- Push bb0 demand (always empty — entry block)
  let da := da.push #[]
  -- Exclude globals (module-level functions, classes, imports) — these are
  -- resolved via qualified name lookup, not block parameters.
  if globals.isEmpty then da
  else da.map fun dv => dv.filter (!globals.contains ·)
where
  /-- Backward pass over statement array. Returns (liveBeforeStmts, updatedDa). -/
  backwardStmts (stmts : Array (stmt SourceRange))
      (liveAfter : Std.HashSet String) (da : DemandArr)
      : Std.HashSet String × DemandArr := Id.run do
    let mut live := liveAfter
    let mut da := da
    let mut i := stmts.size
    while i > 0 do
      i := i - 1
      if h : i < stmts.size then
        let s := stmts[i]
        if isSimpleStmt s then
          let (live', da') := processSimpleStmt s live da
          live := live'
          da := da'
        else
          let (liveBefore, da') := backwardCompound s live da
          live := liveBefore
          da := da'
    (live, da)

  /-- Backward analysis for a compound statement.
      Pushes demand entries for sub-bodies and the statement's own blocks
      in reverse block-ID order. Returns (liveBefore, updatedDa). -/
  backwardCompound (s : stmt SourceRange) (liveAfter : Std.HashSet String)
      (da : DemandArr) : Std.HashSet String × DemandArr :=
    match s with
    | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      -- Phase 2 allocates: thenBlock(N), elseBlock(N+1), joinBlock(N+2),
      -- then condition expr blocks, then body blocks, then orelse blocks.
      -- Backward: orelse blocks, body blocks, cond expr blocks, join, else, then.
      let (elseLive, da) := backwardStmts orelse liveAfter da
      let (thenLive, da) := backwardStmts body liveAfter da
      let (liveBefore, da) := backwardExprBlocks test liveAfter (thenLive ∪ elseLive) da
      -- Push join, else, then demands (reverse allocation order)
      let da := pushDemand da liveAfter    -- joinBlock
      let da := pushDemand da elseLive     -- elseBlock
      let da := pushDemand da thenLive     -- thenBlock
      (liveBefore, da)

    | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      -- Phase 2 allocates: iterInitBlock(N), headerBlock(N+1), endBlock(N+2),
      -- then iter expr blocks, then body blocks, then orelse blocks.
      let (elseLive, da) := backwardStmts orelse liveAfter da
      -- First pass: compute bodyLive to determine headerLive
      let (bodyLive, _) := backwardStmts body liveAfter #[]
      -- For-loop target is usually a Name, but `for obj.attr in ...` or
      -- `for a[i] in ...` are valid Python and read obj/a+i.
      let headerLive := removeTargetDefs (bodyLive ∪ elseLive ∪ liveAfter) target
      let headerLive := addTargetReads headerLive target
      -- Second pass: push body sub-block demands with headerLive as liveAfter
      -- (body flows back to header via back-edge)
      let (_, da) := backwardStmts body headerLive da
      let (liveBefore, da) := backwardExprBlocks iter liveAfter headerLive da
      -- Push endBlock, headerBlock, iterInitBlock (reverse order)
      let da := pushDemand da (elseLive ∪ liveAfter)  -- endBlock
      let da := pushDemand da headerLive               -- headerBlock
      let da := pushDemand da headerLive               -- iterInitBlock (same as header)
      (liveBefore, da)

    | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      -- Cyclic dependency: testLive needs bodyLive (back-edge), but body
      -- sub-block demands need testLive as their liveAfter. Resolved with
      -- two body passes: pass 1 computes bodyLive, pass 2 pushes body DA.
      --
      -- FIXME: possible single-pass optimization: compute test FV/DA into a
      -- separate array, body once with (testFV ∪ elseLive ∪ liveAfter), then
      -- patch test DA entries with bodyLive (monotonic — adding demanded
      -- variables is safe). Pseudocode:
      --   let (elseLive, da) := backwardStmts orelse liveAfter da
      --   let (testFV, testDa) := backwardExprBlocks test elseLive {} #[]
      --   let (bodyLive, da) := backwardStmts body (testFV ∪ liveAfter) da
      --   let da := testDa.foldl (init := da) fun da d =>
      --     da.push (d.toSet ∪ bodyLive).toArray
      -- However, body sub-block demands (from compound stmts inside body)
      -- also depend on the back-edge liveAfter, so those would need patching
      -- too — making the single-pass version significantly more complex.


      -- Phase 2 allocates: testBlock(N), bodyBlock(N+1), endBlock(N+2),
      -- then test expr blocks, then body blocks, then orelse blocks.
      let (elseLive, da) := backwardStmts orelse liveAfter da
      -- Pass 1: compute bodyLive to determine testLive
      let (bodyLive, _) := backwardStmts body liveAfter #[]
      let testLive := addFreeVarsExpr (bodyLive ∪ elseLive ∪ liveAfter) test
      -- Second pass: push body sub-block demands with testLive as liveAfter
      -- (body flows back to testBlock via back-edge)
      let (_, da) := backwardStmts body testLive da
      let (_, da) := backwardExprBlocks test liveAfter {} da
      -- Push endBlock, bodyBlock, testBlock (reverse order)
      let da := pushDemand da (elseLive ∪ liveAfter)  -- endBlock
      let da := pushDemand da testLive                 -- bodyBlock (needs testLive for back-edge)
      let da := pushDemand da testLive                 -- testBlock
      (testLive, da)

    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ => Id.run do
      -- Complex block allocation: handler blocks, joinBlock, maybe finallyBlock,
      -- maybe reraiseBlock, then body blocks, orelse blocks, handler body blocks,
      -- finally blocks.
      let afterTarget := liveAfter
      let (finallyLive, da) := backwardStmts finalbody liveAfter da
      let finallyTarget := if finalbody.isEmpty then liveAfter else finallyLive ∪ liveAfter
      -- Handler bodies (in reverse)
      let mut handlerBodyLives : Array (Std.HashSet String) := #[]
      let mut da := da
      let mut i := handlers.size
      while i > 0 do
        i := i - 1
        if h : i < handlers.size then
          match handlers[i] with
          | .ExceptHandler _ ⟨_, exType⟩ _ ⟨_, hBody⟩ =>
            let (hBodyLive, da') := backwardStmts hBody finallyTarget da
            da := da'
            match exType with
            | some te => da := (backwardExprBlocks te liveAfter {} da).2
            | none => pure ()
            handlerBodyLives := handlerBodyLives.push hBodyLive
      let r1 := backwardStmts orelse finallyTarget da
      da := r1.2
      let orelseLive := r1.1
      let r2 := backwardStmts body finallyTarget da
      da := r2.2
      let bodyLive := r2.1
      -- Push blocks in reverse allocation order (join, reraise, finally, handlers)
      -- Allocation order is: finally, reraise, join — so reverse is: join, reraise, finally
      let lastHandlerIsTyped := match handlers.back? with
        | some (.ExceptHandler _ ⟨_, exType⟩ _ _) => exType.isSome
        | _ => false
      -- joinBlock (highest ID, pushed first)
      da := pushDemand da afterTarget
      -- reraiseBlock (if present)
      if lastHandlerIsTyped || !finalbody.isEmpty then
        da := pushDemand da afterTarget
      -- finallyBlock (if non-empty)
      if !finalbody.isEmpty then
        da := pushDemand da finallyLive
      -- Handler blocks (in reverse)
      let mut handlerLiveAll := ({}:Std.HashSet String)
      let mut j := handlers.size
      let mut hblIdx := 0
      while j > 0 do
        j := j - 1
        if h : j < handlers.size then
          match handlers[j] with
          | .ExceptHandler _ ⟨_, exType⟩ errname _ =>
            let errDef := match errname.val with
              | some ⟨_, name⟩ => ({}:Std.HashSet String).insert name | none => {}
            let hLive := if h2 : hblIdx < handlerBodyLives.size then
              handlerBodyLives[hblIdx] else {}
            hblIdx := hblIdx + 1
            handlerLiveAll := handlerLiveAll ∪ (hLive \ errDef)
            if exType.isSome then
              da := pushDemand da (hLive \ errDef)  -- hBodyBlock
            da := pushDemand da (hLive \ errDef)    -- hBlock
      let liveBefore := bodyLive ∪ handlerLiveAll ∪ orelseLive
      (liveBefore, da)

    | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
      if items.size > 0 then
        let (bodyLive, da) := backwardStmts body liveAfter da
        -- Process context expressions for block demands and FVs in one pass
        let (itemFVs, da) := items.foldr (init := (#[], da)) fun item (fvs, da) =>
          match item with
          | .mk_withitem _ e _ =>
            let (efv, da) := backwardExprBlocks e liveAfter {} da
            (fvs.push efv, da)
        -- itemFVs[0] = fv of last item, itemFVs[1] = fv of second-to-last, ...
        -- Compute liveBefore: remove `as` target defs, add context expr reads
        let liveBefore := Id.run do
          let mut liveBefore := bodyLive ∪ liveAfter
          let mut fvIdx := items.size
          for item in items do
            fvIdx := fvIdx - 1
            match item with
            | .mk_withitem _ _ ⟨_, optVar⟩ =>
              liveBefore := match optVar with
                | some varExpr =>
                  addTargetReads (removeTargetDefs liveBefore varExpr) varExpr
                | none => liveBefore
              if h : fvIdx < itemFVs.size then
                liveBefore := liveBefore ∪ itemFVs[fvIdx]
          liveBefore
        -- Push normalExitBlock, reraiseBlock, excExitBlock, enterBlock (reverse order)
        -- enterBlock demands bodyLive (not minus defs): the `as` variable is defined
        -- in the enclosing block and must be threaded to enterBlock as a param.
        let da := pushDemand da liveAfter              -- normalExitBlock
        let da := pushDemand da liveAfter              -- reraiseBlock
        let da := pushDemand da (bodyLive ∪ liveAfter) -- excExitBlock
        let da := pushDemand da bodyLive               -- enterBlock
        (liveBefore, da)
      else
        (liveAfter, da)

    | _ => (liveAfter, da)

/-! ## Summary-Based Demand Analysis (Step 13)

Two-stage approach: (1) single forward AST pass collects per-block summaries
(reads, defs, successors), (2) fixpoint solver computes liveIn = demand.
Eliminates double-traversal of loop bodies needed by the backward pass.
-/

/-- Per-block summary for fixpoint demand analysis. -/
private structure BlockSummary where
  defs : Std.HashSet String := {}
  reads : Std.HashSet String := {}
  successors : Array Nat := #[]
  deriving Inhabited

/-- State for the forward summarize pass. -/
private structure SumState where
  nextIdx : Nat := 0
  summaries : Array BlockSummary := #[]

/-- Context for loop/exception targets during summarization. -/
private structure SumCtx where
  breakTarget : Option Nat := none
  contTarget : Option Nat := none
  excTarget : Option Nat := none

private def sumAlloc (st : SumState) : Nat × SumState :=
  (st.nextIdx, { nextIdx := st.nextIdx + 1,
                  summaries := st.summaries.push {} })

private def sumAddReads (st : SumState) (idx : Nat) (r : Std.HashSet String)
    : SumState :=
  if idx < st.summaries.size then
    let s := st.summaries[idx]!
    let s' : BlockSummary := { s with reads := s.reads ∪ r }
    { st with summaries := st.summaries.set! idx s' }
  else st

private def sumAddRead (st : SumState) (idx : Nat) (name : String) : SumState :=
  if idx < st.summaries.size then
    let s := st.summaries[idx]!
    let s' : BlockSummary := { s with reads := s.reads.insert name }
    { st with summaries := st.summaries.set! idx s' }
  else st

private def sumAddSucc (st : SumState) (idx : Nat) (succs : Array Nat)
    : SumState :=
  if idx < st.summaries.size then
    let s := st.summaries[idx]!
    let s' : BlockSummary := { s with successors := s.successors ++ succs }
    { st with summaries := st.summaries.set! idx s' }
  else st

private def sumSetDefs (st : SumState) (idx : Nat) (defs : Std.HashSet String)
    : SumState :=
  if idx < st.summaries.size then
    let s := st.summaries[idx]!
    let s' : BlockSummary := { s with defs := defs }
    { st with summaries := st.summaries.set! idx s' }
  else st

private def sumSetBlock (st : SumState) (idx : Nat) (s : BlockSummary)
    : SumState :=
  if idx < st.summaries.size then
    { st with summaries := st.summaries.set! idx s }
  else st

/-- Collect variable names defined by an assignment target. -/
private def collectTargetDefs (e : expr SourceRange) : Std.HashSet String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => ({} : Std.HashSet String).insert name
  | .Starred _ value _ => collectTargetDefs value
  | .Tuple _ ⟨_, elts⟩ _ | .List _ ⟨_, elts⟩ _ =>
    elts.foldl (init := {}) fun acc e => acc ∪ collectTargetDefs e
  | _ => {}

/-- Forward expression summarizer. Adds reads to block summaries and allocates
    expression sub-blocks (BoolOp, IfExp, chained Compare) with proper
    reads/successors so the fixpoint solver computes correct demands.
    Returns (newCurBlock, newCurDefs, st).
    curDefs tracks variables defined earlier in curBlock (for upward-exposure). -/
public partial def demandAnalysis2 (stmts : Array (stmt SourceRange))
    (globals : Std.HashSet String := {})
    : Array DemandVars :=
  -- Allocate bb0 (entry block)
  let (bb0, st) := sumAlloc {}
  -- Summarize function body starting in bb0
  let (_, _, st) := summarizeStmts stmts bb0 {} st
  -- Solve demands
  let demands := solveDemands st.summaries
  -- Convert to DemandArr format (reversed, sorted, bb0 = empty)
  -- PythonToSSA reads da[da.size - (blockId + 1)], so reverse allocation order.
  let da : DemandArr := Id.run do
    let mut da : DemandArr := #[]
    let mut i := demands.size
    while i > 0 do
      i := i - 1
      if i == bb0 then
        da := da.push #[]  -- entry block always empty
      else if h : i < demands.size then
        da := da.push (demands[i].toArray.qsort (· < ·))
      else
        da := da.push #[]
    da
  if globals.isEmpty then da
  else da.map fun dv => dv.filter (!globals.contains ·)
where
  /-- Add a name read to curBlock if not already defined in this block. -/
  addRead (name : String) (curBlock : Nat) (curDefs : Std.HashSet String)
      (st : SumState) : SumState :=
    if curDefs.contains name then st
    else sumAddRead st curBlock name

  /-- Process expression: add reads to block summaries, allocate expression
      blocks. Returns (newCurBlock, newCurDefs, st). -/
  summarizeExpr (e : expr SourceRange) (curBlock : Nat)
      (curDefs : Std.HashSet String) (st : SumState)
      : Nat × Std.HashSet String × SumState :=
    match e with
    | .Name _ ⟨_, name⟩ _ =>
      (curBlock, curDefs, addRead name curBlock curDefs st)

    | .BoolOp _ _ ⟨_, values⟩ =>
      if values.size < 2 then
        values.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) v =>
          summarizeExpr v cur defs st
      else
        let n := values.size
        -- Allocate n blocks: eval[0]..eval[n-2], joinBlock
        let (blockIds, st) := Id.run do
          let mut ids : Array Nat := #[]
          let mut st := st
          for _ in [:n] do
            let (bid, st') := sumAlloc st
            st := st'
            ids := ids.push bid
          (ids, st)
        let joinBlock := blockIds[n - 1]!
        -- Evaluate values[0] in curBlock
        let (cur, _, st) := summarizeExpr values[0]! curBlock curDefs st
        -- curBlock condBranches to eval[0] or joinBlock
        let st := sumAddSucc st cur #[blockIds[0]!, joinBlock]
        -- Process subsequent values in eval blocks
        let (_, st) := Id.run do
          let mut cur := blockIds[0]!
          let mut st := st
          for i in [1:n] do
            if h : i < values.size then
              -- Evaluate values[i] in cur (fresh eval block, defs={})
              let (cur', _, st') := summarizeExpr values[i] cur {} st
              st := st'
              if i < n - 1 then
                -- condBranch to next eval or join
                st := sumAddSucc st cur' #[blockIds[i]!, joinBlock]
                cur := blockIds[i]!
              else
                -- Last value: branch to joinBlock
                st := sumAddSucc st cur' #[joinBlock]
          (cur, st)
        (joinBlock, {}, st)

    | .IfExp _ test body orelse =>
      -- In PythonToSSA: test sub-blocks first, then allocate then/else/join
      let (cur, defs, st) := summarizeExpr test curBlock curDefs st
      let (thenBlock, st) := sumAlloc st
      let (elseBlock, st) := sumAlloc st
      let (joinBlock, st) := sumAlloc st
      -- curBlock condBranches to then/else
      let st := sumAddSucc st cur #[thenBlock, elseBlock]
      -- Then: evaluate body
      let (thenLast, _, st) := summarizeExpr body thenBlock {} st
      let st := sumAddSucc st thenLast #[joinBlock]
      -- Else: evaluate orelse
      let (elseLast, _, st) := summarizeExpr orelse elseBlock {} st
      let st := sumAddSucc st elseLast #[joinBlock]
      (joinBlock, {}, st)

    | .Compare _ left _ ⟨_, comparators⟩ =>
      if comparators.size <= 1 then
        let (cur, defs, st) := summarizeExpr left curBlock curDefs st
        comparators.foldl (init := (cur, defs, st)) fun (cur, defs, st) c =>
          summarizeExpr c cur defs st
      else
        let n := comparators.size
        -- Allocate n blocks: eval[0]..eval[n-2], joinBlock
        let (blockIds, st) := Id.run do
          let mut ids : Array Nat := #[]
          let mut st := st
          for _ in [:n] do
            let (bid, st') := sumAlloc st
            st := st'
            ids := ids.push bid
          (ids, st)
        let joinBlock := blockIds[n - 1]!
        -- Evaluate left in curBlock
        let (cur, _, st) := summarizeExpr left curBlock curDefs st
        -- Evaluate comparators[0] in curBlock
        let (cur, _, st) := summarizeExpr comparators[0]! cur {} st
        -- condBranch to eval[0] or joinBlock
        let st := sumAddSucc st cur #[blockIds[0]!, joinBlock]
        -- Process subsequent comparators in eval blocks
        let (_, st) := Id.run do
          let mut cur := blockIds[0]!
          let mut st := st
          for i in [1:n] do
            if h : i < comparators.size then
              let (cur', _, st') := summarizeExpr comparators[i] cur {} st
              st := st'
              if i < n - 1 then
                st := sumAddSucc st cur' #[blockIds[i]!, joinBlock]
                cur := blockIds[i]!
              else
                st := sumAddSucc st cur' #[joinBlock]
          (cur, st)
        (joinBlock, {}, st)

    -- Non-block-creating cases: just add reads, curBlock unchanged
    | .BinOp _ left _ right =>
      let (cur, defs, st) := summarizeExpr left curBlock curDefs st
      summarizeExpr right cur defs st
    | .UnaryOp _ _ operand => summarizeExpr operand curBlock curDefs st
    | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
      let (cur, defs, st) := summarizeExpr f curBlock curDefs st
      let (cur, defs, st) := args.foldl (init := (cur, defs, st))
        fun (cur, defs, st) a => summarizeExpr a cur defs st
      kwargs.foldl (init := (cur, defs, st)) fun (cur, defs, st) kw =>
        match kw with | .mk_keyword _ _ v => summarizeExpr v cur defs st
    | .Attribute _ value _ _ => summarizeExpr value curBlock curDefs st
    | .Subscript _ value slice _ =>
      let (cur, defs, st) := summarizeExpr value curBlock curDefs st
      summarizeExpr slice cur defs st
    | .Starred _ value _ => summarizeExpr value curBlock curDefs st
    | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
      let (cur, defs, st) := keys.foldl (init := (curBlock, curDefs, st))
        fun (cur, defs, st) k =>
          match k with
          | .some_expr _ ke => summarizeExpr ke cur defs st
          | _ => (cur, defs, st)
      values.foldl (init := (cur, defs, st)) fun (cur, defs, st) v =>
        summarizeExpr v cur defs st
    | .Set _ ⟨_, elts⟩ =>
      elts.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) e =>
        summarizeExpr e cur defs st
    | .List _ ⟨_, elts⟩ _ =>
      elts.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) e =>
        summarizeExpr e cur defs st
    | .Tuple _ ⟨_, elts⟩ _ =>
      elts.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) e =>
        summarizeExpr e cur defs st
    | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
      let (cur, defs, st) := summarizeExpr value curBlock curDefs st
      match fmtSpec with
      | some spec => summarizeExpr spec cur defs st
      | none => (cur, defs, st)
    | .JoinedStr _ ⟨_, values⟩ =>
      values.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) v =>
        summarizeExpr v cur defs st
    | .TemplateStr _ ⟨_, values⟩ =>
      values.foldl (init := (curBlock, curDefs, st)) fun (cur, defs, st) v =>
        summarizeExpr v cur defs st
    | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
      let (cur, defs, st) := match lower with
        | some e => summarizeExpr e curBlock curDefs st
        | none => (curBlock, curDefs, st)
      let (cur, defs, st) := match upper with
        | some e => summarizeExpr e cur defs st
        | none => (cur, defs, st)
      match step with
        | some e => summarizeExpr e cur defs st
        | none => (cur, defs, st)
    | _ => (curBlock, curDefs, st)

  /-- Process a simple statement: add reads/defs to curBlock.
      Returns (newCurBlock, newCurDefs, terminated, st). -/
  summarizeSimpleStmt (s : stmt SourceRange) (curBlock : Nat)
      (curDefs : Std.HashSet String) (ctx : SumCtx) (st : SumState)
      : Nat × Std.HashSet String × Bool × SumState :=
    match s with
    | .Assign _ ⟨_, targets⟩ value _ =>
      -- Process value expression (may create expression blocks)
      let (cur, defs, st) := summarizeExpr value curBlock curDefs st
      -- Target reads (subscript/attribute targets read their objects)
      let tgtReads := targets.foldl (init := ({}:Std.HashSet String)) addTargetReads
      let st := tgtReads.fold (init := st) fun st name =>
        addRead name cur defs st
      -- Target defs
      let tgtDefs := targets.foldl (init := ({}:Std.HashSet String)) fun acc t =>
        acc ∪ collectTargetDefs t
      (cur, defs ∪ tgtDefs, false, st)
    | .AnnAssign _ target _ ⟨_, value⟩ _ =>
      let (cur, defs, st) := match value with
        | some v => summarizeExpr v curBlock curDefs st
        | none => (curBlock, curDefs, st)
      let tgtReads := addTargetReads {} target
      let st := tgtReads.fold (init := st) fun st name =>
        addRead name cur defs st
      (cur, defs ∪ collectTargetDefs target, false, st)
    | .AugAssign _ target _ value =>
      let (cur, defs, st) := summarizeExpr target curBlock curDefs st
      let (cur, defs, st) := summarizeExpr value cur defs st
      (cur, defs, false, st)
    | .Expr _ value =>
      let (cur, defs, st) := summarizeExpr value curBlock curDefs st
      (cur, defs, false, st)
    | .Return _ ⟨_, value⟩ =>
      let (cur, defs, st) := match value with
        | some v => summarizeExpr v curBlock curDefs st
        | none => (curBlock, curDefs, st)
      -- Return has no successors (handled by caller)
      (cur, defs, true, st)
    | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
      let (cur, defs, st) := match exc with
        | some e => summarizeExpr e curBlock curDefs st
        | none => (curBlock, curDefs, st)
      let (cur, defs, st) := match cause with
        | some e => summarizeExpr e cur defs st
        | none => (cur, defs, st)
      -- Raise goes to exception handler if present
      let st := match ctx.excTarget with
        | some t => sumAddSucc st cur #[t]
        | none => st
      (cur, defs, true, st)
    | .Break .. =>
      let st := match ctx.breakTarget with
        | some t => sumAddSucc st curBlock #[t]
        | none => st
      (curBlock, curDefs, true, st)
    | .Continue .. =>
      let st := match ctx.contTarget with
        | some t => sumAddSucc st curBlock #[t]
        | none => st
      (curBlock, curDefs, true, st)
    | .Assert _ test ⟨_, msg⟩ =>
      let (cur, defs, st) := summarizeExpr test curBlock curDefs st
      let (cur, defs, st) := match msg with
        | some m => summarizeExpr m cur defs st
        | none => (cur, defs, st)
      (cur, defs, false, st)
    | .Delete _ ⟨_, targets⟩ =>
      let (cur, defs, st) := targets.foldl (init := (curBlock, curDefs, st))
        fun (cur, defs, st) t => summarizeExpr t cur defs st
      (cur, defs, false, st)
    | .Import _ ⟨_, aliases⟩ =>
      let newDefs := aliases.foldl (init := curDefs) fun acc a =>
        acc.insert (a.asname.getD a.name)
      (curBlock, newDefs, false, st)
    | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
      let newDefs := aliases.foldl (init := curDefs) fun acc a =>
        acc.insert (a.asname.getD a.name)
      (curBlock, newDefs, false, st)
    | _ => (curBlock, curDefs, false, st)

  /-- Summarize a statement array. Tracks current block; splits on compounds.
      Returns (lastBlock, terminated, st). lastBlock's successors are NOT set
      unless terminated — caller must set them. -/
  summarizeStmts (stmts : Array (stmt SourceRange)) (curBlock : Nat)
      (ctx : SumCtx) (st : SumState)
      : Nat × Bool × SumState := Id.run do
    let mut cur := curBlock
    let mut curDefs : Std.HashSet String := {}
    let mut st := st
    let mut terminated := false
    for s in stmts do
      if terminated then break  -- dead code after terminator
      if isSimpleStmt s then
        let (cur', defs', term, st') := summarizeSimpleStmt s cur curDefs ctx st
        cur := cur'
        curDefs := defs'
        terminated := term
        st := st'
      else
        -- Compound stmt: finalize current block, process compound
        let (cont, term, st') := summarizeCompound s cur curDefs ctx st
        cur := cont
        curDefs := {}  -- fresh block
        terminated := term
        st := st'
    -- Set defs on the final block
    if !terminated then
      st := sumSetDefs st cur curDefs
    (cur, terminated, st)

  /-- Summarize a compound statement. Finalizes curBlock and processes sub-bodies.
      Returns (contBlock, terminated, st) where contBlock is the continuation. -/
  summarizeCompound (s : stmt SourceRange) (curBlock : Nat)
      (curDefs : Std.HashSet String) (ctx : SumCtx) (st : SumState)
      : Nat × Bool × SumState :=
    match s with
    | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      -- Allocate then, else, join
      let (thenBlock, st) := sumAlloc st
      let (elseBlock, st) := sumAlloc st
      let (joinBlock, st) := sumAlloc st
      -- Evaluate test in curBlock (may create expression blocks)
      let (cur, _, st) := summarizeExpr test curBlock curDefs st
      -- curBlock condBranches to then/else
      let st := sumAddSucc st cur #[thenBlock, elseBlock]
      let st := sumSetDefs st cur curDefs
      -- Then body
      let (thenLast, thenTerm, st) := summarizeStmts body thenBlock ctx st
      if !thenTerm then
        let st := sumAddSucc st thenLast #[joinBlock]
        -- Else body
        let (elseLast, elseTerm, st) := summarizeStmts orelse elseBlock ctx st
        if !elseTerm then
          let st := sumAddSucc st elseLast #[joinBlock]
          (joinBlock, false, st)
        else
          (joinBlock, false, st)
      else
        let (elseLast, elseTerm, st) := summarizeStmts orelse elseBlock ctx st
        if !elseTerm then
          let st := sumAddSucc st elseLast #[joinBlock]
          (joinBlock, false, st)
        else
          -- Both branches terminate
          (joinBlock, true, st)

    | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      -- Allocate iterInit, header, end
      let (iterInitBlock, st) := sumAlloc st
      let (headerBlock, st) := sumAlloc st
      let (endBlock, st) := sumAlloc st
      -- Evaluate iter in curBlock
      let (cur, _, st) := summarizeExpr iter curBlock curDefs st
      let st := sumAddSucc st cur #[iterInitBlock]
      let st := sumSetDefs st cur curDefs
      -- iterInitBlock → headerBlock
      let st := sumSetBlock st iterInitBlock
        { reads := {}, defs := {}, successors := #[headerBlock] }
      -- headerBlock: target defs, next()/iter() reads
      -- headerBlock branches to body or endBlock
      let tgtDefs := collectTargetDefs target
      let tgtReads := addTargetReads {} target
      let st := sumSetBlock st headerBlock
        { reads := tgtReads, defs := tgtDefs,
          successors := #[endBlock] }  -- body successor added below
      -- Body with loop context
      let loopCtx := { ctx with
        breakTarget := some endBlock
        contTarget := some headerBlock }
      let (bodyFirst, st) := sumAlloc st
      let st := sumAddSucc st headerBlock #[bodyFirst]
      let (bodyLast, bodyTerm, st) := summarizeStmts body bodyFirst loopCtx st
      -- Back-edge to header
      let st := if !bodyTerm then sumAddSucc st bodyLast #[headerBlock] else st
      -- Orelse in endBlock
      let (orelseLast, orelseTerm, st) := summarizeStmts orelse endBlock ctx st
      (orelseLast, orelseTerm, st)

    | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      -- Allocate test, body, end
      let (testBlock, st) := sumAlloc st
      let (bodyBlock, st) := sumAlloc st
      let (endBlock, st) := sumAlloc st
      -- curBlock → testBlock
      let st := sumAddSucc st curBlock #[testBlock]
      let st := sumSetDefs st curBlock curDefs
      -- testBlock: evaluate test expression
      let (testLast, _, st) := summarizeExpr test testBlock {} st
      let st := sumAddSucc st testLast #[bodyBlock, endBlock]
      -- Body with loop context
      let loopCtx := { ctx with
        breakTarget := some endBlock
        contTarget := some testBlock }
      let (bodyLast, bodyTerm, st) := summarizeStmts body bodyBlock loopCtx st
      -- Back-edge to testBlock
      let st := if !bodyTerm then sumAddSucc st bodyLast #[testBlock] else st
      -- Orelse in endBlock
      let (orelseLast, orelseTerm, st) := summarizeStmts orelse endBlock ctx st
      (orelseLast, orelseTerm, st)

    | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
      if items.size > 0 then
        -- Allocate enter, excExit, reraise, normalExit
        let (enterBlock, st) := sumAlloc st
        let (excExitBlock, st) := sumAlloc st
        let (reraiseBlock, st) := sumAlloc st
        let (normalExitBlock, st) := sumAlloc st
        -- Evaluate context expression in curBlock
        let (cur, defs, st) := match items[0]! with
          | .mk_withitem _ ctxExpr _ => summarizeExpr ctxExpr curBlock curDefs st
        -- Add `as` variable defs
        let defs := match items[0]! with
          | .mk_withitem _ _ ⟨_, optVar⟩ =>
            match optVar with
            | some varExpr => defs ∪ collectTargetDefs varExpr
            | none => defs
        let st := sumAddSucc st cur #[enterBlock]
        let st := sumSetDefs st cur defs
        -- enterBlock: body with exception target
        let bodyCtx := { ctx with excTarget := some excExitBlock }
        let (bodyLast, bodyTerm, st) := summarizeStmts body enterBlock bodyCtx st
        let st := if !bodyTerm then sumAddSucc st bodyLast #[normalExitBlock] else st
        -- excExitBlock → normalExitBlock or reraiseBlock
        let st := sumSetBlock st excExitBlock
          { reads := {}, defs := {}, successors := #[normalExitBlock, reraiseBlock] }
        -- reraiseBlock: no successors (raises)
        let st := sumSetBlock st reraiseBlock
          { reads := {}, defs := {}, successors := #[] }
        -- normalExitBlock: continuation
        (normalExitBlock, false, st)
      else
        (curBlock, false, st)

    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
      -- Allocate handler blocks (forward order)
      let (handlerInfo, st) := Id.run do
        let mut info : Array (Nat × Option Nat) := #[]  -- (hBlock, hBodyBlock?)
        let mut st := st
        for h in handlers do
          match h with
          | .ExceptHandler _ ⟨_, exType⟩ _ _ =>
            let (hBlock, st') := sumAlloc st
            st := st'
            let hBodyBlock ← match exType with
              | some _ => let (bid, st') := sumAlloc st; st := st'; pure (some bid)
              | none => pure none
            info := info.push (hBlock, hBodyBlock)
        (info, st)
      let lastHandlerIsTyped := match handlers.back? with
        | some (.ExceptHandler _ ⟨_, exType⟩ _ _) => exType.isSome
        | _ => false
      -- Allocate finally, reraise, join
      let (finallyBlock, st) := if finalbody.isEmpty then (none, st)
        else let (bid, st) := sumAlloc st; (some bid, st)
      let (reraiseBlock, st) := if lastHandlerIsTyped || !finalbody.isEmpty
        then let (bid, st) := sumAlloc st; (some bid, st)
        else (none, st)
      let (joinBlock, st) := sumAlloc st
      let afterTarget := match finallyBlock with
        | some fb => fb | none => joinBlock
      -- curBlock → body (with exception target)
      let excTarget := if handlerInfo.size > 0 then
        some handlerInfo[0]!.1
      else match finallyBlock with
        | some fb => some fb | none => none
      let st := sumSetDefs st curBlock curDefs
      -- Translate body with exception context
      let bodyCtx := { ctx with excTarget := excTarget }
      -- Body starts in a fresh block that curBlock branches to
      -- Actually, body continues in curBlock... no, PythonToSSA continues
      -- in the current block for try body.
      -- The try body is in the current block after curBlock is set up.
      -- Let me just pass curBlock's successors and have body start fresh.
      let st := sumAddSucc st curBlock #[]  -- body continues inline
      let (bodyLast, bodyTerm, st) := summarizeStmts body curBlock bodyCtx st
      -- Normal path → orelse → afterTarget
      let st := if !bodyTerm then
        let (orelseLast, orelseTerm, st) := summarizeStmts orelse bodyLast ctx st
        if !orelseTerm then sumAddSucc st orelseLast #[afterTarget] else st
      else st
      -- Handler blocks
      let st := Id.run do
        let mut st := st
        for i in [:handlerInfo.size] do
          if h : i < handlerInfo.size then
            let (hBlock, hBodyBlock) := handlerInfo[i]
            let nextBlock := if i + 1 < handlerInfo.size then
              handlerInfo[i + 1]!.1
            else match reraiseBlock with
              | some rb => match finallyBlock with
                | some fb => fb  | none => rb
              | none => afterTarget
            match handlers[i]!, hBodyBlock with
            | .ExceptHandler _ _ errname ⟨_, hBody⟩, some bodyBid =>
              -- Typed handler: hBlock condBranches to bodyBid or nextBlock
              let st' := sumSetBlock st hBlock
                { reads := {}, defs := {}, successors := #[bodyBid, nextBlock] }
              st := st'
              let errDef := match errname.val with
                | some ⟨_, name⟩ => ({} : Std.HashSet String).insert name
                | none => {}
              let (hBodyLast, hBodyTerm, st') := summarizeStmts hBody bodyBid
                { ctx with excTarget := none } st
              st := st'
              if !hBodyTerm then
                st := sumAddSucc st hBodyLast #[afterTarget]
            | .ExceptHandler _ _ errname ⟨_, hBody⟩, none =>
              -- Bare except: hBlock is the handler body
              let errDef := match errname.val with
                | some ⟨_, name⟩ => ({} : Std.HashSet String).insert name
                | none => {}
              let (hLast, hTerm, st') := summarizeStmts hBody hBlock
                { ctx with excTarget := none } st
              st := st'
              if !hTerm then
                st := sumAddSucc st hLast #[afterTarget]
        st
      -- Reraise block
      let st := match reraiseBlock with
        | some rb => sumSetBlock st rb
            { reads := {}, defs := {}, successors := #[] }
        | none => st
      -- Finally block
      let st := match finallyBlock with
        | some fb =>
          let (fbLast, fbTerm, st) := summarizeStmts finalbody fb ctx st
          if !fbTerm then
            match reraiseBlock with
            | some rb => sumAddSucc st fbLast #[rb, joinBlock]
            | none => sumAddSucc st fbLast #[joinBlock]
          else st
        | none => st
      (joinBlock, false, st)

    | _ => (curBlock, false, st)

  /-- Fixpoint solver: compute liveIn for each block.
      liveIn(B) = reads(B) ∪ (liveOut(B) \ defs(B))
      liveOut(B) = ∪ { liveIn(S) | S ∈ successors(B) }
      Monotonically increasing — converges when no liveIn grows. -/
  solveDemands (summaries : Array BlockSummary)
      : Array (Std.HashSet String) := Id.run do
    let n := summaries.size
    -- Initialize liveIn = reads for each block
    let mut liveIn : Array (Std.HashSet String) := summaries.map (·.reads)
    let mut changed := true
    while changed do
      changed := false
      -- Process in reverse order (approximation of reverse postorder)
      let mut i := n
      while i > 0 do
        i := i - 1
        if h : i < summaries.size then
          let s := summaries[i]
          -- liveOut = union of successors' liveIn
          let mut liveOut : Std.HashSet String := {}
          for succ in s.successors do
            if h2 : succ < liveIn.size then
              liveOut := liveOut ∪ liveIn[succ]
          -- liveIn = reads ∪ (liveOut \ defs)
          let newLiveIn := s.reads ∪ (liveOut \ s.defs)
          if h3 : i < liveIn.size then
            if newLiveIn.size != liveIn[i].size then
              liveIn := liveIn.set! i newLiveIn
              changed := true
    liveIn

end Strata.Python.Blockify

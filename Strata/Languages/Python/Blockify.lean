/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.PythonDialect
public import Strata.DDM.Util.SourceRange

/-!
# Phase 1: Statement Classification and Demand Analysis for PythonSSA

Provides utilities consumed by the Phase 2 SSA translator:

- **Statement classification**: `isSimpleStmt` distinguishes statements that
  can be emitted within a single block from compound statements that require
  control-flow splitting.
- **Expression block counting**: `countExprBlocks` counts how many SSA blocks
  BoolOp/IfExp/chained-Compare nodes will need during Phase 2 translation.
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

/-! ## Expression Block Counting -/

/-- Count the number of blocks that BoolOp and IfExp nodes will require
    during Phase 2 expression translation. Each BoolOp with n operands
    needs (n-1) intermediate blocks plus 1 join block = n blocks.
    Each IfExp needs 3 blocks (then, else, join).

    This is a lightweight traversal — just counting, no AST modification. -/
public partial def countExprBlocks (e : expr SourceRange) : Nat :=
  match e with
  | .BoolOp _ _ ⟨_, values⟩ =>
    -- n operands → n blocks (n-1 short-circuit branches + 1 join)
    let childCount := values.foldl (init := 0) fun acc v => acc + countExprBlocks v
    values.size + childCount
  | .IfExp _ test body orelse =>
    -- 3 blocks: then, else, join
    3 + countExprBlocks test + countExprBlocks body + countExprBlocks orelse
  | .BinOp _ left _ right =>
    countExprBlocks left + countExprBlocks right
  | .UnaryOp _ _ operand =>
    countExprBlocks operand
  | .Compare _ left _ ⟨_, comparators⟩ =>
    -- Chained comparisons (a < b < c) need short-circuit blocks: n blocks for n comparators
    let chainBlocks := if comparators.size > 1 then comparators.size else 0
    chainBlocks + countExprBlocks left + comparators.foldl (init := 0) fun acc c => acc + countExprBlocks c
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    countExprBlocks f
    + args.foldl (init := 0) fun acc a => acc + countExprBlocks a
    + kwargs.foldl (init := 0) fun acc kw =>
        match kw with | .mk_keyword _ _ v => acc + countExprBlocks v
  | .Attribute _ value _ _ => countExprBlocks value
  | .Subscript _ value slice _ => countExprBlocks value + countExprBlocks slice
  | .Starred _ value _ => countExprBlocks value
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    keys.foldl (init := 0) (fun acc k =>
      match k with
      | .some_expr _ ke => acc + countExprBlocks ke
      | _ => acc)
    + values.foldl (init := 0) fun acc v => acc + countExprBlocks v
  | .Set _ ⟨_, elts⟩ =>
    elts.foldl (init := 0) fun acc e => acc + countExprBlocks e
  | .List _ ⟨_, elts⟩ _ =>
    elts.foldl (init := 0) fun acc e => acc + countExprBlocks e
  | .Tuple _ ⟨_, elts⟩ _ =>
    elts.foldl (init := 0) fun acc e => acc + countExprBlocks e
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    let specCount := match fmtSpec with
      | some spec => countExprBlocks spec
      | none => 0
    countExprBlocks value + specCount
  | .Interpolation _ value _ _ ⟨_, fmtSpec⟩ =>
    let specCount := match fmtSpec with
      | some spec => countExprBlocks spec
      | none => 0
    countExprBlocks value + specCount
  | .JoinedStr _ ⟨_, values⟩ =>
    values.foldl (init := 0) fun acc v => acc + countExprBlocks v
  | .TemplateStr _ ⟨_, values⟩ =>
    values.foldl (init := 0) fun acc v => acc + countExprBlocks v
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
    let lo := match lower with | some e => countExprBlocks e | none => 0
    let hi := match upper with | some e => countExprBlocks e | none => 0
    let st := match step with | some e => countExprBlocks e | none => 0
    lo + hi + st
  | _ => 0

/-- Extract variable names from an assignment target (handles Name, Tuple, List). -/
private def extractNames (e : expr SourceRange) : Array String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => #[name]
  | .Tuple _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | .List _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | _ => #[]


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

/-- Add free variables referenced in an expression to an existing set. -/
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
    elts.foldl (init := acc) fun acc e => addTargetReads acc e
  | _ => acc

/-- Add free variables from a statement's expressions into an existing set. -/
private partial def addFreeVarsStmt (acc : Std.HashSet String)
    (s : stmt SourceRange) : Std.HashSet String :=
  match s with
  | .Assign _ ⟨_, targets⟩ value _ =>
    let acc := targets.foldl (init := acc) fun acc t => addTargetReads acc t
    addFreeVarsExpr acc value
  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    let acc := addTargetReads acc target
    match value with
    | some v => addFreeVarsExpr acc v
    | none => acc
  | .AugAssign _ target _ value =>
    addFreeVarsExpr (addFreeVarsExpr acc target) value
  | .Expr _ value => addFreeVarsExpr acc value
  | .Return _ ⟨_, value⟩ =>
    match value with | some v => addFreeVarsExpr acc v | none => acc
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    let acc := match exc with | some e => addFreeVarsExpr acc e | none => acc
    match cause with | some e => addFreeVarsExpr acc e | none => acc
  | .Assert _ test ⟨_, msg⟩ =>
    let acc := addFreeVarsExpr acc test
    match msg with | some m => addFreeVarsExpr acc m | none => acc
  | .Delete _ ⟨_, targets⟩ =>
    targets.foldl (init := acc) fun acc t => addFreeVarsExpr acc t
  | .If _ test _ _ => addFreeVarsExpr acc test
  | .For _ _ iter _ _ _ => addFreeVarsExpr acc iter
  | .While _ test _ _ => addFreeVarsExpr acc test
  | .With _ ⟨_, items⟩ _ _ =>
    items.foldl (init := acc) fun acc item =>
      match item with | .mk_withitem _ e _ => addFreeVarsExpr acc e
  | .Import .. | .ImportFrom .. | .Pass .. | .Break .. | .Continue .. | .Global ..
  | .Nonlocal .. => {}
  | _ => {}

/-- Variables defined (assigned) by a simple statement. -/
private def defsStmt (s : stmt SourceRange) : Std.HashSet String :=
  match s with
  | .Assign _ ⟨_, targets⟩ _ _ =>
    targets.foldl (init := {}) fun acc t =>
      (extractNames t).foldl (init := acc) fun a n => a.insert n
  | .AnnAssign _ target _ _ _ =>
    (extractNames target).foldl (init := {}) fun a n => a.insert n
  | .AugAssign _ target _ _ =>
    (extractNames target).foldl (init := {}) fun a n => a.insert n
  | .Import _ ⟨_, aliases⟩ =>
    aliases.foldl (init := {}) fun acc a => acc.insert (a.asname.getD a.name)
  | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
    aliases.foldl (init := {}) fun acc a => acc.insert (a.asname.getD a.name)
  | _ => {}

/-- Demand array built by backward pass. da[0] = last block's demand,
    da[da.size-1] = first allocated block's demand. -/
private abbrev DemandArr := Array DemandVars

private def pushDemand (da : DemandArr) (vars : Std.HashSet String) : DemandArr :=
  da.push (vars.toArray.qsort (· < ·))

/-- Backward demand analysis for expression blocks within an expression.
    Pushes demand entries in reverse block-ID order. Returns updated demand array. -/
private partial def backwardExprBlocks (e : expr SourceRange)
    (liveAfter : Std.HashSet String) (da : DemandArr) : DemandArr :=
  match e with
  | .BoolOp _ _ ⟨_, values⟩ =>
    if values.size < 2 then
      da
    else
      let n := values.size
      -- 1. Recurse into sub-expression blocks in reverse
      let da := values.foldr (init := da) fun v acc => backwardExprBlocks v liveAfter acc
      -- 2. Push BoolOp's own blocks in reverse allocation order
      -- Join block (highest ID)
      let da := pushDemand da liveAfter
      -- Eval blocks in reverse: blockIds[n-2] down to blockIds[0]
      let da := Id.run do
        let mut da := da
        let mut cumNeeded := liveAfter
        let mut i := n - 1
        while i >= 1 do
          if h : i < n then
            cumNeeded := addFreeVarsExpr cumNeeded values[i]
          da := pushDemand da cumNeeded
          if i == 0 then break  -- avoid underflow
          i := i - 1
        da
      da

  | .IfExp _ test body orelse =>
    -- Recurse into sub-expression blocks in reverse (orelse, body, test)
    let da := backwardExprBlocks orelse liveAfter da
    let da := backwardExprBlocks body liveAfter da
    let da := backwardExprBlocks test liveAfter da
    -- Push IfExp's 3 blocks in reverse allocation order: join, else, then
    -- FIXME: backwardsExprBlocks must also simultanously compute the liveAfter parts
    -- Otherwise we have a bunch of potentially expensive calls to addFreeVarsExpr that
    -- also walk statement array.
    let da := pushDemand da liveAfter  -- join
    let da := pushDemand da (addFreeVarsExpr liveAfter orelse)  -- else
    let da := pushDemand da (addFreeVarsExpr liveAfter body)  -- then
    da

  | .Compare _ left _ ⟨_, comparators⟩ =>
    if comparators.size <= 1 then
      let da := comparators.foldr (init := da) fun c acc => backwardExprBlocks c liveAfter acc
      backwardExprBlocks left liveAfter da
    else
      let n := comparators.size
      -- Recurse into sub-expression blocks in reverse
      let da := comparators.foldr (init := da) fun c acc => backwardExprBlocks c liveAfter acc
      let da := backwardExprBlocks left liveAfter da
      -- Push chained compare blocks in reverse: join, then eval blocks
      let da := pushDemand da liveAfter  -- join
      let da := Id.run do
        let mut da := da
        let mut cumNeeded := liveAfter
        let mut i := n - 1
        while i >= 1 do
          if h : i < comparators.size then
            cumNeeded := addFreeVarsExpr cumNeeded comparators[i]
          da := pushDemand da cumNeeded
          if i == 0 then break
          i := i - 1
        da
      da

  | .BinOp _ left _ right =>
    let da := backwardExprBlocks right liveAfter da
    backwardExprBlocks left liveAfter da
  | .UnaryOp _ _ operand => backwardExprBlocks operand liveAfter da
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    let da := kwargs.foldr (init := da) fun kw acc =>
      match kw with | .mk_keyword _ _ v => backwardExprBlocks v liveAfter acc
    let da := args.foldr (init := da) fun a acc => backwardExprBlocks a liveAfter acc
    backwardExprBlocks f liveAfter da
  | .Attribute _ value _ _ => backwardExprBlocks value liveAfter da
  | .Subscript _ value slice _ =>
    let da := backwardExprBlocks slice liveAfter da
    backwardExprBlocks value liveAfter da
  | .Starred _ value _ => backwardExprBlocks value liveAfter da
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    let da := values.foldr (init := da) fun v acc => backwardExprBlocks v liveAfter acc
    keys.foldr (init := da) fun k acc =>
      match k with
      | .some_expr _ ke => backwardExprBlocks ke liveAfter acc
      | _ => acc
  | .Set _ ⟨_, elts⟩ =>
    elts.foldr (init := da) fun e acc => backwardExprBlocks e liveAfter acc
  | .List _ ⟨_, elts⟩ _ =>
    elts.foldr (init := da) fun e acc => backwardExprBlocks e liveAfter acc
  | .Tuple _ ⟨_, elts⟩ _ =>
    elts.foldr (init := da) fun e acc => backwardExprBlocks e liveAfter acc
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    let da := match fmtSpec with
      | some spec => backwardExprBlocks spec liveAfter da | none => da
    backwardExprBlocks value liveAfter da
  | .JoinedStr _ ⟨_, values⟩ =>
    values.foldr (init := da) fun v acc => backwardExprBlocks v liveAfter acc
  | .TemplateStr _ ⟨_, values⟩ =>
    values.foldr (init := da) fun v acc => backwardExprBlocks v liveAfter acc
  | _ => da

/-- Backward expression blocks for a simple statement. -/
private partial def backwardStmtExprBlocks (s : stmt SourceRange)
    (liveAfter : Std.HashSet String) (da : DemandArr) : DemandArr :=
  match s with
  | .Assign _ _ value _ => backwardExprBlocks value liveAfter da
  | .AnnAssign _ _ _ ⟨_, value⟩ _ =>
    match value with | some v => backwardExprBlocks v liveAfter da | none => da
  | .AugAssign _ _ _ value => backwardExprBlocks value liveAfter da
  | .Expr _ value => backwardExprBlocks value liveAfter da
  | .Return _ ⟨_, value⟩ =>
    match value with | some v => backwardExprBlocks v liveAfter da | none => da
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    let da := match cause with | some e => backwardExprBlocks e liveAfter da | none => da
    match exc with | some e => backwardExprBlocks e liveAfter da | none => da
  | .Assert _ test ⟨_, msg⟩ =>
    let da := match msg with | some m => backwardExprBlocks m liveAfter da | none => da
    backwardExprBlocks test liveAfter da
  | .Delete _ ⟨_, targets⟩ =>
    targets.foldr (init := da) fun t acc => backwardExprBlocks t liveAfter acc
  | _ => da

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
          -- Expression blocks within this statement
          da := backwardStmtExprBlocks s live da
          -- Update liveness: remove defs, add uses
          live := addFreeVarsStmt (live \ defsStmt s) s
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
      let da := backwardExprBlocks test liveAfter da
      -- Push join, else, then demands (reverse allocation order)
      let da := pushDemand da liveAfter    -- joinBlock
      let da := pushDemand da elseLive     -- elseBlock
      let da := pushDemand da thenLive     -- thenBlock
      let liveBefore := addFreeVarsExpr (thenLive ∪ elseLive) test
      (liveBefore, da)

    | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      -- Phase 2 allocates: iterInitBlock(N), headerBlock(N+1), endBlock(N+2),
      -- then iter expr blocks, then body blocks, then orelse blocks.
      let targetDefs := (extractNames target).foldl (init := ({}:Std.HashSet String))
        fun acc n => acc.insert n
      let (elseLive, da) := backwardStmts orelse liveAfter da
      -- First pass: compute bodyLive to determine headerLive
      let (bodyLive, _) := backwardStmts body liveAfter #[]
      let headerLive := (bodyLive ∪ elseLive ∪ liveAfter) \ targetDefs
      -- Second pass: push body sub-block demands with headerLive as liveAfter
      -- (body flows back to header via back-edge)
      let (_, da) := backwardStmts body headerLive da
      let da := backwardExprBlocks iter liveAfter da
      -- Push endBlock, headerBlock, iterInitBlock (reverse order)
      let da := pushDemand da (elseLive ∪ liveAfter)  -- endBlock
      let da := pushDemand da headerLive               -- headerBlock
      let da := pushDemand da headerLive               -- iterInitBlock (same as header)
      let liveBefore := addFreeVarsExpr headerLive iter
      (liveBefore, da)

    | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      -- Phase 2 allocates: testBlock(N), bodyBlock(N+1), endBlock(N+2),
      -- then test expr blocks, then body blocks, then orelse blocks.
      let (elseLive, da) := backwardStmts orelse liveAfter da
      -- First pass: compute bodyLive to determine testLive
      let (bodyLive, _) := backwardStmts body liveAfter #[]
      let testLive := addFreeVarsExpr (bodyLive ∪ elseLive ∪ liveAfter) test
      -- Second pass: push body sub-block demands with testLive as liveAfter
      -- (body flows back to testBlock via back-edge)
      let (_, da) := backwardStmts body testLive da
      let da := backwardExprBlocks test liveAfter da
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
            | some te => da := backwardExprBlocks te liveAfter da
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
        let da := items.foldr (init := da) fun item acc =>
          match item with | .mk_withitem _ e _ => backwardExprBlocks e liveAfter acc
        let withDefs := items.foldl (init := ({}:Std.HashSet String)) fun acc item =>
          match item with
          | .mk_withitem _ _ ⟨_, optVar⟩ =>
            match optVar with
            | some varExpr => (extractNames varExpr).foldl (init := acc) fun a n => a.insert n
            | none => acc
        let itemFv := items.foldl (init := ({}:Std.HashSet String)) fun acc item =>
          match item with | .mk_withitem _ e _ => addFreeVarsExpr acc e
        -- Push normalExitBlock, reraiseBlock, excExitBlock, enterBlock (reverse order)
        let da := pushDemand da liveAfter              -- normalExitBlock
        let da := pushDemand da liveAfter              -- reraiseBlock
        let da := pushDemand da (bodyLive ∪ liveAfter) -- excExitBlock
        let da := pushDemand da (bodyLive \ withDefs)  -- enterBlock
        let liveBefore := itemFv ∪ (bodyLive \ withDefs) ∪ liveAfter
        (liveBefore, da)
      else
        (liveAfter, da)

    | _ => (liveAfter, da)

end Strata.Python.Blockify

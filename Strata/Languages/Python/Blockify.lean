/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.PythonDialect
public import Strata.DDM.Util.SourceRange

/-!
# Phase 1: Block Layout for PythonSSA

Decomposes Python statements into a `BlockTree` — a tree that preserves
statement nesting while pre-allocating all SSA block IDs. Phase 2 (SSA
Construction) does a depth-first traversal of this tree.

Each compound statement (if/for/while/try/with) becomes a tree constructor
carrying its AST fragments and pre-assigned block IDs. Simple statements
pass through in `stmts` nodes using `Subarray` for zero-copy slicing.

BoolOp/IfExp are NOT decomposed here — they stay in expressions for Phase 2.
Phase 1 counts how many blocks each expression needs and pre-allocates IDs.
-/

namespace Strata.Python.Blockify

open Strata.Python (stmt expr excepthandler withitem boolop arguments alias)

/-! ## Block Tree ID -/

/-- Block ID for the Phase 1 tree. Distinct from `SSA.BlockId` (Phase 2 output). -/
public abbrev BlockTreeId := Nat

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

/-- Returns true if the statement ends control flow in the current block.
    Phase 1 stops accumulating into the current `stmts` slice after one of
    these. Phase 2 emits an SSA terminator when it encounters one. -/
public def isTerminatorStmt (s : stmt SourceRange) : Bool :=
  match s with
  | .Return .. | .Raise .. | .Break .. | .Continue .. => true
  | _ => false

/-! ## Expression Block Counting -/

/-- Count the number of blocks that BoolOp and IfExp nodes will require
    during Phase 2 expression translation. Each BoolOp with n operands
    needs (n-1) intermediate blocks plus 1 join block = n blocks.
    Each IfExp needs 3 blocks (then, else, join).

    This is a lightweight traversal — just counting, no AST modification. -/
partial def countExprBlocks (e : expr SourceRange) : Nat :=
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

/-- Count expression blocks across a slice of simple statements. -/
def countSliceExprBlocks (stmts : Array (stmt SourceRange))
    (start stop : Nat) : Nat := Id.run do
  let mut count := 0
  for i in [start:stop] do
    if h : i < stmts.size then
      let s := stmts[i]
      count := count + match s with
        | .Assign _ _ value _ => countExprBlocks value
        | .AnnAssign _ _ _ ⟨_, value⟩ _ =>
          match value with | some v => countExprBlocks v | none => 0
        | .AugAssign _ _ _ value => countExprBlocks value
        | .Expr _ value => countExprBlocks value
        | .Return _ ⟨_, value⟩ =>
          match value with | some v => countExprBlocks v | none => 0
        | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
          (match exc with | some e => countExprBlocks e | none => 0) +
          (match cause with | some e => countExprBlocks e | none => 0)
        | .Assert _ test ⟨_, msg⟩ =>
          countExprBlocks test +
          (match msg with | some m => countExprBlocks m | none => 0)
        | .Delete _ ⟨_, targets⟩ =>
          targets.foldl (init := 0) fun acc t => acc + countExprBlocks t
        | _ => 0
  return count

/-! ## Block Tree -/

/-! ## Block Tree

`BlockTree` and `ExceptHandlerTree` are mutually inductive: `tryExcept`
references `ExceptHandlerTree`, which contains `Array BlockTree` for
handler bodies. -/

public section
mutual

/-- Tree structure produced by Phase 1. Preserves statement nesting while
    pre-allocating all block IDs. Phase 2 does a DFS traversal. -/
inductive BlockTree where
  /-- Consecutive simple statements (per `isSimpleStmt`). Phase 2 emits
      these into the current block, stopping at the first `isTerminatorStmt`.
      Zero-copy slice into the original AST array. -/
  | stmts (slice : Subarray (stmt SourceRange))
          (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)

  /-- If/elif/else. Allocates: thenBlock, elseBlock, joinBlock. -/
  | ifStmt (test : expr SourceRange)
           (body : Array BlockTree) (orelse : Array BlockTree)
           (thenBlock : BlockTreeId) (elseBlock : BlockTreeId)
           (joinBlock : BlockTreeId)
           (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)
           (sr : SourceRange)

  /-- For loop. Allocates: iterInitBlock, headerBlock, endBlock.
      `target` is the loop variable pattern (Name, Tuple, etc.).
      `iter` is the iterable expression. -/
  | forLoop (target : expr SourceRange) (iter : expr SourceRange)
            (body : Array BlockTree) (orelse : Array BlockTree)
            (iterInitBlock : BlockTreeId) (headerBlock : BlockTreeId)
            (endBlock : BlockTreeId)
            (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)
            (sr : SourceRange)

  /-- While loop. Allocates: testBlock, bodyBlock, endBlock. -/
  | whileLoop (test : expr SourceRange)
              (body : Array BlockTree) (orelse : Array BlockTree)
              (testBlock : BlockTreeId) (bodyBlock : BlockTreeId)
              (endBlock : BlockTreeId)
              (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)
              (sr : SourceRange)

  /-- Try/except/else/finally. Allocates: one block per handler + joinBlock
      + optional finallyBlock + optional reraiseBlock. The reraiseBlock is
      allocated when the last handler is typed (has a type filter), so that
      exceptions not matching any handler are re-raised. -/
  | tryExcept (body : Array BlockTree)
              (handlers : Array ExceptHandlerTree)
              (orelse : Array BlockTree) (finally_ : Array BlockTree)
              (joinBlock : BlockTreeId) (finallyBlock : Option BlockTreeId)
              (reraiseBlock : Option BlockTreeId)
              (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)
              (sr : SourceRange)

  /-- With statement. Allocates: enterBlock, excExitBlock, reraiseBlock, normalExitBlock.
      The excExitBlock calls `__exit__` and checks the return value.
      If truthy → normalExitBlock (suppress exception).
      If falsy → reraiseBlock (re-raise exception). -/
  | withStmt (ctxExpr : expr SourceRange) (asName : Option String)
             (body : Array BlockTree)
             (enterBlock : BlockTreeId) (excExitBlock : BlockTreeId)
             (reraiseBlock : BlockTreeId) (normalExitBlock : BlockTreeId)
             (exprBlockStart : BlockTreeId) (exprBlockCount : Nat)
             (sr : SourceRange)

/-- Exception handler in a try/except tree node.
    For typed handlers (`typeExpr` is `some`), `bodyBlockId` is a separate
    block for the handler body (after the isinstance dispatch check).
    For bare handlers, `bodyBlockId` is `none` — the body runs directly
    in the dispatch block. -/
public inductive ExceptHandlerTree where
  | mk (typeExpr : Option (expr SourceRange))
       (name : Option String)
       (body : Array BlockTree)
       (blockId : BlockTreeId)
       (bodyBlockId : Option BlockTreeId)
       (sr : SourceRange)

end
end -- section

instance : Inhabited BlockTree where
  default := .stmts (#[].toSubarray) 0 0

instance : Inhabited ExceptHandlerTree where
  default := .mk none none #[] 0 none SourceRange.none

/-! ### Repr instances for debugging -/

mutual
private partial def reprBlockTree : BlockTree → String
  | .stmts slice ebs ebc =>
    s!"stmts({slice.size} stmts, exprBlocks={ebs}+{ebc})"
  | .ifStmt _ body orelse thenB elseB joinB ebs ebc _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let elseStr := ", ".intercalate (orelse.toList.map reprBlockTree)
    s!"ifStmt(then=bb{thenB}, else=bb{elseB}, join=bb{joinB}, exprBlocks={ebs}+{ebc}, body=[{bodyStr}], orelse=[{elseStr}])"
  | .forLoop _ _ body orelse initB headerB endB ebs ebc _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let elseStr := ", ".intercalate (orelse.toList.map reprBlockTree)
    s!"forLoop(init=bb{initB}, header=bb{headerB}, end=bb{endB}, exprBlocks={ebs}+{ebc}, body=[{bodyStr}], orelse=[{elseStr}])"
  | .whileLoop _ body orelse testB bodyB endB ebs ebc _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let elseStr := ", ".intercalate (orelse.toList.map reprBlockTree)
    s!"whileLoop(test=bb{testB}, body=bb{bodyB}, end=bb{endB}, exprBlocks={ebs}+{ebc}, body=[{bodyStr}], orelse=[{elseStr}])"
  | .tryExcept body handlers orelse finally_ joinB finallyB reraiseB ebs ebc _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let hStr := ", ".intercalate (handlers.toList.map reprExceptHandler)
    let elseStr := ", ".intercalate (orelse.toList.map reprBlockTree)
    let finStr := ", ".intercalate (finally_.toList.map reprBlockTree)
    let fbStr := match finallyB with | some b => s!"bb{b}" | none => "none"
    let rbStr := match reraiseB with | some b => s!"bb{b}" | none => "none"
    s!"tryExcept(join=bb{joinB}, finally={fbStr}, reraise={rbStr}, exprBlocks={ebs}+{ebc}, body=[{bodyStr}], handlers=[{hStr}], orelse=[{elseStr}], finally_=[{finStr}])"
  | .withStmt _ asName body enterB excExitB reraiseB normalExitB ebs ebc _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let asStr := match asName with | some n => s!"\"{n}\"" | none => "none"
    s!"withStmt(as={asStr}, enter=bb{enterB}, excExit=bb{excExitB}, reraise=bb{reraiseB}, normalExit=bb{normalExitB}, exprBlocks={ebs}+{ebc}, body=[{bodyStr}])"

private partial def reprExceptHandler : ExceptHandlerTree → String
  | .mk _ name body blockId bodyBlockId _ =>
    let bodyStr := ", ".intercalate (body.toList.map reprBlockTree)
    let nameStr := match name with | some n => s!"\"{n}\"" | none => "none"
    let bbStr := match bodyBlockId with | some b => s!", bodyBb=bb{b}" | none => ""
    s!"handler(name={nameStr}, bb{blockId}{bbStr}, body=[{bodyStr}])"
end

instance : Repr BlockTree where
  reprPrec bt _ := reprBlockTree bt

instance : Repr ExceptHandlerTree where
  reprPrec eh _ := reprExceptHandler eh

instance : ToString BlockTree where
  toString := reprBlockTree

instance : ToString ExceptHandlerTree where
  toString := reprExceptHandler

/-- Result of blockifying a single function/method/module-init.
    Phase 2 consumes this to produce an SSA `Func`. -/
public structure BlockifyResult where
  /-- Function name (e.g., `"main"`, `"MyClass.__init__"`, `"@module_init"`). -/
  name        : String
  /-- Parameter names with optional type annotation expressions. -/
  params      : Array (String × Option (expr SourceRange))
  /-- The block tree — Phase 2 does DFS over this. -/
  body        : Array BlockTree
  /-- Every variable assigned anywhere in this function. Used by Phase 2
      for conservative block parameters at join points. -/
  allVars     : Std.HashSet String
  /-- Total block IDs allocated by Phase 1 (statement + expression blocks).
      Phase 2 can assert it produced exactly this many blocks. Not easily
      derived from `body` because expression blocks are pre-allocated ranges,
      not visible as tree nodes. -/
  totalBlocks : Nat
  /-- Warnings produced during blockification (dead code, unsupported constructs). -/
  warnings    : Array String
  /-- Source range of the function definition (`def`/`class` statement).
      Phase 2 uses this for `Func.sr`. For `@module_init`, this is `SourceRange.none`. -/
  sr          : SourceRange
  /-- Whether this function is async (unsupported — Phase 2 emits a warning). -/
  isAsync     : Bool := false
deriving Inhabited

/-! ## Blockify State and Monad -/

structure BlockifyState where
  nextBlockId : Nat := 0
  allVars     : Std.HashSet String := {}
  warnings    : Array String := #[]
deriving Inhabited

abbrev BlockifyM := StateM BlockifyState

private def freshBlockId : BlockifyM BlockTreeId := do
  let s ← get
  let id := s.nextBlockId
  set { s with nextBlockId := id + 1 }
  return id

private def allocBlockIds (n : Nat) : BlockifyM BlockTreeId := do
  if n == 0 then return 0  -- no allocation needed, return dummy
  let s ← get
  let start := s.nextBlockId
  set { s with nextBlockId := start + n }
  return start

private def defineVar (name : String) : BlockifyM Unit :=
  modify fun s => { s with allVars := s.allVars.insert name }

private def warn (msg : String) : BlockifyM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-- Extract variable names from an assignment target (handles Name, Tuple, List). -/
private def extractNames (e : expr SourceRange) : Array String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => #[name]
  | .Tuple _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | .List _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | _ => #[]

/-- Record all variable assignments in a simple statement. Does NOT recurse
    into sub-bodies (compound statements are handled by the tree). -/
private def collectStmtVars (s : stmt SourceRange) : BlockifyM Unit := do
  match s with
  | .Assign _ ⟨_, targets⟩ _ _ =>
    for t in targets do
      (extractNames t).forM defineVar
  | .AnnAssign _ target _ _ _ =>
    (extractNames target).forM defineVar
  | .AugAssign _ target _ _ =>
    (extractNames target).forM defineVar
  | .Import _ ⟨_, aliases⟩ =>
    for a in aliases do
      defineVar (a.asname.getD a.name)
  | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
    for a in aliases do
      defineVar (a.asname.getD a.name)
  | _ => pure ()

/-- Name of a terminator statement for diagnostic messages. -/
private def terminatorName (s : stmt SourceRange) : String :=
  match s with
  | .Return ..   => "return"
  | .Raise ..    => "raise"
  | .Break ..    => "break"
  | .Continue .. => "continue"
  | _            => "terminator"

/-! ## Core Blockify Algorithm -/

/-- Blockify a statement array into a BlockTree array. This is the core
    recursive descent: simple statements are grouped into `stmts` nodes,
    compound statements become tree constructors with pre-assigned block IDs. -/
partial def blockifyStmts (stmts : Array (stmt SourceRange))
    : BlockifyM (Array BlockTree) := do
  let mut result : Array BlockTree := #[]
  let mut sliceStart : Nat := 0
  let mut i : Nat := 0
  while h : i < stmts.size do
    let s := stmts[i]
    if isSimpleStmt s then
      -- Accumulate into current slice
      collectStmtVars s
      -- If this is a terminator, end the slice here
      if isTerminatorStmt s then
        let stop := i + 1
        let exprCount := countSliceExprBlocks stmts sliceStart stop
        let exprStart ← allocBlockIds exprCount
        result := result.push (.stmts (stmts.toSubarray sliceStart stop) exprStart exprCount)
        -- Warn about dead code after terminator
        if i + 1 < stmts.size then
          warn s!"Dead code after {terminatorName s} at index {i}"
        -- Everything after the terminator in this array is dead
        sliceStart := stmts.size
        i := stmts.size
        continue
      i := i + 1
      continue
    -- Compound statement: flush accumulated simple stmts first
    if sliceStart < i then
      let exprCount := countSliceExprBlocks stmts sliceStart i
      let exprStart ← allocBlockIds exprCount
      result := result.push (.stmts (stmts.toSubarray sliceStart i) exprStart exprCount)
    -- Now decompose the compound statement
    let node ← blockifyCompound s
    result := result.push node
    i := i + 1
    sliceStart := i
  -- Flush any trailing simple stmts
  if sliceStart < stmts.size then
    let exprCount := countSliceExprBlocks stmts sliceStart stmts.size
    let exprStart ← allocBlockIds exprCount
    result := result.push (.stmts (stmts.toSubarray sliceStart stmts.size) exprStart exprCount)
  return result
where
  /-- Decompose a single compound statement into a BlockTree node. -/
  blockifyCompound (s : stmt SourceRange) : BlockifyM BlockTree := do
    let sr := s.ann
    match s with
    | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      let thenBlock ← freshBlockId
      let elseBlock ← freshBlockId
      let joinBlock ← freshBlockId
      let exprCount := countExprBlocks test
      let exprStart ← allocBlockIds exprCount
      let bodyTree ← blockifyStmts body
      let orelseTree ← blockifyStmts orelse
      return .ifStmt test bodyTree orelseTree thenBlock elseBlock joinBlock
        exprStart exprCount sr

    | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      (extractNames target).forM defineVar
      let iterInitBlock ← freshBlockId
      let headerBlock ← freshBlockId
      let endBlock ← freshBlockId
      let exprCount := countExprBlocks iter
      let exprStart ← allocBlockIds exprCount
      let bodyTree ← blockifyStmts body
      let orelseTree ← blockifyStmts orelse
      return .forLoop target iter bodyTree orelseTree
        iterInitBlock headerBlock endBlock exprStart exprCount sr

    | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      let testBlock ← freshBlockId
      let bodyBlock ← freshBlockId
      let endBlock ← freshBlockId
      let exprCount := countExprBlocks test
      let exprStart ← allocBlockIds exprCount
      let bodyTree ← blockifyStmts body
      let orelseTree ← blockifyStmts orelse
      return .whileLoop test bodyTree orelseTree testBlock bodyBlock endBlock
        exprStart exprCount sr

    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
      let mut handlerTrees : Array ExceptHandlerTree := #[]
      let mut handlerExprCount : Nat := 0
      let mut lastHandlerIsTyped := false
      for h in handlers do
        match h with
        | .ExceptHandler handlerSr ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
          let hBlockId ← freshBlockId
          -- For typed handlers, allocate a separate body block for isinstance dispatch
          let hBodyBlockId ← match exType with
            | some _ => some <$> freshBlockId
            | none => pure none
          lastHandlerIsTyped := exType.isSome
          match errname.val with
          | some ⟨_, name⟩ => defineVar name
          | none => pure ()
          let handlerName := match errname.val with
            | some ⟨_, name⟩ => some name
            | none => none
          handlerExprCount := handlerExprCount +
            (match exType with | some e => countExprBlocks e | none => 0)
          let hBodyTree ← blockifyStmts hBody
          handlerTrees := handlerTrees.push (.mk exType handlerName hBodyTree hBlockId hBodyBlockId handlerSr)
      let joinBlock ← freshBlockId
      let finallyBlock ← if finalbody.isEmpty then pure none
        else some <$> freshBlockId
      -- Allocate reraise block if last handler is typed (unmatched exceptions re-raise)
      let reraiseBlock ← if lastHandlerIsTyped then some <$> freshBlockId else pure none
      let exprStart ← allocBlockIds handlerExprCount
      let bodyTree ← blockifyStmts body
      let orelseTree ← blockifyStmts orelse
      let finallyTree ← blockifyStmts finalbody
      return .tryExcept bodyTree handlerTrees orelseTree finallyTree
        joinBlock finallyBlock reraiseBlock exprStart handlerExprCount sr

    | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
      if h : items.size > 0 then
        let item := items[0]
        match item with
        | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
          match optVars with
          | some e => (extractNames e).forM defineVar
          | none => pure ()
          let asName := match optVars with
            | some (.Name _ ⟨_, name⟩ _) => some name
            | _ => none
          let enterBlock ← freshBlockId
          let excExitBlock ← freshBlockId
          let reraiseBlock ← freshBlockId
          let normalExitBlock ← freshBlockId
          let exprCount := countExprBlocks ctxExpr
          let exprStart ← allocBlockIds exprCount
          if items.size > 1 then
            warn "Multi-item with statement — only first item decomposed in v1"
          let innerBody ← blockifyStmts body
          return .withStmt ctxExpr asName innerBody
            enterBlock excExitBlock reraiseBlock normalExitBlock exprStart exprCount sr
      else
        warn "Empty with statement"
        return .stmts (#[].toSubarray) 0 0

    | _ =>
      -- Unsupported compound statement (AsyncFor, AsyncWith, TryStar, Match)
      let name := match s with
        | .AsyncFor .. => "AsyncFor" | .AsyncWith .. => "AsyncWith"
        | .TryStar .. => "TryStar" | .Match .. => "Match" | _ => "unknown"
      warn s!"Unsupported compound statement: {name}"
      return .stmts (#[].toSubarray) 0 0

/-! ## Function-Level Entry Points -/

/-- Extract parameter info from a Python arguments node. -/
private def extractParams (args : arguments SourceRange)
    : Array (String × Option (expr SourceRange)) := Id.run do
  match args with
  | .mk_arguments _ posonlyargs posargs vararg kwonlyargs _ kwarg _ =>
    let mut result : Array (String × Option (expr SourceRange)) := #[]
    for a in posonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ ⟨_, annot⟩ _ => result := result.push (name, annot)
    for a in posargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ ⟨_, annot⟩ _ => result := result.push (name, annot)
    match vararg.val with
    | some (.mk_arg _ ⟨_, name⟩ ⟨_, annot⟩ _) =>
      result := result.push (s!"*{name}", annot)
    | none => pure ()
    for a in kwonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ ⟨_, annot⟩ _ => result := result.push (name, annot)
    match kwarg.val with
    | some (.mk_arg _ ⟨_, name⟩ ⟨_, annot⟩ _) =>
      result := result.push (s!"**{name}", annot)
    | none => pure ()
    return result

/-- Strip `*` and `**` prefixes from a parameter name to get the variable name. -/
private def paramVarName (pname : String) : String :=
  if pname.startsWith "**" then pname.drop 2 |>.toString
  else if pname.startsWith "*" then pname.drop 1 |>.toString
  else pname

/-- Blockify a function body. -/
def blockifyFunc (name : String)
    (params : Array (String × Option (expr SourceRange)))
    (body : Array (stmt SourceRange))
    (sr : SourceRange)
    : BlockifyResult :=
  let action : BlockifyM (Array BlockTree) := do
    -- Define parameters as variables
    for (pname, _) in params do
      defineVar (paramVarName pname)
    blockifyStmts body
  -- Reserve bb0 for the entry block; compound statements allocate from bb1+
  let (bodyTree, finalState) := action.run { nextBlockId := 1 }
  { name, params, body := bodyTree,
    allVars := finalState.allVars,
    totalBlocks := finalState.nextBlockId,
    warnings := finalState.warnings,
    sr }

/-- Blockify a module: extracts functions and classes, handles module-level code. -/
public partial def blockifyModule
    (stmts : Array (stmt SourceRange))
    : Array BlockifyResult := Id.run do
  let mut results : Array BlockifyResult := #[]
  for s in stmts do
    match s with
    | .FunctionDef sr ⟨_, name⟩ args ⟨_, body⟩ _ _ _ _ =>
      let params := extractParams args
      results := results.push (blockifyFunc name params body sr)
    | .AsyncFunctionDef sr ⟨_, name⟩ args ⟨_, body⟩ _ _ _ _ =>
      let params := extractParams args
      results := results.push { blockifyFunc name params body sr with isAsync := true }
    | .ClassDef sr ⟨_, className⟩ _ _ ⟨_, classBody⟩ _ _ =>
      -- Each method becomes a top-level function with mangled name
      for cs in classBody do
        match cs with
        | .FunctionDef methodSr ⟨_, methodName⟩ args ⟨_, methodBody⟩ _ _ _ _ =>
          let params := extractParams args
          let mangledName := s!"{className}.{methodName}"
          results := results.push (blockifyFunc mangledName params methodBody methodSr)
        | _ => pure ()
      -- Class init block (class body minus methods)
      let initStmts := classBody.filter fun cs =>
        match cs with | .FunctionDef .. => false | _ => true
      if !initStmts.isEmpty then
        results := results.push (blockifyFunc s!"@{className}_init" #[] initStmts sr)
    | _ => pure ()
  -- Module-level code (everything that's not a function/class def)
  let moduleStmts := stmts.filter fun s =>
    match s with | .FunctionDef .. | .AsyncFunctionDef .. | .ClassDef .. => false | _ => true
  if !moduleStmts.isEmpty then
    results := results.push (blockifyFunc "@module_init" #[] moduleStmts SourceRange.none)
  return results

end Strata.Python.Blockify

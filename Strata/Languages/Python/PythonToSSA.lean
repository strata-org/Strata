/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Python.Blockify
public import Strata.Languages.Python.SSA
public import Strata.Languages.Python.PythonDialect

/-!
# Phase 2: SSA Construction

Depth-first traversal of the `BlockTree` produced by Phase 1 (Blockify).
Emits SSA instructions, manages the binding environment, and produces
`SSA.Func` / `SSA.Module` values.

## Architecture

- `SSAConfig` (read-only via ReaderT): prelude, module name
- `SSAState` (mutable via StateM): val IDs, names, blocks, current block, varEnv
- `SSAM` = `ReaderT SSAConfig (StateM SSAState)`

Statement-level block IDs come from the BlockTree. Expression-level block IDs
are consumed from pre-allocated ranges (via counter in SSAState).
-/

namespace Strata.Python.PythonToSSA

open Strata.Python (stmt expr constant operator unaryop boolop cmpop
                    keyword arguments alias excepthandler)
open Strata.Python.SSA
open Strata.Python.Blockify (BlockTree ExceptHandlerTree BlockifyResult BlockTreeId
                              blockifyModule)

/-! ## Binding Environment -/

/-- A binding is either a local SSA value or a qualified reference (import/prelude). -/
inductive Binding where
  | local     (val : SSAVal)
  | qualified (qn : QualifiedName)
deriving Inhabited

/-! ## Configuration and State -/

/-- Read-only configuration for SSA translation. -/
structure SSAConfig where
  prelude    : Std.HashMap String QualifiedName
  moduleName : String
deriving Inhabited

/-- Mutable state for SSA translation. -/
structure SSAState where
  /-- Next SSA value ID (monotonically increasing within a function). -/
  nextValId      : Nat := 0
  /-- Human-readable names for SSA values. `names[i]` is the name for `SSAVal.mk i`. -/
  names          : Array SSAName := #[]
  /-- Completed blocks. -/
  blocks         : Array Block := #[]
  /-- Instructions accumulated for the current block. -/
  currentInstrs  : Array NamedInstr := #[]
  /-- Current block's ID. -/
  currentBlockId : BlockId := ⟨0⟩
  /-- Current block's parameters. -/
  currentParams  : Array BlockParam := #[]
  /-- Current block's exception handler. -/
  currentExcept  : Option ExceptTarget := none
  /-- Variable name → current binding. -/
  varEnv         : Std.HashMap String Binding := {}
  /-- Per-variable suffix counter for SSAName generation. -/
  nameSuffixes   : Std.HashMap String Nat := {}
  /-- Next available expression block ID (set per compound node). -/
  nextExprBlock  : Nat := 0
  /-- One past the last allocated expression block ID (for assertion). -/
  exprBlockEnd   : Nat := 0
  /-- Accumulated errors. -/
  errors         : Array String := #[]
  /-- Accumulated warnings. -/
  warnings       : Array String := #[]
deriving Inhabited

/-- The SSA translation monad. -/
abbrev SSAM := ReaderT SSAConfig (StateM SSAState)

/-! ## Monad Helpers -/

/-- Allocate a fresh SSA value with a human-readable name. -/
def freshVal (base : String) (_sr : SourceRange) : SSAM SSAVal := do
  let s ← get
  let id := s.nextValId
  let suffix := s.nameSuffixes.getD base 0
  let name : SSAName := { base, suffix }
  set { s with
    nextValId := id + 1
    names := s.names.push name
    nameSuffixes := s.nameSuffixes.insert base (suffix + 1)
  }
  return ⟨id⟩

/-- Emit an instruction into the current block. Returns the result SSAVal. -/
def emitInstr (base : String) (type : Option PyType) (instr : Instruction)
    (sr : SourceRange) (exceptArgs : Option (Array ExceptArgVal) := none)
    : SSAM SSAVal := do
  let val ← freshVal base sr
  let ni : NamedInstr := {
    result := some val, type, instr, sr, exceptArgs
  }
  modify fun s => { s with currentInstrs := s.currentInstrs.push ni }
  return val

/-- Emit an instruction with no result value (e.g., setAttr, setItem). -/
def emitVoidInstr (instr : Instruction) (sr : SourceRange)
    (exceptArgs : Option (Array ExceptArgVal) := none) : SSAM Unit :=
  modify fun s => { s with currentInstrs := s.currentInstrs.push {
    result := none, type := none, instr, sr, exceptArgs
  }}

/-- Record an error and emit an `unsupported` instruction. -/
def ssaError (msg : String) (sr : SourceRange) : SSAM SSAVal := do
  modify fun s => { s with errors := s.errors.push msg }
  emitInstr "_err" none (.unsupported msg) sr

/-- Record a warning. -/
def ssaWarn (msg : String) : SSAM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-- Look up a variable in the binding environment. -/
def lookupVar (name : String) (sr : SourceRange) : SSAM SSAVal := do
  let s ← get
  match s.varEnv[name]? with
  | some (.local val) => return val
  | some (.qualified qn) => emitInstr name none (.qualifiedRef qn) sr
  | none =>
    -- Check the prelude
    let cfg ← read
    match cfg.prelude[name]? with
    | some qn => emitInstr name none (.qualifiedRef qn) sr
    | none => ssaError s!"Unresolved name: {name}" sr

/-- Bind a variable to an SSA value in the environment. -/
def bindVar (name : String) (val : SSAVal) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.local val) }

/-- Bind a variable to a qualified name (from import/prelude). -/
def bindQualified (name : String) (qn : QualifiedName) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.qualified qn) }

/-! ## Block Management -/

/-- Finalize the current block with a terminator and start a new block. -/
def finishBlock (term : Terminator) (termSr : SourceRange)
    (nextBlockId : BlockId) (nextParams : Array BlockParam)
    (nextExcept : Option ExceptTarget := none) : SSAM Unit := do
  let s ← get
  let block : Block := {
    id := s.currentBlockId
    params := s.currentParams
    instrs := s.currentInstrs
    term
    termSr
    except := s.currentExcept
  }
  set { s with
    blocks := s.blocks.push block
    currentInstrs := #[]
    currentBlockId := nextBlockId
    currentParams := nextParams
    currentExcept := nextExcept
  }

/-- Start the very first block of a function. -/
def startFirstBlock (blockId : BlockId) (params : Array BlockParam)
    (except : Option ExceptTarget := none) : SSAM Unit :=
  modify fun s => { s with
    currentBlockId := blockId
    currentParams := params
    currentExcept := except
  }

/-- Map a Phase 1 BlockTreeId to a Phase 2 BlockId.
    For now, use the same numbering (no renumbering). -/
def toBlockId (btId : Nat) : BlockId := ⟨btId⟩

/-! ## Expression Translation -/

/-- Set the expression block allocation range for a compound node. -/
def setExprBlockRange (exprBlockStart : Nat) (exprBlockCount : Nat)
    : SSAM Unit :=
  modify fun s => { s with
    nextExprBlock := exprBlockStart
    exprBlockEnd := exprBlockStart + exprBlockCount
  }

/-- Allocate an expression block ID from the pre-allocated range. -/
def allocExprBlock : SSAM BlockId := do
  let s ← get
  if s.nextExprBlock >= s.exprBlockEnd then
    ssaWarn "Expression block allocation overflow"
  let bid := s.nextExprBlock
  modify fun s => { s with nextExprBlock := s.nextExprBlock + 1 }
  return ⟨bid⟩

/-- Translate a Python expression to an SSA value. -/
partial def translateExpr (e : expr SourceRange) : SSAM SSAVal := do
  let sr := e.ann
  match e with
  | .Constant _ c _ => translateConstant c
  | .Name _ ⟨_, name⟩ _ => lookupVar name sr
  | .BinOp _ left op right =>
    let lv ← translateExpr left
    let rv ← translateExpr right
    let opKind := translateBinOp op
    emitInstr "_tmp" none (.binOp opKind lv rv) sr
  | .UnaryOp _ op operand =>
    let v ← translateExpr operand
    let opKind := translateUnaryOp op
    emitInstr "_tmp" none (.unaryOp opKind v) sr
  | .Compare _ left ⟨_, ops⟩ ⟨_, comparators⟩ =>
    let lv ← translateExpr left
    if ops.size == 1 && comparators.size == 1 then
      let rv ← translateExpr comparators[0]!
      let opKind := translateCmpOp ops[0]!
      emitInstr "_tmp" none (.compareOp opKind lv rv) sr
    else
      -- TODO: chained comparisons desugar to short-circuit and
      ssaError "Chained comparisons not yet implemented" sr
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    let fv ← translateExpr f
    let mut callArgs : Array CallArg := #[]
    for a in args do
      let av ← translateExpr a
      callArgs := callArgs.push (.positional av)
    for kw in kwargs do
      match kw with
      | .mk_keyword _ kwArg kwValue =>
        let kv ← translateExpr kwValue
        match kwArg.val with
        | some ⟨_, argName⟩ => callArgs := callArgs.push (.keyword argName kv)
        | none => callArgs := callArgs.push (.starKwargs kv)
    emitInstr "_tmp" none (.call fv callArgs) sr
  | .Attribute _ value ⟨_, attrName⟩ _ =>
    let objV ← translateExpr value
    emitInstr "_tmp" none (.attr objV attrName) sr
  | .Subscript _ value slice _ =>
    let objV ← translateExpr value
    match slice with
    | .Slice sliceSr ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, step⟩ =>
      let loV ← lo.mapM (translateExpr ·)
      let hiV ← hi.mapM (translateExpr ·)
      let stV ← step.mapM (translateExpr ·)
      emitInstr "_tmp" none (.getSlice objV loV hiV stV) sliceSr
    | _ =>
      let keyV ← translateExpr slice
      emitInstr "_tmp" none (.getItem objV keyV) sr
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    let mut ks : Array SSAVal := #[]
    let mut vs : Array SSAVal := #[]
    for k in keys do
      match k with
      | .some_expr _ ke =>
        let kv ← translateExpr ke
        ks := ks.push kv
      | _ => pure ()  -- TODO: dict unpacking
    for v in values do
      let vv ← translateExpr v
      vs := vs.push vv
    emitInstr "_tmp" none (.mkDict ks vs) sr
  | .List _ ⟨_, elts⟩ _ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let v ← translateExpr e
      vals := vals.push v
    emitInstr "_tmp" none (.mkList vals) sr
  | .Tuple _ ⟨_, elts⟩ _ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let v ← translateExpr e
      vals := vals.push v
    emitInstr "_tmp" none (.mkTuple vals) sr
  | .Set _ ⟨_, elts⟩ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let v ← translateExpr e
      vals := vals.push v
    ssaError "set literal not in SSA IR" sr
  | .JoinedStr _ ⟨_, values⟩ =>
    let mut parts : Array SSAVal := #[]
    for v in values do
      match v with
      | .FormattedValue fvSr fvValue _ _ =>
        let val ← translateExpr fvValue
        let fmted ← emitInstr "_tmp" none (.fmtValue val) fvSr
        parts := parts.push fmted
      | .Interpolation intSr intValue _ _ _ =>
        let val ← translateExpr intValue
        let fmted ← emitInstr "_tmp" none (.fmtValue val) intSr
        parts := parts.push fmted
      | .Constant _ (.ConString _ ⟨_, s⟩) _ =>
        let sv ← emitInstr "_tmp" none (.strLit s) v.ann
        parts := parts.push sv
      | _ =>
        let val ← translateExpr v
        parts := parts.push val
    emitInstr "_tmp" none (.strConcat parts) sr
  | .TemplateStr _ ⟨_, values⟩ =>
    let mut parts : Array SSAVal := #[]
    for v in values do
      let val ← translateExpr v
      parts := parts.push val
    emitInstr "_tmp" none (.strConcat parts) sr
  | .FormattedValue _ value _ _ =>
    let val ← translateExpr value
    emitInstr "_tmp" none (.fmtValue val) sr
  | .Interpolation _ value _ _ _ =>
    let val ← translateExpr value
    emitInstr "_tmp" none (.fmtValue val) sr
  | .Starred _ value _ =>
    translateExpr value
  | .BoolOp _ op ⟨_, values⟩ =>
    translateBoolOp op values sr
  | .IfExp _ test body orelse =>
    translateIfExp test body orelse sr
  | _ =>
    ssaError s!"Unsupported expression" sr
where
  translateConstant (c : constant SourceRange) : SSAM SSAVal := do
    let sr := c.ann
    match c with
    | .ConPos _ ⟨_, n⟩ => emitInstr "_tmp" none (.intLit n) sr
    | .ConNeg _ ⟨_, n⟩ => emitInstr "_tmp" none (.intLit (-(n : Int))) sr
    | .ConString _ ⟨_, s⟩ => emitInstr "_tmp" none (.strLit s) sr
    | .ConFloat _ ⟨_, s⟩ => emitInstr "_tmp" none (.floatLit s) sr
    | .ConTrue _ => emitInstr "_tmp" none (.boolLit true) sr
    | .ConFalse _ => emitInstr "_tmp" none (.boolLit false) sr
    | .ConNone _ => emitInstr "_tmp" none .noneLit sr
    | .ConBytes _ ⟨_, b⟩ => emitInstr "_tmp" none (.bytesLit (String.fromUTF8! b)) sr
    | .ConEllipsis .. => ssaError "Ellipsis not supported" sr
    | .ConComplex .. => ssaError "Complex literals not supported" sr

  translateBinOp (op : operator SourceRange) : BinOpKind :=
    match op with
    | .Add .. => .add | .Sub .. => .sub | .Mult .. => .mult | .Div .. => .div
    | .FloorDiv .. => .floorDiv | .Mod .. => .mod | .Pow .. => .pow
    | _ => .add  -- unsupported ops (bitwise etc.) — will emit error elsewhere

  translateUnaryOp (op : unaryop SourceRange) : UnaryOpKind :=
    match op with
    | .Not .. => .not_ | .USub .. => .uSub
    | _ => .not_  -- unsupported (Invert, UAdd)

  translateCmpOp (op : cmpop SourceRange) : CmpOpKind :=
    match op with
    | .Eq .. => .eq | .NotEq .. => .notEq | .Lt .. => .lt | .LtE .. => .ltE
    | .Gt .. => .gt | .GtE .. => .gtE | .Is .. => .is_ | .IsNot .. => .isNot
    | .In .. => .in_ | .NotIn .. => .notIn

  /-- Short-circuit BoolOp: `a and b` / `a or b` → condBranch chain. -/
  translateBoolOp (op : boolop SourceRange) (values : Array (expr SourceRange))
      (sr : SourceRange) : SSAM SSAVal := do
    if values.size < 2 then
      if h : values.size > 0 then translateExpr values[0]
      else ssaError "Empty BoolOp" sr
    else
      -- TODO: proper condBranch + join with block params
      -- For now, just evaluate all operands and return the last
      let mut result ← translateExpr values[0]!
      for i in [1:values.size] do
        if h : i < values.size then
          let _nextBlock ← allocExprBlock
          let _joinBlock ← allocExprBlock
          let nextVal ← translateExpr values[i]
          result := nextVal
      return result

  /-- Ternary IfExp: `body if test else orelse` → condBranch. -/
  translateIfExp (test body orelse : expr SourceRange)
      (sr : SourceRange) : SSAM SSAVal := do
    -- TODO: proper condBranch + join with block params
    let _ ← translateExpr test
    let _ ← translateExpr body
    let result ← translateExpr orelse
    return result

/-! ## Statement Translation -/

/-- Context passed down during body translation. -/
structure BodyCtx where
  /-- All variables in scope (for conservative block params at joins). -/
  allVars : Array String
  /-- Loop continue target (header block), if inside a loop. -/
  continueTarget : Option BlockId := none
  /-- Loop break target (end block), if inside a loop. -/
  breakTarget : Option BlockId := none
  /-- Active exception handler block, if inside a try. -/
  handlerTarget : Option BlockId := none

/-- Build block arguments for a branch to a join/loop block.
    Looks up each var in allVars in the current varEnv. -/
def buildBranchArgs (allVars : Array String) (sr : SourceRange)
    : SSAM (Array SSAVal) := do
  let mut args : Array SSAVal := #[]
  let s ← get
  for v in allVars do
    match s.varEnv[v]? with
    | some (.local val) => args := args.push val
    | _ =>
      -- Variable not assigned on this path → emit undef
      let uv ← emitInstr v none (.undef v) sr
      args := args.push uv
  return args

/-- Build block parameters from allVars for a join/loop block. -/
def buildBlockParams (allVars : Array String) (sr : SourceRange)
    : SSAM (Array BlockParam) := do
  let mut params : Array BlockParam := #[]
  for v in allVars do
    let val ← freshVal v sr
    params := params.push { val, type := none, sr }
    bindVar v val
  return params

/-- Translate a simple statement. Returns true if a terminator was emitted. -/
partial def translateSimpleStmt (s : stmt SourceRange) (bodyCtx : BodyCtx)
    : SSAM Bool := do
  let sr := s.ann
  match s with
  | .Assign _ ⟨_, targets⟩ value _ =>
    let val ← translateExpr value
    for t in targets do
      assignToTarget t val
    return false

  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    match value with
    | some v =>
      let val ← translateExpr v
      assignToTarget target val
    | none => pure ()  -- annotation-only, no assignment
    return false

  | .AugAssign _ target op value =>
    let targetVal ← translateExpr target
    let rhsVal ← translateExpr value
    let opKind := match op with
      | .Add .. => BinOpKind.add | .Sub .. => .sub | .Mult .. => .mult
      | .Div .. => .div | .FloorDiv .. => .floorDiv | .Mod .. => .mod
      | .Pow .. => .pow | _ => .add
    let result ← emitInstr "_tmp" none (.binOp opKind targetVal rhsVal) sr
    assignToTarget target result
    return false

  | .Expr _ value =>
    let _ ← translateExpr value
    return false

  | .Return _ ⟨_, value⟩ =>
    let retVal ← match value with
      | some v => some <$> translateExpr v
      | none => pure none
    finishBlockWithTerm (.ret retVal) sr
    return true

  | .Raise _ ⟨_, exc⟩ _ =>
    match exc with
    | some e =>
      let excVal ← translateExpr e
      finishBlockWithTerm (.raise excVal) sr
    | none =>
      let _ ← ssaError "bare raise not yet supported" sr
      finishBlockWithTerm .unreachable sr
    return true

  | .Break .. =>
    match bodyCtx.breakTarget with
    | some target =>
      let args ← buildBranchArgs bodyCtx.allVars sr
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError "break outside loop" sr
      finishBlockWithTerm .unreachable sr
    return true

  | .Continue .. =>
    match bodyCtx.continueTarget with
    | some target =>
      let args ← buildBranchArgs bodyCtx.allVars sr
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError "continue outside loop" sr
      finishBlockWithTerm .unreachable sr
    return true

  | .Assert _ test ⟨_, msg⟩ =>
    let testVal ← translateExpr test
    let msgVal ← match msg with
      | some m => some <$> translateExpr m
      | none => pure none
    let _ ← emitInstr "_tmp" none (.assert_ testVal msgVal) sr
    return false

  | .Pass .. => return false

  | .Import _ ⟨_, aliases⟩ =>
    for a in aliases do
      let modName := a.name
      let localName := a.asname.getD modName
      let qn := QualifiedName.mk' modName modName
      bindQualified localName qn
    return false

  | .ImportFrom _ ⟨_, modOpt⟩ ⟨_, aliases⟩ _ =>
    let modName := match modOpt with
      | some ⟨_, m⟩ => m
      | none => "unknown"
    for a in aliases do
      let qn := QualifiedName.mk' modName a.name
      let localName := a.asname.getD a.name
      bindQualified localName qn
    return false

  | .Delete .. =>
    ssaWarn "delete statement ignored"
    return false

  | .Global .. | .Nonlocal .. =>
    return false

  | .FunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ =>
    let cfg ← read
    let qn := QualifiedName.mk' cfg.moduleName name
    bindQualified name qn
    return false

  | .ClassDef _ ⟨_, name⟩ _ _ _ _ _ =>
    let cfg ← read
    let qn := QualifiedName.mk' cfg.moduleName name
    bindQualified name qn
    return false

  | _ =>
    let _ ← ssaError "Unsupported statement" sr
    return false
where
  /-- Assign a value to a target expression (Name, Tuple, etc.). -/
  assignToTarget (target : expr SourceRange) (val : SSAVal) : SSAM Unit := do
    match target with
    | .Name _ ⟨_, name⟩ _ => bindVar name val
    | .Tuple _ ⟨_, elts⟩ _ =>
      for i in [:elts.size] do
        if h : i < elts.size then
          let idx ← emitInstr "_tmp" none (.intLit i) target.ann
          let elem ← emitInstr "_tmp" none (.getItem val idx) target.ann
          assignToTarget elts[i] elem
    | .List _ ⟨_, elts⟩ _ =>
      for i in [:elts.size] do
        if h : i < elts.size then
          let idx ← emitInstr "_tmp" none (.intLit i) target.ann
          let elem ← emitInstr "_tmp" none (.getItem val idx) target.ann
          assignToTarget elts[i] elem
    | .Attribute _ obj ⟨_, attrName⟩ _ =>
      let objV ← translateExpr obj
      emitVoidInstr (.setAttr objV attrName val) target.ann
    | .Subscript _ obj key _ =>
      let objV ← translateExpr obj
      let keyV ← translateExpr key
      emitVoidInstr (.setItem objV keyV val) target.ann
    | _ => ssaWarn s!"Unsupported assignment target"

  /-- Finalize the current block with a terminator (no next block). -/
  finishBlockWithTerm (term : Terminator) (termSr : SourceRange) : SSAM Unit := do
    let s ← get
    let block : Block := {
      id := s.currentBlockId
      params := s.currentParams
      instrs := s.currentInstrs
      term, termSr
      except := s.currentExcept
    }
    set { s with
      blocks := s.blocks.push block
      currentInstrs := #[]
    }

/-! ## BlockTree DFS Traversal -/

/-- Translate an Array BlockTree (the body of a function or compound stmt). -/
partial def translateBody (nodes : Array BlockTree) (bodyCtx : BodyCtx)
    : SSAM Unit := do
  for node in nodes do
    match node with
    | .stmts slice exprBlockStart exprBlockCount =>
      setExprBlockRange exprBlockStart exprBlockCount
      for s in slice do
        let isTerminator ← translateSimpleStmt s bodyCtx
        if isTerminator then break

    | .ifStmt test body orelse thenBlock elseBlock joinBlock
        exprBlockStart exprBlockCount sr =>
      setExprBlockRange exprBlockStart exprBlockCount
      let condVal ← translateExpr test
      -- Save varEnv before branching
      let preIfEnv := (← get).varEnv
      -- Branch to then/else
      let thenArgs ← buildBranchArgs bodyCtx.allVars sr
      let elseArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.condBranch condVal (toBlockId thenBlock) thenArgs
                              (toBlockId elseBlock) elseArgs) sr
        (toBlockId thenBlock) #[]
      -- Then block
      let thenParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := thenParams }
      translateBody body bodyCtx
      -- Branch to join (if not already terminated)
      let _thenEndEnv := (← get).varEnv
      let joinArgsFromThen ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId joinBlock) joinArgsFromThen) sr
        (toBlockId elseBlock) #[]
      -- Else block: restore pre-if env
      modify fun s => { s with varEnv := preIfEnv }
      let elseParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := elseParams }
      translateBody orelse bodyCtx
      let joinArgsFromElse ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId joinBlock) joinArgsFromElse) sr
        (toBlockId joinBlock) #[]
      -- Join block
      let joinParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := joinParams }

    | .forLoop target iter body orelse iterInitBlock headerBlock endBlock
        exprBlockStart exprBlockCount sr =>
      setExprBlockRange exprBlockStart exprBlockCount
      -- Evaluate iterable
      let iterVal ← translateExpr iter
      -- Branch to iterInit
      let initArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId iterInitBlock) initArgs) sr
        (toBlockId iterInitBlock) #[]
      -- IterInit block: call builtins.iter
      let initParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := initParams }
      let iterRef ← emitInstr "_iter" none
        (.qualifiedRef (QualifiedName.mk' "builtins" "iter")) sr
      let iterObj ← emitInstr "_iter" none
        (.call iterRef #[.positional iterVal]) sr
      bindVar "_iter" iterObj
      let headerArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId headerBlock) headerArgs) sr
        (toBlockId headerBlock) #[]
      -- Header block: call builtins.next, unpack target
      let headerParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => {s with
        currentParams := headerParams
        currentExcept := some { target := toBlockId endBlock }
      }
      let nextRef ← emitInstr "_tmp" none
        (.qualifiedRef (QualifiedName.mk' "builtins" "next")) sr
      let iterVar ← lookupVar "_iter" sr
      let nextVal ← emitInstr "_tmp" none (.call nextRef #[.positional iterVar]) sr
      -- Assign loop variable
      assignTarget target nextVal
      -- Translate body with loop context
      let loopCtx := { bodyCtx with
        continueTarget := some (toBlockId headerBlock)
        breakTarget := some (toBlockId endBlock)
      }
      translateBody body loopCtx
      -- Back edge to header
      let backArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId headerBlock) backArgs) sr
        (toBlockId endBlock) #[]
      -- End block (StopIteration caught)
      modify fun s => { s with currentExcept := none }
      let endParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := endParams }
      -- Handle orelse (for..else)
      translateBody orelse bodyCtx

    | .whileLoop test body orelse testBlock endBlock
        exprBlockStart exprBlockCount sr =>
      -- Branch to test block
      let testArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId testBlock) testArgs) sr
        (toBlockId testBlock) #[]
      -- Test block
      let testParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := testParams }
      setExprBlockRange exprBlockStart exprBlockCount
      let condVal ← translateExpr test
      -- TODO: proper ID allocation — while body needs a block ID from Phase 1
      let bodyBlockId : BlockId := ⟨testBlock + 1000⟩
      let thenArgs ← buildBranchArgs bodyCtx.allVars sr
      let elseArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.condBranch condVal bodyBlockId thenArgs
                              (toBlockId endBlock) elseArgs) sr
        bodyBlockId #[]
      let bodyParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := bodyParams }
      let loopCtx := { bodyCtx with
        continueTarget := some (toBlockId testBlock)
        breakTarget := some (toBlockId endBlock)
      }
      translateBody body loopCtx
      -- Back edge to test
      let backArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId testBlock) backArgs) sr
        (toBlockId endBlock) #[]
      -- End block
      let endParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := endParams }
      translateBody orelse bodyCtx

    | .tryExcept body _handlers _orelse _finally_ joinBlock _finallyBlock
        _exprBlockStart _exprBlockCount sr =>
      -- TODO: full try/except implementation
      ssaWarn "try/except not fully implemented yet"
      translateBody body bodyCtx
      -- Skip to join
      let joinArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId joinBlock) joinArgs) sr
        (toBlockId joinBlock) #[]
      let joinParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := joinParams }

    | .withStmt ctxExpr _asName body _enterBlock _excExitBlock _normalExitBlock
        exprBlockStart exprBlockCount sr =>
      -- TODO: full with statement implementation
      ssaWarn "with statement not fully implemented yet"
      setExprBlockRange exprBlockStart exprBlockCount
      let _ ← translateExpr ctxExpr
      translateBody body bodyCtx
where
  /-- Assign to a target expression from a value. -/
  assignTarget (target : expr SourceRange) (val : SSAVal) : SSAM Unit := do
    match target with
    | .Name _ ⟨_, name⟩ _ => bindVar name val
    | .Tuple _ ⟨_, elts⟩ _ =>
      for i in [:elts.size] do
        if h : i < elts.size then
          let idx ← emitInstr "_tmp" none (.intLit i) target.ann
          let elem ← emitInstr "_tmp" none (.getItem val idx) target.ann
          assignTarget elts[i] elem
    | _ => ssaWarn "Unsupported loop target pattern"

/-! ## Top-Level Translation -/

/-- Translate a BlockifyResult into an SSA Func. -/
def translateFunc (result : BlockifyResult) (config : SSAConfig) : Func :=
  let initState : SSAState := {}
  let action : SSAM Unit := do
    -- Create entry block params for function parameters
    let mut funcParams : Array FuncParam := #[]
    for (pname, _typeAnnot) in result.params do
      let varName := if pname.startsWith "**" then (pname.drop 2).toString
        else if pname.startsWith "*" then (pname.drop 1).toString
        else pname
      let val ← freshVal varName SourceRange.none
      let kind := if pname.startsWith "**" then ParamKind.varKeyword
        else if pname.startsWith "*" then ParamKind.varPositional
        else ParamKind.positional
      funcParams := funcParams.push {
        val, name := varName, type := none, default := none, kind
      }
      bindVar varName val
    -- Start the first block (entry block = bb0)
    startFirstBlock ⟨0⟩ #[]
    -- Translate the body
    let allVarsArray := result.allVars.toArray
    let bodyCtx : BodyCtx := { allVars := allVarsArray }
    translateBody result.body bodyCtx
    -- Finalize the last block if not already terminated
    let s ← get
    if !s.currentInstrs.isEmpty || s.blocks.isEmpty then
      let block : Block := {
        id := s.currentBlockId
        params := s.currentParams
        instrs := s.currentInstrs
        term := .ret none
        termSr := SourceRange.none
        except := s.currentExcept
      }
      set { s with blocks := s.blocks.push block, currentInstrs := #[] }
  let ((), finalState) := action config |>.run initState
  {
    name := result.name
    params := #[]  -- TODO: populate from funcParams
    retType := none
    blocks := finalState.blocks
    names := finalState.names
    decorators := #[]
    sr := result.sr
  }

/-- Translate a module's statements into an SSA Module. -/
public def translateModule (moduleName : String)
    (stmts : Array (stmt SourceRange)) : Module :=
  let config : SSAConfig := {
    prelude := pythonPrelude
    moduleName
  }
  let results := blockifyModule stmts
  let funcs := results.map (translateFunc · config)
  { name := moduleName, funcs }

end Strata.Python.PythonToSSA

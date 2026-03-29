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
  /-- Accumulated errors (message, source range). -/
  errors         : Array (String × SourceRange) := #[]
  /-- Accumulated warnings (message, source range). -/
  warnings       : Array (String × SourceRange) := #[]
  /-- Function parameters (populated during translation). -/
  funcParams     : Array FuncParam := #[]
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
def ssaError (sr : SourceRange) (msg : String) : SSAM SSAVal := do
  modify fun s => { s with errors := s.errors.push (msg, sr) }
  emitInstr "_err" none (.unsupported msg) sr

/-- Record a warning with source location. -/
def ssaWarn (sr : SourceRange) (msg : String) : SSAM Unit :=
  modify fun s => { s with warnings := s.warnings.push (msg, sr) }

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
    | none => ssaError sr s!"Unresolved name: {name}"

/-- Bind a variable to an SSA value in the environment. -/
def bindVar (name : String) (val : SSAVal) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.local val) }

/-- Bind a variable to a qualified name (from import/prelude). -/
def bindQualified (name : String) (qn : QualifiedName) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.qualified qn) }

/-- Rename an SSA value's human-readable name. Updates the suffix counter
    so subsequent values with this name get correct suffixes. -/
def renameVal (val : SSAVal) (newBase : String) : SSAM Unit :=
  modify fun s =>
    let suffix := s.nameSuffixes.getD newBase 0
    if h : val.id < s.names.size then
      { s with
        names := s.names.set val.id { base := newBase, suffix }
        nameSuffixes := s.nameSuffixes.insert newBase (suffix + 1) }
    else s

/-- Set the type annotation on the last instruction in the current block
    that defines the given SSA value. -/
def setValType (val : SSAVal) (type : PyType) : SSAM Unit :=
  modify fun s =>
    -- The defining instruction is typically the last one emitted
    let instrs := s.currentInstrs.map fun ni =>
      if ni.result == some val && ni.type.isNone then
        { ni with type := some type }
      else ni
    { s with currentInstrs := instrs }

/-- Parse a Python type annotation expression into an SSA PyType. -/
def parseTypeAnnotation (e : expr SourceRange) : Option PyType :=
  match e with
  | .Name _ ⟨_, "int"⟩ _ => some .int
  | .Name _ ⟨_, "str"⟩ _ => some .str
  | .Name _ ⟨_, "bool"⟩ _ => some .bool
  | .Name _ ⟨_, "float"⟩ _ => some .float
  | .Name _ ⟨_, "bytes"⟩ _ => some .bytes
  | .Name _ ⟨_, "None"⟩ _ => some .none
  | .Name _ ⟨_, "Any"⟩ _ => some .any
  | .Name _ ⟨_, "object"⟩ _ => some .object
  | .Name _ ⟨_, name⟩ _ => some (.named name)
  | .Constant _ (.ConNone _) _ => some .none
  | _ => none  -- TODO: generic types (list[X], dict[K,V], Optional[X], etc.)

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

/-- Set up a new current block without finalizing the previous one.
    Used when the previous block was already finalized by a terminator. -/
def startNewBlock (blockId : BlockId) (params : Array BlockParam)
    (except : Option ExceptTarget := none) : SSAM Unit :=
  modify fun s => { s with
    currentBlockId := blockId
    currentParams := params
    currentInstrs := #[]
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
    ssaWarn SourceRange.none "Expression block allocation overflow"
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
      -- Chained comparison: a < b < c → (a < b) and (b < c) with short-circuit.
      -- Each intermediate value is evaluated once.
      translateChainedCmp lv ops comparators sr
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    let fv ← translateExpr f
    let mut callArgs : Array CallArg := #[]
    -- Starred expressions at call sites become starArgs (e.g., f(*xs))
    for a in args do
      match a with
      | .Starred _ value _ =>
        let av ← translateExpr value
        callArgs := callArgs.push (.starArgs av)
      | _ =>
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
    ssaError sr "set literal not in SSA IR"
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
  -- Unsupported expressions: emit warning + unsupported instruction
  | .ListComp .. =>
    ssaWarn sr "unsupported ListComp"
    emitInstr "_tmp" none (.unsupported "ListComp") sr
  | .DictComp .. =>
    ssaWarn sr "unsupported DictComp"
    emitInstr "_tmp" none (.unsupported "DictComp") sr
  | .SetComp .. =>
    ssaWarn sr "unsupported SetComp"
    emitInstr "_tmp" none (.unsupported "SetComp") sr
  | .GeneratorExp .. =>
    ssaWarn sr "unsupported GeneratorExp"
    emitInstr "_tmp" none (.unsupported "GeneratorExp") sr
  | .Lambda .. =>
    ssaWarn sr "unsupported Lambda"
    emitInstr "_tmp" none (.unsupported "Lambda") sr
  | .NamedExpr .. =>
    ssaWarn sr "unsupported NamedExpr"
    emitInstr "_tmp" none (.unsupported "NamedExpr") sr
  | .Yield .. =>
    ssaWarn sr "unsupported Yield"
    emitInstr "_tmp" none (.unsupported "Yield") sr
  | .YieldFrom .. =>
    ssaWarn sr "unsupported YieldFrom"
    emitInstr "_tmp" none (.unsupported "YieldFrom") sr
  | .Await .. =>
    ssaWarn sr "unsupported Await"
    emitInstr "_tmp" none (.unsupported "Await") sr
  | _ =>
    ssaError sr "Unsupported expression"
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
    | .ConEllipsis .. => ssaError sr "Ellipsis not supported"
    | .ConComplex .. => ssaError sr "Complex literals not supported"

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

  /-- Chained comparison: `a < b < c` → (a < b) and (b < c) with short-circuit.
      Allocates n blocks for n comparators (n-1 eval + 1 join). -/
  translateChainedCmp (leftVal : SSAVal)
      (ops : Array (cmpop SourceRange))
      (comparators : Array (expr SourceRange))
      (sr : SourceRange) : SSAM SSAVal := do
    -- Allocate blocks: one per comparator (n-1 continue + 1 join)
    let n := comparators.size
    let mut blockIds : Array BlockId := #[]
    for _ in [:n] do
      let bid ← allocExprBlock
      blockIds := blockIds.push bid
    let joinBlockId := blockIds.back!
    -- First comparison
    let mut prevRight ← translateExpr comparators[0]!
    let mut cmpResult ← emitInstr "_tmp" none
      (.compareOp (translateCmpOp ops[0]!) leftVal prevRight) sr
    -- For each subsequent comparison, condBranch + eval
    for i in [1:n] do
      if h : i < n then
        let evalBlockId := blockIds[i - 1]!
        -- If false, short-circuit to join; if true, continue
        finishBlock (.condBranch cmpResult evalBlockId #[] joinBlockId #[cmpResult]) sr
          evalBlockId #[]
        let nextRight ← translateExpr comparators[i]
        cmpResult ← emitInstr "_tmp" none
          (.compareOp (translateCmpOp ops[i]!) prevRight nextRight) sr
        prevRight := nextRight
    -- After last comparison, branch to join
    let resultVal ← freshVal "_tmp" sr
    let joinParam : BlockParam := { val := resultVal, type := none, sr }
    finishBlock (.branch joinBlockId #[cmpResult]) sr joinBlockId #[joinParam]
    return resultVal

  /-- Short-circuit BoolOp: `a and b` / `a or b` → condBranch chain.
      For `and`: short-circuits to join with current value on false.
      For `or`: short-circuits to join with current value on true. -/
  translateBoolOp (op : boolop SourceRange) (values : Array (expr SourceRange))
      (sr : SourceRange) : SSAM SSAVal := do
    if values.size < 2 then
      if h : values.size > 0 then translateExpr values[0]
      else ssaError sr "Empty BoolOp"
    else
      -- Allocate n blocks: n-1 eval blocks + 1 join
      let mut blockIds : Array BlockId := #[]
      for _ in [:values.size] do
        let bid ← allocExprBlock
        blockIds := blockIds.push bid
      let joinBlockId := blockIds.back!
      -- Evaluate first operand in current block
      let mut lastVal ← translateExpr values[0]!
      -- For each subsequent operand: condBranch + eval
      for i in [1:values.size] do
        if h : i < values.size then
          let evalBlockId := blockIds[i - 1]!
          match op with
          | .And _ =>
            -- and: true → continue evaluating, false → short-circuit to join
            finishBlock (.condBranch lastVal evalBlockId #[] joinBlockId #[lastVal]) sr
              evalBlockId #[]
          | .Or _ =>
            -- or: true → short-circuit to join, false → continue evaluating
            finishBlock (.condBranch lastVal joinBlockId #[lastVal] evalBlockId #[]) sr
              evalBlockId #[]
          lastVal ← translateExpr values[i]
      -- After last operand, branch to join
      let resultVal ← freshVal "_tmp" sr
      let joinParam : BlockParam := { val := resultVal, type := none, sr }
      finishBlock (.branch joinBlockId #[lastVal]) sr joinBlockId #[joinParam]
      return resultVal

  /-- Ternary IfExp: `body if test else orelse` → condBranch + join. -/
  translateIfExp (test body orelse : expr SourceRange)
      (sr : SourceRange) : SSAM SSAVal := do
    let condVal ← translateExpr test
    let thenBlockId ← allocExprBlock
    let elseBlockId ← allocExprBlock
    let joinBlockId ← allocExprBlock
    -- condBranch to then/else (no block params for expr-level blocks)
    finishBlock (.condBranch condVal thenBlockId #[] elseBlockId #[]) sr
      thenBlockId #[]
    -- Then block: evaluate body, branch to join
    let bodyVal ← translateExpr body
    finishBlock (.branch joinBlockId #[bodyVal]) sr
      elseBlockId #[]
    -- Else block: evaluate orelse, branch to join
    let orelseVal ← translateExpr orelse
    let resultVal ← freshVal "_tmp" sr
    let joinParam : BlockParam := { val := resultVal, type := none, sr }
    finishBlock (.branch joinBlockId #[orelseVal]) sr joinBlockId #[joinParam]
    return resultVal

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
  for v in allVars do
    let s ← get
    match s.varEnv[v]? with
    | some (.local val) => args := args.push val
    | _ =>
      -- Variable not assigned on this path → emit undef and cache it
      let uv ← emitInstr v none (.undef v) sr
      bindVar v uv
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
    let instrsBefore := (← get).currentInstrs.size
    let val ← translateExpr value
    let instrsAfter := (← get).currentInstrs.size
    -- Rename result to first Name target if a new instruction was emitted
    if instrsAfter > instrsBefore then
      if h : targets.size > 0 then
        match targets[0] with
        | .Name _ ⟨_, tgtName⟩ _ => renameVal val tgtName
        | _ => pure ()
      else pure ()
    for t in targets do
      assignToTarget t val
    return false

  | .AnnAssign _ target annotation ⟨_, value⟩ _ =>
    match value with
    | some v =>
      let instrsBefore := (← get).currentInstrs.size
      let val ← translateExpr v
      let instrsAfter := (← get).currentInstrs.size
      if instrsAfter > instrsBefore then
        match target with
        | .Name _ ⟨_, name⟩ _ => renameVal val name
        | _ => pure ()
        match parseTypeAnnotation annotation with
        | some ty => setValType val ty
        | none => pure ()
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
    -- Use target name for the result
    let baseName := match target with
      | .Name _ ⟨_, name⟩ _ => name
      | _ => "_tmp"
    let result ← emitInstr baseName none (.binOp opKind targetVal rhsVal) sr
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
      let _ ← ssaError sr "bare raise not yet supported"
      finishBlockWithTerm .unreachable sr
    return true

  | .Break .. =>
    match bodyCtx.breakTarget with
    | some target =>
      let args ← buildBranchArgs bodyCtx.allVars sr
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError sr "break outside loop"
      finishBlockWithTerm .unreachable sr
    return true

  | .Continue .. =>
    match bodyCtx.continueTarget with
    | some target =>
      let args ← buildBranchArgs bodyCtx.allVars sr
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError sr "continue outside loop"
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
    ssaWarn sr "delete statement ignored"
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
    let _ ← ssaError sr "Unsupported statement"
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
    | _ => ssaWarn target.ann "Unsupported assignment target"

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

/-- Translate an Array BlockTree (the body of a function or compound stmt).
    Returns true if the body terminated (return/raise/break/continue on all paths),
    meaning the current block was already finalized and no fall-through occurs. -/
partial def translateBody (nodes : Array BlockTree) (bodyCtx : BodyCtx)
    : SSAM Bool := do
  let mut terminated := false
  for node in nodes do
    if terminated then break  -- dead code after terminator
    match node with
    | .stmts slice exprBlockStart exprBlockCount =>
      setExprBlockRange exprBlockStart exprBlockCount
      for s in slice do
        let isTerminator ← translateSimpleStmt s bodyCtx
        if isTerminator then
          terminated := true
          break

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
      let thenTerminated ← translateBody body bodyCtx
      -- Branch to join only if then-body didn't already terminate
      if !thenTerminated then
        let joinArgsFromThen ← buildBranchArgs bodyCtx.allVars sr
        finishBlock (.branch (toBlockId joinBlock) joinArgsFromThen) sr
          (toBlockId elseBlock) #[]
      else
        startNewBlock (toBlockId elseBlock) #[]
      -- Else block: restore pre-if env
      modify fun s => { s with varEnv := preIfEnv }
      let elseParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := elseParams }
      let elseTerminated ← translateBody orelse bodyCtx
      if !elseTerminated then
        let joinArgsFromElse ← buildBranchArgs bodyCtx.allVars sr
        finishBlock (.branch (toBlockId joinBlock) joinArgsFromElse) sr
          (toBlockId joinBlock) #[]
      else
        startNewBlock (toBlockId joinBlock) #[]
      -- Join block
      let joinParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := joinParams }
      -- If both branches terminated, the join block is unreachable
      if thenTerminated && elseTerminated then
        terminated := true

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
      let bodyTerminated ← translateBody body loopCtx
      -- Back edge to header only if body didn't terminate
      if !bodyTerminated then
        let backArgs ← buildBranchArgs bodyCtx.allVars sr
        finishBlock (.branch (toBlockId headerBlock) backArgs) sr
          (toBlockId endBlock) #[]
      else
        startNewBlock (toBlockId endBlock) #[]
      -- End block (StopIteration caught)
      modify fun s => { s with currentExcept := none }
      let endParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := endParams }
      -- Handle orelse (for..else)
      let orelseTerminated ← translateBody orelse bodyCtx
      if orelseTerminated then
        terminated := true

    | .whileLoop test body orelse testBlock bodyBlock endBlock
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
      let thenArgs ← buildBranchArgs bodyCtx.allVars sr
      let elseArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.condBranch condVal (toBlockId bodyBlock) thenArgs
                              (toBlockId endBlock) elseArgs) sr
        (toBlockId bodyBlock) #[]
      let bodyParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := bodyParams }
      let loopCtx := { bodyCtx with
        continueTarget := some (toBlockId testBlock)
        breakTarget := some (toBlockId endBlock)
      }
      let bodyTerminated ← translateBody body loopCtx
      -- Back edge to test only if body didn't terminate
      if !bodyTerminated then
        let backArgs ← buildBranchArgs bodyCtx.allVars sr
        finishBlock (.branch (toBlockId testBlock) backArgs) sr
          (toBlockId endBlock) #[]
      else
        startNewBlock (toBlockId endBlock) #[]
      -- End block
      let endParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := endParams }
      let orelseTerminated ← translateBody orelse bodyCtx
      if orelseTerminated then
        terminated := true

    | .tryExcept body handlers orelse finally_ joinBlock finallyBlock
        reraiseBlock exprBlockStart exprBlockCount sr =>
      setExprBlockRange exprBlockStart exprBlockCount
      -- Determine first handler block (exception target for try body)
      let firstHandlerBid := if h : handlers.size > 0 then
        match handlers[0] with | .mk _ _ _ bid _ _ => bid
      else joinBlock  -- try/finally without except
      -- Where to go after handlers: finally if present, else join
      let afterTarget := match finallyBlock with
        | some fb => toBlockId fb
        | none => toBlockId joinBlock
      -- Set except target and translate try body
      modify fun s => { s with currentExcept := some { target := toBlockId firstHandlerBid } }
      let bodyTerminated ← translateBody body bodyCtx
      modify fun s => { s with currentExcept := none }
      -- Normal path: try succeeded → orelse → afterTarget
      if !bodyTerminated then
        let orelseTerminated ← translateBody orelse bodyCtx
        if !orelseTerminated then
          let args ← buildBranchArgs bodyCtx.allVars sr
          finishBlock (.branch afterTarget args) sr (toBlockId firstHandlerBid) #[]
        else
          startNewBlock (toBlockId firstHandlerBid) #[]
      else
        startNewBlock (toBlockId firstHandlerBid) #[]
      -- Handler blocks: each receives allVars + _exc
      for i in [:handlers.size] do
        if h : i < handlers.size then
          match handlers[i] with
          | .mk typeExpr handlerName handlerBody _handlerBlockId handlerBodyBlockId _handlerSr =>
            let handlerParams ← buildBlockParams bodyCtx.allVars sr
            let excVal ← freshVal "_exc" sr
            let excParam : BlockParam := { val := excVal, type := none, sr }
            modify fun s => { s with currentParams := handlerParams.push excParam }
            -- Next handler or reraise block (for isinstance dispatch fallthrough)
            let nextBlock := if h2 : i + 1 < handlers.size then
              match handlers[i + 1] with | .mk _ _ _ nextBid _ _ => toBlockId nextBid
            else match reraiseBlock with
              | some rb => toBlockId rb
              | none => afterTarget
            -- For typed handlers: isinstance dispatch check
            match typeExpr, handlerBodyBlockId with
            | some texpr, some bodyBid =>
              let typeVal ← translateExpr texpr
              let isinstRef ← emitInstr "_tmp" none
                (.qualifiedRef (QualifiedName.mk' "builtins" "isinstance")) sr
              let checkVal ← emitInstr "_tmp" none
                (.call isinstRef #[.positional excVal, .positional typeVal]) sr
              -- condBranch: match → body block, no match → next handler
              let bodyArgs ← buildBranchArgs bodyCtx.allVars sr
              let bodyArgs := bodyArgs.push excVal
              let nextArgs ← buildBranchArgs bodyCtx.allVars sr
              let nextArgs := nextArgs.push excVal
              finishBlock (.condBranch checkVal (toBlockId bodyBid) bodyArgs nextBlock nextArgs) sr
                (toBlockId bodyBid) #[]
              -- Body block: receives allVars + _exc, binds handler name
              let bodyParams ← buildBlockParams bodyCtx.allVars sr
              let bodyExcVal ← freshVal "_exc" sr
              let bodyExcParam : BlockParam := { val := bodyExcVal, type := none, sr }
              modify fun s => { s with currentParams := bodyParams.push bodyExcParam }
              match handlerName with
              | some name =>
                renameVal bodyExcVal name
                bindVar name bodyExcVal
              | none => pure ()
              let handlerTerminated ← translateBody handlerBody bodyCtx
              if !handlerTerminated then
                let args ← buildBranchArgs bodyCtx.allVars sr
                finishBlock (.branch afterTarget args) sr nextBlock #[]
              else
                startNewBlock nextBlock #[]
            | _, _ =>
              -- Bare handler (no type filter): translate body directly
              match handlerName with
              | some name => bindVar name excVal
              | none => pure ()
              let handlerTerminated ← translateBody handlerBody bodyCtx
              if !handlerTerminated then
                let args ← buildBranchArgs bodyCtx.allVars sr
                finishBlock (.branch afterTarget args) sr nextBlock #[]
              else
                startNewBlock nextBlock #[]
      -- Reraise block (if last handler is typed and exception didn't match any)
      match reraiseBlock with
      | some rbId =>
        let reraiseParams ← buildBlockParams bodyCtx.allVars sr
        let reraiseExcVal ← freshVal "_exc" sr
        let reraiseExcParam : BlockParam := { val := reraiseExcVal, type := none, sr }
        modify fun s => { s with currentParams := reraiseParams.push reraiseExcParam }
        finishBlock (.raise reraiseExcVal) sr (toBlockId joinBlock) #[]
      | none => pure ()
      -- Finally block (if present)
      match finallyBlock with
      | some _fbId =>
        let finallyParams ← buildBlockParams bodyCtx.allVars sr
        modify fun s => { s with currentParams := finallyParams }
        let finallyTerminated ← translateBody finally_ bodyCtx
        if !finallyTerminated then
          let joinArgs ← buildBranchArgs bodyCtx.allVars sr
          finishBlock (.branch (toBlockId joinBlock) joinArgs) sr
            (toBlockId joinBlock) #[]
        else
          startNewBlock (toBlockId joinBlock) #[]
      | none => pure ()
      -- Join block
      let joinParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := joinParams }

    | .withStmt ctxExpr asName body enterBlock excExitBlock reraiseBlock
        normalExitBlock exprBlockStart exprBlockCount sr =>
      setExprBlockRange exprBlockStart exprBlockCount
      -- Evaluate context expression and call __enter__
      let mgrVal ← translateExpr ctxExpr
      bindVar "_mgr" mgrVal  -- synthetic binding for __exit__ calls
      let enterVal ← emitInstr "_tmp" none (.attr mgrVal "__enter__") sr
      let ctxVal ← emitInstr "_tmp" none (.call enterVal #[]) sr
      -- Bind 'as' variable if present
      match asName with
      | some name =>
        renameVal ctxVal name
        bindVar name ctxVal
      | none => pure ()
      -- Branch to enter block (body with exception handler)
      let enterArgs ← buildBranchArgs bodyCtx.allVars sr
      finishBlock (.branch (toBlockId enterBlock) enterArgs) sr
        (toBlockId enterBlock) #[]
      -- Enter block: body with except pointing to excExitBlock
      let enterParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with
        currentParams := enterParams
        currentExcept := some { target := toBlockId excExitBlock }
      }
      let bodyTerminated ← translateBody body bodyCtx
      modify fun s => { s with currentExcept := none }
      -- Normal path: call __exit__(None, None, None), branch to normalExitBlock
      if !bodyTerminated then
        let mgrRef ← lookupVar "_mgr" sr
        let exitRef ← emitInstr "_tmp" none (.attr mgrRef "__exit__") sr
        let noneVal ← emitInstr "_tmp" none .noneLit sr
        let _ ← emitInstr "_tmp" none
          (.call exitRef #[.positional noneVal, .positional noneVal, .positional noneVal]) sr
        let normalArgs ← buildBranchArgs bodyCtx.allVars sr
        finishBlock (.branch (toBlockId normalExitBlock) normalArgs) sr
          (toBlockId excExitBlock) #[]
      else
        startNewBlock (toBlockId excExitBlock) #[]
      -- Exception exit block: call __exit__ with exception, check return value
      let excParams ← buildBlockParams bodyCtx.allVars sr
      let excVal ← freshVal "_exc" sr
      let excParam : BlockParam := { val := excVal, type := none, sr }
      modify fun s => { s with currentParams := excParams.push excParam }
      let excMgrRef ← lookupVar "_mgr" sr
      let excExitRef ← emitInstr "_tmp" none (.attr excMgrRef "__exit__") sr
      let exitResult ← emitInstr "_tmp" none
        (.call excExitRef #[.positional excVal, .positional excVal, .positional excVal]) sr
      -- If __exit__ returns truthy → suppress (normalExitBlock); falsy → re-raise
      let suppressArgs ← buildBranchArgs bodyCtx.allVars sr
      let reraiseArgs ← buildBranchArgs bodyCtx.allVars sr
      let reraiseArgs := reraiseArgs.push excVal
      finishBlock (.condBranch exitResult
        (toBlockId normalExitBlock) suppressArgs
        (toBlockId reraiseBlock) reraiseArgs) sr
        (toBlockId reraiseBlock) #[]
      -- Reraise block: re-raise the exception
      let reraiseParams ← buildBlockParams bodyCtx.allVars sr
      let reraiseExcVal ← freshVal "_exc" sr
      let reraiseExcParam : BlockParam := { val := reraiseExcVal, type := none, sr }
      modify fun s => { s with currentParams := reraiseParams.push reraiseExcParam }
      finishBlock (.raise reraiseExcVal) sr (toBlockId normalExitBlock) #[]
      -- Normal exit block: code continues here
      let normalParams ← buildBlockParams bodyCtx.allVars sr
      modify fun s => { s with currentParams := normalParams }
  return terminated
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
    | _ => ssaWarn target.ann "Unsupported loop target pattern"

/-! ## Top-Level Translation -/

/-- Translate a BlockifyResult into an SSA Func. -/
def translateFunc (result : BlockifyResult) (config : SSAConfig)
    (moduleBindings : Std.HashMap String QualifiedName := {})
    : Func × Array (String × SourceRange) :=
  let initState : SSAState := {
    varEnv := moduleBindings.fold (init := {}) fun env name qn =>
      env.insert name (.qualified qn)
  }
  let action : SSAM Unit := do
    -- Warn if async function
    if result.isAsync then
      ssaWarn result.sr s!"unsupported AsyncFunctionDef '{result.name}'"
    -- Create entry block params for function parameters
    for (pname, typeAnnot) in result.params do
      let varName := if pname.startsWith "**" then (pname.drop 2).toString
        else if pname.startsWith "*" then (pname.drop 1).toString
        else pname
      let val ← freshVal varName SourceRange.none
      let kind := if pname.startsWith "**" then ParamKind.varKeyword
        else if pname.startsWith "*" then ParamKind.varPositional
        else ParamKind.positional
      let paramType := typeAnnot.bind parseTypeAnnotation
      modify fun s => { s with funcParams := s.funcParams.push {
        val, name := varName, type := paramType, default := none, kind
      }}
      bindVar varName val
    -- Start the first block (entry block = bb0)
    startFirstBlock ⟨0⟩ #[]
    -- Translate the body
    let allVarsArray := result.allVars.toArray
    let bodyCtx : BodyCtx := { allVars := allVarsArray }
    let bodyTerminated ← translateBody result.body bodyCtx
    -- Finalize the last block with `ret none` if the body didn't terminate.
    -- This covers join/end blocks from compound statements at the end of a
    -- function body — they are branch targets and must be defined.
    let s ← get
    if !bodyTerminated then
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
  let func : Func := {
    name := result.name
    params := finalState.funcParams
    retType := none
    blocks := finalState.blocks
    names := finalState.names
    decorators := #[]
    sr := result.sr
  }
  (func, finalState.warnings)

/-- Result of translating a module to SSA. -/
public structure TranslateResult where
  module   : Module
  warnings : Array (String × SourceRange)
  errors   : Array (String × SourceRange)
deriving Inhabited

/-- Translate a module's statements into an SSA Module. -/
public def translateModule (moduleName : String)
    (stmts : Array (stmt SourceRange)) : TranslateResult :=
  let config : SSAConfig := {
    prelude := pythonPrelude
    moduleName
  }
  let results := blockifyModule stmts
  -- Build module-level bindings: every function/class defined at module level
  let moduleBindings := results.foldl (init := {}) fun bindings r =>
    if r.name == "@module_init" then bindings
    else if r.name.any (· == '.') then
      -- Class method like "Config.__init__" → bind "Config" → module.Config
      let className := r.name.takeWhile (· != '.') |>.toString
      bindings.insert className (QualifiedName.mk' moduleName className)
    else
      bindings.insert r.name (QualifiedName.mk' moduleName r.name)
  let translated := results.map (translateFunc · config moduleBindings)
  let funcs := translated.map (·.1)
  let warnings := translated.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
  { module := { name := moduleName, funcs }, warnings, errors := #[] }

end Strata.Python.PythonToSSA

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.PythonDialect
import Strata.Languages.Python.SSA.Blockify
public import Strata.Languages.Python.SSA.IR
import Strata.Util.DecideProp

/-!
# PythonToSSA: Strict Block-Argument SSA Construction

Direct AST traversal with forwarding context (`fwd`) for expression-level
value threading. All cross-block references are eliminated:

- **Expression blocks** (BoolOp, IfExp, chained Compare): values that must
  survive are passed as extra block params via the `fwd` mechanism.
- **Synthetic variables** (`_iter`, `_mgr`): included in `allVars` so they
  are threaded through statement-level block params.
- **Statement blocks**: demand-driven block params via backward analysis.

Key design: `translateExpr` takes and returns `fwd : Array (String × SSAVal)`.
Block-creating expressions thread `fwd` through sub-blocks; non-block
expressions pass it through unchanged.
-/

namespace Strata.Python.PythonToSSA

open Strata.Python (stmt expr constant operator unaryop boolop cmpop
                    keyword arguments alias excepthandler withitem)
open Strata.Python.SSA
open Strata.Python.Blockify (isSimpleStmt)

/-! ## Module Scanning -/

/-- Lightweight record for a function/method/module-init to translate. -/
private structure FuncInfo where
  name    : String
  params  : Array (String × Option (expr SourceRange))
  body    : Array (stmt SourceRange)
  sr      : SourceRange
  globals : Std.HashSet String
  isAsync : Bool := false

/-- Extract parameter names (with `*`/`**` prefixes) and optional type annotations. -/
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

/-- Collect module-level global names (function defs, class defs, imports). -/
private def collectModuleGlobals (stmts : Array (stmt SourceRange))
    : Std.HashSet String := Id.run do
  let mut globals : Std.HashSet String := {}
  for s in stmts do
    match s with
    | .FunctionDef _ ⟨_, name⟩ .. | .AsyncFunctionDef _ ⟨_, name⟩ .. =>
      globals := globals.insert name
    | .ClassDef _ ⟨_, name⟩ .. =>
      globals := globals.insert name
    | .Import _ ⟨_, aliases⟩ =>
      for a in aliases do
        globals := globals.insert (a.asname.getD a.name)
    | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
      for a in aliases do
        globals := globals.insert (a.asname.getD a.name)
    | _ => pure ()
  return globals

/-- Scan a module's top-level statements into `FuncInfo` records. -/
private def scanModule (stmts : Array (stmt SourceRange))
    : Array FuncInfo := Id.run do
  let globals := collectModuleGlobals stmts
  let mut results : Array FuncInfo := #[]
  for s in stmts do
    match s with
    | .FunctionDef sr ⟨_, name⟩ args ⟨_, body⟩ _ _ _ _ =>
      results := results.push { name, params := extractParams args, body, sr, globals }
    | .AsyncFunctionDef sr ⟨_, name⟩ args ⟨_, body⟩ _ _ _ _ =>
      results := results.push { name, params := extractParams args, body, sr, globals, isAsync := true }
    | .ClassDef sr ⟨_, className⟩ _ _ ⟨_, classBody⟩ _ _ =>
      for cs in classBody do
        match cs with
        | .FunctionDef methodSr ⟨_, methodName⟩ args ⟨_, methodBody⟩ _ _ _ _ =>
          results := results.push { name := s!"{className}.{methodName}"
                                    params := extractParams args
                                    body := methodBody, sr := methodSr, globals }
        | _ => pure ()
      let initStmts := classBody.filter fun cs =>
        match cs with | .FunctionDef .. => false | _ => true
      if !initStmts.isEmpty then
        results := results.push { name := s!"@{className}_init", params := #[]
                                  body := initStmts, sr, globals }
    | _ => pure ()
  let moduleStmts := stmts.filter fun s =>
    match s with | .FunctionDef .. | .AsyncFunctionDef .. | .ClassDef .. => false | _ => true
  if !moduleStmts.isEmpty then
    results := results.push { name := "@module_init", params := #[]
                              body := moduleStmts, sr := SourceRange.none, globals }
  return results

/-! ## Binding Environment -/

inductive Binding where
  | local     (val : SSAVal)
  | qualified (qn : QualifiedName)
deriving Inhabited

/-! ## Configuration and State -/

structure SSAConfig where
  prelude    : Std.HashMap String QualifiedName
  moduleName : String
deriving Inhabited

structure SSAState where
  nextValId      : Nat := 0
  names          : Array SSAName := #[]
  blocks         : Array Block := #[]
  currentInstrs  : Array NamedInstr := #[]
  /-- Maps SSAVal.id → index in currentInstrs for O(1) type updates. -/
  valInstrIdx    : Std.HashMap Nat Nat := {}
  /-- freshBlockId of the block currently being built. -/
  currentBlockId : BlockId := ⟨0⟩
  /-- Maps freshBlockId → program-order (emission) BlockId.
      Populated as blocks are finalized. -/
  blockIdMap     : Array BlockId := #[]
  currentParams  : Array BlockParam := #[]
  currentExcept  : Option ExceptTarget := none
  varEnv         : Std.HashMap String Binding := {}
  nameSuffixes   : Std.HashMap String Nat := {}
  /-- Next block ID to allocate (statement + expression blocks). -/
  nextBlockId    : Nat := 1  -- bb0 is reserved for entry
  /-- Demand analysis array (reverse block-ID order). -/
  demandArr      : Array Blockify.DemandVars := #[]
  /-- Extra synthetic values (e.g., `_iter`, `_mgr`) threaded through all blocks.
      Not in varEnv — carried explicitly. Updated on block transitions. -/
  scopeExtras    : Array (String × SSAVal) := #[]
  warnings       : Array (String × SourceRange) := #[]
  funcParams     : Array FuncParam := #[]
deriving Inhabited

abbrev SSAM := ReaderT SSAConfig (StateM SSAState)

/-! ## Monad Helpers -/

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

/-- Get the base name for an SSA value. -/
def valName (v : SSAVal) : SSAM String := do
  let s ← get
  if h : v.id < s.names.size then return s.names[v.id].base
  else return "_tmp"

def emitInstr (base : String) (type : Option PyType) (instr : Instruction)
    (sr : SourceRange) (exceptArgs : Option (Array ExceptArgVal) := none)
    : SSAM SSAVal := do
  let val ← freshVal base sr
  modify fun s => { s with
    valInstrIdx := s.valInstrIdx.insert val.id s.currentInstrs.size
    currentInstrs := s.currentInstrs.push {
      result := some val, type, instr, sr, exceptArgs
  }}
  return val

def emitVoidInstr (instr : Instruction) (sr : SourceRange)
    (exceptArgs : Option (Array ExceptArgVal) := none) : SSAM Unit :=
  modify fun s => { s with currentInstrs := s.currentInstrs.push {
    result := none, type := none, instr, sr, exceptArgs
  }}

def ssaWarn (sr : SourceRange) (msg : String) : SSAM Unit :=
  modify fun s => { s with warnings := s.warnings.push (msg, sr) }

def ssaError (sr : SourceRange) (msg : String) : SSAM SSAVal := do
  ssaWarn sr msg
  emitInstr "_err" none (.unsupported msg) sr

def lookupVar (name : String) (sr : SourceRange) : SSAM SSAVal := do
  let s ← get
  match s.varEnv[name]? with
  | some (.local val) => return val
  | some (.qualified qn) => emitInstr name none (.qualifiedRef qn) sr
  | none =>
    let cfg ← read
    match cfg.prelude[name]? with
    | some qn => emitInstr name none (.qualifiedRef qn) sr
    | none => ssaError sr s!"Unresolved name: {name}"

def bindVar (name : String) (val : SSAVal) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.local val) }

def bindQualified (name : String) (qn : QualifiedName) : SSAM Unit :=
  modify fun s => { s with varEnv := s.varEnv.insert name (.qualified qn) }

def renameVal (val : SSAVal) (newBase : String) : SSAM Unit :=
  modify fun s =>
    let suffix := s.nameSuffixes.getD newBase 0
    if h : val.id < s.names.size then
      { s with
        names := s.names.set val.id { base := newBase, suffix }
        nameSuffixes := s.nameSuffixes.insert newBase (suffix + 1) }
    else s

def setValType (val : SSAVal) (type : PyType) : SSAM Unit := do
  let s ← get
  match s.valInstrIdx[val.id]? with
  | some idx =>
    if h : idx < s.currentInstrs.size then
      let ni := s.currentInstrs[idx]
      if ni.type.isNone then
        set { s with currentInstrs := s.currentInstrs.set idx { ni with type := some type } }
    else
      ssaWarn .none s!"internal: setValType index {idx} out of range for val %{val.id}"
  | none =>
    ssaWarn .none s!"internal: setValType has no instruction index for val %{val.id}"

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
  | _ => none

/-! ## Block Management -/

/-- Record a freshBlockId → emission-order mapping. Extends the array if needed. -/
private def recordBlockIdMap (map : Array BlockId) (freshId emitId : Nat) : Array BlockId :=
  if freshId < map.size then
    map.set! freshId ⟨emitId⟩
  else Id.run do
    let mut m := map
    while m.size <= freshId do
      m := m.push ⟨0⟩
    return m.set! freshId ⟨emitId⟩

/-- Allocate a fresh block ID. -/
def freshBlockId : SSAM BlockId := do
  let s ← get
  let id := s.nextBlockId
  set { s with nextBlockId := id + 1 }
  return ⟨id⟩

/-- Look up demand vars for a block ID from the state's demand array. -/
def getDemandVars (blockId : BlockId) : SSAM (Array String) := do
  let s ← get
  let idx := s.demandArr.size - (blockId.id + 1)
  if h : idx < s.demandArr.size then
    return s.demandArr[idx]
  else
    ssaWarn .none s!"internal: getDemandVars block bb{blockId.id} out of range (demandArr.size={s.demandArr.size})"
    return #[]

/-! ## Forwarding Context -/

/-- The forwarding context: names + SSA values that must survive through
    expression blocks. Block-creating expressions thread these as extra
    block params/branch args. Stored as parallel arrays for O(1) zip/extract. -/
structure Fwd where
  names : Array String
  vals  : Array SSAVal
deriving Inhabited

instance : EmptyCollection Fwd := ⟨{ names := #[], vals := #[] }⟩

def Fwd.size (fwd : Fwd) : Nat := fwd.vals.size

/-- Extract just the SSA values from the forwarding context (for branch args). -/
def fwdVals (fwd : Fwd) : Array SSAVal := fwd.vals

/-- Zip names from old fwd with new SSA values. O(1) — reuses names array. -/
def zipFwd (fwd : Fwd) (vals : Array SSAVal) : Fwd :=
  { fwd with vals }

/-- Push a new name/value pair onto the forwarding context. -/
def Fwd.push (fwd : Fwd) (name : String) (val : SSAVal) : Fwd :=
  { names := fwd.names.push name, vals := fwd.vals.push val }

/-- Pop the last entry from the forwarding context. -/
def Fwd.pop (fwd : Fwd) : Fwd :=
  { names := fwd.names.pop, vals := fwd.vals.pop }

/-- Shrink forwarding context to the first `n` entries. -/
def Fwd.shrink (fwd : Fwd) (n : Nat) : Fwd :=
  { names := fwd.names.shrink n, vals := fwd.vals.shrink n }

/-- Get the value at index `i`. -/
def Fwd.val! (fwd : Fwd) (i : Nat) : SSAVal := fwd.vals[i]!

/-- Get the name at index `i`. -/
def Fwd.name! (fwd : Fwd) (i : Nat) : String := fwd.names[i]!

/-- Get the value of the last entry. -/
def Fwd.backVal! (fwd : Fwd) : SSAVal := fwd.vals.back!

/-- Append two forwarding contexts. -/
def Fwd.append (fwd1 fwd2 : Fwd) : Fwd :=
  { names := fwd1.names ++ fwd2.names, vals := fwd1.vals ++ fwd2.vals }

instance : HAppend Fwd Fwd Fwd := ⟨Fwd.append⟩

/-- Create fresh block params for the forwarding context. Returns new params
    and updates the forwarding context with the new SSAVals. -/
def fwdToParams (fwd : Fwd) (sr : SourceRange) : SSAM (Array BlockParam × Fwd) := do
  let mut newVals : Array SSAVal := #[]
  let mut params : Array BlockParam := #[]
  for name in fwd.names do
    let val ← freshVal name sr
    params := params.push { val, type := none, sr }
    newVals := newVals.push val
  return (params, ⟨fwd.names, newVals⟩)

/-- After fwdToParams, bind the demand portion of a fwd into varEnv so
    lookupVar returns the new param values instead of stale cross-block refs. -/
def bindDemandFwd (fwd : Fwd) (demandSize : Nat) : SSAM Unit := do
  for i in [:demandSize] do
    if i < demandSize then
      bindVar (fwd.name! i) (fwd.val! i)

/-- Build a fwd prefix from demand vars: look up each variable from varEnv.
    Returns a Fwd to prepend to the caller's fwd. -/
def demandToFwd (blockId : BlockId) (sr : SourceRange)
    : SSAM Fwd := do
  let vars ← getDemandVars blockId
  let mut vals : Array SSAVal := #[]
  for v in vars do
    let val ← lookupVar v sr
    vals := vals.push val
  return ⟨vars, vals⟩

def finishBlock (term : Terminator) (termSr : SourceRange)
    (nextParams : Array BlockParam)
    (nextExcept : Option ExceptTarget := none) : SSAM Unit := do
  let s ← get
  let emitId := s.blocks.size
  let blockIdMap := recordBlockIdMap s.blockIdMap s.currentBlockId.id emitId
  let block : Block := {
    id := ⟨emitId⟩
    params := s.currentParams
    instrs := s.currentInstrs
    term, termSr
    except := s.currentExcept
  }
  set { s with
    blocks := s.blocks.push block
    blockIdMap
    currentInstrs := #[]
    valInstrIdx := {}
    currentParams := nextParams
    currentExcept := nextExcept
  }

def finishBlockWithTerm (term : Terminator) (termSr : SourceRange) : SSAM Unit := do
  let s ← get
  let emitId := s.blocks.size
  let blockIdMap := recordBlockIdMap s.blockIdMap s.currentBlockId.id emitId
  let block : Block := {
    id := ⟨emitId⟩
    params := s.currentParams
    instrs := s.currentInstrs
    term, termSr
    except := s.currentExcept
  }
  set { s with blocks := s.blocks.push block, blockIdMap, currentInstrs := #[], valInstrIdx := {} }

def startNewBlock (params : Array BlockParam)
    (except : Option ExceptTarget := none) : SSAM Unit :=
  modify fun s => { s with
    currentParams := params
    currentInstrs := #[]
    valInstrIdx := {}
    currentExcept := except
  }

def startFirstBlock (params : Array BlockParam)
    (except : Option ExceptTarget := none) : SSAM Unit :=
  modify fun s => { s with
    currentBlockId := ⟨0⟩
    currentParams := params
    currentExcept := except
  }

/-! ## Forwarding Helpers -/

/-! ## Expression Translation with Forwarding -/

/-- Translate a Python expression to an SSA value, threading the forwarding
    context through any expression blocks created.

    Returns (result, updatedFwd) where updatedFwd.size == fwd.size.
    If the expression created blocks, updatedFwd contains remapped SSAVals.
    If not, updatedFwd == fwd.map Prod.snd (unchanged values). -/
partial def translateExpr (e : expr SourceRange) (fwd : Fwd)
    : SSAM (SSAVal × Array SSAVal) := do
  let sr := e.ann
  let passFwd := fwdVals fwd  -- default: pass through unchanged
  match e with
  | .Constant _ c _ =>
    let v ← translateConstant c
    return (v, passFwd)
  | .Name _ ⟨_, name⟩ _ =>
    let v ← lookupVar name sr
    return (v, passFwd)

  | .BinOp _ left op right =>
    let opKind := translateBinOp op
    let (lv, fwdVals1) ← translateExpr left fwd
    let lName ← valName lv
    let fwd1 := (zipFwd fwd fwdVals1).push lName lv
    let (rv, fwdVals2) ← translateExpr right fwd1
    let lv' := fwdVals2.back!
    let fwdVals2 := fwdVals2.pop
    let result ← emitInstr "_tmp" none (.binOp opKind lv' rv) sr
    return (result, fwdVals2)

  | .UnaryOp _ op operand =>
    let opKind := translateUnaryOp op
    let (v, fwdVals1) ← translateExpr operand fwd
    let result ← emitInstr "_tmp" none (.unaryOp opKind v) sr
    return (result, fwdVals1)

  | .Compare _ left ⟨_, ops⟩ ⟨_, comparators⟩ =>
    let (lv, fwdVals1) ← translateExpr left fwd
    if ops.size == 1 && comparators.size == 1 then
      let fwd1 := zipFwd fwd fwdVals1
      let (rv, fwdVals2) ← translateExpr comparators[0]! fwd1
      let result ← emitInstr "_tmp" none
        (.compareOp (translateCmpOp ops[0]!) lv rv) sr
      return (result, fwdVals2)
    else
      -- Chained comparison creates blocks
      let fwd1 := zipFwd fwd fwdVals1
      let (result, fwdVals2) ← translateChainedCmp lv ops comparators sr fwd1
      return (result, fwdVals2)

  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    -- Evaluate function and args, threading fwd through any block-creating
    -- sub-expressions. Always push evaluated values onto fwd' so they survive
    -- block boundaries, then read back remapped values at the end.
    let (fv, fwdVals1) ← translateExpr f fwd
    let mut fwd' := zipFwd fwd fwdVals1
    let origSize := fwd.size
    -- Push funcVal
    let fName ← valName fv
    fwd' := fwd'.push fName fv
    -- Evaluate and push positional args
    let mut argKinds : Array CallArg := #[]
    for i in [:args.size] do
      if h : i < args.size then
        let a := args[i]
        match a with
        | .Starred _ value _ =>
          let (av, fwdVals') ← translateExpr value fwd'
          fwd' := zipFwd fwd' fwdVals'
          argKinds := argKinds.push (.starArgs av)
          let aName ← valName av
          fwd' := fwd'.push aName av
        | _ =>
          let (av, fwdVals') ← translateExpr a fwd'
          fwd' := zipFwd fwd' fwdVals'
          argKinds := argKinds.push (.positional av)
          let aName ← valName av
          fwd' := fwd'.push aName av
    -- Evaluate and push kwargs
    for kw in kwargs do
      match kw with
      | .mk_keyword _ kwArg kwValue =>
        let (kv, fwdVals') ← translateExpr kwValue fwd'
        fwd' := zipFwd fwd' fwdVals'
        match kwArg.val with
        | some ⟨_, argName⟩ => argKinds := argKinds.push (.keyword argName kv)
        | none => argKinds := argKinds.push (.starKwargs kv)
        let kName ← valName kv
        fwd' := fwd'.push kName kv
    -- Read back remapped values from fwd'
    let fv' := fwd'.val! origSize
    let mut callArgs : Array CallArg := #[]
    let mut pushIdx := origSize + 1
    for i in [:argKinds.size] do
      if h : i < argKinds.size then
        let remapped := fwd'.val! pushIdx
        match argKinds[i] with
        | .positional _ => callArgs := callArgs.push (.positional remapped)
        | .starArgs _ => callArgs := callArgs.push (.starArgs remapped)
        | .keyword n _ => callArgs := callArgs.push (.keyword n remapped)
        | .starKwargs _ => callArgs := callArgs.push (.starKwargs remapped)
        pushIdx := pushIdx + 1
    -- Trim fwd' back to original size
    fwd' := fwd'.shrink origSize
    let result ← emitInstr "_tmp" none (.call fv' callArgs) sr
    return (result, fwdVals fwd')

  | .Attribute _ value ⟨_, attrName⟩ _ =>
    let (objV, fwdVals1) ← translateExpr value fwd
    let result ← emitInstr "_tmp" none (.attr objV attrName) sr
    return (result, fwdVals1)

  | .Subscript _ value slice _ =>
    let (objV, fwdVals1) ← translateExpr value fwd
    let fwd1 := zipFwd fwd fwdVals1
    match slice with
    | .Slice sliceSr ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, step⟩ =>
      let loV ← match lo with
        | some e => let (v, _) ← translateExpr e fwd1; pure (some v)
        | none => pure none
      let hiV ← match hi with
        | some e => let (v, _) ← translateExpr e fwd1; pure (some v)
        | none => pure none
      let stV ← match step with
        | some e => let (v, _) ← translateExpr e fwd1; pure (some v)
        | none => pure none
      let result ← emitInstr "_tmp" none (.getSlice objV loV hiV stV) sliceSr
      return (result, fwdVals1)
    | _ =>
      let (keyV, fwdVals2) ← translateExpr slice fwd1
      let result ← emitInstr "_tmp" none (.getItem objV keyV) sr
      return (result, fwdVals2)

  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    let mut ks : Array SSAVal := #[]
    let mut vs : Array SSAVal := #[]
    for k in keys do
      match k with
      | .some_expr _ ke =>
        let (kv, _) ← translateExpr ke fwd
        ks := ks.push kv
      | _ => pure ()
    for v in values do
      let (vv, _) ← translateExpr v fwd
      vs := vs.push vv
    let result ← emitInstr "_tmp" none (.mkDict ks vs) sr
    return (result, passFwd)

  | .List _ ⟨_, elts⟩ _ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let (v, _) ← translateExpr e fwd
      vals := vals.push v
    let result ← emitInstr "_tmp" none (.mkList vals) sr
    return (result, passFwd)

  | .Tuple _ ⟨_, elts⟩ _ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let (v, _) ← translateExpr e fwd
      vals := vals.push v
    let result ← emitInstr "_tmp" none (.mkTuple vals) sr
    return (result, passFwd)

  | .Set _ ⟨_, elts⟩ =>
    let mut vals : Array SSAVal := #[]
    for e in elts do
      let (v, _) ← translateExpr e fwd
      vals := vals.push v
    let result ← ssaError sr "set literal not in SSA IR"
    return (result, passFwd)

  | .JoinedStr _ ⟨_, values⟩ =>
    let mut parts : Array SSAVal := #[]
    for v in values do
      match v with
      | .FormattedValue fvSr fvValue _ _ =>
        let (val, _) ← translateExpr fvValue fwd
        let fmted ← emitInstr "_tmp" none (.fmtValue val) fvSr
        parts := parts.push fmted
      | .Interpolation intSr intValue _ _ _ =>
        let (val, _) ← translateExpr intValue fwd
        let fmted ← emitInstr "_tmp" none (.fmtValue val) intSr
        parts := parts.push fmted
      | .Constant _ (.ConString _ ⟨_, s⟩) _ =>
        let sv ← emitInstr "_tmp" none (.strLit s) v.ann
        parts := parts.push sv
      | _ =>
        let (val, _) ← translateExpr v fwd
        parts := parts.push val
    let result ← emitInstr "_tmp" none (.strConcat parts) sr
    return (result, passFwd)

  | .TemplateStr _ ⟨_, values⟩ =>
    let mut parts : Array SSAVal := #[]
    for v in values do
      let (val, _) ← translateExpr v fwd
      parts := parts.push val
    let result ← emitInstr "_tmp" none (.strConcat parts) sr
    return (result, passFwd)

  | .FormattedValue _ value _ _ =>
    let (val, fv1) ← translateExpr value fwd
    let result ← emitInstr "_tmp" none (.fmtValue val) sr
    return (result, fv1)

  | .Interpolation _ value _ _ _ =>
    let (val, fv1) ← translateExpr value fwd
    let result ← emitInstr "_tmp" none (.fmtValue val) sr
    return (result, fv1)

  | .Starred _ value _ =>
    translateExpr value fwd

  | .BoolOp _ op ⟨_, values⟩ =>
    translateBoolOp op values sr fwd

  | .IfExp _ test body orelse =>
    translateIfExp test body orelse sr fwd

  -- Unsupported expressions
  | .ListComp .. =>
    ssaWarn sr "unsupported ListComp"
    let v ← emitInstr "_tmp" none (.unsupported "ListComp") sr
    return (v, passFwd)
  | .DictComp .. =>
    ssaWarn sr "unsupported DictComp"
    let v ← emitInstr "_tmp" none (.unsupported "DictComp") sr
    return (v, passFwd)
  | .SetComp .. =>
    ssaWarn sr "unsupported SetComp"
    let v ← emitInstr "_tmp" none (.unsupported "SetComp") sr
    return (v, passFwd)
  | .GeneratorExp .. =>
    ssaWarn sr "unsupported GeneratorExp"
    let v ← emitInstr "_tmp" none (.unsupported "GeneratorExp") sr
    return (v, passFwd)
  | .Lambda .. =>
    ssaWarn sr "unsupported Lambda"
    let v ← emitInstr "_tmp" none (.unsupported "Lambda") sr
    return (v, passFwd)
  | .NamedExpr .. =>
    ssaWarn sr "unsupported NamedExpr"
    let v ← emitInstr "_tmp" none (.unsupported "NamedExpr") sr
    return (v, passFwd)
  | .Yield .. =>
    ssaWarn sr "unsupported Yield"
    let v ← emitInstr "_tmp" none (.unsupported "Yield") sr
    return (v, passFwd)
  | .YieldFrom .. =>
    ssaWarn sr "unsupported YieldFrom"
    let v ← emitInstr "_tmp" none (.unsupported "YieldFrom") sr
    return (v, passFwd)
  | .Await .. =>
    ssaWarn sr "unsupported Await"
    let v ← emitInstr "_tmp" none (.unsupported "Await") sr
    return (v, passFwd)
  | _ =>
    let v ← ssaError sr "Unsupported expression"
    return (v, passFwd)
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
    | _ => .add

  translateUnaryOp (op : unaryop SourceRange) : UnaryOpKind :=
    match op with
    | .Not .. => .not_ | .USub .. => .uSub
    | _ => .not_

  translateCmpOp (op : cmpop SourceRange) : CmpOpKind :=
    match op with
    | .Eq .. => .eq | .NotEq .. => .notEq | .Lt .. => .lt | .LtE .. => .ltE
    | .Gt .. => .gt | .GtE .. => .gtE | .Is .. => .is_ | .IsNot .. => .isNot
    | .In .. => .in_ | .NotIn .. => .notIn

  /-- Chained comparison with fwd threading. -/
  translateChainedCmp (leftVal : SSAVal)
      (ops : Array (cmpop SourceRange))
      (comparators : Array (expr SourceRange))
      (sr : SourceRange) (fwd : Fwd) : SSAM (SSAVal × Array SSAVal) := do
    let n := comparators.size
    -- Allocate blocks
    let mut blockIds : Array BlockId := #[]
    for _ in [:n] do
      let bid ← freshBlockId
      blockIds := blockIds.push bid
    let joinBlockId := blockIds.back!
    -- Prepend demand vars to fwd so they're threaded through sub-blocks
    let demandFwd ← demandToFwd blockIds[0]! sr
    let demandSize := demandFwd.size
    let extFwd := demandFwd ++ fwd
    -- First comparison: leftVal op[0] comparators[0]
    -- Push leftVal onto fwd to protect it across expression blocks, then
    -- recover the (possibly remapped) value by index after translation.
    let lvName ← valName leftVal
    let baseSize := extFwd.size
    let mut fwd' := extFwd.push lvName leftVal
    let (firstRight, fwdVals1) ← translateExpr comparators[0]! fwd'
    fwd' := zipFwd fwd' fwdVals1
    let leftVal' := fwd'.val! baseSize
    fwd' := fwd'.shrink baseSize
    let mut prevRight := firstRight
    let mut cmpResult ← emitInstr "_tmp" none
      (.compareOp (translateCmpOp ops[0]!) leftVal' prevRight) sr
    -- For each subsequent comparison
    for i in [1:n] do
      if h : i < n then
        let evalBlockId := blockIds[i - 1]!
        -- Thread fwd + prevRight through blocks
        let prName ← valName prevRight
        let fwdBaseSize := fwd'.size
        let fwdWithPrev := fwd'.push prName prevRight
        let fwdArgs := fwdVals fwdWithPrev
        let joinArgs := #[cmpResult] ++ fwdVals fwd'
        -- short-circuit: false → join, true → continue
        let (evalParams, evalFwd) ← fwdToParams fwdWithPrev sr
        bindDemandFwd evalFwd demandSize
        finishBlock (.condBranch cmpResult evalBlockId fwdArgs joinBlockId joinArgs) sr
          evalParams
        modify fun s => { s with currentBlockId := evalBlockId }
        prevRight := evalFwd.val! fwdBaseSize
        fwd' := evalFwd.shrink fwdBaseSize
        let (nextRight, fwdVals') ← translateExpr comparators[i] evalFwd
        fwd' := zipFwd fwd' fwdVals'.pop
        prevRight := nextRight
        cmpResult ← emitInstr "_tmp" none
          (.compareOp (translateCmpOp ops[i]!) evalFwd.backVal! nextRight) sr
    -- Branch to join with final result
    let resultVal ← freshVal "_tmp" sr
    let mut joinFwdParams : Array BlockParam := #[]
    for name in fwd'.names do
      let v ← freshVal name sr
      joinFwdParams := joinFwdParams.push { val := v, type := none, sr }
    let joinParam : BlockParam := { val := resultVal, type := none, sr }
    let allJoinParams := #[joinParam] ++ joinFwdParams
    let joinArgs := #[cmpResult] ++ fwdVals fwd'
    finishBlock (.branch joinBlockId joinArgs) sr allJoinParams
    modify fun s => { s with currentBlockId := joinBlockId }
    -- Rebind demand vars from join params, then strip demand prefix
    for i in [:demandSize] do
      if h : i < joinFwdParams.size then
        bindVar (fwd'.name! i) joinFwdParams[i].val
    let joinFwdVals := (joinFwdParams.extract demandSize joinFwdParams.size).map (·.val)
    return (resultVal, joinFwdVals)

  /-- Short-circuit BoolOp with fwd threading. -/
  translateBoolOp (op : boolop SourceRange) (values : Array (expr SourceRange))
      (sr : SourceRange) (fwd : Fwd) : SSAM (SSAVal × Array SSAVal) := do
    if values.size < 2 then
      if h : values.size > 0 then translateExpr values[0] fwd
      else
        let v ← ssaError sr "Empty BoolOp"
        return (v, fwdVals fwd)
    else
      let n := values.size
      -- Allocate blocks: n-1 eval + 1 join
      let mut blockIds : Array BlockId := #[]
      for _ in [:n] do
        let bid ← freshBlockId
        blockIds := blockIds.push bid
      let joinBlockId := blockIds.back!
      -- Prepend demand vars to fwd
      let demandFwd ← demandToFwd blockIds[0]! sr
      let demandSize := demandFwd.size
      let extFwd := demandFwd ++ fwd
      -- Evaluate first operand
      let (firstVal, fwdVals1) ← translateExpr values[0]! extFwd
      let mut fwd' := zipFwd extFwd fwdVals1
      let mut lastVal := firstVal
      -- For each subsequent operand: condBranch + eval
      for i in [1:n] do
        if h : i < n then
          let evalBlockId := blockIds[i - 1]!
          let fwdArgs := fwdVals fwd'
          let joinArgs := #[lastVal] ++ fwdArgs
          let (evalParams, evalFwd) ← fwdToParams fwd' sr
          bindDemandFwd evalFwd demandSize
          match op with
          | .And _ =>
            finishBlock (.condBranch lastVal evalBlockId fwdArgs joinBlockId joinArgs) sr
              evalParams
          | .Or _ =>
            finishBlock (.condBranch lastVal joinBlockId joinArgs evalBlockId fwdArgs) sr
              evalParams
          modify fun s => { s with currentBlockId := evalBlockId }
          fwd' := evalFwd
          let (val, fwdVals') ← translateExpr values[i] evalFwd
          fwd' := zipFwd fwd' fwdVals'
          lastVal := val
      -- Branch to join
      let resultVal ← freshVal "_tmp" sr
      let mut joinFwdParams : Array BlockParam := #[]
      for name in fwd'.names do
        let v ← freshVal name sr
        joinFwdParams := joinFwdParams.push { val := v, type := none, sr }
      let joinParam : BlockParam := { val := resultVal, type := none, sr }
      let allJoinParams := #[joinParam] ++ joinFwdParams
      let joinArgs := #[lastVal] ++ fwdVals fwd'
      finishBlock (.branch joinBlockId joinArgs) sr allJoinParams
      modify fun s => { s with currentBlockId := joinBlockId }
      -- Rebind demand vars from join params, then strip demand prefix
      for i in [:demandSize] do
        if h : i < joinFwdParams.size then
          bindVar (fwd'.name! i) joinFwdParams[i].val
      let joinFwdVals := (joinFwdParams.extract demandSize joinFwdParams.size).map (·.val)
      return (resultVal, joinFwdVals)

  /-- IfExp with fwd threading. -/
  translateIfExp (test body orelse : expr SourceRange)
      (sr : SourceRange) (fwd : Fwd) : SSAM (SSAVal × Array SSAVal) := do
    let (condVal, fwdVals1) ← translateExpr test fwd
    let fwd1 := zipFwd fwd fwdVals1
    let thenBlockId ← freshBlockId
    let elseBlockId ← freshBlockId
    let joinBlockId ← freshBlockId
    -- Prepend demand vars to fwd
    let demandFwd ← demandToFwd thenBlockId sr
    let demandSize := demandFwd.size
    let extFwd := demandFwd ++ fwd1
    let fwdArgs := fwdVals extFwd
    -- condBranch with fwd as extra args
    let (thenParams, thenFwd) ← fwdToParams extFwd sr
    bindDemandFwd thenFwd demandSize
    finishBlock (.condBranch condVal thenBlockId fwdArgs elseBlockId fwdArgs) sr
      thenParams
    modify fun s => { s with currentBlockId := thenBlockId }
    -- Then block
    let (bodyVal, thenFwdVals) ← translateExpr body thenFwd
    let thenJoinArgs := #[bodyVal] ++ thenFwdVals
    let (elseParams, elseFwd) ← fwdToParams extFwd sr
    bindDemandFwd elseFwd demandSize
    finishBlock (.branch joinBlockId thenJoinArgs) sr elseParams
    modify fun s => { s with currentBlockId := elseBlockId }
    -- Else block
    let (orelseVal, elseFwdVals) ← translateExpr orelse elseFwd
    let elseJoinArgs := #[orelseVal] ++ elseFwdVals
    -- Join block
    let resultVal ← freshVal "_tmp" sr
    let mut joinFwdParams : Array BlockParam := #[]
    for name in extFwd.names do
      let v ← freshVal name sr
      joinFwdParams := joinFwdParams.push { val := v, type := none, sr }
    let joinParam : BlockParam := { val := resultVal, type := none, sr }
    let allJoinParams := #[joinParam] ++ joinFwdParams
    finishBlock (.branch joinBlockId elseJoinArgs) sr allJoinParams
    modify fun s => { s with currentBlockId := joinBlockId }
    -- Rebind demand vars from join params, then strip demand prefix
    for i in [:demandSize] do
      if h : i < joinFwdParams.size then
        bindVar (extFwd.name! i) joinFwdParams[i].val
    let joinFwdVals := (joinFwdParams.extract demandSize joinFwdParams.size).map (·.val)
    return (resultVal, joinFwdVals)

/-! ## Statement Translation -/

structure BodyCtx where
  demandArr : Array Blockify.DemandVars := #[]
  continueTarget : Option BlockId := none
  breakTarget : Option BlockId := none
  /-- Number of scopeExtras the break target expects. -/
  breakExtrasCount : Nat := 0
  /-- Number of scopeExtras the continue target expects. -/
  continueExtrasCount : Nat := 0
  handlerTarget : Option BlockId := none

/-- Look up demand vars for a given block ID.
    Falls back to allVars if the demand array doesn't cover this block. -/
@[inline]
def BodyCtx.demandVarsFor (ctx : BodyCtx) (blockId : BlockId) (h : blockId.id < ctx.demandArr.size ) : Array String :=
  ctx.demandArr[ctx.demandArr.size - (blockId.id + 1)]

def buildBranchArgs (allVars : Array String) (sr : SourceRange)
    : SSAM (Array SSAVal) := do
  let mut args : Array SSAVal := #[]
  for v in allVars do
    let s ← get
    match s.varEnv[v]? with
    | some (.local val) => args := args.push val
    | _ =>
      let uv ← emitInstr v none (.undef v) sr
      bindVar v uv
      args := args.push uv
  return args

def buildBlockParams (allVars : Array String) (sr : SourceRange)
    : SSAM (Array BlockParam) := do
  let mut params : Array BlockParam := #[]
  for v in allVars do
    let val ← freshVal v sr
    params := params.push { val, type := none, sr }
    bindVar v val
  return params

/-- Build branch args for a target block, including scope extras from state. -/
def buildBranchArgsCtx (targetBlock : BlockId) (bodyCtx : BodyCtx)
    (sr : SourceRange) : SSAM (Array SSAVal) := do

  let .isTrue h := decideProp (targetBlock.id < bodyCtx.demandArr.size)
    | let _ ← ssaError sr "internal error: Invalid target block index"
      return #[]
  let mut args ← buildBranchArgs (bodyCtx.demandVarsFor targetBlock h) sr
  let extras := (← get).scopeExtras
  for (_, val) in extras do
    args := args.push val
  return args

/-- Build block params for entering a block, including scope extras.
    Updates scopeExtras in state with fresh SSAVals. -/
def buildBlockParamsCtx (blockId : BlockId) (bodyCtx : BodyCtx)
    (sr : SourceRange) : SSAM (Array BlockParam) := do
  -- Set currentBlockId so finishBlock records the correct mapping
  modify fun s => { s with currentBlockId := blockId }
  let .isTrue h := decideProp (blockId.id < bodyCtx.demandArr.size)
    | let _ ← ssaError sr "internal error: Invalid target block index"
      return #[]
  let mut params ← buildBlockParams (bodyCtx.demandVarsFor blockId h) sr
  let extras := (← get).scopeExtras
  let mut newExtras : Array (String × SSAVal) := #[]
  for (name, _) in extras do
    let val ← freshVal name sr
    params := params.push { val, type := none, sr }
    newExtras := newExtras.push (name, val)
  modify fun s => { s with scopeExtras := newExtras }
  return params

/-- Translate a simple statement. Returns true if a terminator was emitted. -/
partial def translateSimpleStmt (s : stmt SourceRange) (bodyCtx : BodyCtx)
    : SSAM Bool := do
  let sr := s.ann
  -- Simple statements don't create expression blocks in practice, so fwd=#[]
  let fwd : Fwd := ∅
  match s with
  | .Assign _ ⟨_, targets⟩ value _ =>
    let instrsBefore := (← get).currentInstrs.size
    let (val, _) ← translateExpr value fwd
    let instrsAfter := (← get).currentInstrs.size
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
      let (val, _) ← translateExpr v fwd
      let instrsAfter := (← get).currentInstrs.size
      if instrsAfter > instrsBefore then
        match target with
        | .Name _ ⟨_, name⟩ _ => renameVal val name
        | _ => pure ()
        match parseTypeAnnotation annotation with
        | some ty => setValType val ty
        | none => pure ()
      assignToTarget target val
    | none => pure ()
    return false

  | .AugAssign _ target op value =>
    let (targetVal, _) ← translateExpr target fwd
    let (rhsVal, _) ← translateExpr value fwd
    let opKind := match op with
      | .Add .. => BinOpKind.add | .Sub .. => .sub | .Mult .. => .mult
      | .Div .. => .div | .FloorDiv .. => .floorDiv | .Mod .. => .mod
      | .Pow .. => .pow | _ => .add
    let baseName := match target with
      | .Name _ ⟨_, name⟩ _ => name | _ => "_tmp"
    let result ← emitInstr baseName none (.binOp opKind targetVal rhsVal) sr
    assignToTarget target result
    return false

  | .Expr _ value =>
    let _ ← translateExpr value fwd
    return false

  | .Return _ ⟨_, value⟩ =>
    let retVal ← match value with
      | some v => let (rv, _) ← translateExpr v fwd; pure (some rv)
      | none => pure none
    finishBlockWithTerm (.ret retVal) sr
    return true

  | .Raise _ ⟨_, exc⟩ _ =>
    match exc with
    | some e =>
      let (excVal, _) ← translateExpr e fwd
      finishBlockWithTerm (.raise excVal) sr
    | none =>
      let _ ← ssaError sr "bare raise not yet supported"
      finishBlockWithTerm .unreachable sr
    return true

  | .Break .. =>
    match bodyCtx.breakTarget with
    | some target =>
      let saved := (← get).scopeExtras
      modify fun s => { s with scopeExtras := s.scopeExtras.shrink bodyCtx.breakExtrasCount }
      let args ← buildBranchArgsCtx target bodyCtx sr
      modify fun s => { s with scopeExtras := saved }
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError sr "break outside loop"
      finishBlockWithTerm .unreachable sr
    return true

  | .Continue .. =>
    match bodyCtx.continueTarget with
    | some target =>
      let saved := (← get).scopeExtras
      modify fun s => { s with scopeExtras := s.scopeExtras.shrink bodyCtx.continueExtrasCount }
      let args ← buildBranchArgsCtx target bodyCtx sr
      modify fun s => { s with scopeExtras := saved }
      finishBlockWithTerm (.branch target args) sr
    | none =>
      let _ ← ssaError sr "continue outside loop"
      finishBlockWithTerm .unreachable sr
    return true

  | .Assert _ test ⟨_, msg⟩ =>
    let (testVal, _) ← translateExpr test fwd
    let msgVal ← match msg with
      | some m => let (mv, _) ← translateExpr m fwd; pure (some mv)
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
      | some ⟨_, m⟩ => m | none => "unknown"
    for a in aliases do
      let qn := QualifiedName.mk' modName a.name
      let localName := a.asname.getD a.name
      bindQualified localName qn
    return false

  | .Delete .. => ssaWarn sr "delete statement ignored"; return false
  | .Global .. | .Nonlocal .. => return false

  | .FunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ =>
    let cfg ← read
    bindQualified name (QualifiedName.mk' cfg.moduleName name)
    return false

  | .ClassDef _ ⟨_, name⟩ _ _ _ _ _ =>
    let cfg ← read
    bindQualified name (QualifiedName.mk' cfg.moduleName name)
    return false

  | _ =>
    let _ ← ssaError sr "Unsupported statement"
    return false
where
  assignToTarget (target : expr SourceRange) (val : SSAVal) : SSAM Unit := do
    match target with
    | .Name _ ⟨_, name⟩ _ => bindVar name val
    | .Tuple _ ⟨_, elts⟩ _ | .List _ ⟨_, elts⟩ _ =>
      for i in [:elts.size] do
        if h : i < elts.size then
          let idx ← emitInstr "_tmp" none (.intLit i) target.ann
          let elem ← emitInstr "_tmp" none (.getItem val idx) target.ann
          assignToTarget elts[i] elem
    | .Attribute _ obj ⟨_, attrName⟩ _ =>
      let (objV, _) ← translateExpr obj ∅
      emitVoidInstr (.setAttr objV attrName val) target.ann
    | .Subscript _ obj key _ =>
      let (objV, _) ← translateExpr obj ∅
      let (keyV, _) ← translateExpr key ∅
      emitVoidInstr (.setItem objV keyV val) target.ann
    | _ => ssaWarn target.ann "Unsupported assignment target"

/-! ## Compound Statement Translation (Direct AST Traversal) -/

/-- Translate an array of statements. Handles simple statements inline and
    decomposes compound statements (if/for/while/try/with) into blocks.
    Returns true if terminated on all paths. -/
partial def translateBody (stmts : Array (stmt SourceRange)) (bodyCtx : BodyCtx)
    : SSAM Bool := do
  let mut terminated := false
  for s in stmts do
    if terminated then break
    if isSimpleStmt s then
      let isTerminator ← translateSimpleStmt s bodyCtx
      if isTerminator then
        terminated := true
    else
      let compoundTerminated ← translateCompound s bodyCtx
      if compoundTerminated then
        terminated := true
  return terminated
where
  /-- Translate a compound statement. -/
  translateCompound (s : stmt SourceRange) (bodyCtx : BodyCtx) : SSAM Bool := do
    let sr := s.ann
    match s with
    | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      let thenBlock ← freshBlockId
      let elseBlock ← freshBlockId
      let joinBlock ← freshBlockId
      let (condVal, _) ← translateExpr test ∅
      let thenArgs ← buildBranchArgsCtx thenBlock bodyCtx sr
      let elseArgs ← buildBranchArgsCtx elseBlock bodyCtx sr
      finishBlock (.condBranch condVal thenBlock thenArgs elseBlock elseArgs) sr #[]
      -- Then
      let savedEnv ← get >>= fun s => pure s.varEnv
      let thenParams ← buildBlockParamsCtx thenBlock bodyCtx sr
      modify fun s => { s with currentParams := thenParams }
      let thenTerminated ← translateBody body bodyCtx
      let mut terminated := false
      if !thenTerminated then
        let joinArgs ← buildBranchArgsCtx joinBlock bodyCtx sr
        finishBlock (.branch joinBlock joinArgs) sr #[]
      else
        startNewBlock #[]
      -- Else
      modify fun s => { s with varEnv := savedEnv }
      let elseParams ← buildBlockParamsCtx elseBlock bodyCtx sr
      modify fun s => { s with currentParams := elseParams }
      let elseTerminated ← translateBody orelse bodyCtx
      if !elseTerminated then
        let joinArgs ← buildBranchArgsCtx joinBlock bodyCtx sr
        finishBlock (.branch joinBlock joinArgs) sr #[]
      else
        if thenTerminated then terminated := true
        startNewBlock #[]
      -- Join
      let joinParams ← buildBlockParamsCtx joinBlock bodyCtx sr
      modify fun s => { s with currentParams := joinParams }
      return terminated

    | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      let iterInitBlock ← freshBlockId
      let headerBlock ← freshBlockId
      let endBlock ← freshBlockId
      -- Evaluate iterable, then push it as a scope extra for iterInitBlock
      let (iterVal, _) ← translateExpr iter ∅
      let savedExtras := (← get).scopeExtras
      modify fun s => { s with scopeExtras := s.scopeExtras.push ("_iterable", iterVal) }
      let initArgs ← buildBranchArgsCtx iterInitBlock bodyCtx sr
      finishBlock (.branch iterInitBlock initArgs) sr #[]
      -- IterInit: call iter() on the iterable param
      let initParams ← buildBlockParamsCtx iterInitBlock bodyCtx sr
      modify fun s => { s with currentParams := initParams }
      -- The iterable is now the last scope extra
      let iterableVal := (← get).scopeExtras.back!.snd
      let iterRef ← emitInstr "_iter" none
        (.qualifiedRef (QualifiedName.mk' "builtins" "iter")) sr
      let iterObj ← emitInstr "_iter" none
        (.call iterRef #[.positional iterableVal]) sr
      -- Replace _iterable with _iter in scope extras for the loop body
      modify fun s => { s with scopeExtras := s.scopeExtras.pop.push ("_iter", iterObj) }
      let headerArgs ← buildBranchArgsCtx headerBlock bodyCtx sr
      finishBlock (.branch headerBlock headerArgs) sr #[]
      -- Header: call next(), assign target
      let headerParams ← buildBlockParamsCtx headerBlock bodyCtx sr
      modify fun s => { s with
        currentParams := headerParams
        currentExcept := some { target := endBlock }
      }
      let iterVar := (← get).scopeExtras.back!.snd
      let nextRef ← emitInstr "_tmp" none
        (.qualifiedRef (QualifiedName.mk' "builtins" "next")) sr
      let nextVal ← emitInstr "_tmp" none (.call nextRef #[.positional iterVar]) sr
      assignTarget target nextVal
      let bodyExtrasCount := (← get).scopeExtras.size
      let loopCtx := { bodyCtx with
        continueTarget := some headerBlock
        breakTarget := some endBlock
        continueExtrasCount := bodyExtrasCount  -- includes _iter
        breakExtrasCount := savedExtras.size     -- without _iter
      }
      let bodyTerminated ← translateBody body loopCtx
      if !bodyTerminated then
        let backArgs ← buildBranchArgsCtx headerBlock bodyCtx sr
        finishBlock (.branch headerBlock backArgs) sr #[]
      else
        startNewBlock #[]
      -- End block: restore scope extras (remove _iter)
      modify fun s => { s with
        currentExcept := none
        scopeExtras := savedExtras
      }
      let endParams ← buildBlockParamsCtx endBlock bodyCtx sr
      modify fun s => { s with currentParams := endParams }
      let orelseTerminated ← translateBody orelse bodyCtx
      return orelseTerminated

    | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
      let testBlock ← freshBlockId
      let bodyBlock ← freshBlockId
      let endBlock ← freshBlockId
      let testArgs ← buildBranchArgsCtx testBlock bodyCtx sr
      finishBlock (.branch testBlock testArgs) sr #[]
      -- Test block
      let testParams ← buildBlockParamsCtx testBlock bodyCtx sr
      modify fun s => { s with currentParams := testParams }
      let (condVal, _) ← translateExpr test ∅
      let thenArgs ← buildBranchArgsCtx bodyBlock bodyCtx sr
      let elseArgs ← buildBranchArgsCtx endBlock bodyCtx sr
      finishBlock (.condBranch condVal bodyBlock thenArgs endBlock elseArgs) sr #[]
      -- Body
      let bodyParams ← buildBlockParamsCtx bodyBlock bodyCtx sr
      modify fun s => { s with currentParams := bodyParams }
      let extrasCount := (← get).scopeExtras.size
      let loopCtx := { bodyCtx with
        continueTarget := some testBlock
        breakTarget := some endBlock
        continueExtrasCount := extrasCount
        breakExtrasCount := extrasCount
      }
      let bodyTerminated ← translateBody body loopCtx
      if !bodyTerminated then
        let backArgs ← buildBranchArgsCtx testBlock bodyCtx sr
        finishBlock (.branch testBlock backArgs) sr #[]
      else
        startNewBlock #[]
      -- End block
      let endParams ← buildBlockParamsCtx endBlock bodyCtx sr
      modify fun s => { s with currentParams := endParams }
      let orelseTerminated ← translateBody orelse bodyCtx
      return orelseTerminated

    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
      -- Allocate handler blocks
      let mut handlerBlocks : Array (BlockId × Option (expr SourceRange) × Option String × Array (stmt SourceRange)) := #[]
      let mut handlerBodyBlocks : Array (Option BlockId) := #[]
      let mut lastHandlerIsTyped := false
      for h in handlers do
        match h with
        | .ExceptHandler _ ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
          let hBlock ← freshBlockId
          let hBodyBlock ← match exType with
            | some _ => some <$> freshBlockId
            | none => pure none
          lastHandlerIsTyped := exType.isSome
          let handlerName := match errname.val with
            | some ⟨_, name⟩ => some name | none => none
          handlerBlocks := handlerBlocks.push (hBlock, exType, handlerName, hBody)
          handlerBodyBlocks := handlerBodyBlocks.push hBodyBlock
      -- Allocate in emission order: finally, reraise, join (join is always last)
      let finallyBlock ← if finalbody.isEmpty then pure none else some <$> freshBlockId
      let reraiseBlock ← if lastHandlerIsTyped || !finalbody.isEmpty
        then some <$> freshBlockId else pure none
      let joinBlock ← freshBlockId
      -- afterTarget: where normal completion (handlers/orelse) goes next
      let afterTarget := match finallyBlock with
        | some fb => fb | none => joinBlock
      -- excTarget: where unhandled exceptions from try body go
      -- With handlers: first handler. Without: finally (if present) or join.
      let excTarget := if h : handlerBlocks.size > 0 then
        handlerBlocks[0].1
      else match finallyBlock with
        | some fb => fb | none => joinBlock
      -- Set except and translate try body
      modify fun s => { s with currentExcept := some { target := excTarget } }
      let bodyTerminated ← translateBody body bodyCtx
      modify fun s => { s with currentExcept := none }
      -- Normal path → orelse → afterTarget
      -- For finally: normal path passes undef("_exc") sentinel
      if !bodyTerminated then
        let orelseTerminated ← translateBody orelse bodyCtx
        if !orelseTerminated then
          let mut args ← buildBranchArgsCtx afterTarget bodyCtx sr
          if finallyBlock.isSome then
            let sentinel ← emitInstr "_exc" none (.undef "_exc") sr
            args := args.push sentinel
          finishBlock (.branch afterTarget args) sr #[]
        else
          startNewBlock #[]
      else
        startNewBlock #[]
      -- Handler blocks
      for i in [:handlerBlocks.size] do
        if h : i < handlerBlocks.size then
          let (hBlockId, typeExpr, handlerName, handlerBody) := handlerBlocks[i]
          let handlerParams ← buildBlockParamsCtx hBlockId bodyCtx sr
          let excVal ← freshVal "_exc" sr
          let excParam : BlockParam := { val := excVal, type := none, sr }
          modify fun s => { s with currentParams := handlerParams.push excParam }
          -- Next handler or (for last handler) unhandled exception path
          let nextBlock := if h2 : i + 1 < handlerBlocks.size then
            handlerBlocks[i + 1].1
          else match reraiseBlock with
            | some rb => match finallyBlock with
              | some fb => fb  -- unhandled → finally (with real exc)
              | none => rb     -- no finally → direct reraise
            | none => afterTarget
          match typeExpr, handlerBodyBlocks[i]! with
          | some texpr, some bodyBid =>
            let (typeVal, _) ← translateExpr texpr ∅
            let isinstRef ← emitInstr "_tmp" none
              (.qualifiedRef (QualifiedName.mk' "builtins" "isinstance")) sr
            let checkVal ← emitInstr "_tmp" none
              (.call isinstRef #[.positional excVal, .positional typeVal]) sr
            let mut bodyArgs ← buildBranchArgsCtx bodyBid bodyCtx sr
            bodyArgs := bodyArgs.push excVal
            let mut nextArgs ← buildBranchArgsCtx nextBlock bodyCtx sr
            nextArgs := nextArgs.push excVal
            finishBlock (.condBranch checkVal bodyBid bodyArgs nextBlock nextArgs) sr #[]
            let bodyParams ← buildBlockParamsCtx bodyBid bodyCtx sr
            let bodyExcVal ← freshVal "_exc" sr
            let bodyExcParam : BlockParam := { val := bodyExcVal, type := none, sr }
            modify fun s => { s with currentParams := bodyParams.push bodyExcParam }
            match handlerName with
            | some name => renameVal bodyExcVal name; bindVar name bodyExcVal
            | none => pure ()
            let handlerTerminated ← translateBody handlerBody bodyCtx
            if !handlerTerminated then
              -- Handled exception → afterTarget with undef sentinel if finally present
              let mut args ← buildBranchArgsCtx afterTarget bodyCtx sr
              if finallyBlock.isSome then
                let sentinel ← emitInstr "_exc" none (.undef "_exc") sr
                args := args.push sentinel
              finishBlock (.branch afterTarget args) sr #[]
            else startNewBlock #[]
          | _, _ =>
            match handlerName with
            | some name => bindVar name excVal
            | none => pure ()
            let handlerTerminated ← translateBody handlerBody bodyCtx
            if !handlerTerminated then
              -- Handled exception → afterTarget with undef sentinel if finally present
              let mut args ← buildBranchArgsCtx afterTarget bodyCtx sr
              if finallyBlock.isSome then
                let sentinel ← emitInstr "_exc" none (.undef "_exc") sr
                args := args.push sentinel
              finishBlock (.branch afterTarget args) sr #[]
            else startNewBlock #[]
      -- Reraise block (without finally: direct raise; with finally: placed after finally)
      if finallyBlock.isNone then
        match reraiseBlock with
        | some rb =>
          let reraiseParams ← buildBlockParamsCtx rb bodyCtx sr
          let reraiseExcVal ← freshVal "_exc" sr
          let reraiseExcParam : BlockParam := { val := reraiseExcVal, type := none, sr }
          modify fun s => { s with currentParams := reraiseParams.push reraiseExcParam }
          finishBlock (.raise reraiseExcVal) sr #[]
        | none => pure ()
      -- Finally block: receives demand vars + _exc param
      -- After body: condBranch _exc → reraiseBlock (propagate) or joinBlock (continue)
      match finallyBlock with
      | some fb =>
        let finallyParams ← buildBlockParamsCtx fb bodyCtx sr
        let finallyExcVal ← freshVal "_exc" sr
        let finallyExcParam : BlockParam := { val := finallyExcVal, type := none, sr }
        modify fun s => { s with currentParams := finallyParams.push finallyExcParam }
        let finallyTerminated ← translateBody finalbody bodyCtx
        if !finallyTerminated then
          match reraiseBlock with
          | some rb =>
            let mut reraiseArgs ← buildBranchArgsCtx rb bodyCtx sr
            reraiseArgs := reraiseArgs.push finallyExcVal
            let joinArgs ← buildBranchArgsCtx joinBlock bodyCtx sr
            finishBlock (.condBranch finallyExcVal rb reraiseArgs joinBlock joinArgs) sr #[]
            -- Reraise block after finally
            let reraiseParams ← buildBlockParamsCtx rb bodyCtx sr
            let reraiseExcVal2 ← freshVal "_exc" sr
            let reraiseExcParam2 : BlockParam := { val := reraiseExcVal2, type := none, sr }
            modify fun s => { s with currentParams := reraiseParams.push reraiseExcParam2 }
            finishBlock (.raise reraiseExcVal2) sr #[]
          | none =>
            let joinArgs ← buildBranchArgsCtx joinBlock bodyCtx sr
            finishBlock (.branch joinBlock joinArgs) sr #[]
        else startNewBlock #[]
      | none => pure ()
      -- Join
      let joinParams ← buildBlockParamsCtx joinBlock bodyCtx sr
      modify fun s => { s with currentParams := joinParams }
      return false

    | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
      if h : items.size > 0 then
        match items[0] with
        | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
          let asName := match optVars with
            | some (.Name _ ⟨_, name⟩ _) => some name | _ => none
          let enterBlock ← freshBlockId
          let excExitBlock ← freshBlockId
          let reraiseBlock ← freshBlockId
          let normalExitBlock ← freshBlockId
          if items.size > 1 then
            ssaWarn sr "Multi-item with statement — only first item decomposed in v1"
          -- Evaluate context, call __enter__
          let (mgrVal, _) ← translateExpr ctxExpr ∅
          let enterVal ← emitInstr "_tmp" none (.attr mgrVal "__enter__") sr
          let ctxVal ← emitInstr "_tmp" none (.call enterVal #[]) sr
          match asName with
          | some name => renameVal ctxVal name; bindVar name ctxVal
          | none => pure ()
          -- Push _mgr as scope extra for the with body
          let savedExtras := (← get).scopeExtras
          modify fun s => { s with scopeExtras := s.scopeExtras.push ("_mgr", mgrVal) }
          let enterArgs ← buildBranchArgsCtx enterBlock bodyCtx sr
          finishBlock (.branch enterBlock enterArgs) sr #[]
          -- Enter block: body with except
          let enterParams ← buildBlockParamsCtx enterBlock bodyCtx sr
          modify fun s => { s with
            currentParams := enterParams
            currentExcept := some { target := excExitBlock }
          }
          let bodyTerminated ← translateBody body bodyCtx
          modify fun s => { s with currentExcept := none }
          -- Normal path: __exit__(None, None, None)
          if !bodyTerminated then
            let mgrRef := (← get).scopeExtras.back!.snd
            let exitRef ← emitInstr "_tmp" none (.attr mgrRef "__exit__") sr
            let noneVal ← emitInstr "_tmp" none .noneLit sr
            let _ ← emitInstr "_tmp" none
              (.call exitRef #[.positional noneVal, .positional noneVal, .positional noneVal]) sr
            -- Restore scopeExtras before branching to normalExitBlock (outside with scope)
            let withExtras := (← get).scopeExtras
            modify fun s => { s with scopeExtras := savedExtras }
            let normalArgs ← buildBranchArgsCtx normalExitBlock bodyCtx sr
            modify fun s => { s with scopeExtras := withExtras }
            finishBlock (.branch normalExitBlock normalArgs) sr #[]
          else
            startNewBlock #[]
          -- Exception exit: __exit__(exc, exc, exc), check return
          let excParams ← buildBlockParamsCtx excExitBlock bodyCtx sr
          let excVal ← freshVal "_exc" sr
          let excParam : BlockParam := { val := excVal, type := none, sr }
          modify fun s => { s with currentParams := excParams.push excParam }
          let excMgrRef := (← get).scopeExtras.back!.snd
          let excExitRef ← emitInstr "_tmp" none (.attr excMgrRef "__exit__") sr
          let exitResult ← emitInstr "_tmp" none
            (.call excExitRef #[.positional excVal, .positional excVal, .positional excVal]) sr
          -- Build suppressArgs with savedExtras (normalExitBlock is outside with scope)
          let withExtras2 := (← get).scopeExtras
          modify fun s => { s with scopeExtras := savedExtras }
          let mut suppressArgs ← buildBranchArgsCtx normalExitBlock bodyCtx sr
          modify fun s => { s with scopeExtras := withExtras2 }
          let mut reraiseArgs ← buildBranchArgsCtx reraiseBlock bodyCtx sr
          reraiseArgs := reraiseArgs.push excVal
          finishBlock (.condBranch exitResult
            normalExitBlock suppressArgs
            reraiseBlock reraiseArgs) sr #[]
          -- Reraise block
          let reraiseParams ← buildBlockParamsCtx reraiseBlock bodyCtx sr
          let reraiseExcVal ← freshVal "_exc" sr
          let reraiseExcParam : BlockParam := { val := reraiseExcVal, type := none, sr }
          modify fun s => { s with currentParams := reraiseParams.push reraiseExcParam }
          finishBlock (.raise reraiseExcVal) sr #[]
          -- Normal exit: restore scope extras
          modify fun s => { s with scopeExtras := savedExtras }
          let normalParams ← buildBlockParamsCtx normalExitBlock bodyCtx sr
          modify fun s => { s with currentParams := normalParams }
          return false
      else
        ssaWarn sr "Empty with statement"
        return false

    | _ =>
      let name := match s with
        | .AsyncFor .. => "AsyncFor" | .AsyncWith .. => "AsyncWith"
        | .TryStar .. => "TryStar" | .Match .. => "Match" | _ => "unknown"
      ssaWarn sr s!"Unsupported compound statement: {name}"
      return false

  /-- Assign to a target expression from a value (for loop targets). -/
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

/-- Remap a BlockId using the freshBlockId → emission-order mapping. -/
private def remapBlockId (map : Array BlockId) (bid : BlockId) : BlockId :=
  if h : bid.id < map.size then map[bid.id] else bid

/-- Remap all BlockId references in a terminator. -/
private def remapTerminator (map : Array BlockId) (term : Terminator) : Terminator :=
  match term with
  | .branch target args => .branch (remapBlockId map target) args
  | .condBranch cond t tArgs f fArgs =>
    .condBranch cond (remapBlockId map t) tArgs (remapBlockId map f) fArgs
  | .ret v => .ret v
  | .raise exc => .raise exc
  | .unreachable => .unreachable

private def translateFunc (info : FuncInfo) (config : SSAConfig)
    (moduleBindings : Std.HashMap String QualifiedName := {})
    : Func × Array (String × SourceRange) :=
  let initState : SSAState := {
    varEnv := moduleBindings.fold (init := {}) fun env name qn =>
      env.insert name (.qualified qn)
  }
  let action : SSAM Unit := do
    if info.isAsync then
      ssaWarn info.sr s!"unsupported AsyncFunctionDef '{info.name}'"
    for (pname, typeAnnot) in info.params do
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
    let da := Blockify.demandAnalysis info.body info.globals
    modify fun s => { s with demandArr := da }
    startFirstBlock #[]
    let bodyCtx : BodyCtx := { demandArr := da }
    let bodyTerminated ← translateBody info.body bodyCtx
    if !bodyTerminated then
      let s ← get
      let emitId := s.blocks.size
      let blockIdMap := recordBlockIdMap s.blockIdMap s.currentBlockId.id emitId
      let block : Block := {
        id := ⟨emitId⟩
        params := s.currentParams
        instrs := s.currentInstrs
        term := .ret none
        termSr := SourceRange.none
        except := s.currentExcept
      }
      set { s with blocks := s.blocks.push block, blockIdMap, currentInstrs := #[] }
  let ((), finalState) := action config |>.run initState
  -- Remap all freshBlockId references in terminators and except targets to emission order
  let map := finalState.blockIdMap
  let remappedBlocks := finalState.blocks.map fun block =>
    { block with
      term := remapTerminator map block.term
      except := block.except.map fun et => { target := remapBlockId map et.target } }
  let func : Func := {
    name := info.name
    params := finalState.funcParams
    retType := none
    blocks := remappedBlocks
    names := finalState.names
    decorators := #[]
    sr := info.sr
  }
  (func, finalState.warnings)

/-- Result of translating a module to SSA. -/
public structure TranslateResult where
  module   : Module
  warnings : Array (String × SourceRange)
deriving Inhabited

/-- Translate a module's statements into an SSA Module (v2 with strict SSA). -/
public def translateModule (moduleName : String)
    (stmts : Array (stmt SourceRange)) : TranslateResult :=
  let config : SSAConfig := {
    prelude := pythonPrelude
    moduleName
  }
  let results := scanModule stmts
  let moduleBindings := results.foldl (init := {}) fun bindings r =>
    if r.name == "@module_init" then bindings
    else if r.name.any (· == '.') then
      let className := r.name.takeWhile (· != '.') |>.toString
      bindings.insert className (QualifiedName.mk' moduleName className)
    else
      bindings.insert r.name (QualifiedName.mk' moduleName r.name)
  let translated := results.map (translateFunc · config moduleBindings)
  let funcs := translated.map (·.1)
  let warnings := translated.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
  { module := { name := moduleName, funcs }, warnings }

end Strata.Python.PythonToSSA

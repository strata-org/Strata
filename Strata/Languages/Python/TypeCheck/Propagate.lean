/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.TypeCheck.Transfer
public import Strata.Languages.Python.TypeCheck.SpecEnv
import Strata.Languages.Python.Specs

/-!
# Forward Type Propagation over SSA IR

Walks each function's blocks in topological order, computing an `AbstractType`
for every SSA value via instruction-level transfer functions.
-/

public section
namespace Strata.Python.TypeCheck

open Strata.Python.SSA
open Strata.Python.TypeCheck

structure Diagnostic where
  sr   : SourceRange
  kind : String
  msg  : String
deriving Inhabited

instance : ToString Diagnostic where
  toString d := s!"{d.kind}: {d.msg}"

/-- Per-function analysis state: types for every SSA value. -/
structure TypeState where
  types : Array (Option AbstractType)
  diags : Array Diagnostic
deriving Inhabited

namespace TypeState

def getType (s : TypeState) (v : SSAVal) : AbstractType :=
  if h : v.id < s.types.size then
    s.types[v.id].getD (.any (.unknown s!"unresolved %{v.id}"))
  else
    .any (.unknown s!"out of range %{v.id}")

def setType (s : TypeState) (v : SSAVal) (t : AbstractType) : TypeState :=
  if h : v.id < s.types.size then
    { s with types := s.types.set v.id (some t) }
  else s

def addDiag (s : TypeState) (d : Diagnostic) : TypeState :=
  { s with diags := s.diags.push d }

def init (numVals : Nat) : TypeState :=
  { types := Array.replicate numVals none, diags := #[] }

end TypeState

/-- Result of type checking a module. -/
structure TypeCheckResult where
  funcResults : Array (String × TypeState)
  diagnostics : Array Diagnostic
deriving Inhabited

/-- Configuration for the type check pipeline. -/
structure TypeCheckConfig where
  moduleName : String := ""
  transferTable : TransferTable := defaultTransferTable
  specDir : Option System.FilePath := none

/-- Mutable state for the type check pipeline. -/
structure TypeCheckState where
  funcResults : Array (String × TypeState) := #[]
  diagnostics : Array Diagnostic := #[]
  specEnv : SpecEnv := {}
deriving Inhabited

/-- The type check monad: supports IO (for loading specs) and mutable state. -/
abbrev TypeCheckM := ReaderT TypeCheckConfig (StateT TypeCheckState BaseIO)

namespace TypeCheckM

def run (cfg : TypeCheckConfig) (act : TypeCheckM α) : BaseIO (α × TypeCheckState) :=
  (act cfg).run {}

def addFuncResult (name : String) (state : TypeState) : TypeCheckM Unit :=
  modify fun s => { s with
    funcResults := s.funcResults.push (name, state)
    diagnostics := s.diagnostics ++ state.diags
  }

end TypeCheckM

private def cacheSpec (modName : String) (ms : Option ModuleSpec) : TypeCheckM Unit :=
  modify fun s => { s with specEnv := s.specEnv.insert modName ms }

/-- Load a module's spec on demand, with caching. -/
private def loadModuleSpec (modName : String) : TypeCheckM (Option ModuleSpec) := do
  if let some cached := (← get).specEnv.get? modName then return cached
  let some specDir := (← read).specDir
    | cacheSpec modName none; return none
  let some mod := Strata.Python.Specs.ModuleName.ofString modName |>.toOption
    | cacheSpec modName none; return none
  let path ← Strata.Python.Specs.ModuleName.specIonPath mod specDir
  match path with
  | none => cacheSpec modName none; return none
  | some p =>
    match ← (Strata.Python.Specs.readDDM p |>.toBaseIO : BaseIO _) with
    | .ok sigs =>
      let ms := ModuleSpec.ofSignatures sigs
      cacheSpec modName (some ms)
      return some ms
    | .error _ =>
      cacheSpec modName none
      return none

/-- Resolve a qualified name to a module export. -/
private def resolveQualifiedRef (_sr : SourceRange) (qn : QualifiedName)
    : TypeCheckM AbstractType := do
  let modName := toString qn.module
  match ← loadModuleSpec modName with
  | none => return .any (.unknown s!"unknown module {modName}")
  | some ms =>
    if qn.name == modName then
      return .instance_ modName
    match ms.exports.get? qn.name with
    | some (.classDef _) => return .callable s!"{modName}.{qn.name}"
    | some (.functionDecl _) => return .callable s!"{modName}.{qn.name}"
    | some (.typeDef st) => return specTypeToAbstract st
    | some (.externType source) =>
      return .instance_ s!"{source.pythonModule}.{source.name}"
    | none => return .any (.unknown s!"{qn.name} not found in {modName}")

/-- Look up an attribute in a module's exports. -/
private def resolveModuleAttr (modName name : String) : TypeCheckM AbstractType := do
  match ← loadModuleSpec modName with
  | none => return .any (.unknown s!"attr {name} on {modName}")
  | some ms =>
    match ms.exports.get? name with
    | some (.classDef _) => return .callable s!"{modName}.{name}"
    | some (.functionDecl _) => return .callable s!"{modName}.{name}"
    | some (.typeDef st) => return specTypeToAbstract st
    | some (.externType source) =>
      return .instance_ s!"{source.pythonModule}.{source.name}"
    | none => return .any (.unknown s!"{name} not found in {modName}")

/-- Look up an attribute on a class instance. -/
private def resolveClassAttr (className name : String) : TypeCheckM AbstractType := do
  let parts := className.splitOn "."
  let modParts := parts.dropLast
  let typeName := parts.getLast!
  let modName := ".".intercalate modParts
  if modName.isEmpty then return .any (.unknown s!"attr {name} on {className}")
  match ← loadModuleSpec modName with
  | none => return .any (.unknown s!"attr {name} on {className}")
  | some ms =>
    match ms.exports.get? typeName with
    | some (.classDef cls) =>
      if cls.methods.any (·.name == name) then
        return .callable s!"{className}.{name}"
      if let some field := cls.fields.find? (·.name == name) then
        return specTypeToAbstract field.type
      if cls.exhaustive then
        return .any (.unknown s!"unknown method {name} on {className}")
      return .any (.unknown s!"attr {name} on {className}")
    | _ => return .any (.unknown s!"attr {name} on {className}")

/-- Resolve an attribute access on a typed value. -/
private def resolveAttr (_sr : SourceRange) (className name : String)
    : TypeCheckM AbstractType := do
  if let some _ ← loadModuleSpec className then
    resolveModuleAttr className name
  else
    resolveClassAttr className name

/-- Resolve a call to a known callable. -/
private def resolveCall (_sr : SourceRange) (sigName : String) (_args : Array CallArg)
    (_s : TypeState) : TypeCheckM AbstractType := do
  let parts := sigName.splitOn "."
  if parts.length < 2 then return .any (.unknown s!"call on {sigName}")
  let funcName := parts.getLast!
  let ownerParts := parts.dropLast
  let ownerName := ownerParts.getLast!
  let modParts := ownerParts.dropLast
  let modName := ".".intercalate modParts
  if modName.isEmpty then
    let modName := ".".intercalate ownerParts
    match ← loadModuleSpec modName with
    | none => return .any (.unknown s!"call on {sigName}")
    | some ms =>
      match ms.exports.get? funcName with
      | some (.functionDecl decl) => return specTypeToAbstract decl.returnType
      | some (.classDef _) => return .instance_ sigName
      | _ => return .any (.unknown s!"call on {sigName}")
  else
    match ← loadModuleSpec modName with
    | none => return .any (.unknown s!"call on {sigName}")
    | some ms =>
      match ms.exports.get? ownerName with
      | some (.classDef cls) =>
        if let some method := cls.methods.find? (·.name == funcName) then
          return specTypeToAbstract method.returnType
        return .any (.unknown s!"call on {sigName}")
      | some (.functionDecl decl) => return specTypeToAbstract decl.returnType
      | _ => return .any (.unknown s!"call on {sigName}")

/-- Process a single instruction and return its result type. -/
private def instrType (table : TransferTable) (s : TypeState) (sr : SourceRange)
    (instr : Instruction) : TypeCheckM AbstractType := do
  match instr with
  | .intLit v => return .literal (.int v)
  | .floatLit v => return .literal (.float v)
  | .strLit v => return .literal (.str v)
  | .boolLit v => return .literal (.bool v)
  | .noneLit => return .literal .none
  | .bytesLit _ => return .bytes
  | .undef name => return .any (.uninit name)
  | .isDefined _ => return .bool
  | .qualifiedRef qn => resolveQualifiedRef sr qn
  | .attr obj name =>
    let objType := s.getType obj
    match objType with
    | .any blame => return .any blame
    | .callable className | .instance_ className => resolveAttr sr className name
    | _ => return .any (.unknown s!"attr {name} on {objType}")
  | .call func args =>
    let funcType := s.getType func
    match funcType with
    | .any blame => return .any blame
    | .callable sigName => resolveCall sr sigName args s
    | _ => return .any (.unknown s!"call on {funcType}")
  | .binOp op lhs rhs =>
    return table.lookupBinOp op (s.getType lhs) (s.getType rhs)
      |>.getD (.any (.unknown s!"unsupported binOp"))
  | .unaryOp op operand =>
    return table.lookupUnaryOp op (s.getType operand)
      |>.getD (.any (.unknown s!"unsupported unaryOp"))
  | .compareOp op lhs rhs =>
    return table.lookupCmpOp op (s.getType lhs) (s.getType rhs)
      |>.getD (.any (.unknown s!"unsupported compareOp"))
  | .mkList elems =>
    if elems.isEmpty then return .instance_ "list"
    else return .instance_ "list"
  | .mkDict _ _ => return .instance_ "dict"
  | .mkTuple _ => return .instance_ "tuple"
  | .getItem obj _ =>
    let objType := s.getType obj
    match objType with
    | .any blame => return .any blame
    | _ => return .any (.unknown s!"getItem on {objType}")
  | .setItem obj _ _ =>
    return s.getType obj
  | .getSlice obj _ _ _ =>
    return s.getType obj
  | .fmtValue _ => return .str
  | .strConcat _ => return .str
  | .assert_ _ _ => return .none
  | .setAttr obj _ _ => return s.getType obj
  | .unsupported n => return .any (.unsupported n)

/-- Compute predecessor map: for each block, which blocks branch to it
    and what arguments they pass. -/
private structure BranchEdge where
  args : Array SSAVal
deriving Inhabited

private def buildPredecessors (blocks : Array Block) :
    Std.HashMap Nat (Array (Nat × BranchEdge)) := Id.run do
  let mut preds : Std.HashMap Nat (Array (Nat × BranchEdge)) := {}
  for b in blocks do
    match b.term with
    | .branch target args =>
      let entry := preds.getD target.id #[]
      preds := preds.insert target.id (entry.push (b.id.id, ⟨args⟩))
    | .condBranch _ thenB thenArgs elseB elseArgs =>
      let tEntry := preds.getD thenB.id #[]
      preds := preds.insert thenB.id (tEntry.push (b.id.id, ⟨thenArgs⟩))
      let eEntry := preds.getD elseB.id #[]
      preds := preds.insert elseB.id (eEntry.push (b.id.id, ⟨elseArgs⟩))
    | _ => pure ()
  return preds

/-- Build a map from block ID to array index. -/
private def mkBlockIndex (blocks : Array Block) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  for i in [:blocks.size] do
    if h : i < blocks.size then
      m := m.insert blocks[i].id.id i
  return m

/-- Compute a topological ordering of blocks. Simple BFS from bb0. -/
private def topoOrder (blocks : Array Block) : Array Nat := Id.run do
  let blockMap := mkBlockIndex blocks
  let mut visited : Std.HashSet Nat := {}
  let mut order : Array Nat := #[]
  let mut worklist : Array Nat := #[0]
  let mut wi := 0
  while h : wi < worklist.size do
    let id := worklist[wi]
    wi := wi + 1
    if visited.contains id then continue
    visited := visited.insert id
    order := order.push id
    if let some idx := blockMap.get? id then
      if h2 : idx < blocks.size then
        let b := blocks[idx]
        match b.term with
        | .branch target _ => worklist := worklist.push target.id
        | .condBranch _ thenB _ elseB _ =>
          worklist := worklist.push thenB.id
          worklist := worklist.push elseB.id
        | _ => pure ()
  return order

/-- Run forward type propagation on a single function. -/
def propagateFunc (table : TransferTable) (func : Func) : TypeCheckM TypeState := do
  let numVals := func.names.size
  let mut s := TypeState.init numVals
  for p in func.params do
    s := s.setType p.val (.any (.unknown s!"param {p.name}"))
  let preds := buildPredecessors func.blocks
  let blockOrder := topoOrder func.blocks
  let blockMap := mkBlockIndex func.blocks
  for blockId in blockOrder do
    let some blockIdx := blockMap.get? blockId | continue
    if h : blockIdx < func.blocks.size then
      let block := func.blocks[blockIdx]
      if let some predEdges := preds.get? blockId then
        for i in [:block.params.size] do
          if hi : i < block.params.size then
            let param := block.params[i]
            let joinedType := predEdges.foldl (init := AbstractType.bottom)
              fun acc (_, edge) =>
                if hi2 : i < edge.args.size then
                  AbstractType.join acc (s.getType edge.args[i])
                else acc
            s := s.setType param.val joinedType
      for ni in block.instrs do
        let resultType ← instrType table s ni.sr ni.instr
        if let some v := ni.result then
          s := s.setType v resultType
  return s

/-- Run type checking on an entire module. -/
def typeCheckModule (mod : Module) : TypeCheckM TypeCheckResult := do
  let table := (← read).transferTable
  for func in mod.funcs do
    let state ← propagateFunc table func
    TypeCheckM.addFuncResult func.name state
  let s ← get
  return { funcResults := s.funcResults, diagnostics := s.diagnostics }

end Strata.Python.TypeCheck
end -- public section

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.TypeCheck.AbstractType
public import Strata.Languages.Python.SSA.IR

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

/-- Try constant-folding a binary operation on two literal values. -/
private def foldBinOp (op : BinOpKind) (lv rv : LitValue) : Option AbstractType :=
  match op, lv, rv with
  | .add,  .int a,  .int b  => some (.literal (.int (a + b)))
  | .sub,  .int a,  .int b  => some (.literal (.int (a - b)))
  | .mult, .int a,  .int b  => some (.literal (.int (a * b)))
  | .add,  .str a,  .str b  => some (.literal (.str (a ++ b)))
  | .mult, .str s,  .int n  =>
    if n ≥ 0 then some (.literal (.str ("".intercalate (List.replicate n.toNat s))))
    else some (.literal (.str ""))
  | .mult, .int n,  .str s  =>
    if n ≥ 0 then some (.literal (.str ("".intercalate (List.replicate n.toNat s))))
    else some (.literal (.str ""))
  | _, _, _ => none

/-- Transfer function for binary operators. -/
private def binOpType (op : BinOpKind) (lhs rhs : AbstractType) : AbstractType :=
  match lhs, rhs with
  | .literal lv, .literal rv =>
    if let some result := foldBinOp op lv rv then
      result
    else
      binOpTypeWidened op lhs.widenLiteral rhs.widenLiteral
  | _, _ => binOpTypeWidened op lhs.widenLiteral rhs.widenLiteral
where
  binOpTypeWidened (op : BinOpKind) (l r : AbstractType) : AbstractType :=
    match l, r with
    | .any blame, _ | _, .any blame => .any blame
    | .int, .int =>
      match op with
      | .div => .float
      | _ => .int
    | .float, _ | _, .float => .float
    | .str, .str =>
      match op with
      | .add | .mult => .str
      | _ => .any (.unknown "unsupported op on str")
    | .str, .int | .int, .str =>
      match op with
      | .mult => .str
      | _ => .any (.unknown "unsupported op on str*int")
    | _, _ => .any (.unknown "binOp on unknown types")

/-- Transfer function for unary operators. -/
private def unaryOpType (op : UnaryOpKind) (operand : AbstractType) : AbstractType :=
  match op with
  | .not_ =>
    match operand with
    | .literal (.bool b) => .literal (.bool !b)
    | _ => .bool
  | .uSub =>
    match operand with
    | .literal (.int v) => .literal (.int (-v))
    | _ =>
      match operand.widenLiteral with
      | .int => .int
      | .float => .float
      | .any blame => .any blame
      | _ => .any (.unknown "unary minus on non-numeric")

/-- Transfer function for comparison operators. -/
private def compareOpType (_op : CmpOpKind) (_lhs _rhs : AbstractType) : AbstractType :=
  .bool

/-- Process a single instruction and return its result type. -/
private def instrType (s : TypeState) (instr : Instruction) : AbstractType :=
  match instr with
  | .intLit v => .literal (.int v)
  | .floatLit v => .literal (.float v)
  | .strLit v => .literal (.str v)
  | .boolLit v => .literal (.bool v)
  | .noneLit => .literal .none
  | .bytesLit _ => .bytes
  | .undef name => .any (.uninit name)
  | .isDefined _ => .bool
  | .qualifiedRef _qn => .any (.unknown s!"qualifiedRef {_qn}")
  | .attr obj name =>
    let objType := s.getType obj
    match objType with
    | .any blame => .any blame
    | _ => .any (.unknown s!"attr {name} on {objType}")
  | .call func _args =>
    let funcType := s.getType func
    match funcType with
    | .any blame => .any blame
    | _ => .any (.unknown s!"call on {funcType}")
  | .binOp op lhs rhs => binOpType op (s.getType lhs) (s.getType rhs)
  | .unaryOp op operand => unaryOpType op (s.getType operand)
  | .compareOp op lhs rhs => compareOpType op (s.getType lhs) (s.getType rhs)
  | .mkList elems =>
    if elems.isEmpty then .instance_ "list"
    else .instance_ "list"
  | .mkDict _ _ => .instance_ "dict"
  | .mkTuple _ => .instance_ "tuple"
  | .getItem obj _ =>
    let objType := s.getType obj
    match objType with
    | .any blame => .any blame
    | _ => .any (.unknown s!"getItem on {objType}")
  | .setItem obj _ _ =>
    s.getType obj
  | .getSlice obj _ _ _ =>
    s.getType obj
  | .fmtValue _ => .str
  | .strConcat _ => .str
  | .assert_ _ _ => .none
  | .setAttr obj _ _ => s.getType obj
  | .unsupported n => .any (.unsupported n)

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
def propagateFunc (func : Func) : TypeState := Id.run do
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
        let resultType := instrType s ni.instr
        if let some v := ni.result then
          s := s.setType v resultType
  return s

/-- Result of type checking a module. -/
structure TypeCheckResult where
  funcResults : Array (String × TypeState)
  diagnostics : Array Diagnostic
deriving Inhabited

/-- Configuration for the type check pipeline. -/
structure TypeCheckConfig where
  moduleName : String := ""
deriving Inhabited

/-- Mutable state for the type check pipeline. -/
structure TypeCheckState where
  funcResults : Array (String × TypeState) := #[]
  diagnostics : Array Diagnostic := #[]
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

/-- Run type checking on an entire module. -/
def typeCheckModule (mod : Module) : TypeCheckM TypeCheckResult := do
  for func in mod.funcs do
    let state := propagateFunc func
    TypeCheckM.addFuncResult func.name state
  let s ← get
  return { funcResults := s.funcResults, diagnostics := s.diagnostics }

end Strata.Python.TypeCheck
end -- public section

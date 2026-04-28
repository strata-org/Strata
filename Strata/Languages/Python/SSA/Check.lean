/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.SSA.IR

/-!
# SSA Well-Formedness Checker

Runtime validation of structural invariants on the PythonSSA IR.
Returns an array of error strings — empty means well-formed.

Checks implemented:
1. Block ID uniqueness
2. Block ID references valid (terminators + except targets)
3. SSAVal uniqueness (defined exactly once)
4. Names array covers all SSAVal IDs
5. Branch argument count matches target block parameter count
6. exceptArgs consistency (present iff block has except target)
7. All SSAVal uses defined somewhere in function
8. mkDict keys/vals same length
9. Entry block exists
-/

namespace Strata.Python.SSACheck

open Strata.Python.SSA

/-! ## Helpers -/

/-- Extract all SSAVal references used by an instruction. -/
private def instrUsedVals (instr : Instruction) : Array SSAVal :=
  match instr with
  | .undef _ | .intLit _ | .floatLit _ | .strLit _ | .boolLit _
  | .noneLit | .bytesLit _ | .qualifiedRef _ | .unsupported _ => #[]
  | .isDefined val | .unaryOp _ val | .fmtValue val => #[val]
  | .attr obj _ => #[obj]
  | .setAttr obj _ val | .getItem obj val | .compareOp _ obj val
  | .binOp _ obj val => #[obj, val]
  | .setItem obj key val => #[obj, key, val]
  | .mkDict keys vals => keys ++ vals
  | .mkList elems | .mkTuple elems | .strConcat elems => elems
  | .call func args =>
    let base := #[func]
    args.foldl (init := base) fun acc arg =>
      match arg with
      | .positional v | .keyword _ v | .starArgs v | .starKwargs v => acc.push v
  | .getSlice obj lo hi step =>
    let acc := #[obj]
    let acc := match lo with | some v => acc.push v | none => acc
    let acc := match hi with | some v => acc.push v | none => acc
    match step with | some v => acc.push v | none => acc
  | .assert_ cond msg =>
    match msg with | some m => #[cond, m] | none => #[cond]

/-- Extract all SSAVal references used by a terminator. -/
private def termUsedVals (term : Terminator) : Array SSAVal :=
  match term with
  | .branch _ args => args
  | .condBranch cond _ thenArgs _ elseArgs => #[cond] ++ thenArgs ++ elseArgs
  | .ret (some v) => #[v]
  | .ret none | .unreachable => #[]
  | .raise exc => #[exc]

/-- Extract all BlockId references from a terminator. -/
private def termBlockIds (term : Terminator) : Array BlockId :=
  match term with
  | .branch target _ => #[target]
  | .condBranch _ thenB _ elseB _ => #[thenB, elseB]
  | .ret _ | .raise _ | .unreachable => #[]

/-- Extract all SSAVal references used in exceptArgs. -/
private def exceptArgUsedVals (args : Array ExceptArgVal) : Array SSAVal :=
  args.foldl (init := #[]) fun acc arg =>
    match arg with
    | .val v => acc.push v
    | .exc => acc

/-! ## Per-Function Checker -/

/-- Check all well-formedness invariants for a single function.
    Returns an array of error messages (empty = well-formed). -/
public def checkFunc (f : Func) : Array String := Id.run do
  let mut errors : Array String := #[]

  -- Build lookup tables
  let mut blockMap : Std.HashMap Nat Block := {}
  let mut definedVals : Std.HashSet Nat := {}

  -- Check 1: Block ID uniqueness
  let mut seenBlockIds : Std.HashSet Nat := {}
  for block in f.blocks do
    if seenBlockIds.contains block.id.id then
      errors := errors.push s!"bb{block.id.id}: duplicate block ID"
    seenBlockIds := seenBlockIds.insert block.id.id
    blockMap := blockMap.insert block.id.id block

  -- Collect all defined SSAVals (func params + block params + instruction results)
  -- Check 3: SSAVal uniqueness
  for fp in f.params do
    definedVals := definedVals.insert fp.val.id
  for block in f.blocks do
    for param in block.params do
      if definedVals.contains param.val.id then
        errors := errors.push s!"bb{block.id.id}: %{param.val.id} defined multiple times"
      definedVals := definedVals.insert param.val.id
    for ni in block.instrs do
      match ni.result with
      | some val =>
        if definedVals.contains val.id then
          errors := errors.push s!"bb{block.id.id}: %{val.id} defined multiple times"
        definedVals := definedVals.insert val.id
      | none => pure ()

  -- Check 2: Block ID references valid (terminators + except targets)
  for block in f.blocks do
    for bid in termBlockIds block.term do
      if !blockMap.contains bid.id then
        errors := errors.push s!"bb{block.id.id}: terminator references bb{bid.id} which does not exist"
    match block.except with
    | some et =>
      if !blockMap.contains et.target.id then
        errors := errors.push s!"bb{block.id.id}: except target bb{et.target.id} does not exist"
    | none => pure ()

  -- Check 4: Names array coverage
  for block in f.blocks do
    for param in block.params do
      if param.val.id >= f.names.size then
        errors := errors.push s!"bb{block.id.id}: param %{param.val.id} exceeds names array (size {f.names.size})"
    for ni in block.instrs do
      match ni.result with
      | some val =>
        if val.id >= f.names.size then
          errors := errors.push s!"bb{block.id.id}: result %{val.id} exceeds names array (size {f.names.size})"
      | none => pure ()

  -- Check 5: Branch argument count matches target block parameter count
  for block in f.blocks do
    match block.term with
    | .branch target args =>
      match blockMap[target.id]? with
      | some tgtBlock =>
        if args.size != tgtBlock.params.size then
          errors := errors.push
            s!"bb{block.id.id}: branch to bb{target.id} passes {args.size} args but target has {tgtBlock.params.size} params"
      | none => pure ()  -- caught by check 2
    | .condBranch _ thenB thenArgs elseB elseArgs =>
      match blockMap[thenB.id]? with
      | some tgtBlock =>
        if thenArgs.size != tgtBlock.params.size then
          errors := errors.push
            s!"bb{block.id.id}: condBranch then-arm to bb{thenB.id} passes {thenArgs.size} args but target has {tgtBlock.params.size} params"
      | none => pure ()
      match blockMap[elseB.id]? with
      | some tgtBlock =>
        if elseArgs.size != tgtBlock.params.size then
          errors := errors.push
            s!"bb{block.id.id}: condBranch else-arm to bb{elseB.id} passes {elseArgs.size} args but target has {tgtBlock.params.size} params"
      | none => pure ()
    | _ => pure ()

  -- Check 6: exceptArgs consistency
  for block in f.blocks do
    for ni in block.instrs do
      match ni.exceptArgs with
      | some args =>
        match block.except with
        | none =>
          errors := errors.push
            s!"bb{block.id.id}: instruction has exceptArgs but block has no except target"
        | some et =>
          match blockMap[et.target.id]? with
          | some handlerBlock =>
            if args.size != handlerBlock.params.size then
              errors := errors.push
                s!"bb{block.id.id}: exceptArgs length {args.size} != handler bb{et.target.id} param count {handlerBlock.params.size}"
          | none => pure ()  -- caught by check 2
      | none => pure ()

  -- Check 7: All SSAVal uses defined somewhere in function
  for block in f.blocks do
    for ni in block.instrs do
      for v in instrUsedVals ni.instr do
        if !definedVals.contains v.id then
          errors := errors.push s!"bb{block.id.id}: %{v.id} used but never defined"
      match ni.exceptArgs with
      | some args =>
        for v in exceptArgUsedVals args do
          if !definedVals.contains v.id then
            errors := errors.push s!"bb{block.id.id}: %{v.id} used in exceptArgs but never defined"
      | none => pure ()
    for v in termUsedVals block.term do
      if !definedVals.contains v.id then
        errors := errors.push s!"bb{block.id.id}: %{v.id} used in terminator but never defined"

  -- Check 8: mkDict keys/vals same length
  for block in f.blocks do
    for ni in block.instrs do
      match ni.instr with
      | .mkDict keys vals =>
        if keys.size != vals.size then
          errors := errors.push
            s!"bb{block.id.id}: mkDict has {keys.size} keys but {vals.size} vals"
      | _ => pure ()

  -- Check 9: Entry block exists
  -- Note: function params are defined at the Func level, not as entry block
  -- params. The entry block's params come from demand analysis (typically empty
  -- for bb0). Function param SSAVals are added to definedVals above.
  if f.blocks.size == 0 then
    errors := errors.push "function has no blocks"

  return errors

/-! ## Module-Level Entry Point -/

/-- Check all well-formedness invariants for a module.
    Returns an array of error messages (empty = well-formed). -/
public def checkModule (m : Module) : Array String := Id.run do
  let mut errors : Array String := #[]
  for func in m.funcs do
    let funcErrors := checkFunc func
    for err in funcErrors do
      errors := errors.push s!"func '{func.name}': {err}"
  errors

end Strata.Python.SSACheck

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.TypeCheck.Propagate

/-!
# Formatting for Type Check Results

Produces a textual summary of inferred types per function, used for
test comparison (`.expected` files) and CLI output.
-/

public section
namespace Strata.Python.TypeCheck

open Strata.Python.SSA in
open Strata.Python.TypeCheck in

/-- Format the inferred types for a single function. -/
def fmtFuncTypes (func : Strata.Python.SSA.Func) (state : TypeState) : String := Id.run do
  let mut lines : Array String := #[s!"func {func.name}:"]
  for p in func.params do
    let ty := state.getType p.val
    lines := lines.push s!"  param {p.name}: {ty}"
  let entryId := if h : 0 < func.blocks.size then func.blocks[0].id else default
  for block in func.blocks do
    if block.id != entryId then
      for bp in block.params do
        let name := if h : bp.val.id < func.names.size then
          ToString.toString func.names[bp.val.id]
        else s!"%{bp.val.id}"
        let ty := state.getType bp.val
        lines := lines.push s!"  %{bp.val.id}:{name} : {ty}"
    for ni in block.instrs do
      if let some v := ni.result then
        let name := if h : v.id < func.names.size then
          ToString.toString func.names[v.id]
        else s!"%{v.id}"
        let ty := state.getType v
        lines := lines.push s!"  %{v.id}:{name} : {ty}"
  return "\n".intercalate lines.toList

/-- Format the complete type check result for a module. -/
def fmtTypeCheckResult (mod : Strata.Python.SSA.Module) (result : TypeCheckResult) : String :=
  let header := s!"module \"{mod.name}\":"
  let funcSections := result.funcResults.toList.map fun (name, state) =>
    let func := mod.funcs.toList.find? (·.name == name)
    match func with
    | some f => fmtFuncTypes f state
    | none => s!"func {name}: <not found>"
  let body := "\n\n".intercalate funcSections
  let diagSection := if result.diagnostics.isEmpty then ""
    else
      let diagLines := result.diagnostics.toList.map ToString.toString
      "\n\ndiagnostics:\n" ++ "\n".intercalate (diagLines.map (s!"  {·}"))
  s!"{header}\n\n{body}{diagSection}\n"

end Strata.Python.TypeCheck
end -- public section

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.CoreToCProverGOTO
import Strata.Backends.CBMC.GOTO.DefaultSymbols
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Util.Json

public section

open Std (ToFormat Format format)

/-
Emit the `CProverGOTO.Context` produced by the Core→GOTO translation
(`Strata.Languages.GOTO.CoreToCProverGOTO`) as CBMC-compatible JSON files that
contain all the necessary information to construct a GOTO binary.

Also see `mkGotoBin.sh`, where we use CBMC's `symtab2gb` to construct and
model-check a Strata-generated GOTO binary.
-/

-------------------------------------------------------------------------------

namespace CoreToGOTO

structure CProverGOTO.Json where
  symtab : Lean.Json := .null
  goto   : Lean.Json := .null

open Strata in
open StrataDDM in
def CProverGOTO.Context.toJson (programName : String) (ctx : CProverGOTO.Context) :
  Except String CProverGOTO.Json := do
  let fn_symbol : Map String CProverGOTO.CBMCSymbol :=
    [CProverGOTO.createFunctionSymbol programName ctx.formals ctx.ret ctx.contracts]
  let formals : Map String CProverGOTO.CBMCSymbol :=
    ctx.formals.map (fun (name, ty) =>
        CProverGOTO.createGOTOSymbol programName name (CProverGOTO.mkFormalSymbol programName name)
          (isParameter := true) (isStateVar := true) (ty := some ty))
  let locals : Map String CProverGOTO.CBMCSymbol :=
    ctx.locals.map (fun name =>
        CProverGOTO.createGOTOSymbol programName name (CProverGOTO.mkLocalSymbol programName name)
          (isParameter := false) (isStateVar := false) (ty := ctx.localTypes.get? name))
  let fnAppSymbols : Map String CProverGOTO.CBMCSymbol :=
    (CProverGOTO.collectFnApps ctx.program).map CProverGOTO.createFnAppSymbol
  let knownSymbols := fn_symbol ++ formals ++ locals ++ fnAppSymbols
  let knownNames := knownSymbols.map (·.1)
  let extraSymbols : Map String CProverGOTO.CBMCSymbol :=
    (CProverGOTO.collectSymbolRefs ctx.program).filter (fun info => !knownNames.contains info.name)
      |>.map fun info =>
        CProverGOTO.createGOTOSymbol programName info.name info.name
          (isParameter := false) (isStateVar := false) (ty := some info.type)
  let symbols := Lean.toJson (knownSymbols ++ extraSymbols)
  let goto_functions ← CProverGOTO.programsToJson [(programName, ctx.program)]
  return { symtab := symbols, goto := goto_functions }

open Strata in
open StrataDDM in
def getGotoJson (programName : String) (env : Program) : IO CProverGOTO.Json := do
  let (program, errors) := TransM.run Inhabited.default (translateProgram env)
  if errors.isEmpty then
    (match (CoreToGOTO.transformToGoto program) with
      | .error e =>
        -- Propagate rather than returning empty JSON, which would write `null`
        -- output files yet exit successfully — no failure signal to callers.
        throw (IO.userError s!"GOTO translation error: {e}")
      | .ok ctx =>
        IO.ofExcept (CProverGOTO.Context.toJson programName ctx))
  else
    throw (IO.userError s!"DDM Transform Error: {repr errors}")

open Strata in
open StrataDDM in
def writeToGotoJson (programName symTabFileName gotoFileName : String) (env : Program) : IO Unit := do
  let json ← getGotoJson programName env
  let symtabObj := match json.symtab with | .obj m => m | _ => .empty
  let symtab := CProverGOTO.wrapSymtab symtabObj (moduleName := programName)
  writeJsonFile symTabFileName symtab
  writeJsonFile gotoFileName json.goto

end CoreToGOTO

-------------------------------------------------------------------------------

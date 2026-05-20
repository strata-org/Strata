/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Elab.Command -- shake: keep
public import Strata.DDM.Util.Ion.AST
meta import Strata.DDM.Util.Ion.SymbolTable --shake: keep

-- Use metaprogramming to declare `{sym}SymbolId : SymbolId` for each system symbol.
section
open Lean (TSyntax)
open Lean.Elab.Command (elabCommand)
open Lean.Parser.Category (command)

-- Declare all system symbol ids as constants
run_cmd do
  for sym in Ion.SymbolTable.ionSharedSymbolTableEntries do
    -- To simplify name, strip out non-alphanumeric characters.
    let simplifiedName : String := .ofList <| sym.toList.filter (·.isAlphanum)
    let leanName := Lean.mkIdentFrom (canonical := true) default <| ``Ion.SymbolId |>.str simplifiedName
    let idx := Ion.SymbolTable.system.symbolId sym
    if idx = .zero then
      throwError s!"Unbound symbol {sym}"
    elabCommand $ ← `(command|
      public def $(leanName) : Ion.SymbolId := ⟨$(Lean.Syntax.mkNatLit idx.value)⟩
    )

end

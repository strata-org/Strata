/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Elab.Command
public meta import Strata.DDM.Integration.Lean.HashCommands
public meta import Strata.DDM.TaggedRegions
public meta import Strata.DDM.Elab
public meta import Strata.DDM.Integration.Lean.Env
public meta import Strata.DDM.Integration.Lean.ToExpr
public meta import Strata.Languages.Core.Verifier
public import Strata.DDM.Integration.Lean.HashCommands
public import Strata.Languages.Core.Verifier
import Strata.DDM.TaggedRegions
import Strata.DDM.Integration.Lean.Env
import Strata.DDM.Integration.Lean.ToExpr
import Strata.DDM.Elab.DeclM

open Lean
open Lean.Elab.Term (TermElab)
open Lean.Parser (InputContext)
open Strata.Lean (arrayToExpr)

namespace Strata

public section

/--
Bundle returned by `#strata_expect`: the parsed program (or an empty placeholder
if parsing failed), the snippet source, and any parse-level diagnostics.
-/
structure ExpectedBlock where
  program : Program
  /-- The raw text inside the `#strata_expect ... #end` block. The test helper
      uses it to build a FileMap so `DiagnosticModel`s produced downstream
      (translate, resolve) can be rendered with snippet-local line/col. -/
  source : String
  /-- Diagnostics already produced (e.g. by parsing). Snippet-local positions. -/
  parseDiagnostics : Array Diagnostic
  deriving Inhabited

/-- Convert a `Lean.Message` (as produced by Strata's elaborator on parse error)
into a `Strata.Diagnostic`. Positions are kept snippet-local. -/
private meta def messageToDiagnostic (msg : Lean.Message) : BaseIO Diagnostic := do
  let text ← msg.data.toString
  pure {
    start := msg.pos
    ending := msg.endPos.getD msg.pos
    message := text
    type := DiagnosticType.UserError
  }

-- `#strata_expect ... #end` — negative-test counterpart of `#strata`. See ExpectedBlock.
declare_tagged_region term strataExpectProgram "#strata_expect" "#end"

@[term_elab strataExpectProgram]
meta def strataExpectImpl : TermElab := fun stx _ => do
  let .atom i _ := stx[1]
        | throwError s!"Bad {stx[1]}"
  let .original _ p _ e := i
        | throwError s!"Expected input context"
  let fullInputCtx ← (HasInputContext.getInputContext : CoreM Lean.Parser.InputContext)
  let snippet := String.Pos.Raw.extract fullInputCtx.inputString p e
  let inputCtx : Lean.Parser.InputContext := {
    inputString := snippet
    fileName := "<#strata_expect>"
    fileMap := FileMap.ofString snippet
  }
  let s := (dialectExt.getState (← Lean.getEnv))
  let leanEnv ← Lean.mkEmptyEnvironment 0
  let diagType : Lean.Expr := mkConst ``Diagnostic
  match Strata.Elab.elabProgram s.loaded leanEnv inputCtx 0 inputCtx.endPos with
  | .ok pgm =>
    let some (.str name root) := s.nameMap[pgm.dialect]?
      | throwError s!"Unknown dialect {pgm.dialect}"
    let commandType : Lean.Expr := mkConst ``Operation
    let cmdToExpr (cmd : Strata.Operation) : CoreM Lean.Expr := do
      let n ← Lean.mkFreshUserName `command
      addDefn n commandType (toExpr cmd)
      pure <| mkConst n
    let commandExprs ← monadLift <| pgm.commands.mapM cmdToExpr
    let pgmExpr : Lean.Expr :=
      astExpr! Program.create
        (mkConst (name |>.str s!"{root}_map"))
        (toExpr pgm.dialect)
        (arrayToExpr .zero commandType commandExprs)
    let emptyDiags : Lean.Expr := arrayToExpr .zero diagType #[]
    return mkApp3 (mkConst ``ExpectedBlock.mk) pgmExpr (toExpr snippet) emptyDiags
  | .error errors =>
    let diags ← monadLift <| errors.mapM messageToDiagnostic
    let diagsExpr : Lean.Expr := arrayToExpr .zero diagType (diags.map toExpr)
    let pgmExpr : Lean.Expr :=
      astExpr! Program.create
        (mkConst ``DialectMap.empty)
        (toExpr ("" : DialectName))
        (arrayToExpr .zero (mkConst ``Operation) #[])
    return mkApp3 (mkConst ``ExpectedBlock.mk) pgmExpr (toExpr snippet) diagsExpr

end -- public section

end Strata

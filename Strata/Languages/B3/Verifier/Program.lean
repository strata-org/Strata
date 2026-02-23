/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Program Parsing

Utilities for parsing B3 DDM programs to B3 AST.
-/

namespace Strata.B3.Verifier

open Strata
open Strata.B3AST

/-- Convert DDM Program to B3 AST with error handling -/
def programToB3AST (prog : Program) : Except String (B3AST.Program SourceRange) := do
  let [op] ← pure prog.commands.toList
    | .error "Expected single program command"

  if op.name.name != "command_program" then
    .error s!"Expected command_program, got {op.name.name}"

  let [ArgF.op progOp] ← pure op.args.toList
    | .error "Expected single program argument"

  let cstProg ← B3CST.Program.ofAst progOp

  let (ast, errors) := B3.programFromCST B3.FromCSTContext.empty cstProg
  if !errors.isEmpty then
    .error s!"CST to AST conversion errors: {errors}"
  else
    .ok ast

end Strata.B3.Verifier

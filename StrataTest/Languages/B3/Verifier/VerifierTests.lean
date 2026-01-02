/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier
import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.Conversion

/-!
# B3 Verifier Integration Tests

Tests for end-to-end verification with Z3 solver.
-/

namespace B3.Verifier.Tests

open Strata
open Strata.B3.Verifier

/-- Helper to extract B3 program from DDM parse result -/
def programToB3CST (prog : Program) : B3CST.Program SourceRange :=
  match prog.commands.toList with
  | [op] =>
      if op.name.name == "command_program" then
        match op.args.toList with
        | [ArgF.op progOp] =>
            match B3CST.Program.ofAst progOp with
            | .ok cstProg => cstProg
            | .error _ => default
        | _ => default
      else default
  | _ => default

/-- Helper to convert B3CST to B3AST -/
def b3CSTToAST (cst : B3CST.Program SourceRange) : B3AST.Program Unit × List (B3.CSTToASTError SourceRange) :=
  let (prog, errors) := B3.programFromCST B3.FromCSTContext.empty cst
  (B3AST.Program.mapMetadata (fun _ => ()) prog, errors)

---------------------------------------------------------------------
-- Tests
---------------------------------------------------------------------

/--
info: Check results:
  procedure test: unsat (verified)
-/
#guard_msgs in
#eval do
  let prog := #strata program B3CST;
  function f(x : int) : int
  axiom forall x : int pattern f(x) x > 0 ==> f(x) > 0
  procedure test() {
    check 5 > 0 ==> f(5) > 0
  }
  #end
  let cst := programToB3CST prog
  let (ast, _) := b3CSTToAST cst
  let results ← verifyProgram ast
  IO.println "Check results:"
  for result in results do
    match result.decl with
    | .procedure _ name _ _ _ =>
        let status := match result.decision with
          | .unsat => "unsat (verified)"
          | .sat => "sat (counterexample found)"
          | .unknown => "unknown"
        IO.println s!"  procedure {name.val}: {status}"
    | _ => pure ()

end B3.Verifier.Tests

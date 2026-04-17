/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.MapStmtExpr

/-!
## FunctionsAndProofs IR

An intermediate representation that separates Laurel procedures into
functions (pure, used for computation) and proofs (used for verification).

This IR sits between Laurel and CoreWithLaurelTypes in the pipeline:
  Laurel → FunctionsAndProofs → CoreWithLaurelTypes → Core

Currently partitions by `isFunctional`. When the contract pass is enabled,
the proof pass will generate:
- A function for every procedure (body included only for transparent procedures,
  with Assert/Assume stripped via `stripAssertAssume`).
- A proof for every procedure.
-/

namespace Strata.Laurel

public section

/--
A program in the FunctionsAndProofs IR. Functions are pure computational
procedures; proofs are verification-only procedures.
Both reuse `Laurel.Procedure` as their representation.
-/
structure FunctionsAndProofsProgram where
  functions : List Procedure
  proofs : List Procedure
  datatypes : List DatatypeDefinition
  constants : List Constant

/-- Deep traversal that strips all Assert and Assume nodes from a StmtExpr tree.
    Assert/Assume nodes are replaced with `LiteralBool true`, and Block nodes
    are collapsed by filtering out trivial `LiteralBool true` leftovers. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert _ | .Assume _ => ⟨.LiteralBool true, e.source, e.md⟩
    | .Block stmts label =>
      let stmts' := stmts.filter fun s =>
        match s.val with | .LiteralBool true => false | _ => true
      match stmts' with
      | [] => ⟨.LiteralBool true, e.source, e.md⟩
      | [s] => if label.isNone then s else ⟨.Block [s] label, e.source, e.md⟩
      | _ => ⟨.Block stmts' label, e.source, e.md⟩
    | _ => e) expr

/-- Create the function copy of a procedure. The function body is included only
    when the procedure was originally functional and has a transparent body;
    non-functional procedures get opaque function copies since their bodies
    contain imperative constructs that cannot be translated as pure functions.
    Assert/Assume nodes are stripped from function bodies. -/
private def mkFunctionCopy (proc : Procedure) : Procedure :=
  let body := match proc.body with
    | .Transparent b => .Transparent (stripAssertAssume b)
    | .Opaque _ _ _ => .Opaque [] none []
    | x => x
  { proc with isFunctional := true, body := body }

/--
Proof pass: translate a Laurel program to the FunctionsAndProofs IR.

Partitions procedures by `isFunctional`: functional procedures become
functions, non-functional become proofs.
-/
def laurelToFunctionsAndProofs (program : Program) : FunctionsAndProofsProgram :=
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let functions := program.staticProcedures.map mkFunctionCopy
  let proofs := nonExternal.map fun p =>
    { p with isFunctional := false,
             name := { p.name with text := p.name.text ++ "$proof", uniqueId := none } }
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, proofs, datatypes, constants := program.constants }


end -- public section
end Strata.Laurel

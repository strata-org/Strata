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

The proof pass generates:
- A function for every procedure (body included only for transparent procedures,
  with Assert/Assume stripped).
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
    Assert/Assume nodes are replaced with `LiteralBool true`. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert _ | .Assume _ => ⟨.LiteralBool true, e.md⟩
    | _ => e) expr

/-- Create the function copy of a procedure. The function body is included only
    when the procedure has a transparent body; otherwise the body is made opaque
    with no implementation. Assert/Assume nodes are stripped from function bodies. -/
private def mkFunctionCopy (proc : Procedure) : Procedure :=
  let body := match proc.body with
    | .Transparent b => .Transparent (stripAssertAssume b)
    | _ => .Opaque [] none []
  { proc with isFunctional := true, body := body }

/--
Proof pass: translate a Laurel program to the FunctionsAndProofs IR.

Every procedure generates both a function copy (with Assert/Assume stripped,
body only for transparent procedures) and a proof copy.
-/
def laurelToFunctionsAndProofs (program : Program) : FunctionsAndProofsProgram :=
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let functions := nonExternal.map mkFunctionCopy
  let proofs := nonExternal.map fun p => { p with isFunctional := false }
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, proofs, datatypes, constants := program.constants }

end -- public section
end Strata.Laurel

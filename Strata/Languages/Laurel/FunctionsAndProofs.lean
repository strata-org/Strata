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
- A function for each functional procedure.
- A proof for each non-functional procedure.

In the future, every procedure will generate both a function and a proof,
with assertions/assumptions stripped from function bodies via deep traversal.
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
    Assert/Assume nodes are replaced with `LiteralBool true`.
    This will be used by the full proof pass when every procedure generates
    both a function and a proof. -/
def stripAssertAssume (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun e =>
    match e.val with
    | .Assert _ | .Assume _ => ⟨.LiteralBool true, e.md⟩
    | _ => e) expr

/--
Proof pass: translate a Laurel program to the FunctionsAndProofs IR.

Functional Laurel procedures become functions; non-functional procedures
become proofs.
-/
def laurelToFunctionsAndProofs (program : Program) : FunctionsAndProofsProgram :=
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let (functions, proofs) := nonExternal.partition (·.isFunctional)
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, proofs, datatypes, constants := program.constants }

end -- public section
end Strata.Laurel

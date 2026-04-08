/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
# Ordered Laurel Program

An intermediate representation between `Laurel.Program` and `Core.Program`.
Declarations are topologically ordered (dependencies before dependents),
mutually recursive callables and datatypes are grouped. Axiom slots
(postcondition, invokeOn) are attached to declarations and populated
by `generateAxioms`.

Bodies and types remain in Laurel form (`StmtExpr`, `HighType`).
Expression/type translation to Core happens in a subsequent pass.
-/

namespace Strata.Laurel

public section

/-- An axiom expressed in Laurel's StmtExpr, translated to Core.Expression later. -/
structure LaurelAxiom where
  name : String
  body : StmtExprMd
  md   : MetaData

/-- A declaration in an ordered Laurel program. -/
inductive OrderedDecl where
  /-- A group of functions (single non-recursive, or mutually recursive). -/
  | funcs (procs : List Procedure) (axioms : List LaurelAxiom) (isRecursive : Bool)
  /-- A procedure. -/
  | proc (proc : Procedure) (axioms : List LaurelAxiom)
  /-- A group of (possibly mutually recursive) datatypes. -/
  | datatypes (dts : List DatatypeDefinition)
  /-- A named constant. -/
  | constant (c : Constant)

/-- A Laurel program with topologically ordered declarations. All structural
    decisions (ordering, grouping, function/procedure classification, axiom
    generation) have been made. Bodies are still StmtExpr; types are still
    HighType. -/
structure OrderedProgram where
  decls : List OrderedDecl

end

end Strata.Laurel

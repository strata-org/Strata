/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Function

/-! ## Name conditions on programs

The conditions on the names a program uses that the typing relation
(`ProgramWellTyped`) does not state: program-wide distinctness, and local types named like a
program declaration. `ProgramNamesWF` collects them for a program.

A variable may have the name of a function or constant: the expressions tell the two apart (a
function is an operator, a variable a free variable), so the variable shadows the function in
its scope. The back end, which puts both in one namespace, renames such variables apart first
(`Core.separateVarNamesPipelinePhase`). -/

open Lambda

public section

namespace Core

namespace TypeSpec

open Lambda Imperative

mutual

/-- The names in a statement are valid. A local type declaration names no program
    declaration. -/
def StatementNamesWF (P : Program) : Statement → Prop
  | .cmd _ => True
  | .block _ body _ => StatementsNamesWF P body
  | .ite _ thenb elseb _ => StatementsNamesWF P thenb ∧ StatementsNamesWF P elseb
  | .loop _ _ _ body _ => StatementsNamesWF P body
  | .exit _ _ => True
  | .typeDecl tc _ => ∀ n ∈ P.getNames, n.name ≠ tc.name

/-- The names in every statement of a list are valid. -/
def StatementsNamesWF (P : Program) : List Statement → Prop
  | [] => True
  | s :: ss => StatementNamesWF P s ∧ StatementsNamesWF P ss

end

/-- The names in a procedure are valid: the names in a structured body are valid. -/
def ProcNamesWF (P : Program) (p : Procedure) : Prop :=
  match p.body with
  | .structured ss _ => StatementsNamesWF P ss
  | .cfg _ _ | .abstract => True

/-- The names in a declaration are valid. -/
def DeclNamesWF (P : Program) : Decl → Prop
  | .proc p _ => ProcNamesWF P p
  | _ => True

/-- The names in every declaration of a list are valid. -/
def DeclsNamesWF (P : Program) : List Decl → Prop
  | [] => True
  | d :: ds => DeclNamesWF P d ∧ DeclsNamesWF P ds

/-- The names in program `P` are valid in a context `C`: all declared names are distinct and
    none is an identifier of `C`, and every declaration is valid. -/
def ProgramNamesWF (C : LContext CoreLParams) (P : Program) : Prop :=
  P.getNames.Nodup ∧ (∀ n ∈ P.getNames, n.name ∉ C.idents) ∧ DeclsNamesWF P P.decls

end TypeSpec
end Core

end -- public section

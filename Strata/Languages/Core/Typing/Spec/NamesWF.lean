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
(`ProgramWellTyped`) does not state: program-wide distinctness, clashes between
variables and functions, and local types named like a program declaration.
`ProgramNamesWF` collects them for a program. A function scope `fns` says which
names are functions at a given point; a declaration extends it with the
functions it introduces (`Decl.extendScope`). -/

open Lambda

public section

namespace Core

/-- The functions of `fns` together with those the declaration `d` introduces: its functions,
    and the functions generated for a datatype block. -/
def Decl.extendScope (d : Decl) (fns : String → Prop) : String → Prop :=
  fun n => fns n ∨ n ∈ d.funcNames.map (·.name)

namespace TypeSpec

open Lambda Imperative

/-- A variable name that is not a function of `isFunc`. -/
def VarNotFunc (isFunc : String → Prop) (x : Expression.Ident) : Prop :=
  ¬ isFunc x.name

/-- The names an imperative command introduces are valid: a declared variable is a valid
    variable name. -/
def CmdNamesWF (fns : String → Prop) : Cmd Expression → Prop
  | .init x _ _ _ => VarNotFunc fns x
  | .set _ _ _ => True
  | .assert _ _ _ => True
  | .assume _ _ _ => True
  | .cover _ _ _ => True

mutual

/-- The names in a statement are valid. A local type declaration names no program
    declaration. -/
def StatementNamesWF (P : Program) (fns : String → Prop) : Statement → Prop
  | .cmd (.cmd c) => CmdNamesWF fns c
  | .cmd (.call _ _ _) => True
  | .block _ body _ => StatementsNamesWF P fns body
  | .ite _ thenb elseb _ => StatementsNamesWF P fns thenb ∧ StatementsNamesWF P fns elseb
  | .loop _ _ _ body _ => StatementsNamesWF P fns body
  | .exit _ _ => True
  | .typeDecl tc _ => ∀ n ∈ P.getNames, n.name ≠ tc.name

/-- The names in every statement of a list are valid. -/
def StatementsNamesWF (P : Program) (fns : String → Prop) :
    List Statement → Prop
  | [] => True
  | s :: ss => StatementNamesWF P fns s ∧ StatementsNamesWF P fns ss

end

/-- The names in a function are valid: its formals are not functions of `fns`. -/
def FuncNamesWF (fns : String → Prop) (f : Function) : Prop :=
  ∀ x ∈ f.inputs.keys, VarNotFunc fns x

/-- The names in a procedure are valid: its formals are not functions of `fns`, and the names
    in a structured body are valid. -/
def ProcNamesWF (P : Program) (fns : String → Prop) (p : Procedure) : Prop :=
  (∀ x ∈ p.header.inputs.keys ++ p.header.outputs.keys, VarNotFunc fns x) ∧
  match p.body with
  | .structured ss => StatementsNamesWF P fns ss
  | .cfg _ => True

/-- The names in a declaration are valid, with `fns` the functions in scope before it. The
    functions of a recursive block are in scope for the whole block. -/
def DeclNamesWF (P : Program) (fns : String → Prop) : Decl → Prop
  | .type _ _ => True
  | .ax _ _ => True
  | .lemma _ _ => True
  | .distinct _ _ _ => True
  | .proc p _ => ProcNamesWF P fns p
  | .func f _ => FuncNamesWF fns f
  | .recFuncBlock fs md =>
    ∀ f ∈ fs, FuncNamesWF (Decl.extendScope (.recFuncBlock fs md) fns) f

/-- The names in every declaration of a list are valid, each declaration seeing the functions
    the earlier ones introduce. -/
def DeclsNamesWF (P : Program) (fns : String → Prop) : List Decl → Prop
  | [] => True
  | d :: ds => DeclNamesWF P fns d ∧ DeclsNamesWF P (d.extendScope fns) ds

/-- The names in program `P` are valid in a context `C`: all declared names are distinct and
    none is an identifier of `C`, and every declaration is valid with the functions of `C` in
    scope. -/
def ProgramNamesWF (C : LContext CoreLParams) (P : Program) : Prop :=
  P.getNames.Nodup ∧ (∀ n ∈ P.getNames, n.name ∉ C.idents) ∧
    DeclsNamesWF P (fun n => n ∈ C.functions) P.decls

end TypeSpec
end Core

end -- public section

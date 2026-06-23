/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Implicit.Program
public import Strata.Languages.Core.DDMTransform.FormatCore

/-!
# Formatting for Core-implicit

A `ToFormat` for the Core-implicit AST. Heap commands are rendered directly;
standard Core commands delegate to the existing Core formatter, so implicit
output reads the same as explicit output for the shared constructs. Control
flow (blocks, conditionals, loops) is rendered by recursion over the generic
`Imperative.Stmt` skeleton.

As in `Core.formatProgram`, names that are not part of the Core grammar (type
constructors such as `Composite`, declared procedure/function/type names) must
be registered as free variables for the DDM formatter to render them; these are
threaded through as `extraFreeVars`. The program-level formatter gathers them
from the program's declarations.
-/

namespace Core.Implicit

open Std (Format ToFormat format)
open Imperative
open Strata (Core.formatExprs Core.formatCommand)

public section

/-- Format a heap command. The field reference and operands are rendered with
the Core expression formatter, registering `extraFreeVars` so names outside the
grammar (e.g. the field operator) resolve. -/
def formatHeapCmd (extraFreeVars : Array String) : HeapCmd → Format
  | .heapRead lhs obj field _ty =>
    format lhs.name ++ " := heapRead(" ++ Core.formatExprs [obj] extraFreeVars ++ ", " ++
      Core.formatExprs [field] extraFreeVars ++ ")"
  | .heapWrite obj field rhs =>
    "heapWrite(" ++ Core.formatExprs [obj] extraFreeVars ++ ", " ++
      Core.formatExprs [field] extraFreeVars ++ ", " ++ Core.formatExprs [rhs] extraFreeVars ++ ")"
  | .heapAlloc lhs typeName =>
    format lhs.name ++ " := heapAlloc(" ++ typeName ++ ")"
  | .heapInstanceOf lhs obj typeName =>
    format lhs.name ++ " := heapInstanceOf(" ++ Core.formatExprs [obj] extraFreeVars ++ ", " ++ typeName ++ ")"

/-- Format an implicit command: a heap command directly, or a standard Core
command via the Core formatter (with `extraFreeVars` registered). -/
def formatImplicitCmd (extraFreeVars : Array String) : ImplicitCmd → Format
  | .core c => Core.formatCommand c extraFreeVars
  | .heap c => formatHeapCmd extraFreeVars c

/-- Format a guard (`ExprOrNondet`). -/
private def formatGuard (extraFreeVars : Array String) : ExprOrNondet Core.Expression → Format
  | .det e => Core.formatExprs [e] extraFreeVars
  | .nondet => "*"

/-- Format an implicit statement by recursion over the shared `Stmt` skeleton.
Leaf commands carry their own terminator already, so statements are joined by a
line break rather than an inserted separator. -/
partial def formatStatement (extraFreeVars : Array String) (stmt : Statement) : Format :=
  let joinStmts (ss : List Statement) : Format :=
    Format.joinSep (ss.map (formatStatement extraFreeVars)) Format.line
  match stmt with
  | .cmd c => formatImplicitCmd extraFreeVars c
  | .block label b _ =>
    "block " ++ label ++ " {" ++ Format.nest 2 (Format.line ++ joinStmts b) ++ Format.line ++ "}"
  | .ite cond thenb elseb _ =>
    "if " ++ formatGuard extraFreeVars cond ++ " {" ++
      Format.nest 2 (Format.line ++ joinStmts thenb) ++ Format.line ++
      "} else {" ++ Format.nest 2 (Format.line ++ joinStmts elseb) ++ Format.line ++ "}"
  | .loop guard _ invariants body _ =>
    let invF := Format.joinSep
      (invariants.map (fun (l, e) => "invariant " ++ l ++ ": " ++ Core.formatExprs [e] extraFreeVars))
      Format.line
    "while " ++ formatGuard extraFreeVars guard ++ invF ++ " {" ++
      Format.nest 2 (Format.line ++ joinStmts body) ++ Format.line ++ "}"
  | .exit label _ => "exit " ++ label
  | .funcDecl _ _ => "<funcDecl>"
  | .typeDecl _ _ => "<typeDecl>"

/-- Format an implicit procedure (header line + heap effect + body). -/
def formatProcedure (extraFreeVars : Array String) (p : Procedure) : Format :=
  let effectStr := match p.effect with
    | .none => "none" | .reads => "reads" | .writes => "writes"
  let formatSig (sig : @Lambda.LMonoTySignature Unit) : Format :=
    Format.joinSep (sig.toList.map (fun (id, ty) => id.name ++ " : " ++ format ty)) ", "
  let inputsF := formatSig p.header.inputs
  let outputsF := if p.header.outputs.isEmpty then Format.nil
    else " returns (" ++ formatSig p.header.outputs ++ ")"
  let clauses (kw : String) (cs : List (Core.CoreLabel × Core.Procedure.Check)) : List Format :=
    cs.map (fun (_, c) => kw ++ " " ++ Core.formatExprs [c.expr] extraFreeVars)
  let specClauses := clauses "requires" p.spec.preconditions.toList ++
    clauses "ensures" p.spec.postconditions.toList
  let specF := if specClauses.isEmpty then Format.nil
    else Format.joinSep specClauses Format.line ++ Format.line
  "procedure " ++ p.header.name.name ++ "(" ++ inputsF ++ ")" ++ outputsF ++
    " [heap: " ++ effectStr ++ "]" ++ Format.line ++
    specF ++ Format.joinSep (p.body.map (formatStatement extraFreeVars)) Format.line

/-- Format an object-type schema: `class Name extends … { field : ty; … }`. -/
def formatObjectType (t : ObjectType) : Format :=
  let extendsF := if t.extending.isEmpty then Format.nil
    else " extends " ++ Format.joinSep (t.extending.map Format.text) ", "
  let fieldsF := Format.joinSep
    (t.fields.map (fun (n, ty) => n ++ " : " ++ format ty)) "; "
  "class " ++ t.name ++ extendsF ++ " { " ++ fieldsF ++ " }"

/-- Names a declaration contributes to the formatting context. -/
private def declNames : Decl → List String
  | .proc p _ => [p.header.name.name]
  | .func f _ => [f.name.name]
  | .recFuncBlock fs _ => fs.map (·.name.name)
  | .distinct name _ _ => [name.name]
  | .objectType t _ => [t.name]
  | .type _ _ | .ax _ _ => []

/-- Gather the free-var names a program's declarations need registered. Includes
`Composite`, the type-constructor name object-typed locals carry. -/
def programFreeVars (prog : Program) : Array String :=
  ("Composite" :: prog.decls.flatMap declNames).toArray

/-- Format a Core-implicit program, registering declared names so the Core
formatter resolves them. -/
def formatProgram (prog : Program) : Format :=
  let extra := programFreeVars prog
  let formatDecl : Decl → Format
    | .proc p _ => formatProcedure extra p
    | .objectType t _ => formatObjectType t
    | _ => Format.nil
  "program CoreImplicit;" ++ Format.line ++
    Format.joinSep (prog.decls.map formatDecl) (Format.line ++ Format.line)

instance : ToFormat Procedure where
  format := formatProcedure #[]

instance : ToFormat Program where
  format := formatProgram

end

end Core.Implicit

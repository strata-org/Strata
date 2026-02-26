/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Laurel

open Std (Format)
open Std.Format

def formatOperation : Operation → Format
  | .Eq => "=="
  | .Neq => "!="
  | .And => "&&"
  | .Or => "||"
  | .Not => "!"
  | .Implies => "==>"
  | .Neg => "-"
  | .Add => "+"
  | .Sub => "-"
  | .Mul => "*"
  | .Div => "/"
  | .Mod => "%"
  | .DivT => "/t"
  | .ModT => "%t"
  | .Lt => "<"
  | .Leq => "<="
  | .Gt => ">"
  | .Geq => ">="
  | .StrConcat => "++"


mutual
def formatHighType (t : HighTypeMd) : Format := formatHighTypeVal t.val
  termination_by sizeOf t
  decreasing_by cases t; term_by_mem

def formatHighTypeVal : HighType → Format
  | .TVoid => "void"
  | .TBool => "bool"
  | .TInt => "int"
  | .TFloat64 => "float64"
  | .TString => "string"
  | .THeap => "Heap"
  | .TTypedField valueType => "Field[" ++ formatHighType valueType ++ "]"
  | .TSet elementType => "Set[" ++ formatHighType elementType ++ "]"
  | .TMap keyType valueType => "Map[" ++ formatHighType keyType ++ ", " ++ formatHighType valueType ++ "]"
  | .UserDefined name => Format.text name
  | .Applied base args =>
      Format.text "(" ++ formatHighType base ++ " " ++
      Format.joinSep (args.map formatHighType) " " ++ ")"
  | .Pure base => "pure(" ++ formatHighType base ++ ")"
  | .Intersection types =>
      Format.joinSep (types.map formatHighType) " & "
  | .TCore s => s!"Core({s})"
  termination_by t => sizeOf t
  decreasing_by all_goals term_by_mem
end

instance : Std.ToFormat HighTypeMd where
  format := formatHighType

mutual
def formatStmtExpr (s : StmtExprMd) : Format := formatStmtExprVal s.val
  termination_by sizeOf s
  decreasing_by cases s; term_by_mem

def formatStmtExprVal (s : StmtExpr) : Format :=
  match s with
  | .IfThenElse cond thenBr elseBr =>
      "if " ++ formatStmtExpr cond ++ " then " ++ formatStmtExpr thenBr ++
      match elseBr with
      | none => ""
      | some e => " else " ++ formatStmtExpr e
  | .Block stmts _ =>
      group $ "{" ++ nestD (line ++ joinSep (stmts.map formatStmtExpr) (";" ++ line)) ++ line ++ "}"
  | .LocalVariable name ty init =>
      "var " ++ Format.text name ++ ": " ++ formatHighType ty ++
      match init with
      | none => ""
      | some e => " := " ++ formatStmtExpr e
  | .While cond invs _ body =>
      "while " ++ formatStmtExpr cond ++
      (if invs.isEmpty then Format.nil else " invariant " ++ Format.joinSep (invs.map formatStmtExpr) "; ") ++
      " " ++ formatStmtExpr body
  | .Exit target => "exit " ++ Format.text target
  | .Return value =>
      "return" ++
      match value with
      | none => ""
      | some v => " " ++ formatStmtExpr v
  | .LiteralInt n => Format.text (toString n)
  | .LiteralBool b => if b then "true" else "false"
  | .LiteralString s => "\"" ++ Format.text s ++ "\""
  | .Identifier name => Format.text name
  | .Assign [single] value =>
      formatStmtExpr single ++ " := " ++ formatStmtExpr value
  | .Assign targets value =>
      "(" ++ Format.joinSep (targets.map formatStmtExpr) ", " ++ ")" ++ " := " ++ formatStmtExpr value
  | .FieldSelect target field =>
      formatStmtExpr target ++ "#" ++ Format.text field
  | .PureFieldUpdate target field value =>
      formatStmtExpr target ++ " with { " ++ Format.text field ++ " := " ++ formatStmtExpr value ++ " }"
  | .StaticCall name args =>
      Format.text name ++ "(" ++ Format.joinSep (args.map formatStmtExpr) ", " ++ ")"
  | .PrimitiveOp op [a] =>
      formatOperation op ++ formatStmtExpr a
  | .PrimitiveOp op [a, b] =>
      formatStmtExpr a ++ " " ++ formatOperation op ++ " " ++ formatStmtExpr b
  | .PrimitiveOp op args =>
      formatOperation op ++ "(" ++ Format.joinSep (args.map formatStmtExpr) ", " ++ ")"
  | .New name => "new " ++ Format.text name
  | .This => "this"
  | .ReferenceEquals lhs rhs =>
      formatStmtExpr lhs ++ " === " ++ formatStmtExpr rhs
  | .AsType target ty =>
      formatStmtExpr target ++ " as " ++ formatHighType ty
  | .IsType target ty =>
      formatStmtExpr target ++ " is " ++ formatHighType ty
  | .InstanceCall target name args =>
      formatStmtExpr target ++ "." ++ Format.text name ++ "(" ++
      Format.joinSep (args.map formatStmtExpr) ", " ++ ")"
  | .Forall name ty body =>
      "forall " ++ Format.text name ++ ": " ++ formatHighType ty ++ " => " ++ formatStmtExpr body
  | .Exists name ty body =>
      "exists " ++ Format.text name ++ ": " ++ formatHighType ty ++ " => " ++ formatStmtExpr body
  | .Assigned name => "assigned(" ++ formatStmtExpr name ++ ")"
  | .Old value => "old(" ++ formatStmtExpr value ++ ")"
  | .Fresh value => "fresh(" ++ formatStmtExpr value ++ ")"
  | .Assert cond => "assert " ++ formatStmtExpr cond
  | .Assume cond => "assume " ++ formatStmtExpr cond
  | .ProveBy value proof =>
      "proveBy(" ++ formatStmtExpr value ++ ", " ++ formatStmtExpr proof ++ ")"
  | .ContractOf _ fn => "contractOf(" ++ formatStmtExpr fn ++ ")"
  | .Abstract => "abstract"
  | .All => "all"
  | .Hole => "<?>"
  termination_by sizeOf s
  decreasing_by all_goals term_by_mem
end

def formatParameter (p : Parameter) : Format :=
  Format.text p.name ++ ": " ++ formatHighType p.type

def formatDeterminism : Determinism → Format
  | .deterministic none => "deterministic"
  | .deterministic (some reads) => "deterministic reads " ++ formatStmtExpr reads
  | .nondeterministic => "nondeterministic"

def formatBody : Body → Format
  | .Transparent body => formatStmtExpr body
  | .Opaque postconds impl modif =>
      (if modif.isEmpty then Format.nil
       else " modifies " ++ Format.joinSep (modif.map formatStmtExpr) ", ") ++
      Format.joinSep (postconds.map (fun p => " ensures " ++ formatStmtExpr p)) "" ++
      match impl with
      | none => Format.nil
      | some e => " := " ++ formatStmtExpr e
  | .Abstract post => "abstract ensures " ++ formatStmtExpr post

def formatProcedure (proc : Procedure) : Format :=
  "procedure " ++ Format.text proc.name ++
  "(" ++ Format.joinSep (proc.inputs.map formatParameter) ", " ++ ") returns " ++ Format.line ++
  "(" ++ Format.joinSep (proc.outputs.map formatParameter) ", " ++ ")" ++ Format.line ++
  "requires " ++ formatStmtExpr proc.precondition ++ Format.line ++
  formatDeterminism proc.determinism ++ Format.line ++
  formatBody proc.body

def formatField (f : Field) : Format :=
  (if f.isMutable then "var " else "val ") ++
  Format.text f.name ++ ": " ++ formatHighType f.type

def formatCompositeType (ct : CompositeType) : Format :=
  "composite " ++ Format.text ct.name ++
  (if ct.extending.isEmpty then Format.nil else " extends " ++
   Format.joinSep (ct.extending.map Format.text) ", ") ++
  " { " ++ Format.joinSep (ct.fields.map formatField) "; " ++ " }"

def formatConstrainedType (ct : ConstrainedType) : Format :=
  "constrained " ++ Format.text ct.name ++
  " = " ++ Format.text ct.valueName ++ ": " ++ formatHighType ct.base ++
  " | " ++ formatStmtExpr ct.constraint

def formatDatatypeConstructor (c : DatatypeConstructor) : Format :=
  Format.text c.name ++
  if c.args.isEmpty then Format.nil
  else "(" ++ Format.joinSep (c.args.map fun (n, ty) => Format.text n ++ ": " ++ formatHighType ty) ", " ++ ")"

def formatDatatypeDefinition (dt : DatatypeDefinition) : Format :=
  "datatype " ++ Format.text dt.name ++
  (if dt.typeArgs.isEmpty then Format.nil
   else "(" ++ Format.joinSep (dt.typeArgs.map Format.text) ", " ++ ")") ++
  " { " ++ Format.joinSep (dt.constructors.map formatDatatypeConstructor) ", " ++ " }"

def formatTypeDefinition : TypeDefinition → Format
  | .Composite ty => formatCompositeType ty
  | .Constrained ty => formatConstrainedType ty
  | .Datatype ty => formatDatatypeDefinition ty

def formatProgram (prog : Program) : Format :=
  Format.joinSep (prog.staticProcedures.map formatProcedure) "\n\n"

instance : Std.ToFormat Operation where
  format := formatOperation

instance : Std.ToFormat HighTypeMd where
  format := formatHighType

instance : Std.ToFormat HighType where
  format := formatHighTypeVal

instance : Std.ToFormat StmtExprMd where
  format := formatStmtExpr

instance : Std.ToFormat StmtExpr where
  format := formatStmtExprVal

instance : Std.ToFormat Parameter where
  format := formatParameter

instance : Std.ToFormat Determinism where
  format := formatDeterminism

instance : Std.ToFormat Body where
  format := formatBody

instance : Std.ToFormat Procedure where
  format := formatProcedure

instance : Std.ToFormat Field where
  format := formatField

instance : Std.ToFormat CompositeType where
  format := formatCompositeType

instance : Std.ToFormat ConstrainedType where
  format := formatConstrainedType

instance : Std.ToFormat DatatypeConstructor where
  format := formatDatatypeConstructor

instance : Std.ToFormat DatatypeDefinition where
  format := formatDatatypeDefinition

instance : Std.ToFormat TypeDefinition where
  format := formatTypeDefinition

instance : Std.ToFormat Program where
  format := formatProgram

end Laurel

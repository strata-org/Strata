/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.Languages.Laurel.Grammar.LaurelGrammar
public import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Laurel

public section

open Strata (SourceRange QualifiedIdent Arg Operation SepFormat)

private def sr : SourceRange := .none

private def laurelOp (name : String) (args : Array Arg := #[]) : Arg :=
  .op { ann := sr, name := { dialect := "Laurel", name := name }, args := args }

private def ident (s : String) : Arg := .ident sr s

private def optionArg (a : Option Arg) : Arg := .option sr a

private def commaSep (args : Array Arg) : Arg := .seq sr .comma args

private def semicolonSep (args : Array Arg) : Arg := .seq sr .semicolon args

private def seqArg (args : Array Arg) : Arg := .seq sr .none args

mutual

partial def highTypeToArg (t : HighTypeMd) : Arg := highTypeValToArg t.val

partial def highTypeValToArg : HighType → Arg
  | .TInt => laurelOp "intType"
  | .TBool => laurelOp "boolType"
  | .TFloat64 => laurelOp "float64Type"
  | .TReal => laurelOp "realType"
  | .TString => laurelOp "stringType"
  | .TMap k v => laurelOp "mapType" #[highTypeToArg k, highTypeToArg v]
  | .UserDefined name => laurelOp "compositeType" #[ident name.text]
  | .TCore s => laurelOp "coreType" #[ident s]
  | .TVoid => laurelOp "compositeType" #[ident "void"]
  | .THeap => laurelOp "compositeType" #[ident "Heap"]
  -- Type parameters discarded; the grammar cannot represent Field[T] or Set[T]
  | .TTypedField _vt => laurelOp "compositeType" #[ident "Field"]
  | .TSet _et => laurelOp "compositeType" #[ident "Set"]
  | .Applied base _args =>
    -- Applied types are not directly representable in the grammar;
    -- emit the base type as a best-effort approximation
    highTypeToArg base
  | .Pure base => highTypeToArg base
  | .Intersection types =>
    match types with
    | [] => laurelOp "compositeType" #[ident "Unknown"]
    | t :: _ => highTypeToArg t
  | .Unknown => laurelOp "compositeType" #[ident "Unknown"]

end

private def boolToArg (b : Bool) : Arg :=
  .op { ann := sr, name := { dialect := "Init", name := if b then "boolTrue" else "boolFalse" }, args := #[] }

private def operationName : Operation → String
  | .Eq => "eq" | .Neq => "neq" | .And => "and" | .Or => "or"
  | .AndThen => "andThen" | .OrElse => "orElse" | .Not => "not"
  | .Implies => "implies" | .Neg => "neg" | .Add => "add"
  | .Sub => "sub" | .Mul => "mul" | .Div => "div" | .Mod => "mod"
  | .DivT => "divT" | .ModT => "modT" | .Lt => "lt" | .Leq => "le"
  | .Gt => "gt" | .Geq => "ge" | .StrConcat => "strConcat"

partial def stmtExprToArg (s : StmtExprMd) : Arg := stmtExprValToArg s.val
where
  stmtExprValToArg : StmtExpr → Arg
    | .LiteralBool b => laurelOp "literalBool" #[boolToArg b]
    | .LiteralInt n =>
      match n with
      | .ofNat n => laurelOp "int" #[.num sr n]
      | .negSucc n => laurelOp "neg" #[laurelOp "int" #[.num sr (n + 1)]]
    | .LiteralDecimal d => laurelOp "real" #[.decimal sr d]
    | .LiteralString s => laurelOp "string" #[.strlit sr s]
    | .Hole true _ => laurelOp "hole"
    | .Hole false _ => laurelOp "nondetHole"
    | .Identifier name => laurelOp "identifier" #[ident name.text]
    | .Block stmts label =>
      let stmtArgs := stmts.map stmtExprToArg |>.toArray
      match label with
      | none => laurelOp "block" #[semicolonSep stmtArgs]
      | some l => laurelOp "labelledBlock" #[semicolonSep stmtArgs, ident l]
    | .LocalVariable name ty init =>
      let typeOpt := optionArg (some (laurelOp "typeAnnotation" #[highTypeToArg ty]))
      let initOpt := optionArg (init.map fun e => laurelOp "initializer" #[stmtExprToArg e])
      laurelOp "varDecl" #[ident name.text, typeOpt, initOpt]
    | .Assign [target] value =>
      laurelOp "assign" #[stmtExprToArg target, stmtExprToArg value]
    | .Assign targets value =>
      -- Multi-target assign: emit as assign of first target (best effort)
      match targets with
      | [] => laurelOp "assign" #[laurelOp "identifier" #[ident "_"], stmtExprToArg value]
      | t :: _ => laurelOp "assign" #[stmtExprToArg t, stmtExprToArg value]
    | .FieldSelect target field =>
      laurelOp "fieldAccess" #[stmtExprToArg target, ident field.text]
    | .StaticCall callee args =>
      let calleeArg := laurelOp "identifier" #[ident callee.text]
      let argsArr := args.map stmtExprToArg |>.toArray
      laurelOp "call" #[calleeArg, commaSep argsArr]
    | .PrimitiveOp op [a] =>
      laurelOp (operationName op) #[stmtExprToArg a]
    | .PrimitiveOp op [a, b] =>
      laurelOp (operationName op) #[stmtExprToArg a, stmtExprToArg b]
    | .PrimitiveOp op args =>
      -- Fallback for unusual arities
      let argsArr := args.map stmtExprToArg |>.toArray
      laurelOp (operationName op) argsArr
    | .IfThenElse cond thenBr elseBr =>
      let elseOpt := optionArg (elseBr.map fun e => laurelOp "elseBranch" #[stmtExprToArg e])
      laurelOp "ifThenElse" #[stmtExprToArg cond, stmtExprToArg thenBr, elseOpt]
    | .While cond invs _decreases body =>
      let invArgs := invs.map (fun i => laurelOp "invariantClause" #[stmtExprToArg i]) |>.toArray
      laurelOp "while" #[stmtExprToArg cond, seqArg invArgs, stmtExprToArg body]
    | .Return (some value) => laurelOp "return" #[stmtExprToArg value]
    | .Return none => laurelOp "return" #[laurelOp "block" #[semicolonSep #[]]]
    | .Exit label => laurelOp "exit" #[ident label]
    | .Assert cond => laurelOp "assert" #[stmtExprToArg cond, optionArg none]
    | .Assume cond => laurelOp "assume" #[stmtExprToArg cond]
    | .New name => laurelOp "new" #[ident name.text]
    | .This => laurelOp "identifier" #[ident "this"]
    | .IsType target ty =>
      match ty.val with
      | .UserDefined name => laurelOp "isType" #[stmtExprToArg target, ident name.text]
      | _ => laurelOp "isType" #[stmtExprToArg target, ident "Unknown"]
    | .AsType target ty =>
      match ty.val with
      | .UserDefined name => laurelOp "asType" #[stmtExprToArg target, ident name.text]
      | _ => laurelOp "asType" #[stmtExprToArg target, ident "Unknown"]
    | .InstanceCall target callee args =>
      -- Emit as a static call on target.callee(args)
      let calleeExpr := laurelOp "fieldAccess" #[stmtExprToArg target, ident callee.text]
      let argsArr := args.map stmtExprToArg |>.toArray
      laurelOp "call" #[calleeExpr, commaSep argsArr]
    | .Forall param trigger body =>
      let trigOpt := optionArg (trigger.map fun t => laurelOp "trigger" #[stmtExprToArg t])
      laurelOp "forallExpr" #[ident param.name.text, highTypeToArg param.type, trigOpt, stmtExprToArg body]
    | .Exists param trigger body =>
      let trigOpt := optionArg (trigger.map fun t => laurelOp "trigger" #[stmtExprToArg t])
      laurelOp "existsExpr" #[ident param.name.text, highTypeToArg param.type, trigOpt, stmtExprToArg body]
    | .ReferenceEquals lhs rhs =>
      laurelOp "eq" #[stmtExprToArg lhs, stmtExprToArg rhs]
    | .Assigned name => laurelOp "call" #[laurelOp "identifier" #[ident "assigned"], commaSep #[stmtExprToArg name]]
    | .Old value => laurelOp "call" #[laurelOp "identifier" #[ident "old"], commaSep #[stmtExprToArg value]]
    | .Fresh value => laurelOp "call" #[laurelOp "identifier" #[ident "fresh"], commaSep #[stmtExprToArg value]]
    | .ProveBy value _proof => stmtExprValToArg value.val
    | .ContractOf _type fn => stmtExprValToArg fn.val
    | .Abstract => laurelOp "identifier" #[ident "abstract"]
    | .All => laurelOp "identifier" #[ident "all"]
    | .PureFieldUpdate target field value =>
      -- Not directly in grammar; emit as assignment to field
      laurelOp "assign" #[
        laurelOp "fieldAccess" #[stmtExprToArg target, ident field.text],
        stmtExprToArg value
      ]

private def parameterToArg (p : Parameter) : Arg :=
  laurelOp "parameter" #[ident p.name.text, highTypeToArg p.type]

private def fieldToArg (f : Field) : Arg :=
  if f.isMutable then
    laurelOp "mutableField" #[ident f.name.text, highTypeToArg f.type]
  else
    laurelOp "immutableField" #[ident f.name.text, highTypeToArg f.type]

private def requiresClauseToArg (e : StmtExprMd) : Arg :=
  let errOpt := optionArg (e.md.getPropertySummary.map fun msg =>
    laurelOp "errorSummary" #[.strlit sr msg])
  laurelOp "requiresClause" #[stmtExprToArg e, errOpt]

private def ensuresClauseToArg (e : StmtExprMd) : Arg :=
  let errOpt := optionArg (e.md.getPropertySummary.map fun msg =>
    laurelOp "errorSummary" #[.strlit sr msg])
  laurelOp "ensuresClause" #[stmtExprToArg e, errOpt]

private def modifiesClauseToArg (modifies : List StmtExprMd) : Arg :=
  let refs := modifies.map stmtExprToArg |>.toArray
  laurelOp "modifiesClause" #[commaSep refs]

private def procedureToOp (proc : Procedure) : Strata.Operation :=
  let opName := if proc.isFunctional then "function" else "procedure"
  let params := proc.inputs.map parameterToArg |>.toArray
  let returnTypeArg : Arg :=
    match proc.outputs with
    | [single] => optionArg (some (laurelOp "returnType" #[highTypeToArg single.type]))
    | _ => optionArg none
  let returnParamsArg : Arg :=
    match proc.outputs with
    | [_] => optionArg none
    | _ =>
      if proc.outputs.isEmpty then optionArg none
      else optionArg (some (laurelOp "returnParameters" #[commaSep (proc.outputs.map parameterToArg |>.toArray)]))
  let requiresArgs := proc.preconditions.map requiresClauseToArg |>.toArray
  let invokeOnArg := optionArg (proc.invokeOn.map fun e =>
    laurelOp "invokeOnClause" #[stmtExprToArg e])
  let (ensuresArgs, modifiesArgs, bodyArg) := match proc.body with
    | .Transparent body =>
      (#[], #[], optionArg (some (laurelOp "body" #[stmtExprToArg body])))
    | .Opaque postconds impl modifies =>
      let ens := postconds.map ensuresClauseToArg |>.toArray
      let mods := if modifies.isEmpty then #[] else #[modifiesClauseToArg modifies]
      let body := optionArg (impl.map fun e => laurelOp "body" #[stmtExprToArg e])
      (ens, mods, body)
    | .Abstract postconds =>
      let ens := postconds.map ensuresClauseToArg |>.toArray
      (ens, #[], optionArg none)
    | .External =>
      (#[], #[], optionArg (some (laurelOp "externalBody")))
  { ann := sr
    name := { dialect := "Laurel", name := opName }
    args := #[
      ident proc.name.text,
      commaSep params,
      returnTypeArg,
      returnParamsArg,
      seqArg requiresArgs,
      invokeOnArg,
      seqArg ensuresArgs,
      seqArg modifiesArgs,
      bodyArg
    ] }

private def compositeToOp (ct : CompositeType) : Strata.Operation :=
  let extendsArg := if ct.extending.isEmpty then
    optionArg none
  else
    optionArg (some (laurelOp "extends" #[commaSep (ct.extending.map (fun e => ident e.text) |>.toArray)]))
  let fields := ct.fields.map fieldToArg |>.toArray
  let procs := ct.instanceProcedures.map (fun p => .op (procedureToOp p)) |>.toArray
  let compositeOp : Strata.Operation :=
    { ann := sr
      name := { dialect := "Laurel", name := "composite" }
      args := #[ident ct.name.text, extendsArg, seqArg fields, seqArg procs] }
  { ann := sr
    name := { dialect := "Laurel", name := "compositeCommand" }
    args := #[.op compositeOp] }

private def datatypeConstructorToArg (c : DatatypeConstructor) : Arg :=
  if c.args.isEmpty then
    laurelOp "datatypeConstructorNoArgs" #[ident c.name.text]
  else
    let args := c.args.map parameterToArg |>.toArray
    laurelOp "datatypeConstructor" #[ident c.name.text, commaSep args]

private def datatypeToOp (dt : DatatypeDefinition) : Strata.Operation :=
  let ctors := dt.constructors.map datatypeConstructorToArg |>.toArray
  let ctorList := laurelOp "datatypeConstructorList" #[commaSep ctors]
  let datatypeOp : Strata.Operation :=
    { ann := sr
      name := { dialect := "Laurel", name := "datatype" }
      args := #[ident dt.name.text, ctorList] }
  { ann := sr
    name := { dialect := "Laurel", name := "datatypeCommand" }
    args := #[.op datatypeOp] }

private def constrainedTypeToOp (ct : ConstrainedType) : Strata.Operation :=
  let ctOp : Strata.Operation :=
    { ann := sr
      name := { dialect := "Laurel", name := "constrainedType" }
      args := #[
        ident ct.name.text,
        ident ct.valueName.text,
        highTypeToArg ct.base,
        stmtExprToArg ct.constraint,
        stmtExprToArg ct.witness
      ] }
  { ann := sr
    name := { dialect := "Laurel", name := "constrainedTypeCommand" }
    args := #[.op ctOp] }

private def typeDefinitionToOp : TypeDefinition → Strata.Operation
  | .Composite ct => compositeToOp ct
  | .Constrained ct => constrainedTypeToOp ct
  | .Datatype dt => datatypeToOp dt

private def procedureCommandOp (proc : Procedure) : Strata.Operation :=
  { ann := sr
    name := { dialect := "Laurel", name := "procedureCommand" }
    args := #[.op (procedureToOp proc)] }

/-- Convert a Laurel.Program to a Strata.Program (DDM concrete syntax tree).
    The resulting program can be formatted using `Strata.Program.format` to
    produce Laurel source text. -/
def programToStrata (prog : Laurel.Program) : Strata.Program :=
  let typeOps := prog.types.map typeDefinitionToOp |>.toArray
  let procOps := prog.staticProcedures.map procedureCommandOp |>.toArray
  Strata.Program.create Laurel_map "Laurel" (typeOps ++ procOps)

open Std (Format format)
open Std.Format

/-- Format a HighType as Laurel syntax. `TTypedField` and `TSet` retain their
    type parameters here (e.g. `Field[T]`, `Set[T]`) for readability, even though
    the grammar cannot represent them. -/
partial def fmtHighType (t : HighTypeMd) : Format :=
  match t.val with
  | .TVoid => "void"
  | .TBool => "bool"
  | .TInt => "int"
  | .TFloat64 => "float64"
  | .TReal => "real"
  | .TString => "string"
  | .THeap => "Heap"
  | .TTypedField vt => "Field[" ++ fmtHighType vt ++ "]"
  | .TSet et => "Set[" ++ fmtHighType et ++ "]"
  | .TMap k v => "Map " ++ fmtHighType k ++ " " ++ fmtHighType v
  | .UserDefined name => format name.text
  | .Applied base _args => fmtHighType base
  | .Pure base => fmtHighType base
  | .Intersection types =>
    match types with
    | [] => "Unknown"
    | t :: _ => fmtHighType t
  | .TCore s => "Core " ++ format s
  | .Unknown => "Unknown"

private def fmtParam (p : Parameter) : Format :=
  format p.name.text ++ ": " ++ fmtHighType p.type

private def fmtOp : Laurel.Operation → Format
  | .Eq => " == " | .Neq => " != " | .And => " & " | .Or => " | "
  | .AndThen => " && " | .OrElse => " || " | .Not => "!"
  | .Implies => " ==> " | .Neg => "-" | .Add => " + "
  | .Sub => " - " | .Mul => " * " | .Div => " / " | .Mod => " % "
  | .DivT => " /t " | .ModT => " %t " | .Lt => " < " | .Leq => " <= "
  | .Gt => " > " | .Geq => " >= " | .StrConcat => " ++ "

/-- Format a StmtExpr as valid Laurel DDM syntax. -/
partial def fmtExpr (s : StmtExprMd) : Format := fmtExprVal s.val
where
  fmtExprVal : StmtExpr → Format
    | .LiteralBool b => if b then "true" else "false"
    | .LiteralInt n => format (toString n)
    | .LiteralDecimal d => format (toString d)
    | .LiteralString s => "\"" ++ format s ++ "\""
    | .Hole true _ => "<?>"
    | .Hole false _ => "<??>"
    | .Identifier name => format name.text
    | .Block stmts label =>
      let body := joinSep (stmts.map fmtExpr) (";" ++ line)
      let lbl := match label with | none => "" | some l => format l
      group ("{" ++ nestD (line ++ body) ++ line ++ "}" ++ lbl)
    | .LocalVariable name ty init =>
      "var " ++ format name.text ++ ": " ++ fmtHighType ty ++
      match init with
      | none => ""
      | some e => " := " ++ fmtExpr e
    | .Assign [target] value =>
      fmtExpr target ++ " := " ++ fmtExpr value
    | .Assign targets value =>
      "(" ++ joinSep (targets.map fmtExpr) ", " ++ ") := " ++ fmtExpr value
    | .FieldSelect target field =>
      fmtExpr target ++ "#" ++ format field.text
    | .StaticCall callee args =>
      format callee.text ++ "(" ++ joinSep (args.map fmtExpr) ", " ++ ")"
    | .PrimitiveOp op [a] => fmtOp op ++ fmtExpr a
    | .PrimitiveOp op [a, b] => fmtExpr a ++ fmtOp op ++ fmtExpr b
    | .PrimitiveOp op args =>
      fmtOp op ++ "(" ++ joinSep (args.map fmtExpr) ", " ++ ")"
    | .IfThenElse cond thenBr elseBr =>
      "if " ++ fmtExpr cond ++ " then " ++ fmtExpr thenBr ++
      match elseBr with
      | none => ""
      | some e => " else " ++ fmtExpr e
    | .While cond invs _decreases body =>
      "while(" ++ fmtExpr cond ++ ")" ++
      join (invs.map fun i => line ++ "  invariant " ++ fmtExpr i) ++
      line ++ fmtExpr body
    | .Return (some value) => "return " ++ fmtExpr value
    | .Return none => "return"
    | .Exit label => "exit " ++ format label
    | .Assert cond => "assert " ++ fmtExpr cond
    | .Assume cond => "assume " ++ fmtExpr cond
    | .New name => "new " ++ format name.text
    | .This => "this"
    | .IsType target ty =>
      fmtExpr target ++ " is " ++ fmtHighType ty
    | .AsType target ty =>
      fmtExpr target ++ " as " ++ fmtHighType ty
    | .InstanceCall target callee args =>
      fmtExpr target ++ "#" ++ format callee.text ++ "(" ++
      joinSep (args.map fmtExpr) ", " ++ ")"
    | .Forall param trigger body =>
      let trigFmt := match trigger with
        | some t => "{" ++ fmtExpr t ++ "}"
        | none => ""
      "forall(" ++ format param.name.text ++ ": " ++ fmtHighType param.type ++ ")" ++ trigFmt ++ " => " ++ fmtExpr body
    | .Exists param trigger body =>
      let trigFmt := match trigger with
        | some t => "{" ++ fmtExpr t ++ "}"
        | none => ""
      "exists(" ++ format param.name.text ++ ": " ++ fmtHighType param.type ++ ")" ++ trigFmt ++ " => " ++ fmtExpr body
    | .ReferenceEquals lhs rhs => fmtExpr lhs ++ " == " ++ fmtExpr rhs
    | .Assigned name => "assigned(" ++ fmtExpr name ++ ")"
    | .Old value => "old(" ++ fmtExpr value ++ ")"
    | .Fresh value => "fresh(" ++ fmtExpr value ++ ")"
    | .ProveBy value _proof => fmtExprVal value.val
    | .ContractOf _type fn => fmtExprVal fn.val
    | .Abstract => "abstract"
    | .All => "all"
    | .PureFieldUpdate target field value =>
      fmtExpr target ++ " with { " ++ format field.text ++ " := " ++ fmtExpr value ++ " }"

private def fmtField (f : Field) : Format :=
  (if f.isMutable then "var " else "") ++ format f.name.text ++ ": " ++ fmtHighType f.type

private def fmtErrSummary (e : StmtExprMd) : Format :=
  match e.md.getPropertySummary with
  | none => ""
  | some msg => " summary \"" ++ format msg ++ "\""

private def fmtProcedure (proc : Procedure) : Format :=
  let keyword := if proc.isFunctional then "function " else "procedure "
  let params := joinSep (proc.inputs.map fmtParam) ", "
  let retType := match proc.outputs with
    | [single] => ": " ++ fmtHighType single.type
    | _ => if proc.outputs.isEmpty then Format.nil
           else " returns (" ++ joinSep (proc.outputs.map fmtParam) ", " ++ ")"
  let requires := join (proc.preconditions.map fun p =>
    line ++ "  requires " ++ fmtExpr p ++ fmtErrSummary p)
  let invokeOn := match proc.invokeOn with
    | none => Format.nil
    | some e => line ++ "  invokeOn " ++ fmtExpr e
  let (ensures_, modifies_, bodyFmt) := match proc.body with
    | .Transparent body =>
      (Format.nil, Format.nil, line ++ fmtExpr body)
    | .Opaque postconds impl modifies =>
      let ens := join (postconds.map fun p =>
        line ++ "  ensures " ++ fmtExpr p ++ fmtErrSummary p)
      let mods := if modifies.isEmpty then Format.nil
        else line ++ "  modifies " ++ joinSep (modifies.map fmtExpr) ", "
      let body := match impl with
        | none => Format.nil
        | some e => line ++ fmtExpr e
      (ens, mods, body)
    | .Abstract postconds =>
      let ens := join (postconds.map fun p =>
        line ++ "  ensures " ++ fmtExpr p ++ fmtErrSummary p)
      (ens, Format.nil, Format.nil)
    | .External =>
      (Format.nil, Format.nil, line ++ "external")
  keyword ++ format proc.name.text ++ "(" ++ params ++ ")" ++ retType ++
  requires ++ invokeOn ++ ensures_ ++ modifies_ ++ bodyFmt ++ ";"

private def fmtComposite (ct : CompositeType) : Format :=
  let ext := if ct.extending.isEmpty then Format.nil
    else " extends " ++ joinSep (ct.extending.map fun e => format e.text) ", "
  let fields := join (ct.fields.map fun f => line ++ "  " ++ fmtField f)
  let procs := join (ct.instanceProcedures.map fun p => line ++ "  " ++ fmtProcedure p)
  "composite " ++ format ct.name.text ++ ext ++ " {" ++ fields ++ procs ++ line ++ "}"

private def fmtDatatypeCtor (c : DatatypeConstructor) : Format :=
  format c.name.text ++
  if c.args.isEmpty then Format.nil
  else "(" ++ joinSep (c.args.map fmtParam) ", " ++ ")"

private def fmtDatatype (dt : DatatypeDefinition) : Format :=
  "datatype " ++ format dt.name.text ++ " {" ++
  joinSep (dt.constructors.map fmtDatatypeCtor) ", " ++ "}"

private def fmtConstrainedType (ct : ConstrainedType) : Format :=
  "constrained " ++ format ct.name.text ++
  " = " ++ format ct.valueName.text ++ ": " ++ fmtHighType ct.base ++
  " where " ++ fmtExpr ct.constraint ++ " witness " ++ fmtExpr ct.witness

private def fmtTypeDefinition : TypeDefinition → Format
  | .Composite ct => fmtComposite ct
  | .Constrained ct => fmtConstrainedType ct
  | .Datatype dt => fmtDatatype dt

/-- Format a Laurel.Program as valid Laurel DDM concrete syntax text.
    The output can be parsed back by the Laurel parser. -/
def formatLaurelDDM (prog : Program) : Format :=
  let types := prog.types.map fmtTypeDefinition
  let procs := prog.staticProcedures.map fmtProcedure
  joinSep (types ++ procs) (line ++ line)

end

end Laurel
end Strata

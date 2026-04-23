/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Strata.DDM.Format
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

-- Internal-only: these are public because `mutual`/`partial` prevents `private`
mutual

partial def highTypeToArg (t : HighTypeMd) : Arg := highTypeValToArg t.val

partial def highTypeValToArg : HighType → Arg
  | .TInt => laurelOp "intType"
  | .TBool => laurelOp "boolType"
  | .TFloat64 => laurelOp "float64Type"
  | .TReal => laurelOp "realType"
  | .TString => laurelOp "stringType"
  | .TBv n => laurelOp "bvType" #[.num sr n]
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

-- Internal-only: public because `partial` prevents `private` in this section
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
    | .Assign targets value =>
      -- Grammar only supports single-target assign; use first target or placeholder
      let targetArg := match targets with
        | t :: _ => stmtExprToArg t
        | [] => laurelOp "identifier" #[ident "_"]
      laurelOp "assign" #[targetArg, stmtExprToArg value]
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
    | .Assert cond =>
      let errOpt := optionArg (cond.summary.map fun msg =>
        laurelOp "errorSummary" #[.strlit sr msg])
      laurelOp "assert" #[stmtExprToArg cond.condition, errOpt]
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

private def requiresClauseToArg (c : Condition) : Arg :=
  let errOpt := optionArg (c.summary.map fun msg =>
    laurelOp "errorSummary" #[.strlit sr msg])
  laurelOp "requiresClause" #[stmtExprToArg c.condition, errOpt]

private def ensuresClauseToArg (c : Condition) : Arg :=
  let errOpt := optionArg (c.summary.map fun msg =>
    laurelOp "errorSummary" #[.strlit sr msg])
  laurelOp "ensuresClause" #[stmtExprToArg c.condition, errOpt]

private def modifiesClausesToArgs (modifies : List StmtExprMd) : Array Arg :=
  let (wildcards, specific) := modifies.partition (fun m => match m.val with | .All => true | _ => false)
  let wildcardArgs := wildcards.map (fun _ => laurelOp "modifiesWildcard" #[]) |>.toArray
  let specificArgs := if specific.isEmpty then #[]
    else #[laurelOp "modifiesClause" #[commaSep (specific.map stmtExprToArg |>.toArray)]]
  wildcardArgs ++ specificArgs

private def procedureToOp (proc : Procedure) : Strata.Operation :=
  let opName := if proc.isFunctional then "function" else "procedure"
  let params := proc.inputs.map parameterToArg |>.toArray
  let returnTypeArg : Arg :=
    match proc.outputs with
    | [single] =>
      if single.name == "result"
      then optionArg (some (laurelOp "returnType" #[highTypeToArg single.type]))
      else optionArg none
    | _ => optionArg none
  let returnParamsArg : Arg :=
    match proc.outputs with
    | [single] =>
      if single.name == "result"
      then optionArg none
      else optionArg (some (laurelOp "returnParameters" #[commaSep #[parameterToArg single]]))
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
      let mods := if modifies.isEmpty then #[] else modifiesClausesToArgs modifies
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

private def datatypeConstructorArgToArg (p : Parameter) : Arg :=
  laurelOp "datatypeConstructorArg" #[ident p.name.text, highTypeToArg p.type]

private def datatypeConstructorToArg (c : DatatypeConstructor) : Arg :=
  if c.args.isEmpty then
    laurelOp "datatypeConstructorNoArgs" #[ident c.name.text]
  else
    let args := c.args.map datatypeConstructorArgToArg |>.toArray
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
  -- Placeholder: aliases are eliminated before CST serialization
  | .Alias _ => { ann := sr, name := { dialect := "Laurel", name := "typeAlias" }, args := #[] }

private def procedureCommandOp (proc : Procedure) : Strata.Operation :=
  { ann := sr
    name := { dialect := "Laurel", name := "procedureCommand" }
    args := #[.op (procedureToOp proc)] }

/-- Convert a Laurel.Program to a Strata.Program (DDM concrete syntax tree).
    The resulting program can be formatted using `Strata.Program.format` to
    produce Laurel source text.
    Note: `staticFields` and `constants` are not emitted because the Laurel
    grammar has no top-level commands for them. -/
def programToStrata (prog : Laurel.Program) : Strata.Program :=
  let typeOps := prog.types.map typeDefinitionToOp |>.toArray
  let procOps := prog.staticProcedures.map procedureCommandOp |>.toArray
  Strata.Program.create Laurel_map "Laurel" (typeOps ++ procOps)

/-- Format a Laurel program by converting to DDM concrete syntax and using the grammar-based formatter.
    This avoids duplicating the grammar in a separate formatter. -/
def formatProgram (prog : Laurel.Program) : Std.Format :=
  let sp := programToStrata prog
  let c := sp.formatContext {}
  let s := sp.formatState
  let fmts := sp.commands.map fun cmd => (Strata.mformat cmd c s).format
  Std.Format.joinSep fmts.toList "\n\n"

open Std (Format format)
open Std.Format

private def laurelFmtCtx : Strata.FormatContext :=
  Strata.FormatContext.ofDialects Laurel_map

private def laurelFmtState : Strata.FormatState where
  openDialects := ({} : Std.HashSet String).insert "Laurel"

private def formatArg (a : Arg) : Format :=
  (Strata.mformat a laurelFmtCtx laurelFmtState).format

private def formatOp (o : Strata.Operation) : Format :=
  (Strata.mformat o laurelFmtCtx laurelFmtState).format

def formatHighType (t : HighTypeMd) : Format := formatArg (highTypeToArg t)
def formatHighTypeVal (t : HighType) : Format := formatArg (highTypeValToArg t)
def formatStmtExpr (s : StmtExprMd) : Format := formatArg (stmtExprToArg s)
def formatStmtExprVal (s : StmtExpr) : Format := formatArg (stmtExprToArg ⟨s, none, {}⟩)
def formatParameter (p : Parameter) : Format := formatArg (parameterToArg p)
def formatField (f : Field) : Format := formatArg (fieldToArg f)
def formatDatatypeConstructor (c : DatatypeConstructor) : Format := formatArg (datatypeConstructorToArg c)
def formatProcedure (proc : Procedure) : Format := formatOp (procedureToOp proc)
def formatCompositeType (ct : CompositeType) : Format := formatOp (compositeToOp ct)
def formatConstrainedType (ct : ConstrainedType) : Format := formatOp (constrainedTypeToOp ct)
def formatDatatypeDefinition (dt : DatatypeDefinition) : Format := formatOp (datatypeToOp dt)

def formatTypeDefinition : TypeDefinition → Format
  | .Composite ty => formatCompositeType ty
  | .Constrained ty => formatConstrainedType ty
  | .Datatype ty => formatDatatypeDefinition ty
  | .Alias ta => "type " ++ format ta.name ++ " = " ++ formatHighType ta.target

def formatConstant (c : Constant) : Format :=
  "const " ++ format c.name ++ ": " ++ formatHighType c.type ++
  match c.initializer with
  | none => ""
  | some e => " := " ++ formatStmtExpr e

instance : Std.ToFormat HighTypeMd where format := formatHighType
instance : Std.ToFormat HighType where format := formatHighTypeVal
instance : Std.ToFormat StmtExprMd where format := formatStmtExpr
instance : Std.ToFormat StmtExpr where format := formatStmtExprVal
instance : Std.ToFormat Parameter where format := formatParameter
instance : Std.ToFormat Procedure where format := formatProcedure
instance : Std.ToFormat Field where format := formatField
instance : Std.ToFormat CompositeType where format := formatCompositeType
instance : Std.ToFormat ConstrainedType where format := formatConstrainedType
instance : Std.ToFormat DatatypeConstructor where format := formatDatatypeConstructor
instance : Std.ToFormat DatatypeDefinition where format := formatDatatypeDefinition
instance : Std.ToFormat Constant where format := formatConstant
instance : Std.ToFormat TypeDefinition where format := formatTypeDefinition
instance : Std.ToFormat Program where format := formatProgram

instance : Repr StmtExpr where
  reprPrec r _ := s!"{Std.format r}"

instance : Repr HighType where
  reprPrec r _ := s!"{Std.format r}"

deriving instance Repr for Strata.Laurel.Parameter
deriving instance Repr for Strata.Laurel.Procedure
deriving instance Repr for Strata.Laurel.Field
deriving instance Repr for Strata.Laurel.CompositeType
deriving instance Repr for Strata.Laurel.ConstrainedType
deriving instance Repr for Strata.Laurel.DatatypeConstructor
deriving instance Repr for Strata.Laurel.DatatypeDefinition
deriving instance Repr for Strata.Laurel.Constant

end

end Laurel
end Strata

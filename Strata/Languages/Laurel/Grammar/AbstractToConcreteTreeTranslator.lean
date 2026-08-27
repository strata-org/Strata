/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import Strata.Languages.Laurel.LaurelAST
import StrataDDM.Format
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Util.Tactics

namespace Strata
namespace Laurel

public section

open Strata (SourceRange)
open StrataDDM (QualifiedIdent Arg Operation SepFormat FormatContext FormatState)

private def sr : SourceRange := .none

private def laurelOp (name : String) (args : Array Arg := #[]) : Arg :=
  .op { ann := sr, name := { dialect := "Laurel", name := name }, args := args }

private def ident (s : String) : Arg := .ident sr s

private def optionArg (a : Option Arg) : Arg := .option sr a

private def commaSep (args : Array Arg) : Arg := .seq sr .comma args

private def semicolonSep (args : Array Arg) : Arg := .seq sr .semicolonNewline args

private def seqArg (args : Array Arg) : Arg := .seq sr .none args

-- Internal-only: these are public because `mutual` prevents `private`
mutual

def highTypeToArg (t : HighTypeMd) : Arg := highTypeValToArg t.val
  termination_by sizeOf t
  decreasing_by cases t; simp; omega

def highTypeValToArg : HighType → Arg
  | .TInt => laurelOp "intType"
  | .TBool => laurelOp "boolType"
  | .TFloat64 => laurelOp "float64Type"
  | .TReal => laurelOp "realType"
  | .TString => laurelOp "stringType"
  | .TBv n => laurelOp "bvType" #[.num sr n]
  | .TMap k v => laurelOp "mapType" #[highTypeToArg k, highTypeToArg v]
  | .UserDefined name => laurelOp "compositeType" #[ident name.text]
  -- A type variable renders as a bare identifier in type position; resolution
  -- reclassifies it back to `.TVar` when it matches an in-scope type parameter.
  | .TVar name => laurelOp "compositeType" #[ident name.text]
  | .TVoid => laurelOp "compositeType" #[ident "void"]
  -- Type parameters discarded; the grammar cannot represent Set[T]
  | .TSet _et => laurelOp "compositeType" #[ident "Set"]
  | .Applied base args =>
    -- Emit `Base<arg…>` as the grammar's `appliedType` op (whose name slot is an `Ident`,
    -- so peel the base to its name — mirrors `newTypeArgs`/`isType` emission). Emitting the
    -- args (not just the bare base) is what round-trips a generic `extends Base<T>`.
    match highBaseName? base.val with
    | some n => laurelOp "appliedType" #[ident n.text, commaSep (args.map highTypeToArg).toArray]
    | none => highTypeToArg base  -- unnameable base: best-effort (shouldn't occur)
  | .Intersection types =>
    match types with
    | [] => laurelOp "compositeType" #[ident "Unknown"]
    | t :: _ => highTypeToArg t
  | .Unknown => laurelOp "compositeType" #[ident "Unknown"]
  | .MultiValuedExpr _ => laurelOp "compositeType" #[ident "BUG_MultiValuedExpr"]
  termination_by t => sizeOf t
  decreasing_by
    -- The `.Applied` arm maps over the type-argument *list*, so its goal comes
    -- with an `x ∈ args` hypothesis; `term_by_mem` turns that into the size
    -- lemma. The remaining arms recurse into direct subterms.
    all_goals (try term_by_mem)
    all_goals (simp; try omega)

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

/-- Emit a chained-field-write target as a `FieldPath` op-chain, inverse of
    `translateFieldPath`. A pure identifier / field-access chain (`w#b#val`) maps to
    `fieldPathStep (… (fieldPathRoot w) …)`; returns `none` for any other shape (the
    caller falls back). -/
partial def fieldPathToArg : StmtExprMd → Option Arg
  | ⟨.Var (.Local name), _⟩ => some (laurelOp "fieldPathRoot" #[ident name.text])
  | ⟨.Var (.Field obj field), _⟩ => (fieldPathToArg obj).map fun o =>
      laurelOp "fieldPathStep" #[o, ident field.text]
  | _ => none

-- Internal-only: public because `partial` prevents `private` in this section
-- Printing never consults source locations, so this is defined on the bare
-- `StmtExpr`; `stmtExprToArg` below is the `StmtExprMd` wrapper.
partial def stmtExprValToArg (e : StmtExpr) : Arg :=
  go e
where
  stmtExprToArg (s : StmtExprMd) : Arg := go s.val
  variableToArg : Variable → Arg
    | .Local name => laurelOp "identifier" #[ident name.text]
    | .Field target field => laurelOp "fieldAccess" #[stmtExprToArg target, ident field.text]
    -- Declare is handled specially in the `Assign [⟨.Declare …⟩]` case of `go`.
    -- This fallback drops the type; it should not be reached in normal operation.
    | .Declare param => laurelOp "identifier" #[ident param.name.text]
  go : StmtExpr → Arg
    | .LiteralBool b => laurelOp "literalBool" #[boolToArg b]
    | .LiteralInt n =>
      match n with
      | .ofNat n => laurelOp "int" #[.num sr n]
      | .negSucc n => laurelOp "neg" #[laurelOp "int" #[.num sr (n + 1)]]
    | .LiteralDecimal d => laurelOp "real" #[.decimal sr d]
    | .LiteralString s => laurelOp "string" #[.strlit sr s]
    | .LiteralBv value width => laurelOp "bvLiteral" #[.num sr value, .num sr width]
    | .Hole true _ => laurelOp "hole"
    | .Hole false _ => laurelOp "nondetHole"
    | .Var (.Local name) => laurelOp "identifier" #[ident name.text]
    | .Block stmts label =>
      let stmtArgs := stmts.map stmtExprToArg |>.toArray
      match label with
      | none => laurelOp "block" #[semicolonSep stmtArgs]
      | some l => laurelOp "labelledBlock" #[semicolonSep stmtArgs, ident l]
    | .Var (.Declare param) =>
      let typeOpt := optionArg (param.type.map fun t => laurelOp "typeAnnotation" #[highTypeToArg t])
      let initOpt := optionArg none
      laurelOp "varDecl" #[ident param.name.text, typeOpt, initOpt]
    | .Assign [⟨.Declare param, _⟩] value =>
      let typeOpt := optionArg (param.type.map fun t => laurelOp "typeAnnotation" #[highTypeToArg t])
      let initOpt := optionArg (some (laurelOp "initializer" #[stmtExprToArg value]))
      laurelOp "varDecl" #[ident param.name.text, typeOpt, initOpt]
    | .Assign targets value =>
      if targets.length > 1 then
        let targetArgs := targets.map fun t =>
          match t.val with
          | .Declare ⟨name, ty?⟩ =>
            let typeOpt := optionArg (ty?.map fun t => laurelOp "typeAnnotation" #[highTypeToArg t])
            laurelOp "assignTargetDecl" #[ident name.text, typeOpt]
          | .Local name => laurelOp "assignTargetVar" #[ident name.text]
          | .Field target fieldName =>
            -- `obj` is a FieldPath: emit the path chain. A `w#b#val` target
            -- round-trips; a non-path object (shouldn't occur for a write target) falls
            -- back to the placeholder, as before.
            match fieldPathToArg target with
            | some pathArg => laurelOp "assignTargetField" #[pathArg, ident fieldName.text]
            | none => laurelOp "assignTargetVar" #[ident "_"]
        laurelOp "multiAssign" #[commaSep targetArgs.toArray, stmtExprToArg value]
      else
        let targetArg := match targets with
          | t :: _ => variableToArg t.val
          | [] => laurelOp "identifier" #[ident "_"]
        laurelOp "assign" #[targetArg, stmtExprToArg value]
    | .Var (.Field target field) =>
      laurelOp "fieldAccess" #[stmtExprToArg target, ident field.text]
    | .IncrDecr mode op target =>
      let opName := match mode, op with
        | .Pre,  .Incr => "preIncr"
        | .Pre,  .Decr => "preDecr"
        | .Post, .Incr => "postIncr"
        | .Post, .Decr => "postDecr"
      let targetArg := match target.val with
        | .Field obj fieldName =>
          laurelOp "fieldAccess" #[stmtExprToArg obj, ident fieldName.text]
        | .Local name => laurelOp "identifier" #[ident name.text]
        | .Declare param => laurelOp "identifier" #[ident param.name.text]
      laurelOp opName #[targetArg]
    | .CompoundAssign op target rhs =>
      -- `op` is invariably Add/Sub/Mul/Div/Mod/StrConcat (the C2A translator only
      -- builds those); the fallback emits a non-reparsing sentinel so a future
      -- miswiring fails the round-trip instead of silently masquerading as `+=`.
      let opName := match op with
        | .Add => "addAssign" | .Sub => "subAssign" | .Mul => "mulAssign"
        | .Div => "divAssign" | .Mod => "modAssign" | .StrConcat => "strConcatAssign"
        | _ => "invalidCompoundAssign"
      let targetArg := match target.val with
        | .Field obj fieldName =>
          laurelOp "fieldAccess" #[stmtExprToArg obj, ident fieldName.text]
        | .Local name => laurelOp "identifier" #[ident name.text]
        | .Declare param => laurelOp "identifier" #[ident param.name.text]
      laurelOp opName #[targetArg, stmtExprToArg rhs]
    | .StaticCall callee args =>
      -- A call to a built-in operator wrapper (`$add`, `$lt`, …) came from
      -- operator syntax, so print it back as an operator to round-trip.
      match Operation.ofProcName? callee.text, args with
      | some op, [a] => laurelOp (operationName op) #[stmtExprToArg a]
      | some op, [a, b] => laurelOp (operationName op) #[stmtExprToArg a, stmtExprToArg b]
      | _, _ =>
        let calleeArg := laurelOp "identifier" #[ident callee.text]
        let argsArr := args.map stmtExprToArg |>.toArray
        laurelOp "call" #[calleeArg, commaSep argsArr]
    | .IfThenElse cond thenBr elseBr =>
      let elseOpt := optionArg (elseBr.map fun e => laurelOp "elseBranch" #[stmtExprToArg e])
      laurelOp "ifThenElse" #[stmtExprToArg cond, stmtExprToArg thenBr, elseOpt]
    | .While cond invs _decreases body postTest =>
      let invArgs := invs.map (fun i => laurelOp "invariantClause" #[stmtExprToArg i]) |>.toArray
      if postTest then
        -- `do … while`; grammar op order is `doWhile(body, cond, invariants)`.
        laurelOp "doWhile" #[stmtExprToArg body, stmtExprToArg cond, seqArg invArgs]
      else
        laurelOp "while" #[stmtExprToArg cond, seqArg invArgs, stmtExprToArg body]
    | .Return (some value) => laurelOp "return" #[optionArg (some (stmtExprToArg value))]
    | .Return none => laurelOp "return" #[optionArg none]
    | .Yield => laurelOp "yield" #[]
    | .Resume target none =>
      laurelOp "call" #[laurelOp "identifier" #[ident "resume"], commaSep #[stmtExprToArg target]]
    | .Resume target (some value) =>
      laurelOp "call" #[laurelOp "identifier" #[ident "resume"], commaSep #[stmtExprToArg target, stmtExprToArg value]]
    | .HasNext target =>
      laurelOp "call" #[laurelOp "identifier" #[ident "has_next"], commaSep #[stmtExprToArg target]]
    | .Exit label => laurelOp "exit" #[ident label]
    | .Assert cond summary =>
      let errOpt := optionArg (summary.map fun msg =>
        laurelOp "errorSummary" #[.strlit sr msg])
      laurelOp "assert" #[stmtExprToArg cond, errOpt]
    | .Assume cond => laurelOp "assume" #[stmtExprToArg cond]
    | .Throw value => laurelOp "throw" #[stmtExprToArg value]
    | .Try body catches finally? =>
      let catchArgs := catches.map (fun c =>
        let guardArg := optionArg (c.predicate.map fun p => laurelOp "catchGuard" #[stmtExprToArg p])
        laurelOp "catchClause" #[ident c.binding.text, guardArg, stmtExprToArg c.body]) |>.toArray
      let finallyArg := optionArg (finally?.map fun f => laurelOp "finallyClause" #[stmtExprToArg f])
      laurelOp "tryCatch" #[stmtExprToArg body, seqArg catchArgs, finallyArg]
    | .New name typeArgs =>
      let typeArgsArg := optionArg (if typeArgs.isEmpty then none
        else some (laurelOp "newTypeArgs" #[commaSep (typeArgs.map (fun t => highTypeToArg t)).toArray]))
      laurelOp "new" #[ident name.text, typeArgsArg]
    | .This => laurelOp "identifier" #[ident "this"]
    | .IsType target ty =>
      laurelOp "isType" #[stmtExprToArg target, highTypeToArg ty]
    | .AsType target ty =>
      laurelOp "asType" #[stmtExprToArg target, highTypeToArg ty]
    | .InstanceCall target callee args =>
      -- Emit as a static call on target.callee(args)
      let calleeExpr := laurelOp "fieldAccess" #[stmtExprToArg target, ident callee.text]
      let argsArr := args.map stmtExprToArg |>.toArray
      laurelOp "call" #[calleeExpr, commaSep argsArr]
    | .Quantifier mode param trigger body =>
      let trigOpt := optionArg (trigger.map fun t => laurelOp "trigger" #[stmtExprToArg t])
      let opName := match mode with | .Forall => "forallExpr" | .Exists => "existsExpr"
      laurelOp opName #[ident param.name.text, highTypeToArg param.type, trigOpt, stmtExprToArg body]
    | .ReferenceEquals lhs rhs =>
      laurelOp "eq" #[stmtExprToArg lhs, stmtExprToArg rhs]
    | .Assigned name => laurelOp "call" #[laurelOp "identifier" #[ident "assigned"], commaSep #[stmtExprToArg name]]
    | .Old value none => laurelOp "old" #[stmtExprToArg value]
    -- A labeled `old` has no surface syntax (a transient lowering artifact);
    -- printed as a call only for `.laurel.st` debug dumps.
    | .Old value (some label) =>
      laurelOp "call" #[laurelOp "identifier" #[ident "oldAt"], commaSep #[laurelOp "identifier" #[ident label.text], stmtExprToArg value]]
    | .OldGuarantee value => laurelOp "oldGuarantee" #[stmtExprToArg value]
    | .OldRelies value => laurelOp "oldRelies" #[stmtExprToArg value]
    -- No surface syntax (a transient lowering artifact); printed as a call
    -- only for `.laurel.st` debug dumps.
    | .Snapshot label =>
      laurelOp "call" #[laurelOp "identifier" #[ident "snapshot"], commaSep #[laurelOp "identifier" #[ident label.text]]]
    | .Fresh value => laurelOp "call" #[laurelOp "identifier" #[ident "fresh"], commaSep #[stmtExprToArg value]]
    | .ProveBy value _proof => go value.val
    | .ContractOf _type fn => go fn.val
    | .Abstract => laurelOp "identifier" #[ident "abstract"]
    | .All => laurelOp "identifier" #[ident "all"]
    | .PureFieldUpdate target field value =>
      -- Not directly in grammar; emit as assignment to field
      laurelOp "assign" #[
        laurelOp "fieldAccess" #[stmtExprToArg target, ident field.text],
        stmtExprToArg value
      ]

-- Internal-only: public because `partial` prevents `private` in this section
def stmtExprToArg (s : StmtExprMd) : Arg := stmtExprValToArg s.val

private def parameterToArg (p : Parameter) : Arg :=
  laurelOp "parameter" #[ident p.name.text, highTypeToArg p.type]

private def fieldToArg (f : Field) : Arg :=
  if f.isMutable then
    laurelOp "mutableField" #[ident f.name.text, highTypeToArg f.type]
  else
    laurelOp "immutableField" #[ident f.name.text, highTypeToArg f.type]

/-- Pick the clause op name for a condition's `mode`. `Both` is the plain
    clause, `Assume` the `free` form, and `Assert` the `checked` form. -/
private def clauseOpName (base : String) : ConditionMode → String
  | .Both => base
  | .Assume => "free" ++ base.capitalize
  | .Assert => "checked" ++ base.capitalize

private def requiresClauseToArg (c : Condition) : Arg :=
  let errOpt := optionArg (c.summary.map fun msg =>
    laurelOp "errorSummary" #[.strlit sr msg])
  laurelOp (clauseOpName "requiresClause" c.mode) #[stmtExprToArg c.condition, errOpt]

private def errorSummaryToArg (summary : Option String) : Arg :=
  optionArg (summary.map fun msg => laurelOp "errorSummary" #[.strlit sr msg])

private def ensuresClauseToArg (c : Condition) : Arg :=
  laurelOp (clauseOpName "ensuresClause" c.mode)
    #[stmtExprToArg c.condition, errorSummaryToArg c.summary]

private def modifiesTargetsToArgs (targets : List StmtExprMd) : Array Arg :=
  let (wildcards, specific) := targets.partition StmtExprMd.isWildcard
  let wildcardArgs := wildcards.map (fun _ => laurelOp "modifiesWildcard" #[]) |>.toArray
  let specificArgs := if specific.isEmpty then #[]
    else #[laurelOp "modifiesClause" #[commaSep (specific.map stmtExprToArg |>.toArray)]]
  wildcardArgs ++ specificArgs

/-- Guards have no *authored* syntax (only passes create them), so a guarded
    group prints its guard as a `when`-suffixed clause via `modifiesWhenClause`.
    The clause is a real grammar op that `ConcreteToAbstractTreeTranslator`
    parses back — the round-trip is deliberate, so between-pass output stays
    loadable; do not drop either side. An unguarded group prints exactly as
    before. -/
private def modifiesClausesToArgs (groups : List ModifiesGroup) : Array Arg :=
  groups.foldl (init := #[]) fun acc g =>
    match g.guard with
    | none => acc ++ modifiesTargetsToArgs g.targets
    | some guard =>
      acc.push (laurelOp "modifiesWhenClause"
        #[commaSep (g.targets.map stmtExprToArg |>.toArray), stmtExprToArg guard])

/-- Emit the `Option TypeParams` slot: `none` for monomorphic, else
    `<T, U>`. Position matches the grammar (right after the name). -/
private def typeParamsToArg (typeArgs : List Identifier) : Arg :=
  if typeArgs.isEmpty then optionArg none
  else optionArg (some (laurelOp "typeParams"
    #[commaSep (typeArgs.map (fun t => ident t.text) |>.toArray)]))

private def procedureToOp (proc : Procedure) : StrataDDM.Operation :=
  let params := proc.inputs.map parameterToArg |>.toArray
  let returnTypeArg : Arg :=
    match proc.outputs with
    | [single] =>
      if single.name.text == resultOutputName
      then optionArg (some (laurelOp "returnType" #[highTypeToArg single.type]))
      else optionArg none
    | _ => optionArg none
  let returnParamsArg : Arg :=
    match proc.outputs with
    | [single] =>
      if single.name.text == resultOutputName
      then optionArg none
      else optionArg (some (laurelOp "returnParameters" #[commaSep #[parameterToArg single]]))
    | _ =>
      if proc.outputs.isEmpty then optionArg none
      else optionArg (some (laurelOp "returnParameters" #[commaSep (proc.outputs.map parameterToArg |>.toArray)]))
  let requiresArgs := proc.preconditions.map requiresClauseToArg |>.toArray
  -- `throws` carries the binding as well as the type. The two are set together by
  -- the parser (one op), and `EliminateExceptions` clears them together, so the
  -- fallback name below is unreachable for anything this printer is given.
  let throwsArg := optionArg (proc.throwsType.map fun t =>
    laurelOp "throwsClause"
      #[ident (proc.throwsBinding.map (·.text) |>.getD "e"), highTypeToArg t])
  let throwsOnArgs := proc.throwsOn.map (fun blk =>
    let ens := blk.postconditions.map (fun c =>
      laurelOp "throwsOnEnsures" #[stmtExprToArg c.condition, errorSummaryToArg c.summary])
    let mods := if blk.modifies.isEmpty then []
      else [laurelOp "throwsOnModifies" #[commaSep (blk.modifies.map stmtExprToArg |>.toArray)]]
    laurelOp "throwsOnClause"
      #[stmtExprToArg blk.guard, seqArg (ens ++ mods).toArray]) |>.toArray
  let invokeOnArg := optionArg (proc.invokeOn.map fun e =>
    laurelOp "invokeOnClause" #[stmtExprToArg e])
  let entryArg := optionArg (if proc.isInterpretEntry then some (laurelOp "entryClause" #[]) else none)
  -- The exceptional behavior cases live inside `opaqueSpec` alongside
  -- `ensures`/`modifies`, so they are emitted with it. (A `.Transparent` body has
  -- no spec block to carry them; such a procedure cannot be written in the
  -- surface grammar, since these cases require `opaque`.)
  let (opaqueSpecArg, bodyArg) := match proc.body with
    | .Transparent body =>
      (optionArg none, optionArg (some (laurelOp "body" #[stmtExprToArg body])))
    | .Opaque postconds impl modifies =>
      let ens := postconds.map ensuresClauseToArg |>.toArray
      let mods := if modifies.isEmpty then #[] else modifiesClausesToArgs modifies
      let body := optionArg (impl.map fun e => laurelOp "body" #[stmtExprToArg e])
      (optionArg (some (laurelOp "opaqueSpec"
        #[seqArg ens, seqArg mods, seqArg throwsOnArgs])), body)
    | .Abstract postconds =>
      let ens := postconds.map ensuresClauseToArg |>.toArray
      (optionArg (some (laurelOp "opaqueSpec"
        #[seqArg ens, seqArg #[], seqArg throwsOnArgs])), optionArg none)
    | .External =>
      (optionArg none, optionArg (some (laurelOp "externalBody")))
  { ann := sr
    name := { dialect := "Laurel", name := "procedure" }
    args := #[
      ident proc.name.text,
      typeParamsToArg proc.typeArgs,
      commaSep params,
      returnTypeArg,
      returnParamsArg,
      throwsArg,
      seqArg requiresArgs,
      invokeOnArg,
      entryArg,
      opaqueSpecArg,
      bodyArg
    ] }

private def compositeToOp (ct : CompositeType) : StrataDDM.Operation :=
  let extendsArg := if ct.extending.isEmpty then
    optionArg none
  else
    -- `extending` is now `List HighTypeMd`: emit each parent as a full type (a bare
    -- `Base` renders via `compositeType`, a generic `Base<T>` via `appliedType`).
    optionArg (some (laurelOp "extends" #[commaSep (ct.extending.map highTypeToArg |>.toArray)]))
  let fields := ct.fields.map fieldToArg |>.toArray
  let procs := ct.instanceProcedures.map (fun p => .op (procedureToOp p)) |>.toArray
  let compositeOp : StrataDDM.Operation :=
    { ann := sr
      name := { dialect := "Laurel", name := "composite" }
      args := #[ident ct.name.text, typeParamsToArg ct.typeArgs, extendsArg, seqArg fields, seqArg procs] }
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

private def datatypeToOp (dt : DatatypeDefinition) : StrataDDM.Operation :=
  let ctors := dt.constructors.map datatypeConstructorToArg |>.toArray
  let ctorList := laurelOp "datatypeConstructorList" #[commaSep ctors]
  let datatypeOp : StrataDDM.Operation :=
    { ann := sr
      name := { dialect := "Laurel", name := "datatype" }
      args := #[ident dt.name.text, typeParamsToArg dt.typeArgs, ctorList] }
  { ann := sr
    name := { dialect := "Laurel", name := "datatypeCommand" }
    args := #[.op datatypeOp] }

private def constrainedTypeToOp (ct : ConstrainedType) : StrataDDM.Operation :=
  let ctOp : StrataDDM.Operation :=
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

private def typeDefinitionToOp : TypeDefinition → StrataDDM.Operation
  | .Composite ct => compositeToOp ct
  | .Constrained ct => constrainedTypeToOp ct
  | .Datatype dt => datatypeToOp dt
  | .Alias ta =>
    let aliasOp : StrataDDM.Operation :=
      { ann := sr
        name := { dialect := "Laurel", name := "typeAlias" }
        args := #[ident ta.name.text, typeParamsToArg ta.typeArgs, highTypeToArg ta.target] }
    { ann := sr
      name := { dialect := "Laurel", name := "typeAliasCommand" }
      args := #[.op aliasOp] }
  | .Opaque ot =>
    let opaqueOp : StrataDDM.Operation :=
      { ann := sr
        name := { dialect := "Laurel", name := "opaqueType" }
        args := #[ident ot.name.text, typeParamsToArg ot.typeArgs] }
    { ann := sr
      name := { dialect := "Laurel", name := "opaqueTypeCommand" }
      args := #[.op opaqueOp] }

private def procedureCommandOp (proc : Procedure) : StrataDDM.Operation :=
  { ann := sr
    name := { dialect := "Laurel", name := "procedureCommand" }
    args := #[.op (procedureToOp proc)] }

private def globalVarCommandOp (f : Field) : StrataDDM.Operation :=
  { ann := sr
    name := { dialect := "Laurel", name := "globalVarCommand" }
    args := #[ident f.name.text, highTypeToArg f.type,
              optionArg (f.initializer.map fun value =>
                laurelOp "initializer" #[stmtExprToArg value])] }

/-- Convert a Laurel.Program to a StrataDDM.Program (DDM concrete syntax tree).
    The resulting program can be formatted using `StrataDDM.Program.format` to
    produce Laurel source text.
    Note: `constants` are not emitted because the Laurel grammar has no
    top-level command for them. `staticFields` are emitted as `globalVarCommand`s
    so that a program with globals round-trips through source. -/
def programToStrata (prog : Laurel.Program) : StrataDDM.Program :=
  let fieldOps := prog.staticFields.map globalVarCommandOp |>.toArray
  let typeOps := prog.types.map typeDefinitionToOp |>.toArray
  let procOps := prog.staticProcedures.map procedureCommandOp |>.toArray
  StrataDDM.Program.create Laurel_map "Laurel" (fieldOps ++ typeOps ++ procOps)

/-- Format a Laurel program by converting to DDM concrete syntax and using the grammar-based formatter.
    This avoids duplicating the grammar in a separate formatter. -/
def formatProgram (prog : Laurel.Program) : Std.Format :=
  let sp := programToStrata prog
  let c := sp.formatContext {}
  let s := sp.formatState
  let fmts := sp.commands.map fun cmd => (StrataDDM.mformat cmd c s).format
  Std.Format.joinSep fmts.toList "\n\n"

open Std (Format format)
open Std.Format

private def laurelFmtCtx : FormatContext :=
  FormatContext.ofDialects Laurel_map

private def laurelFmtState : FormatState where
  openDialects := ({} : Std.HashSet String).insert "Laurel"

private def formatArg (a : Arg) : Format :=
  (StrataDDM.mformat a laurelFmtCtx laurelFmtState).format

private def formatOp (o : StrataDDM.Operation) : Format :=
  (StrataDDM.mformat o laurelFmtCtx laurelFmtState).format

def formatHighType (t : HighTypeMd) : Format := formatArg (highTypeToArg t)
def formatHighTypeVal (t : HighType) : Format := formatArg (highTypeValToArg t)
def formatStmtExpr (s : StmtExprMd) : Format := formatArg (stmtExprToArg s)
def formatStmtExprVal (s : StmtExpr) : Format := formatArg (stmtExprValToArg s)
def formatParameter (p : Parameter) : Format := formatArg (parameterToArg p)
def formatField (f : Field) : Format := formatArg (fieldToArg f)
def formatDatatypeConstructor (c : DatatypeConstructor) : Format := formatArg (datatypeConstructorToArg c)
def formatProcedure (proc : Procedure) : Format := formatOp (procedureToOp proc)
def formatCompositeType (ct : CompositeType) : Format := formatOp (compositeToOp ct)
def formatConstrainedType (ct : ConstrainedType) : Format := formatOp (constrainedTypeToOp ct)
def formatDatatypeDefinition (dt : DatatypeDefinition) : Format := formatOp (datatypeToOp dt)
def formatOpaqueTypeDefinition (ot : OpaqueTypeDefinition) : Format :=
  formatOp (typeDefinitionToOp (.Opaque ot))

def formatTypeDefinition : TypeDefinition → Format
  | .Composite ty => formatCompositeType ty
  | .Constrained ty => formatConstrainedType ty
  | .Datatype ty => formatDatatypeDefinition ty
  -- Emit via the op path (like the other type defs) so the target type uses the grammar's
  -- `typeAlias` arg slot — re-parseable — rather than `formatHighType`'s parenthesized form.
  | .Alias ta => formatOp (typeDefinitionToOp (.Alias ta))
  | .Opaque ot => formatOpaqueTypeDefinition ot

def formatVariable (v : Variable) : Format :=
  formatArg (stmtExprValToArg (.Var v))

def formatVariableMd (v : VariableMd) : Format :=
  formatArg (stmtExprToArg ⟨.Var v.val, v.source⟩)

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
instance : Std.ToFormat OpaqueTypeDefinition where format := formatOpaqueTypeDefinition
instance : Std.ToFormat Variable where format := formatVariable
instance : Std.ToFormat VariableMd where format := formatVariableMd
instance : Std.ToFormat Constant where format := formatConstant
instance : Std.ToFormat TypeDefinition where format := formatTypeDefinition
instance : Std.ToFormat Program where format := formatProgram

instance : Repr StmtExpr where
  reprPrec r _ := s!"{Std.format r}"

instance : Repr HighType where
  reprPrec r _ := s!"{Std.format r}"

deriving instance Repr for Strata.Laurel.ConditionMode
deriving instance Repr for Strata.Laurel.Parameter
-- `Condition` and `Body` used to get their `Repr` derived implicitly, as members
-- of the same `mutual` clique as `Procedure`, when `Procedure` was derived below.
-- `Procedure` now lives outside that block, so derive them explicitly and in
-- dependency order (`Body` carries `List Condition`) before the types that use them.
deriving instance Repr for Strata.Laurel.Condition
deriving instance Repr for Strata.Laurel.Body
deriving instance Repr for Strata.Laurel.ThrowsOnBlock
deriving instance Repr for Strata.Laurel.CoroutineContracts
deriving instance Repr for Strata.Laurel.Procedure
deriving instance Repr for Strata.Laurel.Field
deriving instance Repr for Strata.Laurel.CompositeType
deriving instance Repr for Strata.Laurel.ConstrainedType
deriving instance Repr for Strata.Laurel.DatatypeConstructor
deriving instance Repr for Strata.Laurel.DatatypeDefinition
deriving instance Repr for Strata.Laurel.OpaqueTypeDefinition
deriving instance Repr for Strata.Laurel.Constant

end

end Laurel
end Strata

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import Strata.Languages.Laurel.LaurelAST

namespace Strata
namespace Laurel

public section

open Std (ToFormat Format format)
open Strata (Uri FileRange SourceRange)
open StrataDDM (QualifiedIdent Arg Decimal)
open Lean.Parser (InputContext)
open Imperative (MetaData)

structure TransState where
  /-- The file the program being translated came from. Compiler-embedded
      preludes name their defining `.lean` file and set `synthesized`. -/
  uri : Uri
  /-- True when the source is a compiler-embedded prelude rather than a user
      file. Only affects the Core `MetaData` provenance; `FileRange`s still
      name `uri` so every AST node carries a real file. -/
  synthesized : Bool := false
  errors : Array String

@[expose] abbrev TransM := StateT TransState (Except String)

def TransM.run (uri : Uri) (m : TransM α) (synthesized : Bool := false) : Except String α :=
  match StateT.run m { uri := uri, synthesized := synthesized, errors := #[] } with
  | .ok (v, _) => .ok v
  | .error e => .error e

def TransM.error (msg : String) : TransM α :=
  throw msg

private def SourceRange.toFileRange (uri : Uri) (sr : SourceRange) : FileRange :=
  ⟨ uri, sr ⟩

private def getArgFileRange (arg : Arg) : TransM FileRange := do
  return SourceRange.toFileRange (← get).uri arg.ann

def getArgMetaData (arg : Arg) : TransM (Imperative.MetaData Core.Expression) := do
  let s ← get
  return if s.synthesized then
    Imperative.MetaData.ofProvenance (.synthesized .laurelParse)
  else
    Imperative.MetaData.ofSourceRange s.uri arg.ann

def checkOp (op : StrataDDM.Operation) (name : QualifiedIdent) (argc : Nat) :
  TransM Unit := do
  if op.name != name then
    TransM.error s!"Op name mismatch! \n\
                   Name: {repr name}\n\
                   Op: {repr op}"
  if op.args.size != argc then
    TransM.error s!"Op arg count mismatch! \n\
                   Expected: {argc}\n\
                   Got: {op.args.size}\n\
                   Op: {repr op}"
  return ()

def translateIdent (arg : Arg) : TransM Identifier := do
  let .ident _ id := arg
    | TransM.error s!"translateIdent expects ident"
  let source ← getArgFileRange arg
  return { text := id, source := source }

def translateBool (arg : Arg) : TransM Bool := do
  match arg with
  | .expr (.fn _ name) =>
    match name with
    | q`Init.boolTrue => return true
    | q`Init.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr name}"
  | .op op =>
    match op.name with
    | q`Init.boolTrue => return true
    | q`Init.boolFalse => return false
    | _ => TransM.error s!"translateBool expects boolTrue or boolFalse, got {repr op.name}"
  | x => TransM.error s!"translateBool expects expression or operation, got {repr x}"

instance : Inhabited Parameter where
  default := { name := "" , type := default }

def mkHighTypeMd (t : HighType) (source : FileRange) : HighTypeMd := { val := t, source := source }
def mkStmtExprMd (e : StmtExpr) (source : FileRange) : StmtExprMd := { val := e, source := source }

def translateNat (arg : Arg) : TransM Nat := do
  let .num _ n := arg
    | TransM.error s!"translateNat expects num literal"
  return n

def translateHighType (arg : Arg) : TransM HighTypeMd := do
  let src ← getArgFileRange arg
  match _harg : arg with
  | .op op =>
    -- Dispatch on the operator name via `if` chains and match `op.args.toList`;
    -- this structure lets Lean generate the match equations needed for
    -- well-founded recursion.
    if op.name == q`Laurel.intType then return mkHighTypeMd .TInt src
    else if op.name == q`Laurel.boolType then return mkHighTypeMd .TBool src
    else if op.name == q`Laurel.float64Type then return mkHighTypeMd .TFloat64 src
    else if op.name == q`Laurel.realType then return mkHighTypeMd .TReal src
    else if op.name == q`Laurel.stringType then return mkHighTypeMd .TString src
    else if op.name == q`Laurel.bvType then
      match op.args.toList with
      | [widthArg] =>
        let width ← translateNat widthArg
        return mkHighTypeMd (.TBv width) src
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else if op.name == q`Laurel.coreType then
      match op.args.toList with
      | [.ident _ name] => return mkHighTypeMd (.UserDefined name) src
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else if op.name == q`Laurel.mapType then
      match _hargs : op.args.toList with
      | [keyArg, valArg] =>
        let keyType ← translateHighType keyArg
        let valType ← translateHighType valArg
        return mkHighTypeMd (.TMap keyType valType) src
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else if op.name == q`Laurel.compositeType then
      match op.args.toList with
      | [nameArg] =>
        let name ← translateIdent nameArg
        return mkHighTypeMd (.UserDefined name) src
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else if op.name == q`Laurel.appliedType then
      match _hargsApp : op.args.toList with
      | [baseArg, argsArg] =>
        let base ← translateIdent baseArg
        -- The type arguments arrive as one `CommaSepBy` arg: a `.seq` for two or
        -- more, the bare type itself for one. Both recurse (a type argument can
        -- be another application, `Option<Option<int>>`); `attach` carries each
        -- element's membership proof for the termination argument.
        let args ← match _hseqApp : argsArg with
          | .seq _ .comma elems => elems.toList.attach.mapM (fun ⟨a, _⟩ => translateHighType a)
          | _ => do let a ← translateHighType argsArg; pure [a]
        return mkHighTypeMd (.Applied (mkHighTypeMd (.UserDefined base) src) args) src
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else if op.name == q`Laurel.parenType then
      -- Parenthesized type: unwrap to the inner type. Parens carry no semantics;
      -- they exist only so the pretty-printer's parenthesization of a non-atomic
      -- type (e.g. `(Option<int>)`) re-parses.
      match _hargsParen : op.args.toList with
      | [innerArg] => translateHighType innerArg
      | _ => TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
    else TransM.error s!"translateHighType: unsupported type operator {repr op.name}"
  | _ => TransM.error s!"translateHighType expects operation"
  termination_by sizeOf arg
  decreasing_by
    -- `mapType`: two direct args of `op`.
    all_goals (try (
      have hmk : keyArg ∈ op.args := by
        have h1 : keyArg ∈ op.args.toList := by simp [_hargs]
        simpa using h1
      have hmv : valArg ∈ op.args := by
        have h1 : valArg ∈ op.args.toList := by simp [_hargs]
        simpa using h1
      have h2k := Array.sizeOf_lt_of_mem hmk
      have h2v := Array.sizeOf_lt_of_mem hmv
      subst _harg
      cases op
      simp at h2k h2v ⊢
      omega))
    -- `appliedType`, one type argument: the argument arg itself is a direct arg.
    all_goals (try (
      have hm : argsArg ∈ op.args := by
        have h1 : argsArg ∈ op.args.toList := by simp [_hargsApp, _hseqApp]
        simpa using h1
      have h2 := Array.sizeOf_lt_of_mem hm
      subst _harg
      cases op
      simp at h2 ⊢
      omega))
    -- `appliedType`, two or more: element of the `.seq` that is a direct arg, so
    -- the chain is element < seq elements < op.args < the `.op` node.
    all_goals (try (
      have hmem : a ∈ elems := by simpa using ‹a ∈ elems.toList›
      have h1 := Array.sizeOf_lt_of_mem hmem
      have hm : argsArg ∈ op.args := by
        have h := show argsArg ∈ op.args.toList by simp [_hargsApp, _hseqApp]
        simpa using h
      have h2 := Array.sizeOf_lt_of_mem hm
      subst _harg
      cases op
      simp [_hseqApp] at h1 h2 ⊢
      omega))
    -- `parenType`: the inner type is a direct arg.
    all_goals (try (
      have hm : innerArg ∈ op.args := by
        have h1 : innerArg ∈ op.args.toList := by simp [_hargsParen]
        simpa using h1
      have h2 := Array.sizeOf_lt_of_mem hm
      subst _harg
      cases op
      simp at h2 ⊢
      omega))


def translateString (arg : Arg) : TransM String := do
  let .strlit _ s := arg
    | TransM.error s!"translateString expects string literal"
  return s

def translateDecimal (arg : Arg) : TransM Decimal := do
  let .decimal _ d := arg
    | TransM.error s!"translateDecimal expects decimal literal"
  return d

def translateParameter (arg : Arg) : TransM Parameter := do
  let .op op := arg
    | TransM.error s!"translateParameter expects operation"
  match op.name, op.args with
  | q`Laurel.parameter, #[arg0, arg1] =>
    let name ← translateIdent arg0
    let paramType ← translateHighType arg1
    return { name := name, type := paramType }
  | q`Laurel.parameter, args =>
    TransM.error s!"parameter needs two arguments, not {args.size}"
  | _, _ =>
    TransM.error s!"translateParameter expects parameter operation, got {repr op.name}"

def translateParameters (arg : Arg) : TransM (List Parameter) := do
  match arg with
  | .seq _ .comma args =>
    args.toList.mapM translateParameter
  | _ => pure []

instance : Inhabited Procedure where
  default := {
    name := ""
    inputs := []
    outputs := []
    preconditions := []
    decreases := none
    invokeOn := none
    body := .Transparent { val := .LiteralBool true, source := default }
  }

def getBinaryOp? (name : QualifiedIdent) : Option Operation :=
  match name with
  | q`Laurel.add => some Operation.Add
  | q`Laurel.sub => some Operation.Sub
  | q`Laurel.mul => some Operation.Mul
  | q`Laurel.div => some Operation.Div
  | q`Laurel.mod => some Operation.Mod
  | q`Laurel.divT => some Operation.DivT
  | q`Laurel.modT => some Operation.ModT
  | q`Laurel.eq => some Operation.Eq
  | q`Laurel.neq => some Operation.Neq
  | q`Laurel.gt => some Operation.Gt
  | q`Laurel.lt => some Operation.Lt
  | q`Laurel.le => some Operation.Leq
  | q`Laurel.ge => some Operation.Geq
  | q`Laurel.and => some Operation.And
  | q`Laurel.or => some Operation.Or
  | q`Laurel.andThen => some Operation.AndThen
  | q`Laurel.orElse => some Operation.OrElse
  | q`Laurel.implies => some Operation.Implies
  | q`Laurel.strConcat => some Operation.StrConcat
  | _ => none

def getUnaryOp? (name : QualifiedIdent) : Option Operation :=
  match name with
  | q`Laurel.not => some Operation.Not
  | q`Laurel.neg => some Operation.Neg
  | _ => none

/-- Translate a `Seq InvariantClause` into the list of invariant conditions,
    using `translate` for each clause body. Shared by the `while`, `forLoop`,
    and `doWhile` arms. Takes `translate` as a parameter so it can stay outside
    the `translateStmtExpr` mutual block and thus be a total `def`. -/
def translateInvariantClauses (translate : Arg → TransM StmtExprMd) (arg : Arg) :
    TransM (List StmtExprMd) := do
  match arg with
  | .seq _ _ clauses => clauses.toList.mapM fun clause => match clause with
      | .op invOp => match invOp.name, invOp.args with
        | q`Laurel.invariantClause, #[exprArg] => translate exprArg
        | _, _ => TransM.error "Expected invariantClause"
      | _ => TransM.error "Expected operation"
  | _ => pure []

mutual

partial def translateStmtExpr (arg : Arg) : TransM StmtExprMd := do
  let src ← getArgFileRange arg
  match arg with
  | .op op => match op.name, op.args with
    | q`Laurel.assert, #[arg0, errMsgArg] =>
      let cond ← translateStmtExpr arg0
      let summary ← match errMsgArg with
        | .option _ (some (.op errOp)) => match errOp.name, errOp.args with
          | q`Laurel.errorSummary, #[strArg] => do
            let msg ← translateString strArg
            pure (some msg)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.Assert cond summary) src
    | q`Laurel.assume, #[arg0] =>
      let cond ← translateStmtExpr arg0
      return mkStmtExprMd (.Assume cond) src
    | q`Laurel.throw, #[arg0] =>
      let value ← translateStmtExpr arg0
      return mkStmtExprMd (.Throw value) src
    | q`Laurel.tryCatch, #[bodyArg, catchSeqArg, finallyArg] =>
      let body ← translateStmtExpr bodyArg
      let catches ← match catchSeqArg with
        | .seq _ _ clauses => clauses.toList.mapM fun arg => match arg with
            | .op cOp => match cOp.name, cOp.args with
              | q`Laurel.catchClause, #[bindingArg, guardArg, cBodyArg] => do
                let binding ← translateIdent bindingArg
                let predicate ← match guardArg with
                  | .option _ (some (.op gOp)) => match gOp.name, gOp.args with
                    | q`Laurel.catchGuard, #[pArg] => translateStmtExpr pArg >>= (pure ∘ some)
                    | _, _ => pure none
                  | _ => pure none
                let cBody ← translateStmtExpr cBodyArg
                pure ({ binding := binding, predicate := predicate, body := cBody } : CatchClause)
              | _, _ => TransM.error "Expected catchClause"
            | _ => TransM.error "Expected operation"
        | _ => pure []
      let finally? ← match finallyArg with
        | .option _ (some (.op fOp)) => match fOp.name, fOp.args with
          | q`Laurel.finallyClause, #[fBodyArg] => translateStmtExpr fBodyArg >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.Try body catches finally?) src
    | q`Laurel.block, #[arg0] =>
      let stmts ← translateSeqCommand arg0
      return mkStmtExprMd (.Block stmts none) src
    | q`Laurel.labelledBlock, #[arg0, arg1] =>
      let stmts ← translateSeqCommand arg0
      let label ← translateIdent arg1
      return mkStmtExprMd (.Block stmts (some label.text)) src
    | q`Laurel.exit, #[arg0] =>
      let label ← translateIdent arg0
      return mkStmtExprMd (.Exit label.text) src
    | q`Laurel.literalBool, #[arg0] => return mkStmtExprMd (.LiteralBool (← translateBool arg0)) src
    | q`Laurel.int, #[arg0] =>
      let n ← translateNat arg0
      return mkStmtExprMd (.LiteralInt n) src
    | q`Laurel.real, #[arg0] =>
      let d ← translateDecimal arg0
      return mkStmtExprMd (.LiteralDecimal d) src
    | q`Laurel.string, #[arg0] =>
      let s ← translateString arg0
      return mkStmtExprMd (.LiteralString s) src
    | q`Laurel.bvLiteral, #[valueArg, widthArg] =>
      let value ← translateNat valueArg
      let width ← translateNat widthArg
      return mkStmtExprMd (.LiteralBv value width) src
    | q`Laurel.hole, #[] => return mkStmtExprMd (.Hole true none) src
    | q`Laurel.nondetHole, #[] => return mkStmtExprMd (.Hole false none) src
    | q`Laurel.varDecl, #[arg0, typeArg, assignArg] =>
      let name ← translateIdent arg0
      -- The type annotation is optional. When absent, the declaration's type is
      -- recovered by the resolution pass: synthesized from the initializer for
      -- `var x := e`, or `Unknown` (with a diagnostic) for `var x`.
      let varType? ← match typeArg with
        | .option _ (some (.op typeOp)) => match typeOp.name, typeOp.args with
          | q`Laurel.typeAnnotation, #[typeArg0] => (some <$> translateHighType typeArg0)
          | _, _ => TransM.error s!"Variable {name} has a malformed type annotation"
        | .option _ none => pure none
        | _ => TransM.error s!"Variable {name} has a malformed type annotation"
      let value ← match assignArg with
        | .option _ (some (.op assignOp)) => match assignOp.args with
          | #[assignArg0] => translateStmtExpr assignArg0 >>= (pure ∘ some)
          | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
        | .option _ none => pure none
        | _ => TransM.error s!"assignArg {repr assignArg} didn't match expected pattern for variable {name}"
      match value with
      | some init => return mkStmtExprMd (.Assign [⟨.Declare ⟨name, varType?⟩, src⟩] init) src
      | none => return mkStmtExprMd (.Var (.Declare ⟨name, varType?⟩)) src
    | q`Laurel.identifier, #[arg0] =>
      let name ← translateIdent arg0
      return mkStmtExprMd (.Var (.Local name)) src
    | q`Laurel.parenthesis, #[arg0] => translateStmtExpr arg0
    | q`Laurel.assign, #[arg0, arg1] =>
      let target ← translateStmtExpr arg0
      let targetVar : VariableMd ← match target.val with
        | .Var v => pure ⟨v, target.source⟩
        | _ => TransM.error s!"assign target must be a variable or field access"
      let value ← translateStmtExpr arg1
      return mkStmtExprMd (.Assign [targetVar] value) src
    | q`Laurel.preIncr, #[arg0] =>
      let target ← translateIncrDecrTarget arg0 "preIncr"
      return mkStmtExprMd (.IncrDecr .Pre .Incr target) src
    | q`Laurel.preDecr, #[arg0] =>
      let target ← translateIncrDecrTarget arg0 "preDecr"
      return mkStmtExprMd (.IncrDecr .Pre .Decr target) src
    | q`Laurel.postIncr, #[arg0] =>
      let target ← translateIncrDecrTarget arg0 "postIncr"
      return mkStmtExprMd (.IncrDecr .Post .Incr target) src
    | q`Laurel.postDecr, #[arg0] =>
      let target ← translateIncrDecrTarget arg0 "postDecr"
      return mkStmtExprMd (.IncrDecr .Post .Decr target) src
    | q`Laurel.addAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "+="
      return mkStmtExprMd (.CompoundAssign .Add target (← translateStmtExpr arg1)) src
    | q`Laurel.subAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "-="
      return mkStmtExprMd (.CompoundAssign .Sub target (← translateStmtExpr arg1)) src
    | q`Laurel.mulAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "*="
      return mkStmtExprMd (.CompoundAssign .Mul target (← translateStmtExpr arg1)) src
    | q`Laurel.divAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "/="
      return mkStmtExprMd (.CompoundAssign .Div target (← translateStmtExpr arg1)) src
    | q`Laurel.modAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "%="
      return mkStmtExprMd (.CompoundAssign .Mod target (← translateStmtExpr arg1)) src
    | q`Laurel.strConcatAssign, #[arg0, arg1] =>
      let target ← translateIncrDecrTarget arg0 "^="
      return mkStmtExprMd (.CompoundAssign .StrConcat target (← translateStmtExpr arg1)) src
    | q`Laurel.multiAssign, #[targetsSeq, valueArg] =>
      let targets ← match targetsSeq with
        | .seq _ .comma args => args.toList.mapM fun targ => do
          let tSrc ← getArgFileRange targ
          let .op top := targ
            | TransM.error s!"multiAssign target expects operation"
          match top.name, top.args with
          | q`Laurel.assignTargetDecl, #[nameArg, typeArg] =>
            let name ← translateIdent nameArg
            -- Like varDecl's, the annotation is optional; resolution infers the type from the callee's corresponding output.
            let ty? ← match typeArg with
              | .option _ (some (.op typeOp)) => match typeOp.name, typeOp.args with
                | q`Laurel.typeAnnotation, #[typeArg0] => (some <$> translateHighType typeArg0)
                | _, _ => TransM.error s!"Assign target {name} has a malformed type annotation"
              | .option _ none => pure none
              | _ => TransM.error s!"Assign target {name} has a malformed type annotation"
            pure (⟨.Declare ⟨name, ty?⟩, tSrc⟩ : VariableMd)
          | q`Laurel.assignTargetVar, #[nameArg] =>
            let name ← translateIdent nameArg
            pure (⟨.Local name, tSrc⟩ : VariableMd)
          | q`Laurel.assignTargetField, #[objArg, fieldArg] =>
            let obj ← translateIdent objArg
            let field ← translateIdent fieldArg
            pure (⟨.Field ⟨.Var (.Local obj), tSrc⟩ field, tSrc⟩ : VariableMd)
          | _, _ => TransM.error s!"multiAssign: unexpected target {repr top.name}"
        | _ => pure []
      let value ← translateStmtExpr valueArg
      return mkStmtExprMd (.Assign targets value) src
    | q`Laurel.new, #[nameArg] =>
      let name ← translateIdent nameArg
      return mkStmtExprMd (.New name) src
    | q`Laurel.isType, #[targetArg, typeNameArg] =>
      let target ← translateStmtExpr targetArg
      let typeName ← translateIdent typeNameArg
      return mkStmtExprMd (.IsType target (mkHighTypeMd (.UserDefined typeName) src)) src
    | q`Laurel.asType, #[targetArg, typeNameArg] =>
      let target ← translateStmtExpr targetArg
      let typeName ← translateIdent typeNameArg
      return mkStmtExprMd (.AsType target (mkHighTypeMd (.UserDefined typeName) src)) src
    | q`Laurel.call, #[arg0, argsSeq] =>
      let callee ← translateStmtExpr arg0
      let argsList ← match argsSeq with
        | .seq _ .comma args => args.toList.mapM translateStmtExpr
        | _ => pure []
      -- `obj#method(args)` parses as `call(fieldAccess(obj, method), args)`.
      -- Treat such calls as instance-method calls; everything else stays a
      -- static call by callee text (empty when the callee is a higher-order
      -- expression — preserved to match prior behavior).
      match callee.val with
      | .Var (.Field target fieldName) =>
        return mkStmtExprMd (.InstanceCall target fieldName argsList) src
      | .Var (.Local name) =>
        return mkStmtExprMd (.StaticCall name argsList) src
      | _ =>
        return mkStmtExprMd (.StaticCall (mkId "") argsList) src
    | q`Laurel.return, #[arg0] =>
      let value ← match arg0 with
        | .option _ (some valArg) => some <$> translateStmtExpr valArg
        | _ => pure none
      return mkStmtExprMd (.Return value) src
    | q`Laurel.ifThenElse, #[arg0, arg1, elseArg] =>
      let cond ← translateStmtExpr arg0
      let thenBranch ← translateStmtExpr arg1
      let elseBranch ← match elseArg with
        | .option _ (some (.op elseOp)) => match elseOp.name, elseOp.args with
          | q`Laurel.elseBranch, #[elseArg0] => translateStmtExpr elseArg0 >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      return mkStmtExprMd (.IfThenElse cond thenBranch elseBranch) src
    | q`Laurel.fieldAccess, #[objArg, fieldArg] =>
      let obj ← translateStmtExpr objArg
      let field ← translateIdent fieldArg
      let fieldSrc ← getArgFileRange fieldArg
      return mkStmtExprMd (.Var (.Field obj field)) fieldSrc
    | q`Laurel.while, #[condArg, invSeqArg, bodyArg] =>
      let cond ← translateStmtExpr condArg
      let invariants ← translateInvariantClauses translateStmtExpr invSeqArg
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.While cond invariants none body false) src
    | q`Laurel.forLoop, #[initArg, condArg, stepArg, invSeqArg, bodyArg] =>
      let init ← translateStmtExpr initArg
      let cond ← translateStmtExpr condArg
      let step ← translateStmtExpr stepArg
      let invariants ← translateInvariantClauses translateStmtExpr invSeqArg
      let body ← translateStmtExpr bodyArg
      let whileBody := mkStmtExprMd (.Block [body, step] none) src
      let whileStmt := mkStmtExprMd (.While cond invariants none whileBody false) src
      return mkStmtExprMd (.Block [init, whileStmt] none) src
    | q`Laurel.doWhile, #[bodyArg, condArg, invSeqArg] =>
      -- A `do … while` is a post-test `While`. The `EliminateDoWhile` pass
      -- lowers `postTest := true` to the pre-test form later.
      let body ← translateStmtExpr bodyArg
      let cond ← translateStmtExpr condArg
      let invariants ← translateInvariantClauses translateStmtExpr invSeqArg
      return mkStmtExprMd (.While cond invariants none body (postTest := true)) src
    | q`Laurel.old, #[arg0] =>
      let inner ← translateStmtExpr arg0
      return mkStmtExprMd (.Old inner) src
    | q`Laurel.forallExpr, #[nameArg, tyArg, triggerArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let trigger ← match triggerArg with
        | .option _ (some (.op triggerOp)) => match triggerOp.name, triggerOp.args with
          | q`Laurel.trigger, #[triggerExprArg] =>
            translateStmtExpr triggerExprArg >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Quantifier .Forall { name := name, type := ty } trigger body) src
    | q`Laurel.existsExpr, #[nameArg, tyArg, triggerArg, bodyArg] =>
      let name ← translateIdent nameArg
      let ty ← translateHighType tyArg
      let trigger ← match triggerArg with
        | .option _ (some (.op triggerOp)) => match triggerOp.name, triggerOp.args with
          | q`Laurel.trigger, #[triggerExprArg] =>
            translateStmtExpr triggerExprArg >>= (pure ∘ some)
          | _, _ => pure none
        | _ => pure none
      let body ← translateStmtExpr bodyArg
      return mkStmtExprMd (.Quantifier .Exists { name := name, type := ty } trigger body) src
    -- Operators are calls to the built-in `$`-prefixed wrapper procedures
    -- (see `Operation.procName`), so there is no dedicated operator node.
    | _, #[arg0] => match getUnaryOp? op.name with
      | some primOp =>
        let inner ← translateStmtExpr arg0
        return mkStmtExprMd (.StaticCall (mkId primOp.procName) [inner]) src
      | none => TransM.error s!"Unknown unary operation: {op.name}"
    | _, #[arg0, arg1] => match getBinaryOp? op.name with
      | some primOp =>
        let lhs ← translateStmtExpr arg0
        let rhs ← translateStmtExpr arg1
        return mkStmtExprMd (.StaticCall (mkId primOp.procName) [lhs, rhs]) src
      | none => TransM.error s!"Unknown operation: {op.name}"
    | _, _ => TransM.error s!"Unknown operation: {op.name}"
  | _ => TransM.error s!"translateStmtExpr expects operation"

partial def translateSeqCommand (arg : Arg) : TransM (List StmtExprMd) := do
  let .seq _ _ args := arg
    | TransM.error s!"translateSeqCommand expects seq"
  let mut stmts : List StmtExprMd := []
  for arg in args do
    let stmt ← translateStmtExpr arg
    stmts := stmts ++ [stmt]
  return stmts

partial def translateCommand (arg : Arg) : TransM StmtExprMd := do
  translateStmtExpr arg

/--
Translate the target of an increment/decrement operator. The target must be an
lvalue: either a local variable reference (`Var (.Local _)`) or a field access
(`Var (.Field _ _)`). Anything else is reported as a translation error.
-/
partial def translateIncrDecrTarget (arg : Arg) (opName : String) : TransM VariableMd := do
  let inner ← translateStmtExpr arg
  match inner.val with
  | .Var v@(.Local _) => pure ⟨v, inner.source⟩
  | .Var v@(.Field _ _) => pure ⟨v, inner.source⟩
  | _ =>
    TransM.error s!"{opName} target must be a local variable or field access"

end

def translateModifiesExprs (arg : Arg) : TransM (List StmtExprMd) := do
  match arg with
  | .seq _ .comma args =>
    args.toList.mapM translateStmtExpr
  | _ => pure []

/-- User `modifies` clauses fold into a single unguarded `ModifiesGroup` — one
    frame, exactly the pre-guard semantics. A `modifiesWhenClause` (pass-generated,
    but parsed here so printed output round-trips) contributes its own guarded
    group. -/
def translateModifiesClauses (arg : Arg) : TransM (List ModifiesGroup) := do
  match arg with
  | .seq _ _ args => do
    let mut plainTargets : List StmtExprMd := []
    let mut guardedGroups : List ModifiesGroup := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp => match clauseOp.name, clauseOp.args with
        | q`Laurel.modifiesClause, #[refsArg] =>
          let refs ← translateModifiesExprs refsArg
          plainTargets := plainTargets ++ refs
        | q`Laurel.modifiesWildcard, #[] =>
          let src := SourceRange.toFileRange (← get).uri clauseOp.ann
          plainTargets := plainTargets ++ [mkStmtExprMd .All src]
        | q`Laurel.modifiesWhenClause, #[refsArg, guardArg] =>
          let refs ← translateModifiesExprs refsArg
          let guard ← translateStmtExpr guardArg
          guardedGroups := guardedGroups ++ [{ targets := refs, guard := some guard }]
        | _, _ => TransM.error s!"Expected modifiesClause operation, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected modifiesClause operation in modifies sequence"
    -- The plain group exists even with no clauses: for an opaque procedure, an
    -- absent `modifies` means "nothing may change", which is the empty frame —
    -- not the absence of one. (This function is only reached from an
    -- `opaqueSpec`, so the group never lands on a transparent body.)
    pure ({ targets := plainTargets : ModifiesGroup } :: guardedGroups)
  | _ => pure [{ targets := [] : ModifiesGroup }]

/-- Translate the optional `summary "..."` argument of a clause. -/
private def translateErrorSummary (errMsgArg : Arg) : TransM (Option String) := do
  match errMsgArg with
  | .option _ (some (.op errOp)) => match errOp.name, errOp.args with
    | q`Laurel.errorSummary, #[strArg] => do
      let msg ← translateString strArg
      pure (some msg)
    | _, _ => pure none
  | _ => pure none

def translateRequiresClauses (arg : Arg) : TransM (List Condition) := do
  match arg with
  | .seq _ _ args => do
    let mut allRequires : List Condition := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp =>
        -- All three variants share the `(cond, errorMessage)` shape; only the
        -- mode differs. `free` keeps the assumption, `checked` keeps the
        -- assertion, and the plain form keeps both.
        let mode ← match clauseOp.name with
          | q`Laurel.requiresClause => pure ConditionMode.Both
          | q`Laurel.freeRequiresClause => pure ConditionMode.Assume
          | q`Laurel.checkedRequiresClause => pure ConditionMode.Assert
          | _ => TransM.error s!"Expected requiresClause operation, got {repr clauseOp.name}"
        match clauseOp.args with
        | #[exprArg, errMsgArg] =>
          let expr ← translateStmtExpr exprArg
          let summary ← translateErrorSummary errMsgArg
          allRequires := allRequires ++ [{ condition := expr, summary, mode }]
        | _ => TransM.error s!"Expected requiresClause operation with 2 arguments, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected requiresClause operation in requires sequence"
    pure allRequires
  | _ => pure []

def translateEnsuresClauses (arg : Arg) : TransM (List Condition) := do
  match arg with
  | .seq _ _ args => do
    let mut allEnsures : List Condition := []
    for clauseArg in args do
      match clauseArg with
      | .op clauseOp =>
        let mode ← match clauseOp.name with
          | q`Laurel.ensuresClause => pure ConditionMode.Both
          | q`Laurel.freeEnsuresClause => pure ConditionMode.Assume
          | q`Laurel.checkedEnsuresClause => pure ConditionMode.Assert
          | _ => TransM.error s!"Expected ensuresClause operation, got {repr clauseOp.name}"
        match clauseOp.args with
        | #[exprArg, errMsgArg] =>
          let expr ← translateStmtExpr exprArg
          let summary ← translateErrorSummary errMsgArg
          allEnsures := allEnsures ++ [{ condition := expr, summary, mode }]
        | _ => TransM.error s!"Expected ensuresClause operation with 2 arguments, got {repr clauseOp.name}"
      | _ => TransM.error s!"Expected ensuresClause operation in ensures sequence"
    pure allEnsures
  | _ => pure []

/-- Translate the single-output `Laurel.returnType` op into the implicit
    `$result` output parameter.

    A producer may attach a source range only to the outer `returnType` op:
    the Java front-end builds the inner type op from a javac `Type`, which
    carries no tree position, so the inner op's range is the `SourceRange.none`
    sentinel. Fall back to the outer op's range in that case, so the `ensures`
    that `ConstrainedTypeElim` synthesizes for a constrained output type (e.g.
    `int32` for a Java `int`) inherits a real location — otherwise an implicit
    no-overflow failure is reported at the whole-file fallback position instead
    of at the return type.

    The jverify producer now stamps the declared type tree's range on the inner
    op itself (this CR's StrataJavaFrontEnd commit), so for current jverify the
    inner range wins and this fallback is a safety net — it remains load-bearing
    for other producers and previously-emitted Ion. -/
def translateSingleReturnType (returnTypeOp : StrataDDM.Operation) :
    TransM (List Parameter) := do
  match returnTypeOp.name, returnTypeOp.args with
  | q`Laurel.returnType, #[typeArg] =>
    let retType ← translateHighType typeArg
    let retType ← if retType.source.range.isNone then
        do pure { retType with source := ← getArgFileRange (.op returnTypeOp) }
      else pure retType
    pure [{ name := resultOutputName, type := retType : Parameter }]
  | _, _ => TransM.error s!"Expected optionalReturnType operation, got {repr returnTypeOp.name}"

def parseProcedure (arg : Arg) : TransM Procedure := do
  let .op op := arg
    | TransM.error s!"parseProcedure expects operation"

  -- Transitional shim: normalize legacy `procedure` shapes to the current
  -- 10-argument form (`… returnParameters throws requires invokeOn entry
  -- opaqueSpec body`). Older producers emitted either the pre-`entry` 8-arg
  -- shape or the pre-exception 9-arg shape (with `entry`), neither of which had
  -- any exceptional-contract clauses: splice in an absent `throws` before
  -- `requires`, and an absent `entry` where it is missing, so a post-CR binary
  -- can still consume Ion artifacts produced against a previous grammar. (The
  -- exceptional postcondition/frame clauses now live inside `opaqueSpec`, whose
  -- own legacy 2-argument shape is normalized where it is parsed below.)
  let absentOpt : Arg := .option SourceRange.none none
  let args : Array Arg ← match op.name, op.args with
    | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
        requiresArg, invokeOnArg, opaqueSpecArg, bodyArg] =>
      pure #[nameArg, paramArg, returnTypeArg, returnParamsArg,
             absentOpt, requiresArg, invokeOnArg, absentOpt,
             opaqueSpecArg, bodyArg]
    | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
        requiresArg, invokeOnArg, entryArg, opaqueSpecArg, bodyArg] =>
      pure #[nameArg, paramArg, returnTypeArg, returnParamsArg,
             absentOpt, requiresArg, invokeOnArg, entryArg,
             opaqueSpecArg, bodyArg]
    | _, other => pure other

  match op.name, args with
  | q`Laurel.procedure, #[nameArg, paramArg, returnTypeArg, returnParamsArg,
      throwsArg, requiresArg, invokeOnArg, entryArg, opaqueSpecArg, bodyArg] =>
    let name ← translateIdent nameArg
    let parameters ← translateParameters paramArg
    -- Either returnTypeArg or returnParamsArg may have a value, not both
    -- If returnTypeArg is set, create a single "result" parameter
    let returnParameters ← match returnTypeArg with
      | .option _ (some (.op returnTypeOp)) => translateSingleReturnType returnTypeOp
      | .option _ none =>
        -- No return type, check returnParamsArg instead
        match returnParamsArg with
        | .option _ (some (.op returnOp)) => match returnOp.name, returnOp.args with
          | q`Laurel.returnParameters, #[returnArg0] => translateParameters returnArg0
          | _, _ => TransM.error s!"Expected returnParameters operation, got {repr returnOp.name}"
        | .option _ none => pure []
        | _ => TransM.error s!"Expected returnParameters operation, got {repr returnParamsArg}"
      | _ => TransM.error s!"Expected optionalReturnType operation, got {repr returnTypeArg}"
    -- Parse preconditions (requires clauses - zero or more)
    let preconditions ← translateRequiresClauses requiresArg
    -- Parse the optional `throws (e: T)` clause, which names the thrown value as
    -- well as its type, scoping the name over the `throwsOn` blocks below. The two
    -- come from one op, so they are set or unset together.
    let (throwsType, throwsBinding) ← match throwsArg with
      | .option _ (some (.op throwsOp)) => match throwsOp.name, throwsOp.args with
        | q`Laurel.throwsClause, #[bindingArg, tyArg] => do
          let binding ← translateIdent bindingArg
          let ty ← translateHighType tyArg
          pure (some ty, some binding)
        | _, _ => TransM.error s!"Expected throwsClause, got {repr throwsOp.name}"
      | _ => pure (none, none)
    -- Parse optional invokeOn clause
    let invokeOn ← match invokeOnArg with
      | .option _ (some (.op invokeOnOp)) => match invokeOnOp.name, invokeOnOp.args with
        | q`Laurel.invokeOnClause, #[triggerExprArg] =>
          translateStmtExpr triggerExprArg >>= (pure ∘ some)
        | _, _ => TransM.error s!"Expected invokeOnClause operation, got {repr invokeOnOp.name}"
      | .option _ none => pure none
      | _ => pure none
    -- Parse optional entry marker (producer-set entry point for interpretation)
    let isInterpretEntry ← match entryArg with
      | .option _ (some (.op entryOp)) => match entryOp.name, entryOp.args with
        | q`Laurel.entryClause, #[] => pure true
        | _, _ => TransM.error s!"Expected entryClause operation, got {repr entryOp.name}"
      | .option _ none => pure false
      | _ => pure false
    -- An `entry`-marked procedure is invoked with no arguments by `runEntry`,
    -- so it cannot take inputs. Reject the combination here rather than
    -- silently running with unbound inputs at interpretation time.
    if isInterpretEntry && !parameters.isEmpty then
      TransM.error s!"entry procedure '{name.text}' cannot take inputs: \
                      an entry point is invoked with no arguments"
    -- Parse optional opaqueSpec: the caller-visible contract, holding the
    -- normal-path clauses (`ensures`, `modifies`) and the exceptional behavior
    -- cases (`throwsOn <guard> { ensures … modifies … }`).
    -- Transitional shim: a 2-argument `opaqueSpec` carries no exceptional cases
    -- and is read as having none.
    --
    -- One `throwsOn` block becomes one `ThrowsOnBlock`. Within a block the
    -- `ensures` clauses accumulate as postconditions and the `modifies` clauses
    -- union their refs, exactly as the normal-path clauses do at the top level.
    let parseThrowsOnClauses (a : Arg) : TransM (List Condition × List StmtExprMd) :=
      match a with
      | .seq _ _ clauses => do
        let mut posts : List Condition := []
        let mut mods : List StmtExprMd := []
        for arg in clauses do
          match arg with
          | .op cOp => match cOp.name, cOp.args with
            | q`Laurel.throwsOnEnsures, #[condArg, summaryArg] =>
              let condition ← translateStmtExpr condArg
              let summary ← translateErrorSummary summaryArg
              posts := posts ++ [({ condition := condition, summary := summary } : Condition)]
            | q`Laurel.throwsOnModifies, #[refsArg] =>
              let refs ← translateModifiesExprs refsArg
              mods := mods ++ refs
            | _, _ => TransM.error s!"Expected throwsOn ensures/modifies, got {repr cOp.name}"
          | _ => TransM.error "Expected operation in throwsOn clause sequence"
        pure (posts, mods)
      | _ => pure ([], [])
    let parseThrowsOn (a : Arg) : TransM (List ThrowsOnBlock) :=
      match a with
      | .seq _ _ blocks => blocks.toList.mapM fun arg => match arg with
          | .op bOp => match bOp.name, bOp.args with
            | q`Laurel.throwsOnClause, #[guardArg, clausesArg] => do
              let guard ← translateStmtExpr guardArg
              let (posts, mods) ← parseThrowsOnClauses clausesArg
              pure ({ guard := guard, postconditions := posts,
                      modifies := mods } : ThrowsOnBlock)
            | _, _ => TransM.error s!"Expected throwsOnClause, got {repr bOp.name}"
          | _ => TransM.error "Expected operation in throwsOn sequence"
      | _ => pure []
    let (isOpaque, postconditions, modifies, throwsOn) ←
      match opaqueSpecArg with
      | .option _ (some (.op opaqueSpecOp)) => match opaqueSpecOp.name, opaqueSpecOp.args with
        | q`Laurel.opaqueSpec, #[ensuresArg, modifiesArg, throwsOnArg] =>
          let postconditions ← translateEnsuresClauses ensuresArg
          let modifies ← translateModifiesClauses modifiesArg
          let throwsOn ← parseThrowsOn throwsOnArg
          pure (true, postconditions, modifies, throwsOn)
        | q`Laurel.opaqueSpec, #[ensuresArg, modifiesArg] =>
          -- Legacy (pre-exceptional-case) shape.
          let postconditions ← translateEnsuresClauses ensuresArg
          let modifies ← translateModifiesClauses modifiesArg
          pure (true, postconditions, modifies, [])
        | _, _ => TransM.error s!"Expected opaqueSpec operation, got {repr opaqueSpecOp.name}"
      | .option _ none => pure (false, [], [], [])
      | _ => pure (false, [], [], [])
    -- Parse optional body
    let isExternal ← match bodyArg with
      | .option _ (some (.op bodyOp)) => match bodyOp.name, bodyOp.args with
        | q`Laurel.externalBody, #[] => pure true
        | _, _ => pure false
      | _ => pure false
    let body ← match bodyArg with
      | .option _ (some (.op bodyOp)) => match bodyOp.name, bodyOp.args with
        | q`Laurel.body, #[exprArg] => translateCommand exprArg >>= (pure ∘ some)
        | q`Laurel.externalBody, #[] => pure none
        | _, _ => TransM.error s!"Expected body or externalBody operation, got {repr bodyOp.name}"
      | .option _ none => pure none
      | _ => TransM.error s!"Expected body, got {repr bodyArg}"
    -- Determine procedure body kind
    let procBody :=
      if isExternal then Body.External
      else if isOpaque then Body.Opaque postconditions body modifies
      else match body with
      | some b => Body.Transparent b
      | none => Body.Opaque [] none modifies
    return {
      name := name
      inputs := parameters
      outputs := returnParameters
      preconditions := preconditions
      decreases := none
      invokeOn := invokeOn
      isInterpretEntry := isInterpretEntry
      throwsType := throwsType
      throwsBinding := throwsBinding
      throwsOn := throwsOn
      body := procBody
    }
  | q`Laurel.procedure, args =>
    TransM.error s!"parseProcedure expects 8, 9, or 10 arguments, got {args.size}"
  | _, _ =>
    TransM.error s!"parseProcedure expects procedure, got {repr op.name}"

def parseField (arg : Arg) : TransM Field := do
  let .op op := arg
    | TransM.error s!"parseField expects operation"
  match op.name, op.args with
  | q`Laurel.mutableField, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let fieldType ← translateHighType typeArg
    return { name := name, isMutable := true, type := fieldType }
  | q`Laurel.immutableField, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let fieldType ← translateHighType typeArg
    return { name := name, isMutable := false, type := fieldType }
  | _, _ =>
    TransM.error s!"parseField expects mutableField or immutableField, got {repr op.name}"

def parseComposite (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseComposite expects operation"
  match op.name, op.args with
  | q`Laurel.composite, #[nameArg, extendsArg, fieldsArg, procsArg] =>
    let name ← translateIdent nameArg
    let extending ← match extendsArg with
      | .option _ (some (.op extendsOp)) => match extendsOp.name, extendsOp.args with
        | q`Laurel.extends, #[parentsArg] =>
          match parentsArg with
          | .seq _ .comma args => args.toList.mapM translateIdent
          | singleArg => do let parent ← translateIdent singleArg; pure [parent]
        | _, _ => TransM.error s!"Expected optionalExtends operation, got {repr extendsOp.name}"
      | .option _ none => pure []
      | _ => TransM.error s!"Expected optionalExtends, got {repr extendsArg}"
    let fields ← match fieldsArg with
      | .seq _ _ args => args.toList.mapM parseField
      | _ => pure []
    let instanceProcedures ← match procsArg with
      | .seq _ _ args => args.toList.mapM parseProcedure
      | _ => pure []
    return .Composite { name := name, extending := extending, fields := fields, instanceProcedures := instanceProcedures }
  | _, _ =>
    TransM.error s!"parseComposite expects composite, got {repr op.name}"

def parseDatatypeConstructorArg (arg : Arg) : TransM Parameter := do
  let .op op := arg
    | TransM.error s!"parseDatatypeConstructorArg expects operation"
  match op.name, op.args with
  | q`Laurel.datatypeConstructorArg, #[nameArg, typeArg] =>
    let name ← translateIdent nameArg
    let argType ← translateHighType typeArg
    return { name := name, type := argType }
  | _, _ =>
    TransM.error s!"parseDatatypeConstructorArg expects datatypeConstructorArg, got {repr op.name}"

def parseDatatypeConstructor (arg : Arg) : TransM DatatypeConstructor := do
  let .op op := arg
    | TransM.error s!"parseDatatypeConstructor expects operation"
  match op.name, op.args with
  | q`Laurel.datatypeConstructor, #[nameArg, argsSeq] =>
    let name ← translateIdent nameArg
    let args ← match argsSeq with
      | .seq _ .comma args => args.toList.mapM parseDatatypeConstructorArg
      | _ => pure []
    return { name := name, args := args }
  | q`Laurel.datatypeConstructorNoArgs, #[nameArg] =>
    let name ← translateIdent nameArg
    return { name := name, args := [] }
  | _, _ =>
    TransM.error s!"parseDatatypeConstructor expects datatypeConstructor, got {repr op.name}"

def parseDatatype (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseDatatype expects operation"
  -- Transitional shim: normalize the legacy pre-`typeParams` 2-argument datatype
  -- shape (`name, constructors`) to the current 3-argument form by splicing in an
  -- absent `typeParams` option. Mirrors `parseProcedure`'s cross-version shims so
  -- a post-CR binary can still consume Ion artifacts produced against the
  -- pre-generics grammar.
  let args : Array Arg ← match op.name, op.args with
    | q`Laurel.datatype, #[nameArg, constructorsArg] =>
      pure #[nameArg, .option SourceRange.none none, constructorsArg]
    | _, other => pure other
  match op.name, args with
  | q`Laurel.datatype, #[nameArg, typeParamsArg, constructorsArg] =>
    let name ← translateIdent nameArg
    let typeArgs ← match typeParamsArg with
      | .option _ (some (.op tpOp)) => match tpOp.name, tpOp.args with
        | q`Laurel.typeParams, #[paramsArg] =>
          match paramsArg with
          | .seq _ .comma args => args.toList.mapM translateIdent
          | singleArg => do let p ← translateIdent singleArg; pure [p]
        | _, _ => TransM.error s!"Expected typeParams, got {repr tpOp.name}"
      -- Only a genuinely-absent option means "no type parameters"; a present but
      -- malformed slot is a corrupt/unexpected artifact and must be rejected
      -- rather than silently coerced to zero type parameters.
      | .option _ none => pure []
      | other => TransM.error s!"parseDatatype: expected Option TypeParams, got {repr other}"
    let constructors ← match constructorsArg with
      | .op listOp => match listOp.name, listOp.args with
        | q`Laurel.datatypeConstructorList, #[csArg] =>
          match csArg with
          | .seq _ .comma args => args.toList.mapM parseDatatypeConstructor
          | singleArg => do let c ← parseDatatypeConstructor singleArg; pure [c]
        | _, _ => TransM.error s!"Expected datatypeConstructorList, got {repr listOp.name}"
      | _ => TransM.error s!"Expected datatypeConstructorList operation"
    return .Datatype { name := name, typeArgs := typeArgs, constructors := constructors }
  | _, _ =>
    TransM.error s!"parseDatatype expects datatype, got {repr op.name}"

def parseOpaqueType (arg : Arg) : TransM TypeDefinition := do
  let .op op := arg
    | TransM.error s!"parseOpaqueType expects operation"
  match op.name, op.args with
  | q`Laurel.opaqueType, #[nameArg] =>
    let name ← translateIdent nameArg
    return .Datatype { name := name, typeArgs := [], constructors := [] }
  | _, _ =>
    TransM.error s!"parseOpaqueType expects opaqueType, got {repr op.name}"

def parseConstrainedType (arg : Arg) : TransM ConstrainedType := do
  let .op op := arg
    | TransM.error s!"parseConstrainedType expects operation"
  match op.name, op.args with
  | q`Laurel.constrainedType, #[nameArg, valueNameArg, baseArg, constraintArg, witnessArg] =>
    let name ← translateIdent nameArg
    let valueName ← translateIdent valueNameArg
    let base ← translateHighType baseArg
    let constraint ← translateStmtExpr constraintArg
    let witness ← translateStmtExpr witnessArg
    return { name, base, valueName, constraint, witness }
  | _, _ =>
    TransM.error s!"parseConstrainedType expects constrainedType, got {repr op.name}"

/-- The result of translating one top-level command: at most one of a static
    procedure, a type definition, or a global (static) field. -/
private structure TopLevel where
  proc : Option Procedure := none
  type : Option TypeDefinition := none
  field : Option Field := none

private def parseTopLevelWithGlobals (arg : Arg) : TransM TopLevel := do
  let .op op := arg
    | TransM.error s!"parseTopLevel expects operation"

  match op.name, op.args with
  | q`Laurel.procedureCommand, #[procArg] =>
    let proc ← parseProcedure procArg
    return { proc := some proc }
  | q`Laurel.compositeCommand, #[compositeArg] =>
    let typeDef ← parseComposite compositeArg
    return { type := some typeDef }
  | q`Laurel.datatypeCommand, #[datatypeArg] =>
    let typeDef ← parseDatatype datatypeArg
    return { type := some typeDef }
  | q`Laurel.constrainedTypeCommand, #[ctArg] =>
    let ct ← parseConstrainedType ctArg
    return { type := some (.Constrained ct) }
  | q`Laurel.globalVarCommand, #[nameArg, typeArg, initArg] =>
    let name ← translateIdent nameArg
    let fieldType ← translateHighType typeArg
    let initializer ← match initArg with
      | .option _ (some (.op initOp)) => match initOp.name, initOp.args with
        | q`Laurel.initializer, #[valueArg] => translateStmtExpr valueArg
        | _, _ => TransM.error s!"global '{name.text}' has a malformed initializer"
      | .option _ none =>
        TransM.error s!"file-scope global '{name.text}' must declare an initializer: \
                        'var {name.text}: <type> := <value>'"
      | _ => TransM.error s!"global '{name.text}' has a malformed initializer"
    return { field := some { name := name, isMutable := true, type := fieldType,
                             initializer := some initializer } }
  | q`Laurel.globalVarCommand, #[nameArg, _typeArg] =>
    let name ← translateIdent nameArg
    TransM.error s!"file-scope global '{name.text}' must declare an initializer: \
                    'var {name.text}: <type> := <value>'"
  | _, _ =>
    TransM.error s!"parseTopLevel expects procedureCommand, compositeCommand, datatypeCommand, constrainedTypeCommand, or globalVarCommand, got {repr op.name}"

/-- Translate one non-global top-level command, preserving the existing public API. -/
def parseTopLevel (arg : Arg) : TransM (Option Procedure × Option TypeDefinition) := do
  let topLevel ← parseTopLevelWithGlobals arg
  if topLevel.field.isSome then
    TransM.error
      "parseTopLevel expects procedureCommand, compositeCommand, or datatypeCommand, got `Laurel.globalVarCommand`"
  return (topLevel.proc, topLevel.type)

/--
Translate concrete Laurel syntax into abstract Laurel syntax
-/
def parseProgram (prog : StrataDDM.Program) : TransM Laurel.Program := do
  let mut procedures : List Procedure := []
  let mut types : List TypeDefinition := []
  let mut fields : List Field := []
  for op in prog.commands do
    let { proc := procOpt, type := typeOpt, field := fieldOpt } ←
      parseTopLevelWithGlobals (.op op)
    match procOpt with
    | some proc => procedures := procedures ++ [proc]
    | none => pure ()
    match typeOpt with
    | some typeDef => types := types ++ [typeDef]
    | none => pure ()
    match fieldOpt with
    | some field => fields := fields ++ [field]
    | none => pure ()
  return {
    staticProcedures := procedures
    staticFields := fields
    types := types
  }

end

end Laurel

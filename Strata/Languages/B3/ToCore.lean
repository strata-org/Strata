/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Factory

/-!
# B3 to Core Conversion

Converts B3 abstract syntax trees to Strata Core statements for the CoreSMT
verifier pipeline. B3 uses de Bruijn indices for variable references while
Core uses free variables, so the converter maintains a context mapping indices
to Core identifiers.

## TODO: Architectural Improvements

1. **B3 → Core.Decl instead of Core.Statement**
   - Currently converts to `Imperative.Stmt.funcDecl` (statement)
   - Should convert to `Core.Decl.func` (declaration)
   - Then add a phase: Core.Decl → CoreSMT statements (subset validation)
   - This separates parsing from verification subset validation

2. **Procedure Support**
   - Currently only supports parameterless procedures
   - Should convert B3 procedures to `Core.Decl.proc`
   - Verification of each procedure done via CoreSMT on statements only
-/

namespace Strata.B3.ToCore

open Strata.B3AST
open Core
open Lambda

/-- Conversion errors -/
inductive ConversionError where
  | unsupportedFeature (feature : String) (context : String)
  deriving Repr

instance : ToString ConversionError where
  toString
    | .unsupportedFeature feat ctx => s!"Unsupported feature '{feat}' in {ctx}"

/-- Conversion result with error collection -/
structure ConvResult (α : Type) where
  value : α
  errors : List ConversionError
  deriving Repr

def ConvResult.ok (value : α) : ConvResult α := { value, errors := [] }
def ConvResult.withError (value : α) (error : ConversionError) : ConvResult α := { value, errors := [error] }
def ConvResult.addErrors (result : ConvResult α) (newErrors : List ConversionError) : ConvResult α :=
  { result with errors := result.errors ++ newErrors }

instance [Inhabited α] : Inhabited (ConvResult α) where
  default := { value := default, errors := [] }

/-- Conversion context: maps de Bruijn indices to Core identifiers. -/
structure ConvContext where
  vars : List (String × Lambda.LMonoTy)  -- index 0 = head
  funcs : List (String × List Lambda.LMonoTy × Lambda.LMonoTy)  -- (name, argTypes, retType)
  boundDepth : Nat := 0  -- number of enclosing quantifiers/abstractions

def ConvContext.empty : ConvContext := { vars := [], funcs := [] }

def ConvContext.push (ctx : ConvContext) (name : String) (ty : Lambda.LMonoTy) : ConvContext :=
  { ctx with vars := (name, ty) :: ctx.vars }

/-- Push a bound variable (for quantifiers/abstractions) -/
def ConvContext.pushBound (ctx : ConvContext) (name : String) (ty : Lambda.LMonoTy) : ConvContext :=
  { ctx with vars := (name, ty) :: ctx.vars, boundDepth := ctx.boundDepth + 1 }

def ConvContext.addFunc (ctx : ConvContext) (name : String) (argTypes : List Lambda.LMonoTy) (retType : Lambda.LMonoTy) : ConvContext :=
  { ctx with funcs := (name, argTypes, retType) :: ctx.funcs }

/-- Look up a function's type as an arrow type -/
def ConvContext.lookupFuncType (ctx : ConvContext) (name : String) : Option Lambda.LMonoTy :=
  match ctx.funcs.find? (fun (n, _, _) => n == name) with
  | some (_, argTypes, retType) =>
    some (argTypes.foldr (fun argTy acc => .arrow argTy acc) retType)
  | none => none

/-- Map B3 type name to Core monomorphic type. -/
def b3TypeToCoreTy (typeName : String) : Lambda.LMonoTy :=
  match typeName with
  | "int" => .tcons "int" []
  | "bool" => .tcons "bool" []
  | "real" => .tcons "real" []
  | "string" => .tcons "string" []
  | other => .tcons other []

/-- Map B3 type name to Core type scheme. -/
def b3TypeToCoreLTy (typeName : String) : Lambda.LTy :=
  .forAll [] (b3TypeToCoreTy typeName)


/-- Convert B3 binary operator to a Core expression builder.
    Uses factory operator expressions with proper type annotations. -/
def convertBinaryOp (op : BinaryOp M) (lhs rhs : Core.Expression.Expr) : Core.Expression.Expr :=
  let mkBinApp (opExpr : Core.Expression.Expr) :=
    .app () (.app () opExpr lhs) rhs
  match op with
  | .eq _ => .eq () lhs rhs
  | .neq _ => .app () Core.boolNotOp (.eq () lhs rhs)
  | .and _ => mkBinApp Core.boolAndOp
  | .or _ => mkBinApp Core.boolOrOp
  | .implies _ => mkBinApp Core.boolImpliesOp
  | .iff _ => mkBinApp Core.boolEquivOp
  | .impliedBy _ =>
    .app () (.app () Core.boolImpliesOp rhs) lhs
  | .lt _ => mkBinApp Core.intLtOp
  | .le _ => mkBinApp Core.intLeOp
  | .gt _ => mkBinApp Core.intGtOp
  | .ge _ => mkBinApp Core.intGeOp
  | .add _ => mkBinApp Core.intAddOp
  | .sub _ => mkBinApp Core.intSubOp
  | .mul _ => mkBinApp Core.intMulOp
  | .div _ => mkBinApp Core.intDivOp
  | .mod _ => mkBinApp Core.intModOp

/-- Convert B3 unary operator to a Core expression. -/
def convertUnaryOp (op : UnaryOp M) (arg : Core.Expression.Expr) : Core.Expression.Expr :=
  let opExpr := match op with
    | .not _ => Core.boolNotOp
    | .neg _ => Core.intNegOp
  .app () opExpr arg


/-- Convert B3 expression to Core expression.
    Uses de Bruijn indices from B3 AST, maps to free variables in Core. -/
partial def convertExpr (ctx : ConvContext) : B3AST.Expression SourceRange → ConvResult Core.Expression.Expr
  | .literal _ (.intLit _ n) => .ok (.intConst () (Int.ofNat n))
  | .literal _ (.boolLit _ b) => .ok (.boolConst () b)
  | .literal _ (.stringLit _ s) => .ok (.strConst () s)
  | .id _ idx =>
    if idx < ctx.boundDepth then
      .ok (.bvar () idx)
    else
      match ctx.vars[idx]? with
      | some (name, ty) => .ok (.fvar () (CoreIdent.unres name) (some ty))
      | none => .withError (.intConst () 0) (.unsupportedFeature s!"unbound variable at index {idx}" "expression")
  | .binaryOp _ op lhs rhs =>
    let lhsResult := convertExpr ctx lhs
    let rhsResult := convertExpr ctx rhs
    { value := convertBinaryOp op lhsResult.value rhsResult.value,
      errors := lhsResult.errors ++ rhsResult.errors }
  | .unaryOp _ op arg =>
    let argResult := convertExpr ctx arg
    { value := convertUnaryOp op argResult.value, errors := argResult.errors }
  | .ite _ cond thn els =>
    let condResult := convertExpr ctx cond
    let thnResult := convertExpr ctx thn
    let elsResult := convertExpr ctx els
    { value := .ite () condResult.value thnResult.value elsResult.value,
      errors := condResult.errors ++ thnResult.errors ++ elsResult.errors }
  | .functionCall _ fnName args =>
    let fnTy := ctx.lookupFuncType fnName.val
    let base : Core.Expression.Expr := .fvar () (CoreIdent.unres fnName.val) fnTy
    let argResults := args.val.toList.map (convertExpr ctx)
    { value := argResults.foldl (fun acc argRes => .app () acc argRes.value) base,
      errors := argResults.flatMap (·.errors) }
  | .letExpr _ varName value body =>
    let valTy := LMonoTy.tcons "int" []
    let valueResult := convertExpr ctx value
    let bodyResult := convertExpr (ctx.pushBound varName.val valTy) body
    { value := .app () (.abs () (some valTy) bodyResult.value) valueResult.value,
      errors := valueResult.errors ++ bodyResult.errors }
  | .quantifierExpr _ qk vars _patterns body =>
    let qkind : Lambda.QuantifierKind := match qk with
      | .forall _ => .all
      | .exists _ => .exist
    let varList := vars.val.toList.filterMap fun v =>
      match v with
      | .quantVarDecl _ name ty => some (name.val, b3TypeToCoreTy ty.val)
    let ctx' := varList.foldl (fun c (name, ty) => c.pushBound name ty) ctx
    let bodyResult := convertExpr ctx' body
    { value := varList.foldr (fun (_, ty) acc =>
        .quant () qkind (some ty) (.boolConst () true) acc
      ) bodyResult.value,
      errors := bodyResult.errors }
  | .labeledExpr _ _label expr => convertExpr ctx expr


/-- Convert a B3 statement to a list of Core statements. -/
partial def convertStmt (ctx : ConvContext) : B3AST.Statement SourceRange → ConvResult (List Core.Statement)
  | .check _ expr =>
    let exprResult := convertExpr ctx expr
    { value := [Core.Statement.assert "check" exprResult.value], errors := exprResult.errors }
  | .assert _ expr =>
    let exprResult := convertExpr ctx expr
    { value := [Core.Statement.assert "assert" exprResult.value], errors := exprResult.errors }
  | .assume _ expr =>
    let exprResult := convertExpr ctx expr
    { value := [Core.Statement.assume "assume" exprResult.value], errors := exprResult.errors }
  | .reach _ expr =>
    let exprResult := convertExpr ctx expr
    { value := [Core.Statement.cover "reach" exprResult.value], errors := exprResult.errors }
  | .blockStmt _ stmts =>
    let results := stmts.val.toList.map (convertStmt ctx)
    { value := [Imperative.Stmt.block "block" (results.flatMap (·.value))],
      errors := results.flatMap (·.errors) }
  | .varDecl _ name ty _autoinv init =>
    let coreTy := match ty.val with
      | some tyAnn => b3TypeToCoreLTy tyAnn.val
      | none => b3TypeToCoreLTy "int"
    match init.val with
    | some initExpr =>
      let initResult := convertExpr ctx initExpr
      { value := [Core.Statement.init (CoreIdent.unres name.val) coreTy (some initResult.value)],
        errors := initResult.errors }
    | none =>
      .ok [Core.Statement.init (CoreIdent.unres name.val) coreTy none]
  | .assign _ lhs rhs =>
    let rhsResult := convertExpr ctx rhs
    match ctx.vars[lhs.val]? with
    | some (name, _) =>
      { value := [Core.Statement.set (CoreIdent.unres name) rhsResult.value],
        errors := rhsResult.errors }
    | none =>
      .withError [] (.unsupportedFeature s!"unbound variable at index {lhs.val}" "assignment")
  | .ifStmt _ cond thenBranch elseBranch =>
    let condResult := convertExpr ctx cond
    let thenResult := convertStmt ctx thenBranch
    let elseResult := match elseBranch.val with
      | some s => convertStmt ctx s
      | none => .ok []
    { value := [Imperative.Stmt.ite condResult.value thenResult.value elseResult.value],
      errors := condResult.errors ++ thenResult.errors ++ elseResult.errors }
  | .loop _ invariants body =>
    let guard : Core.Expression.Expr := .boolConst () true
    let invResults := invariants.val.toList.map (convertExpr ctx)
    let invariant := match invResults with
      | [] => none
      | [invRes] => some invRes.value
      | invRes :: rest => some (rest.foldl (fun acc res =>
          .app () (.app () (.op () (CoreIdent.unres "Bool.And") none) acc) res.value
        ) invRes.value)
    let bodyResult := convertStmt ctx body
    { value := [Imperative.Stmt.loop guard none invariant bodyResult.value],
      errors := invResults.flatMap (·.errors) ++ bodyResult.errors }
  | .choose _ branches =>
    let results := branches.val.toList.map (convertStmt ctx)
    { value := [Imperative.Stmt.block "choose" (results.flatMap (·.value))],
      errors := results.flatMap (·.errors) }
  | .labeledStmt _ _label stmt => convertStmt ctx stmt
  | _ => .withError [] (.unsupportedFeature "unknown statement type" "statement")


/-- Convert a B3 function declaration to a Core funcDecl statement. -/
def convertFuncDecl (ctx : ConvContext) : B3AST.Decl SourceRange → ConvResult (List Core.Statement)
  | .function _ name params retType tag body =>
    -- Check for unsupported features
    let errors := []
    let errors := if tag.val.isSome then
      errors ++ [.unsupportedFeature "function tags" s!"function {name.val}"]
    else errors
    let errors := if params.val.toList.any (fun p => match p with | .fParameter _ inj _ _ => inj.val) then
      errors ++ [.unsupportedFeature "injective parameters" s!"function {name.val}"]
    else errors
    let errors := if body.val.any (fun fb => match fb with | .functionBody _ whens _ => !whens.val.isEmpty) then
      errors ++ [.unsupportedFeature "'when' clauses" s!"function {name.val}"]
    else errors
    
    let inputs : ListMap CoreIdent Lambda.LTy := params.val.toList.map fun p =>
      match p with
      | .fParameter _ _ pname pty => (CoreIdent.unres pname.val, b3TypeToCoreLTy pty.val)
    let outputTy := b3TypeToCoreLTy retType.val
    let bodyResult := body.val.bind fun fb =>
      match fb with
      | .functionBody _ _ bodyExpr =>
        let paramCtx := params.val.toList.foldl (fun c p =>
          match p with
          | .fParameter _ _ pname pty => c.push pname.val (b3TypeToCoreTy pty.val)
        ) ctx
        some (convertExpr paramCtx bodyExpr)
    let (coreBody, bodyErrors) := match bodyResult with
      | some res => (some res.value, res.errors)
      | none => (none, [])
    let decl : Imperative.PureFunc Core.Expression := {
      name := CoreIdent.unres name.val
      inputs := inputs
      output := outputTy
      body := coreBody
    }
    { value := [Imperative.Stmt.funcDecl decl], errors := errors ++ bodyErrors }
  | _ => .ok []

/-- Build a ConvContext with all function declarations from a B3 program. -/
private def buildFuncContext (decls : List (B3AST.Decl SourceRange)) : ConvContext :=
  decls.foldl (fun ctx decl =>
    match decl with
    | .function _ name params retType _ _ =>
      let argTypes := params.val.toList.map fun p =>
        match p with
        | .fParameter _ _ _ pty => b3TypeToCoreTy pty.val
      ctx.addFunc name.val argTypes (b3TypeToCoreTy retType.val)
    | _ => ctx
  ) ConvContext.empty

/-- Convert a B3 program to a list of Core statements, collecting errors. -/
def convertProgram : B3AST.Program SourceRange → ConvResult (List Core.Statement)
  | .program _ decls =>
    let ctx := buildFuncContext decls.val.toList
    let results := decls.val.toList.map fun decl =>
      match decl with
      | .function _ _ _ _ _ _ => convertFuncDecl ctx decl
      | .axiom _ _vars expr =>
        let exprResult := convertExpr ctx expr
        { value := [Core.Statement.assume "axiom" exprResult.value], errors := exprResult.errors }
      | .procedure _ _name _params _specs body =>
        match body.val with
        | some bodyStmt => convertStmt ctx bodyStmt
        | none => .ok []
      | _ => .withError [] (.unsupportedFeature "unknown declaration type" "program")
    { value := results.flatMap (·.value), errors := results.flatMap (·.errors) }

end Strata.B3.ToCore

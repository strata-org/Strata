/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Factory

/-!
# B3 AST to Strata Core Conversion

Converts B3 abstract syntax trees to Strata Core statements for the CoreSMT
verifier pipeline. B3 uses de Bruijn indices for variable references while
Core uses free variables, so the converter maintains a context mapping indices
to Core identifiers.
-/

namespace Strata.B3.ToCore

open Strata.B3AST
open Core
open Lambda

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
partial def convertExpr (ctx : ConvContext) : B3AST.Expression SourceRange → Core.Expression.Expr
  | .literal _ (.intLit _ n) => .intConst () (Int.ofNat n)
  | .literal _ (.boolLit _ b) => .boolConst () b
  | .literal _ (.stringLit _ s) => .strConst () s
  | .id _ idx =>
    if idx < ctx.boundDepth then
      -- Bound variable (inside quantifier/abstraction) → de Bruijn index
      .bvar () idx
    else
      -- Free variable → named reference
      match ctx.vars[idx]? with
      | some (name, ty) => .fvar () (CoreIdent.unres name) (some ty)
      | none => .intConst () 0  -- fallback for unbound
  | .binaryOp _ op lhs rhs =>
    convertBinaryOp op (convertExpr ctx lhs) (convertExpr ctx rhs)
  | .unaryOp _ op arg =>
    convertUnaryOp op (convertExpr ctx arg)
  | .ite _ cond thn els =>
    .ite () (convertExpr ctx cond) (convertExpr ctx thn) (convertExpr ctx els)
  | .functionCall _ fnName args =>
    let fnTy := ctx.lookupFuncType fnName.val
    let base : Core.Expression.Expr := .fvar () (CoreIdent.unres fnName.val) fnTy
    args.val.toList.foldl (fun acc arg => .app () acc (convertExpr ctx arg)) base
  | .letExpr _ varName value body =>
    let valTy := LMonoTy.tcons "int" []  -- default type for let bindings
    .app () (.abs () (some valTy) (convertExpr (ctx.pushBound varName.val valTy) body))
            (convertExpr ctx value)
  | .quantifierExpr _ qk vars _patterns body =>
    let qkind : Lambda.QuantifierKind := match qk with
      | .forall _ => .all
      | .exists _ => .exist
    let varList := vars.val.toList.filterMap fun v =>
      match v with
      | .quantVarDecl _ name ty => some (name.val, b3TypeToCoreTy ty.val)
    let ctx' := varList.foldl (fun c (name, ty) => c.pushBound name ty) ctx
    let bodyExpr := convertExpr ctx' body
    varList.foldr (fun (_, ty) acc =>
      .quant () qkind (some ty) (.boolConst () true) acc
    ) bodyExpr
  | .labeledExpr _ _label expr => convertExpr ctx expr


/-- Convert a B3 statement to a list of Core statements. -/
partial def convertStmt (ctx : ConvContext) : B3AST.Statement SourceRange → List Core.Statement
  | .check _ expr =>
    [Core.Statement.assert "check" (convertExpr ctx expr)]
  | .assert _ expr =>
    [Core.Statement.assert "assert" (convertExpr ctx expr)]
  | .assume _ expr =>
    [Core.Statement.assume "assume" (convertExpr ctx expr)]
  | .reach _ expr =>
    [Core.Statement.cover "reach" (convertExpr ctx expr)]
  | .blockStmt _ stmts =>
    let innerStmts := stmts.val.toList.flatMap (convertStmt ctx)
    [Imperative.Stmt.block "block" innerStmts]
  | .varDecl _ name ty _autoinv init =>
    let coreTy := match ty.val with
      | some tyAnn => b3TypeToCoreLTy tyAnn.val
      | none => b3TypeToCoreLTy "int"
    let coreInit := init.val.map (convertExpr ctx ·)
    [Core.Statement.init (CoreIdent.unres name.val) coreTy coreInit]
  | .assign _ lhs rhs =>
    match ctx.vars[lhs.val]? with
    | some (name, _) =>
      [Core.Statement.set (CoreIdent.unres name) (convertExpr ctx rhs)]
    | none => []
  | .ifStmt _ cond thenBranch elseBranch =>
    let condExpr := convertExpr ctx cond
    let thenStmts := convertStmt ctx thenBranch
    let elseStmts := match elseBranch.val with
      | some s => convertStmt ctx s
      | none => []
    [Imperative.Stmt.ite condExpr thenStmts elseStmts]
  | .loop _ invariants body =>
    let guard : Core.Expression.Expr := .boolConst () true
    let invariant := match invariants.val.toList with
      | [] => none
      | [inv] => some (convertExpr ctx inv)
      | inv :: rest => some (rest.foldl (fun acc e =>
          .app () (.app () (.op () (CoreIdent.unres "Bool.And") none) acc) (convertExpr ctx e)
        ) (convertExpr ctx inv))
    let bodyStmts := convertStmt ctx body
    [Imperative.Stmt.loop guard none invariant bodyStmts]
  | .choose _ branches =>
    let branchStmts := branches.val.toList.flatMap (convertStmt ctx)
    [Imperative.Stmt.block "choose" branchStmts]
  | .labeledStmt _ _label stmt => convertStmt ctx stmt
  | _ => []


/-- Convert a B3 function declaration to a Core funcDecl statement. -/
def convertFuncDecl (ctx : ConvContext) : B3AST.Decl SourceRange → List Core.Statement
  | .function _ name params retType _tag body =>
    let inputs : ListMap CoreIdent Lambda.LTy := params.val.toList.map fun p =>
      match p with
      | .fParameter _ _injective pname pty =>
        (CoreIdent.unres pname.val, b3TypeToCoreLTy pty.val)
    let outputTy := b3TypeToCoreLTy retType.val
    let coreBody := match body.val with
      | some (.functionBody _ _whens bodyExpr) =>
        let paramCtx := params.val.toList.foldl (fun c p =>
          match p with
          | .fParameter _ _ pname pty => c.push pname.val (b3TypeToCoreTy pty.val)
        ) ctx
        some (convertExpr paramCtx bodyExpr)
      | none => none
    let decl : Imperative.PureFunc Core.Expression := {
      name := CoreIdent.unres name.val
      inputs := inputs
      output := outputTy
      body := coreBody
    }
    [Imperative.Stmt.funcDecl decl]
  | _ => []

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

/-- Convert a B3 program to a list of Core statements. -/
def convertProgram : B3AST.Program SourceRange → List Core.Statement
  | .program _ decls =>
    let ctx := buildFuncContext decls.val.toList
    decls.val.toList.flatMap fun decl =>
      match decl with
      | .function _ _ _ _ _ _ => convertFuncDecl ctx decl
      | .axiom _ _vars expr =>
        [Core.Statement.assume "axiom" (convertExpr ctx expr)]
      | .procedure _ _name _params _specs body =>
        match body.val with
        | some bodyStmt => convertStmt ctx bodyStmt
        | none => []
      | _ => []

end Strata.B3.ToCore

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.Languages.Core.Verifier
import Strata.Languages.Core.Statement
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Options
import Strata.Languages.Laurel.Laurel
import Strata.Languages.Laurel.LiftExpressionAssignments
import Strata.Languages.Laurel.HeapParameterization
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.Languages.Laurel.LaurelFormat

open Core (VCResult VCResults)
open Core (intAddOp intSubOp intMulOp intDivOp intModOp intNegOp intLtOp intLeOp intGtOp intGeOp boolAndOp boolOrOp boolNotOp)

namespace Strata.Laurel

open Strata
open Lambda (LMonoTy LTy LExpr)

/-- Map from constrained type name to its definition -/
abbrev ConstrainedTypeMap := Std.HashMap Identifier ConstrainedType

/-- Pre-translated constraint: base type and Core expression with free variable for the value -/
structure TranslatedConstraint where
  base : HighType
  valueName : Identifier
  /-- Core expression for constraint, with valueName as free variable -/
  coreConstraint : Core.Expression.Expr

/-- Map from constrained type name to pre-translated constraint -/
abbrev TranslatedConstraintMap := Std.HashMap Identifier TranslatedConstraint

/-- Build a map of constrained types from a program -/
def buildConstrainedTypeMap (types : List TypeDefinition) : ConstrainedTypeMap :=
  types.foldl (init := {}) fun m td =>
    match td with
    | .Constrained ct => m.insert ct.name ct
    | _ => m

/-- Get the base type for a type, resolving constrained types -/
def resolveBaseType (ctMap : ConstrainedTypeMap) (ty : HighType) : HighType :=
  match ty with
  | .UserDefined name =>
    match ctMap.get? name with
    | some ct => ct.base
    | none => ty
  | _ => ty

/-
Translate Laurel HighType to Core Type
-/
def translateType (ty : HighType) : LMonoTy :=
  match ty with
  | .TInt => LMonoTy.int
  | .TBool => LMonoTy.bool
  | .TVoid => LMonoTy.bool
  | .THeap => .tcons "Heap" []
  | .TField => .tcons "Field" [LMonoTy.int]  -- For now, all fields hold int
  | .UserDefined _ => .tcons "Composite" []
  | _ => panic s!"unsupported type {repr ty}"

/-- Translate type, resolving constrained types to their base type -/
def translateTypeWithCT (ctMap : ConstrainedTypeMap) (ty : HighType) : LMonoTy :=
  translateType (resolveBaseType ctMap ty)

abbrev TypeEnv := List (Identifier × HighType)

def lookupType (ctMap : ConstrainedTypeMap) (env : TypeEnv) (name : Identifier) : LMonoTy :=
  match env.find? (fun (n, _) => n == name) with
  | some (_, ty) => translateTypeWithCT ctMap ty
  | none => LMonoTy.int  -- fallback

/-- Translate simple expressions (for constraints - no quantifiers) -/
def translateSimpleExpr (ctMap : ConstrainedTypeMap) (env : TypeEnv) (expr : StmtExpr) : Core.Expression.Expr :=
  match expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      .fvar () (Core.CoreIdent.locl name) (some (lookupType ctMap env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateSimpleExpr ctMap env e)
    | .Neg => .app () intNegOp (translateSimpleExpr ctMap env e)
    | _ => panic! s!"translateSimpleExpr: Invalid unary op"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr) :=
      LExpr.mkApp () bop [translateSimpleExpr ctMap env e1, translateSimpleExpr ctMap env e2]
    match op with
    | .Eq => .eq () (translateSimpleExpr ctMap env e1) (translateSimpleExpr ctMap env e2)
    | .Neq => .app () boolNotOp (.eq () (translateSimpleExpr ctMap env e1) (translateSimpleExpr ctMap env e2))
    | .And => binOp boolAndOp | .Or => binOp boolOrOp
    | .Add => binOp intAddOp | .Sub => binOp intSubOp | .Mul => binOp intMulOp
    | .Div => binOp intDivOp | .Mod => binOp intModOp
    | .Lt => binOp intLtOp | .Leq => binOp intLeOp | .Gt => binOp intGtOp | .Geq => binOp intGeOp
    | _ => panic! s!"translateSimpleExpr: Invalid binary op"
  | _ => panic! s!"translateSimpleExpr: Unsupported expression in constraint"

/-- Build map of pre-translated constraints -/
def buildTranslatedConstraintMap (ctMap : ConstrainedTypeMap) : TranslatedConstraintMap :=
  ctMap.fold (init := {}) fun m name ct =>
    let env : TypeEnv := [(ct.valueName, ct.base)]
    let coreExpr := translateSimpleExpr ctMap env ct.constraint
    m.insert name { base := ct.base, valueName := ct.valueName, coreConstraint := coreExpr }

/-- Close free variable by name, converting fvar to bvar at depth k -/
def varCloseByName (k : Nat) (x : Core.CoreIdent) (e : Core.Expression.Expr) : Core.Expression.Expr :=
  match e with
  | .const m c => .const m c
  | .op m o ty => .op m o ty
  | .bvar m i => .bvar m i
  | .fvar m y yty => if x == y then .bvar m k else .fvar m y yty
  | .abs m ty e' => .abs m ty (varCloseByName (k + 1) x e')
  | .quant m qk ty tr e' => .quant m qk ty (varCloseByName (k + 1) x tr) (varCloseByName (k + 1) x e')
  | .app m e1 e2 => .app m (varCloseByName k x e1) (varCloseByName k x e2)
  | .ite m c t f => .ite m (varCloseByName k x c) (varCloseByName k x t) (varCloseByName k x f)
  | .eq m e1 e2 => .eq m (varCloseByName k x e1) (varCloseByName k x e2)

def boolImpliesOp : Core.Expression.Expr :=
  .op () (Core.CoreIdent.glob "Bool.Implies") (some (LMonoTy.arrow LMonoTy.bool (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)))

/--
Translate Laurel StmtExpr to Core Expression
-/
def translateExpr (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (env : TypeEnv) (expr : StmtExpr) : Core.Expression.Expr :=
  match h: expr with
  | .LiteralBool b => .const () (.boolConst b)
  | .LiteralInt i => .const () (.intConst i)
  | .Identifier name =>
      let ident := Core.CoreIdent.locl name
      .fvar () ident (some (lookupType ctMap env name))
  | .PrimitiveOp op [e] =>
    match op with
    | .Not => .app () boolNotOp (translateExpr ctMap tcMap env e)
    | .Neg => .app () intNegOp (translateExpr ctMap tcMap env e)
    | _ => panic! s!"translateExpr: Invalid unary op: {repr op}"
  | .PrimitiveOp op [e1, e2] =>
    let binOp (bop : Core.Expression.Expr): Core.Expression.Expr :=
      LExpr.mkApp () bop [translateExpr ctMap tcMap env e1, translateExpr ctMap tcMap env e2]
    match op with
    | .Eq => .eq () (translateExpr ctMap tcMap env e1) (translateExpr ctMap tcMap env e2)
    | .Neq => .app () boolNotOp (.eq () (translateExpr ctMap tcMap env e1) (translateExpr ctMap tcMap env e2))
    | .And => binOp boolAndOp
    | .Or => binOp boolOrOp
    | .Add => binOp intAddOp
    | .Sub => binOp intSubOp
    | .Mul => binOp intMulOp
    | .Div => binOp intDivOp
    | .Mod => binOp intModOp
    | .Lt => binOp intLtOp
    | .Leq => binOp intLeOp
    | .Gt => binOp intGtOp
    | .Geq => binOp intGeOp
    | _ => panic! s!"translateExpr: Invalid binary op: {repr op}"
  | .PrimitiveOp op args =>
    panic! s!"translateExpr: PrimitiveOp {repr op} with {args.length} args"
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr ctMap tcMap env cond
      let bthen := translateExpr ctMap tcMap env thenBranch
      let belse := match elseBranch with
                  | some e => translateExpr ctMap tcMap env e
                  | none => .const () (.intConst 0)
      .ite () bcond bthen belse
  | .Assign _ value _ => translateExpr ctMap tcMap env value
  | .StaticCall name args =>
      let ident := Core.CoreIdent.glob name
      let fnOp := .op () ident none
      args.foldl (fun acc arg => .app () acc (translateExpr ctMap tcMap env arg)) fnOp
  | .ReferenceEquals e1 e2 =>
      .eq () (translateExpr ctMap tcMap env e1) (translateExpr ctMap tcMap env e2)
  | .Block [single] _ => translateExpr ctMap tcMap env single
  | .Forall _name ty body =>
      let coreType := translateTypeWithCT ctMap ty
      let env' := (_name, ty) :: env
      let bodyExpr := translateExpr ctMap tcMap env' body
      let coreIdent := Core.CoreIdent.locl _name
      let closedBody := varCloseByName 0 coreIdent bodyExpr
      -- forall x: T => body  becomes  forall x. constraint(x) ==> body  if T is constrained
      let finalBody := match ty with
        | .UserDefined typeName => match tcMap.get? typeName with
          | some tc =>
              let substConstraint := tc.coreConstraint.substFvar (Core.CoreIdent.locl tc.valueName)
                (.fvar () coreIdent (some (translateTypeWithCT ctMap ty)))
              LExpr.mkApp () boolImpliesOp [varCloseByName 0 coreIdent substConstraint, closedBody]
          | none => closedBody
        | _ => closedBody
      LExpr.quant () .all (some coreType) (LExpr.noTrigger ()) finalBody
  | .Exists _name ty body =>
      let coreType := translateTypeWithCT ctMap ty
      let env' := (_name, ty) :: env
      let bodyExpr := translateExpr ctMap tcMap env' body
      let coreIdent := Core.CoreIdent.locl _name
      let closedBody := varCloseByName 0 coreIdent bodyExpr
      -- exists x: T => body  becomes  exists x. constraint(x) && body  if T is constrained
      let finalBody := match ty with
        | .UserDefined typeName => match tcMap.get? typeName with
          | some tc =>
              let substConstraint := tc.coreConstraint.substFvar (Core.CoreIdent.locl tc.valueName)
                (.fvar () coreIdent (some (translateTypeWithCT ctMap ty)))
              LExpr.mkApp () boolAndOp [varCloseByName 0 coreIdent substConstraint, closedBody]
          | none => closedBody
        | _ => closedBody
      LExpr.quant () .exist (some coreType) (LExpr.noTrigger ()) finalBody
  | _ => panic! Std.Format.pretty (Std.ToFormat.format expr)
  termination_by expr
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals (rename_i x_in; have := List.sizeOf_lt_of_mem x_in; omega)

def getNameFromMd (md : Imperative.MetaData Core.Expression): String :=
  let fileRange := (Imperative.getFileRange md).get!
  s!"({fileRange.range.start})"

def genConstraintCheck (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (param : Parameter) : Option Core.Expression.Expr :=
  match param.type with
  | .UserDefined name =>
    match tcMap.get? name with
    | some tc =>
      let paramIdent := Core.CoreIdent.locl param.name
      let valueIdent := Core.CoreIdent.locl tc.valueName
      let baseTy := translateTypeWithCT ctMap param.type
      some (tc.coreConstraint.substFvar valueIdent (.fvar () paramIdent (some baseTy)))
    | none => none
  | _ => none

def genConstraintAssert (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (name : Identifier) (ty : HighType) : List Core.Statement :=
  match genConstraintCheck ctMap tcMap { name, type := ty } with
  | some expr => [Core.Statement.assert s!"{name}#constraint" expr .empty]
  | none => []

def defaultExprForType (ctMap : ConstrainedTypeMap) (ty : HighType) : Core.Expression.Expr :=
  match resolveBaseType ctMap ty with
  | .TInt => .const () (.intConst 0)
  | .TBool => .const () (.boolConst false)
  | _ => .const () (.intConst 0)

def isHeapFunction (name : Identifier) : Bool :=
  name == "heapRead" || name == "heapStore"

/--
Translate Laurel StmtExpr to Core Statements
Takes the type environment and output parameter names
-/
def translateStmt (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (env : TypeEnv) (outputParams : List Parameter) (stmt : StmtExpr) : TypeEnv × List Core.Statement :=
  match stmt with
  | @StmtExpr.Assert cond md =>
      let boogieExpr := translateExpr ctMap tcMap env cond
      (env, [Core.Statement.assert ("assert" ++ getNameFromMd md) boogieExpr md])
  | @StmtExpr.Assume cond md =>
      let boogieExpr := translateExpr ctMap tcMap env cond
      (env, [Core.Statement.assume ("assume" ++ getNameFromMd md) boogieExpr md])
  | .Block stmts _ =>
      let (env', stmtsList) := stmts.foldl (fun (e, acc) s =>
        let (e', ss) := translateStmt ctMap tcMap e outputParams s
        (e', acc ++ ss)) (env, [])
      (env', stmtsList)
  | .LocalVariable name ty initializer =>
      let env' := (name, ty) :: env
      let boogieType := LTy.forAll [] (translateTypeWithCT ctMap ty)
      let ident := Core.CoreIdent.locl name
      let constraintCheck := genConstraintAssert ctMap tcMap name ty
      match initializer with
      | some (.StaticCall callee args) =>
          if isHeapFunction callee then
            let boogieExpr := translateExpr ctMap tcMap env (.StaticCall callee args)
            (env', [Core.Statement.init ident boogieType boogieExpr] ++ constraintCheck)
          else
            let boogieArgs := args.map (translateExpr ctMap tcMap env)
            let initStmt := Core.Statement.init ident boogieType (defaultExprForType ctMap ty)
            let callStmt := Core.Statement.call [ident] callee boogieArgs
            (env', [initStmt, callStmt] ++ constraintCheck)
      | some initExpr =>
          let boogieExpr := translateExpr ctMap tcMap env initExpr
          (env', [Core.Statement.init ident boogieType boogieExpr] ++ constraintCheck)
      | none =>
          (env', [Core.Statement.init ident boogieType (defaultExprForType ctMap ty)] ++ constraintCheck)
  | .Assign target value _ =>
      match target with
      | .Identifier name =>
          let ident := Core.CoreIdent.locl name
          let constraintCheck := match env.find? (fun (n, _) => n == name) with
            | some (_, ty) => genConstraintAssert ctMap tcMap name ty
            | none => []
          match value with
          | .StaticCall callee args =>
              if isHeapFunction callee then
                let boogieExpr := translateExpr ctMap tcMap env value
                (env, [Core.Statement.set ident boogieExpr] ++ constraintCheck)
              else
                let boogieArgs := args.map (translateExpr ctMap tcMap env)
                (env, [Core.Statement.call [ident] callee boogieArgs] ++ constraintCheck)
          | _ =>
              let boogieExpr := translateExpr ctMap tcMap env value
              (env, [Core.Statement.set ident boogieExpr] ++ constraintCheck)
      | _ => (env, [])
  | .IfThenElse cond thenBranch elseBranch =>
      let bcond := translateExpr ctMap tcMap env cond
      let (_, bthen) := translateStmt ctMap tcMap env outputParams thenBranch
      let belse := match elseBranch with
                  | some e => (translateStmt ctMap tcMap env outputParams e).2
                  | none => []
      (env, [Imperative.Stmt.ite bcond bthen belse .empty])
  | .While cond invOpt _decOpt body =>
      let condExpr := translateExpr ctMap tcMap env cond
      let invExpr := invOpt.map (translateExpr ctMap tcMap env)
      let (_, bodyStmts) := translateStmt ctMap tcMap env outputParams body
      (env, [Imperative.Stmt.loop condExpr none invExpr bodyStmts .empty])
  | .StaticCall name args =>
      if isHeapFunction name then (env, [])
      else (env, [Core.Statement.call [] name (args.map (translateExpr ctMap tcMap env))])
  | .Return valueOpt =>
      match valueOpt, outputParams.head? with
      | some value, some outParam =>
          let ident := Core.CoreIdent.locl outParam.name
          let boogieExpr := translateExpr ctMap tcMap env value
          let assignStmt := Core.Statement.set ident boogieExpr
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [assignStmt, noFallThrough])
      | none, _ =>
          let noFallThrough := Core.Statement.assume "return" (.const () (.boolConst false)) .empty
          (env, [noFallThrough])
      | some _, none =>
          panic! "Return statement with value but procedure has no output parameters"
  | _ => (env, [])

/--
Translate Laurel Parameter to Core Signature entry
-/
def translateParameterToCore (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := Core.CoreIdent.locl param.name
  let ty := translateType param.type
  (ident, ty)

/-- Translate parameter with constrained type resolution -/
def translateParameterToCoreWithCT (ctMap : ConstrainedTypeMap) (param : Parameter) : (Core.CoreIdent × LMonoTy) :=
  let ident := Core.CoreIdent.locl param.name
  let ty := translateTypeWithCT ctMap param.type
  (ident, ty)

/--
Translate Laurel Procedure to Core Procedure
-/
def translateProcedure (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (constants : List Constant) (proc : Procedure) : Core.Procedure :=
  -- Check if this procedure has a heap parameter (first input named "heap")
  let hasHeapParam := proc.inputs.any (fun p => p.name == "heap" && p.type == .THeap)
  -- Rename heap input to heap_in if present
  let renamedInputs := proc.inputs.map (fun p =>
    if p.name == "heap" && p.type == .THeap then { p with name := "heap_in" } else p)
  let inputPairs := renamedInputs.map (translateParameterToCoreWithCT ctMap)
  let inputs := inputPairs
  let header : Core.Procedure.Header := {
    name := proc.name
    typeArgs := []
    inputs := inputs
    outputs := proc.outputs.map (translateParameterToCoreWithCT ctMap)
  }
  -- Build type environment with original types (for constraint checks)
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type)) ++
                           proc.outputs.map (fun p => (p.name, p.type)) ++
                           constants.map (fun c => (c.name, c.type))
  -- Generate constraint checks for input parameters with constrained types
  let inputConstraints : ListMap Core.CoreLabel Core.Procedure.Check :=
    proc.inputs.filterMap (fun p =>
      match genConstraintCheck ctMap tcMap p with
      | some expr => some (s!"{proc.name}_input_{p.name}_constraint", { expr })
      | none => none)
  -- Translate explicit preconditions
  let explicitPreconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    proc.preconditions.mapIdx fun i precond =>
      let check : Core.Procedure.Check := { expr := translateExpr ctMap tcMap initEnv precond }
      (s!"{proc.name}_pre_{i}", check)
  let preconditions := inputConstraints ++ explicitPreconditions
  -- Generate constraint checks for output parameters with constrained types
  let outputConstraints : ListMap Core.CoreLabel Core.Procedure.Check :=
    proc.outputs.filterMap (fun p =>
      match genConstraintCheck ctMap tcMap p with
      | some expr => some (s!"{proc.name}_output_{p.name}_constraint", { expr })
      | none => none)
  -- Translate explicit postconditions for Opaque bodies
  let explicitPostconditions : ListMap Core.CoreLabel Core.Procedure.Check :=
    match proc.body with
    | .Opaque posts _ _ _ =>
        posts.mapIdx fun i postcond =>
          let check : Core.Procedure.Check := { expr := translateExpr ctMap tcMap initEnv postcond }
          (s!"{proc.name}_post_{i}", check)
    | _ => []
  let postconditions := explicitPostconditions ++ outputConstraints
  let spec : Core.Procedure.Spec := {
    modifies := []
    preconditions := preconditions
    postconditions := postconditions
  }
  -- If we have a heap parameter, add initialization: var heap := heap_in
  let heapInit : List Core.Statement :=
    if hasHeapParam then
      let heapTy := LMonoTy.tcons "Heap" []
      let heapType := LTy.forAll [] heapTy
      let heapIdent := Core.CoreIdent.locl "heap"
      let heapInExpr := LExpr.fvar () (Core.CoreIdent.locl "heap_in") (some heapTy)
      [Core.Statement.init heapIdent heapType heapInExpr]
    else []
  let body : List Core.Statement :=
    match proc.body with
    | .Transparent bodyExpr => heapInit ++ (translateStmt ctMap tcMap initEnv proc.outputs bodyExpr).2
    | .Opaque _posts (some impl) _ _ => heapInit ++ (translateStmt ctMap tcMap initEnv proc.outputs impl).2
    | _ => []
  {
    header := header
    spec := spec
    body := body
  }

def heapTypeDecl : Core.Decl := .type (.con { name := "Heap", numargs := 0 })
def fieldTypeDecl : Core.Decl := .type (.con { name := "Field", numargs := 1 })
def compositeTypeDecl : Core.Decl := .type (.con { name := "Composite", numargs := 0 })

def readFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapRead"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy)]
    output := tVar
    body := none
  }

def updateFunction : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let tVar := LMonoTy.ftvar "T"
  let fieldTy := LMonoTy.tcons "Field" [tVar]
  .func {
    name := Core.CoreIdent.glob "heapStore"
    typeArgs := ["T"]
    inputs := [(Core.CoreIdent.locl "heap", heapTy),
               (Core.CoreIdent.locl "obj", compTy),
               (Core.CoreIdent.locl "field", fieldTy),
               (Core.CoreIdent.locl "val", tVar)]
    output := heapTy
    body := none
  }

-- Axiom: forall h, o, f, v :: heapRead(heapStore(h, o, f, v), o, f) == v
-- Using int for field values since Core doesn't support polymorphism in axioms
def readUpdateSameAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Build: heapRead(heapStore(h, o, f, v), o, f) == v using de Bruijn indices
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (o), Heap (h)
  -- So: h is bvar 0, o is bvar 1, f is bvar 2, v is bvar 3
  let h := LExpr.bvar () 0
  let o := LExpr.bvar () 1
  let f := LExpr.bvar () 2
  let v := LExpr.bvar () 3
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o, f, v]
  let readExpr := LExpr.mkApp () readOp [updateExpr, o, f]
  let eqBody := LExpr.eq () readExpr v
  -- Wrap in foralls: forall v:int, f:Field int, o:Composite, h:Heap
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) eqBody
  .ax { name := "heapRead_heapStore_same", e := body }

-- Axiom: forall h, o1, o2, f, v :: o1 != o2 ==> heapRead(heapStore(h, o1, f, v), o2, f) == heapRead(h, o2, f)
-- Using int for field values since Core doesn't support polymorphism in axioms
def readUpdateDiffObjAxiom : Core.Decl :=
  let heapTy := LMonoTy.tcons "Heap" []
  let compTy := LMonoTy.tcons "Composite" []
  let fieldTy := LMonoTy.tcons "Field" [LMonoTy.int]
  -- Quantifier order (outer to inner): int (v), Field int (f), Composite (o2), Composite (o1), Heap (h)
  -- So: h is bvar 0, o1 is bvar 1, o2 is bvar 2, f is bvar 3, v is bvar 4
  let h := LExpr.bvar () 0
  let o1 := LExpr.bvar () 1
  let o2 := LExpr.bvar () 2
  let f := LExpr.bvar () 3
  let v := LExpr.bvar () 4
  let updateOp := LExpr.op () (Core.CoreIdent.glob "heapStore") none
  let readOp := LExpr.op () (Core.CoreIdent.glob "heapRead") none
  let updateExpr := LExpr.mkApp () updateOp [h, o1, f, v]
  let lhs := LExpr.mkApp () readOp [updateExpr, o2, f]
  let rhs := LExpr.mkApp () readOp [h, o2, f]
  let neq := LExpr.app () boolNotOp (LExpr.eq () o1 o2)
  let implBody := LExpr.app () (LExpr.app () Core.boolImpliesOp neq) (LExpr.eq () lhs rhs)
  let body := LExpr.all () (some LMonoTy.int) <|
              LExpr.all () (some fieldTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some compTy) <|
              LExpr.all () (some heapTy) implBody
  .ax { name := "heapRead_heapStore_diff_obj", e := body }

def translateConstant (c : Constant) : Core.Decl :=
  let ty := translateType c.type
  .func {
    name := Core.CoreIdent.glob c.name
    typeArgs := []
    inputs := []
    output := ty
    body := none
  }

/--
Check if a StmtExpr is a pure expression (can be used as a Core function body).
Pure expressions don't contain statements like assignments, loops, or local variables.
A Block with a single pure expression is also considered pure.
-/
def isPureExpr : StmtExpr → Bool
  | .LiteralBool _ => true
  | .LiteralInt _ => true
  | .Identifier _ => true
  | .PrimitiveOp _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .IfThenElse c t none => isPureExpr c && isPureExpr t
  | .IfThenElse c t (some e) => isPureExpr c && isPureExpr t && isPureExpr e
  | .StaticCall _ args => args.attach.all (fun ⟨a, _⟩ => isPureExpr a)
  | .ReferenceEquals e1 e2 => isPureExpr e1 && isPureExpr e2
  | .Block [single] _ => isPureExpr single
  | _ => false
termination_by e => sizeOf e

/--
Check if a procedure can be translated as a Core function.
A procedure can be a function if:
- It has a transparent body that is a pure expression
- It has no precondition (or just `true`)
- It has exactly one output parameter (the return type)
-/
def canBeBoogieFunction (proc : Procedure) : Bool :=
  match proc.body with
  | .Transparent bodyExpr =>
    isPureExpr bodyExpr &&
    proc.preconditions.isEmpty &&
    proc.outputs.length == 1
  | _ => false

/--
Translate a Laurel Procedure to a Core Function (when applicable)
-/
def translateProcedureToFunction (ctMap : ConstrainedTypeMap) (tcMap : TranslatedConstraintMap) (proc : Procedure) : Core.Decl :=
  let inputs := proc.inputs.map translateParameterToCore
  let outputTy := match proc.outputs.head? with
    | some p => translateType p.type
    | none => LMonoTy.int
  let initEnv : TypeEnv := proc.inputs.map (fun p => (p.name, p.type))
  let body := match proc.body with
    | .Transparent bodyExpr => some (translateExpr ctMap tcMap initEnv bodyExpr)
    | _ => none
  .func {
    name := Core.CoreIdent.glob proc.name
    typeArgs := []
    inputs := inputs
    output := outputTy
    body := body
  }

/--
Translate Laurel Program to Core Program
-/
def translate (program : Program) : Except (Array DiagnosticModel) Core.Program := do
  let sequencedProgram ← liftExpressionAssignments program
  let heapProgram := heapParameterization sequencedProgram
  -- Build constrained type maps
  let ctMap := buildConstrainedTypeMap heapProgram.types
  let tcMap := buildTranslatedConstraintMap ctMap
  -- Separate procedures that can be functions from those that must be procedures
  let (funcProcs, procProcs) := heapProgram.staticProcedures.partition canBeBoogieFunction
  let procedures := procProcs.map (translateProcedure ctMap tcMap heapProgram.constants)
  let procDecls := procedures.map (fun p => Core.Decl.proc p .empty)
  let laurelFuncDecls := funcProcs.map (translateProcedureToFunction ctMap tcMap)
  let constDecls := heapProgram.constants.map translateConstant
  let typeDecls := [heapTypeDecl, fieldTypeDecl, compositeTypeDecl]
  let funcDecls := [readFunction, updateFunction]
  let axiomDecls := [readUpdateSameAxiom, readUpdateDiffObjAxiom]
  return { decls := typeDecls ++ funcDecls ++ axiomDecls ++ constDecls ++ laurelFuncDecls ++ procDecls }

/--
Verify a Laurel program using an SMT solver
-/
def verifyToVcResults (smtsolver : String) (program : Program)
    (options : Options := Options.default)
    (tempDir : Option String := .none)
    : IO (Except (Array DiagnosticModel) VCResults) := do
  let boogieProgramExcept := translate program
    -- Enable removeIrrelevantAxioms to avoid polluting simple assertions with heap axioms
  let options := { options with removeIrrelevantAxioms := true }
  -- Debug: Print the generated Core program
  match boogieProgramExcept with
    | .error e => return .error e
    | .ok boogieProgram =>
      dbg_trace "=== Generated Core Program ==="
      dbg_trace (toString (Std.Format.pretty (Std.ToFormat.format boogieProgram)))
      dbg_trace "================================="

      let runner tempDir :=
        EIO.toIO (fun f => IO.Error.userError (toString f))
            (Core.verify smtsolver boogieProgram tempDir options)
      let ioResult <- match tempDir with
      | .none =>
        IO.FS.withTempDir runner
      | .some p =>
        IO.FS.createDirAll ⟨p⟩
        runner ⟨p⟩
      return .ok ioResult


def verifyToDiagnostics (smtsolver : String) (files: Map Strata.Uri Lean.FileMap) (program : Program): IO (Array Diagnostic) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors.map (fun dm => dm.toDiagnostic files)
  | .ok results => return results.filterMap (fun dm => dm.toDiagnostic files)


def verifyToDiagnosticModels (smtsolver : String) (program : Program): IO (Array DiagnosticModel) := do
  let results <- verifyToVcResults smtsolver program
  match results with
  | .error errors => return errors
  | .ok results => return results.filterMap toDiagnosticModel

end Laurel

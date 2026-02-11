/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Program
import Strata.Languages.Core.CoreGen
import Strata.DDM.Util.DecimalRat

/-!
# Core.Program → CoreCST Conversion

This module converts Core.Program AST to Core CST (concrete syntax).
Used for formatting and pretty-printing Core constructs using DDM's
formatting system.
-/

namespace Strata

open Core
open Strata.CoreDDM

---------------------------------------------------------------------
-- Conversion Errors
---------------------------------------------------------------------

/-- Errors that can occur during AST→CST conversion (formatting) -/
inductive ASTToCSTError (M : Type) where
  | unsupportedConstruct (fn : String) (description : String) (context : String) (metadata : M) :
      ASTToCSTError M
  deriving Repr, Inhabited

namespace ASTToCSTError

def toString [ToString M] : ASTToCSTError M → String
  | unsupportedConstruct fn desc ctx _m =>
    s!"Unsupported construct in {fn}: {desc}\nContext: {ctx}"

instance [ToString M] : ToString (ASTToCSTError M) where
  toString := ASTToCSTError.toString

end ASTToCSTError

---------------------------------------------------------------------
-- Core.Program → CoreCST Conversion
---------------------------------------------------------------------

section ToCST

structure Scope where
  /-- Track bound type variables in this scope -/
  boundTypeVars : Array String := #[]
  /-- Track bound variables in this scope -/
  boundVars : Array String := #[]
  /-- Track free variables in this scope -/
  freeVars : Array String := #[]
  deriving Inhabited, Repr

structure ToCSTContext where
  /-- Stack of scopes, with global scope at index 0 -/
  scopes : Array Scope := #[{}]
  deriving Inhabited, Repr

namespace ToCSTContext

def empty : ToCSTContext := { scopes := #[{}] }

/-- Format context for error messages -/
def toErrorString (ctx : ToCSTContext) : String :=
  let lines := ctx.scopes.toList.mapIdx fun i scope =>
    let header := if i = 0 then "Global scope:" else s!"Scope {i}:"
    let btv := if scope.boundTypeVars.isEmpty then ""
               else s!"\n  boundTypeVars: {scope.boundTypeVars.toList}"
    let bv := if scope.boundVars.isEmpty then ""
              else s!"\n  boundVars: {scope.boundVars.toList}"
    let fv := if scope.freeVars.isEmpty then ""
              else s!"\n  freeVars: {scope.freeVars.toList}"
    s!"{header}{btv}{bv}{fv}"
  String.intercalate "\n" lines

/-- Get all bound type variables across all scopes -/
def boundTypeVars (ctx : ToCSTContext) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.boundTypeVars) #[]

/-- Get all bound variables across all scopes -/
def boundVars (ctx : ToCSTContext) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.boundVars) #[]

/-- Get all free variables across all scopes -/
def freeVars (ctx : ToCSTContext) : Array String :=
  ctx.scopes.foldl (fun acc s => acc ++ s.freeVars) #[]

/-- Add a bound type variable to the current scope -/
def addBoundTypeVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundTypeVars := scope.boundTypeVars.push name }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Add bound type variables to the current scope -/
def addBoundTypeVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundTypeVars := scope.boundTypeVars ++ names }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Add a free variable to the global scope (scope 0) -/
def addFreeVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  let scope := ctx.scopes[0]!
  let newScope := { scope with freeVars := scope.freeVars.push name }
  { ctx with scopes := ctx.scopes.set! 0 newScope }

/-- Add free variables to the global scope (scope 0) -/
def addFreeVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  let scope := ctx.scopes[0]!
  { ctx with scopes := ctx.scopes.set! 0 { scope with freeVars := scope.freeVars ++ names } }

/-- Add a bound variable to the current scope -/
def addBoundVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundVars := scope.boundVars.push name }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Add bound variables to the current scope -/
def addBoundVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let newScope := { scope with boundVars := scope.boundVars ++ names }
  { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Push a new scope onto the stack -/
def pushScope (ctx : ToCSTContext) : ToCSTContext :=
  { ctx with scopes := ctx.scopes.push {} }

/-- Pop the current scope from the stack (never pops scope 0) -/
def popScope (ctx : ToCSTContext) : ToCSTContext :=
  if ctx.scopes.size > 1 then
    { ctx with scopes := ctx.scopes.pop }
  else
    ctx

end ToCSTContext

/-- Monad for AST->CST conversion with context and error tracking -/
abbrev ToCSTM (M : Type) := StateT ToCSTContext (Except (List (ASTToCSTError M)))
/-- Throw an error in ToCSTM -/
def ToCSTM.throwError [Inhabited M] (fn : String) (desc : String)
    : ToCSTM M α := do
  let ctx ← get
  throw [.unsupportedConstruct fn desc ctx.toErrorString default]

/-- Convert `LMonoTy` to `CoreType` -/
def lmonoTyToCoreType [Inhabited M] (ty : Lambda.LMonoTy) :
    ToCSTM M (CoreType M) := do
  let ctx ← get
  match ty with
  | .ftvar name =>
    -- Lambda `.ftvars` are really just bound type variables.
    match ctx.boundTypeVars.toList.findIdx? (· == name) with
    | some idx =>
      if idx < ctx.boundTypeVars.size then
        let bvarIdx := ctx.boundTypeVars.size - (idx + 1)
        pure (.bvar default bvarIdx)
      else
        ToCSTM.throwError "lmonoTyToCoreType" s!"unbound ftvar {name}"
    | none => ToCSTM.throwError "lmonoTyToCoreType" s!"unbound ftvar {name}"
  | .bitvec 1 => pure (.bv1 default)
  | .bitvec 8 => pure (.bv8 default)
  | .bitvec 16 => pure (.bv16 default)
  | .bitvec 32 => pure (.bv32 default)
  | .bitvec 64 => pure (.bv64 default)
  | .bool => pure (.bool default)
  | .int => pure (.int default)
  | .string => pure (.string default)
  | .real => pure (.real default)
  | .tcons "regex" [] => pure (.regex default)
  | .tcons "Map" [k, v] => do
    let kty ← lmonoTyToCoreType k
    let vty ← lmonoTyToCoreType v
    pure (.Map default kty vty)
  | .tcons name args =>
    let ctx ← get
    match ctx.scopes[0]!.freeVars.toList.findIdx? (· == name) with
    | some idx => do
      let argTys ← args.mapM lmonoTyToCoreType
      pure (.fvar default idx argTys.toArray)
    | none => ToCSTM.throwError "lmonoTyToCoreType" s!"unknown type constructor {name}"
  | _ => ToCSTM.throwError "lmonoTyToCoreType" s!"unknown type {ty}"

/-- Convert `LTy` to `CoreType` -/
def lTyToCoreType [Inhabited M] (ty : Lambda.LTy) : ToCSTM M (CoreType M) :=
  match ty with
  | .forAll typeVars monoTy => do
    modify ToCSTContext.pushScope
    modify (ToCSTContext.addBoundTypeVars · typeVars.toArray)
    let result ← lmonoTyToCoreType monoTy
    modify ToCSTContext.popScope
    pure result

/-- Convert a type constructor declaration to CST -/
def typeConToCST [Inhabited M] (tcons : TypeConstructor)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let name : Ann String M := ⟨default, tcons.name⟩
  let args : Ann (Option (Bindings M)) M :=
    if tcons.numargs = 0 then
      ⟨default, none⟩
    else
      let bindings := List.range tcons.numargs |>.map fun i =>
        let paramName : Ann String M := ⟨default, s!"a{i}"⟩
        let paramType := TypeP.type default
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  pure (.command_typedecl default name args)

/-- Convert a datatype declaration to CST -/
def datatypeToCST [Inhabited M] (datatypes : List (Lambda.LDatatype Visibility))
    (_md : Imperative.MetaData Expression) : ToCSTM M (List (Command M)) := do
  -- Process each datatype independently
  let mut results := []
  for dt in datatypes do
    -- Add this datatype name to freeVars
    modify (·.addFreeVar dt.name)
    -- modify ToCSTContext.pushScope
    let name : Ann String M := ⟨default, dt.name⟩
    modify (·.addBoundTypeVars dt.typeArgs.toArray)
    let args : Ann (Option (Bindings M)) M :=
      if dt.typeArgs.isEmpty then
        ⟨default, none⟩
      else
        let bindings := dt.typeArgs.map fun param =>
          let paramName : Ann String M := ⟨default, param⟩
          let paramType := TypeP.type default
          Binding.mkBinding default paramName paramType
        ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
    let processConstr (c : Lambda.LConstr Visibility) : ToCSTM M (Constructor M) := do
      -- Add constructor name and tester name to free variables
      modify (·.addFreeVar c.name.name)
      modify (·.addFreeVar c.testerName)
      -- Add accessor function names to free variables
      for (id, _) in c.args do
        modify (·.addFreeVar (Lambda.destructorFuncName dt id))
      let constrName : Ann String M := ⟨default, c.name.name⟩
      let constrArgs ←
        if c.args.isEmpty then
          pure ⟨default, none⟩
        else do
          let bindings ← c.args.mapM fun (id, ty) => do
            let paramName : Ann String M := ⟨default, id.name⟩
            let paramType ← lmonoTyToCoreType ty
            pure (Binding.mkBinding default paramName (TypeP.expr paramType))
          pure ⟨default, some ⟨default, bindings.toArray⟩⟩
      pure (Constructor.constructor_mk default constrName constrArgs)
    let constrs ← dt.constrs.mapM processConstr
    let constrList := constrs.tail.foldl
      (fun acc c => ConstructorList.constructorListPush default acc c)
      (ConstructorList.constructorListAtom default constrs.head!)
    -- modify ToCSTContext.popScope
    results := results ++ [.command_datatype default name args constrList]
  pure results

/-- Convert a type synonym declaration to CST -/
def typeSynToCST [Inhabited M] (syn : TypeSynonym)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, syn.name⟩
  let args : Ann (Option (Bindings M)) M :=
    if syn.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let bindings := syn.typeArgs.map fun param =>
        let paramName : Ann String M := ⟨default, param⟩
        let paramType := TypeP.type default
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  let targs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  modify (·.addBoundTypeVars syn.typeArgs.toArray)
  let rhs ← lmonoTyToCoreType syn.type
  modify ToCSTContext.popScope
  pure (.command_typesynonym default name args targs rhs)

def lconstToExpr [Inhabited M] (c : Lambda.LConst) : ToCSTM M (CoreDDM.Expr M) :=
  match c with
  | .boolConst true => pure (.btrue default)
  | .boolConst false => pure (.bfalse default)
  | .intConst n => pure (.natToInt default ⟨default, n.toNat⟩)
  | .realConst r =>
    match Strata.Decimal.fromRat r with
    | some d => pure (.realLit default ⟨default, d⟩)
    | none => ToCSTM.throwError "lconstToExpr" s!"real {r}"
  | .strConst s => pure (.strLit default ⟨default, s⟩)
  | .bitvecConst 1 n => pure (.bv1Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 8 n => pure (.bv8Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 16 n => pure (.bv16Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 32 n => pure (.bv32Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 64 n => pure (.bv64Lit default ⟨default, n.toNat⟩)
  | .bitvecConst w _ => ToCSTM.throwError "lconstToExpr" s!"bitvec width {w}"

partial def lopToExpr [Inhabited M]
    (name : Lambda.Identifier CoreLParams.mono.base.IDMeta) : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  -- Check if this is a 0-ary function constant in freeVars
  match ctx.freeVars.toList.findIdx? (· == name.name) with
  | some idx => pure (.fvar default idx)
  | none => ToCSTM.throwError "lopToExpr" s!"op {name.name} not found"


mutual
/-- Convert `Lambda.LExpr` to Core `Expr` -/
partial def lexprToExpr [Inhabited M]
    (e : Lambda.LExpr CoreLParams.mono)
    (LambdaFVarsBound : Bool) : ToCSTM M (CoreDDM.Expr M) := do
  let ctx ← get
  match e with
  | .const _ c => lconstToExpr c
  | .bvar _ idx =>
    if idx < ctx.boundVars.size then
      let bvarIdx := ctx.boundVars.size - (idx + 1)
      pure (.bvar default bvarIdx)
    else
      ToCSTM.throwError "lexprToExpr" s!"bvar {idx}"
  | .fvar _ id _ =>
    -- We first look for Lambda .fvars in the boundVars context, before checking
    -- the freeVars context. Lambda .fvars can come from formals of a function
    -- or procedure (DDM .bvar), but also from global variable declaration (DDM
    -- .fvar). Note that Strata Core does not allow variable shadowing.
    match ctx.boundVars.toList.findIdx? (· == id.name) with
    | some idx => pure (.bvar default (ctx.boundVars.size - (idx + 1)))
    | none =>
      match ctx.freeVars.toList.findIdx? (· == id.name) with
      | some idx => pure (.fvar default idx)
      | none => ToCSTM.throwError "lexprToExpr" s!"fvar {id.name}"
  | .ite _ c t f => liteToExpr c t f LambdaFVarsBound
  | .eq _ e1 e2 => leqToExpr e1 e2 LambdaFVarsBound
  | .op _ name _ => lopToExpr name
  | .app _ fn arg => lappToExpr fn arg LambdaFVarsBound
  | .abs _ _ _ => ToCSTM.throwError "lexprToExpr" "lambda not supported in CoreDDM"
  | .quant _ _ _ _ _ => ToCSTM.throwError "lexprToExpr" "quantifier"

partial def liteToExpr [Inhabited M]
    (c t f : Lambda.LExpr CoreLParams.mono) (bound : Bool) : ToCSTM M (CoreDDM.Expr M) := do
  let cExpr ← lexprToExpr c bound
  let tExpr ← lexprToExpr t bound
  let fExpr ← lexprToExpr f bound
  let ty := CoreType.bool default
  pure (.if default ty cExpr tExpr fExpr)

partial def leqToExpr [Inhabited M]
    (e1 e2 : Lambda.LExpr CoreLParams.mono) (bound : Bool) : ToCSTM M (CoreDDM.Expr M) := do
  let e1Expr ← lexprToExpr e1 bound
  let e2Expr ← lexprToExpr e2 bound
  let ty := CoreType.bool default
  pure (.equal default ty e1Expr e2Expr)

partial def lappToExpr [Inhabited M]
    (fn arg : Lambda.LExpr CoreLParams.mono) (bound : Bool) : ToCSTM M (CoreDDM.Expr M) :=
  match fn with
  | .op _ name _ => do
    let argExpr ← lexprToExpr arg bound
    match name.name with
    | "Bool.Not" => pure (.not default argExpr)
    | "str_len" => pure (.str_len default argExpr)
    | "str_toregex" => pure (.str_toregex default argExpr)
    | "re_star" => pure (.re_star default argExpr)
    | "re_plus" => pure (.re_plus default argExpr)
    | "re_comp" => pure (.re_comp default argExpr)
    | _ => ToCSTM.throwError "lappToExpr" s!"unary op {name.name}"
  | .app _ fn2 arg1 =>
    match fn2 with
    | .op _ name _ => do
      let arg1Expr ← lexprToExpr arg1 bound
      let arg2Expr ← lexprToExpr arg bound
      match name.name with
      | "Bool.And" => pure (.and default arg1Expr arg2Expr)
      | "Bool.Or" => pure (.or default arg1Expr arg2Expr)
      | "Bool.Implies" => pure (.implies default arg1Expr arg2Expr)
      | "Bool.Equiv" => pure (.equiv default arg1Expr arg2Expr)
      | "str_concat" => pure (.str_concat default arg1Expr arg2Expr)
      | "str_inregex" => pure (.str_inregex default arg1Expr arg2Expr)
      | "re_range" => pure (.re_range default arg1Expr arg2Expr)
      | "re_concat" => pure (.re_concat default arg1Expr arg2Expr)
      | "re_union" => pure (.re_union default arg1Expr arg2Expr)
      | "re_inter" => pure (.re_inter default arg1Expr arg2Expr)
      | _ => ToCSTM.throwError "lappToExpr" s!"binary op {name.name}"
    | .app _ fn3 arg1 =>
      match fn3 with
      | .op _ name _ => do
        let arg1Expr ← lexprToExpr arg1 bound
        let arg2Expr ← lexprToExpr arg bound
        let arg3Expr ← lexprToExpr arg bound
        match name.name with
        | "str_substr" => pure (.str_substr default arg1Expr arg2Expr arg3Expr)
        | "re_loop" => pure (.re_loop default arg1Expr arg2Expr arg3Expr)
        | _ => ToCSTM.throwError "lappToExpr" s!"ternary op {name.name}"
      | _ => ToCSTM.throwError "lappToExpr" "nested app"
    | _ => ToCSTM.throwError "lappToExpr" "complex app"
  | _ => ToCSTM.throwError "lappToExpr" "general app"

end

mutual
/-- Convert Core.Statement to CoreDDM.Statement -/
partial def stmtToCST [Inhabited M] (s : Core.Statement) : ToCSTM M (CoreDDM.Statement M) :=
  match s with
  | .init name ty expr _md => do
    let nameAnn : Ann String M := ⟨default, name.name⟩
    let tyCST ← lTyToCoreType ty
    let exprCST ← lexprToExpr expr true
    pure (.initStatement default tyCST nameAnn exprCST)
  | .set name expr _md => do
    let lhs := Lhs.lhsIdent default ⟨default, name.name⟩
    let exprCST ← lexprToExpr expr true
    let tyCST := CoreType.bool default  -- placeholder, ideally infer from expr
    pure (.assign default tyCST lhs exprCST)
  | .havoc name _md => do
    let nameAnn : Ann String M := ⟨default, name.name⟩
    pure (.havoc_statement default nameAnn)
  | .assert label expr _md => do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr true
    pure (.assert default labelAnn exprCST)
  | .assume label expr _md => do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr true
    pure (.assume default labelAnn exprCST)
  | .cover label expr _md => do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr expr true
    pure (.cover default labelAnn exprCST)
  | .call lhs pname args _md => do
    let lhsAnn : Ann (Array (Ann String M)) M := ⟨default, (lhs.map fun id => ⟨default, id.name⟩).toArray⟩
    let pnameAnn : Ann String M := ⟨default, pname⟩
    let argsCST ← args.mapM (lexprToExpr · true)
    let argsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, argsCST.toArray⟩
    pure (.call_statement default lhsAnn pnameAnn argsAnn)
  | .block label stmts _md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    let blockCST ← blockToCST stmts
    pure (.block_statement default labelAnn blockCST)
  | .ite cond thenb elseb _md => do
    let condCST ← lexprToExpr cond true
    let thenCST ← blockToCST thenb
    let elseCST ← elseToCST elseb
    pure (.if_statement default condCST thenCST elseCST)
  | .loop guard _measure invariant body _md => do
    let guardCST ← lexprToExpr guard true
    let invs ← invariantsToCST invariant
    let bodyCST ← blockToCST body
    pure (.while_statement default guardCST invs bodyCST)
  | .goto label _md => do
    let labelAnn : Ann String M := ⟨default, label⟩
    pure (.goto_statement default labelAnn)
  | .funcDecl _ _ => ToCSTM.throwError "stmtToCST" "funcDecl in statement"

partial def blockToCST [Inhabited M] (stmts : List Core.Statement) : ToCSTM M (CoreDDM.Block M) := do
  let stmtsCST ← stmts.mapM stmtToCST
  pure (.block default ⟨default, stmtsCST.toArray⟩)

partial def elseToCST [Inhabited M] (stmts : List Core.Statement) : ToCSTM M (Else M) := do
  if stmts.isEmpty then
    pure (.else0 default)
  else
    let blockCST ← blockToCST stmts
    pure (.else1 default blockCST)

partial def invariantsToCST [Inhabited M]
    (inv : Option (Lambda.LExpr CoreLParams.mono)) : ToCSTM M (Invariants M) :=
  match inv with
  | none => pure (.nilInvariants default)
  | some expr => do
    let exprCST ← lexprToExpr expr true
    pure (.consInvariants default exprCST (.nilInvariants default))
end

/-- Convert a procedure to CST -/
def procToCST [Inhabited M] (proc : Core.Procedure) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, proc.header.name.toPretty⟩
  modify (ToCSTContext.addBoundTypeVars · proc.header.typeArgs.toArray)
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if proc.header.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let tvars := proc.header.typeArgs.map fun tv =>
        TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
      ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩
  let processInput (id : CoreIdent) (ty : Lambda.LMonoTy) : ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.toPretty⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.toPretty)
  let inputResults ← proc.header.inputs.toList.mapM (fun (id, ty) => processInput id ty)
  let inputBindings := inputResults.map (·.1)
  let inputNames := inputResults.map (·.2) |>.toArray
  let inputs : Bindings M := .mkBindings default ⟨default, inputBindings.toArray⟩
  let processOutput (id : CoreIdent) (ty : Lambda.LMonoTy) : ToCSTM M (MonoBind M × String) := do
    let nameAnn : Ann String M := ⟨default, id.toPretty⟩
    let tyCST ← lmonoTyToCoreType ty
    pure (MonoBind.mono_bind_mk default nameAnn tyCST, id.toPretty)
  let outputResults ← proc.header.outputs.toList.mapM (fun (id, ty) => processOutput id ty)
  let outputBinds := outputResults.map (·.1)
  let outputNames := outputResults.map (·.2) |>.toArray
  modify (ToCSTContext.addBoundVars · inputNames)
  modify (ToCSTContext.addBoundVars · outputNames)
  let outputs : Ann (Option (MonoDeclList M)) M :=
    if outputBinds.isEmpty then
      ⟨default, none⟩
    else
      let declList := outputBinds.tail.foldl
        (fun acc bind => MonoDeclList.monoDeclPush default acc bind)
        (MonoDeclList.monoDeclAtom default outputBinds.head!)
      ⟨default, some declList⟩
  -- Build spec elements
  let mut specElts : List (SpecElt M) := []
  -- Add modifies
  for id in proc.spec.modifies do
    let modSpec := SpecElt.modifies_spec default ⟨default, id.name⟩
    specElts := specElts ++ [modSpec]
  -- Add requires
  let freeAnn : Ann (Option (Free M)) M := ⟨default, none⟩
  for (label, check) in proc.spec.preconditions.toList do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr check.expr true
    let reqSpec := SpecElt.requires_spec default labelAnn freeAnn exprCST
    specElts := specElts ++ [reqSpec]
  -- Add ensures
  for (label, check) in proc.spec.postconditions.toList do
    let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, label⟩)⟩
    let exprCST ← lexprToExpr check.expr true
    let ensSpec := SpecElt.ensures_spec default labelAnn freeAnn exprCST
    specElts := specElts ++ [ensSpec]
  let specAnn : Ann (Array (SpecElt M)) M := ⟨default, specElts.toArray⟩
  let spec : Ann (Option (Spec M)) M :=
    if specElts.isEmpty then
      ⟨default, none⟩
    else
      ⟨default, some (Spec.spec_mk default specAnn)⟩
  let bodyCST ← blockToCST proc.body
  let body : Ann (Option (CoreDDM.Block M)) M := ⟨default, some bodyCST⟩
  modify ToCSTContext.popScope
  pure (.command_procedure default name typeArgs inputs outputs spec body)

/-- Convert a function declaration to CST -/
def funcToCST [Inhabited M]
    (func : Lambda.LFunc CoreLParams)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  modify ToCSTContext.pushScope
  let name : Ann String M := ⟨default, func.name.name⟩
  -- Add type arguments to context and create TypeArgs.
  modify (·.addBoundTypeVars func.typeArgs.toArray)
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if func.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let tvars := func.typeArgs.map fun tv =>
        TypeVar.type_var default (⟨default, tv⟩ : Ann String M)
      ⟨default, some (TypeArgs.type_args default ⟨default, tvars.toArray⟩)⟩
  let processInput (id : CoreLParams.Identifier) (ty : Lambda.LMonoTy) : ToCSTM M (Binding M × String) := do
    let paramName : Ann String M := ⟨default, id.name⟩
    let paramType ← lmonoTyToCoreType ty
    let binding := Binding.mkBinding default paramName (TypeP.expr paramType)
    pure (binding, id.name)
  let results ← func.inputs.toList.mapM (fun (id, ty) => processInput id ty)
  let bindings := results.map (·.1)
  let paramNames := results.map (·.2) |>.toArray
  let b : Bindings M := .mkBindings default ⟨default, bindings.toArray⟩
  let r ← lmonoTyToCoreType func.output
  let result ← match func.body with
  | none => pure (.command_fndecl default name typeArgs b r)
  | some body => do
    -- Add formals to the context.
    modify (·.addBoundVars paramNames)
    let bodyExpr ← lexprToExpr body true
    let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
    pure (.command_fndef default name typeArgs b r bodyExpr inline?)
  modify ToCSTContext.popScope
  pure result

/-- Convert an axiom to CST -/
def axiomToCST [Inhabited M] (ax : Axiom)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨
      default, some (.label default ⟨default, ax.name⟩)⟩
  let exprCST ← lexprToExpr ax.e false
  pure (.command_axiom default labelAnn exprCST)

/-- Convert a distinct declaration to CST -/
def distinctToCST [Inhabited M] (name : CoreIdent) (es : List (Lambda.LExpr CoreLParams.mono))
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let labelAnn : Ann (Option (Label M)) M := ⟨default, some (.label default ⟨default, name.toPretty⟩)⟩
  let exprsCST ← es.mapM (lexprToExpr · false)
  let exprsAnn : Ann (Array (CoreDDM.Expr M)) M := ⟨default, exprsCST.toArray⟩
  pure (.command_distinct default labelAnn exprsAnn)

/-- Convert a variable declaration to CST -/
def varToCST [Inhabited M]
    (name : CoreIdent) (ty : Lambda.LTy) (_e : Lambda.LExpr CoreLParams.mono)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
  let nameAnn : Ann String M := ⟨default, name.toPretty⟩
  let tyCST ← lTyToCoreType ty
  let typeArgs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let bind := Bind.bind_mk default nameAnn typeArgs tyCST
  pure (.command_var default bind)

/-- Convert a `Core.Decl` to a Core `Command` -/
def declToCST [Inhabited M] (decl : Core.Decl) : ToCSTM M (List (Command M)) :=
  match decl with
  | .var name ty e md => do
    modify (·.addFreeVar name.toPretty)
    let cmd ← varToCST name ty e md
    pure [cmd]
  | .type (.con tcons) md => do
    modify (·.addFreeVar tcons.name)
    let cmd ← typeConToCST tcons md
    pure [cmd]
  | .type (.syn syn) md => do
    modify (·.addFreeVar syn.name)
    let cmd ← typeSynToCST syn md
    pure [cmd]
  | .type (.data datatypes) md =>
    datatypeToCST datatypes md
  | .func func md => do
    modify (·.addFreeVar func.name.name)
    let cmd ← funcToCST func md
    pure [cmd]
  | .proc proc _md => do
    modify (·.addFreeVar proc.header.name.toPretty)
    let cmd ← procToCST proc
    pure [cmd]
  | .ax ax md => do
    let cmd ← axiomToCST ax md
    pure [cmd]
  | .distinct name es md => do
    let cmd ← distinctToCST name es md
    pure [cmd]

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST [Inhabited M] (prog : Core.Program) :
    ToCSTM M (List (Command M)) := do
  let cmdLists ← prog.decls.mapM declToCST
  pure cmdLists.flatten

end ToCST

---------------------------------------------------------------------

end Strata

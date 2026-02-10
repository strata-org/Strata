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
  | unsupportedConstruct (description : String) (metadata : M) :
      ASTToCSTError M
  deriving Repr, Inhabited

namespace ASTToCSTError

def toString [ToString M] : ASTToCSTError M → String
  | unsupportedConstruct desc _m => s!"Unsupported construct: {desc}"

instance [ToString M] : ToString (ASTToCSTError M) where
  toString := ASTToCSTError.toString

end ASTToCSTError

---------------------------------------------------------------------
-- Core.Program → CoreCST Conversion
---------------------------------------------------------------------

section ToCST

structure ToCSTContext where
  /-- Track bound type variables -/
  boundTypeVars : Array String := #[]
  /-- Track bound variables -/
  boundVars : Array String := #[]
  /-- Track free variables -/
  freeVars : Array String := #[]
  deriving Repr

namespace ToCSTContext

def empty : ToCSTContext := {}

def addBoundTypeVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { ctx with boundTypeVars := ctx.boundTypeVars.push name }

def addBoundTypeVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  { ctx with boundTypeVars := ctx.boundTypeVars.append names }

def addFreeVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { ctx with freeVars := ctx.freeVars.push name }

def addFreeVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  { ctx with freeVars := ctx.freeVars.append names }

def addBoundVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { ctx with boundVars := ctx.boundVars.push name }

def addBoundVars (ctx : ToCSTContext) (names : Array String) : ToCSTContext :=
  { ctx with boundVars := ctx.boundVars.append names }

end ToCSTContext

/-- Monad for AST->CST conversion with context and error tracking -/
abbrev ToCSTM (M : Type) := StateT ToCSTContext (Except (List (ASTToCSTError M)))
/-- Throw an error in ToCSTM -/
def ToCSTM.throwError [Inhabited M] (err : ASTToCSTError M) : ToCSTM M α :=
  throw [err]

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
        ToCSTM.throwError (.unsupportedConstruct s!"unbound ftvar {name}" default)
    | none => ToCSTM.throwError (.unsupportedConstruct s!"unbound ftvar {name}" default)
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
    match ctx.freeVars.toList.findIdx? (· == name) with
    | some idx => do
      let argTys ← args.mapM lmonoTyToCoreType
      pure (.fvar default idx argTys.toArray)
    | none => ToCSTM.throwError (.unsupportedConstruct s!"unknown type constructor {name}" default)
  | _ => ToCSTM.throwError (.unsupportedConstruct s!"unknown type {ty}" default)

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

/-- Convert a type synonym declaration to CST -/
def typeSynToCST [Inhabited M] (syn : TypeSynonym)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
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
  pure (.command_typesynonym default name args targs rhs)

def lconstToExpr [Inhabited M] (c : Lambda.LConst) : ToCSTM M (CoreDDM.Expr M) :=
  match c with
  | .boolConst true => pure (.btrue default)
  | .boolConst false => pure (.bfalse default)
  | .intConst n => pure (.natToInt default ⟨default, n.toNat⟩)
  | .realConst r =>
    match Strata.Decimal.fromRat r with
    | some d => pure (.realLit default ⟨default, d⟩)
    | none => ToCSTM.throwError (.unsupportedConstruct s!"real {r}" default)
  | .strConst s => pure (.strLit default ⟨default, s⟩)
  | .bitvecConst 1 n => pure (.bv1Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 8 n => pure (.bv8Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 16 n => pure (.bv16Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 32 n => pure (.bv32Lit default ⟨default, n.toNat⟩)
  | .bitvecConst 64 n => pure (.bv64Lit default ⟨default, n.toNat⟩)
  | .bitvecConst w _ => ToCSTM.throwError (.unsupportedConstruct s!"bitvec width {w}" default)

partial def lopToExpr [Inhabited M]
    (name : Lambda.Identifier CoreLParams.mono.base.IDMeta) : ToCSTM M (CoreDDM.Expr M) :=
  match name.name with
  | "not" => pure (.not default (.btrue default))
  | "true" => pure (.btrue default)
  | "false" => pure (.bfalse default)
  | _ => ToCSTM.throwError (.unsupportedConstruct s!"op {name.name}" default)

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
      ToCSTM.throwError (.unsupportedConstruct s!"bvar {idx}" default)
  | .fvar _ id _ =>
    if LambdaFVarsBound then
      match ctx.boundVars.toList.findIdx? (· == id.name) with
      | some idx => pure (.bvar default (ctx.boundVars.size - (idx + 1)))
      | none => ToCSTM.throwError (.unsupportedConstruct s!"fvar {id.name}" default)
    else
      match ctx.freeVars.toList.findIdx? (· == id.name) with
      | some idx => pure (.fvar default idx)
      | none => ToCSTM.throwError (.unsupportedConstruct s!"fvar {id.name}" default)
  | .op _ name _ => lopToExpr name
  | .app _ fn arg => lappToExpr fn arg LambdaFVarsBound
  | .ite _ c t f => liteToExpr c t f LambdaFVarsBound
  | .eq _ e1 e2 => leqToExpr e1 e2 LambdaFVarsBound
  | .abs _ _ _ => ToCSTM.throwError (.unsupportedConstruct "lambda" default)
  | .quant _ _ _ _ _ => ToCSTM.throwError (.unsupportedConstruct "quantifier" default)

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
    | "not" => pure (.not default argExpr)
    | _ => ToCSTM.throwError (.unsupportedConstruct s!"unary op {name.name}" default)
  | .app _ fn2 arg1 =>
    match fn2 with
    | .op _ name _ => do
      let arg1Expr ← lexprToExpr arg1 bound
      let arg2Expr ← lexprToExpr arg bound
      match name.name with
      | "and" => pure (.and default arg1Expr arg2Expr)
      | "or" => pure (.or default arg1Expr arg2Expr)
      | "implies" => pure (.implies default arg1Expr arg2Expr)
      | "equiv" => pure (.equiv default arg1Expr arg2Expr)
      | "str_concat" => pure (.str_concat default arg1Expr arg2Expr)
      | "str_inregex" => pure (.str_inregex default arg1Expr arg2Expr)
      | _ => ToCSTM.throwError (.unsupportedConstruct s!"binary op {name.name}" default)
    | .app _ fn3 arg1 =>
      match fn3 with
      | .op _ name _ => do
        let arg1Expr ← lexprToExpr arg1 bound
        let arg2Expr ← lexprToExpr arg bound
        let arg3Expr ← lexprToExpr arg bound
        match name.name with
        | "str_substr" => pure (.str_substr default arg1Expr arg2Expr arg3Expr)
        | _ => ToCSTM.throwError (.unsupportedConstruct s!"ternary op {name.name}" default)
      | _ => ToCSTM.throwError (.unsupportedConstruct "nested app" default)
    | _ => ToCSTM.throwError (.unsupportedConstruct "complex app" default)
  | _ => ToCSTM.throwError (.unsupportedConstruct "general app" default)

end

/-- Convert a function declaration to CST -/
def funcToCST [Inhabited M]
    (func : Lambda.LFunc CoreLParams)
    (_md : Imperative.MetaData Expression) : ToCSTM M (Command M) := do
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
  match func.body with
  | none => pure (.command_fndecl default name typeArgs b r)
  | some body => do
    -- Add formals to the context.
    modify (·.addBoundVars paramNames)
    let bodyExpr ← lexprToExpr body true
    let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
    pure (.command_fndef default name typeArgs b r bodyExpr inline?)

/-- Convert a `Core.Decl` to a Core `Command` -/
def declToCST [Inhabited M] (decl : Core.Decl) : ToCSTM M (Command M) :=
  match decl with
  | .type (.con tcons) md => do
    modify (·.addFreeVar tcons.name)
    typeConToCST tcons md
  | .type (.syn syn) md => do
    modify (·.addFreeVar syn.name)
    typeSynToCST syn md
  | .func func md => do
    modify (·.addFreeVar func.name.name)
    funcToCST func md
  | _ => ToCSTM.throwError (.unsupportedConstruct "unimplemented decl" default)

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST [Inhabited M] (prog : Core.Program) : ToCSTM M (List (Command M)) :=
  prog.decls.mapM declToCST

end ToCST

---------------------------------------------------------------------

end Strata

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

def addBoundVar (ctx : ToCSTContext) (name : String) : ToCSTContext :=
  { ctx with boundVars := ctx.boundVars.push name }

end ToCSTContext

/-- Convert `LMonoTy` to `CoreType` -/
def lmonoTyToCoreType [Inhabited M] (ctx : ToCSTContext) (ty : Lambda.LMonoTy) :
    CoreType M × List (ASTToCSTError M) :=
  match ty with
  | .ftvar name =>
    match ctx.boundTypeVars.toList.findIdx? (· == name) with
    | some idx =>
      if idx < ctx.boundTypeVars.size then
        let bvarIdx := ctx.boundTypeVars.size - (idx + 1)
        (.bvar default bvarIdx, [])
      else
        (.bvar default 0, [.unsupportedConstruct s!"unbound ftvar {name}" default])
    | none => (.bvar default 0, [.unsupportedConstruct s!"unbound ftvar {name}" default])
  | .bitvec 1 => (.bv1 default, [])
  | .bitvec 8 => (.bv8 default, [])
  | .bitvec 16 => (.bv16 default, [])
  | .bitvec 32 => (.bv32 default, [])
  | .bitvec 64 => (.bv64 default, [])
  | .bool => (.bool default, [])
  | .int => (.int default, [])
  | .string => (.string default, [])
  | .real => (.real default, [])
  | .tcons "regex" [] => (.regex default, [])
  | .tcons "Map" [k, v] =>
    let (kty, kerrs) := lmonoTyToCoreType ctx k
    let (vty, verrs) := lmonoTyToCoreType ctx v
    (.Map default kty vty, kerrs ++ verrs)
  | .tcons name args =>
    match ctx.freeVars.toList.findIdx? (· == name) with
    | some idx =>
      let (argTys, argErrs) := args.foldl
        (init := (#[], []))
        fun (tys, errs) arg =>
          let (ty, tyErrs) := lmonoTyToCoreType ctx arg
          (tys.push ty, errs ++ tyErrs)
      (.fvar default idx argTys, argErrs)
    | none => (.fvar default 0 #[],
                [.unsupportedConstruct s!"unknown type constructor {name}" default])
  | _ =>
    (default, [.unsupportedConstruct s!"unknown type {ty}" default])

def lconstToExpr [Inhabited M] (c : Lambda.LConst) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  match c with
  | .boolConst true => (.btrue default, [])
  | .boolConst false => (.bfalse default, [])
  | .intConst n => (.natToInt default ⟨default, n.toNat⟩, [])
  | .realConst r =>
    match Strata.Decimal.fromRat r with
    | some d => (.realLit default ⟨default, d⟩, [])
    | none => (.btrue default,
      [.unsupportedConstruct s!"real {r}" default])
  | .strConst s => (.strLit default ⟨default, s⟩, [])
  | .bitvecConst 1 n => (.bv1Lit default ⟨default, n.toNat⟩, [])
  | .bitvecConst 8 n => (.bv8Lit default ⟨default, n.toNat⟩, [])
  | .bitvecConst 16 n => (.bv16Lit default ⟨default, n.toNat⟩, [])
  | .bitvecConst 32 n => (.bv32Lit default ⟨default, n.toNat⟩, [])
  | .bitvecConst 64 n => (.bv64Lit default ⟨default, n.toNat⟩, [])
  | .bitvecConst w _ => (.btrue default,
    [.unsupportedConstruct s!"bitvec width {w}" default])

partial def lopToExpr [Inhabited M]
    (name : Lambda.Identifier CoreLParams.mono.base.IDMeta) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  match name.name with
  | "not" => (.not default (.btrue default), [])
  | "true" => (.btrue default, [])
  | "false" => (.bfalse default, [])
  | _ => (.fvar default 0, [.unsupportedConstruct s!"op {name.name}" default])

mutual
/-- Convert `Lambda.LExpr` to Core `Expr` -/
partial def lexprToExpr [Inhabited M] (ctx : ToCSTContext)
    (e : Lambda.LExpr CoreLParams.mono)
    (LambdaFVarsBound : Bool) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  match e with
  | .const _ c => lconstToExpr c
  | .bvar _ idx =>
    if idx < ctx.boundVars.size then
      let bvarIdx := ctx.boundVars.size - (idx + 1)
      (.bvar default bvarIdx, [])
    else
      (.bvar default 0, [.unsupportedConstruct s!"bvar {idx}" default])
  | .fvar _ id _ =>
    if LambdaFVarsBound then
      match ctx.boundVars.toList.findIdx? (· == id.name) with
      | some idx => (.bvar default (ctx.boundVars.size - (idx + 1)), [])
      | none => (.bvar default 0, [.unsupportedConstruct s!"fvar {id.name}" default])
    else
      match ctx.freeVars.toList.findIdx? (· == id.name) with
      | some idx => (.fvar default idx, [])
      | none => (.fvar default 0, [.unsupportedConstruct s!"fvar {id.name}" default])
  | .op _ name _ => lopToExpr name
  | .app _ fn arg => lappToExpr ctx fn arg LambdaFVarsBound
  | .ite _ c t f => liteToExpr ctx c t f LambdaFVarsBound
  | .eq _ e1 e2 => leqToExpr ctx e1 e2 LambdaFVarsBound
  | .abs _ _ _ =>
    (.fvar default 0, [.unsupportedConstruct "lambda" default])
  | .quant _ _ _ _ _ =>
    (.fvar default 0, [.unsupportedConstruct "quantifier" default])

partial def liteToExpr [Inhabited M] (ctx : ToCSTContext)
    (c t f : Lambda.LExpr CoreLParams.mono) (bound : Bool) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  let (cExpr, cErrs) := lexprToExpr ctx c bound
  let (tExpr, tErrs) := lexprToExpr ctx t bound
  let (fExpr, fErrs) := lexprToExpr ctx f bound
  let ty := CoreType.bool default
  (.if default ty cExpr tExpr fExpr, cErrs ++ tErrs ++ fErrs)

partial def leqToExpr [Inhabited M] (ctx : ToCSTContext)
    (e1 e2 : Lambda.LExpr CoreLParams.mono) (bound : Bool) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  let (e1Expr, e1Errs) := lexprToExpr ctx e1 bound
  let (e2Expr, e2Errs) := lexprToExpr ctx e2 bound
  let ty := CoreType.bool default
  (.equal default ty e1Expr e2Expr, e1Errs ++ e2Errs)

partial def lappToExpr [Inhabited M] (ctx : ToCSTContext)
    (fn arg : Lambda.LExpr CoreLParams.mono) (bound : Bool) :
    CoreDDM.Expr M × List (ASTToCSTError M) :=
  match fn with
  | .op _ name _ =>
    let (argExpr, argErrs) := lexprToExpr ctx arg bound
    match name.name with
    | "not" => (.not default argExpr, argErrs)
    | _ => (.fvar default 0, argErrs ++ [.unsupportedConstruct s!"unary op {name.name}" default])
  | .app _ fn2 arg1 =>
    match fn2 with
    | .op _ name _ =>
      let (arg1Expr, arg1Errs) := lexprToExpr ctx arg1 bound
      let (arg2Expr, arg2Errs) := lexprToExpr ctx arg bound
      let allErrs := arg1Errs ++ arg2Errs
      match name.name with
      | "and" => (.and default arg1Expr arg2Expr, allErrs)
      | "or" => (.or default arg1Expr arg2Expr, allErrs)
      | "implies" => (.implies default arg1Expr arg2Expr, allErrs)
      | "equiv" => (.equiv default arg1Expr arg2Expr, allErrs)
      | "str_concat" => (.str_concat default arg1Expr arg2Expr, allErrs)
      | "str_inregex" => (.str_inregex default arg1Expr arg2Expr, allErrs)
      | _ => (.fvar default 0, allErrs ++ [.unsupportedConstruct s!"binary op {name.name}" default])
    | .app _ fn3 arg1 =>
      match fn3 with
      | .op _ name _ =>
        let (arg1Expr, arg1Errs) := lexprToExpr ctx arg1 bound
        let (arg2Expr, arg2Errs) := lexprToExpr ctx arg bound
        let (arg3Expr, arg3Errs) := lexprToExpr ctx arg bound
        let allErrs := arg1Errs ++ arg2Errs ++ arg3Errs
        match name.name with
        | "str_substr" => (.str_substr default arg1Expr arg2Expr arg3Expr, allErrs)
        | _ => (.fvar default 0, allErrs ++ [.unsupportedConstruct s!"ternary op {name.name}" default])
      | _ => (.fvar default 0, [.unsupportedConstruct "nested app" default])
    | _ => (.fvar default 0, [.unsupportedConstruct "complex app" default])
  | _ => (.fvar default 0, [.unsupportedConstruct "general app" default])


end

/-- Convert a type constructor declaration to CST -/
def typeConToCST [Inhabited M] (tcons : TypeConstructor)
    (_md : Imperative.MetaData Expression) :
    Command M × List (ASTToCSTError M) :=
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
  (.command_typedecl default name args, [])

/-- Convert a type synonym declaration to CST -/
def typeSynToCST [Inhabited M] (ctx : ToCSTContext) (syn : TypeSynonym)
    (_md : Imperative.MetaData Expression) :
    Command M × List (ASTToCSTError M) :=
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
  let ctx := ctx.addBoundTypeVars syn.typeArgs.toArray
  let (rhs, errs) := lmonoTyToCoreType ctx syn.type
  (.command_typesynonym default name args targs rhs, errs)

/-- Convert a function declaration to CST -/
def funcToCST [Inhabited M] (ctx : ToCSTContext)
    (func : Lambda.LFunc CoreLParams)
    (_md : Imperative.MetaData Expression) :
    Command M × List (ASTToCSTError M) :=
  let name : Ann String M := ⟨default, func.name.name⟩
  let typeArgs : Ann (Option (TypeArgs M)) M :=
    if func.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      -- FIXME
      ⟨default, none⟩
      -- let tvars : Array (TypeVar M) := (func.typeArgs.map fun tv =>
      --   TypeVar.type_var (Ann.mk default tv : Ann String M) : TypeVar M).toArray
      -- ⟨default, some (TypeArgs.type_args default (Ann.mk default tvars))⟩
  let (bindings, bindErrs, paramNames) := func.inputs.foldl
    (init := ([], [], #[]))
    fun (acc, errs, names) (id, ty) =>
      let paramName : Ann String M := ⟨default, id.name⟩
      let (paramType, tyErrs) := lmonoTyToCoreType ctx ty
      let binding := Binding.mkBinding default paramName
        (TypeP.expr paramType)
      (acc ++ [binding], errs ++ tyErrs, names.push id.name)
  let b : Bindings M := .mkBindings default ⟨default,
    bindings.toArray⟩
  let (r, retErrs) := lmonoTyToCoreType ctx func.output
  let allErrs := bindErrs ++ retErrs
  match func.body with
  | none =>
    (.command_fndecl default name typeArgs b r, allErrs)
  | some body =>
    let bodyCtx := { ctx with boundVars := ctx.boundVars ++ paramNames }
    let (bodyExpr, bodyErrs) := lexprToExpr bodyCtx body true
    let inline? : Ann (Option (Inline M)) M := ⟨default, none⟩
    (.command_fndef default name typeArgs b r bodyExpr inline?,
     allErrs ++ bodyErrs)

/-- Convert a `Core.Decl` to a Core `Command`, returning updated context -/
def declToCST [Inhabited M] (ctx : ToCSTContext) (decl : Core.Decl) :
    Command M × List (ASTToCSTError M) × ToCSTContext :=
  match decl with
  | .type (.con tcons) md =>
    let ctx := ctx.addFreeVar tcons.name
    let (cmd, errs) := typeConToCST tcons md
    (cmd, errs, ctx)
  | .type (.syn syn) md =>
    let ctx := ctx.addFreeVar syn.name
    let (cmd, errs) := typeSynToCST ctx syn md
    (cmd, errs, ctx)
  | .func func md =>
    let ctx := ctx.addFreeVar func.name.name
    let (cmd, errs) := funcToCST ctx func md
    (cmd, errs, ctx)
  | _ =>
    let name : Ann String M := ⟨default, "TODO"⟩
    let args : Ann (Option (Bindings M)) M := ⟨default, none⟩
    (.command_typedecl default name args,
     [.unsupportedConstruct "unimplemented decl" default], ctx)

/-- Convert `Core.Program` to a list of CST `Commands` -/
def programToCST [Inhabited M] (ctx : ToCSTContext)
    (prog : Core.Program) :
    List (Command M) × List (ASTToCSTError M) :=
  let (cmds, errs, _) := prog.decls.foldl
    (init := ([], [], ctx))
    fun (cmds, errs, ctx) decl =>
      let (cmd, declErrs, ctx') := declToCST ctx decl
      (cmds ++ [cmd], errs ++ declErrs, ctx')
  (cmds, errs)

end ToCST

---------------------------------------------------------------------

end Strata

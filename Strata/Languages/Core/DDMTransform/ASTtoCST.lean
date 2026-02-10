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
  deriving Inhabited

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

def addFreeVar (ctx : ToCSTContext) (name : String) :
    ToCSTContext :=
  { ctx with freeVars := ctx.freeVars.push name }

def addBoundVar (ctx : ToCSTContext) (name : String) :
    ToCSTContext :=
  { ctx with boundVars := ctx.boundVars.push name }

end ToCSTContext

/-- Convert `LMonoTy` to `CoreType` -/
def lmonoTyToCoreType [Inhabited M] (ty : Lambda.LMonoTy) :
    CoreType M × List (ASTToCSTError M) :=
  match ty with
  | .tcons "bool" [] => (.bool default, [])
  | .int => (.int default, [])
  | .tcons "string" [] => (.string default, [])
  | .tcons "regex" [] => (.regex default, [])
  | .real => (.real default, [])
  | .bitvec 1 => (.bv1 default, [])
  | .bitvec 8 => (.bv8 default, [])
  | .bitvec 16 => (.bv16 default, [])
  | .bitvec 32 => (.bv32 default, [])
  | .bitvec 64 => (.bv64 default, [])
  | .tcons "Map" [k, v] =>
    let (kty, kerrs) := lmonoTyToCoreType k
    let (vty, verrs) := lmonoTyToCoreType v
    (.Map default kty vty, kerrs ++ verrs)
  | _ =>
    (.bool default, [.unsupportedConstruct s!"type {ty}" default])

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

/-- Convert `Lambda.LExpr` to Core `Expr` -/
partial def lexprToExpr [Inhabited M] (ctx : ToCSTContext)
    (e : Lambda.LExpr CoreLParams.mono)
    -- LambdaFVarsBound is true when `e` corresponds to the body of a function
    -- where `.fvars` correspond to the formals.
    (LambdaFVarsBound : Bool := false) :
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
  | .op _ _name _ =>
    (.fvar default 0, [.unsupportedConstruct "op" default])
  | .app _ _ _ =>
    (.fvar default 0, [.unsupportedConstruct "app" default])
  | .abs _ _ _ =>
    (.fvar default 0, [.unsupportedConstruct "lambda" default])
  | _ =>
    (.fvar default 0, [.unsupportedConstruct "unknown expr" default])

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
        let paramType := TypeP.expr (CoreType.bool default)
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  (.command_typedecl default name args, [])

/-- Convert a type synonym declaration to CST -/
def typeSynToCST [Inhabited M] (syn : TypeSynonym)
    (_md : Imperative.MetaData Expression) :
    Command M × List (ASTToCSTError M) :=
  let name : Ann String M := ⟨default, syn.name⟩
  let args : Ann (Option (Bindings M)) M :=
    if syn.typeArgs.isEmpty then
      ⟨default, none⟩
    else
      let bindings := syn.typeArgs.map fun param =>
        let paramName : Ann String M := ⟨default, param⟩
        let paramType := TypeP.expr (CoreType.bool default)
        Binding.mkBinding default paramName paramType
      ⟨default, some (.mkBindings default ⟨default, bindings.toArray⟩)⟩
  let targs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let (rhs, errs) := lmonoTyToCoreType syn.type
  (.command_typesynonym default name args targs rhs, errs)

/-- Convert a function declaration to CST -/
def funcToCST [Inhabited M] (ctx : ToCSTContext)
    (func : Lambda.LFunc CoreLParams)
    (_md : Imperative.MetaData Expression) :
    Command M × List (ASTToCSTError M) :=
  let name : Ann String M := ⟨default, func.name.name⟩
  let typeArgs : Ann (Option (TypeArgs M)) M := ⟨default, none⟩
  let (bindings, bindErrs, paramNames) := func.inputs.foldl
    (init := ([], [], #[]))
    fun (acc, errs, names) (id, ty) =>
      let paramName : Ann String M := ⟨default, id.name⟩
      let (paramType, tyErrs) := lmonoTyToCoreType ty
      let binding := Binding.mkBinding default paramName
        (TypeP.expr paramType)
      (acc ++ [binding], errs ++ tyErrs, names.push id.name)
  let b : Bindings M := .mkBindings default ⟨default,
    bindings.toArray⟩
  let (r, retErrs) := lmonoTyToCoreType func.output
  let allErrs := bindErrs ++ retErrs
  match func.body with
  | none =>
    (.command_fndecl default name typeArgs b r, allErrs)
  | some body =>
    let bodyCtx := { ctx with boundVars := ctx.boundVars ++ paramNames }
    let (bodyExpr, bodyErrs) := lexprToExpr bodyCtx body (LambdaFVarsBound := true)
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
    let (cmd, errs) := typeSynToCST syn md
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

-- Convert Core.Program to a list of Commands
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

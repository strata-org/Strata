/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Expressions
import Strata.DL.Imperative.TypeContext
import Strata.DL.Lambda.Factory

namespace Core
open Lambda Imperative
open Std (ToFormat Format format)
open Strata (DiagnosticModel FileRange)

---------------------------------------------------------------------

namespace CmdType

def isBoolType (ty : LTy) : Bool :=
  match ty with
  | .forAll [] LMonoTy.bool => true
  | _ => false

def lookup (Env : TEnv Unit) (x : CoreIdent) : Option LTy :=
  Env.context.types.find? x

def update (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) : TEnv Unit :=
  Env.addInNewestContext (T := CoreLParams) [(x, ty)]

def freeVars (e : (LExpr CoreLParams.mono)) : List CoreIdent :=
  (LExpr.freeVars e).map (fun (i, _) => i)

/--
Preprocess a user-facing type in Core amounts to converting a poly-type (i.e.,
`LTy`) to a mono-type (i.e., `LMonoTy`) via instantiation. We still return an
`LTy`, with no bound variables.
-/
def preprocess (C: LContext CoreLParams) (Env : TEnv Unit) (ty : LTy) :
    Except DiagnosticModel (LTy × TEnv Unit) := do
  let (mty, Env) ← ty.instantiateWithCheck C Env |>.mapError DiagnosticModel.fromFormat
  return (.forAll [] mty, Env)

def postprocess (_: LContext CoreLParams) (Env: TEnv Unit) (ty : LTy) :
    Except DiagnosticModel (LTy × TEnv Unit) := do
  if h: ty.isMonoType then
    let ty := LMonoTy.subst Env.stateSubstInfo.subst (ty.toMonoType h)
    .ok (.forAll [] ty, Env)
  else
    .error <| DiagnosticModel.fromFormat f!"[postprocess] Expected mono-type; instead got {ty}"

/--
The inferred type of `e` will be an `LMonoTy`, but we return an `LTy` with no
bound variables.
-/
def inferType (C: LContext CoreLParams) (Env: TEnv Unit) (c : Cmd Expression) (e : LExpr CoreLParams.mono) :
    Except DiagnosticModel ((LExpr CoreLParams.mono) × LTy × TEnv Unit) := do
  -- We only allow free variables to appear in `init` statements. Any other
  -- occurrence leads to an error.
  let T ← match c with
    | .init _ _ _ _ =>
      let efv := LExpr.freeVars e
      .ok (Env.addInOldestContext efv)
    | _ =>
      let _ ← Env.freeVarCheck e f!"[{c}]" |>.mapError DiagnosticModel.fromFormat
      .ok Env
  let (ea, T) ← LExpr.resolve C T e |>.mapError DiagnosticModel.fromFormat
  let ety := ea.toLMonoTy
  return (ea.unresolved, (.forAll [] ety), T)

/--
Type constraints come from functions `inferType` and `preprocess`, both of which
are expected to return `LTy`s with no bound variables which can be safely
converted to `LMonoTy`s.
-/
def canonicalizeConstraints (constraints : List (LTy × LTy)) :
    Except DiagnosticModel Constraints := do
  match constraints with
  | [] => .ok []
  | (t1, t2) :: c_rest =>
    if h: t1.isMonoType && t2.isMonoType then
      let t1 := t1.toMonoType (by simp_all)
      let t2 := t2.toMonoType (by simp at h; simp_all only)
      let c_rest ← canonicalizeConstraints c_rest
      .ok ((t1, t2) :: c_rest)
    else
      .error <| DiagnosticModel.fromFormat f!"[canonicalizeConstraints] Expected to see only mono-types in \
                type constraints, but found the following instead:\n\
                t1: {t1}\nt2: {t2}\n"

def unifyTypes (Env: TEnv Unit) (constraints : List (LTy × LTy)) :
    Except DiagnosticModel (TEnv Unit) := do
  let constraints ← canonicalizeConstraints constraints
  let S ← Constraints.unify constraints Env.stateSubstInfo |> .mapError (fun f => DiagnosticModel.fromFormat (format f))
  let Env := Env.updateSubst S
  return Env

def typeErrorFmt (e : DiagnosticModel) : Format :=
  e.format none

---------------------------------------------------------------------

instance : Imperative.TypeContext Expression (LContext CoreLParams) (TEnv Unit) DiagnosticModel where
  isBoolType   := CmdType.isBoolType
  freeVars     := CmdType.freeVars
  preprocess   := CmdType.preprocess
  postprocess  := CmdType.postprocess
  update       := CmdType.update
  lookup       := CmdType.lookup
  inferType    := CmdType.inferType
  unifyTypes   := CmdType.unifyTypes
  typeErrorFmt := CmdType.typeErrorFmt

end CmdType
---------------------------------------------------------------------

end Core

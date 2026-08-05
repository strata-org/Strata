/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.TypeContext
import Strata.DL.Lambda.LExprT

namespace Core
open Lambda Imperative
open Std (ToFormat Format format)
open Strata (Message FileRange)

public section

---------------------------------------------------------------------

namespace CmdType

def isBoolType (ty : LTy) : Bool :=
  match ty with
  | .forAll [] LMonoTy.bool => true
  | _ => false

def lookup (Env : TEnv Unit) (x : CoreIdent) : Option LTy :=
  Env.context.types.find? x

def update (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) : TEnv Unit :=
  Env.addInNewestContext (T := CoreLParams) (Strata.Util.HMap.ofList [(x, ty)])

def freeVars (e : (LExpr CoreLParams.mono)) : List CoreIdent :=
  (LExpr.freeVars e).map (fun (i, _) => i)

/--
Preprocess a user-facing type in Core amounts to converting a poly-type (i.e.,
`LTy`) to a mono-type (i.e., `LMonoTy`) via instantiation. We still return an
`LTy`, with no bound variables.
-/
def preprocess (C: LContext CoreLParams) (Env : TEnv Unit) (ty : LTy) :
    Except Message (LTy × TEnv Unit) := do
  let (mty, Env) ← ty.instantiateWithCheck C Env |>.mapError Message.fromFormat
  return (.forAll [] mty, Env)

def postprocess (_: LContext CoreLParams) (Env: TEnv Unit) (ty : LTy) :
    Except Message (LTy × TEnv Unit) := do
  if h: ty.isMonoType then
    let ty := LMonoTy.subst Env.stateSubstInfo.subst (ty.toMonoType h)
    .ok (.forAll [] ty, Env)
  else
    .error <| Message.fromFormat f!"[postprocess] Expected mono-type; instead got {ty}"

/--
The inferred type of `e` will be an `LMonoTy`, but we return an `LTy` with no
bound variables.
-/
def inferType (C: LContext CoreLParams) (Env: TEnv Unit) (c : Cmd Expression) (e : LExpr CoreLParams.mono) :
    Except Message ((LExpr CoreLParams.mono) × LTy × TEnv Unit) := do
  let _ ← Env.freeVarCheck e f!"[{c}]" |>.mapError Message.fromFormat
  let T := Env
  let (ea, T) ← LExpr.resolve C T e |>.mapError Message.fromFormat
  let ety := ea.toLMonoTy
  return (ea.unresolved, (.forAll [] ety), T)

/--
Type constraints come from functions `inferType` and `preprocess`, both of which
are expected to return `LTy`s with no bound variables which can be safely
converted to `LMonoTy`s.
-/
def canonicalizeConstraints (constraints : List (LTy × LTy)) :
    Except Message Constraints := do
  match constraints with
  | [] => .ok []
  | (t1, t2) :: c_rest =>
    if h: t1.isMonoType && t2.isMonoType then
      let t1 := t1.toMonoType (by simp_all)
      let t2 := t2.toMonoType (by simp at h; simp_all only)
      let c_rest ← canonicalizeConstraints c_rest
      .ok ((t1, t2) :: c_rest)
    else
      .error <| Message.fromFormat f!"[canonicalizeConstraints] Expected to see only mono-types in \
                type constraints, but found the following instead:\n\
                t1: {t1}\nt2: {t2}\n"

def unifyTypes (Env: TEnv Unit) (constraints : List (LTy × LTy)) :
    Except Message (TEnv Unit) := do
  let constraints ← canonicalizeConstraints constraints
  let S ← Constraints.unify constraints Env.stateSubstInfo |> .mapError (fun f => Message.fromFormat (format f))
  let Env := Env.updateSubst S
  return Env

def typeErrorFmt (e : Message) : Format :=
  e.format none

---------------------------------------------------------------------

instance : Imperative.TypeContext Expression (LContext CoreLParams) (TEnv Unit) Message where
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

end
end Core

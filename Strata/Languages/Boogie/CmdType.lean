/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Boogie.OldExpressions
import Strata.Languages.Boogie.Expressions
import Strata.DL.Imperative.TypeContext
import Strata.DL.Lambda.Factory

namespace Boogie
open Lambda Imperative
open Std (ToFormat Format format)

-- Local instance for LFunc formatting
instance : ToFormat (LFunc BoogieLParams) where
  format f := f!"func {f.name}"
---------------------------------------------------------------------

namespace CmdType

def isBoolType (ty : LTy) : Bool :=
  match ty with
  | .forAll [] LMonoTy.bool => true
  | _ => false

def lookup (Env : (TEnv BoogieLParams)) (x : BoogieIdent) : Option LTy :=
  Env.context.types.find? x

def update (Env : TEnv BoogieLParams) (x : BoogieIdent) (ty : LTy) : TEnv BoogieLParams :=
  Env.insertInContext x ty

def freeVars (e : (LExpr BoogieLParams.mono)) : List BoogieIdent :=
  (LExpr.freeVars e).map (fun (i, _) => i)

/--
Preprocess a user-facing type in Boogie amounts to converting a poly-type (i.e.,
`LTy`) to a mono-type (i.e., `LMonoTy`) via instantiation. We still return an
`LTy`, with no bound variables.
-/
def preprocess (Env : TEnv BoogieLParams) (ty : LTy) : Except Format (LTy × TEnv BoogieLParams) := do
  let (mty, Env) ← ty.instantiateWithCheck Env
  return (.forAll [] mty, Env)

def postprocess (Env: TEnv BoogieLParams) (ty : LTy) : Except Format (LTy × TEnv BoogieLParams) := do
  if h: ty.isMonoType then
    let ty := LMonoTy.subst Env.state.substInfo.subst (ty.toMonoType h)
    .ok (.forAll [] ty, Env)
  else
    .error f!"[postprocess] Expected mono-type; instead got {ty}"

/--
The inferred type of `e` will be an `LMonoTy`, but we return an `LTy` with no
bound variables.
-/
def inferType (Env: TEnv BoogieLParams) (c : Cmd Expression) (e : (LExpr BoogieLParams.mono)) :
    Except Format ((LExpr BoogieLParams.mono) × LTy × TEnv BoogieLParams) := do
  -- We only allow free variables to appear in `init` statements. Any other
  -- occurrence leads to an error.
  let T ← match c with
    | .init _ _ _ _ =>
      let efv := LExpr.freeVars e
      .ok (Env.addInOldestContext efv)
    | _ =>
      let _ ← Env.freeVarCheck e f!"[{c}]"
      .ok Env
  let e := OldExpressions.normalizeOldExpr e
  let (ea, T) ← LExpr.fromLExpr T e
  let ety := ea.toLMonoTy
  return (ea.unresolved, (.forAll [] ety), T)

/--
Type constraints come from functions `inferType` and `preprocess`, both of which
are expected to return `LTy`s with no bound variables which can be safely
converted to `LMonoTy`s.
-/
def canonicalizeConstraints (constraints : List (LTy × LTy)) : Except Format Constraints := do
  match constraints with
  | [] => .ok []
  | (t1, t2) :: c_rest =>
    if h: t1.isMonoType && t2.isMonoType then
      let t1 := t1.toMonoType (by simp_all)
      let t2 := t2.toMonoType (by simp at h; simp_all only)
      let c_rest ← canonicalizeConstraints c_rest
      .ok ((t1, t2) :: c_rest)
    else
      .error f!"[canonicalizeConstraints] Expected to see only mono-types in \
                type constraints, but found the following instead:\n\
                t1: {t1}\nt2: {t2}\n"

def unifyTypes (Env: TEnv BoogieLParams) (constraints : List (LTy × LTy)) : Except Format (TEnv BoogieLParams) := do
  let constraints ← canonicalizeConstraints constraints
  let S ← Constraints.unify constraints Env.state.substInfo
  let Env := Env.updateSubst S
  return Env

---------------------------------------------------------------------

instance : Imperative.TypeContext Expression (TEnv BoogieLParams) where
  isBoolType  := CmdType.isBoolType
  freeVars    := CmdType.freeVars
  preprocess  := CmdType.preprocess
  postprocess := CmdType.postprocess
  update      := CmdType.update
  lookup      := CmdType.lookup
  inferType   := CmdType.inferType
  unifyTypes  := CmdType.unifyTypes

end CmdType
---------------------------------------------------------------------

end Boogie

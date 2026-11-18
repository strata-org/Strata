/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.FunctionType

public section

namespace Core

open Lambda
open Std (Format ToFormat format)

/-- The bodyless factory entry with the checked signature. -/
def CheckedSignature.stub (sig : CheckedSignature) : LFunc CoreLParams :=
  Lambda.LFuncDefined.toLFunc
    ({ name := sig.func.name, typeArgs := sig.func.typeArgs,
       inputs := sig.func.inputs.keys.zip sig.inputs, output := sig.output } : Function)

namespace RecFuncBlock

/-- Check a member `func` of the block `funcs` up to its expressions: its name is new to `C`,
    it is marked recursive and not inline, its signature names are valid as written with the
    functions of `C` and the members of `funcs` in scope, and its signature resolves. The
    signature is resolved with the member's reserved type parameters renamed as for the full
    member: the fresh names avoid the type variables of the member's expressions. -/
def checkSignature (C : Expression.TyContext) (Env : Expression.TyEnv)
    (funcs : List Function) (func : Function) : Except Format CheckedSignature := do
  Function.checkNameFresh C func
  if func.attr.any (· == .inline) then
    throw f!"recursive function '{func.name}' cannot be marked inline"
  unless func.isRecursive do
    throw f!"recursive function block member '{func.name}' must be marked recursive"
  Function.checkHeaderNames (fun n => n ∈ C.functions ∨ n ∈ funcs.map (·.name.name)) func
  Function.renameAndResolve C Env func

/-- Extend a context with every stub. -/
def stubContext (C : Expression.TyContext) (stubs : List (LFunc CoreLParams)) :
    Expression.TyContext :=
  stubs.foldl (fun C stub => C.addFactoryFunction stub) C

/-- Extend the incoming context with every fully checked member. -/
def fullContext (C : Expression.TyContext) (funcs : List Function) :
    Expression.TyContext :=
  funcs.foldl (fun C func => C.addFactoryFunction func.toLFunc) C

/-- Type check a mutually recursive function block: check every signature, then every body
    against `C` extended with all signature stubs, with rigid constants that avoid the names of
    `S` and of the stubs' signatures. Return the checked functions, `C` extended with them, the
    environment, and `S` extended with the type names of the registered stubs' signatures. -/
def typeCheckIn (S : Std.HashSet String) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (funcs : List Function) :
    Except Format
      (List Function × Expression.TyContext × Expression.TyEnv × Std.HashSet String) := do
  if funcs.isEmpty then
    throw f!"recursive function block must contain at least one function"
  let sigs ← funcs.mapM (checkSignature C Env funcs)
  let Cstub := stubContext C (sigs.map (·.stub))
  let S := S.insertMany (Factory.tyNamesFrom C.functions.toArray.size Cstub.functions)
  let funcs' ← sigs.mapM fun sig => Prod.fst <$>
    Function.checkDefinition (Thunk.pure S) Cstub Env sig.func sig.output sig.inputs
      sig.tyNames
  .ok (funcs', fullContext C funcs', Env, S)

/-- Type check a mutually recursive function block (`typeCheckIn`) with rigid constants that
    avoid the type names in scope in `C` and `Env`. -/
def typeCheck (C : Expression.TyContext) (Env : Expression.TyEnv)
    (funcs : List Function) :
    Except Format (List Function × Expression.TyContext × Expression.TyEnv) := do
  let (funcs', C', Env', _) ← typeCheckIn (scopeTyNameThunk C Env).get C Env funcs
  .ok (funcs', C', Env')

end RecFuncBlock

end Core

end -- public section

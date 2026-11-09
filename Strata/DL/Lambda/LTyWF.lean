/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyWFSpec

/-! ## Executable checking for Lambda monotypes -/

namespace Lambda

open Std (Format)

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta]

public section

/-- Check a resolved monotype against the variable policy and known constructors. An unknown
    constructor is reported against the written type `source` and the aliases in scope. -/
public def LMonoTy.typeCheckResolved (ty : LMonoTy) (C : LContext T)
    (admissible : TyVarAdmissibility) (source : LMonoTy := ty) (aliases : List TypeAlias := []) :
    Except Format LMonoTy :=
  if !ty.freeVars.all admissible then
    .error f!"Type {ty} contains a free type variable that is not admissible here."
  else if ty.knownInstance C.knownTypes then
    .ok ty
  else
    .error (unregisteredTypeError (Std.format source) source aliases C.knownTypes)

/-- Resolve aliases, then check the resulting monotype. -/
public def LMonoTy.typeCheckSource (ty : LMonoTy) (C : LContext T)
    (Env : TEnv T.IDMeta) (admissible : TyVarAdmissibility) :
    Except Format (LMonoTy × TEnv T.IDMeta) := do
  let (resolved, Env') ← ty.resolveAliases Env
  let checked ← resolved.typeCheckResolved C admissible ty Env.context.aliases
  .ok (checked, Env')

/-- Register a type alias after checking its declaration, storing its alias-resolved body. -/
def TEnv.addTypeAlias (alias : TypeAlias) (C : LContext T)
    (Env : TEnv T.IDMeta) : Except Format (TEnv T.IDMeta) := do
  if !alias.typeArgs.Nodup then
    .error f!"[TEnv.addTypeAlias] Duplicates found in the type arguments!\n\
               Name: {alias.name}\n\
               Type Arguments: {alias.typeArgs}\n\
               Type Definition: {alias.type}"
  else if !(alias.type.freeVars ⊆ alias.typeArgs) then
    .error f!"[TEnv.addTypeAlias] Type definition contains free type arguments!\n\
              Name: {alias.name}\n\
              Type Arguments: {alias.typeArgs}\n\
              Type Definition: {alias.type}"
  else if let some a := alias.typeArgs.find? (fun v => v ∉ alias.type.freeVars) then
    .error f!"Type synonym '{alias.name}': type argument '{a}' is not used in the definition"
  else if C.knownTypes.containsName alias.name then
    .error f!"This type declaration's name is reserved!\n\
              {alias}\n\
              KnownTypes' names:\n\
              {C.knownTypes.keywords}"
  else if Env.context.aliases.any (fun a => a.name == alias.name) then
    .error f!"This type declaration's name is already a type synonym!\n\
              {alias}\n\
              Existing type synonyms' names:\n\
              {Env.context.aliases.map (fun a => a.name)}"
  else
    let (rhsResolved, Env) ←
      LMonoTy.typeCheckSource alias.type C Env TyVarAdmissibility.all
    let newAliases := { typeArgs := alias.typeArgs,
                        name := alias.name,
                        type := rhsResolved } :: Env.context.aliases
    let context := { Env.context with aliases := newAliases }
    .ok (Env.updateContext context)

end

end Lambda

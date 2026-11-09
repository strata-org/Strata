/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv

/-! ## Declarative well-formedness of Lambda monotypes -/

namespace Lambda

public section

mutual
/-- A resolved monotype is well-formed when its variables are admissible and each constructor
    in it is registered at its arity. -/
inductive ResolvedTyWF (C : LContext T) (admissible : TyVarAdmissibility) :
    LMonoTy → Prop where
  | ftvar (h : admissible v = true) : ResolvedTyWF C admissible (.ftvar v)
  | bitvec : ResolvedTyWF C admissible (.bitvec n)
  | tcons (hknown : C.knownTypes.contains { name := name, metadata := args.length } = true)
      (hargs : ResolvedTysWF C admissible args) :
      ResolvedTyWF C admissible (.tcons name args)

/-- Every member of a resolved monotype list is well-formed. -/
inductive ResolvedTysWF (C : LContext T) (admissible : TyVarAdmissibility) :
    LMonoTys → Prop where
  | nil : ResolvedTysWF C admissible []
  | cons (hhead : ResolvedTyWF C admissible head)
      (htail : ResolvedTysWF C admissible tail) :
      ResolvedTysWF C admissible (head :: tail)
end

mutual
/-- Declarative alias resolution for one source monotype: arguments resolve first, and the first
    alias matching the constructor name and the resolved arity, if any, is expanded at them. -/
inductive SourceTyResolves (aliases : List TypeAlias) : LMonoTy → LMonoTy → Prop where
  | ftvar : SourceTyResolves aliases (.ftvar v) (.ftvar v)
  | bitvec : SourceTyResolves aliases (.bitvec n) (.bitvec n)
  | tcons
      (hargs : SourceTysResolve aliases args resolvedArgs)
      (hfind : aliases.find? (fun a => a.name == name &&
        a.typeArgs.length == resolvedArgs.length) = none) :
      SourceTyResolves aliases (.tcons name args) (.tcons name resolvedArgs)
  | alias
      (hargs : SourceTysResolve aliases args resolvedArgs)
      (hfind : aliases.find? (fun a => a.name == name &&
        a.typeArgs.length == resolvedArgs.length) = some alias) :
      SourceTyResolves aliases (.tcons name args) (alias.expand resolvedArgs)

/-- Declarative alias resolution for a source monotype list. -/
inductive SourceTysResolve (aliases : List TypeAlias) : LMonoTys → LMonoTys → Prop where
  | nil : SourceTysResolve aliases [] []
  | cons (hhead : SourceTyResolves aliases head resolvedHead)
      (htail : SourceTysResolve aliases tail resolvedTail) :
      SourceTysResolve aliases (head :: tail) (resolvedHead :: resolvedTail)
end

/-- A source monotype is well-formed, with resolution `resolved`, when alias resolution turns it
    into `resolved` and `resolved` is a well-formed resolved monotype. -/
structure SourceTyWF (C : LContext T) (admissible : TyVarAdmissibility)
    (aliases : List TypeAlias) (ty resolved : LMonoTy) : Prop where
  hresolve : SourceTyResolves aliases ty resolved
  htype : ResolvedTyWF C admissible resolved

end

end Lambda

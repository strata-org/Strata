/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.Function
public import Strata.DL.Lambda.LExprWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.Util.HMaps

/-! ## Definitions shared by the typing relation and the typing rules of `ProgramTypeSpec`

Variable scopes, the conditions on expression annotations, and the condition on factory
extensions. -/

public section

namespace Core

open Lambda Imperative

/-- The scope binding each formal at the trivial scheme over its own type. -/
abbrev formalsScope (sigR : @LMonoTySignature Unit) : Strata.Util.HMap CoreIdent LTy :=
  Strata.Util.HMap.ofList (sigR.map (fun q => (q.1, LTy.forAll [] q.2)))

namespace TypeSpec

open LExpr

/-- The stack of variable scopes of a type scope. -/
abbrev TypeScopes := Strata.Util.HMaps (Lambda.Identifier Unit) LTy

/-- Every binder annotation in `e` applies only type constructors registered at their arity. -/
@[expose] def BinderAnnotsKnown (C : LContext CoreLParams) (e : Expression.Expr) : Prop :=
  ∀ t ∈ LExpr.binderAnnotations e, LMonoTy.knownInstance t C.knownTypes = true

/-- The annotations of `e` agree with the variable scopes `ts` and the function table of `C`. -/
structure ScopesAnnotAgree (C : LContext CoreLParams) (ts : TypeScopes) (e : Expression.Expr) :
    Prop where
  /-- Every annotated free variable is declared in `ts` at its annotation. -/
  fvarsDeclared : ∀ x ann, (x, some ann) ∈ LExpr.freeVars e →
    ts.find? x = some (.forAll [] ann)
  /-- Every operator annotation is an instance of the body of its function's type scheme. -/
  opsInstantiate : ∀ o ty, (o, ty) ∈ LExpr.opAnnots e →
    ∃ f xs body, C.functions[o.name]? = some f ∧ f.type = .ok (.forAll xs body) ∧
      ∃ τ, ty = LMonoTy.subst τ body
  /-- Every operator names a function of `C`. -/
  opsKnown : ∀ o ∈ LExpr.getOps e, (C.functions[o.name]?).isSome

/-- The variable scopes `ts` with one new scope binding each input parameter to its type. -/
def procInputScopes (ts : TypeScopes) (proc : Procedure) : TypeScopes :=
  ts.push (formalsScope proc.header.inputs)

/-- The variable scopes `ts` with one new scope binding the inputs, outputs and `old` in-outs. -/
def procBodyScopes (ts : TypeScopes) (proc : Procedure) : TypeScopes :=
  let oldSig : @LMonoTySignature Unit :=
    proc.header.getInoutParams.map (fun (id, ty) => (CoreIdent.mkOld id.name, ty))
  ts.push (formalsScope (oldSig ++ proc.header.outputs ++ proc.header.inputs))

/-- The variable scopes `ts` with one new scope binding each formal to its declared monotype. -/
def funcScopes (ts : TypeScopes) (func : Function) : TypeScopes :=
  ts.push (formalsScope func.inputs)

/--
`C'` is `C` with, for each function in `newFuncs`, an entry under its name that `agrees` with it;
old entries and other fields are unchanged and no other names appear.

The extension is stated declaratively rather than as the fold that adds `newFuncs` to `C`, so
proofs about it need no induction over the fold.
-/
structure FactoryExtendedBy (agrees : LFunc CoreLParams → LFunc CoreLParams → Prop)
    (C C' : LContext CoreLParams) (newFuncs : List (LFunc CoreLParams)) : Prop where
  -- Every field except `functions` is unchanged.
  knownTypes_eq : C'.knownTypes = C.knownTypes
  datatypes_eq : C'.datatypes = C.datatypes
  idents_eq : C'.idents = C.idents
  rigidTypeVars_eq : C'.rigidTypeVars = C.rigidTypeVars
  /-- Every entry of `C`'s factory is unchanged. -/
  preserves_old : ∀ (nm : String) (g : LFunc CoreLParams),
      C.functions[nm]? = some g → C'.functions[nm]? = some g
  /-- Each new function's name holds an entry that `agrees` with the function. -/
  contains_new : ∀ f ∈ newFuncs, ∃ g, C'.functions[f.name.name]? = some g ∧ agrees f g
  /-- No name is present in `C'` unless it was in `C` or is one of the new
      functions. -/
  no_other : ∀ nm ∈ C'.functions, nm ∈ C.functions ∨ nm ∈ newFuncs.map (·.name.name)

end TypeSpec

end Core

end -- public section

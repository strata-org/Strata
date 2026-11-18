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

Variable scopes (with `TypeScopes.addInits`, `addCFGInits` and `monoType?`), the conditions
on expression annotations, and the condition on factory extensions. -/

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

/-- `vt` with the variable `x` of type `ty` added to the newest scope. -/
def TypeScopes.addInit (vt : TypeScopes) (x : Expression.Ident) (ty : LTy) : TypeScopes :=
  vt.pop.push (vt.newest.insert x ty)

/-- `vt` with each variable an `init` of `ss` declares added to the newest scope. -/
def TypeScopes.addInits (vt : TypeScopes) (ss : List Statement) :
    TypeScopes :=
  ss.foldl (init := vt) fun vt s =>
    match s with
    | .init x ty _ _ => vt.addInit x ty
    | _ => vt

/-- `vt` with each variable an `init` command of any block of `g` declares added to the newest
    scope. A CFG has no nested scopes, and its checker rejects a local declared at two types or
    with the name of a header variable, so the one flat scope gives each variable exactly its
    declared type. -/
def TypeScopes.addCFGInits (vt : TypeScopes) (g : DetCFG) : TypeScopes :=
  g.blocks.foldl (init := vt) fun vt (_, b) =>
    b.cmds.foldl (init := vt) fun vt c =>
      match c with
      | .cmd (.init x ty _ _) => vt.addInit x ty
      | _ => vt

/-- The monotype `vt` declares for the variable `x`. -/
def TypeScopes.monoType? (vt : TypeScopes) (x : Expression.Ident) :
    Option Lambda.LMonoTy :=
  (vt.find? x).bind Lambda.LTy.toMonoType?

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

/-- `ren` renames distinct type parameters among `typeArgs` to distinct new names, none of
    them among `mentioned`, the type variables of the declaration. So the renamed declaration
    means the same, and no type parameter turns into another type variable of the
    declaration. -/
def TyArgRenamingCore (typeArgs mentioned : List String) (ren : List (String × String)) : Prop :=
  (ren.map Prod.fst).Nodup ∧ (ren.map Prod.snd).Nodup ∧
    ∀ p ∈ ren, p.1 ∈ typeArgs ∧ p.2 ∉ mentioned

/-- An injective renaming of type parameters to names the declaration does not
    mention (`TyArgRenamingCore`) that renames only type parameters with a
    reserved prefix, to names that are neither rigid in `C` nor free in the type
    of a variable of `Γ`. -/
def TyArgRenaming (C : LContext CoreLParams) (Γ : TContext Unit)
    (typeArgs mentioned : List String) (ren : List (String × String)) : Prop :=
  TyArgRenamingCore typeArgs mentioned ren ∧
    ∀ p ∈ ren, isAllowedName p.1 = false ∧ p.2 ∉ C.rigidTypeVars ∧
      TContext.isFresh (T := CoreLParams) p.2 Γ

end TypeSpec

end Core

end -- public section

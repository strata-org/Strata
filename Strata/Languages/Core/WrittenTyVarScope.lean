/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
import Strata.Util.Name

public section

namespace Core

open Lambda Imperative

/-! ## Scoping written type variables

Written type variables get checker names unique to the scope of the declaration binding them. -/

namespace WrittenTyVarScope

/-- The checker name of each written type variable bound in the open scopes. -/
abbrev ScopeMap := List (TyIdentifier × TyIdentifier)

/-- The walk state that is never restored: the written type variables met so far, and the
    names a fresh name must avoid. -/
structure ScopeState where
  seen : List TyIdentifier
  avoid : List TyIdentifier

/-- The checker name of a written type variable: its binding in `m`, or the variable itself. -/
def checkerName (m : ScopeMap) (v : TyIdentifier) : TyIdentifier :=
  (m.lookup v).getD v

/-- A name `base_k` not in `avoid` that a user may write; the base is `v`, or `t` when `v_1` is
    reserved. -/
def freshName (v : TyIdentifier) (avoid : List TyIdentifier) : TyIdentifier :=
  let base := if TyVarAdmissibility.notGeneratedOrRigid (v ++ "_1") then v else "t"
  Strata.Name.freshNameBy (fun n => n == base || avoid.contains n) (avoid.length + 1) base

/-- Bind each non-rigid variable of `vs` that `m` does not bind: to itself the first time the
    walk meets it, else to a fresh name. -/
def bindVars (rigid : List TyIdentifier) :
    List TyIdentifier → ScopeMap → ScopeState → ScopeMap × ScopeState
  | [], m, st => (m, st)
  | v :: vs, m, st =>
    if v ∈ rigid ∨ (m.lookup v).isSome then bindVars rigid vs m st
    else if v ∈ st.seen then
      let w := freshName v st.avoid
      bindVars rigid vs ((v, w) :: m) { st with avoid := w :: st.avoid }
    else bindVars rigid vs ((v, v) :: m) { seen := v :: st.seen, avoid := v :: st.avoid }

/-- Rename each free type variable `v` of `ty` to `f v`. -/
def renameTy (f : TyIdentifier → TyIdentifier) (ty : LMonoTy) : LMonoTy :=
  LMonoTy.subst [LExpr.buildSubstFromFunction (LMonoTy.freeVars ty) (fun v => .ftvar (f v))] ty

/-- The checker name of a type variable in an expression annotation; a name a user may not
    write is kept. -/
def annotName (m : ScopeMap) (v : TyIdentifier) : TyIdentifier :=
  if TyVarAdmissibility.notGeneratedOrRigid v then checkerName m v else v

/-- Rename the free-variable and binder annotations of an expression in scope `m`; operator
    annotations are kept. -/
def renameExpr (m : ScopeMap) (e : Expression.Expr) : Expression.Expr :=
  LExpr.replaceUserProvidedType e (renameTy (annotName m)) (fun _ uty => uty)

/-- `renameExpr` on an optional (nondeterministic) expression. -/
def renameExprOrNondet (m : ScopeMap) (e : ExprOrNondet Expression) :
    ExprOrNondet Expression :=
  e.map (renameExpr m)

/-- `renameExpr` on the input expressions of a call's arguments. -/
def renameCallArgs (m : ScopeMap) (args : List (CallArg Expression)) :
    List (CallArg Expression) :=
  args.map (CallArg.mapInput (renameExpr m))

/-- Rename a command in scope `m`. A declaration first binds its declared type's variables,
    which its initializer then sees. -/
def renameCmd (rigid : List TyIdentifier) (m : ScopeMap) (st : ScopeState) :
    Command → Command × ScopeMap × ScopeState
  | .cmd (.init x (.forAll [] ty) e md) =>
    let r := bindVars rigid (LMonoTy.freeVars ty) m st
    (.cmd (.init x (.forAll [] (renameTy (checkerName r.1) ty)) (renameExprOrNondet r.1 e) md),
      r.1, r.2)
  | .cmd (.init x (.forAll (a :: as) ty) e md) =>
    (.cmd (.init x (.forAll (a :: as) ty) e md), m, st)
  | .cmd (.set x e md) => (.cmd (.set x (renameExprOrNondet m e) md), m, st)
  | .cmd (.assert l e md) => (.cmd (.assert l (renameExpr m e) md), m, st)
  | .cmd (.assume l e md) => (.cmd (.assume l (renameExpr m e) md), m, st)
  | .cmd (.cover l e md) => (.cmd (.cover l (renameExpr m e) md), m, st)
  -- `tyArgs` is not renamed: the type checker, which checks the renamed call, discards it.
  | .call pname tyArgs args md => (.call pname tyArgs (renameCallArgs m args) md, m, st)

/-- The type variables of the free-variable and binder annotations in an expression. -/
def exprTyVars (e : Expression.Expr) : List TyIdentifier :=
  (LExpr.fvarAnnotations e ++ LExpr.binderAnnotations e).flatMap LMonoTy.freeVars

/-- The first type variable of a free-variable or binder annotation in `e` that is neither rigid
    nor bound in `m`; with `writable`, only type variables a user may write count. -/
def unboundAnnotVar? (writable : Bool) (rigid : List TyIdentifier) (m : ScopeMap)
    (e : Expression.Expr) : Option TyIdentifier :=
  (exprTyVars e).find? fun v =>
    (!writable || TyVarAdmissibility.notGeneratedOrRigid v) && !rigid.contains v &&
      (m.lookup v).isNone

/-- The error text for the first expression of `es` with an annotation type variable that
    `unboundAnnotVar?` reports; `none` when every expression is in scope. -/
def unboundAnnotMsg? (writable : Bool) (rigid : List TyIdentifier) (m : ScopeMap)
    (es : List Expression.Expr) : Option Std.Format :=
  (es.findSome? (unboundAnnotVar? writable rigid m)).map
    fun v => f!"type variable `{v}` is not in scope"

/-- The type variables of the declared types, the type arguments of calls, and the free-variable
    and binder annotations in a list of statements. -/
def stmtsTyVars (ss : List Statement) : List TyIdentifier :=
  stmtsCollect exprTyVars LMonoTy.freeVars ss

/-- The walk state at the start of `ss`: nothing met, and fresh names avoid `ambient`, `rigid`
    and every type variable `ss` writes. -/
def initState (rigid ambient : List TyIdentifier) (ss : List Statement) : ScopeState :=
  { seen := [], avoid := ambient ++ rigid ++ stmtsTyVars ss }

end WrittenTyVarScope

end Core

end -- public section

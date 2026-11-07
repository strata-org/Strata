/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Axiom
public import Strata.Languages.Core.Function
public import Strata.DL.Lambda.NamePrefixes

/-! # Abstracting calls in generated lemmas

The termination and well-formedness lemmas of a function `f` must hold
whatever `f` returns. Otherwise a non-terminating `f` whose definition is
contradictory would prove its own lemmas. `Lemma.forallAbstractingCalls` states a
lemma over the functions `fns` of a recursive block without mentioning them:
each monomorphic function `f` of `fns` becomes one universally quantified
variable `f_fn` of `f`'s type, which every occurrence of `f` in the lemma uses.
The lemma then holds for every function of that type, and keeps the fact that
equal arguments give equal results, so a check on `f(n - 1)` still covers
`f((n - 2) + 1)`.

A polymorphic function cannot become a single variable, since its calls may
stand at different instantiations, which are not known before the lemma is type
checked. Each occurrence of it gets a variable of its own, of the function's
declared type with its type parameters renamed apart, so that type checking
infers the instantiation of each call from its arguments, even when nothing
else in the lemma constrains the result. Two calls to a polymorphic function
are then not known to agree, even on identical arguments. This loses
precision, never soundness: a lemma that needs two such calls to agree, such
as a division by `plen(tl(xs))` guarded by `plen(tl(xs)) > 0`, cannot be
proved, but no invalid lemma is proved.

TODO: give each polymorphic function one variable per type instantiation, as
monomorphic functions get one variable, by abstracting after type checking or
by sharing variables on the inferred instantiation.

A lemma that does not mention the functions of `fns` can be declared before
them, so that their definitions never reach the solver when it is checked.
This relies on each obligation being sent only the CSE definitions it uses
(`pruneUnusedCSEDefinitions`): a definition shared from another obligation
could mention a function of `fns` and bring in its axioms.
-/

public section

namespace Core

open Lambda

private structure AbstractState where
  /-- The monomorphic functions replaced so far with the variable standing for
      each. -/
  shared : List (String × CoreIdent) := []
  /-- The variables introduced so far with their types, newest first. -/
  vars : List (CoreIdent × LMonoTy) := []
  /-- Names that a new variable must avoid. -/
  used : Std.HashSet String

/-- The type of `func`. For a polymorphic function, its type parameters are
    renamed apart, fresh for each occurrence of it, so that type checking infers
    each occurrence's instantiation on its own. -/
private def functionType (func : Function) : StateM AbstractState LMonoTy := do
  let declared := LMonoTy.mkArrow' func.output func.inputs.values
  if func.typeArgs.isEmpty then return declared
  let k := (← get).vars.length
  let S : Subst := [Strata.Util.HMap.ofList (func.typeArgs.map fun a =>
    (a, LMonoTy.ftvar s!"{abstractTyPrefix}{k}_{a}"))]
  return LMonoTy.subst S declared

/-- The variable standing for an occurrence of `func`: for a monomorphic
    function, the one already introduced for it, if any, and otherwise a new one
    named after `func` and of its type. -/
private def varFor (func : Function) : StateM AbstractState (LExpr CoreLParams.mono) := do
  let f := func.name.name
  let ty ← functionType func
  let st ← get
  match if func.typeArgs.isEmpty then st.shared.lookup f else none with
  | some x => return .fvar () x (some ty)
  | none =>
    let x : CoreIdent := ⟨Lemma.freshName st.used s!"{f}_fn", ()⟩
    set { st with shared := (f, x) :: st.shared, vars := (x, ty) :: st.vars,
                  used := st.used.insert x.name }
    return .fvar () x (some ty)

/-- Replace each occurrence of a function of `fns` by a variable of the
    function's type: the same variable for every occurrence of a monomorphic
    function, and a new one for each occurrence of a polymorphic one. -/
private def abstractFunctions (fns : List Function) :
    LExpr CoreLParams.mono → StateM AbstractState (LExpr CoreLParams.mono)
  | .op m f ty =>
    match fns.find? (·.name.name == f.name) with
    | some func => varFor func
    | none => pure (.op m f ty)
  | .app m fn arg => return .app m (← abstractFunctions fns fn) (← abstractFunctions fns arg)
  | .abs m n ty b => return .abs m n ty (← abstractFunctions fns b)
  | .quant m k n ty tr b =>
    return .quant m k n ty (← abstractFunctions fns tr) (← abstractFunctions fns b)
  | .ite m c t f =>
    return .ite m (← abstractFunctions fns c) (← abstractFunctions fns t)
      (← abstractFunctions fns f)
  | .eq m a b => return .eq m (← abstractFunctions fns a) (← abstractFunctions fns b)
  | e => pure e

/-- Quantify `e` universally over `binders`, after replacing the calls to the
    functions of `fns` by universally quantified variables, as described in
    the module documentation. The new variables are quantified inside
    `binders`.

    TODO: prove the two properties the termination and well-formedness checks
    rely on: the result mentions no function of `fns`, and the result implies
    `Lemma.forallOver binders e` for every interpretation of the functions of
    `fns`. -/
def Lemma.forallAbstractingCalls (fns : List Function) (binders : List (CoreIdent × LMonoTy))
    (e : LExpr CoreLParams.mono) : LExpr CoreLParams.mono :=
  let used := Std.HashSet.ofList (binders.map (·.1.name) ++ (LExpr.freeVars e).map (·.1.name))
  let (e, st) := (abstractFunctions fns e).run { used }
  Lemma.forallOver binders (Lemma.forallOver st.vars.reverse e)

end Core

end -- public section

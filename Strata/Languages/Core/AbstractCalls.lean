/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Axiom
public import Strata.Languages.Core.Function
import Strata.Util.Name

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
stand at different instantiations. Each occurrence of it gets a variable of its
own, whose type is the occurrence's annotation, which type checking sets to the
call's instantiation. An unannotated occurrence, which only input that is not
type checked contains, gets the function's declared type with its type
parameters renamed apart. Two calls to a polymorphic function are then not
known to agree, even on identical arguments. This loses precision, never
soundness: a lemma that needs two such calls to agree, such as a division by
`plen(tl(xs))` guarded by `plen(tl(xs)) > 0`, cannot be proved, but no invalid
lemma is proved.

TODO: give each polymorphic function one variable per type instantiation, as
monomorphic functions get one variable, by sharing variables on the annotated
instantiation.

A lemma that does not mention the functions of `fns` can be declared before
them, so that their definitions never reach the solver when it is checked.
This relies on each obligation being sent only the CSE definitions it uses
(`pruneUnusedCSEDefinitions`): a definition shared from another obligation
could mention a function of `fns` and bring in its axioms.
-/

public section

namespace Core

open Lambda

/-- Prefix of the type variables that instantiate a polymorphic function's type parameters
    where a generated lemma abstracts a call to it.
    Kept as a literal copy in `Lambda.reservedNamePrefixes`, so type checking still
    rejects or renames program names that use it. -/
@[expose] def abstractTyPrefix : String := "$__abs_"

private structure AbstractState where
  /-- The monomorphic functions replaced so far with the variable standing for
      each. -/
  shared : List (String × CoreIdent) := []
  /-- The variables introduced so far with their types, newest first. -/
  vars : List (CoreIdent × LMonoTy) := []
  /-- Names that a new variable must avoid. -/
  used : Std.HashSet String

/-- The type of an occurrence of `func` annotated `ty`. A monomorphic function
    has its declared type. A polymorphic one has the annotation, and without
    one its declared type with its type parameters renamed apart, fresh for each
    occurrence. -/
private def functionType (func : Function) (ty : Option LMonoTy) :
    StateM AbstractState LMonoTy := do
  let declared := LMonoTy.mkArrow' func.output func.inputs.values
  if func.typeArgs.isEmpty then return declared
  if let some ty := ty then return ty
  let k := (← get).vars.length
  let S : Subst := [Strata.Util.HMap.ofList (func.typeArgs.map fun a =>
    (a, LMonoTy.ftvar s!"{abstractTyPrefix}{k}_{a}"))]
  return LMonoTy.subst S declared

/-- The variable standing for an occurrence of `func` annotated `ty`: for a
    monomorphic function, the one already introduced for it, if any, and
    otherwise a new one named after `func` and of its type. -/
private def varFor (func : Function) (ty : Option LMonoTy) :
    StateM AbstractState (LExpr CoreLParams.mono) := do
  let f := func.name.name
  let ty ← functionType func ty
  let st ← get
  match if func.typeArgs.isEmpty then st.shared.lookup f else none with
  | some x => return .fvar coreLoc x (some ty)
  | none =>
    let x : CoreIdent := ⟨Strata.Name.freshName st.used s!"{f}_fn", ()⟩
    set { st with shared := (f, x) :: st.shared, vars := (x, ty) :: st.vars,
                  used := st.used.insert x.name }
    return .fvar coreLoc x (some ty)

/-- Replace each occurrence of a function of `fns` by a variable of the
    function's type: the same variable for every occurrence of a monomorphic
    function, and a new one for each occurrence of a polymorphic one. -/
private def abstractFunctions (fns : List Function) :
    LExpr CoreLParams.mono → StateM AbstractState (LExpr CoreLParams.mono)
  | .op m f ty =>
    match fns.find? (·.name.name == f.name) with
    | some func => varFor func ty
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

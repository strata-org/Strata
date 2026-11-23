/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote

/-! # Anonymous values: solver-invented elements of uninterpreted sorts

A solver model gives a variable of an uninterpreted sort (`type S;`) a value it
invented for the purpose, `@S_0` from cvc5 or `S!val!0` from z3: some element of `S`,
distinct from the model's other elements. *An anonymous value* is the Core
representation of such an element for counterexample replay: the operator
`.op default n (some S)`, where `n` is `anonName m S`, the solver's name `m` for the element
qualified by its sort, together with a nullary constructor `n : S` (`anonConstr n S`)
added to the factory replay evaluates with (`extendAnon`). The factory holds one
function per name, so the qualification is what keeps apart elements of different sorts
that a solver names alike: z3 names the first element of `S int` and of `S bool` both
`S!val!0`.

As constructors, anonymous values are canonical values, and the evaluator's
equality `LExpr.eql` decides two of them by identity with no change to it: the same
name is syntactically equal, and two different constructor names are distinct
(`eql_anon`).

No program can talk about an anonymous value. A program reaches an operator only
through a name it declares, and an anonymous value's name is the solver's name for the
element followed by ` : ` and the sort. The solver's name is not a declared name:
cvc5's begin with `@`, which SMT-LIB reserves for solvers and which
`escapeForSMT` never emits for a name of ours, and the model reader renames one that
collides with a name in play (`Strata.SMT.Symbol.ofSolverSymbol`). `extendAnon` also
leaves the factory unchanged at a name it already holds, so an anonymous value never
redefines a declared operator.

Anonymous values enter a counterexample only from a solver model, whose elements
satisfy the program's constraints on the sort. `defaultCanonicalValue` does not produce
them.

Key definitions: `anonName`, `anonConstr`, `anonElems`, `extendAnon`. -/

namespace Core

open Lambda

public section

/-- Whether a solver symbol is the solver's name for an element of an uninterpreted
    sort: cvc5 spells these with a leading `@`, z3 as `<sort>!val!<n>`. -/
@[expose] def isSolverElementName (n : String) : Bool :=
  n.startsWith "@" || (n.splitOn "!val!").length > 1

/-- `ty` is an uninterpreted sort of the program: a type constructor that is neither
    a built-in type (`KnownTypes`) nor the type of a constructor of `F`. -/
@[expose] def isUninterpretedSort (F : @Lambda.Factory CoreLParams) : LMonoTy → Bool
  | .tcons n _ =>
    !Core.KnownTypes.containsName n &&
      !F.toArray.any (fun f => f.isConstr && match f.output with
        | .tcons m _ => m == n
        | _ => false)
  | _ => false

/-- The name of the anonymous value for the solver's element `n` of sort `ty`: `n`
    qualified by `ty`, so that one solver name at two sorts gives two names. It keeps
    `n`'s leading `@` or its `!val!`, so it is still a solver element name
    (`isSolverElementName`). -/
@[expose] def anonName (n : String) (ty : LMonoTy) : String :=
  s!"{n} : {Std.format ty}"

/-- The nullary constructor standing for the anonymous value `n` of sort `ty`. -/
@[expose] def anonConstr (n : String) (ty : LMonoTy) : LFunc CoreLParams :=
  { name := ⟨n, ()⟩, inputs := [], output := ty, isConstr := true }

/-- The anonymous values occurring in `e`, with their sorts: every operator whose name
    is a solver element name and whose annotation is a monomorphic type. -/
@[expose] def anonElems : LExpr CoreLParams.mono → List (String × LMonoTy)
  | .op _ n (some ty) =>
    if isSolverElementName n.name && LMonoTy.freeVars ty == [] then [(n.name, ty)] else []
  | .app _ f a => anonElems f ++ anonElems a
  | _ => []

/-- Whether `e` contains a free variable named like a solver's element of an
    uninterpreted sort: the form a lifted model gives one before annotation. -/
@[expose] def hasSolverElementFvar : LExpr CoreLParams.mono → Bool
  | .fvar _ n _ => isSolverElementName n.name
  | .app _ f a => hasSolverElementFvar f || hasSolverElementFvar a
  | _ => false

/-- One anonymous value's constructor added to `F`, unless `F` already holds the name
    or the sort is not monomorphic. -/
@[expose] def pushAnon (F : @Lambda.Factory CoreLParams) (x : String × LMonoTy) :
    @Lambda.Factory CoreLParams :=
  if LMonoTy.freeVars x.2 = [] then F.pushIfNew (anonConstr x.1 x.2) else F

/-- `F` extended with a constructor for every anonymous value occurring in `vals`. -/
@[expose] def extendAnon (F : @Lambda.Factory CoreLParams) (vals : List (LExpr CoreLParams.mono)) :
    @Lambda.Factory CoreLParams :=
  (vals.flatMap anonElems).foldl pushAnon F

end -- public section

end Core

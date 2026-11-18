/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Axiom
public import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.FunctionType

public section

namespace Core

open Lambda
open Std (ToFormat Format format)

/-- Type check an axiom or lemma proposition `e` at type `bool` with `typeArgs`
    held rigid: written and stored annotations may mention no type variable
    other than `typeArgs`. The rigid constants avoid the registered types of
    `C`, the names in `scope` (the type names in scope) and `tyNames ()` (the
    type names `e` mentions). -/
def typeCheckProp (scope : Thunk (Std.HashSet String)) (kind : String)
    (name : CoreLabel) (typeArgs : List TyIdentifier)
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (e : Expression.Expr) (tyNames : Unit → List String) :
    Except Format (Expression.Expr × Expression.TyEnv) := do
  let σ := rigidNamesAvoiding C scope (Thunk.pure ∅) name tyNames typeArgs
  let (out, stored, EnvR) ←
    (Function.checkBoolProp (addSkolemTypes C σ) Env typeArgs σ (format e) (tyVarsIn typeArgs)
      e).mapError (fun m => f!"Error in {kind} {name}: {m}")
  if !stored then
    throw f!"{kind.capitalize} '{name}' is typed at a generated type variable that is not \
             declared"
  .ok (out, EnvR)

namespace Axiom

/-- Type check an axiom, a proposition with no type parameters, so no rigid constant needs a
    set of type names to avoid. -/
def typeCheckIn (C : Expression.TyContext) (Env : Expression.TyEnv) (a : Axiom) :
    Except Format (Expression.Expr × Expression.TyEnv) :=
  typeCheckProp (Thunk.pure ∅) "axiom" a.name [] C Env a.e fun _ => []

end Axiom

end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.PureExpr

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/--
`EvalError` denotes the kinds of errors that may arise during (partial)
evaluation of Imperative programs.
-/
inductive EvalError (P : PureExpr) where
  | InitVarExists (tid : P.TypedIdent) (existing_value : P.Expr)
  | AssignVarNotExists (tid : P.Ident) (value : P.Expr)
  | HavocVarNotExists (tid : P.Ident)
  | AssertFail (label : String) (b : P.Expr)
  | AssumeFail (label : String) (b : P.Expr)
  | LabelNotExists (label : String)
  | Misc (f : Format)
  | OutOfFuel

def EvalError.toFormat [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty]
    (e : EvalError P) : Format :=
  match e with
  | .InitVarExists var val =>
    (f!"[INIT ERROR] Variable {var} already exists, with current value {val}.")
  | AssignVarNotExists var val =>
    (f!"[ASSIGN ERROR] Variable {var} has not been declared yet, so it \
       cannot be assigned to {val}.")
  | HavocVarNotExists var =>
    (f!"[HAVOC ERROR] Variable {var} has not been declared yet, so it \
       cannot be havocked.")
  | AssertFail label b =>
    (f!"[ASSERT ERROR] Assertion {label} failed!{Format.line}{b}")
  | AssumeFail label b =>
    (f!"[ASSUME ERROR] Assumption {label} falsified!{Format.line}{b}")
  | LabelNotExists label =>
    (f!"[GOTO ERROR] Label {label} does not exist later in the program.")
  | OutOfFuel =>
    (f!"[ERROR] Ran out of fuel.")
  | Misc f =>
    (f!"[ERROR] {f}")

instance [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty] : ToFormat (EvalError P) where
  format := EvalError.toFormat

---------------------------------------------------------------------

end Imperative

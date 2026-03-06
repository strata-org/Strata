/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.Cmd

namespace Imperative
open Std (ToFormat Format format)

---------------------------------------------------------------------

/--
Interface that must be provided to instantiate the type checker for Imperative's
commands (`Cmds.typeCheck`) for expressions specified using `PureExpr`. A
description of some parameters is as follows:

`TypeError`: Kinds of errors that can arise during type checking Imperative's
commands.

`Context`: contains information that does not change throughout type checking,
such as known types and known functions.

`TypeEnv`: contains a map of variables to their types, type substitution
information, etc.
-/
class TypeContext (P : PureExpr) (Context TypeEnv TypeError : Type) where
  isBoolType   : P.Ty → Bool
  freeVars     : P.Expr → List P.Ident
  preprocess   : Context → TypeEnv → P.Ty → Except TypeError (P.Ty × TypeEnv)
  postprocess  : Context → TypeEnv → P.Ty → Except TypeError (P.Ty × TypeEnv)
  update       : TypeEnv → P.Ident → P.Ty → TypeEnv
  lookup       : TypeEnv → P.Ident → Option P.Ty
  inferType    : Context → TypeEnv → Cmd P → P.Expr → Except TypeError (P.Expr × P.Ty × TypeEnv)
  unifyTypes   : TypeEnv → List (P.Ty × P.Ty) → Except TypeError TypeEnv
  typeErrorFmt : TypeError → Std.Format

---------------------------------------------------------------------
end Imperative

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt

/-! # Properties of Imperative commands

Definitional equations for the generic command interfaces implemented by
`Cmd` and `CmdExt`, plus exact defined- and modified-variable equations for
base-command initialization and havoc.

Key results:
- `Cmd.hasInit_eq` / `Cmd.hasHavoc_eq` and their `CmdExt` counterparts expose
  the concrete constructors behind the generic interfaces.
- `init_cmd_definedVars` / `init_true_definedVars` characterize initialization
  targets.
- `init_modVars` / `havoc_modVars` characterize modified variables.
-/

namespace Imperative

public section

/-- Base-command initialization through `HasInit` is `Cmd.init`. -/
@[simp] theorem Cmd.hasInit_eq {P : PureExpr}
    (ident : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    (HasInit.init (P := P) (CmdT := Cmd P) ident ty value md) =
      Cmd.init ident ty value md :=
  rfl

/-- Base-command havoc through `HasHavoc` is a nondeterministic `Cmd.set`. -/
@[simp] theorem Cmd.hasHavoc_eq {P : PureExpr}
    (ident : P.Ident) (md : MetaData P) :
    (HasHavoc.havoc (P := P) (CmdT := Cmd P) ident md) =
      Cmd.set ident .nondet md :=
  rfl

/-- Extended-command initialization wraps the base initialization. -/
@[simp] theorem CmdExt.hasInit_eq {P : PureExpr}
    (ident : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    (HasInit.init (P := P) (CmdT := CmdExt P) ident ty value md) =
      CmdExt.cmd (Cmd.init ident ty value md) :=
  rfl

/-- Extended-command havoc wraps a nondeterministic base `Cmd.set`. -/
@[simp] theorem CmdExt.hasHavoc_eq {P : PureExpr}
    (ident : P.Ident) (md : MetaData P) :
    (HasHavoc.havoc (P := P) (CmdT := CmdExt P) ident md) =
      CmdExt.cmd (Cmd.set ident .nondet md) :=
  rfl

/-- An initialization command defines exactly its target register. -/
theorem init_cmd_definedVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P)
    (md : MetaData P) (excludeScoped : Bool) :
    HasVarsImp.definedVars (P := P)
      (HasInit.init (P := P) (CmdT := Cmd P) x ty value md)
      excludeScoped = [x] := by
  with_unfolding_all rfl

/-- An initialization statement defines exactly its target register when
scoped definitions are included. -/
theorem init_true_definedVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    Stmt.definedVars
      (.cmd (HasInit.init (P := P) (CmdT := Cmd P) x ty value md))
      true = [x] := by
  with_unfolding_all rfl

/-- An `init` command defines its target but does not modify an existing slot. -/
theorem init_modVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (ty : P.Ty) (value : ExprOrNondet P) (md : MetaData P) :
    HasVarsImp.modifiedVars
      (HasInit.init (P := P) (CmdT := Cmd P) x ty value md) =
        ([] : List P.Ident) := by
  with_unfolding_all rfl

/-- A `havoc` command modifies exactly its target register. -/
theorem havoc_modVars {P : PureExpr} [HasFvars P]
    (x : P.Ident) (md : MetaData P) :
    HasVarsImp.modifiedVars
      (HasHavoc.havoc (P := P) (CmdT := Cmd P) x md) = [x] := by
  with_unfolding_all rfl

end -- public section

end Imperative

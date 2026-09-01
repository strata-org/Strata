/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Checked.Builder
import all Strata.Languages.Laurel.Checked.Builder

/-!
# Checked Laurel: raw builders

The low-level, type-correctness-**bypassing** builders. Each fabricates a typed handle
(`Expr`/`Ref`) from a raw `StmtExpr`/name/args with *no* guarantee that it matches the
phantom `Ty` — that is the caller's responsibility. They reach `Builder`'s private handle
constructors via `import all`.

The `raw*` prefix marks them as the escape hatch; prefer the checked combinators. Safety
rests on `Builder`'s private constructors, which stop other modules from fabricating an
ill-typed handle.
-/

open Strata Strata.Laurel

public section
namespace Strata.Laurel.Checked

namespace Ref

/-- A `Ref` for a local/parameter by name, tagged with the caller-chosen type `α`. -/
def rawLocalVar (α : Ty) (name : String) : Ref α :=
  ⟨.Local (mkId name)⟩

end Ref

/-- Emit an assignment of `value`. Multiple `targets` are a parallel assignment. -/
def rawAssign {m α} [Builder m] (targets : List (AstNode Variable)) (value : Expr α)
     (source : FileRange := .unknown) : m Unit :=
  emitStmt (.Assign targets value.node) source

namespace Expr

/-- Build an `Expr α` from a raw `StmtExpr`; the phantom `α` is unchecked. -/
def rawOfStmt {α : Ty} (val : StmtExpr) (source : FileRange := .unknown) : Expr α :=
  ⟨{ val := val, source := source }⟩

/-- A static call `f(args…)`, tagged with the caller-chosen result type `α`. -/
def rawCall {α : Ty} (f : String) (args : List (AstNode StmtExpr)) (source : FileRange := .unknown) : Expr α :=
  rawOfStmt (.StaticCall (mkId f) args) source

/-- Reference a local/parameter by name as an `Expr`, tagged with the caller-chosen `α`. -/
def rawLocalRef {α : Ty} (name : String) (source : FileRange := .unknown) : Expr α :=
  rawOfStmt (.Var (.Local (mkId name))) source

/-- Read field `field` off a composite reference (a pure `Expr`). -/
def rawGetField {ref : Ty} (recv : Expr ref) (field : String) (value : Ty) (source : FileRange := .unknown) : Expr value :=
  rawOfStmt (.Var (.Field recv.node (mkId field))) source

/-- The assignment statement writing `val` to `field` of a composite reference. The body
    monad `emit`s this to perform a (real, aliased) field mutation. -/
def rawSetField {m} {ref value : Ty} [Builder m] (recv : Expr ref) (field : String) (val : Expr value)
     (source : FileRange := .unknown) : m Unit :=
  rawAssign [{ val := Variable.Field recv.node (mkId field), source := source }] val source

end Expr

end Strata.Laurel.Checked
end -- public section

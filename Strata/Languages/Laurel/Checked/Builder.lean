/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST

/-!
# Checked Laurel: primitive types

Introduces typed representation of Laurel expressions along with a Builder class to
simplify constructing well-typed Laurel programs.

The fundamental types are:
* `Ty` a Laurel type without metadata used for representing the type, and
* typed handles `Expr α` and `Ref α` for working with typed expressions
  and references.

This also introduces a `Builder` typeclass that can accumulate Laurel expressions
and provide access to a fresh name generator.  Additional macros for working with
Builder are in the `Macros` module and a default implementation is in `BuilderM`.
-/

open Strata Strata.Laurel

public section
namespace Strata.Laurel.Checked

/-- Wrap a value in an `AstNode` with no source location default. -/
private def nd {t : Type} (v : t) (source : FileRange := .unknown) : AstNode t :=
  { val := v, source := source }

/-! ## Laurel types

A `Ty` names the Laurel `HighType` a handle lowers to. `Expr`/`Ref` are indexed by a
`Ty` value. -/

/--
Wraps a Laurel `HighType` for the typed representation with no-metadata
through the constructors so that equality does not have metadata
to distinguish types that have the same structure.

The constructor is private; use the smart constructors below for
the builtin types.
-/
structure Ty where
  private mk ::
  /-- The Laurel type this lowers to. -/
  highType : HighType
  deriving Repr

namespace Ty

def int : Ty := ⟨.TInt⟩

def bool : Ty := ⟨.TBool⟩

/-- The unit type (a `-> None`/`void` result). -/
def none : Ty := ⟨.TVoid⟩


def string : Ty := ⟨.TString⟩

def bv (w : Nat) := Ty.mk <| .TBv w

def real : Ty := ⟨.TReal⟩

def totalMap (key value : Ty) : Ty := ⟨.TMap (nd key.highType) (nd value.highType)⟩

def set (elt : Ty) : Ty := ⟨.TSet (nd elt.highType)⟩

/-- A named type `name<args…>` (a bare `name` when `args` is empty). -/
def named (name : String) (args : List Ty := []) : Ty :=
  if args.isEmpty then
    ⟨.UserDefined (mkId name)⟩
  else
    ⟨.Applied (nd (.UserDefined (mkId name))) (args.map fun a => nd a.highType)⟩

end Ty

/--
A Laurel expression, tagged with its type `α`. The constructor is private; build one via
the literal combinators, the generated checked combinators, or the raw builders in
`Strata.Languages.Laurel.Checked.Raw`.
-/
structure Expr (α : Ty) where
  private mk ::
  /-- The underlying located Laurel statement/expression node. -/
  node : AstNode StmtExpr

namespace Expr

def boolLit (b : Bool) (source : FileRange := .unknown) : Expr Ty.bool :=
  ⟨{ val := .LiteralBool b, source := source }⟩

def strLit (s : String) (source : FileRange := .unknown) : Expr .string :=
  ⟨{ val := .LiteralString s, source := source }⟩

def intLit (i : Int) (source : FileRange := .unknown) : Expr .int :=
  ⟨{ val := .LiteralInt i, source := source }⟩

end Expr

/--
A reference to an assignable location (a local, parameter, or field), tagged with `α`.

The constructor is private, and it should be constructed using checked combinators
(or raw builders in `Strata.Languages.Laurel.Checked.Raw`).
-/
structure Ref (α : Ty) where
  private mk ::
  /-- The underlying Laurel variable. -/
  toVariable : Variable

/-- `TotalMap key value` — the built-in Laurel total-map type (Core's map sort). Unlike
    `Set`, which the prelude declares `opaque` (so `derive_laurel_ops` generates its `Ty`
    def), `TotalMap` is only ever an *implicit* built-in (`.TMap`) with no declaration to
    generate from, so its name is provided here for callers. -/
abbrev TotalMap (key value : Ty) : Ty := Ty.totalMap key value

/-! ## Builder typeclass  -/

class Builder (m : Type → Type) extends Monad m where
  /-- Append a statement to the body being built. -/
  emit (s : AstNode StmtExpr) : m Unit

  /-- Allocate a fresh local name with the given hint (e.g. `contents$3`). -/
  freshName (hint : String) : m Identifier

  /-- Run `body`  and return the statements it emits as a `Block`. -/
  captureBlock (body : m Unit) : m (AstNode StmtExpr)

export Builder (emit freshName captureBlock)

def emitStmt {m} [Builder m] (s : StmtExpr) (source : FileRange := .unknown) : m Unit :=
  emit { val := s, source := source }

/-! ## Statement combinators -/

/-- Declare a fresh local initialized to `value`, returning a handle to it. -/
def letLocal {m} [Builder m] {α : Ty} (hint : String) (value : Expr α) : m (Expr α) := do
  let n ← freshName hint
  let decl : Variable := .Declare { name := n, type := some (nd α.highType) }
  emitStmt <| .Assign [nd decl] value.node
  pure <| ⟨nd (.Var (.Local n))⟩

end Strata.Laurel.Checked
end -- public section

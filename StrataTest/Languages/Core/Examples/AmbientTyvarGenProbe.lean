/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

meta import Strata.Languages.Core.StatementType

/-! Abstract-syntax probe: does a nested `funcDecl` generalize over a type
    variable that becomes free in the AMBIENT context via a polymorphic
    var-instantiation? -/

meta section

namespace Core.AmbientTyvarGenProbe

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/-- `var x : forall a. a := *` — a polymorphic var-init. `preprocess` instantiates
    `forall a. a` to a FRESH generated tyvar (e.g. `$__ty0`), storing
    `x : forall [] $__ty0` in the ambient context. That `$__ty0` is NOT rigid
    (no enclosing procedure type params). Then a nested function captures `x`. -/
def probeStmts : List Statement :=
  let f : PureFunc Expression := {
    name := ⟨"f", ()⟩,
    typeArgs := ["b"],
    isConstr := false,
    inputs := [],
    output := .forAll [] (.ftvar "b"),   -- nested fn claims output type `b`
    body := some eb[x],                  -- ...but body is the ambient `x`
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [ .init "x" t[∀α. %α] .nondet .empty,
    .funcDecl f .empty ]

#eval do
  let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none probeStmts
  return format ans.fst

/-- Simpler probe: nested fn output is exactly the ambient var's (fresh) type.
    Monomorphic; should this be accepted? It returns x at x's own type. -/
def probeStmts2 : List Statement :=
  let g : PureFunc Expression := {
    name := ⟨"g", ()⟩,
    typeArgs := ["b"],
    isConstr := false,
    inputs := [(⟨"z", ()⟩, .forAll [] (.ftvar "b"))],
    output := .forAll [] (.ftvar "b"),
    body := some eb[x],                  -- body ignores z, returns ambient x
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [ .init "x" t[∀α. %α] .nondet .empty,
    .funcDecl g .empty ]

#eval do
  let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none probeStmts2
  return format ans.fst

/-- Extract the recorded type of the nested `f<b>():b { x }` by running the
    statement-level typechecker's aux and reading back the factory function. -/
#eval do
  let (_, _, C') ← Statement.typeCheckAux LContext.default TEnv.default Program.init none probeStmts
  match C'.functions.toArray.find? (fun (fn : LFunc CoreLParams) => fn.name.name == "f") with
  | some fn => return format f!"f recorded as: typeArgs={fn.typeArgs}, inputs={fn.inputs}, output={fn.output}, body={fn.body}"
  | none => return format "f not found"

/-- EXPLOIT: after declaring `f<b>() : b { x }` (body = ambient `x : $__ty0`),
    call `f` at BOTH int and bool in the same scope. If both initializers
    type-check, `f` (which returns the single fixed value `x`) has been used at
    two incompatible types — a concrete unsoundness witness. -/
def exploitStmts : List Statement :=
  let f : PureFunc Expression := {
    name := ⟨"f", ()⟩,
    typeArgs := ["b"],
    isConstr := false,
    inputs := [],
    output := .forAll [] (.ftvar "b"),
    body := some eb[x],
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [ .init "x" t[∀α. %α] .nondet .empty,
    .funcDecl f .empty,
    .init "i" t[int] (.det eb[(~f)]) .empty,    -- f() used at int
    .init "bo" t[bool] (.det eb[(~f)]) .empty,  -- f() used at bool
    .assert "i_is_int" eb[i == #5] .empty ]

#eval do
  let ans ← Statement.typeCheck LContext.default TEnv.default Program.init none exploitStmts
  return format ans.fst

end Core.AmbientTyvarGenProbe

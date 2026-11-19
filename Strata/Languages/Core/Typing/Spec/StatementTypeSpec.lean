/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.CommandTypeSpec

/-! ## The Typechecker Spec for Statements

This file gives the typechecker spec for statements and statement lists. It threads the ambient
`LContext`, the variable scope, the written type variables in scope, and the labels of the
enclosing blocks.

### Scoping (lexical)

A block (and each `ite`/`loop` branch) is lexically scoped: bindings and
`typeDecl`s made inside it are block-local and its output context is its input
`C, Γ`. Only top-level `typeDecl` statements extend `C` for subsequent
statements.

### Labels

At the top level `L = []`, so every `exit` must be caught by a lexically
enclosing block.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-! ### Written type variables
A written type variable denotes one type from the first declaration that uses it to the end of
its enclosing block, conditional branch or loop body. -/

mutual

/-- The typechecker spec for statements, threading the environment `Δ` of written type
    variables. -/
inductive StatementHasType (P : Program) :
    LContext CoreLParams → TContext Unit → WrittenEnv → List String → Statement →
    LContext CoreLParams → TContext Unit → WrittenEnv → Prop where
  /-- An atomic (extended) command, typed by `CmdExtHasType`; `C` is unchanged. -/
  | cmd : ∀ C Γ Γc Δ Δ' L c Γ',
      CmdExtHasType C P Δ Γ c Γc Δ' →
      TContext.Equiv (T := CoreLParams) Γ' Γc →
      StatementHasType P C Γ Δ L (.cmd c) C Γ' Δ'
  /-- A labeled block whose label does not shadow an enclosing one; lexically scoped. -/
  | block : ∀ C Γ Δ C_body Γ_body Δ_body L label body md Γ',
      label ∉ L →
      StatementsHasType P C Γ Δ (label :: L) body C_body Γ_body Δ_body →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L (.block label body md) C Γ' Δ
  /-- Deterministic if-then-else: a `bool` condition and branches typed independently. -/
  | ite_det : ∀ (C : LContext CoreLParams) Γ Δ C_t Γ_t Δ_t C_e Γ_e Δ_e L cond thenb
      elseb md Γ',
      HasType C Γ (instAnnots Δ cond) (.forAll [] .bool) →
      WrittenAnnotsOk C Γ cond →
      AnnotsInScope C.rigidTypeVars Δ cond →
      StatementsHasType P C Γ Δ L thenb C_t Γ_t Δ_t →
      StatementsHasType P C Γ Δ L elseb C_e Γ_e Δ_e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L (.ite (.det cond) thenb elseb md) C Γ' Δ
  /-- Non-deterministic if-then-else: as `ite_det` but with no condition. -/
  | ite_nondet : ∀ C Γ Δ C_t Γ_t Δ_t C_e Γ_e Δ_e L thenb elseb md Γ',
      StatementsHasType P C Γ Δ L thenb C_t Γ_t Δ_t →
      StatementsHasType P C Γ Δ L elseb C_e Γ_e Δ_e →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L (.ite .nondet thenb elseb md) C Γ' Δ
  /-- Loop: a `bool` guard, an `int` measure and `bool` invariants. -/
  | loop : ∀ (C : LContext CoreLParams) Γ Δ C_body Γ_body Δ_body L guard measure invariants
      body md Γ',
      (∀ g, guard = .det g → HasType C Γ (instAnnots Δ g) (.forAll [] .bool)) →
      (∀ g, guard = .det g → WrittenAnnotsOk C Γ g) →
      (∀ m, measure = some m → HasType C Γ (instAnnots Δ m) (.forAll [] .int)) →
      (∀ m, measure = some m → WrittenAnnotsOk C Γ m) →
      (∀ p, p ∈ invariants → HasType C Γ (instAnnots Δ p.2) (.forAll [] .bool)) →
      (∀ p, p ∈ invariants → WrittenAnnotsOk C Γ p.2) →
      (∀ g, guard = .det g → AnnotsInScope C.rigidTypeVars Δ g) →
      (∀ m, measure = some m → AnnotsInScope C.rigidTypeVars Δ m) →
      (∀ p, p ∈ invariants → AnnotsInScope C.rigidTypeVars Δ p.2) →
      StatementsHasType P C Γ Δ L body C_body Γ_body Δ_body →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L
        (.loop guard measure invariants body md) C Γ' Δ
  /-- Exit statement: its target must name an enclosing block (`label ∈ L`). -/
  | exit : ∀ C Γ Δ L label md Γ',
      label ∈ L →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L (.exit label md) C Γ' Δ
  /-- Local type declaration whose name clashes with no program name or alias. -/
  | typeDecl : ∀ C C' Γ Δ L tc md Γ',
      (∀ n ∈ P.getNames, n.name ≠ tc.name) →
      (∀ al ∈ Γ.aliases, al.name ≠ tc.name) →
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementHasType P C Γ Δ L (.typeDecl tc md) C' Γ' Δ

/-- The typechecker spec for statement lists, threading `C`, `Γ`, and the environment `Δ` of
    written type variables. -/
inductive StatementsHasType (P : Program) :
    LContext CoreLParams → TContext Unit → WrittenEnv → List String → List Statement →
    LContext CoreLParams → TContext Unit → WrittenEnv → Prop where
  /-- The empty statement list leaves the context unchanged. -/
  | nil : ∀ C Γ Δ L Γ',
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      StatementsHasType P C Γ Δ L [] C Γ' Δ
  /-- The first statement is typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' Δ Δ' Δ'' L s ss,
      StatementHasType P C Γ Δ L s C' Γ' Δ' →
      StatementsHasType P C' Γ' Δ' L ss C'' Γ'' Δ'' →
      StatementsHasType P C Γ Δ L (s :: ss) C'' Γ'' Δ''

end

end -- public section

end TypeSpec
end Core

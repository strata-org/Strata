/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CommandTypeSpec
public import Strata.Languages.Core.FunctionTypeSpec

/-! ## Declarative Typing Specification for Statements

This file specifies when a `Statement` (= `Imperative.Stmt Core.Expression
Core.Command`) and a list of statements are well-typed. It is the statement-level
analogue of `CmdTypeSpec` / `CommandTypeSpec`.

The specification is parameterized via `ExprTypingSpec` (so it instantiates to
both the polymorphic `HasType` and the annotated `HasTypeA`), exactly like
`CmdHasType'` / `CmdExtHasType'`, which it reuses for the `cmd` constructor.

Unlike commands, statement typing threads the ambient `LContext` `C`
(built-in/declared functions and known types), the `TContext` `Γ` (variable
type-scope), and the set `L` of labels of enclosing blocks (so `exit` targets an
enclosing block). The relations are 6-place: `C Γ L stmt C' Γ'`.

### Scoping (lexical)

A block (and each `ite`/`loop` branch) is lexically scoped: bindings and
`typeDecl`/`funcDecl`s made inside it are block-local and its output context is
its input `C, Γ`. Only top-level `funcDecl`/`typeDecl` statements extend `C` for
subsequent statements.

### Labels

At the top level `L = []`, so every `exit` must be caught by a lexically
enclosing block.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

mutual

/--
Declarative typing for statements, parameterized over `ExprTypingSpec`.

The relation `StatementHasType' τ P C Γ L s C' Γ'` reads: "under program `P`,
in ambient context `C`, type-scope `Γ`, and enclosing-block label set `L`,
statement `s` is well-typed and yields output context `C'` and type-scope `Γ'`."
`L` collects the labels of the blocks lexically enclosing `s`, so an `exit`
targets only an enclosing block.
-/
inductive StatementHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List String → Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- An atomic (extended) command. Delegates to `CmdExtHasType'`; `C` is
      unchanged (commands do not declare functions or types). Output `Δ` up to
      `TContext.Equiv` (see `CmdHasType'`). -/
  | cmd : ∀ C Γ Γ' L c Δ,
      CmdExtHasType' (τ := τ) C P Γ c Γ' →
      TContext.Equiv (T := CoreLParams) Δ Γ' →
      StatementHasType' τ P C Γ L (.cmd c) C Δ

  /-- A labeled block. Its label must not shadow an enclosing one (`label ∉ L`);
      the body is typed with `label` added to the label set. The body's output
      context is existentially discarded (the block is lexically scoped). The
      block's output `Δ` matches its input `Γ` up to `TContext.Equiv`. -/
  | block : ∀ C Γ C_body Γ_body L label body md Δ,
      label ∉ L →
      StatementsHasType' τ P C Γ (label :: L) body C_body Γ_body →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.block label body md) C Δ

  /-- Deterministic if-then-else: the condition must be `bool`; each branch is
      typed independently (no cross-branch leakage). The output `Δ` matches the
      input `Γ` up to `TContext.Equiv`. -/
  | ite_det : ∀ C Γ C_t Γ_t C_e Γ_e L cond thenb elseb md Δ,
      S.exprTyped C Γ cond (S.embed .bool) →
      StatementsHasType' τ P C Γ L thenb C_t Γ_t →
      StatementsHasType' τ P C Γ L elseb C_e Γ_e →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.ite (.det cond) thenb elseb md) C Δ

  /-- Non-deterministic if-then-else: as `ite_det` but with no condition. -/
  | ite_nondet : ∀ C Γ C_t Γ_t C_e Γ_e L thenb elseb md Δ,
      StatementsHasType' τ P C Γ L thenb C_t Γ_t →
      StatementsHasType' τ P C Γ L elseb C_e Γ_e →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.ite .nondet thenb elseb md) C Δ

  /-- Loop. The guard (if deterministic) must be `bool`; the measure (if
      present) must be `int`; each invariant must be `bool`. The output `Δ`
      matches the input `Γ` up to `TContext.Equiv`. -/
  | loop : ∀ C Γ C_body Γ_body L guard measure invariants body md Δ,
      (∀ g, guard = .det g → S.exprTyped C Γ g (S.embed .bool)) →
      (∀ m, measure = some m → S.exprTyped C Γ m (S.embed .int)) →
      (∀ p, p ∈ invariants → S.exprTyped C Γ p.2 (S.embed .bool)) →
      StatementsHasType' τ P C Γ L body C_body Γ_body →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.loop guard measure invariants body md) C Δ

  /-- Exit statement: its target must name an enclosing block (`label ∈ L`). -/
  | exit : ∀ C Γ L label md Δ,
      label ∈ L →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.exit label md) C Δ

  /-- Local function declaration. The declaration must be non-recursive, and
      every declared type must be a monotype. The resulting function is added to
      `C` for subsequent statements. -/
  | funcDecl : ∀ C Γ L decl func md Δ,
      ¬ decl.isRecursive →
      Function.ofPureFunc decl = .ok func →
      FuncHasType' τ C Γ func →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.funcDecl decl md) (C.addFactoryFunction func.toLFunc) Δ

  /-- Local type declaration. The new type is added to `C` and must not clash
      with an existing known type. -/
  | typeDecl : ∀ C C' Γ L tc md Δ,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementHasType' τ P C Γ L (.typeDecl tc md) C' Δ

/--
Declarative typing for a list of statements, threading `C`, `Γ`, and the ambient
label set `L` (`L` is fixed across the list).
-/
inductive StatementsHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List String → List Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- The empty statement list leaves the context unchanged, up to
      `TContext.Equiv` (see `CmdHasType'`). -/
  | nil : ∀ C Γ L Δ,
      TContext.Equiv (T := CoreLParams) Δ Γ →
      StatementsHasType' τ P C Γ L [] C Δ

  /-- The first statement is typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' L s ss,
      StatementHasType' τ P C Γ L s C' Γ' →
      StatementsHasType' τ P C' Γ' L ss C'' Γ'' →
      StatementsHasType' τ P C Γ L (s :: ss) C'' Γ''

end

/-- `StatementHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev StatementHasType (P : Program) :=
  @StatementHasType' LTy P instHasType

/-- `StatementsHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev StatementsHasType (P : Program) :=
  @StatementsHasType' LTy P instHasType

/-- `StatementHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev StatementHasTypeA (P : Program) :=
  @StatementHasType' LMonoTy P instHasTypeA

/-- `StatementsHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev StatementsHasTypeA (P : Program) :=
  @StatementsHasType' LMonoTy P instHasTypeA

end -- public section

end TypeSpec
end Core

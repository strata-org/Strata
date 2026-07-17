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

Unlike commands, statement typechecking (`Core.Statement.typeCheckAux`) threads
the ambient `LContext` `C` (built-in/declared functions and known types), the
`TContext` `Γ` (variable type-scope), and the set `L` of labels of enclosing
blocks (so `exit` targets an enclosing block). The relations are 6-place:
`C Γ L stmt C' Γ'`.

### Scoping (lexical, post-#1392)

`goBlock` runs the block body under `pushEmptyContext` and restores via
`popContext`, AND discards the body's output `LContext`, returning the input
`C`. Consequently:

* A `block` (and each `ite`/`loop` branch, which route through `goBlock`) is
  typed under the *input* `C, Γ`, and its output context is the *input* `C, Γ` —
  variable bindings and `typeDecl`/`funcDecl` declarations made inside are
  block-local and do not escape.
* Only top-level `funcDecl`/`typeDecl` statements (in `go`, not under a block)
  extend `C` for subsequent statements.

The running unification substitution does persist across blocks/branches, but it
is invisible at the `(C, Γ)` level: the soundness theorems relate *substituted*
contexts, so the persisted refinement is absorbed there.

### Function dependency

The `funcDecl` constructor's premise is `FuncHasType'`, the declarative function
typing specification, evaluated in the ambient context `C, Γ` the declaration is
checked in.

### Labels

`block label` types its body under `label :: L` and requires `label ∉ L` (no
shadowing); `exit label` requires `label ∈ L`. At the top level `L = []`, so every
`exit` must be caught by a lexically enclosing block.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

mutual

/--
Declarative typing for statements, parameterized over `ExprTypingSpec`.

The relation `StmtHasType' τ P C Γ L s C' Γ'` reads: "under program `P`,
in ambient context `C`, type-scope `Γ`, and enclosing-block label set `L`,
statement `s` is well-typed and yields output context `C'` and type-scope `Γ'`."
`L` collects the labels of the blocks lexically enclosing `s`, so an `exit`
targets only an enclosing block (cf. the `labels` parameter of `typeCheckAux.go`).
-/
inductive StmtHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List String → Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- An atomic (extended) command. Delegates to `CmdExtHasType'`; `C` is
      unchanged (commands do not declare functions or types). -/
  | cmd : ∀ C Γ Γ' L c,
      CmdExtHasType' (τ := τ) C P Γ c Γ' →
      StmtHasType' τ P C Γ L (.cmd c) C Γ'

  /-- A labeled block. Its label must not shadow an enclosing one (`label ∉ L`);
      the body is typed under the input `C, Γ` with `label` added to the label
      set. The body's output context is existentially discarded (the block is
      lexically scoped), so the block's own output context is the input `C, Γ`. -/
  | block : ∀ C Γ C_body Γ_body L label body md,
      label ∉ L →
      StmtsHasType' τ P C Γ (label :: L) body C_body Γ_body →
      StmtHasType' τ P C Γ L (.block label body md) C Γ

  /-- Deterministic if-then-else: the condition must be `bool`; each branch is
      typed independently from the input `C, Γ` (no cross-branch leakage) under
      the same label set `L`. The output context is the input `C, Γ`. -/
  | ite_det : ∀ C Γ C_t Γ_t C_e Γ_e L cond thenb elseb md,
      S.exprTyped C Γ cond (S.embed .bool) →
      StmtsHasType' τ P C Γ L thenb C_t Γ_t →
      StmtsHasType' τ P C Γ L elseb C_e Γ_e →
      StmtHasType' τ P C Γ L (.ite (.det cond) thenb elseb md) C Γ

  /-- Non-deterministic if-then-else: as `ite_det` but with no condition. -/
  | ite_nondet : ∀ C Γ C_t Γ_t C_e Γ_e L thenb elseb md,
      StmtsHasType' τ P C Γ L thenb C_t Γ_t →
      StmtsHasType' τ P C Γ L elseb C_e Γ_e →
      StmtHasType' τ P C Γ L (.ite .nondet thenb elseb md) C Γ

  /-- Loop. The guard (if deterministic) must be `bool`; the measure (if
      present) must be `int`; each invariant must be `bool`; the body is typed
      from the input `C, Γ` under the same label set `L`. Output context is the
      input `C, Γ`. -/
  | loop : ∀ C Γ C_body Γ_body L guard measure invariants body md,
      (∀ g, guard = .det g → S.exprTyped C Γ g (S.embed .bool)) →
      (∀ m, measure = some m → S.exprTyped C Γ m (S.embed .int)) →
      (∀ p, p ∈ invariants → S.exprTyped C Γ p.2 (S.embed .bool)) →
      StmtsHasType' τ P C Γ L body C_body Γ_body →
      StmtHasType' τ P C Γ L (.loop guard measure invariants body md) C Γ

  /-- Exit statement: its target must name an enclosing block (`label ∈ L`).
      Context unchanged. -/
  | exit : ∀ C Γ L label md,
      label ∈ L →
      StmtHasType' τ P C Γ L (.exit label md) C Γ

  /-- Local function declaration. The function is non-recursive and well-typed
      (per `FuncHasType'`, evaluated in the ambient `C, Γ`); the resulting `func`
      is added to `C` for subsequent statements. -/
  | funcDecl : ∀ C Γ L decl func md,
      ¬ decl.isRecursive →
      FuncHasType' τ C Γ func →
      StmtHasType' τ P C Γ L (.funcDecl decl md) (C.addFactoryFunction func) Γ

  /-- Local type declaration. The new type is added to `C` (must not clash with
      an existing known type, per `addKnownTypeWithError`). -/
  | typeDecl : ∀ C C' Γ L tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      StmtHasType' τ P C Γ L (.typeDecl tc md) C' Γ

/--
Declarative typing for a list of statements, threading `C`, `Γ`, and the ambient
label set `L`. Mirrors the `go` loop in `typeCheckAux` (`L` is fixed across the list).
-/
inductive StmtsHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List String → List Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- The empty statement list leaves the context unchanged. -/
  | nil : ∀ C Γ L,
      StmtsHasType' τ P C Γ L [] C Γ

  /-- The first statement is typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' L s ss,
      StmtHasType' τ P C Γ L s C' Γ' →
      StmtsHasType' τ P C' Γ' L ss C'' Γ'' →
      StmtsHasType' τ P C Γ L (s :: ss) C'' Γ''

end

/-- `StmtHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev StmtHasType (P : Program) :=
  @StmtHasType' LTy P instHasType

/-- `StmtsHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev StmtsHasType (P : Program) :=
  @StmtsHasType' LTy P instHasType

/-- `StmtHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev StmtHasTypeA (P : Program) :=
  @StmtHasType' LMonoTy P instHasTypeA

/-- `StmtsHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev StmtsHasTypeA (P : Program) :=
  @StmtsHasType' LMonoTy P instHasTypeA

end -- public section

end TypeSpec
end Core

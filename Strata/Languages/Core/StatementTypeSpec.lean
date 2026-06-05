/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CmdTypeSpec
public import Strata.Languages.Core.FunctionTypeSpec
public import Strata.Languages.Core.Program

/-! ## Declarative Typing Specification for Statements

Specifies when statements and blocks are well-typed, parameterized over the
`ExprTypingSpec` typeclass (see `CmdTypeSpec.lean`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for extended commands (imperative commands + procedure calls).
-/
inductive CmdExtHasType' (τ : Type) (C : LContext CoreLParams) (P : Program)
    [S : ExprTypingSpec τ] :
    TContext Unit → Command → TContext Unit → Prop where

  /-- A standard imperative command. -/
  | cmd : ∀ Γ Γ' c,
      @CmdHasType' τ C S Γ c Γ' →
      CmdExtHasType' τ C P Γ (.cmd c) Γ'

  /-- A procedure call.
      There exists a type instantiation σ such that input expressions and
      output variables have types matching the instantiated signature. -/
  | call : ∀ Γ (pname : String) callArgs proc md
      (σ : List (TyIdentifier × LMonoTy)),
      Program.Procedure.find? P pname = some proc →
      (CallArg.getInputExprs callArgs).length = proc.header.inputs.length →
      (CallArg.getLhs callArgs).length = proc.header.outputs.length →
      -- All lhs variables exist in context
      (∀ v, v ∈ CallArg.getLhs callArgs → (Γ.types.find? v).isSome) →
      -- Input expressions have the instantiated formal types
      (∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
           (hj : i < proc.header.inputs.values.length),
        S.exprTyped C Γ ((CallArg.getInputExprs callArgs)[i])
          (S.embed (LMonoTy.subst [σ] (proc.header.inputs.values[i])))) →
      -- LHS variable types match instantiated output types
      (∀ i (hi : i < (CallArg.getLhs callArgs).length)
           (hj : i < proc.header.outputs.values.length),
        Γ.types.find? ((CallArg.getLhs callArgs)[i]) =
          some (.forAll [] (LMonoTy.subst [σ] (proc.header.outputs.values[i])))) →
      -- In-out arguments are simple variables with matching names
      (∀ i (hi : i < proc.header.inputs.keys.length),
        (ListMap.keys proc.header.outputs).contains (proc.header.inputs.keys[i]) →
        ∃ m id, (CallArg.getInputExprs callArgs)[i]? = some (.fvar m id none) ∧
                id = (proc.header.inputs.keys[i])) →
      CmdExtHasType' τ C P Γ (.call pname callArgs md) Γ

/-- `CmdExtHasType` instantiated with `HasType`. -/
abbrev CmdExtHasType (C : LContext CoreLParams) (P : Program) :=
  @CmdExtHasType' LTy C P instHasType

/-- `CmdExtHasType` instantiated with `HasTypeA`. -/
abbrev CmdExtHasTypeA (C : LContext CoreLParams) (P : Program) :=
  @CmdExtHasType' LMonoTy C P instHasTypeA


mutual

/--
Declarative typing for statements, parameterized over `ExprTypingSpec`.
-/
inductive StmtHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- An atomic command. -/
  | cmd : ∀ C Γ Γ' c,
      CmdExtHasType' τ C P Γ c Γ' →
      StmtHasType' τ P C Γ (.cmd c) C Γ'

  /-- A labeled block. -/
  | block : ∀ C C' Γ Γ' label stmts md,
      StmtsHasType' τ P C Γ stmts C' Γ' →
      StmtHasType' τ P C Γ (.block label stmts md) C' Γ'

  /-- Deterministic if-then-else: condition must be bool, both branches
      typed from the same input Γ. -/
  | ite_det : ∀ C C_t C_e Γ Γ_t Γ_e cond thenb elseb md,
      S.exprTyped C Γ cond (S.embed .bool) →
      StmtsHasType' τ P C Γ thenb C_t Γ_t →
      StmtsHasType' τ P C Γ elseb C_e Γ_e →
      StmtHasType' τ P C Γ (.ite (.det cond) thenb elseb md) C_t Γ_t

  /-- Non-deterministic if-then-else. -/
  | ite_nondet : ∀ C C_t C_e Γ Γ_t Γ_e thenb elseb md,
      StmtsHasType' τ P C Γ thenb C_t Γ_t →
      StmtsHasType' τ P C Γ elseb C_e Γ_e →
      StmtHasType' τ P C Γ (.ite .nondet thenb elseb md) C_t Γ_t

  /-- Loop: guard must be bool (if deterministic), measure must be int
      (if present), invariants must be bool, body typed from Γ. -/
  | loop : ∀ C C_body Γ Γ_body guard measure invariants body md,
      (∀ g, guard = .det g → S.exprTyped C Γ g (S.embed .bool)) →
      (∀ m, measure = some m → S.exprTyped C Γ m (S.embed .int)) →
      (∀ p, p ∈ invariants → S.exprTyped C Γ p.2 (S.embed .bool)) →
      StmtsHasType' τ P C Γ body C_body Γ_body →
      StmtHasType' τ P C Γ (.loop guard measure invariants body md) C Γ

  /-- Exit statement. -/
  | exit : ∀ C Γ label md,
      StmtHasType' τ P C Γ (.exit label md) C Γ

  /-- Local function declaration. -/
  | funcDecl : ∀ C Γ decl func md,
      ¬ decl.isRecursive →
      FuncHasType' τ C func →
      StmtHasType' τ P C Γ (.funcDecl decl md) (C.addFactoryFunction func) Γ

  /-- Local type declaration. -/
  | typeDecl : ∀ C C' Γ tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs }
        default = .ok C' →
      StmtHasType' τ P C Γ (.typeDecl tc md) C' Γ

inductive StmtsHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List Statement →
    LContext CoreLParams → TContext Unit → Prop where

  /-- Empty statement list. -/
  | nil : ∀ C Γ,
      StmtsHasType' τ P C Γ [] C Γ

  /-- Cons: first statement typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' s ss,
      StmtHasType' τ P C Γ s C' Γ' →
      StmtsHasType' τ P C' Γ' ss C'' Γ'' →
      StmtsHasType' τ P C Γ (s :: ss) C'' Γ''

end

/-- `StmtHasType` instantiated with `HasType`. -/
abbrev StmtHasType (P : Program) :=
  @StmtHasType' LTy P instHasType

/-- `StmtsHasType` instantiated with `HasType`. -/
abbrev StmtsHasType (P : Program) :=
  @StmtsHasType' LTy P instHasType

/-- `StmtHasType` instantiated with `HasTypeA`. -/
abbrev StmtHasTypeA (P : Program) :=
  @StmtHasType' LMonoTy P instHasTypeA

/-- `StmtsHasType` instantiated with `HasTypeA`. -/
abbrev StmtsHasTypeA (P : Program) :=
  @StmtsHasType' LMonoTy P instHasTypeA

end -- public section

end TypeSpec
end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CmdTypeSpec
public import Strata.Languages.Core.Program

/-! ## Declarative Typing Specification for Commands (CmdExt)

This file specifies when a `Command` (= `CmdExt Expression`) is well-typed.
`Command` extends imperative `Cmd` with a procedure `call` instruction.

The specification is parameterized via `ExprTypingSpec` (see `CmdTypeSpec.lean`).
The `call` constructor requires that there exists a type instantiation `σ` such
that the actual argument types and LHS variable types match the procedure's
formal parameter types after applying `σ`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for extended commands (imperative commands + procedure calls).
-/
inductive CmdExtHasType' (C : LContext CoreLParams) (P : Program)
    [S : ExprTypingSpec τ] :
    TContext Unit → Command → TContext Unit → Prop where

  /-- A standard imperative command delegates to `CmdHasType'`. -/
  | cmd : ∀ Γ Γ' c,
      @CmdHasType' τ C S Γ c Γ' →
      CmdExtHasType' C P Γ (.cmd c) Γ'

  /-- A procedure call.

      There exists a type instantiation `σ` (mapping the procedure's type
      parameters to concrete monotypes) such that:
      - The procedure exists in the program.
      - Arities match (inputs and outputs).
      - All LHS (output) variables exist in the context.
      - Each input expression has the instantiated formal input type.
      - Each LHS variable's context type equals the instantiated formal output type.
      - In-out arguments are simple variable references with matching names. -/
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
        ∃ m, (CallArg.getInputExprs callArgs)[i]? =
        some (.fvar m (proc.header.inputs.keys[i]) none)) →
      CmdExtHasType' C P Γ (.call pname callArgs md) Γ

/-- `CmdExtHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev CmdExtHasType (C : LContext CoreLParams) (P : Program) :=
  @CmdExtHasType' _ C P instHasType

/-- `CmdExtHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev CmdExtHasTypeA (C : LContext CoreLParams) (P : Program) :=
  @CmdExtHasType' _ C P instHasTypeA

end -- public section

end TypeSpec
end Core

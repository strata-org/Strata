/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.CmdTypeSpec
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.WF

/-! ## The Typechecker Spec for Commands (CmdExt)

This file gives the typechecker spec for a `Command` (= `CmdExt Expression`).
`Command` extends imperative `Cmd` with a procedure `call` instruction.

Expressions are typed as read through the environment of
written type variables, as in `CmdHasType`. The `call` constructor requires
that there exists a type instantiation `σ` such that the actual argument types
and LHS variable types match the procedure's formal parameter types after
applying `σ`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typechecker spec for extended commands, threading the environment `Δ` of written type
    variables. A call leaves `Δ` unchanged; its inputs are read through `Δ` and their annotation
    type variables are rigid or bound in `Δ`. -/
inductive CmdExtHasType (C : LContext CoreLParams) (P : Program) :
    WrittenEnv → TContext Unit → Command → TContext Unit → WrittenEnv → Prop where
  /-- A standard imperative command delegates to `CmdHasType`. -/
  | cmd : ∀ Δ Γ c Γ' Δ',
      CmdHasType C Δ Γ c Γ' Δ' →
      CmdExtHasType C P Δ Γ (.cmd c) Γ' Δ'
  /-- A procedure call.

      There exists a type instantiation `σ` (mapping the procedure's type
      parameters to concrete monotypes) such that:
      - The procedure exists in the program, and the call is well-formed
        (`WF.WFcallProp`): its arguments match the procedure's parameters in
        number and mode, and its result variables are distinct.
      - All LHS (output) variables exist in the context.
      - Each input expression's type is alias-equivalent to the instantiated formal input type,
        and it satisfies the written-annotation requirement.
      - Each LHS variable's context type is alias-equivalent to the instantiated formal output
        type.

      The type arguments stored in the call are not constrained here: the
      checker ignores them and stores the instance `σ`, which
      `CmdExtWellTyped.call` requires of its output.

      A call leaves the context unchanged; the output `Γ'` is up to
      `TContext.Equiv` (see `CmdHasType`). -/
  | call : ∀ Δ Γ (pname : String) tyArgs callArgs proc md
      (σ : List (TyIdentifier × LMonoTy)) Γ',
      Program.Procedure.find? P pname = some proc →
      WF.WFcallProp P pname callArgs →
      (∀ v, v ∈ CallArg.getLhs callArgs → (Γ.types.find? v).isSome) →
      -- In-out arguments (an unannotated `fvar`) are typed by context lookup;
      -- by-value inputs are typed via `HasType`.
      (∀ i (hi : i < (CallArg.getInputExprs callArgs).length)
           (hj : i < proc.header.inputs.values.length),
        ∃ mty, AliasEquiv Γ.aliases mty
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (proc.header.inputs.values[i])) ∧
          (match (CallArg.getInputExprs callArgs)[i] with
           | .fvar _ x none => Γ.types.find? x = some (.forAll [] mty)
           | e => HasType C Γ (instAnnots Δ e) (.forAll [] mty))) →
      (∀ e ∈ CallArg.getInputExprs callArgs, WrittenAnnotsOk C Γ e) →
      (∀ e ∈ CallArg.getInputExprs callArgs, AnnotsInScope C.rigidTypeVars Δ e) →
      (∀ i (hi : i < (CallArg.getLhs callArgs).length)
           (hj : i < proc.header.outputs.values.length),
        ∃ mty, AliasEquiv Γ.aliases mty
            (LMonoTy.subst (Strata.Util.HMaps.ofScopes [σ]) (proc.header.outputs.values[i])) ∧
          Γ.types.find? ((CallArg.getLhs callArgs)[i]) = some (.forAll [] mty)) →
      TContext.Equiv (T := CoreLParams) Γ' Γ →
      CmdExtHasType C P Δ Γ (.call pname tyArgs callArgs md) Γ' Δ

end -- public section

end TypeSpec
end Core

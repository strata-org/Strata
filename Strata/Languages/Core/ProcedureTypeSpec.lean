/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementTypeSpec

/-! ## Declarative Typing Specification for Procedures

Specifies when a `Procedure` is well-typed, parameterized over the expression
typing predicate.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- Build the input-only type context for a procedure. -/
def procInputContext (proc : Procedure) (aliases : List TypeAlias) : TContext Unit :=
  { types := [LMonoTySignature.toTrivialLTy proc.header.inputs], aliases }

/-- Build the old-variable bindings for in-out parameters. -/
def procOldBindings (proc : Procedure) : List (CoreIdent × LTy) :=
  proc.header.getInoutParams.map fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty)

/-- Build the full type context for a procedure (inputs + outputs + old vars). -/
def procFullContext (proc : Procedure) (aliases : List TypeAlias) : TContext Unit :=
  let ins : List (CoreIdent × LTy) := LMonoTySignature.toTrivialLTy proc.header.inputs
  let outs : List (CoreIdent × LTy) := LMonoTySignature.toTrivialLTy proc.header.outputs
  let old : List (CoreIdent × LTy) := procOldBindings proc
  { types := [ins ++ outs ++ old], aliases }

/--
Declarative typing for procedures, parameterized over `ExprTypingSpec`.

A procedure is well-typed if:
- Inputs and outputs have no duplicates
- Preconditions are bool-typed in the input-only context
- Postconditions are bool-typed in the input+output+old context
- The body is well-typed in the full context
-/
def ProcHasType' (τ : Type) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (P : Program) (proc : Procedure)
    (aliases : List TypeAlias) : Prop :=
  let Γ_in := procInputContext proc aliases
  let Γ_full := procFullContext proc aliases
  proc.header.inputs.keys.Nodup ∧
  proc.header.outputs.keys.Nodup ∧
  -- Preconditions are bool-typed in Γ_in
  (∀ lbl check, ListMap.find? proc.spec.preconditions lbl = some check →
    S.exprTyped C Γ_in check.expr (S.embed .bool)) ∧
  -- Postconditions are bool-typed in Γ_full
  (∀ lbl check, ListMap.find? proc.spec.postconditions lbl = some check →
    S.exprTyped C Γ_full check.expr (S.embed .bool)) ∧
  -- Body is well-typed in Γ_full
  (∃ C' Γ', StmtsHasType' τ P C Γ_full proc.body C' Γ')

/-- `ProcHasType` instantiated with `HasType`. -/
abbrev ProcHasType (C : LContext CoreLParams) (P : Program) (proc : Procedure)
    (aliases : List TypeAlias) : Prop :=
  @ProcHasType' LTy instHasType C P proc aliases

/-- `ProcHasType` instantiated with `HasTypeA`. -/
abbrev ProcHasTypeA (C : LContext CoreLParams) (P : Program) (proc : Procedure)
    (aliases : List TypeAlias) : Prop :=
  @ProcHasType' LMonoTy instHasTypeA C P proc aliases

end -- public section

end TypeSpec
end Core

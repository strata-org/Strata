/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureTypeSpec

/-! ## Declarative Typing Specification for Programs

Specifies when a `Program` is well-typed, parameterized over the expression
typing predicate.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/--
Declarative typing for individual declarations, parameterized over `ExprTypingSpec`.
-/
inductive DeclHasType' (τ : Type) [S : ExprTypingSpec τ]
    (P : Program) :
    LContext CoreLParams → TContext Unit → Decl →
    LContext CoreLParams → TContext Unit → Prop where

  /-- Abstract type declaration: adds the type name to known types. -/
  | type_con : ∀ C C' Γ tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs }
        default = .ok C' →
      DeclHasType' τ P C Γ (.type (.con tc) md) C' Γ

  /-- Type synonym declaration. -/
  | type_syn : ∀ C Γ ts md,
      DeclHasType' τ P C Γ (.type (.syn ts) md) C Γ

  /-- Datatype declaration. -/
  | type_data : ∀ C C' Γ block md,
      C.addMutualBlock block = .ok C' →
      DeclHasType' τ P C Γ (.type (.data block) md) C' Γ

  /-- Axiom: expression must have type bool. -/
  | ax : ∀ C Γ a md,
      S.exprTyped C Γ a.e (S.embed .bool) →
      DeclHasType' τ P C Γ (.ax a md) C Γ

  /-- Distinct declaration: all expressions must be well-typed. -/
  | distinct : ∀ C Γ l es md,
      (∀ e, e ∈ es → ∃ mty, S.exprTyped C Γ e (S.embed mty)) →
      DeclHasType' τ P C Γ (.distinct l es md) C Γ

  /-- Procedure declaration. -/
  | proc : ∀ C Γ proc md,
      ProcHasType' τ C P proc Γ.aliases →
      DeclHasType' τ P C Γ (.proc proc md) C Γ

  /-- Non-recursive function declaration. -/
  | func : ∀ C Γ func func' md,
      ¬ func.isRecursive →
      FuncHasType' τ C func' →
      DeclHasType' τ P C Γ (.func func md) (C.addFactoryFunction func') Γ

  /-- Mutually recursive function block. -/
  | recFuncBlock : ∀ C Γ (funcs funcs' : List Function) md,
      funcs ≠ [] →
      funcs'.length = funcs.length →
      (∀ f, f ∈ funcs → ¬ f.attr.any (· == .inline)) →
      -- Each function is well-typed in the extended context (with all signatures)
      (let C_ext := funcs.foldl (fun (acc : LContext CoreLParams) (f : Function) =>
        acc.addFactoryFunction { name := f.name, typeArgs := f.typeArgs,
                                 inputs := f.inputs, output := f.output }) C
       ∀ f, f ∈ funcs' → FuncHasType' τ C_ext f) →
      DeclHasType' τ P C Γ (.recFuncBlock funcs md)
        (funcs'.foldl (fun (acc : LContext CoreLParams) (f : Function) =>
          acc.addFactoryFunction f) C) Γ

/-- Declarative typing for a list of declarations. -/
inductive DeclsHasType' (τ : Type) [S : ExprTypingSpec τ]
    (P : Program) :
    LContext CoreLParams → TContext Unit → List Decl →
    LContext CoreLParams → TContext Unit → Prop where

  | nil : ∀ C Γ,
      DeclsHasType' τ P C Γ [] C Γ

  | cons : ∀ C C' C'' Γ Γ' Γ'' d ds,
      DeclHasType' τ P C Γ d C' Γ' →
      DeclsHasType' τ P C' Γ' ds C'' Γ'' →
      DeclsHasType' τ P C Γ (d :: ds) C'' Γ''

/-- A program is well-typed if all its declarations are well-typed in sequence
    and all top-level names are distinct. -/
def ProgHasType' (τ : Type) [S : ExprTypingSpec τ]
    (C₀ : LContext CoreLParams) (Γ₀ : TContext Unit) (p : Program) : Prop :=
  p.getNames.Nodup ∧
  ∃ C' Γ', DeclsHasType' τ p C₀ Γ₀ p.decls C' Γ'

/-- `DeclHasType` instantiated with `HasType`. -/
abbrev DeclHasType (P : Program) :=
  @DeclHasType' LTy instHasType P

/-- `DeclsHasType` instantiated with `HasType`. -/
abbrev DeclsHasType (P : Program) :=
  @DeclsHasType' LTy instHasType P

/-- `ProgHasType` instantiated with `HasType`. -/
abbrev ProgHasType :=
  @ProgHasType' LTy instHasType

/-- `DeclHasType` instantiated with `HasTypeA`. -/
abbrev DeclHasTypeA (P : Program) :=
  @DeclHasType' LMonoTy instHasTypeA P

/-- `DeclsHasType` instantiated with `HasTypeA`. -/
abbrev DeclsHasTypeA (P : Program) :=
  @DeclsHasType' LMonoTy instHasTypeA P

/-- `ProgHasType` instantiated with `HasTypeA`. -/
abbrev ProgHasTypeA :=
  @ProgHasType' LMonoTy instHasTypeA

end -- public section

end TypeSpec
end Core

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProcedureTypeSpec
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.DatatypeTypeSpec

/-! ## Declarative Typing Specification for Programs

Specifies when a whole `Program` is well-typed, parameterized over the
`ExprTypingSpec` typeclass (so it instantiates to both the polymorphic `HasType`
and the annotated `HasTypeA`), reusing the per-declaration specs
(`FuncHasType'`, `ProcHasType'`) for functions and procedures, and `MutualADTWF`
(`DatatypeTypeSpec.lean`) for datatype blocks.

The specification is layered:

* `DeclHasType'` — a single declaration, threading both the ambient `LContext`
  `C` (known types / functions / datatypes) and the `TContext` `Γ` (type
  aliases). This is the declaration-level analogue of `StatementHasType'`, which
  threads `C` across a statement list.
* `DeclsHasType'` / `ProgramHasType'` — the declaration list and the whole
  program, threading `DeclHasType'` (analogue of `StatementsHasType'`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-! ### Declaration and program typing -/

/--
`FactoryExtendedBy C C' newFuncs` says the context `C'` is `C` with exactly the
functions `newFuncs` added: `C'` agrees with `C` on every field except
`functions`, its factory contains everything `C`'s does plus each `f ∈ newFuncs`,
and it introduces no other function names.

Stating the extension declaratively (rather than as a literal `List.foldl` that
adds `newFuncs` to `C`) frees the soundness proof from inducting over the fold.
-/
structure FactoryExtendedBy
    (C C' : LContext CoreLParams) (newFuncs : List (LFunc CoreLParams)) : Prop where
  -- Every field except `functions` is unchanged.
  knownTypes_eq : C'.knownTypes = C.knownTypes
  datatypes_eq : C'.datatypes = C.datatypes
  idents_eq : C'.idents = C.idents
  rigidTypeVars_eq : C'.rigidTypeVars = C.rigidTypeVars
  /-- Every function already in `C` is still present. -/
  preserves_old : ∀ nm ∈ C.functions, nm ∈ C'.functions
  /-- Every new function's name is present in `C'`. -/
  contains_new : ∀ f ∈ newFuncs, f.name.name ∈ C'.functions
  /-- No name is present in `C'` unless it was in `C` or is one of the new
      functions (the factory grows by exactly `newFuncs`). -/
  no_other : ∀ nm ∈ C'.functions, nm ∈ C.functions ∨ nm ∈ newFuncs.map (·.name.name)

/--
Declarative typing for a single declaration, parameterized over `ExprTypingSpec`.

`DeclHasType' τ P C Γ decl C' Γ'` reads: "under program `P`, in ambient context
`C` and type-scope `Γ`, declaration `decl` is well-typed and yields output
context `C'` and type-scope `Γ'`." `P` is threaded to `ProcHasType'` (so
procedure bodies can resolve `call`s and local `funcDecl`s).

Only `type` synonyms extend `Γ` (with a new alias); type constructors/datatypes
and function/procedure declarations extend `C` (with a known type, datatype
factory entries, or factory functions).
-/
inductive DeclHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → Decl →
    LContext CoreLParams → TContext Unit → Prop where

  /-- A type-constructor declaration: the new type is added to `C`'s known types
      (must not clash with an existing one); `Γ` is unchanged. -/
  | type_con : ∀ C C' Γ tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      DeclHasType' τ P C Γ (.type (.con tc) md) C' Γ

  /-- A type-synonym declaration: the alias is well-formed (distinct type args,
      body closed over the args, no phantom args, name not reserved), and `Γ`
      gains it. The stored body is fully de-aliased — alias-free w.r.t. the
      existing aliases and alias-equivalent to the written body. `C` is unchanged. -/
  | type_syn : ∀ C Γ ts md storedTy,
      ts.typeArgs.Nodup →
      (∀ v, v ∈ LMonoTy.freeVars ts.type → v ∈ ts.typeArgs) →
      (∀ v, v ∈ ts.typeArgs → v ∈ LMonoTy.freeVars ts.type) →
      ¬ C.knownTypes.containsName ts.name →
      LMonoTy.aliasFree Γ.aliases storedTy →
      AliasEquiv Γ.aliases storedTy ts.type →
      DeclHasType' τ P C Γ (.type (.syn ts) md) C
        { Γ with aliases := { typeArgs := ts.typeArgs, name := ts.name, type := storedTy } :: Γ.aliases }

  /-- A (mutual) datatype declaration: the block is well-formed (`MutualADTWF`);
      the datatypes and their generated functions extend `C`. `Γ` is unchanged. -/
  | type_data : ∀ C C' Γ block md,
      MutualADTWF C block →
      C.addMutualBlock block = .ok C' →
      DeclHasType' τ P C Γ (.type (.data block) md) C' Γ

  /-- An axiom declaration: its expression is a `bool` in the current context.
      Contexts are unchanged. -/
  | ax : ∀ C Γ a md,
      S.exprTyped C Γ a.e (S.embed .bool) →
      DeclHasType' τ P C Γ (.ax a md) C Γ

  /-- A `distinct` declaration: each listed expression is well-typed at some
      monotype. Contexts are unchanged. -/
  | distinct : ∀ C Γ l es md,
      (∀ e ∈ es, ∃ mty, S.exprTyped C Γ e (S.embed mty)) →
      DeclHasType' τ P C Γ (.distinct l es md) C Γ

  /-- A procedure declaration: it is well-typed per `ProcHasType'` (evaluated in
      the enclosing program `P`). Contexts are unchanged. -/
  | proc : ∀ C Γ proc md,
      ProcHasType' τ P C Γ proc →
      DeclHasType' τ P C Γ (.proc proc md) C Γ

  /-- A function declaration: non-recursive and well-typed per `FuncHasType'`;
      the output `C'` is `C` extended with the function (via `FactoryExtendedBy`).
      `Γ` is unchanged. -/
  | func : ∀ C C' Γ func md,
      ¬ func.isRecursive →
      FuncHasType' τ C Γ func →
      FactoryExtendedBy C C' [func.toLFunc] →
      DeclHasType' τ P C Γ (.func func md) C' Γ

  /-- A mutually recursive function block. Two-phase:

      * `Cstub` is `C` extended with a signature stub for every block function (so
        mutual calls resolve during body checking);
      * every block function is well-typed against `Cstub`;
      * the output `C'` is `C` extended with each function's full `toLFunc`.

      The block is non-empty and contains no `inline` functions; `Γ` is unchanged. -/
  | recFuncBlock : ∀ C Cstub C' Γ funcs md stubs fullFuncs,
      funcs ≠ [] →
      (∀ f ∈ funcs, ∀ a ∈ f.attr, a ≠ .inline) →
      stubs = funcs.map (fun f => { name := f.name, typeArgs := f.typeArgs,
                                    inputs := f.inputs, output := f.output }) →
      fullFuncs = funcs.map (·.toLFunc) →
      FactoryExtendedBy C Cstub stubs →
      FactoryExtendedBy C C' fullFuncs →
      (∀ f ∈ funcs, FuncHasType' τ Cstub Γ f) →
      DeclHasType' τ P C Γ (.recFuncBlock funcs md) C' Γ

/--
Declarative typing for a list of declarations, threading `C` and `Γ` (analogue
of `StatementsHasType'`). `P` is fixed across the list (it is the enclosing program).
-/
inductive DeclsHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ] :
    LContext CoreLParams → TContext Unit → List Decl →
    LContext CoreLParams → TContext Unit → Prop where

  /-- The empty declaration list leaves the context unchanged. -/
  | nil : ∀ C Γ,
      DeclsHasType' τ P C Γ [] C Γ

  /-- The first declaration is typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' d ds,
      DeclHasType' τ P C Γ d C' Γ' →
      DeclsHasType' τ P C' Γ' ds C'' Γ'' →
      DeclsHasType' τ P C Γ (d :: ds) C'' Γ''

/--
Declarative typing for a whole program `P` from ambient context `C` and type-scope
`Γ`: every declared name is globally distinct (`P.getNames.Nodup`, a single flat
namespace across all declaration kinds), and the declarations are well-typed. `P`
is passed as its own enclosing program so procedure bodies can resolve calls.
-/
def ProgramHasType' (τ : Type) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (Γ : TContext Unit) (P : Program) : Prop :=
  P.getNames.Nodup ∧ ∃ C' Γ', DeclsHasType' τ P C Γ P.decls C' Γ'

/-! ### Instantiations -/

/-- `DeclHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev DeclHasType (P : Program) :=
  @DeclHasType' LTy P instHasType

/-- `DeclHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev DeclHasTypeA (P : Program) :=
  @DeclHasType' LMonoTy P instHasTypeA

/-- `DeclsHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev DeclsHasType (P : Program) :=
  @DeclsHasType' LTy P instHasType

/-- `DeclsHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev DeclsHasTypeA (P : Program) :=
  @DeclsHasType' LMonoTy P instHasTypeA

/-- `ProgramHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev ProgramHasType :=
  @ProgramHasType' LTy instHasType

/-- `ProgramHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev ProgramHasTypeA :=
  @ProgramHasType' LMonoTy instHasTypeA

end -- public section

end TypeSpec
end Core

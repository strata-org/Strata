/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
public import Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.Languages.Core.Typing.Spec.TypeSpecShared
public import Strata.Languages.Core.Typing.Spec.ProcSigAgreement

/-! ## The Typechecker Spec for Programs

Specifies when a whole `Program` satisfies the typechecker spec, reusing the
per-declaration specs (`FuncHasTypeExact`, `ProcHasType`) for functions and
procedures. A datatype block is typed by registering an alias-equivalent copy of
it with `LContext.addMutualBlock`.

The specification is layered:

* `DeclHasType` — a single declaration, threading both the ambient `LContext`
  `C` (known types / functions / datatypes) and the `TContext` `Γ` (type
  aliases). This is the declaration-level analogue of `StatementHasType`, which
  threads `C` across a statement list.
* `DeclsHasType` / `ProgramHasType` — the declaration list and the whole
  program, threading `DeclHasType` (analogue of `StatementsHasType`).

The checker renames each type parameter of a function, procedure or lemma that starts with a
reserved prefix, so a declaration is typed through a renaming of its type parameters
(`FuncAlphaVariant`, `ProcAlphaVariant`, `LemmaAlphaVariant`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-! ### Declaration and program typing -/

/-- `l'` is `l` with some of its reserved type parameters renamed throughout, injectively and to
    names that neither `l` nor the context `C`, `Γ` uses (`TyArgRenaming`). -/
def LemmaAlphaVariant (C : LContext CoreLParams) (Γ : TContext Unit) (l l' : Lemma) : Prop :=
  ∃ ren : List (String × String),
    TyArgRenaming C Γ l.typeArgs l.mentionedTyVars ren ∧ l' = l.renameTypeArgs ren

/-- The factory entry `g` stored for the declared function `f` has the shape of `f`: the same
    constructor flag, recursion flag and attributes, a body and a measure exactly when `f` has
    them, the same metadata on its preconditions (so as many of them), and as many axioms. -/
structure FuncShapeAgree (f g : LFunc CoreLParams) : Prop where
  isConstr : f.isConstr = g.isConstr
  isRecursive : f.isRecursive = g.isRecursive
  attr : f.attr = g.attr
  body : f.body.isSome = g.body.isSome
  measure : f.measure.isSome = g.measure.isSome
  axiomsLength : f.axioms.length = g.axioms.length
  preconditionsMetadata : f.preconditions.map (·.md) = g.preconditions.map (·.md)

/-- The factory entry `g` stored for the declared function `f` agrees with `f` in signature, up
    to the aliases of `Γ`, and in shape. -/
def FuncEntryOk (Γ : TContext Unit) (f g : LFunc CoreLParams) : Prop :=
  FuncSigAgree Γ.aliases f g ∧ FuncShapeAgree f g

/-- The conditions on a type synonym declaring the alias `a`, whose body is stored as
    `storedTy`, with `Γ'` the type scope after it: the alias is well formed, its name is not a
    known type or an alias in scope, and the written body is a valid source type resolving to
    `storedTy` through the aliases in scope. -/
structure InputSynonymOk (C : LContext CoreLParams) (Γ : TContext Unit) (a : TypeAlias)
    (storedTy : LMonoTy) (Γ' : TContext Unit) : Prop where
  wf : TypeAlias.WF a
  nameUnregistered : ¬ C.knownTypes.containsName a.name
  nameFresh : ∀ al ∈ Γ.aliases, al.name ≠ a.name
  bodyTyped : SourceTyWF C TyVarAdmissibility.all Γ.aliases a.type storedTy
  storedAliasFree : LMonoTy.aliasFree Γ.aliases storedTy
  scope : Γ' = { Γ with aliases := { a with type := storedTy } :: Γ.aliases }

/--
The typechecker spec for a single declaration.

`DeclHasType P C Γ decl C' Γ'` reads: "under program `P`, in ambient context
`C` and type-scope `Γ`, declaration `decl` is typed and yields output
context `C'` and type-scope `Γ'`." `P` is threaded to `ProcHasTypeExact` (so
procedure bodies can resolve `call`s).

Only `type` synonyms extend `Γ` (with a new alias); type constructors/datatypes
and function declarations extend `C` (with a known type, datatype
factory entries, or factory functions).
-/
inductive DeclHasType (P : Program) :
    LContext CoreLParams → TContext Unit → Decl →
    LContext CoreLParams → TContext Unit → Prop where

  /-- A type-constructor declaration: the new type is added to `C`'s known types (must not clash
      with an existing one); `Γ` is unchanged. -/
  | type_con : ∀ C C' Γ tc md,
      C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default = .ok C' →
      DeclHasType P C Γ (.type (.con tc) md) C' Γ

  /-- A type-synonym declaration meeting `InputSynonymOk` for the alias it declares, for some
      stored body type, with `Γ'` the type scope after it; `C` is unchanged. -/
  | type_syn : ∀ C Γ ts md Γ',
      (∃ storedTy, InputSynonymOk C Γ
        { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } storedTy Γ') →
      DeclHasType P C Γ (.type (.syn ts) md) C Γ'

  /-- A (mutual) datatype declaration: `LContext.addMutualBlock` accepts an alias-equivalent copy
      `block_r` of the block and extends `C` with its datatypes and their generated functions
      to `C'`. `Γ` is unchanged. -/
  | type_data : ∀ C C' Γ block md block_r,
      MutualBlockTyCompat Γ block_r block →
      C.addMutualBlock block_r = .ok C' →
      DeclHasType P C Γ (.type (.data block) md) C' Γ

  /-- An axiom declaration: a `bool` proposition with no type parameters; contexts are
      unchanged. -/
  | ax : ∀ (C : LContext CoreLParams) Γ a md,
      HasType C Γ a.e (.forAll [] .bool) →
      WrittenAnnotsOk C Γ a.e →
      AnnotsInScope [] (fun _ => none) a.e →
      DeclHasType P C Γ (.ax a md) C Γ

  /-- A lemma declaration with a renaming `l'` of its type parameters (`LemmaAlphaVariant`) that
      is a `bool` proposition over distinct type parameters with no reserved prefix; contexts are
      unchanged. -/
  | lemma : ∀ (C : LContext CoreLParams) Γ l l' md,
      LemmaAlphaVariant C Γ l l' →
      HasType C Γ l'.e (.forAll [] .bool) →
      WrittenAnnotsOk C Γ l'.e →
      l'.typeArgs.Nodup →
      (∀ a ∈ l'.typeArgs, isAllowedName a = true) →
      AnnotsInScope l'.typeArgs (fun _ => none) l'.e →
      DeclHasType P C Γ (.lemma l md) C Γ

  /-- A `distinct` declaration: expressions of one monotype, any number of them (fewer than two
      hold trivially); contexts are unchanged. -/
  | distinct : ∀ (C : LContext CoreLParams) Γ l es md,
      (∃ mty, ∀ e ∈ es, HasType C Γ e (.forAll [] mty)) →
      (∀ e ∈ es, WrittenAnnotsOk C Γ e) →
      (∀ e ∈ es, AnnotsInScope [] (fun _ => none) e) →
      DeclHasType P C Γ (.distinct l es md) C Γ

  /-- A procedure declaration that satisfies the typechecker spec `ProcHasType` (evaluated in
      the enclosing program `P`). Contexts are unchanged. -/
  | proc : ∀ C Γ proc md,
      ProcHasType P C Γ proc →
      DeclHasType P C Γ (.proc proc md) C Γ

  /-- A non-recursive function declaration whose name is not a function name of `C`, with a
      renaming `f'` of its type parameters (`FuncAlphaVariant`) that satisfies the typechecker
      spec, extends `C` with an entry agreeing with `f'` per `FuncEntryOk`; `Γ` is unchanged. -/
  | func : ∀ C C' Γ func f' md,
      ¬ func.isRecursive →
      func.name.name ∉ C.functions →
      FuncAlphaVariant C Γ func f' →
      FuncHasTypeExact C Γ f' →
      FactoryExtendedBy (FuncEntryOk Γ) C C' [f'.toLFunc] →
      DeclHasType P C Γ (.func func md) C' Γ

  /-- A non-empty mutually recursive block of recursive, non-`inline` functions, none with a
      function name of `C`, with renamings `funcs'` of their type parameters
      (`FuncAlphaVariant`) each typed against `Cstub` (`C` plus the signature stub of every
      renamed function), extends `C` with every renamed function; `Γ` is unchanged. -/
  | recFuncBlock : ∀ C Cstub C' Γ funcs funcs' md stubs fullFuncs,
      funcs ≠ [] →
      (∀ f ∈ funcs, f.name.name ∉ C.functions) →
      (∀ f ∈ funcs, ∀ a ∈ f.attr, a ≠ .inline) →
      List.Rel₂ (FuncAlphaVariant C Γ) funcs funcs' →
      stubs = funcs'.map (fun f => { name := f.name, typeArgs := f.typeArgs,
                                     inputs := f.inputs, output := f.output }) →
      fullFuncs = funcs'.map (·.toLFunc) →
      FactoryExtendedBy (FuncEntryOk Γ) C Cstub stubs →
      FactoryExtendedBy (FuncEntryOk Γ) C C' fullFuncs →
      (∀ f ∈ funcs', FuncHasTypeExact Cstub Γ f) →
      (∀ f ∈ funcs, f.isRecursive = true) →
      DeclHasType P C Γ (.recFuncBlock funcs md) C' Γ

/--
The typechecker spec for a list of declarations, threading `C` and `Γ`
(analogue of `StatementsHasType`). `P` is fixed across the list (it is the
enclosing program).
-/
inductive DeclsHasType (P : Program) :
    LContext CoreLParams → TContext Unit → List Decl →
    LContext CoreLParams → TContext Unit → Prop where

  /-- The empty declaration list leaves the context unchanged. -/
  | nil : ∀ C Γ,
      DeclsHasType P C Γ [] C Γ

  /-- The first declaration is typed, then the rest in the updated context. -/
  | cons : ∀ C C' C'' Γ Γ' Γ'' d ds,
      DeclHasType P C Γ d C' Γ' →
      DeclsHasType P C' Γ' ds C'' Γ'' →
      DeclsHasType P C Γ (d :: ds) C'' Γ''

/--
The typechecker spec for a whole program `P` from ambient context `C` and
type-scope `Γ`: every declared name is globally distinct (`P.getNames.Nodup`, a
single flat namespace across all declaration kinds) and absent from the ambient
identifiers `C.idents`, and the declarations are typed. `P` is passed as its own
enclosing program so procedure bodies can resolve calls.
-/
def ProgramHasType (C : LContext CoreLParams) (Γ : TContext Unit) (P : Program) : Prop :=
  P.getNames.Nodup ∧ (∀ n ∈ P.getNames, n.name ∉ C.idents) ∧
    ∃ C' Γ', DeclsHasType P C Γ P.decls C' Γ'

end -- public section

end TypeSpec
end Core

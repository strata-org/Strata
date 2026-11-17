/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.StatementTypeSpec
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.TypeSkolem

/-! ## The Typechecker Spec for Procedures

Specifies when a `Procedure` satisfies the typechecker spec, reusing `StatementsHasTypeΔ'` for
the body.

`ProcHasType'` holds when: its parameter, return and
type-argument names are distinct, no type parameter has a reserved prefix, and
its signature has no undeclared type variables; every variable the body
modifies is an output or body-local; each pre/postcondition is a `bool`
expression in the appropriate context with valid written annotations whose
free-variable and binder type variables are type parameters of the procedure
(operator annotations are not scoped); and its body satisfies the typechecker spec under
the empty enclosing-label set (a CFG body carries no obligation).
Preconditions are typed in the input context (inputs only); postconditions and
the body in the body context (inputs, outputs, and an `old g` binding per
in-out parameter `g`). `ProcHasType` asks this of some renaming of the reserved
type parameters (`ProcAlphaVariant`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typing context for a procedure's preconditions: the ambient context `Γ`
    with one new scope binding each input parameter to its declared monotype.
    Return variables are intentionally absent — preconditions may not reference them. -/
def procInputContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  { Γ with types := procInputScopes Γ.types proc }

/-- The typing context for a procedure's postconditions and body: the input scope
    extended with the outputs and, for each in-out parameter `g`, an `old g`
    binding at `g`'s type.

    The bindings are those of `Procedure.paramTys`. Scopes are concatenated
    `old ++ output ++ input`; `HMap.ofList` keeps the last occurrence of a key, giving
    `input`-then-`output`-then-`old` priority. -/
def procBodyContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  { Γ with types := procBodyScopes Γ.types proc }

/--
The typechecker spec for a procedure body, in ambient context `C` and body-scope
`Γ_body`. The body's output contexts `C'`/`Γ'` are free arguments of `structured`.

* `structured`: the statement list is typed with no enclosing labels
  (`L = []`, so every `exit` targets a lexically enclosing `block`) and with no written type
  variable bound.
* `cfg`: a CFG body carries no obligation.
-/
inductive ProcBodyHasType' (P : Program) (C : LContext CoreLParams) (Γ_body : TContext Unit) :
    Procedure.Body → Prop where
  | structured : ∀ ss C' Γ' Δ',
      StatementsHasTypeΔ' P C Γ_body (fun _ => none) [] ss C' Γ' Δ' →
      ProcBodyHasType' P C Γ_body (.structured ss)
  | cfg : ∀ c, ProcBodyHasType' P C Γ_body (.cfg c)

/--
The typechecker spec for procedures.
`P` is the enclosing program (threaded to the body's `StatementsHasTypeΔ'` for
command typing); `C` and `Γ` are the ambient context and type-scope the procedure
declaration is checked in.
-/
structure ProcHasType' (P : Program) (C : LContext CoreLParams) (Γ : TContext Unit)
    (proc : Procedure) : Prop where
  /-- The procedure's input parameter names are distinct. -/
  inputsNodup : proc.header.inputs.keys.Nodup
  /-- The procedure's output (return) variable names are distinct. -/
  outputsNodup : proc.header.outputs.keys.Nodup
  /-- No parameter is named like the saved starting value of an in-out parameter. -/
  oldNamesFresh : proc.header.oldNamesFresh
  /-- The procedure's type argument names are distinct. -/
  typeArgsNodup : proc.header.typeArgs.Nodup
  /-- No type parameter starts with a reserved prefix. -/
  typeArgsNotReserved : ∀ a ∈ proc.header.typeArgs, isAllowedName a = true
  /-- Every free type variable in the input/output signature is declared in
      `typeArgs`. -/
  noUndeclaredVars : proc.header.SigDeclared
  /-- Each input and output parameter type is a valid written type. -/
  signatureWellKinded : ∀ ty ∈ proc.header.inputs.values ++ proc.header.outputs.values,
    ValidWrittenTy C Γ.aliases ty
  /-- Every variable the body modifies is an output parameter or is defined in
      the body (the modification-rights check). -/
  modRights : ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body →
    v ∈ proc.header.outputs.keys ++
        HasVarsImp.definedVars (P := Expression) proc.body false
  /-- Each precondition is a `bool` expression in the input context. -/
  preconditionsTyped : ∀ c ∈ proc.spec.preconditions.values,
    HasType C (procInputContext Γ proc) c.expr (.forAll [] .bool)
  /-- Each postcondition is a `bool` expression in the body context (which
      includes outputs and `old` bindings for in-out parameters). -/
  postconditionsTyped : ∀ c ∈ proc.spec.postconditions.values,
    HasType C (procBodyContext Γ proc) c.expr (.forAll [] .bool)
  /-- Each precondition satisfies the written-annotation requirement. -/
  preconditionsAnnots : ∀ c ∈ proc.spec.preconditions.values,
    WrittenAnnotsOk C (procInputContext Γ proc) c.expr
  /-- Each postcondition satisfies the written-annotation requirement. -/
  postconditionsAnnots : ∀ c ∈ proc.spec.postconditions.values,
    WrittenAnnotsOk C (procBodyContext Γ proc) c.expr
  /-- Each annotation type variable in a precondition is a procedure type parameter. -/
  preconditionsInScope : ∀ c ∈ proc.spec.preconditions.values,
    AnnotsInScope proc.header.typeArgs (fun _ => none) c.expr
  /-- Each annotation type variable in a postcondition is a procedure type parameter. -/
  postconditionsInScope : ∀ c ∈ proc.spec.postconditions.values,
    AnnotsInScope proc.header.typeArgs (fun _ => none) c.expr
  /-- The body is typed in the body context, with the procedure's type arguments rigid. -/
  bodyTyped : ProcBodyHasType' P
    { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }
    (procBodyContext Γ proc) proc.body
  /-- No input or output parameter is named like an in-scope function. -/
  formalsNotFunctions : ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
    id.name ∉ C.functions

/-- `proc'` is `proc` with some of its reserved type parameters renamed throughout, injectively
    and to names that neither `proc` nor the context `C`, `Γ` uses (`TyArgRenaming`). -/
def ProcAlphaVariant (C : LContext CoreLParams) (Γ : TContext Unit) (proc proc' : Procedure) :
    Prop :=
  ∃ ren : List (String × String),
    TyArgRenaming C Γ proc.header.typeArgs proc.mentionedTyVars ren ∧
      proc' = proc.renameTypeArgs ren

/-- The typechecker spec for procedures: some renaming of the type parameters of `proc`
    (`ProcAlphaVariant`) satisfies `ProcHasType'`. -/
def ProcHasType (P : Program) (C : LContext CoreLParams) (Γ : TContext Unit)
    (proc : Procedure) : Prop :=
  ∃ proc', ProcAlphaVariant C Γ proc proc' ∧ ProcHasType' P C Γ proc'

end -- public section

end TypeSpec
end Core

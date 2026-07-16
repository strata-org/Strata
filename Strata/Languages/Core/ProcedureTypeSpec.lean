/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementTypeSpec
public import Strata.Languages.Core.Procedure

/-! ## Declarative Typing Specification for Procedures

Specifies when a `Procedure` is well-typed, parameterized over the
`ExprTypingSpec` typeclass (so it instantiates to both the polymorphic `HasType`
and the annotated `HasTypeA`), reusing `StmtsHasType'` for the body.

A procedure is well-typed (per `Core.Procedure.typeCheck`) when:

1. Its formal parameter names are distinct and its return variable names are
   distinct (`checkNoDuplicates`).
2. Its type argument names are distinct and every type variable in the
   input/output signature is declared in `typeArgs` (`checkTypeArgsWF`).
3. Every variable the body modifies is either an output parameter or a variable
   defined in the body (`checkModificationRights`).
4. Each precondition is a `bool` expression in the *input* context — the ambient
   `Γ` extended with a scope binding each input parameter to its declared type
   (`typeCheckConditions … proc.spec.preconditions` against `envWithInputs`).
   Preconditions may not reference return variables.
5. Each postcondition is a `bool` expression in the *body* context — the input
   context further extended with the output parameters and, for each in-out
   parameter `g`, an `old g` binding (`typeCheckConditions … proc.spec.postconditions`
   against `envWithOldVars`).
6. Its body (when structured) is well-typed as a statement list in the body
   context, under the empty enclosing-label set `L = []` (so every `exit` in the
   body must target a lexically enclosing `block`). CFG bodies are rejected by
   the checker (`Statement.typeCheck … proc.body`).

This is intended as a *complete* characterization of `Procedure.typeCheck`'s
type-level obligations (only the soundness direction — a successful check implies
this spec — is proved).

### Type parameters

The declarative contexts store the parameter types with their *declared*
(user-named) type variables; the soundness proof bridges to the checker's
fresh-variable instantiation/renaming. `Procedure.typeCheck` requires the
`typeArgs` to be distinct and every signature type variable to be declared in
`typeArgs`, captured by the `typeArgsNodup` and `noUndeclaredVars` fields.

### Contexts

Both `procInputContext` and `procBodyContext` push a *single new scope* onto
`Γ.types` (mirroring `setupInputEnv`'s one `pushEmptyContext` followed by
`addInNewestContext` calls that all append to that same newest scope):

* `procInputContext` — newest scope = inputs.
* `procBodyContext`  — newest scope = inputs ++ outputs ++ old-inout bindings.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typing context for a procedure's preconditions: the ambient context `Γ`
    (in which the procedure declaration is checked) with one new newest scope
    binding each input parameter to its declared monotype (as a trivial polytype).
    Mirrors `setupInputEnv` (`pushEmptyContext` then `addInNewestContext` of the
    inputs). Return variables are intentionally absent — preconditions may not
    reference them. -/
def procInputContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  let inputScope := proc.header.inputs.map (fun (id, mty) => (id, .forAll [] mty))
  { Γ with types := Γ.types.push inputScope }

/-- The typing context for a procedure's postconditions and body: the input
    context further extended (in the *same* newest scope) with the output
    parameters and, for each in-out parameter `g`, an `old g` binding at `g`'s
    type. Mirrors the `envWithOutputs`/`envWithOldVars` steps, each of which
    `addInNewestContext`s onto the scope pushed by `setupInputEnv`. -/
def procBodyContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  let inputScope := proc.header.inputs.map (fun (id, mty) => (id, .forAll [] mty))
  let outputScope := proc.header.outputs.map (fun (id, mty) => (id, .forAll [] mty))
  let oldScope := proc.header.getInoutParams.map
    (fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty))
  { Γ with types := Γ.types.push (inputScope ++ outputScope ++ oldScope) }

/--
Declarative typing for a procedure body, in ambient context `C` and body-scope
`Γ_body`. Split out as an inductive (rather than an existential inside
`ProcHasType'`) so the body's output contexts `C'`/`Γ'` are carried by the
`structured` constructor instead of being existentially quantified — this keeps
`ProcHasType'` free of `∀`/`∃` alternation, which eases deriving property-based
testing generators.

* `structured`: the statement list is well-typed with no enclosing labels
  (`L = []`), so every `exit` in the body targets a lexically enclosing `block`.
  The body's output context is not retained (the body scope is popped after
  checking), so `C'`/`Γ'` are free constructor arguments.
* `cfg`: CFG bodies are rejected by `Procedure.typeCheck`, so they carry no
  typing obligation (this constructor always applies).
-/
inductive ProcBodyHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (Γ_body : TContext Unit) : Procedure.Body → Prop where
  | structured : ∀ ss C' Γ',
      StmtsHasType' τ P C Γ_body [] ss C' Γ' →
      ProcBodyHasType' τ P C Γ_body (.structured ss)
  | cfg : ∀ c, ProcBodyHasType' τ P C Γ_body (.cfg c)

/--
Declarative typing for procedures, parameterized over `ExprTypingSpec`.
`P` is the enclosing program (threaded to the body's `StmtsHasType'` for
`funcDecl`); `C` and `Γ` are the ambient context and type-scope the procedure
declaration is checked in.
-/
structure ProcHasType' (τ : Type) (P : Program) [S : ExprTypingSpec τ]
    (C : LContext CoreLParams) (Γ : TContext Unit) (proc : Procedure) : Prop where
  /-- The procedure's input parameter names are distinct. -/
  inputsNodup : proc.header.inputs.keys.Nodup
  /-- The procedure's output (return) variable names are distinct. -/
  outputsNodup : proc.header.outputs.keys.Nodup
  /-- The procedure's type argument names are distinct. -/
  typeArgsNodup : proc.header.typeArgs.Nodup
  /-- Every free type variable in the input/output signature is declared in
      `typeArgs`. -/
  noUndeclaredVars : ∀ v,
    v ∈ LMonoTys.freeVars proc.header.inputs.values ++
        LMonoTys.freeVars proc.header.outputs.values →
    v ∈ proc.header.typeArgs
  /-- Every variable the body modifies is an output parameter or is defined in
      the body (the modification-rights check). -/
  modRights : ∀ v, v ∈ HasVarsImp.modifiedVars (P := Expression) proc.body →
    v ∈ proc.header.outputs.keys ++
        HasVarsImp.definedVars (P := Expression) proc.body false
  /-- Each precondition is a `bool` expression in the input context. -/
  preconditionsTyped : ∀ c ∈ proc.spec.preconditions.values,
    S.exprTyped C (procInputContext Γ proc) c.expr (S.embed .bool)
  /-- Each postcondition is a `bool` expression in the body context (which
      includes outputs and `old` bindings for in-out parameters). -/
  postconditionsTyped : ∀ c ∈ proc.spec.postconditions.values,
    S.exprTyped C (procBodyContext Γ proc) c.expr (S.embed .bool)
  /-- The body is well-typed in the body context (see `ProcBodyHasType'`). -/
  bodyTyped : ProcBodyHasType' τ P C (procBodyContext Γ proc) proc.body

/-- `ProcHasType'` instantiated with the polymorphic `HasType` relation. -/
abbrev ProcHasType (P : Program) :=
  @ProcHasType' LTy P instHasType

/-- `ProcHasType'` instantiated with the annotated `HasTypeA` relation. -/
abbrev ProcHasTypeA (P : Program) :=
  @ProcHasType' LMonoTy P instHasTypeA

end -- public section

end TypeSpec
end Core

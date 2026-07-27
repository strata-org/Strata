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

A procedure is well-typed when: its parameter/return/type-argument names are
distinct and its signature has no undeclared type variables; every variable the
body modifies is an output or body-local; each pre/postcondition is a `bool`
expression in the appropriate context; and its body (structured only — CFG bodies
are rejected) is well-typed under the empty enclosing-label set. Preconditions are
typed in the input context (inputs only); postconditions and the body in the body
context (inputs, outputs, and an `old g` binding per in-out parameter `g`).
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-- The typing context for a procedure's preconditions: the ambient context `Γ`
    with one new scope binding each input parameter to its declared monotype.
    Return variables are intentionally absent — preconditions may not reference them. -/
def procInputContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  let inputScope := proc.header.inputs.map (fun (id, mty) => (id, .forAll [] mty))
  { Γ with types := Γ.types.push inputScope }

/-- The typing context for a procedure's postconditions and body: the input
    context's scope further extended with the output parameters and, for each
    in-out parameter `g`, an `old g` binding at `g`'s type. -/
def procBodyContext (Γ : TContext Unit) (proc : Procedure) : TContext Unit :=
  let inputScope := proc.header.inputs.map (fun (id, mty) => (id, .forAll [] mty))
  let outputScope := proc.header.outputs.map (fun (id, mty) => (id, .forAll [] mty))
  let oldScope := proc.header.getInoutParams.map
    (fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty))
  { Γ with types := Γ.types.push (inputScope ++ outputScope ++ oldScope) }

/-- `procBodyContext` only extends `Γ.types`, so it leaves the alias list unchanged. -/
@[simp] theorem procBodyContext_aliases (Γ : TContext Unit) (proc : Procedure) :
    (procBodyContext Γ proc).aliases = Γ.aliases := by simp only [procBodyContext]

/-- `procBodyContext`'s `types` field is `Γ.types` with the parameter/output/old scope
    pushed on top. -/
theorem procBodyContext_types (Γ : TContext Unit) (proc : Procedure) :
    (procBodyContext Γ proc).types = Γ.types.push
      ((proc.header.inputs.map (fun (id, mty) => (id, .forAll [] mty))) ++
       (proc.header.outputs.map (fun (id, mty) => (id, .forAll [] mty))) ++
       (proc.header.getInoutParams.map
         (fun (id, ty) => (CoreIdent.mkOld id.name, .forAll [] ty)))) := by
  simp only [procBodyContext]

/--
Declarative typing for a procedure body, in ambient context `C` and body-scope
`Γ_body`. The body's output contexts `C'`/`Γ'` are free arguments of `structured`.

* `structured`: the statement list is well-typed with no enclosing labels
  (`L = []`), so every `exit` targets a lexically enclosing `block`.
* `cfg`: CFG bodies are rejected by the checker, so they carry no obligation.
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

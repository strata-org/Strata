/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation.LaurelCompilationPipeline

/-!
A type-parameter reference that reaches resolution ALREADY tvarized, which no Laurel
*source* program can produce: the grammar has one shape for a bare name in type position,
so the parser always hands resolution a `HighType.UserDefined` and the `.UserDefined` arm
of `resolveHighType` reclassifies it to `.TVar` — stamping the binder's `uniqueId` on the
way through.

A front end does not go through the grammar. It builds the Laurel AST directly and already
knows, from its own type system, that a name is a type variable, so it emits
`HighType.TVar` itself (`JavaToLaurelCompiler`, `HighType.TVar(ident(...))`). It cannot
supply a `uniqueId` — those are allocated by resolution — so the reference arrives bare and
`resolveHighType`'s dedicated `.TVar` arm is the only thing that stamps it; the catch-all
passes a type through unchanged.

That arm is load-bearing because scope membership for a type variable is decided on BINDER
IDENTITY (`uniqueId`), not spelling: an unstamped reference is in no scope at all, so a
generic call in a front-end generic body has no evidence for its type argument and is
reported as un-inferable. Two things make such a report especially bad. `ContractPass`
introduces the annotation (it types a polymorphic callee's argument temp from the argument,
so a postcondition helper is called with `var $cp: T`), and a pass-created annotation is
only re-resolved AFTER that pass — where the pipeline wraps any newly introduced diagnostic
as an internal error blaming the compiler.

These are unit tests rather than corpus cases because the corpus goes through the parser,
which cannot express the input.
-/

open Strata

namespace Strata.Laurel

private def ty (highType : HighType) : HighTypeMd := ⟨highType, default⟩
private def md (expr : StmtExpr) : StmtExprMd := ⟨expr, default⟩
private def varMd (v : Variable) : VariableMd := ⟨v, default⟩

/-- `procedure f<T>(value: T) returns (result: int) opaque ensures true { result := 3 }`,
    with `value`'s type built as a front end builds it: a `HighType.TVar` naming `T`
    directly, with no `uniqueId`.

    An `ensures` and an implementation are both required to reach the failing shape.
    `ContractPass` snapshots the inputs into `$cp_N` temporaries only when there is a
    postcondition to ASSERT at the end of a body, and it is the temp's annotation —
    reconstructed from the argument, because the declared parameter type mentions a type
    variable — that carries the unstamped `T` into the helper call. -/
private def frontEndTypeVarProgram (valueType : HighType) : Program :=
  { staticProcedures := [
      { name := mkId "f"
        typeArgs := [mkId "T"]
        inputs := [{ name := mkId "value", type := ty valueType }]
        outputs := [{ name := mkId "result", type := ty .TInt }]
        preconditions := []
        decreases := none
        body := .Opaque [{ condition := md (.LiteralBool true) }]
          (some (md (.Assign [varMd (.Local (mkId "result"))] (md (.LiteralInt 3))))) [] }]
    staticFields := []
    types := []
    constants := [] }

private def reportTranslation (label : String) (valueType : HighType) : IO Unit := do
  let (core?, diagnostics) ← Laurel.translate default (frontEndTypeVarProgram valueType)
  IO.println s!"{label}: translated {core?.isSome}, diagnostics {diagnostics.length}"
  for d in diagnostics do
    IO.println s!"  {d.message}"

/-- The front end's shape: a bare `.TVar`. Resolution stamps it from the type-parameter
    scope, so the postcondition helper's `T` is determined and the program translates. -/
private def checkBareTypeVarResolves : IO Unit :=
  reportTranslation "bare TVar" (.TVar (mkId "T"))

/-- The parser's shape, for contrast: the same program written as a `.UserDefined` name,
    which the `.UserDefined` arm reclassifies and stamps. Pinned beside the case above so the
    pair witnesses that both producers of a type-parameter reference reach the same verdict. -/
private def checkUserDefinedTypeVarResolves : IO Unit :=
  reportTranslation "UserDefined name" (.UserDefined (mkId "T"))

/--
info: bare TVar: translated true, diagnostics 0
-/
#guard_msgs in
#eval checkBareTypeVarResolves

/--
info: UserDefined name: translated true, diagnostics 0
-/
#guard_msgs in
#eval checkUserDefinedTypeVarResolves

end Strata.Laurel

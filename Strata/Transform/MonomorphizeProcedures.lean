/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.StatementType
public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.Factory
import all Strata.DL.Imperative.Stmt

/-! # Monomorphize Procedures

The `MonomorphizeProcedures` program transformation monomorphizes every
polymorphic procedure so that no procedure's types mention type variables.

## Where it runs

This pass runs in `corePipelinePhases` immediately *before* `typeCheckPhase`
(and therefore after `CallElim` in `transformPipelinePhases`).  Two consequences
of this position matter:

* `CallElim` has already run, so no procedure body contains a `call` and each
  procedure can be monomorphized independently of the others.
* `typeCheckPhase` which runs after `MonomorphizeProcedures` clears `header.typeArgs`
  and instantiates the signature to fresh internal type variables such as
  `$__ty0`, so running before it lets each procedure still carry its declared
  type parameters in `header.typeArgs` under their original source names
  (e.g. `a`).

The subsequent `typeCheckPhase` then re-checks the now-monomorphic procedure
against its opaque-typed signature, propagating the opaque types through the
body.

## How it works

For each procedure whose `header.typeArgs` is `x₁, …, xₖ`:

1. A fresh, globally-unique *opaque type* is minted per type parameter, named
   `$__opaque_{procName}_{xᵢ}_N` (the `$__` prefix reserves the internal
   namespace so the name cannot collide with a user-declared type; the trailing
   `_N` is a fresh counter from the shared `CoreGenState`, guaranteeing
   uniqueness).  Each becomes a nullary top-level type declaration `type {name};`
   emitted immediately before the procedure.
2. A type substitution mapping each `xᵢ` to its opaque nullary type constructor
   is applied to the whole procedure: input/output signatures, precondition and
   postcondition expressions, and every expression *and local declaration type*
   in the body (`LExpr.applySubst` for expression annotations, `LMonoTy.subst`
   for signature and declaration types).
3. `header.typeArgs` is cleared, so the procedure is now monomorphic.

The statement-level substitution reuses the type checker's `Core.Statement.subst`
(`StatementType.lean`, which in turn uses `Command.subst` and `Lambda.LTy.subst`).
Only structured bodies are monomorphized: a CFG body is reported as an error.
-/

public section

namespace Core
namespace MonomorphizeProcedures

open Lambda Imperative
open Strata.Util (HMap)

/-! ### Applying the type substitution

The statement / command / declared-type substitution is the type checker's
existing `Core.Statement.subst` (which uses `Command.subst` and `Lambda.LTy.subst`,
in `StatementType.lean` / `LTyUnify.lean`).  Here we only assemble the
whole-procedure substitution on top of it. -/

open Core.Transform

/-- Apply `S` to a whole procedure: its signature, spec clauses, and body, and
    clear `header.typeArgs`.  Throws if the body is a CFG (unsupported).  The
    body substitution reuses `Statement.subst`. -/
def substProc (S : Subst) (proc : Procedure) : CoreTransformM Procedure := do
  let body ← match proc.body with
    | .structured ss => pure (Procedure.Body.structured (ss.map (Core.Statement.Statement.subst S)))
    | .cfg _ =>
      throw (Strata.Message.fromString
        "MonomorphizeProcedures: CFG procedure bodies are not supported")
  return { proc with
    header := { proc.header with
      typeArgs := [],
      inputs := proc.header.inputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)),
      outputs := proc.header.outputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)) },
    spec := { proc.spec with
      preconditions :=
        proc.spec.preconditions.map (fun (l, c) => (l, { c with expr := c.expr.applySubst S })),
      postconditions :=
        proc.spec.postconditions.map (fun (l, c) => (l, { c with expr := c.expr.applySubst S })) },
    body := body }

/-! ### The transformation -/

/-- Reserved prefix for generated opaque type names.  Uses the `$__` internal
    namespace (as `CallElim.freshTyVarPrefix := "$__cety"` does) so that a
    generated opaque type name can never collide with a user-declared type — the
    `CoreGenState` counter does not ingest existing source names, so without a
    reserved prefix a user `type P_a_opaque_type_0;` alongside `procedure P<a>`
    would clash. -/
private def opaqueTypePrefix : String := "$__opaque"

/-- Mint a fresh, globally-unique opaque type name for type variable `tyVar` of
    procedure `procName`.  The shared `CoreGenState` appends a fresh `_N`
    counter, e.g. `$__opaque_P_a_0`. -/
private def genOpaqueTypeName (procName tyVar : String) : CoreGenM CoreIdent :=
  CoreGenState.gen ⟨s!"{opaqueTypePrefix}_{procName}_{tyVar}", ()⟩

/-- Monomorphize a single procedure.  One fresh opaque type is minted per
    declared type parameter (`header.typeArgs`); the opaque type declarations are
    returned first, followed by the substituted procedure.  A procedure with no
    type parameters is returned unchanged. -/
def monomorphizeProc (proc : Procedure) (md : MetaData Expression) :
    CoreTransformM (List Decl) := do
  let tyVars := proc.header.typeArgs.dedup
  if tyVars.isEmpty then
    return [Decl.proc proc md]
  else
    let procName := proc.header.name.name
    let mut pairs : List (TyIdentifier × LMonoTy) := []
    let mut opaqueDecls : List Decl := []
    for tv in tyVars do
      let nm ← genOpaqueTypeName procName tv
      pairs := pairs ++ [(tv, LMonoTy.tcons nm.name [])]
      opaqueDecls := opaqueDecls ++ [Decl.type (.con { name := nm.name, params := [] }) .empty]
    let scope : SubstOne := HMap.ofList pairs
    let S : Subst := [scope]
    let proc' ← substProc S proc
    return opaqueDecls ++ [Decl.proc proc' md]

/-- Monomorphize every procedure in the program, introducing opaque types for
    the free type variables of each polymorphic procedure. -/
def run (p : Program) : CoreTransformM Program := do
  let out ← p.decls.foldlM (init := (#[] : Array Decl)) fun acc decl => do
    match decl with
    | .proc proc md =>
      if proc.header.typeArgs.isEmpty then
        -- Skip: nothing to substitute.  The structural guards (`.noCalls`,
        -- `.noCFGBodies`) protect the substitution step, which is only applied
        -- to polymorphic procedures; passing a non-polymorphic procedure through
        -- unchanged is always safe regardless of its body or call sites.
        pure (acc.push decl)
      else
        match proc.body with
        | .cfg _ =>
          throw (Strata.Message.fromFormat
            f!"❌ MonomorphizeProcedures: procedure {proc.header.name.name} has a CFG \
               body; monomorphization only handles structured bodies.")
        | .structured ss =>
          if !(Statements.noCalls ss) then
            throw (Strata.Message.fromFormat
              f!"❌ MonomorphizeProcedures: procedure {proc.header.name.name} still \
                 contains a call; eliminate calls before monomorphizing.")
          else
            let contrib ← monomorphizeProc proc md
            pure (acc ++ contrib.toArray)
    | _ => pure (acc.push decl)
  return { decls := out.toList }

end MonomorphizeProcedures

open Core.Transform in
/-- `CoreTransformM` runner for `MonomorphizeProcedures`, suitable for use with
    `Core.Transform.run`.  Reports whether any opaque type declaration was
    introduced (which happens iff some procedure was monomorphized). -/
def monomorphizeProcedures (p : Program) : CoreTransformM (Bool × Program) := do
  let p' ← MonomorphizeProcedures.run p
  return (p'.decls.length != p.decls.length, p')

/-- Pipeline phase for `MonomorphizeProcedures`.  Model-preserving: replacing an
    implicitly universally-quantified type variable with a fresh, arbitrary
    opaque type is universal generalization (∀-introduction), which preserves
    the proof obligation and introduces no spurious models. -/
def monomorphizeProceduresPipelinePhase : PipelinePhase :=
  -- Monomorphizing each procedure on its own is sound only once no body
  -- contains a call, which is why `noCalls` is required and not merely
  -- convenient.
  modelPreservingPipelinePhase "monomorphizeProcedures"
    (requires := factSet![.noCFGBodies, .noCalls])
    (establishes := factSet![.noPolymorphicProcedures])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                         .noInternalFuncDecl, .noPolymorphicFunctions])
    fun prog =>
      monomorphizeProcedures prog

end Core

end -- public section

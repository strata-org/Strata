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
public import Strata.DL.Lambda.LExprType
public import Strata.DL.Lambda.NamePrefixes
public import Strata.Languages.Core.NameMangling
import all Strata.DL.Imperative.Stmt
public import Strata.Util.Name

/-! # Generalize Type Parameters to Opaque Types

The `GenOpaqueTypeParams` program transformation replaces each type parameter
of a polymorphic procedure by a fresh opaque type, so that no procedure's types
mention type variables. It treats polymorphic lemmas the same way: a lemma's
type parameters are replaced by fresh opaque types in its formula.

This is universal generalization, not monomorphization: a type parameter is
not instantiated at the types it is used at (as `MonomorphizeFunctions` does
for functions) but replaced by one arbitrary type, so proving the result proves
the original at every instantiation.

## Where it runs

This pass runs in `corePipelinePhases` immediately *before* `typeCheckPhase`
(and therefore after `CallElim` in `transformPipelinePhases`).  Two consequences
of this position matter:

* `CallElim` has already run, so no procedure body contains a `call` and each
  procedure can be processed independently of the others.
* `typeCheckPhase` which runs after `GenOpaqueTypeParams` clears `header.typeArgs`
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
   `$__opaque_{procName}_{xᵢ}_N`, where `_N` is a fresh counter from the shared
   `CoreGenState`, skipping any name the program already declares as a type, so
   it never collides with one.  Each becomes a nullary top-level type declaration `type {name};`
   emitted immediately before the procedure.
2. A type substitution mapping each `xᵢ` to its opaque nullary type constructor
   is applied to the whole procedure: input/output signatures, precondition and
   postcondition expressions, and every expression *and local declaration type*
   in the body (`LExpr.applyTypeSubst` for expression annotations, `LMonoTy.subst`
   for signature and declaration types).
3. `header.typeArgs` is cleared, so the procedure is now monomorphic.

The statement-level substitution reuses the type checker's `Core.Statement.subst`
(`StatementType.lean`, which in turn uses `Command.subst` and `Lambda.LTy.subst`).
Only structured bodies are supported: a CFG body is reported as an error.
-/

public section

namespace Core
namespace GenOpaqueTypeParams

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
        "GenOpaqueTypeParams: CFG procedure bodies are not supported")
  return { proc with
    header := { proc.header with
      typeArgs := [],
      inputs := proc.header.inputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)),
      outputs := proc.header.outputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)) },
    spec := { proc.spec with
      preconditions :=
        proc.spec.preconditions.map (fun (l, c) => (l, { c with expr := c.expr.applyTypeSubst S })),
      postconditions :=
        proc.spec.postconditions.map (fun (l, c) => (l, { c with expr := c.expr.applyTypeSubst S })) },
    body := body }

/-! ### The transformation -/

/-- Prefix for generated opaque type names, in the `$__` internal namespace as
    `Lambda.callElimTyPrefix := "$__cety"` is, so that generated names stand out.
    It does not make them fresh: `genOpaqueTypeName` skips the names the
    program declares with it. -/
private def opaqueTypePrefix : String := "$__opaque"

/-- Mint a fresh, globally-unique opaque type name for type variable `tyVar` of
    procedure `procName`, differing from every name in `taken` (the program's
    type names that start with `opaqueTypePrefix`).  The shared `CoreGenState`
    appends a fresh `_N` counter, e.g. `$__opaque_P_a_0`. -/
private def genOpaqueTypeName (taken : Std.HashSet String) (procName tyVar : String) :
    CoreGenM CoreIdent :=
  CoreGenState.genAvoiding taken ⟨s!"{opaqueTypePrefix}_{procName}_{tyVar}", ()⟩

/-- One nullary opaque type declaration per pair `(tv, n)` of `names`, named
    `n`, and the substitution mapping each type variable `tv` to its opaque
    type. -/
def opaqueTypes (names : List (TyIdentifier × String)) : List Decl × Subst :=
  (names.map fun (_, n) => Decl.type (.con { name := n, params := [] }) .empty,
   [HMap.ofList (names.map fun (tv, n) => (tv, LMonoTy.tcons n []))])

/-- Reject the first of `names` containing `Core.NameMangling.monoDelim`, naming it. The
    names opaque types are built from are checked here, so the error names what the user
    wrote, not the generated type. This is the early half of
    `MonomorphizeFunctions.namesUnmangled`, which rejects the generated name later. -/
def checkNoMonoDelim {m : Type → Type} [Monad m] [MonadExcept Strata.Message m]
    (names : List String) : m Unit := do
  if let some bad := names.find? Core.NameMangling.hasMonoDelim then
    throw (Strata.Message.fromString
      s!"GenOpaqueTypeParams: the name '{bad}' contains '{Core.NameMangling.monoDelim}', \
         which is reserved for monomorphized copies")

/-- Mint one fresh opaque type per type variable of the declaration `name`,
    avoiding the type names in `taken`.
    Returns the opaque type declarations and the substitution mapping each type
    variable to its opaque type.

    Rejects a `name` or type variable containing `Core.NameMangling.monoDelim`. The
    opaque type's name is built from both, and `MonomorphizeFunctions` rejects any
    type name containing the delimiter. Rejecting here reports the name the user
    wrote, not the generated one. -/
def mkOpaqueSubst (taken : Std.HashSet String) (name : String) (tyVars : List TyIdentifier) :
    CoreTransformM (List Decl × Subst) := do
  checkNoMonoDelim (name :: tyVars)
  let names ← tyVars.mapM fun tv => return (tv, (← genOpaqueTypeName taken name tv).name)
  return opaqueTypes names

/-- Replace the type parameters of a single procedure by opaque types.  One fresh opaque type is minted per
    declared type parameter (`header.typeArgs`); the opaque type declarations are
    returned first, followed by the substituted procedure.  A procedure with no
    type parameters is returned unchanged. -/
def genOpaqueProc (taken : Std.HashSet String) (proc : Procedure) (md : MetaData Expression) :
    CoreTransformM (List Decl) := do
  let tyVars := proc.header.typeArgs.uniq
  if tyVars.isEmpty then
    return [Decl.proc proc md]
  else
    let (opaqueDecls, S) ← mkOpaqueSubst taken proc.header.name.name tyVars
    let proc' ← substProc S proc
    return opaqueDecls ++ [Decl.proc proc' md]

/-- Replace the type parameters of a lemma by opaque types: a lemma holds at every instantiation of its type
    parameters, so it is checked at fresh opaque types, as a procedure is. -/
def genOpaqueLemma (taken : Std.HashSet String) (l : Lemma) (md : MetaData Expression) :
    CoreTransformM (List Decl) := do
  let tyVars := l.typeArgs.uniq
  if tyVars.isEmpty then
    return [Decl.lemma l md]
  else
    let (opaqueDecls, S) ← mkOpaqueSubst taken l.name tyVars
    return opaqueDecls ++ [Decl.lemma { l with typeArgs := [], e := l.e.applyTypeSubst S } md]

/-- Introduce opaque types for the type parameters of every polymorphic
    procedure and lemma in the program. -/
def run (p : Program) : CoreTransformM Program := do
  -- Only a declared type with the opaque prefix can equal a generated name; for
  -- most programs there is none, and nothing is hashed or retried.
  let taken := Std.HashSet.ofList (p.typeNames.filter (·.startsWith opaqueTypePrefix))
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
            f!"❌ GenOpaqueTypeParams: procedure {proc.header.name.name} has a CFG \
               body; only structured bodies are supported.")
        | .structured ss =>
          if !(Statements.noCalls ss) then
            throw (Strata.Message.fromFormat
              f!"❌ GenOpaqueTypeParams: procedure {proc.header.name.name} still \
                 contains a call; eliminate calls before running this pass.")
          else
            let contrib ← genOpaqueProc taken proc md
            pure (acc ++ contrib.toArray)
    | .lemma l md => do
      let contrib ← genOpaqueLemma taken l md
      pure (acc ++ contrib.toArray)
    | _ => pure (acc.push decl)
  return { decls := out.toList }

/-- Replace every type variable that a type-checked lemma still has by a fresh
    opaque type, declared just before it, and drop the lemma's type parameters.
    This covers the type variables that type checking introduces for the
    lemma's declared type parameters, and those that nothing in its formula
    fixes, such as the element type of `Nil()` in `adtRank(Nil())`, which the
    SMT encoder would otherwise reject. Unlike `genOpaqueLemma`, which runs
    before type checking, this closes the type variables of the formula's
    annotations, not the lemma's declared type parameters.

    TODO: prove what this relies on: if the closed lemma holds, the original
    lemma holds at every instantiation of its type variables, since nothing
    constrains an opaque type. This is the argument by which
    `genOpaqueTypeParams` is model-preserving. -/
def closeLemmaTypeVars (p : Program) : Program :=
  -- Only a declared type with the free-type prefix can clash with a generated
  -- name. The base names `{lemma}_{i}` of different lemmas differ, since lemma
  -- names are distinct and the index after the last `_` has no `_`. So when no
  -- declared type has the prefix, the base names are used as they are.
  let taken := Std.HashSet.ofList (p.typeNames.filter (·.startsWith freeTyPrefix))
  let close (taken : Std.HashSet String) (l : Lemma) (md : MetaData Expression) :
      List Decl × Std.HashSet String :=
    match (annotTyVars l.e).eraseDups with
    | [] => ([.lemma l md], taken)
    | tvs =>
      let bases := tvs.mapIdx fun i _ => s!"{freeTyPrefix}{l.name}_{i}"
      -- Skip the names the program declares, so none of them is captured.
      let (names, taken) :=
        if taken.isEmpty then (bases, taken) else Strata.Name.freshNames taken bases
      let (decls, S) := opaqueTypes (tvs.zip names)
      (decls ++ [.lemma { l with typeArgs := [], e := l.e.applyTypeSubst S } md], taken)
  let (decls, _) := p.decls.foldl (init := (#[], taken)) fun (acc, taken) d =>
    match d with
    | .lemma l md =>
      let (ds, taken) := close taken l md
      (acc ++ ds.toArray, taken)
    | d => (acc.push d, taken)
  { p with decls := decls.toList }

/-- Reject a lemma that `closeLemmaTypeVars` would build an opaque type name from (one
    whose formula's annotations have type variables) when its name contains
    `Core.NameMangling.monoDelim`, naming the lemma: `MonomorphizeFunctions` would reject
    the generated `$__free_L#1_0` anyway. A lemma it closes nothing in keeps its name. -/
def checkClosedLemmaNames (p : Program) : Except Strata.Message Unit :=
  checkNoMonoDelim (p.decls.filterMap fun
    -- Test the name first: almost no lemma name has the delimiter, so the formula is
    -- rarely walked a second time.
    | .lemma l _ =>
      if Core.NameMangling.hasMonoDelim l.name && !(annotTyVars l.e).isEmpty then some l.name
      else none
    | _ => none)

end GenOpaqueTypeParams

open Core.Transform in
/-- `CoreTransformM` runner for `GenOpaqueTypeParams`, suitable for use with
    `Core.Transform.run`.  Reports whether any opaque type declaration was
    introduced (which happens iff some procedure or lemma had type parameters). -/
def genOpaqueTypeParams (p : Program) : CoreTransformM (Bool × Program) := do
  let p' ← GenOpaqueTypeParams.run p
  return (p'.decls.length != p.decls.length, p')

/-- Pipeline phase for `GenOpaqueTypeParams`.  Model-preserving: replacing an
    implicitly universally-quantified type variable with a fresh, arbitrary
    opaque type is universal generalization (∀-introduction), which preserves
    the proof obligation and introduces no spurious models. -/
def genOpaqueTypeParamsPipelinePhase : PipelinePhase :=
  -- Processing each procedure on its own is sound only once no body
  -- contains a call, which is why `noCalls` is required and not merely
  -- convenient.
  modelPreservingPipelinePhase "genOpaqueTypeParams"
    (requires := factSet![.noCFGBodies, .noCalls])
    (establishes := factSet![.noPolymorphicProcedures])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                         .noProcedureContracts,
                         .noPolymorphicFunctions, .typeAnnotated, .noInits])
    fun prog =>
      genOpaqueTypeParams prog

end Core

end -- public section

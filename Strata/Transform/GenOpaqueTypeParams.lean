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

This pass runs in `corePipelinePhases` after `typeCheckPipelinePhase` and `CallElim`.
Two consequences of this position matter:

* `CallElim` has already run, so no procedure body contains a `call` and each
  procedure can be processed independently of the others.
* Type checking keeps each procedure's `header.typeArgs` under their source names
  (e.g. `a`), so the substitution rewrites them directly to the opaque types.

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
   in the body, structured or CFG (`LExpr.applyTypeSubst` for expression
   annotations and branch guards, `LMonoTy.subst` for signature and declaration
   types).
3. `header.typeArgs` is cleared, so the procedure is now monomorphic.

The statement-level substitution reuses the type checker's `Core.Statement.subst`
(`StatementType.lean`, which in turn uses `Command.subst` and `Lambda.LTy.subst`); a CFG
body is substituted block by block with `Statement.DetBlock.subst`, the substitution the CFG
type checker applies to its blocks.
-/

public section

namespace Core
namespace GenOpaqueTypeParams

open Lambda Imperative
open Strata.Util (HMap)

/-- Prefix of the opaque types that replace a type-checked lemma's remaining type
    variables.
    Kept as a literal copy in `Lambda.reservedNamePrefixes`, so type checking still
    rejects or renames program names that use it. -/
@[expose] def freeTyPrefix : String := "$__free_"

/-! ### Applying the type substitution

The statement / command / declared-type substitution is the type checker's
existing `Core.Statement.subst` (which uses `Command.subst` and `Lambda.LTy.subst`,
in `StatementType.lean` / `LTyUnify.lean`).  Here we only assemble the
whole-procedure substitution on top of it. -/

open Core.Transform

/-- Apply `S` to a whole procedure: its signature, spec clauses, and body, and
    clear `header.typeArgs`.  The body substitution reuses `Statement.subst` for a
    structured body and `Statement.DetBlock.subst` for each block of a CFG body. -/
def substProc (S : Subst) (proc : Procedure) : Procedure :=
  let body := match proc.body with
    | .structured ss => Procedure.Body.structured (ss.map (Core.Statement.Statement.subst S))
    | .cfg g =>
      Procedure.Body.cfg
        { g with blocks := g.blocks.map fun (l, b) => (l, Core.Statement.DetBlock.subst S b) }
  { proc with
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
    `Core.CallElim.callElimTyPrefix := "$__cety"` is, so that generated names stand out.
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
  (names.map fun p => Decl.opaqueType p.2, Subst.ofNullaryConsts names)

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
    let proc' := substProc S proc
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
    procedure and lemma in the program, avoiding the type names in `taken`: the
    program's type names with the opaque prefix. -/
def runAvoiding (taken : Std.HashSet String) (p : Program) :
    CoreTransformM Program := do
  let out ← p.decls.foldlM (init := (#[] : Array Decl)) fun acc decl => do
    match decl with
    | .proc proc md =>
      if proc.header.typeArgs.isEmpty then
        -- Skip: nothing to substitute.  The no-call check below protects the
        -- substitution step, which is only applied to polymorphic procedures;
        -- passing a non-polymorphic procedure through unchanged is always safe
        -- regardless of its body or call sites.
        pure (acc.push decl)
      else if !(proc.body.allStatements Statements.noCalls) then
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

/-- `runAvoiding` with the program's own `$__opaque`-prefixed type names. -/
def run (p : Program) : CoreTransformM Program :=
  -- Only a declared type with the opaque prefix can equal a generated name; for
  -- most programs there is none, and nothing is hashed or retried.
  runAvoiding (p.typeNamesWithPrefix opaqueTypePrefix) p

/-- Replace every type variable that a lemma still has by a fresh
    opaque type, declared just before it, and drop the lemma's type parameters.
    The fresh names avoid the type names in `taken`: the program's type names
    with the free-type prefix.
    This covers a type variable that is neither a type parameter of the lemma
    nor fixed by its formula, such as a type left open in a termination lemma
    built without a type check, which the SMT encoder would otherwise reject.
    It runs after `genOpaqueLemma`, which replaces the lemma's declared type
    parameters, and closes the type variables left in the formula's
    annotations.

    TODO: prove what this relies on: if the closed lemma holds, the original
    lemma holds at every instantiation of its type variables, since nothing
    constrains an opaque type. This is the argument by which
    `genOpaqueTypeParams` is model-preserving. -/
def closeLemmaTypeVarsAvoiding (taken : Std.HashSet String) (p : Program) :
    Program :=
  -- Only a declared type with the free-type prefix can clash with a generated
  -- name. The base names `{lemma}_{i}` of different lemmas differ, since lemma
  -- names are distinct and the index after the last `_` has no `_`. So when no
  -- declared type has the prefix, the base names are used as they are.
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

/-- Reject a lemma that `closeLemmaTypeVarsAvoiding` would build an opaque type name from (one
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
    introduced, which happens iff some procedure or lemma had type parameters or a
    lemma had a type variable left in its annotations. -/
def genOpaqueTypeParams (p : Program) : CoreTransformM (Bool × Program) := do
  -- `runAvoiding` declares only opaque-prefixed types, so the free-prefixed
  -- type names of its output are those of `p`.
  let names := p.typeNames
  let withOpaque ← GenOpaqueTypeParams.runAvoiding
    (namesWithPrefix names GenOpaqueTypeParams.opaqueTypePrefix) p
  let p' := GenOpaqueTypeParams.closeLemmaTypeVarsAvoiding
    (namesWithPrefix names GenOpaqueTypeParams.freeTyPrefix) withOpaque
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
    (requires := factSet![.noCalls, .typeAnnotated])
    (establishes := factSet![.noPolymorphicProcedures])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment,
                         .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                         .noProcedureContracts,
                         .noPolymorphicFunctions, .typeAnnotated, .noInits, .exitsCovered])
    fun prog =>
      genOpaqueTypeParams prog

end Core

end -- public section

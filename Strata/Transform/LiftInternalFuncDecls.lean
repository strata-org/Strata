/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Imperative.Stmt

/-! # Lift Internal Function Declarations

This transformation hoists every local function declaration (`Stmt.funcDecl`)
found inside a procedure body up to a top-level `Decl.func` in the
`Core.Program`.

## Motivation

A `funcDecl` statement's body may legitimately reference variables from the
surrounding lexical context, so its raw function is *not* closed
(see `Lambda.LFuncClosed`).  The evaluator copes with this by capturing the
values of those variables at `funcDecl`-evaluation time
(`Core.captureFreevars` / `Statement.evalAux`).  This pass performs that capture
*statically*, turning each internal function into a closed top-level function so
that `Lambda.LFuncClosed` holds for every function in the program.

Once this pass has run, every procedure body satisfies `Block.noFuncDecl`, and
every function in the program is closed.  This lets downstream transform
correctness proofs assume `Stmt.noFuncDecl` inputs and a fixed `Factory` that
is never extended mid-evaluation.

## How it works (lambda lifting with declaration-site value capture)

For each internal function `f` with captured variables `c₁, …, cₖ` (free
variables referenced in the body / axioms / preconditions but not bound by
`f`'s own formals, with types read off the `fvar` annotations left by type
inference):

1. At the original declaration site, a fresh snapshot variable is introduced
   per captured variable — `var $__liftfncl_i := cᵢ` — freezing `cᵢ`'s value at
   exactly the program point where the `funcDecl` used to be.  The `funcDecl`
   statement itself is replaced by these snapshot `init`s.
2. Inside `f`, each `cᵢ` is renamed to its snapshot variable `$__liftfncl_i`,
   which becomes a *leading* parameter of `f`.  Any type variables occurring in
   the captured types are added to `f`'s `typeArgs` (a captured `x : V` from an
   enclosing `procedure p<V>` contributes `V`).
3. Every reference to `f` is rewritten by substituting the operator `op f` with
   `op f` applied to the snapshot arguments (`Lambda.LExpr.substOps`), so a call
   `f(a₁, …, aₙ)` becomes `f($__liftfncl_1, …, $__liftfncl_k, a₁, …, aₙ)`.
   Because the captured arguments lead, this is a purely local rewrite at the
   `.op` node; the operator is re-annotated with the lifted function's
   instantiated arrow type — the captured parameter types prepended onto the
   original call-site annotation — so the rewritten program stays
   well-type-annotated (no reliance on a subsequent type-check to recover it).
4. `f` is emitted as a closed top-level `Decl.func`, placed immediately before
   its enclosing procedure.

Every hoisted function is given a fresh top-level name under the `$__liftfncl`
prefix. As other passes in Strata like InsertLoopInvariantAsserts do, it is
assumed that the input Core program doesn't have any identifier starting with
this prefix. This isn't being enforced by Core verifier yet, so in theory
the user can write a program that has these prefixes, and a way of enforcing
absence of these is necessary in the future.

## Semantics

Because the captured values are snapshotted at the declaration site (not read
at the call site), this pass faithfully models the evaluator's
`captureFreevars` semantics even when a captured variable is reassigned between
the `funcDecl` and the calls that reach it: the snapshot preserves the
declaration-time value.  Fresh snapshot variables use the `$__liftfncl` prefix,
generated through `CoreTransformState`'s string generator so they never clash
with user or previously generated names.
-/

public section

namespace Core
namespace LiftInternalFuncDecls

open Lambda Imperative
open Std (Format format)
open Strata.Util (HMap)

/-- The operator-substitution map used to rewrite call sites: each lifted
    function's original name maps to a *builder* that, given the original
    reference's type annotation, produces the replacement for `.op name`.
    For a captured function this is `op newName` applied to its (leading)
    snapshot arguments; for a pure rename it is just `op newName`.  The builder
    also re-annotates the operator with the lifted function's instantiated arrow
    type — the captured (leading) parameter types prepended onto the original
    annotation — so the rewritten call site stays fully type-annotated. -/
private abbrev OpSubst := HMap CoreIdent (Option LMonoTy → Expression.Expr)

/-- Apply the closure-conversion substitutions to a `funcDecl`'s definition
    (body, axioms, precondition expressions, and the termination measure):
    - `fvarSubst` renames each captured variable `c` to its fresh snapshot
      parameter (`Lambda.LExpr.substFvars`);
    - `opSubst` rewrites references to sibling / recursive lifted functions so
      the captured arguments are supplied (`Lambda.LExpr.substOps`). -/
private def rewritePureFunc (fvarSubst : Map CoreIdent Expression.Expr) (opSubst : OpSubst)
    (d : PureFunc Expression) : PureFunc Expression :=
  let go (e : Expression.Expr) : Expression.Expr :=
    (e.substFvars fvarSubst).substOps opSubst
  { d with
    body := d.body.map go,
    axioms := d.axioms.map go,
    preconditions := d.preconditions.map (fun p => { p with expr := go p.expr }),
    measure := d.measure.map go }

/-- Compute the free variables captured by a `funcDecl` (referenced in the body,
    axioms, preconditions, or termination measure, but not a formal parameter),
    paired with their types read from the `fvar` annotations.  Fails if a
    captured variable has an unannotated or inconsistently-annotated
    occurrence.  Not `private`: `LiftInternalFuncDeclsCorrect` case-splits on it. -/
def capturedVars (decl : PureFunc Expression) :
    Except Format (List (CoreIdent × LMonoTy)) := do
  let formals : Std.HashSet CoreIdent := Std.HashSet.ofList (decl.inputs.map (·.1))
  let bodyFvs := (decl.body.map Lambda.LExpr.freeVars).getD []
  let axFvs := decl.axioms.flatMap Lambda.LExpr.freeVars
  let precFvs := decl.preconditions.flatMap (fun p => Lambda.LExpr.freeVars p.expr)
  let mesFvs := (decl.measure.map Lambda.LExpr.freeVars).getD []
  let nonFormal := (bodyFvs ++ axFvs ++ precFvs ++ mesFvs).filter (fun (id, _) => !formals.contains id)
  let names := (nonFormal.map (·.1)).dedup
  names.mapM fun id => do
    -- Every occurrence of a captured variable must carry the same, non-`none`
    -- type annotation.  (Type inference guarantees this for surface programs;
    -- the check hardens the pass against direct-AST callers.)
    let occurrences := nonFormal.filter (fun (i, _) => i == id)
    if occurrences.any (fun (_, t) => t.isNone) then
      throw f!"LiftInternalFuncDecls: captured variable '{id.name}' has an \
               unannotated occurrence in function '{decl.name.name}'"
    match occurrences.filterMap (·.2) with
    | mty :: rest =>
      if rest.all (fun t => decide (t = mty)) then pure (id, mty)
      else
        throw f!"LiftInternalFuncDecls: captured variable '{id.name}' has \
                 inconsistent type annotations in function '{decl.name.name}'"
    | [] =>
      -- Unreachable: `id` came from `nonFormal`, so it has ≥ 1 occurrence, and
      -- the `isNone` check above rules out unannotated ones.
      throw f!"LiftInternalFuncDecls: cannot determine the type of captured \
               variable '{id.name}' in function '{decl.name.name}'"

/-- Build the closed top-level `Function` for a lifted `funcDecl` by prepending
    the captured (snapshot) variables as leading inputs (and their type
    variables as extra `typeArgs`).  Body/axioms/preconditions are copied
    verbatim (they have already been renamed and call-rewritten by
    `rewritePureFunc`).  The captured parameters lead so that a call site can be
    rewritten purely at the `.op` node — `op f` becomes `op f` applied to the
    captured arguments, and the original arguments follow. -/
private def toFunction (d : PureFunc Expression) (newName : CoreIdent)
    (extraInputs : List (CoreIdent × LMonoTy)) (extraTypeArgs : List TyIdentifier) :
    Function :=
  { name := newName,
    typeArgs := d.typeArgs ++ extraTypeArgs,
    isConstr := d.isConstr,
    isRecursive := d.isRecursive,
    inputs := extraInputs ++ d.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty)),
    output := Lambda.LTy.toMonoTypeUnsafe d.output,
    body := d.body,
    attr := d.attr,
    axioms := d.axioms,
    preconditions := d.preconditions,
    measure := d.measure }

open Core.Transform

/-- Prefix used for the fresh variables that snapshot captured values at the
    original declaration site, and for lifted top-level function names. -/
private def liftPrefix : String := "$__liftfncl"

/-- Generate a fresh snapshot-variable identifier under `liftPrefix`. -/
private def genLiftVar : CoreGenM CoreIdent := CoreGenState.gen ⟨liftPrefix, ()⟩

/-- Generate a fresh top-level name for a lifted function, under `liftPrefix`. -/
private def genLiftFuncName (base : CoreIdent) : CoreGenM CoreIdent :=
  CoreGenState.gen ⟨s!"{liftPrefix}_{base.name}", ()⟩

/-- One local function scheduled for hoisting. -/
structure LiftingFunc where
  /-- The original local function declaration. -/
  decl : PureFunc Expression
  /-- Its captured variables, as `(originalVar, snapshotVar, type)` triples:
      `originalVar` is snapshotted into the fresh `snapshotVar` at the
      declaration site, and `snapshotVar : type` becomes a leading parameter. -/
  captured : List (CoreIdent × CoreIdent × LMonoTy)

/- Recursively walk a statement, replacing each `funcDecl` with a sequence of
   snapshot `init`s (one fresh `$__liftfncl` variable per captured variable,
   initialized to the captured value at this program point) and recording a
   `LiftingFunc` for the hoist.  Recurses into `block`/`ite`/`loop` bodies. -/
mutual
def collectLiftingFuncsFromStmt (s : Statement) :
    CoreTransformM (List LiftingFunc × List Statement) := do
  match s with
  | .funcDecl decl _ =>
    let cvs ← match capturedVars decl with
      | .ok c => pure c
      | .error e => throw (Strata.Message.fromFormat e)
    let captured ← cvs.mapM fun (id, mty) => do
      let f ← genLiftVar
      pure (id, f, mty)
    -- Snapshot the captured value at the declaration site: `var f := c`.
    let snapshots : List Statement := captured.map fun (id, f, mty) =>
      Statement.init f (Lambda.LTy.forAll [] mty) (.det (.fvar () id (some mty))) .empty
    pure ([{ decl := decl, captured := captured }], snapshots)
  | .block l b md =>
    let (lfs, b') ← collectLiftingFuncsFromBlock b
    pure (lfs, [.block l b' md])
  | .ite c t e md =>
    let (lt, t') ← collectLiftingFuncsFromBlock t
    let (le, e') ← collectLiftingFuncsFromBlock e
    pure (lt ++ le, [.ite c t' e' md])
  | .loop g mea inv b md =>
    let (lfs, b') ← collectLiftingFuncsFromBlock b
    pure (lfs, [.loop g mea inv b' md])
  | .cmd c => pure ([], [.cmd c])
  | .exit l md => pure ([], [.exit l md])
  | .typeDecl tc md => pure ([], [.typeDecl tc md])
  termination_by Imperative.Stmt.sizeOf s

def collectLiftingFuncsFromBlock (ss : List Statement) :
    CoreTransformM (List LiftingFunc × List Statement) := do
  match ss with
  | [] => pure ([], [])
  | s :: rest =>
    let (l1, s1) ← collectLiftingFuncsFromStmt s
    let (l2, r1) ← collectLiftingFuncsFromBlock rest
    pure (l1 ++ l2, s1 ++ r1)
  termination_by Imperative.Block.sizeOf ss
end

/-- Pure phase of `hoistProcedure`: given the results of the two stateful
    phases (fresh top-level names `named` and the transitively-extended capture
    map `extMap`), produce the array of output decls.  The array is
    `funcDecls.push (Decl.proc ⟨proc with body := newBody⟩ md)`, where
    `funcDecls : Array Decl` is a `map` producing only `.func` values, and
    `newBody` is `.structured (Statements.mapExprs _ ss)` if the input body was
    `.structured ss` (or the input body unchanged for CFG bodies). -/
def buildLiftedDecls (proc : Procedure) (md : MetaData Expression)
    (named : Array (LiftingFunc × CoreIdent))
    (extMap : Std.HashMap String (List (CoreIdent × CoreIdent × LMonoTy))) :
    Array Decl :=
  let opSubstList : OpSubst := HMap.ofList <| named.toList.map fun (lf, newName) =>
    let extCap := extMap.getD lf.decl.name.name []
    let capturedArgs : List Expression.Expr := extCap.map fun (_, f, mty) => .fvar () f (some mty)
    let capMtys : List LMonoTy := extCap.map fun (_, _, mty) => mty
    (lf.decl.name, fun oldTy =>
      LExpr.mkApp () (.op () newName (oldTy.map (LMonoTy.mkArrow' · capMtys))) capturedArgs)
  let funcDecls : Array Decl := named.map fun (lf, newName) =>
    let extCap := extMap.getD lf.decl.name.name []
    let fvarSubst : Map CoreIdent Expression.Expr :=
      lf.captured.map fun (id, f, mty) => (id, .fvar () f (some mty))
    let rewritten := rewritePureFunc fvarSubst opSubstList lf.decl
    let extraInputs := extCap.map fun (_, f, mty) => (f, mty)
    let ownTyVars :=
      lf.decl.inputs.flatMap (fun (_, ty) => (Lambda.LTy.toMonoTypeUnsafe ty).freeVars)
        ++ (Lambda.LTy.toMonoTypeUnsafe lf.decl.output).freeVars
    let extraTypeArgs :=
      ((extCap.flatMap (fun (_, _, mty) => mty.freeVars)) ++ ownTyVars).dedup.filter
        (fun tv => tv ∉ lf.decl.typeArgs)
    let f := toFunction rewritten newName extraInputs extraTypeArgs
    Decl.func f .empty
  let newBody := match proc.body with
    | .structured ss => .structured (Statements.mapExprs (fun e => e.substOps opSubstList) ss)
    | .cfg _ => proc.body
  funcDecls.push (Decl.proc { proc with body := newBody } md)

/-- Hoist the local functions collected from a single procedure body.  Emits one
    closed top-level `Decl.func` per `LiftingFunc` (their declaration-site
    snapshots are already spliced into `stripped`), followed by the procedure
    whose body has had its call sites rewritten. -/
private def hoistProcedure (proc : Procedure) (md : MetaData Expression)
    (lfs : List LiftingFunc) :
    CoreTransformM (Array Decl) := do
  -- Phase 1: mint a fresh `$__liftfncl`-prefixed top-level name per function
  -- (collision-proof against user names) through the shared generator.
  let mut named : Array (LiftingFunc × CoreIdent) := #[]
  for lf in lfs do
    let newName ← genLiftFuncName lf.decl.name
    named := named.push (lf, newName)

  -- Phase 2: transitively extend each function's captured set over the sibling
  -- call graph.  When a function `f` calls a capturing sibling `g`, `substOps`
  -- (Phase 4) injects `g`'s snapshot variables into `f`'s body; those variables
  -- must also be parameters of `f`, or `f` would be left open.  So
  --   extCaptured(f) = own(f) ∪ ⋃ { extCaptured(g) | g a sibling called by f }
  -- computed as a least fixpoint (reusing `g`'s snapshot variables).
  let siblingNames : Std.HashSet String := Std.HashSet.ofList (lfs.map (·.decl.name.name))
  let calledSiblings (d : PureFunc Expression) : List String :=
    let ops := (d.body.map Lambda.LExpr.getOps).getD []
      ++ d.axioms.flatMap Lambda.LExpr.getOps
      ++ d.preconditions.flatMap (fun p => Lambda.LExpr.getOps p.expr)
      ++ (d.measure.map Lambda.LExpr.getOps).getD []
    ((ops.map (·.name)).filter siblingNames.contains).dedup
  let dedupBySnapshot (cs : List (CoreIdent × CoreIdent × LMonoTy)) :
      List (CoreIdent × CoreIdent × LMonoTy) :=
    let (out, _) := cs.foldl
      (fun (acc : Array (CoreIdent × CoreIdent × LMonoTy) × Std.HashSet String) c =>
        let key := c.2.1.name
        if acc.2.contains key then acc else (acc.1.push c, acc.2.insert key))
      (#[], Std.HashSet.emptyWithCapacity)
    out.toList
  let callsMap : Std.HashMap String (List String) :=
    Std.HashMap.ofList (lfs.map fun lf => (lf.decl.name.name, calledSiblings lf.decl))
  let mut extMap : Std.HashMap String (List (CoreIdent × CoreIdent × LMonoTy)) :=
    Std.HashMap.ofList (lfs.map fun lf => (lf.decl.name.name, lf.captured))
  for _ in [0 : lfs.length] do
    extMap := Std.HashMap.ofList <| lfs.map fun lf =>
      let nm := lf.decl.name.name
      let cur := extMap.getD nm []
      let inherited := (callsMap.getD nm []).flatMap (fun g => extMap.getD g [])
      (nm, dedupBySnapshot (cur ++ inherited))

  -- Phases 3: build the operator-substitution map, the closed top-level
  -- function declarations, and rewrite the procedure's (stripped) body.
  -- Delegated to the pure `buildLiftedDecls` so the state-monadic wrapper
  -- above and the pure result construction can be reasoned about separately.
  return buildLiftedDecls proc md named extMap

/-- Process a single top-level declaration: for a `.proc` with a structured body
    that contains internal `funcDecl`s, strip and hoist them; otherwise, pass
    through unchanged.  Returns the list of decls contributed to the output
    program (typically a single decl, but a hoisted procedure contributes its
    lifted `.func` decls plus the rewritten procedure). -/
def processDecl (topLevelFuncNames : Std.HashSet String) (decl : Decl) :
    CoreTransformM (List Decl) := do
  match decl with
  | .proc proc md =>
    match proc.body with
    | .cfg _ =>
      -- CFG bodies cannot contain `funcDecl` (a structured-only construct).
      pure [decl]
    | .structured ss =>
      let (lfs, stripped) ← collectLiftingFuncsFromBlock ss
      if lfs.isEmpty then
        pure [decl]
      else
        -- Reject recursive internal function declarations.
        let recNames := ((lfs.filter (·.decl.isRecursive)).map (·.decl.name.name)).dedup
        if !recNames.isEmpty then
          let names := String.intercalate ", " (recNames.map (fun n => s!"'{n}'"))
          throw <| Strata.Message.fromFormat
            f!"LiftInternalFuncDecls: procedure '{proc.header.name.name}' declares \
               recursive internal function(s) {names}; recursive internal function \
               declarations are not supported"
        -- Reject clashing internal function names within this procedure.
        -- The error message below will help the frontend generating internal
        -- function declarations with identical name rename them to have
        -- unique names.
        let allNames := lfs.map (·.decl.name.name)
        let dupNames := (allNames.filter (fun n => allNames.count n > 1)).dedup
        if !dupNames.isEmpty then
          let names := String.intercalate ", " (dupNames.map (fun n => s!"'{n}'"))
          throw <| Strata.Message.fromFormat
            f!"LiftInternalFuncDecls: procedure '{proc.header.name.name}' declares \
               multiple internal functions with the clashing name(s) {names}; \
               internal function declarations must have distinct names"
        -- Reject internal function names that clash with a top-level `Decl.func` as well.
        let clashesWithTopLevel :=
          (allNames.filter topLevelFuncNames.contains).dedup
        if !clashesWithTopLevel.isEmpty then
          let names := String.intercalate ", " (clashesWithTopLevel.map (fun n => s!"'{n}'"))
          throw <| Strata.Message.fromFormat
            f!"LiftInternalFuncDecls: procedure '{proc.header.name.name}' declares \
               internal function(s) {names} that clash with top-level function(s); \
               internal function declarations must not shadow top-level functions"
        -- TODO: Conservatively reject procedures that combine local type declarations with internal
        -- function declarations.  Lifting hoists the functions above the procedure, where a
        -- procedure-local `type T;` is not in scope, so a lifted function that mentions such a
        -- type would fail to re-type-check.  No known benchmarks currently combine these features;
        -- when one is encountered, this pass should be expanded to hoist both local type and
        -- function declarations.
        -- Fast (linear, short-circuiting) presence check; on failure we then
        -- collect the actual names once for the diagnostic.
        if Imperative.Block.hasLocalTypeDecl ss then
          let localTypes := (ss.flatMap Imperative.Stmt.localTypeDecls |>.map (·.name)).dedup
          let names := String.intercalate ", " (localTypes.map (fun n => s!"'{n}'"))
          throw <| Strata.Message.fromFormat
            f!"LiftInternalFuncDecls: procedure '{proc.header.name.name}' combines local type \
               declaration(s) {names} with internal function declaration(s); lifting internal \
               functions in the presence of local type declarations is not supported"
        let proc := { proc with body := .structured stripped }
        let arr ← hoistProcedure proc md lfs
        pure arr.toList
  | _ => pure [decl]

/-- Hoist every internal `funcDecl` in the program's procedures to a closed
    top-level `Decl.func`. -/
def run (p : Program) : CoreTransformM Program := do
  -- Names of all top-level function declarations in the program (both plain
  -- `Decl.func` and each member of a `Decl.recFuncBlock`).  An internal
  -- `funcDecl` that shares a name with one of these would shadow it lexically.
  let topLevelFuncNames : Std.HashSet String :=
    Std.HashSet.ofList (p.decls.flatMap fun
      | .func f _ => [f.name.name]
      | .recFuncBlock fs _ => fs.map (·.name.name)
      | _ => [])
  let out ← p.decls.foldlM (init := (#[] : Array Decl)) fun acc decl => do
    let contrib ← processDecl topLevelFuncNames decl
    pure (acc ++ contrib.toArray)
  return { decls := out.toList }

end LiftInternalFuncDecls

open Core.Transform in
/-- `CoreTransformM` runner for `LiftInternalFuncDecls`, suitable for use with
    `Core.Transform.run`.  Returns whether any function was hoisted. -/
def liftInternalFuncDecls (p : Program) : CoreTransformM (Bool × Program) := do
  let p' ← LiftInternalFuncDecls.run p
  return (p'.decls.length != p.decls.length, p')

/-- Pipeline phase for `LiftInternalFuncDecls`.  Model-preserving: it changes
    only how functions are represented (local → closed top-level), not the
    program's meaning. -/
def liftInternalFuncDeclsPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "liftInternalFuncDecls" fun prog =>
    liftInternalFuncDecls prog

end Core

end -- public section

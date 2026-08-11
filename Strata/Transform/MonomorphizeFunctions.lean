/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.NameMangling
public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LExprTraversal
import Strata.Util.Worklist
import all Strata.DL.Imperative.Stmt

/-! # Monomorphize Functions

The `MonomorphizeFunctions` program transformation removes polymorphism from
top-level *functions* by duplicating each polymorphic function once per distinct
ground type-instantiation it is used at, and rewriting every reference to point
at the matching specialized copy.

## Where it runs

This pass runs in `corePipelinePhases` after:
- `typeCheckPhase`: a function call site reveals its instantiation through the
  type annotation the type checker attaches to the `.op` node.  Before type
  checking, `f`'s call sites carry `f`'s generic arrow (e.g. `a → a`); only after
  it do they carry the instantiated arrow (e.g. `int → int`).
- `LiftInternalFuncDecls` has also already hoisted every function to the top level,
  so all functions are `Decl.func` / `Decl.recFuncBlock` declarations.

## How it works (worklist)

The worklist seeds from the top-level procedures, axioms, `distinct` facts and
monomorphic functions as well as monomorphic functions in Factory.
A polymorphic function is specialized only if it is reachable from one of those
contexts.
After then, each recorded `(f, inst)` is then processed by type-substituting `f`'s
signature and body (`f.typeArgs ↦ inst`). If folding their bodies and axioms
reveal further specialization of other polymorphic functions, They are iteratively
processed through the worklist algorithm.

Finally each polymorphic declaration is replaced, in place, by its specialized
copies with references rewritten (a function used at no ground instantiation
simply vanishes — dead polymorphic functions are removed).

Recursive polymorphic functions are specialized in a way that each specialization
is added to the existing mutual block.
-/

public section

namespace Core
namespace MonomorphizeFunctions

open Lambda Imperative
open Core.Transform
open Strata.PtrCache
open Core.NameMangling

/-- Where a polymorphic function to monomorphize originates. -/
inductive FuncSource where
  /-- A top-level declaration in the user's Program (`Program.decls`). -/
  | program (declIdx : Nat)
  /-- A polymorphic function in the Core `Factory` (e.g. `select`, `update`,
      `Seq` operations, datatype axioms). -/
  | factory
  deriving BEq, Hashable, Repr

/-- The polymorphic top-level functions of a program, and the polymorphic
    functions in the Factory. -/
structure PolymorphicFuncDecls where
  /-- Maps a polymorphic Program-level function's name to its declaration. -/
  functionByName : Std.HashMap String Function
  /-- Maps a polymorphic Program-level function's name to its top-level
      declaration index. -/
  declIdxByName : Std.HashMap String Nat
  /-- The names of polymorphic Factory functions. -/
  polyFactoryNames : Std.HashSet String

/-- Collect the names of polymorphic functions in `factory`, excluding
    SMT-trigger meta-operators (matched by name by the SMT encoder and only
    used to set the trigger patterns accordingly). -/
def collectPolymorphicFuncDeclsFromFactory
    (factory : Lambda.Factory CoreLParams) : Std.HashSet String :=
  factory.toArray.foldl (init := {}) fun acc f =>
    if !f.typeArgs.isEmpty && !isTriggerMetaOp f.name.name then
      acc.insert f.name.name
    else acc
where
  /-- SMT-trigger meta-operators are matched by name by SMTEncoder and
      only used to set the triggers accordingly. -/
  isTriggerMetaOp (name : String) : Bool :=
    name == "TriggerGroup.addTrigger" ||
    name == "TriggerGroup.empty" ||
    name == "Triggers.addGroup" ||
    name == "Triggers.empty"

/-- Index the polymorphic top-level functions of `p` and polymorphic
    functions in `factory`. -/
def collectPolymorphicFuncDecls (p : Program) (factory : Lambda.Factory CoreLParams) :
    PolymorphicFuncDecls :=
  let init : Std.HashMap String Function × Std.HashMap String Nat := ({}, {})
  let (functionByName, declIdxByName) :=
    p.decls.zipIdx.foldl (init := init) fun acc (decl, idx) =>
      match decl with
      | .func f _ => insertIfPoly acc idx f
      | .recFuncBlock fs _ => fs.foldl (init := acc) fun acc f => insertIfPoly acc idx f
      | _ => acc
  { functionByName, declIdxByName,
    polyFactoryNames := collectPolymorphicFuncDeclsFromFactory factory }
where
  /-- Add `f` to the `(functionByName, declIdxByName)` accumulator if it is
      polymorphic; otherwise leave the accumulator unchanged. -/
  insertIfPoly
      (acc : Std.HashMap String Function × Std.HashMap String Nat)
      (idx : Nat) (f : Function) :
      Std.HashMap String Function × Std.HashMap String Nat :=
    if f.typeArgs.isEmpty then acc
    else (acc.1.insert f.name.name f, acc.2.insert f.name.name idx)

/-! ### Structures for specialized functions -/

/-- A type substitution information. -/
structure TypeArgsSubstitution where
  /-- The monotypes given as args to a polymorphic function call. -/
  givenTypes : List Lambda.LMonoTy
  /-- The substitution map built from givenTypes and the polymorphic function
    this substitution is being applied to -/
  subst: Subst
  deriving BEq

/-- A reference to a polymorphic function call, together with the instantiation
    of its type variables and the source-declaration index it came from. -/
structure FuncSpecialization where
  /-- The polymorphic function's name. -/
  name : String
  /-- The monotype instantiation of its type parameters (`ty` param of `.op`). -/
  typeSubst : TypeArgsSubstitution
  /-- Where the polymorphic function this refers to lives — a `Program.decls`
      entry, or the `Factory`. -/
  source : FuncSource

/-- Two references denote the same specialization when they share a base name,
    source, and ground instantiation `givenTypes`; `subst` is functionally
    determined by `givenTypes`, so it is excluded.  Kept consistent with the
    `Hashable` instance so the worklist's `HashSet` dedups by mangled identity
    (otherwise the same name is specialized twice and the second copy collides). -/
instance : BEq FuncSpecialization where
  beq a b :=
    a.name == b.name && a.source == b.source &&
    a.typeSubst.givenTypes == b.typeSubst.givenTypes

instance : Hashable FuncSpecialization where
  hash fs := mixHash (hash fs.typeSubst.givenTypes) (hash fs.name)

/-- The functions defined by the source of `fs`: for a `.func`, the singleton;
    for a `.recFuncBlock`, its members; for a Factory
    function, the singleton — looked up by name.  Returns `[]` if the source
    can't be resolved (shouldn't happen for a well-formed `FuncSpecialization`). -/
def FuncSpecialization.functionsAt (p : Program)
    (factory : Lambda.Factory CoreLParams) (fs : FuncSpecialization) : List Function :=
  match fs.source with
  | .program didx =>
    -- Each poly function/member is specialized independently at exactly the
    -- instantiations reached by its own call sites.  For a `recFuncBlock`,
    -- return only the member whose name matches `fs`.
    match p.decls[didx]! with
    | .func f _ => [f]
    | .recFuncBlock members _ => members.filter (·.name.name == fs.name)
    | _ => []
  | .factory =>
    match factory.get? fs.name with
    | some lfunc => [lfunc.toFunc]
    | none => []

/-- Look up a polymorphic function by name. -/
def PolymorphicFuncDecls.lookup (self : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (name : String) :
    Option (Function × FuncSource) :=
  match self.functionByName.get? name with
  | some f => (self.declIdxByName.get? name).map (fun didx => (f, .program didx))
  | none =>
    if self.polyFactoryNames.contains name then
      (factory.get? name).map (fun lfunc => (lfunc.toFunc, .factory))
    else none

/-- Return the type-variable substitution implied by an `.op f (some ty)`
    reference, or `none` if unification fails.  Relies on the pass running after
    `typeCheckPipelinePhase` so `ty` is the concrete instantiation (see the
    module header). -/
def getTypeSubstitution (f : Function) (ty : Option LMonoTy)
  : Option TypeArgsSubstitution :=
  match f.toLFunc.opTypeSubst (.op () f.name ty) with
  | some S =>
    some {
      givenTypes := f.typeArgs.map (fun ta => LMonoTy.subst S (.ftvar ta))
      subst := S
    }
  | none => none


/-! ### Mangling monomorphized function names -/

/-- Rename an `.op` LExpr of a polymorphic function (Program-level or
    Factory) to its specialized name. -/
def rewriteLExprOp (polyfunDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (e : Expression.Expr) :
    StateM (PtrCache mangleTy) (Option Expression.Expr × List FuncSpecialization) := do
  let .op m o ty := e | pure (none, [])
  -- Look up the polymorphic-function record and determine its source.
  let some (fdef, source) := polyfunDecls.lookup factory o.name | pure (none, [])
  let some typeSubst := getTypeSubstitution fdef ty | pure (none, [])
  let fs : FuncSpecialization := { name := o.name, typeSubst, source }
  let nm ← modifyGet (fun cache => mangleFuncName cache fs.name fs.typeSubst.givenTypes)
  return (some (.op m nm ty), [fs])

/-- Rewrite every reference to a polymorphic function to its specialized
    name, threading the caller's `PtrCache mangleTy` (via `applyOnceDFSM`) so a
    type is mangled only once across *all* expressions the caller rewrites. -/
def mangleOpsInLExpr (polyfunDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (e : Expression.Expr) : StateM (PtrCache mangleTy) Expression.Expr := do
  let (e', _) ← Lambda.LExpr.Traversal.applyOnceDFSM .preorder (rewriteLExprOp polyfunDecls factory) e
  return e'


/-! ### Collecting .op LExpr nodes that provide the monomorphic types for specialization  -/

/-- Fold out the references to polymorphic functions (Program-level or
    Factory) in `e`, visiting each physically distinct subterm once
    (`PtrCache`). -/
def collectFuncSpecializations (pfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    List FuncSpecialization :=
  Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
    (fun e => Id.run do
      let .op _ o ty := e | pure []
      let some (fdef, source) := pfunDecls.lookup factory o.name | pure []
      let some typeSubst := getTypeSubstitution fdef ty | pure []
      pure [{ name := o.name, typeSubst, source }])
    e

/-- The user-facing expressions in a `Command` (mirror of `Command.mapExprM`). -/
def collectFromCommand (c : Command) : List Expression.Expr :=
  ((Command.mapExprM (M := StateM (Array Expression.Expr))
      (fun e => do modify (·.push e); pure e) c).run #[]).2.toList

/-- All references to polymorphic functions in a procedure's commands and
    pre/postconditions. -/
def collectFromProcedure (polyfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (proc : Procedure) : List FuncSpecialization :=
  let specExprs := proc.spec.preconditions.values.map (·.expr) ++
                   proc.spec.postconditions.values.map (·.expr)
  -- Collect from both body forms, mirroring `rewriteProcedure` (which rewrites
  -- both), so no reference is renamed without its specialization being seeded.
  let bodyExprs := match proc.body with
    | .structured ss => Statements.collectExprs ss
    | .cfg cfg => cfg.blocks.flatMap fun (_, b) =>
        b.cmds.flatMap collectFromCommand ++
        (match b.transfer with | .condGoto pp _ _ _ => [pp] | .finish _ => [])
  (specExprs ++ bodyExprs).flatMap (collectFuncSpecializations polyfunDecls factory)

/-- The user-facing expressions of a function: body, axioms, precondition
    expressions, and measure. -/
def expressionsFromFunction (f : Function) : List Expression.Expr :=
  f.body.toList ++ f.axioms ++ f.preconditions.map (·.expr) ++ f.measure.toList

/-- All references to polymorphic functions in a function's expressions. -/
def collectFromFunction (pfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (f : Function) : List FuncSpecialization :=
  (expressionsFromFunction f).flatMap (collectFuncSpecializations pfunDecls factory)


/-! ### Rewriting expressions in all top-level declarations modulo functions themselves -/

/-- Rewrite operator references in a procedure's spec and body, threading the cache. -/
def rewriteProcedure (polyfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (proc : Procedure) :
    StateM (PtrCache mangleTy) Procedure := do
  let rw := mangleOpsInLExpr polyfunDecls factory
  let pre' ← proc.spec.preconditions.mapM (fun (l, c) => do pure (l, { c with expr := ← rw c.expr }))
  let post' ← proc.spec.postconditions.mapM (fun (l, c) => do pure (l, { c with expr := ← rw c.expr }))
  let body' ← match proc.body with
    | .structured ss => Procedure.Body.structured <$> Statements.mapExprsM rw ss
    | .cfg cfg => do
      let blocks ← cfg.blocks.mapM (fun (l, b) => do
        let cmds ← b.cmds.mapM (Command.mapExprM rw)
        let transfer ← match b.transfer with
          | .condGoto pp lt lf md => (fun p => DetTransferCmd.condGoto p lt lf md) <$> rw pp
          | .finish md => pure (.finish md)
        pure (l, { b with cmds := cmds, transfer := transfer }))
      pure (Procedure.Body.cfg { cfg with blocks := blocks })
  pure { proc with
    spec := { proc.spec with preconditions := pre', postconditions := post' },
    body := body' }

/-- Rewrite polymorphic-function references in the always-live top-level decls
    (procedures, axioms, `distinct`) to their specialized names, and return the
    instantiations found (to seed the worklist). -/
def processTopDecls (index : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (p : Program) :
    StateM (PtrCache mangleTy) (Program × List FuncSpecialization) := do
  let mut decls : Array Decl := #[]
  -- Accumulate references in an `Array` (amortized O(1) push) rather than a
  -- `List` (`++` is O(n) so repeatedly appending is O(n²) in the decl count).
  let mut refs : Array FuncSpecialization := #[]
  for decl in p.decls do
    match decl with
    | .proc proc md =>
      refs := refs ++ collectFromProcedure index factory proc
      decls := decls.push (.proc (← rewriteProcedure index factory proc) md)
    | .ax a md =>
      refs := refs ++ collectFuncSpecializations index factory a.e
      decls := decls.push (.ax { a with e := ← mangleOpsInLExpr index factory a.e } md)
    | .distinct n es md =>
      refs := refs ++ es.flatMap (collectFuncSpecializations index factory)
      decls := decls.push (.distinct n (← es.mapM (mangleOpsInLExpr index factory)) md)
    | .func f _ =>
      -- A monomorphic function passes through untouched here (rewriting happens
      -- in `updateFunctionsInProgram`), but its body is *always live* in the
      -- output — so seed its polymorphic-function references now.  Polymorphic
      -- `.func`s are handled by the worklist, not seeded from.
      if f.typeArgs.isEmpty then
        refs := refs ++ collectFromFunction index factory f
      decls := decls.push decl
    | .recFuncBlock fs _ =>
      -- Same: seed from every *monomorphic* member of the block.  Polymorphic
      -- members are covered by the worklist.
      for f in fs do
        if f.typeArgs.isEmpty then
          refs := refs ++ collectFromFunction index factory f
      decls := decls.push decl
    | _ => decls := decls.push decl
  return ({ decls := decls.toList }, refs.toList)


/-! ### Type instantiation and specialization -/

/-- Apply a type substitution to every field of `f`. -/
def monomorphizeFunction (f : Function) (newName : CoreIdent) (inst : TypeArgsSubstitution)
  : Function :=
  let S := inst.subst
  { f with
    inputs := f.inputs.map (fun (id, mty) => (id, LMonoTy.subst S mty)),
    output := LMonoTy.subst S f.output,
    body := f.body.map (·.applySubst S),
    axioms := f.axioms.map (·.applySubst S),
    preconditions := f.preconditions.map (fun p => { p with expr := p.expr.applySubst S }),
    measure := f.measure.map (·.applySubst S)
    name := newName,
    typeArgs := [] }

/-- The state threaded through the worklist while working on monomorphization -/
structure MonoWorklistState where
  cache : PtrCache mangleTy -- A String cache of mangled MonoTys
  -- (Function specialization, the monomorphized function)
  specializedFnsInProg : Array (FuncSpecialization × Function)
  specializedFnsInFactory : Array (FuncSpecialization × Function)

/-- Empty starting state. -/
def MonoWorklistState.init : MonoWorklistState :=
  { cache := PtrCache.empty,
    specializedFnsInProg := #[],
    specializedFnsInFactory := #[] }

/-- The state monad for the monomorphization worklist. -/
abbrev MonoWorklistStateM := StateM MonoWorklistState

/-- Default upper bound on the number of specializations the worklist will
    process.

    Overridable via `run`'s `cap` parameter so tests can inject a small value
    without running to a million iterations. -/
def maxSpecializations : Nat := 1000000

/-- Specialize one function `f` of a polymorphic declaration to the specialization
    `fs`, appending the `(fs, tf)` pair to `specializedFnsInProg` (Program source) or
    `specializedFnsInFactory` (Factory source), and returning the `FuncSpecialization`s
    discovered inside `tf`'s body (to be enqueued). -/
def addSpecializedFunctions (pfuncDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (fs : FuncSpecialization) (f : Function) :
    MonoWorklistStateM (List FuncSpecialization) := do
  -- `functionsAt` returns only the member whose name matches `fs.name`, so
  -- `f.name.name == fs.name` and we can use `fs` directly.
  let s ← get
  let (nm, cache') := mangleFuncName s.cache fs.name fs.typeSubst.givenTypes
  let tf := monomorphizeFunction f nm fs.typeSubst
  let newState := match fs.source with
    | .program _ => { s with cache := cache', specializedFnsInProg := s.specializedFnsInProg.push (fs, tf) }
    | .factory => { s with cache := cache', specializedFnsInFactory := s.specializedFnsInFactory.push (fs, tf) }
  set newState
  return collectFromFunction pfuncDecls factory tf

/-- The worklist's per-item action: for a specialization `fs`, specialize each
    member function of the declaration it refers to (a Program `.func` is a
    singleton; a `recFuncBlock` yields only the single member whose name matches
    `fs.name` — each member is specialized independently at exactly its
    reachable instantiations; a Factory function is a singleton), and return the
    `FuncSpecialization`s newly discovered in the specialized bodies. -/
def processFuncSpecialization
    (pfuncDecls : PolymorphicFuncDecls) (p : Program)
    (factory : Lambda.Factory CoreLParams) (fs : FuncSpecialization) :
    MonoWorklistStateM (List FuncSpecialization) := do
  let acc ← (fs.functionsAt p factory).foldlM
    (init := (#[] : Array FuncSpecialization))
    fun (acc : Array FuncSpecialization) m => do
      return acc.appendList (← addSpecializedFunctions pfuncDecls factory fs m)
  return acc.toList

/-- Rewrite operator references in a function's expressions, threading the cache. -/
def mangleOpsInFunctionDecl (polyfunDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (f : Function) :
    StateM (PtrCache mangleTy) Function := do
  let body' ← f.body.mapM (mangleOpsInLExpr polyfunDecls factory)
  let axioms' ← f.axioms.mapM (mangleOpsInLExpr polyfunDecls factory)
  let pre' ← f.preconditions.mapM (fun pc => do return { pc with expr := ← mangleOpsInLExpr polyfunDecls factory pc.expr })
  let measure' ← f.measure.mapM (mangleOpsInLExpr polyfunDecls factory)
  return { f with body := body', axioms := axioms', preconditions := pre', measure := measure' }

/-- Rewrite every function in `p`'s declaration list.
    - Monomorphic functions and non-poly `recFuncBlock`s pass through with
      their operator references renamed.
    - Each polymorphic `Decl.func` is replaced by its monomorphized copies.
    - Each mutually recursive functions block is replaced by a single new block
      in which every monomorphic member is passed through (with references renamed) and every
      polymorphic member is inlined-replaced by its specialized copies.
    - Everything else — types, procedures, axioms, `distinct` - passes through
      unchanged because they were already rewritten by `processTopDecls`). -/
def updateFunctionsInProgram
    (polyfuncDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (p : Program) (specs : Array (FuncSpecialization × Function)) :
    StateM (PtrCache mangleTy) Program := do
  -- Group the Program-sourced specializations once, keyed by their originating
  -- declaration index *and* function name, so each decl/member looks up its
  -- specialized copies directly.  Insertion order within each bucket is
  -- preserved.
  let specsByFn : Std.HashMap (Nat × String) (Array (FuncSpecialization × Function)) :=
    specs.foldl (init := {}) fun m (spec, fn) =>
      match spec.source with
      | .program didx =>
        let key := (didx, spec.name)
        m.insert key ((m.getD key #[]).push (spec, fn))
      | .factory => m
  let mut out : Array Decl := #[]
  for (decl, idx) in p.decls.zipIdx do
    match decl with
    | .func f md =>
      if f.typeArgs.isEmpty then
        out := out.push (.func (← mangleOpsInFunctionDecl polyfuncDecls factory f) md)
      else
        for (_spec, fn) in specsByFn.getD (idx, f.name.name) #[] do
          out := out.push (.func (← mangleOpsInFunctionDecl polyfuncDecls factory fn) md)
    | .recFuncBlock fs md =>
      let mut members : Array Function := #[]
      for f in fs do
        if f.typeArgs.isEmpty then
          members := members.push (← mangleOpsInFunctionDecl polyfuncDecls factory f)
        else
          for (_spec, fn) in specsByFn.getD (idx, f.name.name) #[] do
            members := members.push (← mangleOpsInFunctionDecl polyfuncDecls factory fn)
      if !members.isEmpty then
        out := out.push (.recFuncBlock members.toList md)
    | _ => out := out.push decl
  return { decls := out.toList }

/-- Rebuild `factory`, dropping every polymorphic entry and appending the
    specialized copies produced by the worklist.  Rewrites op references inside
    each specialized body (so factory-internal references become their specialized
    names, and any surviving monomorphic factory entries also see the renames). -/
def updateFactory (polyfuncDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (specializedFnsInFactory : Array (FuncSpecialization × Function)) :
    StateM (PtrCache mangleTy) (Lambda.Factory CoreLParams) := do
  -- Keep every non-polymorphic entry from the original factory, plus any
  -- polymorphic entry that isn't indexed for monomorphization (e.g. the
  -- SMT-trigger meta-ops).
  let mut kept : Array (Lambda.LFunc CoreLParams) := #[]
  for lfunc in factory.toArray do
    if lfunc.typeArgs.isEmpty ∨ !polyfuncDecls.polyFactoryNames.contains lfunc.name.name then
      let rewrittenFunc ← mangleOpsInFunctionDecl polyfuncDecls factory lfunc.toFunc
      kept := kept.push { lfunc with toFunc := rewrittenFunc }

  -- Append specialized copies (their bodies also rewritten).
  for (fs, tf) in specializedFnsInFactory do
    let rewritten ← mangleOpsInFunctionDecl polyfuncDecls factory tf
    let concreteEval := (factory.get? fs.name).bind (·.concreteEval)
    kept := kept.push { toFunc := rewritten, concreteEval }
  return Lambda.Factory.ofArray kept


/-! ### The top-level transformation -/

def run (p : Program) (cap : Nat := maxSpecializations) : CoreTransformM Program := do
  let factory ← Core.Transform.getFactory
  let polyfuncDecls := collectPolymorphicFuncDecls p factory

  -- Seed from the always-live top-level declarations (procedures, axioms,
  -- `distinct`), rewriting their references in place. Polymorphic functions are
  -- specialized only if reached from these decls.
  let (ptd, cache) := (processTopDecls polyfuncDecls factory p).run PtrCache.empty
  let (p, seedRefs) := ptd

  -- Also seed from every *monomorphic* Factory function's body/axioms: these
  -- are kept-and-rewritten in `updateFactory`, so their polymorphic-function
  -- references are always live in the output and must be specialized too.
  let factorySeedRefs : Array FuncSpecialization :=
    factory.toArray.foldl (init := #[]) fun acc lfunc =>
      if lfunc.typeArgs.isEmpty then
        acc.appendList (collectFromFunction polyfuncDecls factory lfunc.toFunc)
      else acc
  let seedRefs := seedRefs ++ factorySeedRefs.toList

  -- Traverse polymorphic functions calling other polymorphic functions with
  -- different type instantiations, and collect all specializations.
  let (finished, endState) ←
    (Strata.Worklist.run seedRefs (processFuncSpecialization polyfuncDecls p factory)
      cap).run
        { MonoWorklistState.init with cache := cache }
  let cache := endState.cache

  if !finished then
    throw (Strata.Message.fromString
      "MonomorphizeFunctions: too many specializations (non-uniform polymorphic \
       recursion is not supported)")

  -- Monomorphize every function.
  let (out, cache) :=
    (updateFunctionsInProgram polyfuncDecls factory p endState.specializedFnsInProg).run cache
  -- Rebuild the Factory: drop poly entries and add specialized copies.
  let (factory', _) :=
    (updateFactory polyfuncDecls factory endState.specializedFnsInFactory).run cache

  Core.Transform.setFactory factory'
  return out

end MonomorphizeFunctions

open Core.Transform in
/-- `CoreTransformM` runner for `MonomorphizeFunctions`. -/
def monomorphizeFunctions (p : Program) : CoreTransformM (Bool × Program) := do
  let p' ← MonomorphizeFunctions.run p
  return (p'.decls != p.decls, p')

/-- Pipeline phase for `MonomorphizeFunctions`.  Model-preserving: a specialized
    copy is a type-instantiated duplicate of the original function, so it denotes
    the same values at that instantiation; references are rewritten to preserve
    meaning. -/
def monomorphizeFunctionsPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "monomorphizeFunctions" fun prog =>
    monomorphizeFunctions prog

end Core

end -- public section

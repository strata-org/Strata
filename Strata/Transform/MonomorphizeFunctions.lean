/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.NameMangling
public import Strata.Languages.Core.NameSets
public import Strata.DL.Lambda.LTyUnify
public import Strata.DL.Lambda.LExprType
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
- Functions are represented by top-level `Decl.func` / `Decl.recFuncBlock`
  declarations.

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
  /-- The prefix of the copies' names (`choosePrefix` of `avoidNames`). -/
  copyPrefix : String := monoPrefix

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

/-- The names `p` uses at operator level or declares: every operator `p` refers to, in a
    statement or not, and the type constructors in its annotation; and every name `p` declares
    for a function, a type, a datatype's type parameter, a constructor, a tester or a field. -/
def checkedNames (p : Program) : List String :=
  let opNames := p.decls.flatMap fun d =>
    (Statements.allExprs d.statements ++ d.ownExprs).flatMap fun e =>
      e.getOps.map (·.name) ++ e.opAnnots.flatMap fun a => tconsNames a.2
  let declNames := p.decls.flatMap fun d =>
    match d with
    | .func f _ => [f.name.name]
    | .recFuncBlock fs _ => fs.map (·.name.name)
    | .type (.con tc) _ => [tc.name]
    | .type (.syn ts) _ => [ts.name]
    | .type (.data block) _ => block.flatMap fun dt =>
        dt.name :: dt.typeArgs ++ dt.constrs.flatMap fun c =>
          c.name.name :: c.testerName :: c.args.map (·.1.name)
    | _ => []
  opNames ++ declNames


/-- The names of the binders of `e` (quantifiers and abstractions). The SMT encoder names a
    bound variable after its binder, and a bound variable shadows a function of the same name
    inside its body. -/
def binderNames : Expression.Expr → List String
  | .abs _ n _ e => n :: binderNames e
  | .quant _ _ n _ tr e => n :: (binderNames tr ++ binderNames e)
  | .app _ f a => binderNames f ++ binderNames a
  | .ite _ c t f => binderNames c ++ binderNames t ++ binderNames f
  | .eq _ a b => binderNames a ++ binderNames b
  | _ => []

/-- The names of the variables of `p`: every free variable of its expressions, the binders of
    its expressions, the parameters of its procedures and the variables their bodies define or
    modify, and the parameters of its functions. The SMT encoder declares a free variable as a
    nullary function, in the same namespace as the functions, so a variable must not be named
    like a copy either. -/
def varNames (p : Program) : List String :=
  let exprs := p.decls.flatMap fun d => Statements.allExprs d.statements ++ d.ownExprs
  (exprs.flatMap fun e => e.collectFvarNames.map (·.name) ++ binderNames e) ++
  (p.decls.flatMap fun
    | .proc q _ =>
      (q.header.inputs.keys ++ q.header.outputs.keys).map (·.name) ++
      (Imperative.Block.modifiedOrDefinedVars q.body.statements true).map (·.name)
    | .func f _ => f.inputs.keys.map (·.name)
    | .recFuncBlock fs _ => fs.flatMap fun f => f.inputs.keys.map (·.name)
    | _ => [])

/-- **The names a copy's name must differ from**: the names `p` uses or declares
    (`checkedNames`), the names a generated declaration avoids (`Program.takenNames`): those of
    all its declarations, axioms, lemmas, `distinct` declarations and procedures included, which
    share one namespace with the copies that become function declarations, and the labels of its
    checks, which name proof obligations and which the pipeline requires to be distinct from
    every declaration's name; the functions its datatypes generate (eliminators, constructors,
    testers, destructors and unsafe destructors, `MutualDatatype.generatedFuncNames`), the names
    of its variables and binders (`varNames`), and the functions of `factory`, which holds Core's
    built-in functions and those a front end registers (`moreFns`), with their parameters and
    binders: monomorphization rewrites a factory function's body to call copies, and the
    encoder declares its parameters by name, so a parameter named like a copy would shadow it.
    Binders are included, so a quantifier's binder never shares a copy's name in SMT, whichever
    symbols the encoder has declared when it names the binder.

    A copy's name starts with `monoPrefix`, so only the names that start with it matter
    (`choosePrefix`). The names the phases after monomorphization generate start with other
    reserved prefixes (`$__lam_`, `$__opaque`, `$__bv`), except those built from an existing
    name `x` by appending a suffix. Such a name starts with `P#` only if `x` is `monoPrefix`
    followed by underscores and the suffix continues with more underscores and then `#`, since
    the padded `P` is longer than every name here. So the condition on a later phase is that
    **the suffixes it appends start with neither `#` nor a run of underscores followed by `#`**.
    The suffixes appended today are `@` or `_` followed by digits, which meet it; a new name
    generator must meet it too. -/
def avoidNames (p : Program) (factory : Lambda.Factory CoreLParams) : List String :=
  checkedNames p ++
  p.takenNames ++
  (p.decls.flatMap fun
    | .type (.data block) _ => Lambda.MutualDatatype.generatedFuncNames block
    | _ => []) ++
  varNames p ++
  factory.toArray.toList.flatMap fun f =>
    f.name.name :: f.inputs.keys.map (·.name) ++ f.exprs.flatMap binderNames

/-- Index the polymorphic top-level functions of `p` and polymorphic
    functions in `factory`. The copies' prefix is chosen against `avoidNames p factory`
    (`choosePrefix_fresh`). -/
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
    polyFactoryNames := collectPolymorphicFuncDeclsFromFactory factory,
    copyPrefix := choosePrefix (avoidNames p factory) }
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
    reference, or `none` if matching fails.  Relies on the pass running after
    `typeCheckPipelinePhase` so `ty` is the concrete instantiation (see the
    module header). -/
def getTypeSubstitution (f : Function) (ty : Option LMonoTy)
  : Option TypeArgsSubstitution :=
  match f.toLFunc.opTypeSubst (.op (ExprSourceLoc.synthesized "monomorphize") f.name ty) with
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
  let nm ← modifyGet (fun cache =>
    mangleFuncName polyfunDecls.copyPrefix cache fs.name fs.typeSubst.givenTypes)
  return (some (.op m nm ty), [fs])

/-- Rewrite every reference to a polymorphic function to its specialized
    name, threading the caller's `PtrCache mangleTy` (via `applyOnceDFSM`) so a
    type is mangled only once across *all* expressions the caller rewrites. -/
def mangleOpsInLExpr (polyfunDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams)
    (e : Expression.Expr) : StateM (PtrCache mangleTy) Expression.Expr := do
  let (e', _) ← Lambda.LExpr.Traversal.applyOnceDFSM .preorder (rewriteLExprOp polyfunDecls factory) e
  return e'


/-! ### Collecting .op LExpr nodes that provide the monomorphic types for specialization  -/

/-- The reference to a polymorphic function (Program-level or Factory) that the
    node `e` makes, if it is such an `.op`. -/
def opFuncSpecialization (pfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    List FuncSpecialization := Id.run do
  let .op _ o ty := e | pure []
  let some (fdef, source) := pfunDecls.lookup factory o.name | pure []
  let some typeSubst := getTypeSubstitution fdef ty | pure []
  pure [{ name := o.name, typeSubst, source }]

/-- Fold out the references to polymorphic functions (Program-level or
    Factory) in `e`, visiting each physically distinct subterm once
    (`PtrCache`). A map or sequence literal refers to the operators that build it
    (`Core.litToOpExpr`), since the SMT encoder emits their specialized copies for it. -/
def collectFuncSpecializations (pfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (e : Expression.Expr) :
    List FuncSpecialization :=
  Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
    (fun e => match e with
      | .const _ c@(.mapConst ..) | .const _ c@(.sequenceConst ..) =>
        Lambda.LExpr.Traversal.visitDFSPtrCached .preorder
          (opFuncSpecialization pfunDecls factory) (litToOpExpr c)
      | _ => opFuncSpecialization pfunDecls factory e)
    e

/-- The user-facing expressions in a `Command` (mirror of `Command.mapExprM`). -/
def collectFromCommand (c : Command) : List Expression.Expr :=
  ((Command.mapExprM (M := StateM (Array Expression.Expr))
      (fun e => do modify (·.push e); pure e) c).run #[]).2.toList

/-- All references to polymorphic functions in a procedure's commands, CFG
    transfers and block metadata, and pre/postconditions. -/
def collectFromProcedure (polyfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (proc : Procedure) : List FuncSpecialization :=
  let specExprs := proc.spec.preconditions.values.map (·.expr) ++
                   proc.spec.postconditions.values.map (·.expr)
  -- Collect from both body forms, mirroring `rewriteProcedure` (which rewrites
  -- both), so no reference is renamed without its specialization being seeded.
  let bodyExprs := match proc.body with
    | .structured ss _ => Statements.collectExprs ss
    | .cfg cfg _ => cfg.blocks.flatMap fun (_, b) =>
        b.md.exprs ++ b.cmds.flatMap collectFromCommand ++
        (match b.transfer with | .condGoto pp _ _ _ => [pp] | .finish _ => [])
    | .abstract => []
  (specExprs ++ bodyExprs).flatMap (collectFuncSpecializations polyfunDecls factory)

/-- All references to polymorphic functions in a function's expressions. -/
def collectFromFunction (pfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (f : Function) : List FuncSpecialization :=
  f.exprs.flatMap (collectFuncSpecializations pfunDecls factory)


/-! ### Rewriting expressions in all top-level declarations modulo functions themselves -/

/-- Rewrite operator references in a procedure's spec and body, threading the cache. -/
def rewriteProcedure (polyfunDecls : PolymorphicFuncDecls)
    (factory : Lambda.Factory CoreLParams) (proc : Procedure) :
    StateM (PtrCache mangleTy) Procedure := do
  let rw := mangleOpsInLExpr polyfunDecls factory
  let pre' ← proc.spec.preconditions.mapM (fun (l, c) => do pure (l, { c with expr := ← rw c.expr }))
  let post' ← proc.spec.postconditions.mapM (fun (l, c) => do pure (l, { c with expr := ← rw c.expr }))
  let body' ← match proc.body with
    | .structured ss o => (Procedure.Body.structured · o) <$> Statements.mapExprsM rw ss
    | .cfg cfg o => do
      let blocks ← cfg.blocks.mapM (fun (l, b) => do
        let cmds ← b.cmds.mapM (Command.mapExprM rw)
        let transfer ← match b.transfer with
          | .condGoto pp lt lf md => (fun p => DetTransferCmd.condGoto p lt lf md) <$> rw pp
          | .finish md => pure (.finish md)
        let md ← b.md.mapExprsM rw
        pure (l, { b with cmds := cmds, transfer := transfer, md := md }))
      pure (Procedure.Body.cfg { cfg with blocks := blocks } o)
    | .abstract => pure .abstract
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
    | .lemma l md =>
      refs := refs ++ collectFuncSpecializations index factory l.e
      decls := decls.push (.lemma { l with e := ← mangleOpsInLExpr index factory l.e } md)
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
  { Lambda.LFuncDefined.applyTypeSubst f inst.subst with name := newName, typeArgs := [] }

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

/-! ### Polymorphic recursion whose instances never end

A call in the body of a polymorphic function `f` to a polymorphic function `g` instantiates each
type parameter `b` of `g` at a type `τ` written over the type parameters of `f`. For each type
parameter `a` of `f` occurring in `τ`, the parameter `(f, a)` flows into `(g, b)`, and grows
when `τ` is not `a` itself. A cycle of flows through a growing one makes every instance of the
functions on it need a strictly bigger one, so a function on such a cycle that is reached has
infinitely many instances. Without such a cycle, the instances stay finite: `f<a>` calling
`f<MyList int>` reaches `f<MyList int>` and stops. -/

/-- A call from a polymorphic function to a polymorphic Program function: the caller, the
    callee, and the callee's type arguments, written over the caller's type parameters. -/
structure PolyCall where
  caller : Function
  callee : Function
  typeArgs : List LMonoTy

/-- Every call between the polymorphic Program functions of `pfuncDecls`. -/
def polyCalls (pfuncDecls : PolymorphicFuncDecls) (factory : Lambda.Factory CoreLParams) :
    List PolyCall :=
  pfuncDecls.functionByName.toList.flatMap fun (_, f) =>
    (collectFromFunction pfuncDecls factory f).filterMap fun fs =>
      (pfuncDecls.functionByName.get? fs.name).map fun g =>
        { caller := f, callee := g, typeArgs := fs.typeSubst.givenTypes }

/-- A flow from type parameter `src` of a call's caller to type parameter `dst` of its callee
    (`(name, parameter index)`), through the call `call`; `grows` when the callee's type
    argument is not the caller's parameter itself. -/
structure ParamFlow where
  src : String × Nat
  dst : String × Nat
  grows : Bool
  call : PolyCall

/-- The flows of the call `c`. -/
def PolyCall.flows (c : PolyCall) : List ParamFlow :=
  c.caller.typeArgs.zipIdx.flatMap fun (a, i) =>
    c.typeArgs.zipIdx.filterMap fun (τ, j) =>
      if τ.freeVars.contains a then
        some { src := (c.caller.name.name, i), dst := (c.callee.name.name, j),
               grows := τ != .ftvar a, call := c }
      else none

/-- The flows of `flows` from `start` back to `goal`, in order, if there is such a path. A
    breadth-first search: each node is visited once. -/
def flowPath (flows : List ParamFlow) (start goal : String × Nat) : Option (List ParamFlow) :=
  go (2 * flows.length + 2) [(start, [])] [start]
where
  /-- Search from the frontier (each node with the reversed path to it), with `seen` the nodes
      already queued. A node is queued once, the goal at most once per flow into it, so `fuel`
      twice the number of flows suffices. -/
  go : Nat → List ((String × Nat) × List ParamFlow) → List (String × Nat) →
      Option (List ParamFlow)
    | 0, _, _ => none
    | _, [], _ => none
    | fuel + 1, (n, path) :: rest, seen =>
      if n == goal && !path.isEmpty then some path.reverse
      else
        let next := (flows.filter (·.src == n)).filter fun fl =>
          fl.dst == goal || !seen.contains fl.dst
        let seen := seen ++ next.map (·.dst)
        go fuel (rest ++ next.map fun fl => (fl.dst, fl :: path)) seen

/-- A cycle of flows through a growing flow whose functions include one of `reached`, as the
    calls along it from that flow's caller back to it. -/
def growingCycle (calls : List PolyCall) (reached : Std.HashSet String) :
    Option (List PolyCall) :=
  let flows := calls.flatMap PolyCall.flows
  flows.findSome? fun fl =>
    if !fl.grows || !reached.contains fl.src.1 then none
    else (flowPath flows fl.dst fl.src).map fun rest => (fl :: rest).map (·.call)

/-- `f` written at the type arguments `tys`, as `f<t1, t2>`. -/
def instanceText (f : Function) (tys : List LMonoTy) : String :=
  s!"{f.name.name}<{", ".intercalate (tys.map (toString ∘ Std.format))}>"

/-- The error for the cycle of calls `cycle`, starting at its first caller at its own type
    parameters and showing the first instances the calls around it need. -/
def growingCycleError (cycle : List PolyCall) : Strata.Message :=
  match cycle with
  | [] => Strata.Message.fromString "MonomorphizeFunctions: polymorphic recursion is not supported"
  | c :: _ =>
    let step (acc : List String × List LMonoTy) (call : PolyCall) :=
      let S := Strata.Util.HMaps.ofScopes [call.caller.typeArgs.zip acc.2]
      let tys := call.typeArgs.map (LMonoTy.subst S)
      (instanceText call.callee tys :: acc.1, tys)
    let start := c.caller.typeArgs.map LMonoTy.ftvar
    let calls := (List.replicate 3 cycle).flatten.take (max 3 cycle.length)
    let (shown, _) := calls.foldl step ([instanceText c.caller start], start)
    Strata.Message.fromString
      s!"MonomorphizeFunctions: polymorphic recursion is not supported: \
         {" needs ".intercalate (shown.reverse.take 2)}{
           String.join (shown.reverse.drop 2 |>.map (s!", which needs " ++ ·))}, ..."

/-- The names of the polymorphic Program functions reached from the functions named `seeds`
    through `calls`. -/
def reachedFunctions (calls : List PolyCall) (seeds : List String) : Std.HashSet String :=
  go (calls.length + seeds.length + 1) seeds {}
where
  /-- Visit `todo`, adding to `seen`. A name's calls are queued once, when it is first seen,
      so the visits are bounded by the seeds and the calls, which `fuel` counts. -/
  go : Nat → List String → Std.HashSet String → Std.HashSet String
    | 0, _, seen => seen
    | _, [], seen => seen
    | fuel + 1, n :: todo, seen =>
      if seen.contains n then go fuel todo seen
      else
        let next := (calls.filter (·.caller.name.name == n)).map (·.callee.name.name)
        go fuel (todo ++ next) (seen.insert n)

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
  let (nm, cache') := mangleFuncName pfuncDecls.copyPrefix s.cache fs.name fs.typeSubst.givenTypes
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

/-- `f`, marked as the copy of the factory function `base` (`FuncAttr.monoCopyOf`). The SMT
    encoder reads a factory function as `base` only when it carries this mark. -/
@[expose] def markCopyOf (base : String) (f : Function) : Function :=
  { f with attr := f.attr.push (.monoCopyOf base) }

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

  -- Append specialized copies (their bodies also rewritten), each marked as a copy of the
  -- function it specializes.
  for (fs, tf) in specializedFnsInFactory do
    let rewritten ← mangleOpsInFunctionDecl polyfuncDecls factory tf
    let concreteEval := (factory.get? fs.name).bind (·.concreteEval)
    kept := kept.push { toFunc := markCopyOf fs.name rewritten, concreteEval }
  return Lambda.Factory.ofArray kept


/-! ### The top-level transformation -/

/-- No name is rejected: the copies' names are built with a prefix no name of the program or
    the factory starts with (`collectPolymorphicFuncDecls`), and every name written into them
    is escaped (`escName`). A copy in the factory is marked with the function it copies
    (`markCopyOf`), which is how the SMT encoder tells it from a function named like one. -/
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

  -- Refuse at once a reached function whose instances would never end, rather than let the
  -- worklist run to its cap.
  let calls := polyCalls polyfuncDecls factory
  if let some cycle := growingCycle calls (reachedFunctions calls (seedRefs.map (·.name))) then
    throw (growingCycleError cycle)

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
  -- Specializing renames operator references rather than restructuring
  -- anything, so every fact carries across; it needs the lifted form because it
  -- only specializes top-level function declarations.
  modelPreservingPipelinePhase "monomorphizeFunctions"
    -- A call inside a polymorphic procedure can instantiate a function at that
    -- procedure's type parameter, which is not a concrete type to specialize at,
    -- so the procedures must be monomorphic first.
    (requires := factSet![.noPolymorphicProcedures, .typeAnnotated])
    (establishes := factSet![.noPolymorphicFunctions])
    (preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .noLoopInvariants,
                         .noLoopMeasures, .staticSingleAssignment, .noBetaRedexes,
                         .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .typeAnnotated, .noInits, .exitsCovered, .noCFGCycles])
    fun prog => monomorphizeFunctions prog

end Core

end -- public section

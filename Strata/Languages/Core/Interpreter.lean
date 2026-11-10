/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Interpreter
public import Strata.DL.Imperative.InterpreterCall
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Env
public import Strata.DL.Lambda.LExprEval
public import Std.Data.TreeMap.Lemmas
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Lambda.LExprEvalProps

/-! # Core's instantiation of the monadic interpreter

The Core language data the monad-generic engine (`Imperative.runInterp`) needs, and
Core's command stepper over it:

* the fuel-bounded evaluator `evalBounded`;
* Core's executable value checks (`replayValueOps`) and the `InterpLang Expression`
  instance;
* the `Command` stepper `replayStepCmd` and its run loop `runCoreInterp`, both generic
  over the effect monad `m`: abbreviations of the generic call-aware `Imperative.Calls.stepCmd`
  and `Imperative.Calls.runCallInterp` at `Expression`.

Lemmas about these definitions, among them the refinement of the specification evaluator
by `evalBounded` (`evalBounded_refines_evalFully`), are in `Core/InterpreterProps.lean`.

The stepper handles `.call` as an **exact run-to-completion** of the callee body in
the same monad (so callee nondeterminism resolves through that monad's `choose`).
The `.call` branch mirrors the reference semantics' `EvalCommandE.call_sem`.  The three
properties the branch reproduces:

* **Spec clauses are emitted, never adjudicated.**  The non-`free` preconditions
  are emitted as assert events at the callee entry snapshot, each with its site
  metadata at the call (`Imperative.Calls.checksAtCall`), and the non-`free`
  postconditions as assert events at the callee final snapshot, in the trace
  order `preconditions ++ bodyEvents ++ postconditions` (the callee body's own
  events land between the two batches because the body is run between them).
  Emission is exactly what `EvalCmdE`'s `eval_assert` already does for an
  ordinary `assert`: capture the unevaluated condition with its factory/store and
  move on.  A clause that is false, non-Boolean, or non-reducing therefore does
  **not** make the call stuck — adjudicating it is the downstream checker's job.
* **The callee frame starts empty.**  `Calls.callEntryStore` builds `σAO` from the
  empty store, so a callee formal already bound in the caller cannot collide.
* **Only non-`free` clauses are emitted** (`defaultAssertEvents`, i.e. the
  `getDefaultCheckExprs` filter), not every clause.

Faithful-mirror choices:
* Unresolved callees are refused (`unsupportedCalleeNotFound`); a `.cfg` body runs from its
  entry block through the CFG driver.
* Call arguments are evaluated with the fuel-bounded `evalBounded`, for engine
  consistency, not the unbounded `Expression.eval`.

Not covered: the `EvalCommandContractE` havoc semantics for a *genuinely*
contract-only callee.  A `.structured []` body is run as an ordinary (trivial) body,
so a contract-only procedure whose outputs must be havoc'd and whose postconditions
must be *assumed* is not handled here. -/

namespace Core

open Imperative

public section

/-- Whether the monomorphic type `τ` is ground (`Lambda.LMonoTy.IsGround`): it is the type of
    the sort it denotes, so it mentions no type variable. -/
@[expose] def isGroundTy (τ : Lambda.LMonoTy) : Bool :=
  decide ((τ.substTyVars Lambda.refTyVarVal).toMonoTy = τ)

/-- The type annotation a runtime store gives a variable: the type its runtime value type
    checks to. -/
@[expose] def runtimeAnn (σr : RStore Expression) : CoreIdent → Option Lambda.LMonoTy :=
  fun x => (σr x).bind (Lambda.LExpr.typeCheck [])

/-- Whether `e` lies in the domain of the reference evaluator `Lambda.LExpr.denoteEval` on the
    semantic stores the runtime store `σr` denotes: every free variable of `e` is bound in `σr`,
    and `e`, each free variable annotated with the type of its runtime value (`runtimeAnn`),
    type checks at a ground type. -/
@[expose, irreducible] def evalTypedDomain (σr : RStore Expression) (e : Expression.Expr) : Bool :=
  (Lambda.LExpr.LExpr.getVars e).all (fun x => (σr x).isSome) &&
    ((e.annotateFvars (runtimeAnn σr)).typeCheck []).any isGroundTy

/-- Whether every operator of `e` that names a function `fn` of `F` is annotated with the
    instance of `fn`'s type `inputs → output` under the substitution that unifying the annotation
    with that type finds (`Lambda.LFunc.opTypeSubst`). -/
@[expose] def opsInstantiated (F : Lambda.Factory CoreLParams) : Expression.Expr → Bool
  | .op m name ty =>
    match F[name.name]? with
    | some fn =>
      match Lambda.LFunc.opTypeSubst fn (.op m name ty), ty with
      | some S, some tyOp =>
        tyOp == (Lambda.LMonoTy.mkArrow' fn.output (fn.inputs.map Prod.snd)).subst S
      | _, _ => false
    | none => true
  | .app _ f a => opsInstantiated F f && opsInstantiated F a
  | .abs _ _ _ body => opsInstantiated F body
  | .ite _ c t f => opsInstantiated F c && opsInstantiated F t && opsInstantiated F f
  | .eq _ a b => opsInstantiated F a && opsInstantiated F b
  | .quant _ _ _ _ tr body => opsInstantiated F tr && opsInstantiated F body
  | _ => true

/-- Whether the operators of `e` and of the runtime values of its free variables are annotated
    with instances of their functions' types (`opsInstantiated`). -/
@[expose] def evalOpsChecked (F : Lambda.Factory CoreLParams) (σr : RStore Expression)
    (e : Expression.Expr) : Bool :=
  opsInstantiated F e &&
    (Lambda.LExpr.LExpr.getVars e).all (fun x => (σr x).all (opsInstantiated F))

/-- The fuel-bounded evaluator: on an expression in the reference evaluator's domain
    (`evalTypedDomain`) whose operators, and those of the runtime values of its free variables,
    are annotated with instances of their functions' types (`evalOpsChecked`), reduce `e` with
    `Lambda.LExpr.eval` at `fuel` and return the value only when it reduces to a fully-decided
    `.value true` that type checks against the factory (`typeCheckWith`, so its operator
    annotations agree with their signatures); otherwise, `none`. Every result this returns is
    the one the fixpoint evaluator `Lambda.LExpr.evalFully` (which retries at increasing fuel)
    returns; it denotes the value of the reference evaluator `Expression.eval`
    (`Lambda.LExpr.denoteEval`) at factories meeting `EvalFactoryWF` (`BoundedEvalSoundAt`). -/
@[expose] def evalBounded (fuel : Nat) :
    Lambda.Factory CoreLParams → RStore Expression → Expression.Expr → Option Expression.Expr :=
  fun F store e =>
    if evalTypedDomain store e && evalOpsChecked F store e then
      match Lambda.LExpr.eval fuel F store e with
      | (v, .value true) => if (v.typeCheckWith F []).isSome then some v else none
      | _ => none
    else none

/-- Whether `value` type-checks, with no bound type variables, to the ground monomorphic type
    `ty` under `factory`; a type with a type variable is never met (no value of the reference
    semantics has one). -/
def valueHasMonoType (factory : Lambda.Factory CoreLParams) (value : Expression.Expr)
    (ty : Lambda.LMonoTy) : Bool :=
  value.typeCheckWith factory [] == some ty && isGroundTy ty

/-- Whether `value` type-checks to `ty` under `factory`: `ty` must be monomorphic and ground, and
    `value` must type-check to it (`valueHasMonoType`); a polymorphic `ty` is never met. -/
def valueHasType (factory : Lambda.Factory CoreLParams) (value : Expression.Expr) (ty : Lambda.LTy) :
    Bool :=
  match Lambda.LTy.toMonoType? ty with
  | some monoTy => valueHasMonoType factory value monoTy
  | none => false

/-- Executable value operations for Core expressions. Two values have the same type when they
    type-check to the same type. -/
def replayValueOps : ReplayValueOps Expression (Lambda.Factory CoreLParams) where
  isValue factory value := Lambda.LExpr.isValue factory value
  hasType := valueHasType
  sameType factory left right :=
    left.typeCheckWith factory [] == right.typeCheckWith factory []

/-- Positional binding of names to values over a store: `Calls.bindPositional` at Core's
    identifiers. -/
abbrev bindPositional {V : Type _} (store : Expression.Ident → Option V)
    (names : List Expression.Ident) (values : List V) : Expression.Ident → Option V :=
  Calls.bindPositional store names values

/-- Reading a list of variables from a store: `Calls.readVarList` at Core's identifiers. -/
abbrev readVarList {V : Type _} (store : Expression.Ident → Option V)
    (names : List Expression.Ident) : Option (List V) :=
  Calls.readVarList store names

/-- The order of Core identifiers by name, the key order of the interpreter store's map. -/
abbrev identCmp : CoreIdent → CoreIdent → Ordering := compareOn Lambda.Identifier.name

/-- Identifiers with equal names are equal (their metadata is `Unit`). -/
instance instLawfulEqCmpIdentCmp : Std.LawfulEqCmp identCmp where
  eq_of_compare {a b} h := by
    cases a; cases b
    simpa using Std.LawfulEqCmp.eq_of_compare (cmp := (compare : String → String → Ordering)) h
  compare_self := Std.ReflCmp.compare_self

/-- The maps of the Core interpreter store's entries, ordered by `identCmp`. -/
abbrev StoreWrites := Std.TreeMap CoreIdent (Option Expression.Expr) identCmp

/-- The entry of a name. Irreducible, as are `StoreWrites.insert` and `StoreWrites.erase`:
    definitional unfolding of an interpreter store stops at its map. -/
@[irreducible] def StoreWrites.find? (w : StoreWrites) (x : CoreIdent) :
    Option (Option Expression.Expr) :=
  w[x]?

/-- The map with the entry of a name set. -/
@[irreducible] def StoreWrites.insert (w : StoreWrites) (x : CoreIdent)
    (e : Option Expression.Expr) : StoreWrites :=
  Std.TreeMap.insert w x e

/-- The map without an entry for a name. -/
@[irreducible] def StoreWrites.erase (w : StoreWrites) (x : CoreIdent) : StoreWrites :=
  Std.TreeMap.erase w x

/-- Core's language-fixed data for the monadic interpreter: the executable
    value predicates, the fuel-bounded evaluator, the denotation of runtime values (a runtime
    value denotes only if it passes `isValue` and type checks against the factory, so it is a
    value expression whose operator annotations agree with their signatures), and the
    interpreter store's entries in a `Std.TreeMap` ordered by `identCmp` (`StoreWrites`).
    The per-run knobs (`haltOn`/`oracleConfig`) stay in `ReplayCfg`. -/
instance : InterpLang Expression where
  RFactory := Lambda.Factory CoreLParams
  rfactory F := F.factory
  ops := replayValueOps
  boundedEval := evalBounded
  denote F r :=
    if Lambda.LExpr.isValue F.factory r && (r.typeCheckWith F.factory []).isSome then
      Lambda.LExpr.denoteEval F (fun _ => none) r
    else none
  typeOf := fun f v => (v.typeCheckWith f []).map (Lambda.LTy.forAll [])
  eqModuloMeta := Lambda.LExpr.eqModuloMeta
  Writes := StoreWrites
  writesEmpty := ∅
  writesFind? := StoreWrites.find?
  writesInsert := StoreWrites.insert
  writesErase := StoreWrites.erase
  writesFind?_empty _ := by unfold StoreWrites.find?; exact Std.TreeMap.getElem?_emptyc
  writesFind?_insert_self _ _ _ := by
    unfold StoreWrites.find? StoreWrites.insert; exact Std.TreeMap.getElem?_insert_self
  writesFind?_insert_ne _ _ _ _ h := by
    unfold StoreWrites.find? StoreWrites.insert
    rw [Std.TreeMap.getElem?_insert, ite_eq_right (mt Std.LawfulEqCmp.eq_of_compare (Ne.symm h))]
  writesFind?_erase_self _ _ := by
    unfold StoreWrites.find? StoreWrites.erase; exact Std.TreeMap.getElem?_erase_self
  writesFind?_erase_ne _ _ _ h := by
    unfold StoreWrites.find? StoreWrites.erase
    rw [Std.TreeMap.getElem?_erase, ite_eq_right (mt Std.LawfulEqCmp.eq_of_compare (Ne.symm h))]

/-- Bounded evaluation of a list of expressions with `evalBounded`: `Calls.evalBoundedList` at
    `Expression`. -/
abbrev evalBoundedList (fuel : Nat) (factory : Lambda.Factory CoreLParams)
    (store : RStore Expression) (es : List Expression.Expr) : Option (List Expression.Expr) :=
  Calls.evalBoundedList fuel factory store es

/-- Core's command stepper, generic over the effect monad `m`: the call-aware stepper
    `Calls.stepCmd` at `Expression`.  `depth` is the remaining call-depth budget. -/
abbrev replayStepCmd {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (π : String → Option Procedure) (depth : Nat) :
    StepCmdM Expression Command m :=
  Calls.stepCmd π depth

/-- Core's run loop, generic over the effect monad `m`: the call-aware driver
    `Calls.runCallInterp` at `Expression`, nesting at most `maxCallDepth` calls.  Each instance
    only chooses `m` (for replay, `m := ReplayM Expression`). -/
abbrev runCoreInterp {m : Type → Type} [Monad m] [InterpEffects Expression m]
    [MonadExcept StopReason m] (π : String → Option Procedure)
    (fuel : Nat) (cfg : IConfig Expression Command)
    (maxCallDepth : Nat := defaultMaxCallDepth) : m (IConfig Expression Command) :=
  Calls.runCallInterp π fuel cfg maxCallDepth

/-- Target-id match of an event (`Calls.targetReached` at `Expression`): an `.assert` or `.cover`
    whose `label` and metadata match `target`, with no evaluation of the condition. -/
abbrev targetReached (target : AssertId Expression) : IEvent Expression → Bool :=
  Calls.targetReached target

end -- public section

end Core

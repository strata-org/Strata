/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Interpreter

/-! # `EvalM`: concrete execution of `runCoreInterp`, at assert/assume policies (`EvalOpts`)

`EvalM` is the `InterpEffects Expression` instance for concrete execution: `emit` evaluates
assert/assume conditions and acts on the policy, and `choose` resolves to the type's canonical
default (`evalDefaultChoice`).  The instance is meant to agree with the ground Core interpreter
`Imperative.Cmd.run` at each of its policies on deterministic programs; this file states no such
agreement.

Key definitions: `EvalOpts`, `EvalOpts.legacy`, `runCoreEvalWith`, `runCoreEval`. Lemmas about
`EvalM`'s effects are in `Core/InterpreterEvalProps.lean`. -/

namespace Core

open Imperative

public section

/-! ## Default values for nondeterministic choices -/

/-- A canonical value of a monomorphic primitive type, for don't-care slots; `none` for types
    with no literal default. -/
def defaultCanonicalValue : Lambda.LMonoTy → Option Expression.Expr
  | .tcons "int" [] => some (.intConst () 0)
  | .tcons "bool" [] => some (.boolConst () false)
  | .tcons "string" [] => some (.strConst () "")
  | .tcons "real" [] => some (.rationalConst () 0)
  | .bitvec n => some (.bitvecConst () n 0)
  | _ => none

/-- The constructor-nesting bound for `datatypeDefault`. -/
def datatypeDefaultDepth : Nat := 8

/-- A default value of the monomorphic type `ty`: `defaultCanonicalValue` when it exists, else
    the first constructor of `F` producing `ty` whose argument types have defaults at
    `depth - 1`; `none` at depth `0`. -/
def datatypeDefault (F : @Lambda.Factory CoreLParams) :
    Nat → Lambda.LMonoTy → Option Expression.Expr
  | 0, _ => none
  | depth + 1, ty =>
    match defaultCanonicalValue ty with
    | some v => some v
    | none =>
      match ty with
      | .tcons name _ =>
        F.toArray.toList.findSome? fun f =>
          if !f.isConstr then none else
          match f.output with
          | .tcons outName _ =>
            if outName != name then none else
            let subst? : Option Lambda.Subst :=
              if f.typeArgs.isEmpty then some Lambda.Subst.empty
              else match Lambda.Constraints.unify [(ty, f.output)] Lambda.SubstInfo.empty with
                | .ok info => some info.subst
                | .error _ => none
            subst?.bind fun S =>
              let inst (t : Lambda.LMonoTy) : Lambda.LMonoTy := Lambda.LMonoTy.subst S t
              let generic := Lambda.LMonoTy.mkArrow' f.output f.inputs.values
              (f.inputs.values.map inst).mapM (datatypeDefault F depth) |>.map fun args =>
                args.foldl (fun acc a => .app () acc a) (.op () f.name (some (inst generic)))
          | _ => none
      | _ => none

/-- The default for an unbound input or a nondeterministic choice: `defaultCanonicalValue`, else
    `datatypeDefault` at `datatypeDefaultDepth` when canonical in `F` and of type `ty`. -/
def defaultValueIn (F : @Lambda.Factory CoreLParams) (ty : Lambda.LMonoTy) :
    Option Expression.Expr :=
  match defaultCanonicalValue ty with
  | some v => some v
  | none =>
    (datatypeDefault F datatypeDefaultDepth ty).filter fun v =>
      Lambda.LExpr.isValue F v && valueHasMonoType F v ty

/-- What a false assertion does to an `EvalM` run (`Cmd.run`'s `continuePastAssert` hook). -/
inductive AssertPolicy where
  /-- Record the failure in `EvalState.assertFailures` and continue. -/
  | collect
  /-- Stop the run at the first false assertion, with the store frozen there. -/
  | halt
  deriving DecidableEq, Repr, Inhabited

/-- What an `assume` does to an `EvalM` run (`Cmd.run`'s `ignoreAssume` hook). -/
inductive AssumePolicy where
  /-- Record the assume and continue. -/
  | ignore
  /-- Stop the run unless the assume's condition evaluates to the true literal. -/
  | enforce
  deriving DecidableEq, Repr, Inhabited

/-- `EvalM` run options: the eval fuel, the call-depth limit, and one policy per behavioural hook
    of `Cmd.run`. -/
structure EvalOpts where
  /-- Fuel for `evalBounded` when `emit` evaluates an assert/assume condition. -/
  fuel : Nat
  /-- What a false assertion does. -/
  assertPolicy : AssertPolicy := .halt
  /-- What an `assume` does. -/
  assumePolicy : AssumePolicy := .ignore
  /-- The most calls a run may nest (`runCoreEvalWith` passes it to `runCoreInterp`). -/
  maxCallDepth : Nat := defaultMaxCallDepth
  deriving Repr, Inhabited

/-- The options matching `Cmd.run`'s defaults: halt at the first false assertion, ignore assumes. -/
abbrev EvalOpts.legacy (fuel : Nat) : EvalOpts :=
  { fuel := fuel, assertPolicy := .halt, assumePolicy := .ignore }

/-- Why an `EvalM` run stopped early: `assertFailed` (a false assertion under
    `AssertPolicy.halt`, carrying the failing assert's event argument), `stuck` (a generic
    engine `StopReason`), and the two `EvalM`-only failures `assumeDidNotReduceToBool` and
    `nondetChoiceUnsupported`. -/
inductive EvalHalt where
  | assertFailed (arg : REventArg Expression (Lambda.Factory CoreLParams))
  | stuck (reason : StopReason)
  | assumeDidNotReduceToBool (label : String)
  | nondetChoiceUnsupported

/-- English rendering of an `EvalHalt`. -/
def EvalHalt.describe : EvalHalt → String
  | .assertFailed arg => s!"assert ({arg.label}) failed"
  | .stuck reason => reason.describe
  | .assumeDidNotReduceToBool label =>
      s!"assume ({label}) condition did not reduce to bool"
  | .nondetChoiceUnsupported =>
      "nondeterministic choice unsupported in faithful-legacy evaluation"

instance : ToString EvalHalt where
  toString := EvalHalt.describe

/-- `EvalM`'s state: the reversed event trace and, under `AssertPolicy.collect`, the collected
    failures (label, evaluated condition, metadata), most recent first. -/
structure EvalState where
  traceRev : List (IEvent Expression) := []
  assertFailures : List (String × Expression.Expr × Imperative.MetaData Expression) := []

/-- The concrete-execution monad: it reads the run options `EvalOpts`, may stop early with an
    `EvalHalt`, and threads an `EvalState` that is kept when the run halts. -/
abbrev EvalM := ReaderT EvalOpts (ExceptT EvalHalt (StateT EvalState Id))

/-- Every generic `StopReason` throw is an `EvalHalt.stuck` halt. -/
instance : MonadExceptOf StopReason EvalM where
  throw r := throwThe EvalHalt (EvalHalt.stuck r)
  tryCatch x h := tryCatchThe EvalHalt x fun (e : EvalHalt) =>
    match e with
    | .stuck r => h r
    | .assertFailed arg => throwThe EvalHalt (EvalHalt.assertFailed arg)
    | .assumeDidNotReduceToBool l =>
      throwThe EvalHalt (EvalHalt.assumeDidNotReduceToBool l)
    | .nondetChoiceUnsupported => throwThe EvalHalt EvalHalt.nondetChoiceUnsupported

/-- The value `EvalM`'s `choose` resolves a choice of type `ty` to: `defaultValueIn`, kept only
    when it passes the engine's value and type checks. -/
@[expose] def evalDefaultChoice (fac : Lambda.Factory CoreLParams) (ty : Expression.Ty) :
    Option Expression.Expr :=
  ((Lambda.LTy.toMonoType? ty).bind (defaultValueIn fac)).filter fun v =>
    (InterpLang.ops (P := Expression)).isValue fac v
      && (InterpLang.ops (P := Expression)).hasType fac v ty

/-- `EvalM`'s effects.  `choose` resolves to `evalDefaultChoice` or throws
    `nondetChoiceUnsupported`.  `emit` of an `assert` evaluates its condition and reads it as a
    Boolean literal up to metadata (`InterpLang.boolLit?`): `true` records and continues, `false`
    records and halts (`.halt`) or is collected (`.collect`), anything else is stuck.  An `assume`
    is recorded under `.ignore`, and under `.enforce` only when its condition is `true`, stopping
    otherwise.  A `cover` is recorded. -/
instance : InterpEffects Expression EvalM where
  choose fac _ ty := match evalDefaultChoice fac ty with
    | some v => pure v
    | none => throwThe EvalHalt EvalHalt.nondetChoiceUnsupported
  emit ev := do
    let opts ← read
    match ev with
    | .assert arg =>
      match evalBounded opts.fuel arg.factory arg.store arg.expr with
      | some v =>
        match InterpLang.boolLit? (P := Expression) v with
        | some false =>
          match opts.assertPolicy with
          | .halt => do
            modify fun st => { st with traceRev := ev :: st.traceRev }
            throwThe EvalHalt (EvalHalt.assertFailed arg)
          | .collect =>
            modify fun st =>
              { st with traceRev := ev :: st.traceRev,
                        assertFailures := (arg.label, v, arg.metadata) :: st.assertFailures }
        | some true =>
          modify fun st => { st with traceRev := ev :: st.traceRev }
        | none => throw StopReason.expressionWasNotBoolean
      | none => throw StopReason.expressionDidNotEvaluate
    | .assume arg =>
      match opts.assumePolicy with
      | .ignore => modify fun st => { st with traceRev := ev :: st.traceRev }
      | .enforce =>
        match evalBounded opts.fuel arg.factory arg.store arg.expr with
        | some v =>
          match InterpLang.boolLit? (P := Expression) v with
          | some true =>
            modify fun st => { st with traceRev := ev :: st.traceRev }
          | some false =>
            throw (StopReason.assumptionFalseUnderReplay arg.label)
          | none =>
            throwThe EvalHalt (EvalHalt.assumeDidNotReduceToBool arg.label)
        | none =>
          throwThe EvalHalt (EvalHalt.assumeDidNotReduceToBool arg.label)
    | .cover _ => modify fun st => { st with traceRev := ev :: st.traceRev }

/-- Run `runCoreInterp π` from the embedding of `cfg` under `EvalM` at the given options, with
    their call-depth limit. -/
def runCoreEvalWith (π : String → Option Procedure) (opts : EvalOpts) (fuel : Nat)
    (cfg : IConfig Expression Command) :
    Except EvalHalt (IConfig Expression Command) × EvalState :=
  (((runCoreInterp (m := EvalM) π fuel cfg opts.maxCallDepth).run opts).run).run {}

/-- `runCoreEvalWith` at `EvalOpts.legacy fuel`, the run fuel doubling as the eval fuel. -/
def runCoreEval (π : String → Option Procedure) (fuel : Nat)
    (cfg : IConfig Expression Command) :
    Except EvalHalt (IConfig Expression Command) × EvalState :=
  runCoreEvalWith π (EvalOpts.legacy fuel) fuel cfg

/-- The final store of an `EvalM` run: the terminal store, the frozen store at an assertion
    halt, or `none` otherwise. -/
def runCoreEvalStore (π : String → Option Procedure) (fuel : Nat)
    (cfg : IConfig Expression Command) : Option (RStore Expression) :=
  match runCoreEval π fuel cfg with
  | (.ok cfg', _) => some cfg'.getEnv.store.get
  | (.error (.assertFailed arg), _) => some arg.store
  | (.error (.stuck _), _) => none
  | (.error (.assumeDidNotReduceToBool _), _) => none
  | (.error .nondetChoiceUnsupported, _) => none

/-- The label of the false assertion an `EvalM` run halted on, if any. -/
def runCoreEvalFailedLabel (π : String → Option Procedure) (fuel : Nat)
    (cfg : IConfig Expression Command) : Option String :=
  match runCoreEval π fuel cfg with
  | (.error (.assertFailed arg), _) => some arg.label
  | _ => none

end -- public section

end Core

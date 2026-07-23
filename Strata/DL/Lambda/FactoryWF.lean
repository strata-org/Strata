/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory

/-!
## Well-formedness of LFunc and Factory

WF of Func is separately defined in Strata/DL/Util/Func.lean
-/

namespace Lambda

open Std (ToFormat Format format)
open Strata.DL.Util (Func FuncWF FuncClosed TyIdentifier)

public section


/-- Well-formedness properties for LFunc — extends generic `FuncWF` with
    Lambda-specific extractors and the generated-prefix guard on `typeArgs`. -/
structure LFuncWF {T : LExprParams} (f : LFunc T) extends
    FuncWF
      (fun id => id.name) -- getName
      (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
      (fun e => e.freeVars) -- getTyFreeVars
      f.toFunc where
  /-- Constructors must not have a body or concreteEval. This ensures that
      canonical values (which include fully-applied constructors) are normal
      forms — they cannot be further reduced by `expand_fn` or `eval_fn`. -/
  constr_no_eval :
    f.isConstr → f.body = none ∧ f.concreteEval = none := by decide
  /-- Type arguments must not start with the reserved generated-variable
      prefix `$__ty` used by the type-checker. -/
  typeArgs_no_gen_prefix :
    ∀ ta, ta ∈ f.typeArgs → ¬ ("$__ty".toList.isPrefixOf ta.toList = true) := by decide
  /-- `concreteEval` does not succeed if the length of args is incorrect. -/
  concreteEval_argmatch :
    ∀ fn md args res, f.concreteEval = .some fn
      → fn md args = .some res
      → args.length = f.inputs.length := by intro fn _ _ _ hfn; simp [LFunc.concreteEval] at hfn
  /-- body and concreteEval cannot exist at once. -/
  body_or_concreteEval :
    ¬ (f.concreteEval.isSome ∧ f.body.isSome) := by simp [LFunc.concreteEval]
  /-- `concreteEval` is metadata-insensitive: it produces
      `eraseMetadata`-equivalent results for `eraseMetadata`-equivalent
      arguments, regardless of the metadata parameter. -/
  concreteEval_eraseMetadata :
    ∀ ceval, f.concreteEval = some ceval →
      ∀ md1 md2 (args1 args2 : List (LExpr T.mono)) res1,
        args1.map LExpr.eraseMetadata = args2.map LExpr.eraseMetadata →
        ceval md1 args1 = some res1 →
        ∃ res2, ceval md2 args2 = some res2 ∧
          LExpr.eraseMetadata res1 = LExpr.eraseMetadata res2 := by
    intro _ h; simp [LFunc.concreteEval] at h
  /-- `concreteEval` does not introduce fresh free variables: every free
      variable of a successful result was already free in some argument. -/
  concreteEval_freeVars :
    ∀ ceval, f.concreteEval = some ceval →
      ∀ md (args : List (LExpr T.mono)) res,
        ceval md args = some res →
        ∀ z ∈ LExpr.LExpr.getVars res, ∃ a ∈ args, z ∈ LExpr.LExpr.getVars a := by
    intro _ h; simp [LFunc.concreteEval] at h

/-- Closedness properties for LFunc — the Lambda-specific instantiation of the
    generic `FuncClosed`: the body and preconditions have no free variables
    beyond the function's inputs.

    NOTE: `LFuncClosed` (and its factory-level counterpart `FactoryClosed`) does
    NOT hold of freshly typechecked functions. A local `funcDecl` statement's
    body may legitimately reference variables from the surrounding lexical
    context, so its raw `LFunc` is not closed. The evaluator handles this by
    capturing those variables at `funcDecl`-evaluation time (see
    `Core.captureFreevars` / `Statement.evalAux` for `funcDecl`). TODO: add a
    dedicated pass that performs this capture-elimination on typechecked
    functions up front, at which point the stronger `LFuncClosed`/`FactoryClosed`
    condition becomes true for them. Until then, the typing proofs assume only
    `LFuncWF`/`FactoryWF`, and only the evaluation proofs additionally assume
    `LFuncClosed`/`FactoryClosed`. -/
structure LFuncClosed {T : LExprParams} (f : LFunc T) extends
    FuncClosed
      (fun id => id.name) -- getName
      (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
      f.toFunc where

/-- An LFunc bundled with its well-formedness and closedness proofs. -/
structure WFLFunc (T : LExprParams) where
  func : LFunc T
  wf : LFuncWF func
  closed : LFuncClosed func

/-- The name of the underlying LFunc. -/
def WFLFunc.name (f : WFLFunc T) : T.Identifier := f.func.name

/-- The operator expression for the underlying LFunc. -/
@[expose] def WFLFunc.opExpr [Inhabited T.Metadata] (f : WFLFunc T) : LExpr T.mono :=
  f.func.opExpr

/-- An array of well-formed LFuncs with a proof that function
    names are unique. Also carries closedness of every function (see
    `LFuncClosed`); factories assembled from `WFLFunc`s are fully closed. -/
structure WFLFactory (T : LExprParams) where
  toFactory : Factory T
  wf : ∀(func : LFunc T), func ∈ toFactory.toArray → LFuncWF func
  closed : ∀(func : LFunc T), func ∈ toFactory.toArray → LFuncClosed func

/-- Construct a `WFLFactory` from an array of `WFLFunc`s.
    The `name_nodup` proof defaults to `by decide`. -/
@[expose] def WFLFactory.ofArray {T} (funcs : Array (WFLFunc T))
    (name_nodup : List.Nodup (funcs.toList.map (·.func.name.name)) := by decide)
    : WFLFactory T :=
  let a := funcs.map (·.func)
  let f := Factory.ofArray a
  {
    toFactory := f
    wf := by
      intro func mem
      have q : List.Nodup (a.toList |>.map (fun fn => fn.name.name)) := by
        simp [a]
        exact name_nodup
      have mem_a := Factory.ofArray_mem mem
      simp [a] at mem_a
      have ⟨⟨func2, func2WF, func2Closed⟩, wfMem⟩ := mem_a
      grind
    closed := by
      intro func mem
      have mem_a := Factory.ofArray_mem mem
      simp [a] at mem_a
      have ⟨⟨func2, func2WF, func2Closed⟩, wfMem⟩ := mem_a
      grind
  }

/--
Well-formedness properties of Factory.
-/
structure FactoryWF {T} (fac : Factory T) where
  lfuncs_wf : ∀ (lf:LFunc T), lf ∈ fac.toArray → LFuncWF lf

@[simp]
theorem WFLFactory.toFactory_wf {T} (wf : WFLFactory T) : FactoryWF wf.toFactory :=
  { lfuncs_wf := wf.wf }

/--
Closedness of a Factory: every function is closed (`LFuncClosed`).

See `LFuncClosed` for why this is separated from `FactoryWF`: it does not hold
of freshly typechecked functions.
-/
structure FactoryClosed {T} (fac : Factory T) where
  lfuncs_closed : ∀ (lf:LFunc T), lf ∈ fac.toArray → LFuncClosed lf

@[simp]
theorem WFLFactory.toFactory_closed {T} (wf : WFLFactory T) : FactoryClosed wf.toFactory :=
  { lfuncs_closed := wf.closed }

end -- public section
end Lambda

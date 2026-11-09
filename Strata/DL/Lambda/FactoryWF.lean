/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.LExprType
import all Strata.DL.Lambda.FactoryProps

/-!
## Well-formedness of LFunc and Factory

WF of Func is separately defined in Strata/DL/Util/Func.lean
-/

namespace Lambda

open Std (ToFormat Format format)
open Strata.DL.Util (Func FuncWF TyIdentifier)

public section


/-- Well-formedness properties for `LFunc`: generic name, type-variable, body,
    and precondition invariants; Lambda-specific evaluator invariants; and the
    generated-prefix guard on `typeArgs`. In particular, `body_freevars` and
    `precond_freevars` ensure that the body and preconditions have no free
    variables beyond the function's inputs. -/
structure LFuncWF {T : LExprParams} (f : LFunc T) extends
    FuncWF
      (fun id => id.name) -- getName
      (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
      (fun e => e.freeVars) -- getTyFreeVars
      f.toFunc where
  /-- Constructors must not have a body or concreteEval. This ensures that
      values (which include fully-applied constructors) are normal
      forms — they cannot be further reduced by `expand_fn` or `eval_fn`. -/
  constr_no_eval :
    f.isConstr → f.body = none ∧ f.concreteEval = none := by decide
  /-- Type arguments must not start with the reserved generated-variable
      prefix `$__ty` used by the type-checker. -/
  typeArgs_no_gen_prefix :
    ∀ ta, ta ∈ f.typeArgs → ¬ (genTyPrefix.toList.isPrefixOf ta.toList = true) := by decide
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
  /-- The concrete evaluator of a `shortCircuit` function, which `eval` applies to
      arguments after the first one that are not evaluated yet, commutes with
      `substFvars` applied to those arguments, for any substitution `sm`. -/
  shortCircuit_substFvars :
    Strata.DL.Util.FuncAttr.hasShortCircuit f.attr = true →
      ∀ ceval, f.concreteEval = some ceval →
      ∀ [DecidableEq T.IDMeta] md (a : LExpr T.mono) (rest : List (LExpr T.mono))
        (sm : Map T.Identifier (LExpr T.mono)),
        ceval md (a :: rest.map (LExpr.substFvars · sm)) =
          (ceval md (a :: rest)).map (LExpr.substFvars · sm) := by
    intro h c hc
    first
      | (simp [Strata.DL.Util.FuncAttr.hasShortCircuit] at h; done)
      | (simp [LFunc.concreteEval] at hc; done)
      | (exfalso; revert h; decide)

/-- Well-formedness of a function's type signature: distinct type arguments,
    none with the reserved prefix `$__ty`, covering the input and output type
    variables. -/
structure LFuncSigWF {T : LExprParams} (f : LFunc T) : Prop where
  typeArgs_nodup : List.Nodup f.typeArgs
  typeArgs_no_gen_prefix :
    ∀ ta, ta ∈ f.typeArgs → ¬ (genTyPrefix.toList.isPrefixOf ta.toList = true)
  inputs_typevars_in_typeArgs :
    ∀ ty, ty ∈ f.inputs.values → ty.freeVars ⊆ f.typeArgs
  output_typevars_in_typeArgs : f.output.freeVars ⊆ f.typeArgs

/-- An LFunc bundled with its well-formedness proof. -/
structure WFLFunc (T : LExprParams) where
  func : LFunc T
  wf : LFuncWF func

/-- The name of the underlying LFunc. -/
def WFLFunc.name (f : WFLFunc T) : T.Identifier := f.func.name

/-- The operator expression for the underlying LFunc. -/
@[expose] def WFLFunc.opExpr [Inhabited T.Metadata] (f : WFLFunc T) : LExpr T.mono :=
  f.func.opExpr

/-- An array-backed factory whose functions each carry an `LFuncWF` proof.
    Function names are unique. -/
structure WFLFactory (T : LExprParams) where
  toFactory : Factory T
  wf : ∀(func : LFunc T), func ∈ toFactory.toArray → LFuncWF func

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
        simp only [Array.toList_map, List.map_map, a]
        exact name_nodup
      have mem_a := Factory.ofArray_mem mem
      simp only [Array.mem_map, a] at mem_a
      have ⟨⟨func2, func2WF⟩, wfMem⟩ := mem_a
      grind
  }

/--
Well-formedness properties of a factory.
-/
structure FactoryWF {T} (fac : Factory T) where
  lfuncs_wf : ∀ (lf:LFunc T), lf ∈ fac.toArray → LFuncWF lf

/-- Every function of the factory has a well-formed type signature. -/
structure FactorySigWF {T} (fac : Factory T) : Prop where
  lfuncs_wf : ∀ (lf : LFunc T), lf ∈ fac.toArray → LFuncSigWF lf

@[simp]
theorem WFLFactory.toFactory_wf {T} (wf : WFLFactory T) : FactoryWF wf.toFactory :=
  { lfuncs_wf := wf.wf }

/--
No constructor of `fac` produces a Boolean: the output type of every function
marked `isConstr` differs from `bool` under every type substitution. Then the
only values of type `bool` are the two Boolean constants.
-/
@[expose] def Factory.ConstrsNotBool {T} (fac : Factory T) : Prop :=
  ∀ fn ∈ fac.toArray, fn.isConstr = true → ∀ S, LMonoTy.subst S fn.output ≠ .bool

end -- public section
end Lambda

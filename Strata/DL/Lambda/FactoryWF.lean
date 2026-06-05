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
open Strata.DL.Util (Func FuncWF TyIdentifier)

public section


/-- Well-formedness properties for LFunc — extends generic `FuncWF` with
    Lambda-specific extractors and the generated-prefix guard on `typeArgs`. -/
structure LFuncWF {T : LExprParams} (f : LFunc T) extends
    FuncWF
      (fun id => id.name) -- getName
      (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
      (fun e => e.freeVars) -- getTyFreeVars
      f where
  /-- Constructors must not have a body or concreteEval. This ensures that
      canonical values (which include fully-applied constructors) are normal
      forms — they cannot be further reduced by `expand_fn` or `eval_fn`. -/
  constr_no_eval :
    f.isConstr → f.body = none ∧ f.concreteEval = none := by decide
  /-- Type arguments must not start with the reserved generated-variable
      prefix `$__ty` used by the type-checker. -/
  typeArgs_no_gen_prefix :
    ∀ ta, ta ∈ f.typeArgs → ¬ ("$__ty".toList.isPrefixOf ta.toList = true) := by decide
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
    intro _ h; simp [Func.concreteEval] at h

/-- An LFunc bundled with its well-formedness proof. -/
structure WFLFunc (T : LExprParams) where
  func : LFunc T
  wf : LFuncWF func

/-- The name of the underlying LFunc. -/
def WFLFunc.name (f : WFLFunc T) : T.Identifier := f.func.name

/-- The operator expression for the underlying LFunc. -/
def WFLFunc.opExpr [Inhabited T.Metadata] (f : WFLFunc T) : LExpr T.mono :=
  f.func.opExpr

/-- An array of well-formed LFuncs with a proof that function
    names are unique. -/
structure WFLFactory (T : LExprParams) where
  toFactory : Factory T
  wf : ∀(func : LFunc T), func ∈ toFactory.toArray → LFuncWF func

/-- Construct a `WFLFactory` from an array of `WFLFunc`s.
    The `name_nodup` proof defaults to `by decide`. -/
def WFLFactory.ofArray {T} (funcs : Array (WFLFunc T))
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
      have ⟨⟨func2, func2WF⟩, wfMem⟩ := mem_a
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

end -- public section
end Lambda

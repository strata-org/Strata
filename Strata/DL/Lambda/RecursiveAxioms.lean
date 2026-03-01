/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Util.List

/-!
## Axiom Generation for Recursive Functions

Given a recursive function with a `decreases` parameter over an algebraic datatype,
generates per-constructor axioms. Each axiom is a quantified equation:

  ∀ (other_params..., fields...). f(..., C(fields...), ...) = PE(f(..., C(fields...), ...))

The LHS is left unevaluated (it serves as the trigger pattern). The RHS is obtained by
passing the LHS to the partial evaluator, which inlines the function (since the recursive
argument is a constructor application) and reduces.
-/

namespace Lambda

open Std (Format format)
open Strata.DL.Util (FuncAttr)

/-- Check well-formedness of a recursive function and extract the components
    needed for axiom generation: recParam index and datatype.
    The `inlineIfConstr` attribute must have been previously set by `addFactoryFunc`
    (which resolves the `decreases` expression to a parameter index). -/
def checkRecursiveFunc [DecidableEq T.IDMeta]
    (func : LFunc T) (tf : @TypeFactory T.IDMeta)
    : Except Format (Nat × LDatatype T.IDMeta) := do
  if func.inputs.isEmpty then
    .error f!"Recursive function {func.name} must have at least one parameter"
  let recIdx ← FuncAttr.findInlineIfConstr func.attr |>.elim
    (.error f!"Recursive function {func.name} has no inlineIfConstr attribute") .ok
  let inputTys := func.inputs.values
  let recTy ← inputTys[recIdx]? |>.elim
    (.error f!"Recursive function {func.name}: recParam index {recIdx} out of bounds") .ok
  let dtName ← match recTy with
    | LMonoTy.tcons n _ => .ok n
    | _ => .error f!"Recursive function {func.name}: decreases parameter type is not a datatype"
  let dt ← tf.getType dtName |>.elim
    (.error f!"Recursive function {func.name}: datatype {dtName} not found") .ok
  return (recIdx, dt)

/-- Generate per-constructor axiom LExprs for a recursive function.
    Assumes the function is well-formed (use `checkRecursiveFunc` first).
    The PE must have the function in its factory with `inlineIfConstr`. -/
def mkRecursiveAxioms [Inhabited T.Metadata] [DecidableEq T.Metadata] [DecidableEq T.IDMeta]
    (func : LFunc T) (recIdx : Nat) (dt : LDatatype T.IDMeta)
    (pe : LExpr T.mono → LExpr T.mono) (m : T.Metadata)
    : Except Format (List (LExpr T.mono)) :=
  let formals := func.inputs.keys
  let inputTys := func.inputs.values
  dt.constrs.mapM fun c => do
    let numFields := c.args.length
    let totalBvs := numFields + formals.length - 1
    -- Binding order (outermost → innermost): other params, then constructor fields.
    -- Example: lookup(key:int, xs:IntList) with recIdx=1, Cons(hd,tl):
    --   ∀ key:int. ∀ hd:int. ∀ tl:IntList. lookup(key=%2, Cons(hd=%1, tl=%0)) = ...
    let dtTy : LMonoTy := .tcons dt.name []
    let constrTy := c.args.foldr (fun (_, argTy) acc => .arrow argTy acc) dtTy
    let constrApp := c.args.foldlIdx (fun acc i _ =>
      .app m acc (.bvar m (numFields - 1 - i))
    ) (.op m c.name (.some constrTy) : LExpr T.mono)
    let otherIdx (idx : Nat) : Nat := if idx < recIdx then idx else idx - 1
    let formalExpr (idx : Nat) : LExpr T.mono :=
      if idx == recIdx then constrApp
      else .bvar m (totalBvs - 1 - otherIdx idx)
    -- LHS: f(bvars..., C(fields...), bvars...) — not PE'd (serves as trigger)
    let lhs := formals.foldlIdx (fun acc idx _ =>
      .app m acc (formalExpr idx)
    ) (LFunc.opExpr func)
    -- RHS: PE inlines the function since the recursive arg is a constructor
    let rhs := pe lhs
    if lhs == rhs then
      .error f!"Recursive function {func.name}: PE did not reduce axiom for \
               constructor {c.name}. Ensure the function is in the factory with inlineIfConstr."
    let eq : LExpr T.mono := .eq m lhs rhs
    -- Wrap in quantifiers innermost-first: fields (with trigger on innermost),
    -- then other params.
    let allTys := (c.args.map (·.snd)).reverse ++ (inputTys.eraseIdx recIdx).reverse
    match allTys with
    | [] => .ok eq
    | ty :: rest =>
      let inner := LExpr.quant m .all (.some ty) lhs eq
      .ok (rest.foldl (fun body ty =>
        .quant m .all (.some ty) (LExpr.noTrigger m) body
      ) inner)

/-- Generate per-constructor axiom LExprs for a recursive function,
    including well-formedness checking. -/
def genRecursiveAxioms [Inhabited T.Metadata] [DecidableEq T.Metadata] [DecidableEq T.IDMeta]
    (func : LFunc T) (tf : @TypeFactory T.IDMeta)
    (pe : LExpr T.mono → LExpr T.mono) (m : T.Metadata)
    : Except Format (List (LExpr T.mono)) := do
  let (recIdx, dt) ← checkRecursiveFunc func tf
  mkRecursiveAxioms func recIdx dt pe m

end Lambda

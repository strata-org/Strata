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

/-- Check well-formedness of a recursive function and extract the components
    needed for axiom generation: recParam index and datatype. -/
def checkRecursiveFunc [DecidableEq T.IDMeta]
    (func : LFunc T) (tf : @TypeFactory T.IDMeta)
    : Except String (Nat × LDatatype T.IDMeta) := do
  let recIdx ← func.recParam |>.elim (.error s!"Recursive function {func.name} has no recParam") .ok
  let inputTys := func.inputs.values
  let recTy ← inputTys[recIdx]? |>.elim
    (.error s!"Recursive function {func.name}: recParam index {recIdx} out of bounds") .ok
  let dtName ← match recTy with
    | .tcons n _ => .ok n
    | _ => .error s!"Recursive function {func.name}: decreases parameter type is not a datatype"
  let dt ← tf.getType dtName |>.elim
    (.error s!"Recursive function {func.name}: datatype {dtName} not found") .ok
  return (recIdx, dt)

/-- Generate per-constructor axiom LExprs for a recursive function.
    Assumes the function is well-formed (use `checkRecursiveFunc` first). -/
def mkRecursiveAxioms [Inhabited T.Metadata] [DecidableEq T.IDMeta]
    (func : LFunc T) (recIdx : Nat) (dt : LDatatype T.IDMeta)
    (pe : LExpr T.mono → LExpr T.mono)
    : List (LExpr T.mono) :=
  let formals := func.inputs.keys
  let inputTys := func.inputs.values
  dt.constrs.map fun c =>
    let numFields := c.args.length
    let numOtherParams := formals.length - 1
    let totalBvs := numFields + numOtherParams
    let m : T.Metadata := default
    /-Binding order (outermost → innermost): other params, then constructor fields. Example: lookup(key:int, xs:IntList) with recIdx=1, Cons(hd,tl):
    ∀ key:int. ∀ hd:int. ∀ tl:IntList. lookup(key=%2, Cons(hd=%1, tl=%0)) = ... -/
    let constrOp : LExpr T.mono := .op m c.name none
    let constrApp := c.args.foldlIdx (fun acc i _ =>
      .app m acc (.bvar m (numFields - 1 - i))
    ) constrOp
    -- Map each formal to its bvar or the constructor application
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
    let eq : LExpr T.mono := .eq m lhs rhs
    -- Wrap in quantifiers innermost-first: fields (with trigger on innermost),
    -- then other params.
    let allTys := (c.args.map (·.snd)).reverse ++ (inputTys.eraseIdx recIdx).reverse
    match allTys with
    | [] => eq
    | ty :: rest =>
      let inner := LExpr.quant m .all (.some ty) lhs eq
      rest.foldl (fun body ty =>
        .quant m .all (.some ty) (LExpr.noTrigger m) body
      ) inner

/-- Generate per-constructor axiom LExprs for a recursive function,
    including well-formedness checking. -/
def genRecursiveAxioms [Inhabited T.Metadata] [DecidableEq T.IDMeta]
    (func : LFunc T) (tf : @TypeFactory T.IDMeta)
    (pe : LExpr T.mono → LExpr T.mono)
    : Except String (List (LExpr T.mono)) := do
  let (recIdx, dt) ← checkRecursiveFunc func tf
  return mkRecursiveAxioms func recIdx dt pe

end Lambda

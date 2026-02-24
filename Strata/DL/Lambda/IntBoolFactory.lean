/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LState
import Strata.DL.Lambda.FactoryWF

/-! ## A Minimal Factory with Support for Unbounded Integer and Boolean Operations

See also `Strata.DL.Lambda.Factory`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open LExpr LTy

section IntBoolFactory

-- Inhabited T.IDMeta is needed for the arg_nodup proofs in WFLFunc.
variable {T : LExprParams} [Inhabited T.IDMeta]

open Strata.DL.Util (Func FuncWF FuncPrecondition TyIdentifier)

/--
A typeclass that bundles `mkConst` and `cevalTy` for a given
`(LMonoTy, ValTy)` pair, allowing eval combinators to infer them
automatically.
-/
class LambdaLeanType (ty : outParam LMonoTy) (ValTy : Type) where
  mkConst : ∀(T : LExprParams), T.Metadata → ValTy → LExpr T.mono
  cevalTy : ∀(T : LExprParams), LExpr T.mono → Option ValTy

instance : LambdaLeanType .int Int where
  mkConst T := @intConst T.mono
  cevalTy _ := LExpr.denoteInt

instance : LambdaLeanType .bool Bool where
  mkConst T := @boolConst T.mono
  cevalTy _ := LExpr.denoteBool

instance : LambdaLeanType .string String where
  mkConst T := @LExpr.strConst T.mono
  cevalTy _ := LExpr.denoteString

instance (n : Nat) : LambdaLeanType (.bitvec n) (BitVec n) where
  mkConst _ m v := LExpr.bitvecConst m n v
  cevalTy _ := LExpr.denoteBitVec n

/-! ### Uneval combinators (no concrete evaluation)

These build well-formed `WFLFunc`s that have no `concreteEval` or `body`. -/

/-- General polymorphic unevaluated function with optional axioms.
    Handles any arity and any number of type arguments. -/
@[inline]
def polyUneval (n : T.Identifier) (typeArgs : List String)
    (inputs : List (T.Identifier × LMonoTy)) (output : LMonoTy)
    (axioms : List (LExpr T.mono) := [])
    (h_nodup : List.Nodup (inputs.map (·.1.name)) := by first | decide | grind)
    (h_ta_nodup : List.Nodup typeArgs := by grind)
    (h_inputs : ∀ ty, ty ∈ ListMap.values inputs →
      ty.freeVars ⊆ typeArgs := by first | decide | grind)
    (h_output : output.freeVars ⊆ typeArgs
      := by first | decide | grind) : WFLFunc T :=
  ⟨{ name := n, typeArgs := typeArgs, inputs := inputs, output := output,
     axioms := axioms }, {
    arg_nodup := h_nodup
    body_freevars := by intro b hb; simp at hb
    concreteEval_argmatch := by intro fn _ _ _ hfn; simp at hfn
    body_or_concreteEval := by simp
    typeArgs_nodup := h_ta_nodup
    inputs_typevars_in_typeArgs := h_inputs
    output_typevars_in_typeArgs := h_output
    precond_freevars := by intro p hp; simp at hp
  }⟩

/-- Nullary unevaluated function (0 inputs). -/
@[inline]
def nullaryUneval (n : T.Identifier) (ty : LMonoTy)
    (hty : ty.freeVars = [] := by decide) : WFLFunc T :=
  polyUneval n [] [] ty
    (h_inputs := by intro _ h; simp [ListMap.values] at h)

/-- Unary unevaluated function with mixed input/output types. -/
@[inline]
def unaryFuncUneval (n : T.Identifier) (inTy outTy : LMonoTy)
    (hInTy : inTy.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide) : WFLFunc T :=
  polyUneval n [] [("x", inTy)] outTy
    (h_inputs := by
      intro ty hty; simp [ListMap.values] at hty
      subst hty; simp [hInTy])


/-- Binary unevaluated function with heterogeneous input types. -/
@[inline]
def binaryFuncUneval (n : T.Identifier) (inTy1 inTy2 outTy : LMonoTy)
    (hInTy1 : inTy1.freeVars = [] := by decide)
    (hInTy2 : inTy2.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide) : WFLFunc T :=
  polyUneval n [] [("x", inTy1), ("y", inTy2)] outTy
    (h_inputs := by
      intro ty hty; simp [ListMap.values] at hty
      rcases hty with rfl | rfl <;> simp [*])


/-- Ternary unevaluated function with mixed input types.
    First input has type `inTy1`; second and third share type `inTy2`. -/
@[inline]
def ternaryFuncUneval (n : T.Identifier) (inTy1 inTy2 outTy : LMonoTy)
    (hInTy1 : inTy1.freeVars = [] := by decide)
    (hInTy2 : inTy2.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide) : WFLFunc T :=
  polyUneval n [] [("x", inTy1), ("y", inTy2), ("z", inTy2)] outTy
    (h_inputs := by
      intro ty hty; simp [ListMap.values] at hty
      rcases hty with rfl | rfl | rfl <;> simp [*])

/-! ### Eval combinators (with concrete evaluation)

These build well-formed `WFLFunc`s with a `concreteEval` for constant folding.
Types are resolved via `LambdaLeanType` instances. -/

/-! #### Unary -/

/-- Unary operation with mixed input/output types and concrete evaluation.
    Types are resolved via `LambdaLeanType` instances. -/
@[inline]
def unaryOp (n : T.Identifier)
    {inTy outTy InValTy OutValTy} [ToString OutValTy]
    [hIn : LambdaLeanType inTy InValTy] [hOut : LambdaLeanType outTy OutValTy]
    (op : InValTy → OutValTy)
    (hInTy : inTy.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide) : WFLFunc T :=
  let mkConst := LambdaLeanType.mkConst (ValTy := OutValTy) T
  let cevalInTy := LambdaLeanType.cevalTy (ValTy := InValTy) T
  ⟨{ name := n,
     inputs := [("x", inTy)],
     output := outTy,
     concreteEval := some (fun md args => match args with
       | [x] => match cevalInTy x with
         | some a => .some (mkConst md (op a))
         | _ => .none
       | _ => none) }, {
    arg_nodup := by simp
    body_freevars := by intro b hb; simp at hb
    concreteEval_argmatch := by
      intro fn md args res hfn heval
      simp at hfn; subst hfn
      match args with
      | [] | _ :: _ :: _ => simp at heval
      | [_] => rfl
    body_or_concreteEval := by simp
    typeArgs_nodup := by simp
    inputs_typevars_in_typeArgs := by
      intro ity hity; simp [ListMap.values] at hity; subst hity; simp [hInTy]
    output_typevars_in_typeArgs := by simp [hOutTy]
    precond_freevars := by intro p hp; simp at hp
  }⟩

/-! #### Binary -/

/-- Binary operation with mixed input/output types, optional guard,
    optional preconditions, and concrete evaluation. The guard is
    checked on the second argument; `none` is returned if it
    fails. -/
@[inline]
def binaryOp (n : T.Identifier)
    {inTy outTy InValTy OutValTy} [ToString OutValTy]
    [hIn : LambdaLeanType inTy InValTy]
    [hOut : LambdaLeanType outTy OutValTy]
    (op : InValTy → InValTy → OutValTy)
    (guard : InValTy → Bool := fun _ => true)
    (preconditions :
      List (FuncPrecondition (LExpr T.mono) T.Metadata) := [])
    (hInTy : inTy.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide)
    (h_precond : ∀ p, p ∈ preconditions →
      (LExpr.freeVars p.expr).map (·.1.name) ⊆ ["x", "y"]
      := by simp) : WFLFunc T :=
  let mkConst := LambdaLeanType.mkConst (ValTy := OutValTy) T
  let cevalInTy := LambdaLeanType.cevalTy (ValTy := InValTy) T
  ⟨{ name := n,
     inputs := [("x", inTy), ("y", inTy)],
     output := outTy,
     preconditions := preconditions,
     concreteEval := some (fun md args => match args with
       | [x, y] => match cevalInTy x, cevalInTy y with
         | some a, some b =>
           if guard b then mkConst md (op a b) else .none
         | _, _ => .none
       | _ => none) }, {
    arg_nodup := by simp
    body_freevars := by intro b hb; simp at hb
    concreteEval_argmatch := by
      intro fn md args res hfn heval
      simp at hfn; subst hfn
      match args with
      | [] | [_] | _ :: _ :: _ :: _ => simp at heval
      | [_, _] => rfl
    body_or_concreteEval := by simp
    typeArgs_nodup := by simp
    inputs_typevars_in_typeArgs := by
      intro ity hity; simp [ListMap.values] at hity
      rcases hity with rfl | rfl <;> simp [hInTy]
    output_typevars_in_typeArgs := by simp [hOutTy]
    precond_freevars := h_precond
  }⟩

/-! ### Integer Arithmetic Operations -/

def intAddFunc : WFLFunc T :=
  binaryOp "Int.Add" Int.add

def intSubFunc : WFLFunc T :=
  binaryOp "Int.Sub" Int.sub

def intMulFunc : WFLFunc T :=
  binaryOp "Int.Mul" Int.mul

def intDivFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.Div" (· / ·) (· != 0)

def intModFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.Mod" (· % ·) (· != 0)

def intDivTFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.DivT" Int.tdiv (· != 0)

def intModTFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.ModT" Int.tmod (· != 0)

def intNegFunc : WFLFunc T :=
  unaryOp "Int.Neg" Int.neg

def intLtFunc : WFLFunc T :=
  binaryOp (InValTy := Int) (OutValTy := Bool) "Int.Lt" (· < ·)

def intLeFunc : WFLFunc T :=
  binaryOp (InValTy := Int) (OutValTy := Bool) "Int.Le" (· ≤ ·)

def intGtFunc : WFLFunc T :=
  binaryOp (InValTy := Int) (OutValTy := Bool) "Int.Gt" (· > ·)

def intGeFunc : WFLFunc T :=
  binaryOp (InValTy := Int) (OutValTy := Bool) "Int.Ge" (· ≥ ·)

/-! ### Boolean Operations -/

def boolAndFunc : WFLFunc T :=
  binaryOp "Bool.And" Bool.and

def boolOrFunc : WFLFunc T :=
  binaryOp "Bool.Or" Bool.or

def boolImpliesFunc : WFLFunc T :=
  binaryOp (InValTy := Bool) "Bool.Implies" (!· || ·)

def boolEquivFunc : WFLFunc T :=
  binaryOp (InValTy := Bool) "Bool.Equiv" (· == ·)

def boolNotFunc : WFLFunc T :=
  unaryOp "Bool.Not" Bool.not

/-! ### Safe (preconditioned) operations -/

section

variable [Inhabited T.mono.base.Metadata]

private def yNeZeroPrecond :
    FuncPrecondition (LExpr T.mono) T.Metadata :=
  let yVar : LExpr T.mono := .fvar default "y" (some .int)
  let zero : LExpr T.mono := .intConst default 0
  ⟨.app default boolNotFunc.func.opExpr
      (.eq default yVar zero), default⟩

@[simp]
private theorem yNeZeroPrecond_freeVars :
    (yNeZeroPrecond (T := T)).expr.freeVars = [(⟨"y", default⟩, some LMonoTy.int)] := by
  simp [yNeZeroPrecond, LExpr.freeVars,
    LFunc.opExpr, boolNotFunc, unaryOp]

def intSafeDivFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.SafeDiv" (· / ·) (· != 0)
    (preconditions := [yNeZeroPrecond])

def intSafeModFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.SafeMod" (· % ·) (· != 0)
    (preconditions := [yNeZeroPrecond])

end

def IntBoolFactory [Inhabited T.mono.base.Metadata] : @Factory T := (#[
    intAddFunc,
    intSubFunc,
    intMulFunc,
    intDivFunc,
    intSafeDivFunc,
    intModFunc,
    intSafeModFunc,
    intDivTFunc,
    intModTFunc,
    intNegFunc,
    intLtFunc,
    intLeFunc,
    intGtFunc,
    intGeFunc,

    boolAndFunc,
    boolOrFunc,
    boolImpliesFunc,
    boolEquivFunc,
    boolNotFunc,
  ] : Array (WFLFunc T)).map (·.func)

end IntBoolFactory

---------------------------------------------------------------------

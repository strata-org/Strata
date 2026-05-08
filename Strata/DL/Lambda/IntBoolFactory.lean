/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LState
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Util.ListMap

/-! ## A Minimal Factory with Support for Unbounded Integer and Boolean Operations

See also `Strata.DL.Lambda.Factory`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open LExpr LTy

public section

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
  /-- `cevalTy` is metadata-insensitive: expressions with the same
      `eraseMetadata` yield the same result. -/
  cevalTy_eraseMetadata :
    ∀ (T : LExprParams) (e1 e2 : LExpr T.mono),
      LExpr.eraseMetadata e1 = LExpr.eraseMetadata e2 →
      cevalTy T e1 = cevalTy T e2
  /-- `mkConst` after `eraseMetadata` is independent of the metadata argument. -/
  mkConst_eraseMetadata :
    ∀ (T : LExprParams) (md1 md2 : T.Metadata) (v : ValTy),
      LExpr.eraseMetadata (mkConst T md1 v) = LExpr.eraseMetadata (mkConst T md2 v)

private theorem cevalTy_of_eraseMetadata_eq
    {T : LExprParams}
    (f : LExpr T.mono → Option V)
    (hf_const : ∀ (m1 m2 : T.Metadata) (c : LConst), f (.const m1 c) = f (.const m2 c))
    (hf_non_const : ∀ e, (∀ m c, e ≠ .const m c) → f e = none)
    (e1 e2 : LExpr T.mono)
    (h : LExpr.eraseMetadata e1 = LExpr.eraseMetadata e2) :
    f e1 = f e2 := by
  cases e1 <;> cases e2 <;>
    simp_all [LExpr.eraseMetadata, LExpr.replaceMetadata]
  next m1 _ m2 _ => exact hf_const m1 m2 _

instance : LambdaLeanType .int Int where
  mkConst T := @intConst T.mono
  cevalTy _ := LExpr.denoteInt
  cevalTy_eraseMetadata := by
    intro T e1 e2 h
    exact cevalTy_of_eraseMetadata_eq LExpr.denoteInt
      (by intro m1 m2 c; cases c <;> simp [LExpr.denoteInt])
      (by intro e he; cases e <;> simp_all [LExpr.denoteInt])
      e1 e2 h
  mkConst_eraseMetadata := by
    intro T md1 md2 v
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata]

instance : LambdaLeanType .bool Bool where
  mkConst T := @boolConst T.mono
  cevalTy _ := LExpr.denoteBool
  cevalTy_eraseMetadata := by
    intro T e1 e2 h
    exact cevalTy_of_eraseMetadata_eq LExpr.denoteBool
      (by intro m1 m2 c; cases c <;> simp [LExpr.denoteBool])
      (by intro e he; cases e <;> simp_all [LExpr.denoteBool])
      e1 e2 h
  mkConst_eraseMetadata := by
    intro T md1 md2 v
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata]

instance : LambdaLeanType .string String where
  mkConst T := @LExpr.strConst T.mono
  cevalTy _ := LExpr.denoteString
  cevalTy_eraseMetadata := by
    intro T e1 e2 h
    exact cevalTy_of_eraseMetadata_eq LExpr.denoteString
      (by intro m1 m2 c; cases c <;> simp [LExpr.denoteString])
      (by intro e he; cases e <;> simp_all [LExpr.denoteString])
      e1 e2 h
  mkConst_eraseMetadata := by
    intro T md1 md2 v
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata]

instance (n : Nat) : LambdaLeanType (.bitvec n) (BitVec n) where
  mkConst _ m v := LExpr.bitvecConst m n v
  cevalTy _ := LExpr.denoteBitVec n
  cevalTy_eraseMetadata := by
    intro T e1 e2 h
    exact cevalTy_of_eraseMetadata_eq (LExpr.denoteBitVec n)
      (by intro m1 m2 c; cases c <;> simp [LExpr.denoteBitVec])
      (by intro e he; cases e <;> simp_all [LExpr.denoteBitVec])
      e1 e2 h
  mkConst_eraseMetadata := by
    intro T md1 md2 v
    simp [LExpr.eraseMetadata, LExpr.replaceMetadata]

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
      := by first | decide | grind)
    (h_ta_no_gen : ∀ ta, ta ∈ typeArgs → ¬ ("$__ty".toList.isPrefixOf ta.toList = true)
      := by first | decide | grind) : WFLFunc T :=
  ⟨{ name := n, typeArgs := typeArgs, inputs := inputs, output := output,
     axioms := axioms }, {
    arg_nodup := h_nodup
    body_freevars := by intro b hb; simp at hb
    concreteEval_argmatch := by intro fn _ _ _ hfn; simp at hfn
    body_or_concreteEval := by simp
    constr_no_eval := by simp
    typeArgs_nodup := h_ta_nodup
    inputs_typevars_in_typeArgs := h_inputs
    output_typevars_in_typeArgs := h_output
    precond_freevars := by intro p hp; simp at hp
    typeArgs_no_gen_prefix := h_ta_no_gen
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

/-! #### Parameter name constants

These are used by `unaryOp`/`binaryOp` for their input parameter names,
and must be referenced by any code constructing precondition expressions
(e.g., `Factory.lean` overflow check preconditions). -/

/-- Parameter name for unary operations. -/
def unaryParamName : String := "x"
/-- First parameter name for binary operations. -/
def binaryParam1Name : String := "x"
/-- Second parameter name for binary operations. -/
def binaryParam2Name : String := "y"

/-! #### Unary -/

/-- Unary operation with mixed input/output types and concrete evaluation.
    Types are resolved via `LambdaLeanType` instances. -/
@[inline]
def unaryOp (n : T.Identifier)
    {inTy outTy InValTy OutValTy} [ToString OutValTy]
    [hIn : LambdaLeanType inTy InValTy] [hOut : LambdaLeanType outTy OutValTy]
    (op : InValTy → OutValTy)
    (preconditions :
      List (FuncPrecondition (LExpr T.mono) T.Metadata) := [])
    (hInTy : inTy.freeVars = [] := by decide)
    (hOutTy : outTy.freeVars = [] := by decide)
    (h_precond : ∀ p, p ∈ preconditions →
      (LExpr.freeVars p.expr).map (·.1.name) ⊆ [unaryParamName]
      := by simp [unaryParamName]) : WFLFunc T :=
  let mkConst := LambdaLeanType.mkConst (ValTy := OutValTy) T
  let cevalInTy := LambdaLeanType.cevalTy (ValTy := InValTy) T
  ⟨{ name := n,
     inputs := [(unaryParamName, inTy)],
     output := outTy,
     preconditions := preconditions,
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
    precond_freevars := by
      intro p hp
      exact h_precond p hp
    typeArgs_no_gen_prefix := by simp
    constr_no_eval := by simp
    concreteEval_eraseMetadata := by
      intro ceval h md1 md2 args1 args2 res1 hmap heval
      simp at h; subst h
      match args1, heval with
      | [x1], heval =>
        have hlen : args2.length = 1 := by
          have := congrArg List.length hmap; simp at this; omega
        match args2, hlen with
        | [x2], _ =>
        simp [List.map] at hmap
        have hceq := hIn.cevalTy_eraseMetadata T x1 x2 hmap
        simp only [] at heval ⊢
        match hc1 : cevalInTy x1 with
        | none => simp [hc1] at heval
        | some a =>
          have hc2 : cevalInTy x2 = some a := by
            change LambdaLeanType.cevalTy T x2 = some a; rw [← hceq]; exact hc1
          simp only [hc2]
          simp only [hc1, Option.some.injEq] at heval; subst heval
          exact ⟨mkConst md2 (op a), rfl, hOut.mkConst_eraseMetadata T md1 md2 (op a)⟩
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
      (LExpr.freeVars p.expr).map (·.1.name) ⊆ [binaryParam1Name, binaryParam2Name]
      := by simp [binaryParam1Name, binaryParam2Name]) : WFLFunc T :=
  let mkConst := LambdaLeanType.mkConst (ValTy := OutValTy) T
  let cevalInTy := LambdaLeanType.cevalTy (ValTy := InValTy) T
  ⟨{ name := n,
     inputs := [(binaryParam1Name, inTy), (binaryParam2Name, inTy)],
     output := outTy,
     preconditions := preconditions,
     concreteEval := some (fun md args => match args with
       | [x, y] => match cevalInTy x, cevalInTy y with
         | some a, some b =>
           if guard b then mkConst md (op a b) else .none
         | _, _ => .none
       | _ => none) }, {
    arg_nodup := by simp [binaryParam1Name, binaryParam2Name]
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
    typeArgs_no_gen_prefix := by simp
    constr_no_eval := by simp
    concreteEval_eraseMetadata := by
      intro ceval h md1 md2 args1 args2 res1 hmap heval
      simp at h; subst h
      match args1, heval with
      | [x1, y1], heval =>
        have hlen : args2.length = 2 := by
          have := congrArg List.length hmap; simp at this; omega
        match args2, hlen with
        | [x2, y2], _ =>
          simp [List.map] at hmap
          obtain ⟨hxeq, hyeq⟩ := hmap
          have hcx := hIn.cevalTy_eraseMetadata T x1 x2 hxeq
          have hcy := hIn.cevalTy_eraseMetadata T y1 y2 hyeq
          simp only [] at heval ⊢
          match hcx1 : cevalInTy x1, hcy1 : cevalInTy y1 with
          | none, _ => simp [hcx1] at heval
          | some _, none => simp [hcy1] at heval
          | some a, some b =>
            have hcx2 : cevalInTy x2 = some a := by
              change LambdaLeanType.cevalTy T x2 = some a; rw [← hcx]; exact hcx1
            have hcy2 : cevalInTy y2 = some b := by
              change LambdaLeanType.cevalTy T y2 = some b; rw [← hcy]; exact hcy1
            simp only [hcx2, hcy2]
            simp only [hcx1, hcy1] at heval
            split at heval
            · rename_i hg
              simp only [Option.some.injEq] at heval; subst heval
              exact ⟨mkConst md2 (op a b), by simp [hg], hOut.mkConst_eraseMetadata T md1 md2 (op a b)⟩
            · simp at heval
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

def wrapImplications [Inhabited T.Metadata]
    (implications : List (T.Metadata × LExpr T.mono))
    (ob : LExpr T.mono) : LExpr T.mono :=
  implications.foldr (fun (md, lhs) acc =>
    .app md (.app md (@boolImpliesFunc T).opExpr lhs) acc) ob

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

def intSafeDivTFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.SafeDivT" Int.tdiv (· != 0)
    (preconditions := [yNeZeroPrecond])

def intSafeModTFunc : WFLFunc T :=
  binaryOp (InValTy := Int) "Int.SafeModT" Int.tmod (· != 0)
    (preconditions := [yNeZeroPrecond])

end

def IntBoolFactory [Inhabited T.mono.base.Metadata] : Factory T :=
  .ofArray <| (#[
    intAddFunc,
    intSubFunc,
    intMulFunc,
    intDivFunc,
    intSafeDivFunc,
    intModFunc,
    intSafeModFunc,
    intDivTFunc,
    intSafeDivTFunc,
    intModTFunc,
    intSafeModTFunc,
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

end -- public section

---------------------------------------------------------------------

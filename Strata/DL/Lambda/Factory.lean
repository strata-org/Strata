/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DDM.AST
import Strata.DDM.Util.Array
import Strata.DL.Util.Func
import Strata.DL.Util.List
import Strata.DL.Util.ListMap

/-!
## Lambda's Factory

This module formalizes Lambda's _factory_, which is a mechanism to extend the
type checker (see `Strata.DL.Lambda.LExprT`) and partial evaluator (see
`Strata.DL.Lambda.LExprEval`) by providing a map from operations to their types
and optionally, denotations. The factory allows adding type checking and
evaluation support for new operations without modifying the implementation of
either or any core ASTs.

Also see `Strata.DL.Lambda.IntBoolFactory` for a concrete example of a factory.
-/


namespace Lambda
open Strata
open Std (ToFormat Format format)

variable {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

---------------------------------------------------------------------

open LTy.Syntax

section Factory

variable {IDMeta : Type} [DecidableEq IDMeta] [Inhabited IDMeta]

/--
A signature is a map from variable identifiers to types.
-/
abbrev Signature (IDMeta : Type) (Ty : Type) := ListMap (Identifier IDMeta) Ty

def Signature.format (ty : Signature IDMeta Ty) [Std.ToFormat Ty] : Std.Format :=
  match ty with
  | [] => ""
  | [(k, v)] => f!"({k} : {v})"
  | (k, v) :: rest =>
    f!"({k} : {v}) " ++ Signature.format rest

abbrev LMonoTySignature := Signature IDMeta LMonoTy

abbrev LTySignature := Signature IDMeta LTy

def inline_attr : String := "inline"
def inline_if_constr_attr : String := "inline_if_constr"
def eval_if_constr_attr : String := "eval_if_constr"

-- Re-export Func from Util for backward compatibility
open Strata.DL.Util (Func FuncPrecondition TyIdentifier)

/--
A Lambda factory function - instantiation of `Func` for Lambda expressions.

Universally quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.
-/
abbrev LFunc (T : LExprParams) := Func (T.Identifier) (LExpr T.mono) LMonoTy T.Metadata

/--
Helper constructor for LFunc to maintain backward compatibility.
-/
def LFunc.mk {T : LExprParams} (name : T.Identifier) (typeArgs : List TyIdentifier := [])
    (isConstr : Bool := false) (inputs : ListMap T.Identifier LMonoTy) (output : LMonoTy)
    (body : Option (LExpr T.mono) := .none) (attr : Array String := #[])
    (concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none)
    (axioms : List (LExpr T.mono) := [])
    (preconditions : List (FuncPrecondition (LExpr T.mono) T.Metadata) := []) : LFunc T :=
  Func.mk name typeArgs isConstr inputs output body attr concreteEval axioms preconditions

instance [Inhabited T.Metadata] [Inhabited T.IDMeta] : Inhabited (LFunc T) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

-- Provide explicit instance for LFunc to ensure proper resolution
instance [ToFormat T.IDMeta] [Inhabited T.Metadata] : ToFormat (LFunc T) where
  format := Func.format

def LFunc.type [DecidableEq T.IDMeta] (f : (LFunc T)) : Except Format LTy := do
  if !(decide f.inputs.keys.Nodup) then
    .error f!"[{f.name}] Duplicates found in the formals!\
              {Format.line}\
              {f.inputs}"
  else if !(decide f.typeArgs.Nodup) then
    .error f!"[{f.name}] Duplicates found in the universally \
              quantified type identifiers!\
              {Format.line}\
              {f.typeArgs}"
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  match input_tys with
  | [] => .ok (.forAll f.typeArgs f.output)
  | ity :: irest =>
    .ok (.forAll f.typeArgs (Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)))

omit [Inhabited T.Metadata] [ToFormat T.IDMeta] in
theorem LFunc.type_inputs_nodup [DecidableEq T.IDMeta] (f : LFunc T) (ty : LTy) :
    f.type = .ok ty → f.inputs.keys.Nodup := by
  intro h
  simp only [LFunc.type, bind, Except.bind] at h
  -- At this point grind is possible if this proof needs maintenance
  split at h <;> try contradiction
  simp_all

def LFunc.opExpr [Inhabited T.Metadata] (f: LFunc T) : LExpr T.mono :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op (default : T.Metadata) f.name (some ty)

def LFunc.inputPolyTypes (f : (LFunc T)) : @LTySignature T.IDMeta :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFunc.outputPolyType (f : (LFunc T)) : LTy :=
  .forAll f.typeArgs f.output

def LFunc.eraseTypes (f : LFunc T) : LFunc T :=
  { f with
    body := f.body.map LExpr.eraseTypes,
    axioms := f.axioms.map LExpr.eraseTypes,
    preconditions := f.preconditions.map fun p => { p with expr := p.expr.eraseTypes }
  }

/--
The type checker and partial evaluator for Lambda is parameterizable by
a user-provided `Factory`.

We don't have any "built-in" functions like `+`, `-`, etc. in `(LExpr
IDMeta)` -- lambdas are our only tool. `Factory` gives us a way to add
support for concrete/symbolic evaluation and type checking for `FunFactory`
functions without actually modifying any core logic or the ASTs.
-/
def Factory (T : LExprParams) := Array (LFunc T)

def Factory.default : @Factory T := #[]

instance : Inhabited (@Factory T) where
  default := @Factory.default T

instance : Membership (LFunc T) (@Factory T) where
  mem x f := Array.Mem x f


def Factory.getFunctionNames (F : @Factory T) : Array T.Identifier :=
  F.map (fun f => f.name)

def Factory.getFactoryLFunc (F : @Factory T) (name : String) : Option (LFunc T) :=
  F.find? (fun fn => fn.name.name == name)

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def Factory.addFactoryFunc (F : @Factory T) (func : LFunc T) : Except DiagnosticModel (@Factory T) :=
  match F.getFactoryLFunc func.name.name with
  | none => .ok (F.push func)
  | some func' =>
    .error <| DiagnosticModel.fromFormat f!"A function of name {func.name} already exists! \
              Redefinitions are not allowed.\n\
              Existing Function: {func'}\n\
              New Function:{func}"


/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def Factory.addFactory (F newF : @Factory T) : Except DiagnosticModel (@Factory T) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF


def getLFuncCall {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) :=
  go e []
  where go e (acc : List (LExpr ⟨T, GenericTy⟩)) :=
  match e with
  | .app _ (.app _ e' arg1) arg2 =>  go e' ([arg1, arg2] ++ acc)
  | .app _ (.op m fn  fnty) arg1 =>  ((.op m fn fnty), ([arg1] ++ acc))
  | _ => (e, acc)

def getConcreteLFuncCall (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) :=
  let (op, args) := getLFuncCall e
  if args.all (@LExpr.isConst ⟨T, GenericTy⟩) then (op, args) else (e, [])

/--
If `e` is a call of a factory function, get the operator (`.op`), a list
of all the actuals, and the `(LFunc IDMeta)`.
-/
def Factory.callOfLFunc {GenericTy} (F : @Factory T) (e : LExpr ⟨T, GenericTy⟩)
    (allowPartialApp := false)
    : Option (LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) × LFunc T) :=
  let (op, args) := getLFuncCall e
  match op with
  | .op _ name _ =>
    let maybe_func := getFactoryLFunc F name.name
    match maybe_func with
    | none => none
    | some func =>
      -- Note that we don't do any type or well-formedness checking here; this
      -- is just a simple arity check.
      let matchesArg:Bool :=
        if allowPartialApp then Nat.ble args.length func.inputs.length
        else args.length == func.inputs.length
      match matchesArg with
      | true => (op, args, func) | false => none
  | _ => none

end Factory

theorem getLFuncCall.go_size {T: LExprParamsT} {e: LExpr T} {op args acc} : getLFuncCall.go e acc = (op, args) →
op.sizeOf + List.sum (args.map LExpr.sizeOf) <= e.sizeOf + List.sum (acc.map LExpr.sizeOf) := by
  fun_induction go generalizing op args
  case case1 acc e' arg1 arg2 IH =>
    intros Hgo; specialize (IH Hgo); simp_all; omega
  case case2 acc fn fnty arg1 =>
    simp_all; intros op_eq args_eq; subst op args; simp; omega
  case case3 op' args' _ _ => intros Hop; cases Hop; omega

theorem LExpr.sizeOf_pos {T} (e: LExpr T): 0 < sizeOf e := by
  cases e<;> simp <;> omega

theorem List.sum_size_le (f: α → Nat) {l: List α} {x: α} (x_in: x ∈ l): f x ≤ List.sum (l.map f) := by
  induction l; simp_all; grind

theorem getLFuncCall_smaller {T} {e: LExpr T} {op args} : getLFuncCall e = (op, args) → (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  unfold getLFuncCall; intros Hgo; have Hsize := (getLFuncCall.go_size Hgo);
  simp_all; have Hop:= LExpr.sizeOf_pos op; intros a a_in;
  have Ha := List.sum_size_le LExpr.sizeOf a_in; omega

theorem Factory.callOfLFunc_smaller {T} {F : @Factory T.base} {e : LExpr T} {op args F'}
    {allowPartialMatch}
    : Factory.callOfLFunc F e (allowPartialApp := allowPartialMatch) = some (op, args, F') →
  (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  simp[Factory.callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp; cases op <;> simp
  rename_i o ty; cases (F.getFactoryLFunc o.name) <;> simp
  rename_i F'
  cases allowPartialMatch
  · cases (args.length == List.length F'.inputs) <;> simp; intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)
  · cases (Nat.ble args.length (List.length F'.inputs)) <;> simp
    intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)

end Lambda

---------------------------------------------------------------------

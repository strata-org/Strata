/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DDM.AST
import Strata.DDM.Util.Array
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

/--
A Lambda factory function, where the body can be optional. Universally
quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.

A optional evaluation function can be provided in the `concreteEval` field for
each factory function to allow the partial evaluator to do constant propagation
when all the arguments of a function are concrete. Such a function should take
two inputs: a function call expression and also -- somewhat redundantly, but
perhaps more conveniently -- the list of arguments in this expression.  Here's
an example of a `concreteEval` function for `Int.Add`:

```
(fun e args => match args with
               | [e1, e2] =>
                 let e1i := LExpr.denoteInt e1
                 let e2i := LExpr.denoteInt e2
                 match e1i, e2i with
                 | some x, some y => (.const (toString (x + y)) mty[int])
                 | _, _ => e
               | _ => e)
```

Note that if there is an arity mismatch or if the arguments are not
concrete/constants, this fails and it returns .none.

(TODO) Use `.bvar`s in the body to correspond to the formals instead of using
`.fvar`s.
-/
structure LFunc (T : LExprParams) where
  name     : T.Identifier
  typeArgs : List TyIdentifier := []
  isConstr : Bool := false --whether function is datatype constructor
  inputs   : @LMonoTySignature T.IDMeta
  output   : LMonoTy
  body     : Option (LExpr T.mono) := .none
  -- (TODO): Add support for a fixed set of attributes (e.g., whether to inline
  -- a function, etc.).
  attr     : Array String := #[]
  -- The T.Metadata argument is the metadata that will be attached to the
  -- resulting expression of concreteEval if evaluation was successful.
  concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none
  axioms   : List (LExpr T.mono) := []  -- For axiomatic definitions

/--
Well-formedness properties of LFunc. These are split from LFunc because
otherwise it becomes impossible to create a 'temporary' LFunc object whose
wellformedness might not hold yet.
-/
structure LFuncWF {T : LExprParams} (f : LFunc T) where
  -- No args have same name.
  arg_nodup:
    List.Nodup (f.inputs.map (·.1.name))
  -- Free variables of body must be arguments.
  body_freevars:
    ∀ b freevars, f.body = .some b
      → freevars = LExpr.freeVars b
      → (∀ fv, fv ∈ freevars →
          ∃ arg, List.Mem arg f.inputs ∧ fv.1.name = arg.1.name)
  -- concreteEval does not succeed if the length of args is incorrect.
  concreteEval_argmatch:
    ∀ fn md args res, f.concreteEval = .some fn
      → fn md args = .some res
      → args.length = f.inputs.length

instance LFuncWF.arg_nodup_decidable {T : LExprParams} (f : LFunc T):
    Decidable (List.Nodup (f.inputs.map (·.1.name))) := by
  apply List.nodupDecidable

instance LFuncWF.body_freevars_decidable {T : LExprParams} (f : LFunc T):
    Decidable (∀ b freevars, f.body = .some b
      → freevars = LExpr.freeVars b
      → (∀ fv, fv ∈ freevars →
          ∃ arg, List.Mem arg f.inputs ∧ fv.1.name = arg.1.name)) :=
  match Hbody: f.body with
  | .some b =>
    if Hall:(LExpr.freeVars b).all
        (fun fv => List.any f.inputs (fun arg => fv.1.name == arg.1.name))
    then by
      apply isTrue
      intros b' freevars Hb' Hfreevars fv' Hmem
      cases Hb'
      rw [← Hfreevars] at Hall
      rw [List.all_eq_true] at Hall
      have Hall' := Hall fv' Hmem
      rw [List.any_eq_true] at Hall'
      rcases Hall' with ⟨arg', H⟩
      exists arg'
      solve | (simp at H ; congr)
    else by
      apply isFalse
      grind
  | .none => by
    apply isTrue; grind

-- LFuncWF.concreteEval_argmatch is not decidable.

instance [Inhabited T.Metadata] [Inhabited T.IDMeta] : Inhabited (LFunc T) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

instance : ToFormat (LFunc T) where
  format f :=
    let attr := if f.attr.isEmpty then f!"" else f!"@[{f.attr}]{Format.line}"
    let typeArgs := if f.typeArgs.isEmpty
                    then f!""
                    else f!"∀{f.typeArgs}."
    let type := f!"{typeArgs} ({Signature.format f.inputs}) → {f.output}"
    let sep := if f.body.isNone then f!";" else f!" :="
    let body := if f.body.isNone then f!"" else Std.Format.indentD f!"({f.body.get!})"
    f!"{attr}\
       func {f.name} : {type}{sep}\
       {body}"

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
    axioms := f.axioms.map LExpr.eraseTypes
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

/--
Well-formedness properties of Factory.
-/
structure FactoryWF {T : LExprParams} (fac:Factory T) where
  name_nodup:
    List.Nodup (fac.toList.map (·.name.name))
  lfuncs_wf:
    ∀ (lf:LFunc T), lf ∈ fac → LFuncWF lf

instance FactoryWF.name_nodup_decidable {T : LExprParams} (fac : Factory T):
    Decidable (List.Nodup (fac.toList.map (·.name.name))) := by
  apply List.nodupDecidable


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
If Factory.addFactoryFunc succeeds, and the input factory & LFunc were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactoryFunc_wf
  (F : @Factory T) (F_wf: FactoryWF F) (func : LFunc T) (func_wf: LFuncWF func):
  ∀ F', F.addFactoryFunc func = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactoryFunc
  unfold Factory.getFactoryLFunc
  intros F' Hmatch
  split at Hmatch -- Case-analysis on the match condition
  · rename_i heq
    cases Hmatch -- F' is Array.push F
    apply FactoryWF.mk
    · have Hnn := F_wf.name_nodup
      grind [Array.toList_push,List]
    · intros lf Hmem
      rw [Array.mem_push] at Hmem
      cases Hmem
      · have Hwf := F_wf.lfuncs_wf
        apply Hwf; assumption
      · grind
  · grind

/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def Factory.addFactory (F newF : @Factory T) : Except DiagnosticModel (@Factory T) :=
  Array.foldlM (fun factory func => factory.addFactoryFunc func) F newF


/--
If Factory.addFactory succeeds, and the input two factories were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactory_wf
  (F : @Factory T) (F_wf: FactoryWF F) (newF : @Factory T)
  (newF_wf: FactoryWF newF):
  ∀ F', F.addFactory newF = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactory
  rw [← Array.foldlM_toList]
  generalize Hl: newF.toList = l
  induction l generalizing newF F
  · rw [Array.toList_eq_nil_iff] at Hl
    rw [List.foldlM_nil]
    unfold Pure.pure Except.instMonad Except.pure
    grind
  · rename_i lf lf_tail tail_ih
    have Hl: newF = (List.toArray [lf]) ++ (List.toArray lf_tail) := by grind
    have Htail_wf: FactoryWF (lf_tail.toArray) := by
      rw [Hl] at newF_wf
      apply FactoryWF.mk
      · have newF_wf_name_nodup := newF_wf.name_nodup
        grind
      · intro lf
        have newF_wf_lfuncs_wf := newF_wf.lfuncs_wf lf
        intro Hmem
        apply newF_wf_lfuncs_wf
        apply Array.mem_append_right
        assumption
    have Hhead_wf: LFuncWF lf := by
      rw [Hl] at newF_wf
      have Hwf := newF_wf.lfuncs_wf
      apply Hwf
      apply Array.mem_append_left
      grind
    intro F'
    simp only [List.foldlM]
    unfold bind
    unfold Except.instMonad
    simp only []
    unfold Except.bind
    intro H
    split at H
    · contradiction
    · rename_i F_interm HaddFacFun
      have HF_interm_wf: FactoryWF F_interm := by
        apply (Factory.addFactoryFunc_wf F F_wf lf) <;> assumption
      simp only [] at H
      apply tail_ih F_interm HF_interm_wf (lf_tail.toArray) <;> grind


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

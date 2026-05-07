/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LTy
public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnify
public import Strata.DDM.AST
public import Strata.DDM.Util.Array
public import Strata.DL.Util.Func
public import Strata.DL.Util.List
public import Strata.DL.Util.ListMap

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

public section

---------------------------------------------------------------------

open LTy.Syntax

section Factory

/--
A signature is a map from variable identifiers to types.
-/
@[expose] abbrev Signature (IDMeta : Type) (Ty : Type) := ListMap (Identifier IDMeta) Ty

def Signature.format (ty : Signature IDMeta Ty) [Std.ToFormat Ty] : Std.Format :=
  match ty with
  | [] => ""
  | [(k, v)] => f!"({k} : {v})"
  | (k, v) :: rest =>
    f!"({k} : {v}) " ++ Signature.format rest

@[expose] abbrev LMonoTySignature {IDMeta : Type} := Signature IDMeta LMonoTy

@[expose] abbrev LTySignature {IDMeta : Type} := Signature IDMeta LTy

-- Re-export Func from Util for backward compatibility
open Strata.DL.Util (Func FuncPrecondition TyIdentifier)

/--
A Lambda factory function - instantiation of `Func` for Lambda expressions.

Universally quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.
-/
@[expose] abbrev LFunc (T : LExprParams) := Func (T.Identifier) (LExpr T.mono) LMonoTy T.Metadata

/--
Helper constructor for LFunc to maintain backward compatibility.
-/
@[expose] def LFunc.mk {T : LExprParams} (name : T.Identifier) (typeArgs : List TyIdentifier := [])
    (isConstr : Bool := false) (isRecursive : Bool := false)
    (inputs : ListMap T.Identifier LMonoTy) (output : LMonoTy)
    (body : Option (LExpr T.mono) := .none) (attr : Array Strata.DL.Util.FuncAttr := #[])
    (concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none)
    (axioms : List (LExpr T.mono) := [])
    (preconditions : List (FuncPrecondition (LExpr T.mono) T.Metadata) := []) : LFunc T :=
  Func.mk name typeArgs isConstr isRecursive inputs output body attr concreteEval axioms preconditions

instance [Inhabited T.Metadata] [Inhabited T.IDMeta] : Inhabited (LFunc T) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

-- Provide explicit instance for LFunc to ensure proper resolution
instance [ToFormat T.IDMeta] [Inhabited T.Metadata] : ToFormat (LFunc T) where
  format := Func.format

@[expose]
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

theorem LFunc.type_inputs_nodup {T : LExprParams} [DecidableEq T.IDMeta] (f : LFunc T) (ty : LTy) :
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
structure Factory (T : LExprParams) where
  /-- The underlying array of factory functions. -/
  toArray : Array (LFunc T)
  /-- Maps function names to their index in `toArray` for O(1) lookup. -/
  private nameMap : Std.HashMap String Nat
  /-- Every array element's name is mapped to its index in `nameMap`. -/
  private toArrayDefined : ∀ (i : Fin toArray.size), nameMap[toArray[i].name.name]? = some i
  /-- Every key in `nameMap` maps to a valid index in `toArray`. -/
  private nameMapValid : ∀{k : String} (p : k ∈ nameMap), nameMap[k] < toArray.size
  /-- Every key in `nameMap` is the name of the element it points to. -/
  private nameMapConsistent : ∀ {k : String} (p : k ∈ nameMap), (toArray[nameMap[k]]'(nameMapValid p)).name.name = k

namespace Factory

private theorem List_inj_implies_nodup {α} (l : List α)
  (p : ∀(i j : Nat) (p : i < l.length) (q : j < l.length), l[i] = l[j] → i = j)  :
     l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons h l ind =>
    rw [List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨k, hk, hval⟩ := hmem
      have := p 0 (k + 1) (by simp) (by simp [hk]) (by simp [hval])
      omega
    · exact ind (fun i j hi hj heq => by
        have := p (i + 1) (j + 1) (by simp [hi]) (by simp[hj]) (by simpa using heq)
        omega)

/-- The function names in a factory are unique. -/
theorem name_nodup {T} (f : Factory T) : List.Nodup (f.toArray |>.toList |>.map (·.name.name)) := by
  match f with
  | { toArray := ⟨l⟩, nameMap, toArrayDefined, nameMapValid, nameMapConsistent } =>
    apply List_inj_implies_nodup
    intro i j hi hj heq
    simp only [List.length_map] at hi hj
    -- toArrayDefined gives us injectivity via the nameMap
    have hdi : nameMap[l[i].name.name]? = some i := toArrayDefined ⟨i, hi⟩
    have hdj : nameMap[l[j].name.name]? = some j := toArrayDefined ⟨j, hj⟩
    grind

protected def mem {T} (f : Factory T) (name : String) := name ∈ f.nameMap

def instMemDecidable {T} (f : Factory T) (name : String) : Decidable (f.mem name) :=
  (inferInstance : Decidable (name ∈ f.nameMap))

instance instMem {T} : Membership String (Factory T) where
  mem := Factory.mem

instance instMembershipDecidable {T} (f : Factory T) (name : String) : Decidable (name ∈ f) :=
  f.instMemDecidable name

def get {T} (f : Factory T) (name : String) (p : name ∈ f): LFunc T :=
  let idx := f.nameMap[name]
  have idx_lt : idx < f.toArray.size := f.nameMapValid p
  f.toArray[idx]

def get? {T} (f : Factory T) (name : String) : Option (LFunc T) :=
  match h : f.nameMap[name]? with
  | none =>
    none
  | some idx =>
    have idx_lt : idx < f.toArray.size := by
      simp only [Std.HashMap.getElem?_eq_some_iff] at h
      have ⟨e, em⟩ := h
      simp only [←em]
      apply f.nameMapValid
    f.toArray[idx]

instance instGetElem? {T} : GetElem? (Factory T) String (LFunc T) Membership.mem where
  getElem := Factory.get
  getElem? := Factory.get?

protected def default {T} : Factory T := {
  toArray := #[]
  nameMap := {}
  toArrayDefined := by intro ⟨i, hi⟩; exact absurd hi (by simp [Array.size])
  nameMapValid := by intro k km; grind
  nameMapConsistent := by intro k km; grind
}

theorem default_empty {T} (x : String) : ¬(x ∈ (Factory.default : Factory T)) := by
  simp +instances [instMem, Factory.mem, Factory.default]

instance {T} : Inhabited (Factory T) where
  default := Factory.default

def push {T} (F : Factory T) (fn : LFunc T) (is_new : ¬(fn.name.name ∈ F)) : Factory T :=
  let idx := F.toArray.size
  { toArray := F.toArray.push fn
    nameMap := F.nameMap.insert fn.name.name idx
    toArrayDefined := by
      intro ⟨i, hi⟩
      if heq : i < F.toArray.size then
        unfold instMem at is_new
        simp only [Factory.mem] at is_new
        have r := F.toArrayDefined ⟨i, heq⟩
        grind
      else
        grind
    nameMapValid := by
      intro nm nm_mem
      have p := @F.nameMapValid
      grind
    nameMapConsistent := by
      intro k km
      simp +instances only [instMem, Factory.mem] at is_new
      if heq : k = fn.name.name then
        grind
      else
        have km' : k ∈ F.nameMap := by grind
        have := F.nameMapConsistent km'
        grind
  }

/-- Insert `fn` into the factory if no function with the same name already exists. -/
def pushIfNew {T} (f : Factory T) (fn : LFunc T) : Factory T :=
  if p : fn.name.name ∈ f then
    f
  else
    f.push fn p

private theorem mem_pushIfNew {T} {f : Factory T} {g h : LFunc T}
    (p : g ∈ (f.pushIfNew h).toArray) : g ∈ f.toArray ∨ g = h := by
  revert p
  simp [pushIfNew, push]
  grind

def append {T} (F : Factory T) (a : Array (LFunc T)) : Factory T :=
  a.foldl (init := F) pushIfNew

private theorem ofArray_mem_take {T} {f : Factory T} {as : Array (LFunc T)} {fn : LFunc T}
    (p : fn ∈ (f.append as).toArray) : fn ∈ f.toArray ∨ fn ∈ (as.take as.size) := by
  simp only [append] at p
  revert p
  intro p2
  apply Array.foldl_induction (init := f) (f := pushIfNew)
    (motive := fun i m => fn ∈ m.toArray → fn ∈ f.toArray ∨ fn ∈ as.take i)
  case h0 =>
    grind
  case hf =>
    intro ⟨i, ilt⟩ f2 p p2
    simp_all only [Array.mem_extract_iff_getElem]
    match mem_pushIfNew p2 with
    | Or.inl q =>
      grind
    | Or.inr q =>
      grind
  case a =>
    exact p2

def ofArray {T} (a : Array (LFunc T)) : Factory T :=
  .default |>.append a

theorem ofArray_mem {T} {a : Array (LFunc T)} {fn : LFunc T}
    (p : fn ∈ (Factory.ofArray a).toArray) : fn ∈ a := by
  have q := ofArray_mem_take p
  simp [Factory.default] at q
  exact q

@[simp] theorem toArray_default {T} : (Factory.default (T := T)).toArray = #[] := by
  unfold Factory.default; rfl

@[simp]
theorem default_mem_is_false (T) (name : String) : name ∈ Factory.default (T := T) ↔ False := by
  simp +instances[Factory.default, Factory.instMem, Factory.mem]

theorem push_mem_iff {T} (f : Factory T) (fn : LFunc T) (h : fn.name.name ∉ f) (name : String) :
    name ∈ f.push fn h ↔ name = fn.name.name ∨ name ∈ f := by
  simp +instances only [instMem, Factory.mem, push]
  simp only [Std.HashMap.mem_insert]
  constructor <;> intro hm <;> grind

theorem mem_iff_mem_names {T} (f : Factory T) (s : String) :
    s ∈ f ↔ s ∈ f.toArray.map (·.name.name) := by
  constructor
  · intro hs
    have hvalid := f.nameMapValid hs
    have hcons := f.nameMapConsistent hs
    rw [Array.mem_iff_getElem]
    exact ⟨f.nameMap[s], by simp [Array.size_map]; exact hvalid, by simp [Array.getElem_map]; exact hcons⟩
  · intro hs
    rw [Array.mem_iff_getElem] at hs
    obtain ⟨i, hi, hname⟩ := hs
    simp [Array.size_map] at hi
    simp [Array.getElem_map] at hname
    have := f.toArrayDefined ⟨i, hi⟩
    simp +instances [instMem, Factory.mem]
    rw [← hname]
    grind

theorem push_mem_match {T} (f : Factory T) (fn : LFunc T) (h : fn.name.name ∉ f) (name : String) :
  (f.push fn h)[name]? = if name = fn.name.name then some fn else f[name]? := by
  simp +instances [push, instGetElem?, Factory.get?]
  grind

theorem getElem?_is_some_implies_mem {T} {f : Factory T} {name : String} {fn : LFunc T}
 (eq : f[name]? = some fn) : fn ∈ f.toArray := by
  change Factory.get? f name = some fn at eq
  unfold Factory.get? at eq
  split at eq
  · contradiction
  · rename_i idx h_idx
    injection eq with h_eq
    subst h_eq
    have idx_lt : idx < f.toArray.size := by
      simp only [Std.HashMap.getElem?_eq_some_iff] at h_idx
      obtain ⟨h_mem, h_val⟩ := h_idx
      rw [←h_val]
      exact f.nameMapValid h_mem
    exact Array.mem_def.mpr (Array.getElem_mem_toList idx_lt)

theorem getElem?_some_implies_mem {T} {f : Factory T} {name : String} {fn : LFunc T}
    (eq : f[name]? = some fn) : name ∈ f := by
  simp +instances [instGetElem?, Factory.get?, instMem, Factory.mem] at eq ⊢
  grind

theorem getElem?_some_getElem {T} {f : Factory T} {name : String} {fn : LFunc T}
    (eq : f[name]? = some fn) : f[name]'(getElem?_some_implies_mem eq) = fn := by
  simp +instances [instGetElem?, Factory.get?, Factory.get] at eq ⊢
  split at eq
  · contradiction
  · rename_i idx h_idx; simp at eq; grind

/-- If `fn ∈ F.toArray` and `fn.name.name = s`, then `s ∈ F` and `F[s] = fn`. -/
theorem mem_name_eq_getElem {T} {F : Factory T} {fn : LFunc T} {s : String}
    (hmem : fn ∈ F.toArray) (hname : fn.name.name = s) :
    ∃ (hs : s ∈ F), F[s]'hs = fn := by
  rw [Array.mem_def] at hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨i, hi, hval⟩ := hmem
  have hi' : i < F.toArray.size := by grind
  have hval' : F.toArray[i]'hi' = fn := by simpa using hval
  have hdef : F.nameMap[s]? = some i := by
    have hdef := F.toArrayDefined ⟨i, hi'⟩
    simp at hdef
    grind
  have hs : s ∈ F := by
    simp +instances only [instMem, Factory.mem]
    grind
  refine ⟨hs, ?_⟩
  simp +instances only [instGetElem?, Factory.get]
  have hidx : F.nameMap[s] = i := (Std.HashMap.getElem?_eq_some_iff.mp hdef).2
  grind

def getFunctionNames {T} (F : Factory T) : Array T.Identifier :=
  F.toArray.map (fun f => f.name)

section
variable  {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

/--
Add a function `func` to the factory `F`. Redefinitions are not allowed.
-/
def tryPush {T} [Inhabited T.Metadata] [ToFormat T.IDMeta] (F : Factory T) (func : LFunc T) : Except DiagnosticModel (Factory T) :=
  if h : func.name.name ∈ F then
    let func' := F[func.name.name]
    .error <| DiagnosticModel.fromFormat f!"A function of name {func.name} already exists! \
              Redefinitions are not allowed.\n\
              Existing Function: {func'}\n\
              New Function:{func}"
  else
    .ok (F.push func h)

/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def tryAddAll (F : Factory T) (newF : Array (LFunc T)) : Except DiagnosticModel (Factory T) :=
  newF.foldlM (·.tryPush ·) (init := F)

/--
Append a factory `newF` to an existing factory `F`, checking for redefinitions
along the way.
-/
def addFactory (F newF : Factory T) : Except DiagnosticModel (Factory T) :=
  F.tryAddAll newF.toArray

end

end Factory

@[expose] def getLFuncCall {GenericTy} (e : LExpr ⟨T, GenericTy⟩) : LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) :=
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
def Factory.callOfLFunc {GenericTy} (F : Factory T) (e : LExpr ⟨T, GenericTy⟩)
    (allowPartialApp := false)
    : Option (LExpr ⟨T, GenericTy⟩ × List (LExpr ⟨T, GenericTy⟩) × LFunc T) :=
  let (op, args) := getLFuncCall e
  match op with
  | .op _ name _ =>
    match F[name.name]? with
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

theorem callOfLFunc_eq_some {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧
      F[name.name]? = some fn ∧ args.length = fn.inputs.length := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

theorem callOfLFunc_getLFuncCall {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    {aPA : Bool}
    (hcall : Factory.callOfLFunc F e (allowPartialApp := aPA) = some (callee, args, fn))
    : getLFuncCall e = (callee, args) := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  cases aPA <;> simp at hcall <;> split at hcall <;> simp at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; exact Prod.ext ‹_› rfl)

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

theorem Factory.callOfLFunc_smaller {T} {F : Factory T.base} {e : LExpr T} {op args F'}
    {allowPartialMatch}
    : Factory.callOfLFunc F e (allowPartialApp := allowPartialMatch) = some (op, args, F') →
  (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  simp[Factory.callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp; cases op <;> simp
  rename_i o ty; cases F[o.name]? <;> simp
  rename_i F'
  cases allowPartialMatch
  · cases (args.length == List.length F'.inputs) <;> simp; intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)
  · cases (Nat.ble args.length (List.length F'.inputs)) <;> simp
    intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)

/-- If `F[s]?` finds a function, its name matches the query. -/
theorem Factory.getElem?_name {T} {F : Factory T} {s : String} {fn : LFunc T}
    (h : F[s]? = some fn) : fn.name.name = s := by
  simp +instances [instGetElem?, Factory.get?] at h
  split at h
  · contradiction
  · rename_i idx h_idx; simp at h
    have h_mem : s ∈ F.nameMap := by grind
    have h_idx_val : F.nameMap[s] = idx :=
      (Std.HashMap.getElem?_eq_some_iff.mp h_idx).2
    have h_cons := F.nameMapConsistent h_mem
    grind

/-- `callOfLFunc` ensures the number of args equals the number of inputs. -/
theorem Factory.callOfLFunc_arity {T} {F : Factory T} {e callee : LExpr T.mono}
    {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : args.length = fn.inputs.length := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

/-- The callee of `callOfLFunc` is an `.op` whose name resolves to `fn` via `F[_]?`. -/
theorem Factory.callOfLFunc_getElem?
    {T} {F : Factory T} {e callee : LExpr T.mono}
    {args : List (LExpr T.mono)} {fn : LFunc T}
    {aPA : Bool}
    (hcall : Factory.callOfLFunc F e (allowPartialApp := aPA) = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧ F[name.name]? = some fn := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  cases aPA <;> simp at hcall <;> split at hcall <;> simp at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; grind)

/-- If `callOfLFunc` returns a triple, the function is a member of the factory array. -/
theorem callOfLFunc_func_mem
    {T : LExprParams} (F : @Factory T) (e : LExpr T.mono)
    (op : LExpr T.mono) (args : List (LExpr T.mono)) (func : LFunc T)
    (aPA : Bool)
    (h : F.callOfLFunc e (allowPartialApp := aPA) = some (op, args, func)) :
    func ∈ F.toArray := by
  simp only [Factory.callOfLFunc] at h
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h
  cases op' <;> simp at h
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h
  | some func' =>
    simp only [h_gf] at h
    cases aPA <;> simp at h <;> split at h <;> simp at h
    all_goals (obtain ⟨_, _, rfl⟩ := h; exact Factory.getElem?_is_some_implies_mem h_gf)

/--
Apply type substitution `S` to all type annotations in an `LExpr`.
This is only for user-defined types, not metadata-stored resolved types.
If e is an LExprT whose metadata contains type information, use applySubstT.
-/
def LExpr.applySubst {T : LExprParams} (e : LExpr T.mono) (S : Subst) : LExpr T.mono :=
  if S.hasEmptyScopes then e else replaceUserProvidedType e (LMonoTy.subst S)

theorem LExpr.applySubst_eq_replaceUserProvidedType {T : LExprParams}
    (e : LExpr T.mono) (S : Subst) :
    e.applySubst S = replaceUserProvidedType e (LMonoTy.subst S) := by
  unfold applySubst
  split
  case isTrue h_empty =>
    have h_id : LMonoTy.subst S = id := funext (fun ty => LMonoTy.subst_emptyS h_empty)
    rw [h_id]
    induction e <;> unfold replaceUserProvidedType <;> grind
  case isFalse => rfl

/--
Best-effort type extraction from an `LExpr` without a typing context.
Returns `none` when the type cannot be determined syntactically.
-/
def LExpr.typeOf {T : LExprParams} : LExpr T.mono → Option LMonoTy
  | .const _ c              => some c.ty
  | .op _ _ ty              => ty
  | .bvar _ _               => none
  | .fvar _ _ ty            => ty
  | .abs _ _ (some argTy) e => e.typeOf.map (.arrow argTy ·)
  | .abs _ _ none _         => none
  | .quant _ _ _ _ _ _      => some .bool
  | .app _ fn _             => fn.typeOf.bind (fun | .arrow _ ret => some ret | _ => none)
  | .ite _ _ t _            => t.typeOf
  | .eq _ _ _               => some .bool

/--
Derive a type substitution from the `.op` type annotation alone, by unifying it
against the function's generic type. On annotated terms (i.e., terms that have
undergone type inference), the `.op` node always carries a type annotation, so
this suffices.

Returns `some Subst.empty` when `fn.typeArgs` is empty (monomorphic — no-op).
Returns `none` if the callee is not annotated or unification fails.
-/
@[expose] def LFunc.opTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    : Option Subst :=
  if fn.typeArgs.isEmpty then some Subst.empty
  else match callee with
    | .op _ _ (some instTy) =>
      let genericTy := LMonoTy.mkArrow' fn.output fn.inputs.values
      match Constraints.unify [(instTy, genericTy)] SubstInfo.empty with
      | .ok substInfo => some substInfo.subst
      | .error _ => none
    | _ => none

/--
Derive a type substitution by unifying the instantiated operator type against the
function's generic type. Used when inlining a polymorphic function body to
instantiate type variables.

Prefers the `.op` annotation (via `opTypeSubst`). Falls back to a best-effort
approach using argument types when the `.op` is not annotated. On annotated terms
(after type inference), the `.op` always carries a type annotation, so the fallback
is never needed.

Returns `some Subst.empty` when `fn.typeArgs` is empty (monomorphic — no-op).
Returns `none` if the type substitution cannot be derived.
-/
@[expose] def LFunc.computeTypeSubst {T : LExprParams} (fn : LFunc T) (callee : LExpr T.mono)
    (args : List (LExpr T.mono)) : Option Subst :=
  match fn.opTypeSubst callee with
  | some s => some s
  | none =>
    -- Fallback: use argument types (best-effort, only when .op is unannotated)
    if fn.typeArgs.isEmpty then some Subst.empty
    else
      let argConstraints := (args.zip fn.inputs.values).filterMap
        (fun (arg, formal) => arg.typeOf.map (·, formal))
      if argConstraints.isEmpty then none
      else match Constraints.unify argConstraints SubstInfo.empty with
        | .ok substInfo => some substInfo.subst
        | .error _ => none

/-- When `opTypeSubst` succeeds, `computeTypeSubst` agrees with it. -/
theorem LFunc.computeTypeSubst_of_opTypeSubst {T : LExprParams}
    {fn : LFunc T} {callee : LExpr T.mono} {args : List (LExpr T.mono)} {s : Subst}
    (h : fn.opTypeSubst callee = some s)
    : fn.computeTypeSubst callee args = some s := by
  unfold LFunc.computeTypeSubst
  rw [h]

end -- public section
end Lambda

---------------------------------------------------------------------

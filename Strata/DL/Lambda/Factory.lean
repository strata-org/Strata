/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExpr
public import Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.LTyUnify
public import Strata.DL.Util.Func
import Strata.Util.ListProps
import Std.Data.HashMap.Lemmas

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
The AST-facing Lambda function structure - instantiation of the base `Func` for
Lambda expressions. It is used for functions that appear in the Strata AST
(e.g. `Core.Function`, `funcDecl`), and carries only plain data — the base
`Func` excludes the function-typed `concreteEval`, so it has decidable equality.

Universally quantified type identifiers, if any, appear before this signature and can
quantify over the type identifiers in it.
-/
@[expose] abbrev LFuncDefined (T : LExprParams) := Func (T.Identifier) (LExpr T.mono) LMonoTy T.Metadata

/--
A Lambda factory function - the full, evaluator/factory-facing function
structure. It extends the AST-facing `Func` with the partial-evaluator hook
`concreteEval`. All other fields live on the base `Func`.

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
If LFunc already has body, it must not have concreteEval, and vice versa.
-/
structure LFunc (T : LExprParams) extends
    Func (T.Identifier) (LExpr T.mono) LMonoTy T.Metadata where
  mk' ::
  -- The Metadata argument is attached to the resulting expression of
  -- concreteEval if evaluation was successful.
  concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none

/--
Helper constructor for LFunc to maintain backward compatibility.
-/
@[expose] def LFunc.mk {T : LExprParams} (name : T.Identifier) (typeArgs : List TyIdentifier := [])
    (isConstr : Bool := false) (isRecursive : Bool := false)
    (inputs : ListMap T.Identifier LMonoTy) (output : LMonoTy)
    (body : Option (LExpr T.mono) := .none) (attr : Array Strata.DL.Util.FuncAttr := #[])
    (concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none)
    (axioms : List (LExpr T.mono) := [])
    (preconditions : List (FuncPrecondition (LExpr T.mono) T.Metadata) := [])
    (measure : Option (LExpr T.mono) := .none) : LFunc T :=
  { name, typeArgs, isConstr, isRecursive, inputs, output, body, attr,
    axioms, preconditions, measure, concreteEval }

/-- Lift an AST-facing `LFuncDefined` (base `Func`) into the full `LFunc`,
    optionally attaching `concreteEval` at the evaluator boundary. All other
    data carries over unchanged via `toFunc`. -/
@[expose] def LFuncDefined.toLFunc {T : LExprParams} (f : LFuncDefined T)
    (concreteEval : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono)) := .none) : LFunc T :=
  { toFunc := f, concreteEval }

instance [Inhabited T.Metadata] [Inhabited T.IDMeta] : Inhabited (LFunc T) where
  default := { name := Inhabited.default, inputs := [], output := LMonoTy.bool }

-- Take `[ToFormat (LExpr T.mono)]` as an instance argument so a more specific
-- expression formatter (e.g. the Core CST pretty-printer for `Expression.Expr`)
-- is chosen at concrete instantiations rather than the generic `LExpr` one.
instance [ToFormat T.IDMeta] [Inhabited T.Metadata] [ToFormat (LExpr T.mono)] :
    ToFormat (LFunc T) where
  format f := Func.format f.toFunc

@[expose]
def LFuncDefined.type [DecidableEq T.IDMeta] (f : (LFuncDefined T)) : Except Format LTy := do
  if !(decide f.inputs.keys.Nodup) then
    .error f!"[{f.name}] Duplicates found in the formals!\
              {Format.line}\
              {f.inputs}"
  else if !(decide f.typeArgs.Nodup) then
    .error f!"[{f.name}] Duplicates found in the universally \
              quantified type identifiers!\
              {Format.line}\
              {f.typeArgs}"
  -- Reject any arrow type with ≠ 2 arguments: a non-binary `tcons "arrow" [a,b,c]` would be
  -- flattened by `destructArrow` below and re-nested binary, so the reconstructed signature
  -- would disagree with the original output.
  else if !(f.output.arrowsBinary && Lambda.LMonoTys.arrowsBinary f.inputs.values) then
    .error f!"[{f.name}] Signature contains an arrow type with ≠ 2 arguments; \
              function types must be binary (t1 -> t2)."
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  match input_tys with
  | [] => .ok (.forAll f.typeArgs f.output)
  | ity :: irest =>
    .ok (.forAll f.typeArgs (Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)))

theorem LFuncDefined.type_inputs_nodup {T : LExprParams} [DecidableEq T.IDMeta] (f : LFuncDefined T) (ty : LTy) :
    f.type = .ok ty → f.inputs.keys.Nodup := by
  intro h
  simp only [LFuncDefined.type, bind, Except.bind] at h
  -- At this point grind is possible if this proof needs maintenance
  split at h <;> try contradiction
  simp_all

@[expose] def LFuncDefined.opExpr [Inhabited T.Metadata] (f: LFuncDefined T) : LExpr T.mono :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op (default : T.Metadata) f.name (some ty)

def LFuncDefined.inputPolyTypes (f : (LFuncDefined T)) : @LTySignature T.IDMeta :=
  f.inputs.map (fun (id, mty) => (id, .forAll f.typeArgs mty))

def LFuncDefined.inputMonoSignature (f : (LFuncDefined T)) : @LTySignature T.IDMeta :=
  f.inputs.map (fun (id, mty) => (id, .forAll [] mty))

def LFuncDefined.outputPolyType (f : (LFuncDefined T)) : LTy :=
  .forAll f.typeArgs f.output

def LFuncDefined.eraseTypes (f : LFuncDefined T) : LFuncDefined T :=
  { f with
    body := f.body.map LExpr.eraseTypes,
    axioms := f.axioms.map LExpr.eraseTypes,
    preconditions := f.preconditions.map fun p => { p with expr := p.expr.eraseTypes } }

@[expose] def LFunc.type [DecidableEq T.IDMeta] (f : (LFunc T)) : Except Format LTy :=
  LFuncDefined.type f.toFunc

@[expose] def LFunc.opExpr [Inhabited T.Metadata] (f: LFunc T) : LExpr T.mono :=
  LFuncDefined.opExpr f.toFunc

def LFunc.inputPolyTypes (f : (LFunc T)) : @LTySignature T.IDMeta :=
  LFuncDefined.inputPolyTypes f.toFunc

def LFunc.inputMonoSignature (f : (LFunc T)) : @LTySignature T.IDMeta :=
  LFuncDefined.inputMonoSignature f.toFunc

def LFunc.outputPolyType (f : (LFunc T)) : LTy :=
  LFuncDefined.outputPolyType f.toFunc

def LFunc.eraseTypes (f : LFunc T) : LFunc T :=
  { f with toFunc := LFuncDefined.eraseTypes f.toFunc }

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

def append {T} (F : Factory T) (a : Array (LFunc T)) : Factory T :=
  a.foldl (init := F) pushIfNew

def ofArray {T} (a : Array (LFunc T)) : Factory T :=
  .default |>.append a

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

end Factory

/--
Apply type substitution `S` to all type annotations in an `LExpr`.
This is only for user-defined types, not metadata-stored resolved types.
If e is an LExprT whose metadata contains type information, use applySubstT.
-/
def LExpr.applySubst {T : LExprParams} (e : LExpr T.mono) (S : Subst) : LExpr T.mono :=
  if S.hasEmptyScopes then e else replaceUserProvidedType e (LMonoTy.subst S)

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

end -- public section
end Lambda

---------------------------------------------------------------------

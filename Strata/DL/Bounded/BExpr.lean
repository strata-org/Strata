/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.IntBoolFactory

/-! ## Lambda Expressions with Bounded Ints

Here, we desugar LExprTs with bounded int types into regular Lambda expressions by performing two steps:
1. Translating the term, keeping track of assumptions implicit in the bounded types.
2. Generating well-formedness conditions e.g. for function calls.
Most bounds must be explicitly stated; the only inferred/checked ones occur when calling a function requiring a bounded argument on a int-typed argument.
-/

/-
The process of keeping track of assumptions and constraints is complicated. Here we give the key ideas (using the type nat = {x | 0 ≤ x} as an example):
1. There are two kinds of assumptions: context-dependent (e.g. for ∀ (x: nat). e, we assume 0 ≤ x when translating e) and context-independent (e.g. for external operator foo: int → nat, we are always free to assume 0 ≤ foo 1).
2. The context-dependent assumptions must be propagated top-down (when recursively translating the body of a quantifier or lambda), while the context-independent assumptions must be propagated bottom-up (as we do not know which external symbols appear in a subterm without inspecting it).
3. Assumptions can only be added to boolean-valued terms. Therefore, the basic algorithm is as follows: maintain a set of the top-down assumptions and recursively traverse the term, removing bounded types. Whenever a bool-valued expression is reached, recursively translate the body and collect the bottom-up assumptions. Then add all assumptions to the translated body.
4. However, we cannot freely add assumptions in non-strictly-positive positions without changing the semantics. Therefore, if in such a position, we do not add the bottom-up assumptions but rather keep propagating upward until we reach a strictly positive position (which must exist at least at the outer layer). Since it is not possible to always determine whether a position is positive without β-reduction, we are conservative and assume all unknown positions are non-positive.
5. We must be careful about binders and quantify bottom-up assumptions that escape the scope of a quantified variable due to the above positivity restriction. For example, (∃ (x: int). foo x < 0) → False is translated to (∀ (x: int). 0 ≤ foo' x) → ((∃ (x: int). foo' x < 0) → False) where foo' has type int → int

Generating well-formedness conditions is somewhat simpler. The main rules are:
1. Constants that claim to have a bounded type are checked (e.g. 3: nat)
2. For application e₁e₂ where e₁ has type b → T, we check that b holds of the translated e₂
3. For application e₁e₂ : b where e₁ has type T -> int, we check that the translated application satisfies b. (Note: we cannot just check bounded types in general because some bounds are assumed e.g. for external operators)
4. For λ (x : T). e : T -> b, we check that e satisfies bound b (possibly assuming any bounds for x)
Proving these well-formedness conditions may require both the top-down and bottom-up assumptions, so we compute all at the same time.

See StrataTest/DL/Bounded/BExprTest.lean for test cases that further illustrate the expected translations and well-formedness conditions.

-/

namespace Bounded
open Std (ToFormat Format format)
open Lambda

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier]

/--
Translate bounded integer expression b to LExprT with holes filled by e
-/
def boundValToLExprT (b: BoundVal) (e: LExprT Identifier) : LExprT Identifier :=
  match b with
  | .bvar => e
  | .bconst val => .const (val.repr) LMonoTy.int

/-
Utilities to construct common operators on common int and bool functions from IntBoolFactory.lean
-/

-- Adapted for LExprT from Factory.lean
def LFunc.opExprT (f: LFunc Identifier) : LExprT Identifier :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op f.name ty

/--
Constructs the LExprT (.op o) e1 e2, where o has type bool -> bool -> bool
-/
def boolBinopExprT (o: LFunc Identifier) (e1 e2: LExprT Identifier) : LExprT Identifier :=
  .app (.app (LFunc.opExprT o) e1 (.arrow .bool .bool)) e2 .bool

/--
Constructs the LExprT (.op o) e1 e2, where o has type int -> int -> bool
-/
def intCompBinopExprT (o: LFunc Identifier) (e1 e2: LExprT Identifier) : LExprT Identifier :=
  .app (.app (LFunc.opExprT o) e1 (.arrow .int .bool)) e2 .bool

def andExprT [Coe String Identifier] (e1 e2: LExprT Identifier) : LExprT Identifier :=
  boolBinopExprT boolAndFunc e1 e2

def implExprT [Coe String Identifier] (e1 e2: LExprT Identifier) : LExprT Identifier :=
  boolBinopExprT boolImpliesFunc e1 e2

def notExprT [Coe String Identifier] (e: LExprT Identifier) : LExprT Identifier :=
  .app (LFunc.opExprT boolNotFunc) e .bool

def intLtExprT [Coe String Identifier] (e1 e2: LExprT Identifier) : LExprT Identifier :=
  intCompBinopExprT intLtFunc e1 e2

def intLeExprT [Coe String Identifier] (e1 e2: LExprT Identifier) : LExprT Identifier :=
  intCompBinopExprT intLeFunc e1 e2

/--
Translate BoundExpr b to corresponding Lambda expression
-/
def boundExprToLExprT [Coe String Identifier] (b: BoundExpr) (e: LExprT Identifier) :
LExprT Identifier :=
  match b with
  | .beq b1 b2 =>
    .eq (boundValToLExprT b1 e) (boundValToLExprT b2 e) LMonoTy.bool
  | .blt b1 b2 => intLtExprT (boundValToLExprT b1 e) (boundValToLExprT b2 e)
  | .ble b1 b2 => intLeExprT (boundValToLExprT b1 e) (boundValToLExprT b2 e)
  | .band e1 e2 => andExprT (boundExprToLExprT e1 e) (boundExprToLExprT e2 e)
  | .bnot e1 => notExprT (boundExprToLExprT e1 e)

-- Auxilliary functions for translation

/--
Add list of assumptions l to boolean-valued e
-/
private def addAssumptions [Coe String Identifier] (l: List (LExprT Identifier)) (e: LExprT Identifier) : LExprT Identifier :=
  List.foldr implExprT e l

/--
Produce l₁ ∧ ... ∧ lₙ ∧ e
-/
private def addAndExprs [Coe String Identifier] (l: List (LExprT Identifier)) (e: LExprT Identifier) : LExprT Identifier :=
  List.foldr andExprT e l

/-
An inefficient method of maintaining a list with no duplicates. Should be replaced with a HashSet or similar
-/
def ListSet α := List α

def ListSet.contains {α} [DecidableEq α] (l: ListSet α) (x: α) : Bool :=
  List.foldr (fun y acc => x == y || acc) false l

def ListSet.insert {α} [DecidableEq α] (l: ListSet α) (x: α) : ListSet α :=
  if ListSet.contains l x then l else x :: l

def ListSet.insertAll {α} [DecidableEq α] (l: ListSet α) (xs: List α) : ListSet α :=
  List.foldr (fun x acc => ListSet.insert acc x) l xs

def ListSet.union {α} [DecidableEq α] (l: List (ListSet α)) : ListSet α :=
  List.foldr ListSet.insertAll [] l

-- Auxiliary functions for producing bounds/assumptions

/-
All top-down assumptions initially start as expressions over (.bvar 0 .int). As we pass through binders, these bvars must be increased. We only care about expressions consisting of bvar, eq, app (output of boundExprToLExprT)
-/
private def increaseBVar (e: LExprT Identifier) : LExprT Identifier :=
  match e with
  | .bvar b ty => .bvar (b+1) ty
  | .eq e1 e2 ty => .eq (increaseBVar e1) (increaseBVar e2) ty
  | .app e1 e2 ty => .app (increaseBVar e1) (increaseBVar e2) ty
  | _ => e

private def increaseBVars (l: List (LExprT Identifier)) : List (LExprT Identifier) :=
  List.map increaseBVar l

private def isBounded (t: LMonoTy) : Option BoundExpr :=
  match t with
  | LMonoTy.bounded b => .some b
  | _ => .none

private def removeTyBound (t: LMonoTy) : LMonoTy :=
  match t with
  | LMonoTy.bounded _ => LMonoTy.int
  | .tcons name args m => .tcons name (List.map removeTyBound args) m
  | _ => t

/--
If ty is .bounded b, produces expression b(e)
-/
private def boundExprIfType [Coe String Identifier] (ty: LMonoTy) (e: LExprT Identifier) : List (LExprT Identifier) :=
  ((isBounded ty).map (fun b => boundExprToLExprT b e)).toList

/--
If ty is .bounded b, produces expression b(.bvar 0 .int)
-/
def makeBoundAssumption [Coe String Identifier] (ty : LMonoTy) : List (LExprT Identifier) := boundExprIfType ty (.bvar 0 .int)

/--
Generates WF condition for calling e1 with argument e2 if bounded type expected
-/
def wfCallCondition [Coe String Identifier] (assume : List (LExprT Identifier)) (e1 e2: LExprT Identifier) :=
  match LExprT.toLMonoTy e1 with
  | .arrow (.bounded b) _ =>
    -- check that translated e2 satisfies precondition under assumptions
    [addAssumptions assume (boundExprToLExprT b e2)]
  | _ => []

/--
  Universally quantifies all expressions in lists l1 and l2, additionally adding assumptions in "assume" to l1. These quantifiers will eventually be removed in a postprocessing step
-/
private def addBoundedWf [Coe String Identifier] (assume: List (LExprT Identifier)) (l1 l2: List (LExprT Identifier)) : List (LExprT Identifier) :=
  List.map (fun e => .quant .all .int (.bvar 0 .int) (addAssumptions assume e)) l1 ++ List.map (.quant .all .int (.bvar 0 .int)) l2

/--
  Universally quantifies all expressions in list l with additional assumptions in "assume"
-/
private def addBoundedWfAssume [Coe String Identifier] (assume: List (LExprT Identifier)) (l: List (LExprT Identifier)) :=
  addBoundedWf assume l []

/--
Determines if a term uses a particular bound variable at the top level
-/
private def hasBvar (e: LExprT Identifier) (n: Nat) : Bool :=
  match e with
  | .bvar m _ => n == m
  | .app e1 e2 _ => hasBvar e1 n || hasBvar e2 n
  | .abs e _ => hasBvar e (n + 1)
  | .quant _ _ _ e => hasBvar e (n + 1)
  | .eq e1 e2 _ => hasBvar e1 n || hasBvar e2 n
  | .mdata _ e => hasBvar e n
  | .ite e1 e2 e3 _ => hasBvar e1 n || hasBvar e2 n || hasBvar e3 n
  | _ => false

/--
When passing an assumption through a binder, we need to quantify the bound variable if used.
-/
private def quantifyAssumptions (ty: LMonoTy) (e: LExprT Identifier): LExprT Identifier :=
  --TODO: triggers?
  if hasBvar e 0 then .quant .all ty (.bvar 0 ty) e else e

/--
Add extra to base iff b holds
-/
def conditionalAdd (b : Bool) (base extra : List α) : List α :=
  if b then base ++ extra else base

def conditionalReturn (pos : Bool) (value : List α) : List α :=
  if pos then [] else value

/--
A "clean" translation that only removes types; used for triggers
-/
private def translateClean [Coe String Identifier] (e: LExprT Identifier) : LExprT Identifier :=
  match e with
  | .const c ty => .const c (removeTyBound ty)
  | .op o ty => .op o (removeTyBound ty)
  | .bvar b ty => .bvar b (removeTyBound ty)
  | .fvar f ty => .fvar f (removeTyBound ty)
  | .app e1 e2 ty => .app (translateClean e1) (translateClean e2) (removeTyBound ty)
  | .abs e ty => .abs (translateClean e) (removeTyBound ty)
  | .quant qk ty tr e' => .quant qk (removeTyBound ty) (translateClean tr) (translateClean e')
  | .ite c t f ty => .ite (translateClean c) (translateClean t) (translateClean f) (removeTyBound ty)
  | .eq e1 e2 ty => .eq (translateClean e1) (translateClean e2) (removeTyBound ty)
  | .mdata m e => .mdata m (translateClean e)

structure translationRes Identifier where
(translate : LExprT Identifier)
(wfCond : ListSet (LExprT Identifier))
(assume : List (LExprT Identifier))

/--
  Under top-down assumptions "assume" and positivity "pos", produce the translation, well-formedness conditions, and bottom-up assumptions for expression e
-/
def translateBounded [Coe String Identifier] [DecidableEq Identifier] (e: LExprT Identifier) (assume: List (LExprT Identifier)) (pos : Bool) : translationRes Identifier :=
  match e with
  -- constants do not need assumptions; they produce a wf goal if bounded
  | .const c ty =>
    let res := .const c (removeTyBound ty);
    ⟨res, boundExprIfType ty res, []⟩
  -- an op adds a bottom-up assumption if it has bounded type; its wf is assumed
  | .op o ty =>
    let res := .op o (removeTyBound ty);
    ⟨if ty == .bool then addAssumptions assume res else res, [], boundExprIfType ty res⟩
  -- bvars are handled when bound
  | .bvar b ty => ⟨ .bvar b (removeTyBound ty), [], [] ⟩
  -- fvars generate bottom-up assumptions if bounded
  | .fvar f ty =>
    let res := .fvar f (removeTyBound ty);
    ⟨res, [], boundExprIfType ty res⟩
  /-
  Application has several cases:
  1. If the entire application has boolean type, assumptions can be added subject to positivity.
  2. Otherwise, if the application has bounded type, it produces a bottom-up assumption. There is a subtle case. If the function has type (t -> int), then we must generate a wf condition. Otherwise, the bound will be assumed (for external operators) or checked (for abstraction/if-then-else/etc)
  3. In either case, we produce a wf condition if the argument should have bounded type.
  -/
  | .app (.op o ty1) e2 .bool =>
    let notCase := o == boolNotFunc.name;
    -- inside "not" - not positive
    let e2' := translateBounded e2 [] (not notCase && pos);
    let all_assumes := conditionalAdd pos assume e2'.assume;
    let res := addAssumptions all_assumes (.app (.op o (removeTyBound ty1)) e2'.translate .bool);
    ⟨res, ListSet.union [wfCallCondition (assume ++ e2'.assume) (.op o ty1) e2'.translate, e2'.wfCond], conditionalReturn pos e2'.assume⟩
  | .app (.app (.op o ty1) e1 ty2) e2 .bool =>
    -- The first argument has positivity pos if the operator is "and" or "or" otherwise false
    let first := (o == boolAndFunc.name || o == boolOrFunc.name) && pos;
    -- The second also includes the RHS of implication
    let second := (o == boolAndFunc.name || o == boolOrFunc.name || o == boolImpliesFunc.name) && pos;
    let e1' := translateBounded e1 [] first;
    let e2' := translateBounded e2 [] second;
    let all_assumes := conditionalAdd pos assume (e1'.assume ++ e2'.assume);
    let res := addAssumptions all_assumes (.app (.app (.op o (removeTyBound ty1)) e1'.translate (removeTyBound ty2)) e2'.translate .bool);
    ⟨res, ListSet.union [wfCallCondition (assume ++ e2'.assume) e1 e2'.translate, e1'.wfCond, e2'.wfCond], conditionalReturn pos (e1'.assume ++ e2'.assume)⟩
  | .app e1 e2 .bool =>
    --Anything else we cannot assume is positive
    let e1' := translateBounded e1 [] false;
    let e2' := translateBounded e2 [] false;
    let all_assumes := conditionalAdd pos assume (e1'.assume ++ e2'.assume);
    let res := addAssumptions all_assumes (.app e1'.translate e2'.translate .bool);
    ⟨res, ListSet.union [wfCallCondition (assume ++ e2'.assume) e1 e2'.translate, e1'.wfCond, e2'.wfCond], conditionalReturn pos (e1'.assume ++ e2'.assume)⟩
  | .app e1 e2 ty =>
    let e1' := translateBounded e1 assume pos;
    let e2' := translateBounded e2 assume pos;
    let res := .app e1'.translate e2'.translate (removeTyBound ty);
    -- If we have application f x where f : _ -> int and f x has bounded type, need wf condition that application result is bounded
    let extraWf :=
      match LExprT.toLMonoTy e1, ty with
      | .arrow _ .int, .bounded _ =>
        boundExprIfType ty e'
      | _, _ => [];
    ⟨res, ListSet.union [wfCallCondition (assume ++ e2'.assume) e1 e2'.translate, extraWf, e1'.wfCond, e2'.wfCond], boundExprIfType ty e' ++ e1'.assume ++ e2'.assume⟩
  /-
  Lambda abstraction:
  1. If the argument is bounded, add as top-down assumption
  2. If the body has type bool, add assumptions and translate
  3. Otherwise, add assumptions and increase bvars of all in "assume" list, as they are passing through a binder
  4. WF: if body bounded, prove body satisfies bound with same assumptions (but without new binder)
  -/
  | .abs e (.arrow ty .bool) =>
    let e' := translateBounded e [] pos;
    let all_assume := conditionalAdd pos (makeBoundAssumption ty ++ (increaseBVars assume)) e'.assume;
    ⟨.abs (addAssumptions all_assume e'.translate) (removeTyBound (.arrow ty .bool)), addBoundedWfAssume all_assume e'.wfCond, conditionalReturn pos (List.map (quantifyAssumptions ty) e'.assume)⟩
  | .abs e (.arrow ty1 ty2) =>
    let all_assume := makeBoundAssumption ty1 ++ (increaseBVars assume);
    let e' := translateBounded e all_assume pos;
    let res := .abs e'.translate (removeTyBound (.arrow ty1 ty2));
    -- Note: don't add assumptions to e'.wfCond, already included
    ⟨res, addBoundedWf all_assume (boundExprIfType ty2 e'.translate) e'.wfCond, List.map (quantifyAssumptions ty1) e'.assume⟩
  | .abs _ _ => ⟨.const "0" .int, [], []⟩ -- error case
  /-
  Quantifiers are simpler because they are boolean-valued. ∀ (x : nat). e adds an assumption x >= 0 -> ..., while ∃ (x: nat). e results in x >= 0 ∧ ..
  -/
  | .quant .all ty tr e =>
    let e' := translateBounded e [] pos;
    let tr' := translateClean tr;
    let all_assume := conditionalAdd pos (makeBoundAssumption ty ++ (increaseBVars assume)) e'.assume;
    ⟨.quant .all (removeTyBound ty) tr' (addAssumptions all_assume e'.translate), addBoundedWfAssume all_assume e'.wfCond, conditionalReturn pos (List.map (quantifyAssumptions ty) e'.assume)⟩
  | .quant .exist ty tr e =>
    let newAssumption := makeBoundAssumption ty;
    let e' := translateBounded e [] pos;
    let tr' := translateClean tr;
    let all_assume := conditionalAdd pos (increaseBVars assume) e'.assume;
    ⟨.quant .exist (removeTyBound ty) tr' (addAssumptions all_assume (addAndExprs newAssumption e'.translate)), addBoundedWfAssume (newAssumption ++ all_assume) e'.wfCond, conditionalReturn pos (List.map (quantifyAssumptions ty) e'.assume)⟩
  /-
  For if-then-else, add assumptions to the condition, which is always bool-valued. For a bool-valued result, can add the conditions freely. For a bounded-valued term, produce a wf condition proving this.
  -/
  | .ite c t f .bool =>
    -- c is NOT positive; equivalent to c -> t /\ ~c -> f
    let c' := translateBounded c [] false;
    let t' := translateBounded t [] pos;
    let f' := translateBounded f [] pos;
    let res := .ite (addAssumptions assume c'.translate) (addAssumptions (conditionalAdd pos assume t'.assume) t'.translate) (addAssumptions (conditionalAdd pos assume f'.assume) f'.translate) .bool;
    ⟨(if pos then addAssumptions c'.assume else id) res, ListSet.union [c'.wfCond, t'.wfCond, f'.wfCond], c'.assume ++ conditionalReturn pos (t'.assume ++ f'.assume)⟩
  | .ite c t f ty =>
    let c' := translateBounded c [] pos;
    let t' := translateBounded t assume pos;
    let f' := translateBounded f assume pos;
    -- here can add inside if positive, never add outside
    let res := .ite (addAssumptions (conditionalAdd pos assume c'.assume) c'.translate) t'.translate f'.translate ty;
    ⟨res, ListSet.union [boundExprIfType ty res, c'.wfCond, t'.wfCond, f'.wfCond], conditionalReturn pos (c'.assume ++ t'.assume ++ f'.assume)⟩
  /-
  Equality is always bool-valued, so can add assumptions
  Equality/iff are equivalent, NOT positive
  -/
  | .eq e1 e2 ty =>
    let e1' := translateBounded e1 [] false;
    let e2' := translateBounded e2 [] false;
    ⟨addAssumptions (conditionalAdd pos assume (e1'.assume ++ e2'.assume)) (.eq e1'.translate e2'.translate ty), ListSet.union [e1'.wfCond, e2'.wfCond], conditionalReturn pos (e1'.assume ++ e2'.assume)⟩
  | .mdata m e =>
    let e' := translateBounded e assume pos;
    ⟨.mdata m e'.translate, e'.wfCond, e'.assume⟩

/--
Translated an expression with bounded types to one without, preserving semantics of bool-valued terms by adding assumptions
-/
def translateBoundedExpr [Coe String Identifier] (e: LExprT Identifier) : LExprT Identifier :=
  (translateBounded e [] true).translate

/-
Many of the wf conditions have the form: forall x, f(x). We remove the quantifiers to make the SMT formulas easier to solve.
Must be stateful because we need to generate fresh variables
-/

-- temporary until LExpr/LExprT are unified
private def LExprT.substK (k : Nat) (s : LExprT Identifier) (e : LExprT Identifier) : LExprT Identifier :=
  match e with
  | .const c ty => .const c ty
  | .op o ty => .op o ty
  | .bvar i ty => if (i == k) then s else .bvar i ty
  | .fvar y ty => .fvar y ty
  | .mdata info e' => .mdata info (substK k s e')
  | .abs e' ty => .abs (substK (k + 1) s e') ty
  | .quant qk ty tr' e' => .quant qk ty (substK (k + 1) s tr') (substK (k + 1) s e')
  | .app e1 e2 ty => .app (substK k s e1) (substK k s e2) ty
  | .ite c t e ty => .ite (substK k s c) (substK k s t) (substK k s e) ty
  | .eq e1 e2 ty => .eq (substK k s e1) (substK k s e2) ty

def LExprT.varOpen (k : Nat) (x : Identifier × LMonoTy) (e : LExprT Identifier) : LExprT Identifier :=
  LExprT.substK k (.fvar x.fst x.snd) e

/--
Remove leading "forall" quantifiers statefully
-/
private def removeLeadingForall (T : TEnv Identifier) (e: LExprT Identifier) : Except Format (LExprT Identifier × TEnv Identifier) :=
  match e with
  | .quant .all ty _ e => do
    let (xv, xty, T) ← Lambda.LExprT.typeBoundVar T ty;
    .ok (LExprT.varOpen 0 (xv, xty) e, T)
  | _ => .ok (e, T)

private def removeLeadingForalls (T : TEnv Identifier) (l: List (LExprT Identifier)) : Except Format (List (LExprT Identifier) × TEnv Identifier) :=
  List.foldlM (fun (l, T) e =>
  do
    let (e, T') ← removeLeadingForall T e;
    .ok (e :: l, T')) ([], T) l

-- Functional version with extra quantifiers
def boundedWfConditionsQuant [Coe String Identifier] (e: LExprT Identifier) : List (LExprT Identifier) :=
  (translateBounded e [] true).wfCond

-- Stateful version without extra quantifiers
def boundedWfConditions [Coe String Identifier] (T : TEnv Identifier) (e: LExprT Identifier) : Except Format (List (LExprT Identifier) × TEnv Identifier) := removeLeadingForalls T (boundedWfConditionsQuant e)

end Bounded

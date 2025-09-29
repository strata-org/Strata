/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.IntBoolFactory

/-! ## Lambda Expressions with Bounded Ints

Here, we parameterize LExprs with bounded int types. These augmented expressions
can be desugared into regular Lambda expressions by erasing the int bounds. To make
the bounds meaningful, we also generate constraints.
All bounds must be explicitly stated; they will not be inferred.

-/

/-!
In general, each input bound gives rise to an assumption in the expression body
as well as an obligation for any arguments, whereas an output bound is the opposite.
-/

namespace Bounded
open Std (ToFormat Format format)
open Lambda

variable {Identifier : Type} [ToString Identifier] [DecidableEq Identifier] [ToFormat Identifier] [HasGen Identifier]

/-

There are two parts to desugaring BLambda to Lambda: translating the terms
by (almost) simply removing the integer bounds, and generating the
corresponding well-formedness conditions. Well-formedness is more general than
just bounded ints, though that is all we have for now.
-/

def isBounded (t: LMonoTy) : Option BoundExpr :=
  match t with
  | LMonoTy.bounded b => .some b
  | _ => .none

def removeBound (t: LMonoTy) : LMonoTy :=
  match t with
  | LMonoTy.bounded _ => LMonoTy.int
  | .tcons name args m => .tcons name (List.map removeBound args) m
  | _ => t


-- generate a single constraint with a body
-- we rely on Lambda's existing substitution for this, simply constructing
-- an expression with a single free variable (called "x", but it will always
-- be substiuted so the name is irrelevant)
-- ugh, free var is Identifier, do substitution directly
--not great, unsafe maybe?
def BoundValToLExprT (b: BoundVal) (e: LExprT Identifier) : LExprT Identifier :=
  match b with
  | .bvar => e
  | .bconst val => .const (val.repr) LMonoTy.int

-- a hack for now (from Factory.lean)
def LFunc.opExprT (f: LFunc Identifier) : LExprT Identifier :=
  let input_tys := f.inputs.values
  let output_tys := Lambda.LMonoTy.destructArrow f.output
  let ty := match input_tys with
            | [] => f.output
            | ity :: irest => Lambda.LMonoTy.mkArrow ity (irest ++ output_tys)
  .op f.name ty

--This is VERY messy,need to think about where this should take place
--MUCH nicer to do on untyped terms but need type for function application
-- Invariant, e must have type int
def BoundExprToLExprT [Coe String Identifier] (b: BoundExpr) (e: LExprT Identifier) :
LExprT Identifier :=
  match b with
  | .beq b1 b2 =>
    .eq (BoundValToLExprT b1 e) (BoundValToLExprT b2 e) LMonoTy.bool
  | .blt b1 b2 =>
    .app (.app (LFunc.opExprT intLtFunc) (BoundValToLExprT b1 e) (LMonoTy.arrow LMonoTy.int LMonoTy.bool)) (BoundValToLExprT b2 e) LMonoTy.bool
  | .ble b1 b2 =>
    .app (.app (LFunc.opExprT intLeFunc) (BoundValToLExprT b1 e) (LMonoTy.arrow LMonoTy.int LMonoTy.bool)) (BoundValToLExprT b2 e) LMonoTy.bool
  | .band e1 e2 =>
    .app (.app (LFunc.opExprT boolAndFunc) (BoundExprToLExprT e1 e)
  (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) (BoundExprToLExprT e2 e) LMonoTy.bool
  | .bnot e1 =>
    .app (LFunc.opExprT boolNotFunc) (BoundExprToLExprT e1 e) LMonoTy.bool

-- e must have type bool
def addAssumptions [Coe String Identifier] (l: List (LExprT Identifier)) (e: LExprT Identifier) : LExprT Identifier :=
  List.foldr (fun x acc =>  .app (.app (LFunc.opExprT boolImpliesFunc) x LMonoTy.bool) acc LMonoTy.bool) e l

def isBool (t: LMonoTy) : Bool :=
  match t with
  | .bool => True
  | _ => False

-- Only deal with expressions of form bvar, eq, app (output of BoundExprToLExprT on bvar)
def increaseBVar (e: LExprT Identifier) : LExprT Identifier :=
  match e with
  | .bvar b ty => .bvar (b+1) ty
  | .eq e1 e2 ty => .eq (increaseBVar e1) (increaseBVar e2) ty
  | .app e1 e2 ty => .app (increaseBVar e1) (increaseBVar e2) ty
  | _ => e


def increaseBVars (l: List (LExprT Identifier)) : List (LExprT Identifier) :=
  List.map increaseBVar l

-- TODO: see what to use here
def ListSet α := List α
-- #print Membership
-- instance : Membership α (ListSet α) :=
--   Membership.mk (fun l x => by unfold ListSet at l; exact (x ∈ l))

def ListSet.contains {α} [DecidableEq α] (l: ListSet α) (x: α) : Bool :=
  List.foldr (fun y acc => x == y || acc) false l

def ListSet.insert {α} [DecidableEq α] (l: ListSet α) (x: α) : ListSet α :=
  if ListSet.contains l x then l else x :: l

def ListSet.insertAll {α} [DecidableEq α] (l: ListSet α) (xs: List α) : ListSet α :=
  List.foldr (fun x acc => ListSet.insert acc x) l xs

def ListSet.union {α} [DecidableEq α] (l: List (ListSet α)) : ListSet α :=
  List.foldr ListSet.insertAll [] l

/- Do translation and wf generation in 1 go - need same assumptions, expesive to compute both-/
structure translationRes Identifier where
(translate : LExprT Identifier)
(wfCond : ListSet (LExprT Identifier))
(assume : List (LExprT Identifier))

-- more aux functions

-- evaluate expression at bound if type is bounded
def boundExprIfType [Coe String Identifier] (ty: LMonoTy) (e: LExprT Identifier) : List (LExprT Identifier) :=
  ((isBounded ty).map (fun b => BoundExprToLExprT b e)).toList

-- Generate WF condition for calling e1 with argument e2 if bounded type expected
def wfCallCondition [Coe String Identifier] (assume : List (LExprT Identifier)) (e1 e2: LExprT Identifier) :=
  match LExprT.toLMonoTy e1 with
  | .arrow (.bounded b) _ =>
    -- check that translated e2 satisfies precondition under assumptions
    [addAssumptions assume (BoundExprToLExprT b e2)]
  | _ => []

-- NOTE: l1 includes assumptions, l2 does not
def addBoundedWf [Coe String Identifier] (assume: List (LExprT Identifier)) (l1 l2: List (LExprT Identifier)) : List (LExprT Identifier) :=
  List.map (fun e => .quant .all .int (.bvar 0 .int) (addAssumptions assume e)) l1 ++ List.map (.quant .all .int (.bvar 0 .int)) l2

def addBoundedWfAssume [Coe String Identifier] (assume: List (LExprT Identifier)) (l: List (LExprT Identifier)) :=
  addBoundedWf assume l []

/--
Translate expression to one without bounded ints.
This is a non-trivial translation, as we want to preserve the semantics of the resulting term.
To see why this is tricky, consider the following examples:
1. ∀ (x: Nat), 0 <= x (should result in something semantically equivalent to true)
2. λ(x: Nat), if 0 <= x then 1 else 0 (should result in function that always evaluates to 1)
3. λ(x: int), if foo x >= 0 then 1 else 0 (supposing foo : int -> Nat, should also result in function that always evaluates to 1)
4. (x: Nat) + (y: Nat) >= 0 must be true

To handle the first case, any bound variables induce constraints that must be
inserted in the resulting formula. The second case shows that adding the constraints is complicated, because the resulting term is not necessarily bool-valued. The third example shows that variables are not enough: any term of bounded type must result in an assumption somehow. The fourth shows that terms may not be closed; therefore, we must collect free variable assumptions as well.

To deal with all of this, our translation function produces two outputs: the translated term and a set of constraints. Broadly, new constraints are added whenever we see a bounded bound variable or an expression of bounded type. We must propagate them back up to any boolean-valued expressions. There is a subtlety resulting from bound variables, as we must make sure the constraints are scoped appropriately (e.g. ∀ (y: Nat).  λ(x: Nat). x + y >= 0, which becomes
∀ Nat. λ Nat. #0 + #1 >= 0 must result in ∀ #0 >= 0 -> λ Nat. #0 >= 0 -> #0 + #1 >= 0).

Also note that assumptions percolate in two directions: A bound variable (possibly) induces a new assumption somewhere inside a subterm, while a (e.g.) function application induces a new assumption in a parent call. Thus, we need both input (the first kind) and output (the second kind) assumption lists.

Note that we do NOT have to worry about the fact that the new functions have a larger domain when types are erased. We generate separate well-formedness checks (below) to ensure that any call of the function occurs on an argument satisfying the constraints.

Invariant: assumptions must not have bounded types (TODO enforce this), same for inputs
Invariant (I think): All assumptions are of form: b(bvar #x)

There is one more complication. When propagating bottom-up assumptions, we cannot just add them at the first bool expression encountered. To see why, consider the example:
~ ((x: Nat) < 0)
This must become
0 <= x -> ~ (x < 0)
NOT
~ (0 <= x -> x < 0)
basically, this should occur any time we are on the left of an implication. Thus, we must add assumptions at any top-level boolean expression. To keep track of this, we use the parameter inBool which becomes false once we have passed at least one bool-valued expression. We only add assumptions if inBool is

We need to keep track of positivity. We cannot add assumptions (e.g) on the LHS of an implication; we need to propagate a level above. This is annoying because connectives are not built in to Lambda.

-/
def translateBounded [Coe String Identifier] [DecidableEq Identifier] (e: LExprT Identifier) (assume: List (LExprT Identifier))
--(pos : Bool)
: translationRes Identifier :=
  match e with
  -- constants do not need assumptions; they produce a wf goal if bounded
  | .const c ty =>
    let res := .const c (removeBound ty);
    ⟨res, boundExprIfType ty res, []⟩
  -- an op adds a bottom-up assumption if it has bounded type; its wf is assumed
  | .op o ty =>
    let res := .op o (removeBound ty);
    ⟨if isBool ty then addAssumptions assume res else res, [], boundExprIfType ty res⟩
  -- bvars are handled when bound
  | .bvar b ty => ⟨ .bvar b (removeBound ty), [], [] ⟩
  -- fvars generate bottom-up assumptions if bounded
  | .fvar f ty =>
    let res := .fvar f (removeBound ty);
    ⟨res, [], boundExprIfType ty res⟩
  /-
  Application has several cases:
  1. If the entire application has boolean type, assumptions can be added
  2. Otherwise, if the application has bounded type, it produces a bottom-up assumption. There is a subtle case. If the function has type (t -> int), then we must generate a wf condition. Otherwise, the bound will be assumed (for external operators) or checked (for abstraction/if-then-else/etc)
  3. In either case, we produce a wf condition if the argument should have bounded type
  -/
  | .app e1 e2 ty =>
    if isBool ty then
      let e1' := translateBounded e1 [];
      let e2' := translateBounded e2 [];
      let all_assumes := assume ++ e1'.assume ++ e2'.assume;
      let res := addAssumptions all_assumes (.app e1'.translate e2'.translate (removeBound ty));
      ⟨res, ListSet.union [wfCallCondition (assume ++ e2'.assume) e1 e2'.translate, e1'.wfCond, e2'.wfCond], []⟩
    else
      let e1' := translateBounded e1 assume;
      let e2' := translateBounded e2 assume;
      let e' := .app e1'.translate e2'.translate (removeBound ty);
      let extraWf :=
        match LExprT.toLMonoTy e1, ty with
        | .arrow _ .int, .bounded _ =>
          boundExprIfType ty e'
        | _, _ => [];
      ⟨e', ListSet.union [wfCallCondition (assume ++ e2'.assume) e1 e2'.translate, extraWf, e1'.wfCond, e2'.wfCond], boundExprIfType ty e' ++ e1'.assume ++ e2'.assume⟩
  /-
  Abstraction is the most complex case:
  1. If the argument is bounded, add as top-down assumption
  2. If the body has type bool, add assumptions and translate
  3. Otherwise, add assumptions and increase bvars of all in "assume" list, as they are passing through a binder
  3. WF: prove body satisfies bound if needed with same assumptions (but without new binder)
  -/
  | .abs e ty =>
    let newAssumption :=
      match ty with
      | .arrow (.bounded b) _ =>
        [BoundExprToLExprT b (.bvar 0 .int)]
      | _ => [];
    match ty with
    | .arrow _ .bool =>
      let e' := translateBounded e [];
      let all_assume := newAssumption ++ (increaseBVars assume) ++ e'.assume;
      -- TODO: change
      ⟨.abs (addAssumptions all_assume e'.translate) (removeBound ty), addBoundedWfAssume all_assume e'.wfCond, []⟩
    | .arrow _ ty1 =>
      let all_assume := newAssumption ++ (increaseBVars assume);
      let e' := translateBounded e all_assume;
      let e'' := .abs e'.translate (removeBound ty);
      -- Note: don't add assumptions to e'.wfCond, already included
      ⟨e'', addBoundedWf all_assume (boundExprIfType ty1 e'.translate) e'.wfCond, e'.assume⟩
    | _ => ⟨.const "0" .int, [], []⟩ -- error case
  /-
  Quantifiers are simpler because they are boolean-valued. ∀ (x : nat). e adds an assumption x >= 0 -> ..., while ∃ (x: nat). e results in x >= 0 ∧ ..
  -/
  | .quant .all ty tr e =>
    let newAssumption :=
      match ty with
      | .bounded b =>
        [BoundExprToLExprT b (.bvar 0 .int)]
      | _ => [];
    let e' := translateBounded e [];
    let tr' := translateBounded tr []; --TODO: need "clean" one here
    let all_assume := (newAssumption ++ (increaseBVars assume) ++ e'.assume);
    -- TODO: factor out quant part
    ⟨.quant .all (removeBound ty) tr'.translate (addAssumptions all_assume e'.translate), addBoundedWfAssume all_assume e'.wfCond, []⟩
  | .quant .exist ty tr e =>
    let newAssumption :=
      match ty with
      | .bounded b =>
        some (BoundExprToLExprT b (.bvar 0 .int))
      | _ => none;
    let e' := translateBounded e [];
    let tr' := translateBounded tr []; --TODO: need "clean" one here
    let add_and x : LExprT Identifier :=
      match newAssumption with
      | .some f => (.app (.app (LFunc.opExprT boolAndFunc) f (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) x LMonoTy.bool)
      | .none => x;
    ⟨.quant .exist (removeBound ty) tr'.translate (add_and (addAssumptions ((increaseBVars assume) ++ e'.assume) e'.translate)), addBoundedWfAssume (newAssumption.toList ++ (increaseBVars assume) ++ e'.assume) e'.wfCond, []⟩
  /-
  For if-then-else, we add assumptions to the condition, which is always bool-valued. For a bool-valued result, we can add the conditions freely. For a bounded-valued term, we produce a wf condition proving this.
  -/
  | .ite c t f .bool =>
    let c' := translateBounded c [];
    let t' := translateBounded t [];
    let f' := translateBounded f [];
    ⟨.ite (addAssumptions (assume ++ c'.assume) c'.translate) (addAssumptions (assume ++ t'.assume) t'.translate) (addAssumptions (assume ++ f'.assume) f'.translate) .bool, ListSet.union [c'.wfCond, t'.wfCond, f'.wfCond] ,[]⟩
  | .ite c t f ty =>
    let c' := translateBounded c [];
    let t' := translateBounded t assume;
    let f' := translateBounded f assume;
    let e' := .ite (addAssumptions (assume ++ c'.assume) c'.translate) t'.translate f'.translate ty;
    ⟨e', ListSet.union [boundExprIfType ty e', c'.wfCond, t'.wfCond, f'.wfCond], t'.assume ++ f'.assume⟩
  -- Equality is always bool-valued, so we can add assumptions
  | .eq e1 e2 ty =>
    let e1' := translateBounded e1 [];
    let e2' := translateBounded e2 [];
    ⟨addAssumptions (assume ++ e1'.assume ++ e2'.assume) (.eq e1'.translate e2'.translate ty), ListSet.union [e1'.wfCond, e2'.wfCond], []⟩
  | .mdata m e =>
    let e' := translateBounded e assume;
    ⟨.mdata m e'.translate, e'.wfCond, e'.assume⟩

-- TODO: name
def translateBounded' [Coe String Identifier] (e: LExprT Identifier) : LExprT Identifier :=
  (translateBounded e []).translate

-- TEMPORARY until LExpr/LExprT are unified
def LExprT.substK (k : Nat) (s : LExprT Identifier) (e : LExprT Identifier) : LExprT Identifier :=
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

/-
Many of the wf conditions have the form: forall x, f(x). We remove the quantifiers to make the SMT formulas easier to solve.
Must be stateful because we need to generate fresh variables
-/
def removeLeadingForall (T : TEnv Identifier) (e: LExprT Identifier) : Except Format (LExprT Identifier × TEnv Identifier) :=
  match e with
  | .quant .all ty _ e => do
    let (xv, xty, T) ← Lambda.LExprT.typeBoundVar T ty;
    .ok (LExprT.varOpen 0 (xv, xty) e, T)
  | _ => .ok (e, T)

def removeLeadingForalls (T : TEnv Identifier) (l: List (LExprT Identifier)) : Except Format (List (LExprT Identifier) × TEnv Identifier) :=
  List.foldlM (fun (l, T) e =>
  do
    let (e, T') ← removeLeadingForall T e;
    .ok (e :: l, T')) ([], T) l

-- Functional version with extra quantifiers
def boundedWfConditions' [Coe String Identifier] (e: LExprT Identifier) : List (LExprT Identifier) :=
  (translateBounded e []).wfCond

-- Stateful version without extra quantifiers
def boundedWfConditions [Coe String Identifier] (T : TEnv Identifier) (e: LExprT Identifier) : Except Format (List (LExprT Identifier) × TEnv Identifier) := removeLeadingForalls T (boundedWfConditions' e)

-- NOTE: the assumptions are useful: they show us the "axioms" that we depend on (assumptions about external ops and free variables)

end Bounded

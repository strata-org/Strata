/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
-- import Strata.DL.Bounded.BTy
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
-/
def translateBounded [Coe String Identifier] (e: LExprT Identifier) (assumptions: List (LExprT Identifier)) : LExprT Identifier × List (LExprT Identifier) :=
  match e with
  | .const c ty => (.const c (removeBound ty), [])
  -- an op adds an assumption if it has bounded type (otherwise, its application may add an assumption further up the chain)
  | .op o ty => let e1 := .op o (removeBound ty);
  (if isBool ty then addAssumptions assumptions e1 else e1, ((isBounded ty).bind (fun b => BoundExprToLExprT b e1)).toList)
  -- bvars should already have been handled if needed
  | .bvar b ty => (.bvar b (removeBound ty), [])
  -- fvars should be given back to the caller as a potential assumption
  | .fvar f ty => let e1 := .fvar f (removeBound ty);  (e1, ((isBounded ty).bind (fun b => BoundExprToLExprT b e1)).toList)
  -- application: if the entire application has bool type, add assumptions (and remove from recursive call)
  -- need to collect assumptions from both recursive calls and add if needed
  | .app e1 e2 ty =>
    if isBool ty then
    let e1' := translateBounded e1 [];
    let e2' := translateBounded e2 [];
    -- safe to add all assumptions, including recursive ones, nothing to propagate up
    (addAssumptions (assumptions ++ e1'.2 ++ e2'.2) (.app e1'.1 e2'.1 (removeBound ty)), [])
    else
    --just recursive, may need assumptions in both but do not need assumptions from 1 in another
    let e1' := translateBounded e1 assumptions;
    let e2' := translateBounded e2 assumptions;
    (.app e1'.1 e2'.1 (removeBound ty), e1'.2 ++ e2'.2)
  -- abstraction: probably the trickiest one.
  -- 1. if the body has bool type, easier, add assumptions (including new one) and translate
  -- 2. Otherwise, need to add assumption and increase bvars of all in "assumptions" list (as they are passing through binder)
  | .abs e ty =>
    --get new assumption (if variable is bounded)
    let newAssumption :=
      match ty with
      | .arrow (.bounded b) _ =>
        [BoundExprToLExprT b (.bvar 0 .int)]
      | _ => [];
    -- case 1: body has bool type
    match ty with
    | .arrow _ .bool =>
      let e' := translateBounded e [];
      (.abs (addAssumptions (newAssumption ++ (increaseBVars assumptions) ++ e'.2) e'.1) (removeBound ty), [])
    -- otherwise, propagate the assumptions, adding a new one
    | _ => let e' := translateBounded e (newAssumption ++ (increaseBVars assumptions));
      (.abs e'.1 (removeBound ty), e'.2)
  -- quantifiers are complex but a bit simpler because we know they are boolean-valued
  | .quant .all ty tr e =>
    let newAssumption :=
      match ty with
      | .bounded b =>
        [BoundExprToLExprT b (.bvar 0 .int)]
      | _ => [];
    let e' := translateBounded e [];
    let tr' := translateBounded tr []; --TODO: need "clean" one here
    (.quant .all (removeBound ty) tr'.1 (addAssumptions (newAssumption ++ (increaseBVars assumptions) ++ e'.2) e'.1), [])
  -- only difference: need exists x, b(x) /\ (assumptions -> e)
  | .quant .exist ty tr e =>
    let newAssumption :=
      match ty with
      | .bounded b =>
        some (BoundExprToLExprT b (.bvar 0 .int))
      | _ => none;
    let e' := translateBounded e [];
    let tr' := translateBounded tr []; --TODO: need "clean" one here
    let add_and x : LExprT Identifier := match newAssumption with
      | .some f => (.app (.app (LFunc.opExprT boolAndFunc) f (LMonoTy.arrow LMonoTy.bool LMonoTy.bool)) x LMonoTy.bool)
      | .none => x;
    (.quant .exist (removeBound ty) tr'.1 (add_and (addAssumptions ((increaseBVars assumptions) ++ e'.2) e'.1)), [])
  -- if-then-else is recursive, but we can add the assumptions to the condition. Likewise, we can test if the result is boolean-valued to see if we add to result
  | .ite c t f .bool =>
    let c' := translateBounded c [];
    let t' := translateBounded t [];
    let f' := translateBounded f [];
    (.ite (addAssumptions (assumptions ++ c'.2) c'.1) (addAssumptions (assumptions ++ t'.2) t'.1) (addAssumptions (assumptions ++ f'.2) f'.1) .bool, [])
  | .ite c t f ty =>
    let c' := translateBounded c [];
    let t' := translateBounded t assumptions;
    let f' := translateBounded f assumptions;
    (.ite (addAssumptions (assumptions ++ c'.2) c'.1) t'.1 f'.1 ty, t'.2 ++ f'.2)
  -- eq is bool so easy
  | .eq e1 e2 ty => --shouldnt' need to check bool
    let e1' := translateBounded e1 [];
    let e2' := translateBounded e2 [];
    (addAssumptions (assumptions ++ e1'.2 ++ e2'.2) (.eq e1'.1 e2'.1 ty), [])
  -- metadata just recursive
  | .mdata m e =>
    let e' := translateBounded e assumptions;
    (.mdata m e'.1, e'.2)

-- TODO: test this with all examples from above





/--
Generate the constraints for a bounded lambda expression. They are:
1. For any int constant c : {x | b (x)}, generate constraint b(c)
2. For .app e1 e2, if e1 has type {x : b(x)} -> t, generate constraint b(e2)
3. For fvar
We also get information (NOTE: BOTH for translation and constraints):
3. For forall {x | b(x)} tr e have forall x, b(x) -> e
4. For exists {x | b(x)} tr e, have exists x, b(x) /\ e
For any free variables in the term, we add the assumption from their bound
(for example, suppose we have forall (x: Nat), x * (y: Nat) >= 0,
  this results in y >= 0 -> forall (x: int), x * y >= 0)
-/
def bounded_constraints [Coe String Identifier]
(e: Lambda.LExpr BMonoTy Identifier) : List (Lambda.LExpr Lambda.LMonoTy Identifier) :=
  match e with
  | .const x (some (.boundint b)) =>
    -- Constant must be int
    match x.toInt? with
    | some i => [bound_to_expr b (.const x LMonoTy.int )]
    | none => [] --this will be caught during typechecking
  | .app e1 e2 =>
  --problem: need to be at given type but dont have types yet


end Bounded

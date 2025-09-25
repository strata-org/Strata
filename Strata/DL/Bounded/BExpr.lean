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

/- Do translation and wf generation in 1 go - need same assumptions, expesive to compute both-/
structure translationRes Identifier where
(translate : LExprT Identifier)
(wfCond : List (LExprT Identifier))
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

--TODO: change to avoid quantifier
-- NOTE: l1 includes assumptions, l2 does not
def addBoundedWf [Coe String Identifier] (assume: List (LExprT Identifier)) (l1 l2: List (LExprT Identifier)) : List (LExprT Identifier) :=
  List.map (fun e => .quant .all .int (.bvar 0 .int) (addAssumptions assume e)) l1 ++ List.map (.quant .all .int (.bvar 0 .int)) l2

def addBoundedWfAssume [Coe String Identifier] (assume: List (LExprT Identifier)) (l: List (LExprT Identifier)) :=
  addBoundedWf assume l []

-- for bounded-valued terms, need to generate condition that body satisfies bound
-- def wfBoundedBody [Coe String Identifier] (ty: LMonoTy) (e: LExprT Identifier) :=
--   ((isBounded ty).map (fun b => BoundExprToLExprT b e)).toList


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
def translateBounded [Coe String Identifier] (e: LExprT Identifier) (assume: List (LExprT Identifier)) : translationRes Identifier :=
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
      ⟨res, (wfCallCondition (assume ++ e2'.assume) e1 e2'.translate) ++ e1'.wfCond ++ e2'.wfCond, []⟩
    else
      let e1' := translateBounded e1 assume;
      let e2' := translateBounded e2 assume;
      let e' := .app e1'.translate e2'.translate (removeBound ty);
      let extraWf :=
        match LExprT.toLMonoTy e1, ty with
        | .arrow _ .int, .bounded _ =>
          boundExprIfType ty e'
        | _, _ => [];
      ⟨e', (wfCallCondition (assume ++ e2'.assume) e1 e2'.translate) ++ extraWf ++ e1'.wfCond ++ e2'.wfCond, e1'.assume ++ e2'.assume ++ boundExprIfType ty e'⟩
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
      ⟨e'', addBoundedWf all_assume (boundExprIfType ty1 e'') e'.wfCond, e'.assume⟩
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
    ⟨.ite (addAssumptions (assume ++ c'.assume) c'.translate) (addAssumptions (assume ++ t'.assume) t'.translate) (addAssumptions (assume ++ f'.assume) f'.translate) .bool, c'.wfCond ++ t'.wfCond ++ f'.wfCond ,[]⟩
  | .ite c t f ty =>
    let c' := translateBounded c [];
    let t' := translateBounded t assume;
    let f' := translateBounded f assume;
    let e' := .ite (addAssumptions (assume ++ c'.assume) c'.translate) t'.translate f'.translate ty;
    ⟨e', (boundExprIfType ty e) ++ c'.wfCond ++ t'.wfCond ++ f'.wfCond, t'.assume ++ f'.assume⟩
  -- Equality is always bool-valued, so we can add assumptions
  | .eq e1 e2 ty =>
    let e1' := translateBounded e1 [];
    let e2' := translateBounded e2 [];
    ⟨addAssumptions (assume ++ e1'.assume ++ e2'.assume) (.eq e1'.translate e2'.translate ty), e1'.wfCond ++ e2'.wfCond, []⟩
  | .mdata m e =>
    let e' := translateBounded e assume;
    ⟨.mdata m e'.translate, e'.wfCond, e'.assume⟩

def translateBounded' [Coe String Identifier]  (e: LExprT Identifier) : LExprT Identifier :=
  (translateBounded e []).translate

def boundedWfConditions [Coe String Identifier]  (e: LExprT Identifier) : List (LExprT Identifier) :=
  (translateBounded e []).wfCond

-- NOTE: the assumptions are useful: they show us the "axioms" that we depend on (assumptions about external ops and free variables)

-- Tests

namespace Test

-- NOTE: with a semantics for LExpr/LExprT, we could prove the equivalences mentioned above

def natTy : LMonoTy := LMonoTy.bounded (.ble (.bconst 0) .bvar)
def leOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intLeFunc) e1 (.arrow .int .bool)) e2 .bool

def geOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intGeFunc) e1 (.arrow .int .bool)) e2 .bool

def addOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intAddFunc) e1 (.arrow .int .int)) e2 .int

def mulOp (e1 e2: LExprT String) : LExprT String := .app (.app (LFunc.opExprT intMulFunc) e1 (.arrow .int .int)) e2 .int

def notOp (e: LExprT String) : LExprT String := .app (LFunc.opExprT boolNotFunc) e .bool

-- easier to read
def eraseTy (x: LExprT String) :=
  LExpr.eraseTypes (LExprT.toLExpr x)

def eraseTys l := List.map eraseTy l

namespace TranslateTest

-- 1. ∀ (x: Nat), 0 <= x (quantified assumption)

def test1 := (@LExprT.quant String .all natTy (.bvar 0 natTy) (leOp (.const "0" .int) (.bvar 0 .int)))

#eval translateBounded' test1

--easier to read
#eval (eraseTy (translateBounded' test1) )

/-- info: Lambda.LExpr.quant
  (Lambda.QuantifierKind.all)
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.bvar 0)
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op
        "Bool.Implies"
        (some (Lambda.LMonoTy.tcons
           "arrow"
           [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
            Lambda.LMonoTy.tcons
              "arrow"
              [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
               Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
              (Lambda.LTyRestrict.nodata)]
           (Lambda.LTyRestrict.nodata))))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Int.Le"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
        (Lambda.LExpr.bvar 0)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Int.Le"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
      (Lambda.LExpr.bvar 0)))
-/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test1))

-- 2. λ(x: Nat), if 0 <= x then 1 else 0 (assumption inside ite)

def test2 : LExprT String := .abs (.ite (leOp (.const "0" .int) (.bvar 0 .int)) (.const "1" .int) (.const "2" .int) .int) (.arrow natTy .int)

#eval translateBounded' test2

#eval (LExpr.eraseTypes (LExprT.toLExpr (translateBounded' test2)))

/-- info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Bool.Implies"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Le"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Int.Le"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
        (Lambda.LExpr.bvar 0)))
    (Lambda.LExpr.const "1" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))
    (Lambda.LExpr.const "2" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))) -/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test2))

-- 3. λ(x: int), if foo x >= 0 then 1 else 0 (for foo: int -> Nat) (propagate op/application information)

def test3 : LExprT String := .abs (.ite (geOp (.app (.op "foo" (.arrow .int natTy)) (.bvar 0 .int) natTy) (.const "0" .int)) (.const "1" .int) (.const "0" .int) .int) (.arrow .int .int)

#eval translateBounded' test3

#eval (LExpr.eraseTypes (LExprT.toLExpr (translateBounded' test3)))

/--
info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Bool.Implies"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Le"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "foo"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.bvar 0))))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Int.Ge"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "foo"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))))
    (Lambda.LExpr.const "1" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))
    (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
    -/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test3))

-- 4. (x: Nat) + (y: Nat) >= 0 (free variable bounds)

def test4 : LExprT String := geOp (addOp (.fvar "x" natTy) (.fvar "y" natTy)) (.const "0" .int)

#eval translateBounded' test4

#eval (LExpr.eraseTypes (LExprT.toLExpr (translateBounded' test4)))

/--
info: Lambda.LExpr.app
  (Lambda.LExpr.app
    (Lambda.LExpr.op
      "Bool.Implies"
      (some (Lambda.LMonoTy.tcons
         "arrow"
         [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
          Lambda.LMonoTy.tcons
            "arrow"
            [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
             Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
            (Lambda.LTyRestrict.nodata)]
         (Lambda.LTyRestrict.nodata))))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Int.Le"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
      (Lambda.LExpr.fvar "x" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))))
  (Lambda.LExpr.app
    (Lambda.LExpr.app
      (Lambda.LExpr.op
        "Bool.Implies"
        (some (Lambda.LMonoTy.tcons
           "arrow"
           [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
            Lambda.LMonoTy.tcons
              "arrow"
              [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
               Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
              (Lambda.LTyRestrict.nodata)]
           (Lambda.LTyRestrict.nodata))))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Int.Le"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
        (Lambda.LExpr.fvar "y" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Int.Ge"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Add"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.fvar "x" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
          (Lambda.LExpr.fvar "y" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))))
      (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))) -/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test4))

-- 5. λ (x: Nat). λ (y: Nat). x + y >= 0 (multiple bound vars)

def test5 : LExprT String := .abs (.abs (geOp (addOp (.bvar 1 .int) (.bvar 0 .int)) (.const "0" .int)) (.arrow natTy .bool)) (.arrow natTy (.arrow natTy .bool))

#eval translateBounded' test5

#eval (LExpr.eraseTypes (LExprT.toLExpr (translateBounded' test5)))

/--
info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.abs
    (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Bool.Implies"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Le"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Bool.Implies"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.app
            (Lambda.LExpr.app
              (Lambda.LExpr.op
                "Int.Le"
                (some (Lambda.LMonoTy.tcons
                   "arrow"
                   [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                    Lambda.LMonoTy.tcons
                      "arrow"
                      [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                       Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                      (Lambda.LTyRestrict.nodata)]
                   (Lambda.LTyRestrict.nodata))))
              (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
            (Lambda.LExpr.bvar 1)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Ge"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.app
              (Lambda.LExpr.app
                (Lambda.LExpr.op
                  "Int.Add"
                  (some (Lambda.LMonoTy.tcons
                     "arrow"
                     [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                      Lambda.LMonoTy.tcons
                        "arrow"
                        [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                         Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)]
                        (Lambda.LTyRestrict.nodata)]
                     (Lambda.LTyRestrict.nodata))))
                (Lambda.LExpr.bvar 1))
              (Lambda.LExpr.bvar 0)))
          (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata))))))))
-/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test5))


-- 6. λ (x: Nat), if foo then λ (y: Nat). not (x = -1) else λ (y: Nat). x + y >= 0 (propagate inside branches of if-then-else)

def test6 : LExprT String := .abs (.ite (.op "foo" .bool) (.abs (notOp (.eq (.bvar 1 .int) (.const "-1" .int) .bool)) (.arrow natTy .bool)) (.abs (geOp (addOp (.bvar 1 .int) (.bvar 0 .int)) (.const "0" .int)) (.arrow natTy .bool)) (.arrow natTy .bool)) (.arrow natTy (.arrow natTy .bool))

#eval translateBounded' test6

#eval (LExpr.eraseTypes (LExprT.toLExpr (translateBounded' test6)))

/--
info: Lambda.LExpr.abs
  (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
  (Lambda.LExpr.ite
    (Lambda.LExpr.app
      (Lambda.LExpr.app
        (Lambda.LExpr.op
          "Bool.Implies"
          (some (Lambda.LMonoTy.tcons
             "arrow"
             [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
              Lambda.LMonoTy.tcons
                "arrow"
                [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                 Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                (Lambda.LTyRestrict.nodata)]
             (Lambda.LTyRestrict.nodata))))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Int.Le"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
          (Lambda.LExpr.bvar 0)))
      (Lambda.LExpr.op "foo" (some (Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)))))
    (Lambda.LExpr.abs
      (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Bool.Implies"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.app
            (Lambda.LExpr.app
              (Lambda.LExpr.op
                "Int.Le"
                (some (Lambda.LMonoTy.tcons
                   "arrow"
                   [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                    Lambda.LMonoTy.tcons
                      "arrow"
                      [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                       Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                      (Lambda.LTyRestrict.nodata)]
                   (Lambda.LTyRestrict.nodata))))
              (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
            (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Bool.Implies"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.app
              (Lambda.LExpr.app
                (Lambda.LExpr.op
                  "Int.Le"
                  (some (Lambda.LMonoTy.tcons
                     "arrow"
                     [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                      Lambda.LMonoTy.tcons
                        "arrow"
                        [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                         Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                        (Lambda.LTyRestrict.nodata)]
                     (Lambda.LTyRestrict.nodata))))
                (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
              (Lambda.LExpr.bvar 1)))
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Bool.Not"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.eq
              (Lambda.LExpr.bvar 1)
              (Lambda.LExpr.const "-1" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))))))
    (Lambda.LExpr.abs
      (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))
      (Lambda.LExpr.app
        (Lambda.LExpr.app
          (Lambda.LExpr.op
            "Bool.Implies"
            (some (Lambda.LMonoTy.tcons
               "arrow"
               [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                Lambda.LMonoTy.tcons
                  "arrow"
                  [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                   Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                  (Lambda.LTyRestrict.nodata)]
               (Lambda.LTyRestrict.nodata))))
          (Lambda.LExpr.app
            (Lambda.LExpr.app
              (Lambda.LExpr.op
                "Int.Le"
                (some (Lambda.LMonoTy.tcons
                   "arrow"
                   [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                    Lambda.LMonoTy.tcons
                      "arrow"
                      [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                       Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                      (Lambda.LTyRestrict.nodata)]
                   (Lambda.LTyRestrict.nodata))))
              (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
            (Lambda.LExpr.bvar 0)))
        (Lambda.LExpr.app
          (Lambda.LExpr.app
            (Lambda.LExpr.op
              "Bool.Implies"
              (some (Lambda.LMonoTy.tcons
                 "arrow"
                 [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                  Lambda.LMonoTy.tcons
                    "arrow"
                    [Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata),
                     Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                    (Lambda.LTyRestrict.nodata)]
                 (Lambda.LTyRestrict.nodata))))
            (Lambda.LExpr.app
              (Lambda.LExpr.app
                (Lambda.LExpr.op
                  "Int.Le"
                  (some (Lambda.LMonoTy.tcons
                     "arrow"
                     [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                      Lambda.LMonoTy.tcons
                        "arrow"
                        [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                         Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                        (Lambda.LTyRestrict.nodata)]
                     (Lambda.LTyRestrict.nodata))))
                (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))
              (Lambda.LExpr.bvar 1)))
          (Lambda.LExpr.app
            (Lambda.LExpr.app
              (Lambda.LExpr.op
                "Int.Ge"
                (some (Lambda.LMonoTy.tcons
                   "arrow"
                   [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                    Lambda.LMonoTy.tcons
                      "arrow"
                      [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                       Lambda.LMonoTy.tcons "bool" [] (Lambda.LTyRestrict.nodata)]
                      (Lambda.LTyRestrict.nodata)]
                   (Lambda.LTyRestrict.nodata))))
              (Lambda.LExpr.app
                (Lambda.LExpr.app
                  (Lambda.LExpr.op
                    "Int.Add"
                    (some (Lambda.LMonoTy.tcons
                       "arrow"
                       [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                        Lambda.LMonoTy.tcons
                          "arrow"
                          [Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata),
                           Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)]
                          (Lambda.LTyRestrict.nodata)]
                       (Lambda.LTyRestrict.nodata))))
                  (Lambda.LExpr.bvar 1))
                (Lambda.LExpr.bvar 0)))
            (Lambda.LExpr.const "0" (some (Lambda.LMonoTy.tcons "int" [] (Lambda.LTyRestrict.nodata)))))))))
            -/
#guard_msgs in
#eval (LExprT.toLExpr (translateBounded' test6))

end TranslateTest

-- Tests for wf conditions

namespace WFTest

-- 1. constant: (1: Nat)
-- Expected: 0 <= 1

def test1 : LExprT String := .const "1" natTy

/--info: [Lambda.LExpr.app
   (Lambda.LExpr.app (Lambda.LExpr.op "Int.Le" none) (Lambda.LExpr.const "0" none))
   (Lambda.LExpr.const "1" none)]
   -/
#guard_msgs in
#eval eraseTys (boundedWfConditions test1)

-- 2. application: (λ x: Nat. x) 1
-- Expected: 0 <= 1

def test2 : LExprT String := .app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.const "1" .int) .int

#eval eraseTys (boundedWfConditions test2)

-- 3. application with assumption (bottom up): (λ x: Nat. x) (foo : Nat)
-- Expected: 0 <= foo -> 0 <= foo

def test3 : LExprT String := .app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.op "foo" natTy) .int

#eval eraseTys (boundedWfConditions test3)

-- 4. application with assumption (top down): (λ x: Nat. (λ y: Nat. y) x)
-- Expected: 0 <= x -> 0 <= x

def test4 : LExprT String := .abs (.app (.abs (.bvar 0 .int) (.arrow natTy .int)) (.bvar 0 .int) .int) (.arrow natTy .int)

#eval eraseTys (boundedWfConditions test4)

-- 5. abstraction with assumption: (λ x: Nat. foo (x + 1)) (foo: Nat -> int)
-- Expected: 0 <= x -> 0 <= x + 1

def test5 : LExprT String := .abs (.app (.op "foo" (.arrow natTy .int)) (addOp (.bvar 0 .int) (.const "1" .int)) .int) (.arrow natTy .int)

#eval eraseTys (boundedWfConditions test5)

-- 6. quantified assumption: (∃ x: Nat. foo x) where (foo: Nat -> int)
-- Expected: 0 <= x -> 0 <= x

def test6 : LExprT String := .quant .exist natTy (.bvar 0 .int) (.app (.op "foo" (.arrow natTy .int)) (.bvar 0 .int) .int)

#eval eraseTys (boundedWfConditions test6)

-- 7. Lambda with bounded body (λ x: Nat. (x + 1: Nat))
-- Expected: 0 <= x -> 0 <= x + 1

def test7 : LExprT String := .abs (addOp (.bvar 0 .int) (.const "1" .int)) (.arrow natTy natTy)

#eval eraseTys (boundedWfConditions test7)


-- 8. Application with bounded body: (foo x) : Nat where foo: int -> Nat
-- Expected: [] (foo assumed)

def test8 : LExprT String := .app (.op "foo" (.arrow .int natTy)) (.fvar "x" .int) natTy

#eval eraseTys (boundedWfConditions test8)

-- 9. Application with bounded body, no assumption: (λ (x: int) . x * x) 1 : Nat
-- Expected: 0 <= (λ (x: int) . x * x) 1

def test9 : LExprT String := .app (.abs (mulOp (.bvar 0 .int) (.bvar 0 .int)) (.arrow .int .int)) (.const "1" .int) natTy

#eval eraseTys (boundedWfConditions test9)

-- 10. If-then-else with bounded body: if b then 1 else 0 : Nat
-- Expected: 0 <= if b then 1 else 0

def test10 : LExprT String := .ite (.const "b" .bool) (.const "1" .int) (.const "0" .int) natTy

#eval eraseTys (boundedWfConditions test10)

-- 11. If-then-else with bound functions: if b then λ (x: int). x * x : Nat else λ (y: int). 0 : Nat (whole type int -> Nat)
-- Expected: 0 <= x * x; 0 <= 0

def test11 : LExprT String := .ite (.const "b" .bool) (.abs (mulOp (.bvar 0 .int) (.bvar 0 .int)) (.arrow .int natTy)) (.abs (.const "0" .int) (.arrow .int natTy)) (.arrow .int natTy)

#eval eraseTys (boundedWfConditions test11)

end WFTest

--tests with more sophisticated bounded types (mostly AI generated)

namespace OtherTest

-- Test 1: Nested bounded function applications
-- Input: add : {x < 10} → {y < 5} → {z < 15}, applied to (3 : {x < 10}) and (2 : {x < 5})
-- Expected: translate = add 3 2, wfCond = [3 < 10, 2 < 5] (note: there are duplicates, should fix - change to Set)

def testNestedBoundedApps : LExprT String :=
  .app (.app (.op "add" (.arrow (.bounded (.blt (.bvar) (.bconst 10)))
                               (.arrow (.bounded (.blt (.bvar) (.bconst 5)))
                                      (.bounded (.blt (.bvar) (.bconst 15))))))
            (.const "3" (.bounded (.blt (.bvar) (.bconst 10))))
            (.arrow (.bounded (.blt (.bvar) (.bconst 5))) (.bounded (.blt (.bvar) (.bconst 15)))))
       (.const "2" (.bounded (.blt (.bvar) (.bconst 5))))
       (.bounded (.blt (.bvar) (.bconst 15)))

#eval eraseTys (boundedWfConditions testNestedBoundedApps)
#eval eraseTy (translateBounded' testNestedBoundedApps)

-- Test 2: Bounded variable in quantifier with complex bound expression
-- Input: ∀ (x : {x < 100 ∧ 0 ≤ x}). x = 42
-- Expected: translate = ∀ x:int. (x < 100 ∧ 0 ≤ x) → (x = 42), wfCond = []

def testComplexBoundInQuantifier : LExprT String :=
  .quant .all (.bounded (.band (.blt (.bvar) (.bconst 100))
                              (.ble (.bconst 0) (.bvar))))
         (.bvar 0 (.bounded (.band (.blt (.bvar) (.bconst 100))
                                  (.ble (.bconst 0) (.bvar)))))
         (.eq (.bvar 0 (.bounded (.band (.blt (.bvar) (.bconst 100))
                                       (.ble (.bconst 0) (.bvar)))))
              (.const "42" .int) .bool)

#eval eraseTys (boundedWfConditions testComplexBoundInQuantifier)
#eval eraseTy (translateBounded' testComplexBoundInQuantifier)

-- Test 3: If-then-else with bounded branches and boolean condition
-- Input: if ((getValue 5 : {0 ≤ x}) > 0) then (1 : {x < 10}) else (0 : {x < 10}) : {x < 10}
-- Expected: translate = if (0 ≤ getValue 5) → (getValue 5 > 0) then 1 else 0, wfCond = [1 < 10, 0 < 10, (if (getValue 5) then 1 else 0) < 10]
def testBoundedIte : LExprT String :=
  .ite (.app (.app (LFunc.opExprT intLtFunc)
                   (.const "0" .int)
                   (.arrow .int .bool))
             (.app (.op "getValue" (.arrow .int (.bounded (.ble (.bconst 0) (.bvar)))))
                   (.const "5" .int)
                   (.bounded (.ble (.bconst 0) (.bvar))))
             .bool)
       (.const "1" (.bounded (.blt (.bvar) (.bconst 10))))
       (.const "0" (.bounded (.blt (.bvar) (.bconst 10))))
       (.bounded (.blt (.bvar) (.bconst 10)))

#eval eraseTys (boundedWfConditions testBoundedIte)
#eval eraseTy (translateBounded' testBoundedIte)

-- Test 4: Lambda with bounded parameter and bounded return type
-- Input: λ (x : {0 ≤ x}). increment x : {y < 100}
-- Expected: translate = λ x:int. increment x, wfCond = [∀ x:int. 0 ≤ x → increment x < 100; 0 <= x -> 0 <= x]
def testBoundedLambda : LExprT String :=
  .abs (.app (.op "increment" (.arrow (.bounded (.ble (.bconst 0) (.bvar)))
                                     (.bounded (.blt (.bvar) (.bconst 100)))))
             (.bvar 0 (.bounded (.ble (.bconst 0) (.bvar))))
             (.bounded (.blt (.bvar) (.bconst 100))))
       (.arrow (.bounded (.ble (.bconst 0) (.bvar)))
               (.bounded (.blt (.bvar) (.bconst 100))))

#eval eraseTys (boundedWfConditions testBoundedLambda)
#eval eraseTy (translateBounded' testBoundedLambda)

-- Test 5: Equality between bounded expressions
-- Input: (square (3 : {-10 ≤ x ≤ 10}) : {0 ≤ y}) = (9 : {0 ≤ z})
-- Expected: translate = square 3 = 9, wfCond = [-10 ≤ 3 ≤ 10, 0 ≤ 9]
def testBoundedEquality : LExprT String :=
  .eq (.app (.op "square" (.arrow (.bounded (.band (.ble (.bconst (-10)) (.bvar))
                                                  (.ble (.bvar) (.bconst 10))))
                                 (.bounded (.ble (.bconst 0) (.bvar)))))
            (.const "3" (.bounded (.band (.ble (.bconst (-10)) (.bvar))
                                        (.ble (.bvar) (.bconst 10)))))
            (.bounded (.ble (.bconst 0) (.bvar))))
      (.const "9" (.bounded (.ble (.bconst 0) (.bvar))))
      .bool

#eval eraseTys (boundedWfConditions testBoundedEquality)
#eval eraseTy (translateBounded' testBoundedEquality)

-- Test 6: Free variable with bounded type in assumptions
-- Input: compare (x : {x < 50}) 25, with assumption [x < 50]
-- Expected: translate = (x < 50) → compare x 25, wfCond = []
def testFreeVarWithAssumptions : LExprT String :=
  .app (.app (.op "compare" (.arrow .int (.arrow .int .bool)))
             (.fvar "x" (.bounded (.blt (.bvar) (.bconst 50))))
             (.arrow .int .bool))
       (.const "25" .int)
       .bool

#eval eraseTys (boundedWfConditions testFreeVarWithAssumptions)
#eval eraseTy (translateBounded' testFreeVarWithAssumptions)

-- Test 7: Metadata preservation with bounded types
-- Input: @metadata(42 : {0 ≤ x < 100})
-- Expected: translate = @metadata(42), wfCond = [0 ≤ 42 < 100]
def testMetadataWithBounds : LExprT String :=
  .mdata (Info.mk "test_info")
         (.const "42" (.bounded (.band (.ble (.bconst 0) (.bvar))
                                      (.blt (.bvar) (.bconst 100)))))

#eval eraseTys (boundedWfConditions testMetadataWithBounds)
#eval eraseTy (translateBounded' testMetadataWithBounds)

-- Test 8: Chain of bounded function applications
-- Input: f3 (f2 (f1 5 : {x < 10}) : {x < 20}) : {x < 30}
-- Expected: translate = f3 (f2 (f1 5)), wfCond = [f1 5 < 10 → f2 (f1 5) < 20 -> f2 (f1 5) < 20, f1 5 < 10 -> f1 5 < 10]
def testBoundedChain : LExprT String :=
  .app (.op "f3" (.arrow (.bounded (.blt (.bvar) (.bconst 20)))
                        (.bounded (.blt (.bvar) (.bconst 30)))))
       (.app (.op "f2" (.arrow (.bounded (.blt (.bvar) (.bconst 10)))
                              (.bounded (.blt (.bvar) (.bconst 20)))))
             (.app (.op "f1" (.arrow .int (.bounded (.blt (.bvar) (.bconst 10)))))
                   (.const "5" .int)
                   (.bounded (.blt (.bvar) (.bconst 10))))
             (.bounded (.blt (.bvar) (.bconst 20))))
       (.bounded (.blt (.bvar) (.bconst 30)))

#eval eraseTys (boundedWfConditions testBoundedChain)
#eval eraseTy (translateBounded' testBoundedChain)

-- Test 9: Bounded type in boolean context with negation
-- Input: ¬((getValue 10 : {0 ≤ x}) < 5)
-- Expected: translate = (0 ≤ getValue 10) → ¬(getValue 10 < 5), wfCond = []
def testBoundedInBoolContext : LExprT String :=
  .app (LFunc.opExprT boolNotFunc)
       (.app (.app (LFunc.opExprT intLtFunc)
                   (.app (.op "getValue" (.arrow .int (.bounded (.ble (.bconst 0) (.bvar)))))
                         (.const "10" .int)
                         (.bounded (.ble (.bconst 0) (.bvar))))
                   (.arrow .int .bool))
             (.const "5" .int)
             .bool)
       .bool

#eval eraseTys (boundedWfConditions testBoundedInBoolContext)
#eval eraseTy (translateBounded' testBoundedInBoolContext)

end OtherTest

end Test


end Bounded

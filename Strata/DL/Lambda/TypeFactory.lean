/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Factory

/-!
## Lambda's Type Factory

This module contains Lambda's _type factory_, a mechanism for expressing datatypes (sum and product types). It synthesizes the corresponding constructors and eliminators as `LFunc`.
-/


namespace Lambda

open Std (ToFormat Format format)

---------------------------------------------------------------------

open LTy.Syntax

variable {IDMeta : Type} [DecidableEq IDMeta] [Inhabited IDMeta]

/--
A type constructor description. Note that the free type variables in `args` must be a subset of the `typeArgs` of the corresponding datatype.
-/
structure LConstr (IDMeta : Type) where
  name : Identifier IDMeta
  args : List (Identifier IDMeta × LMonoTy)
deriving Repr, DecidableEq

/--
A datatype description. `typeArgs` contains the free type variables of the given datatype.
-/
structure LDatatype (IDMeta : Type) where
  name : String
  typeArgs : List TyIdentifier
  constrs: List (@LConstr IDMeta)
deriving Repr, DecidableEq

/--
A datatype applied to arguments
-/
def data (d: LDatatype IDMeta) (args: List LMonoTy) : LMonoTy :=
  .tcons d.name args

/--
The default type application for a datatype. E.g. for datatype `type List α = | Nil | Cons α (List α)`, produces LMonoTy `List α`.
-/
def dataDefault (d: LDatatype IDMeta) : LMonoTy :=
  data d (d.typeArgs.map .ftvar)

/--
The `LFunc` corresponding to constructor `c` of datatype `d`. Note that constructor functions do not have bodies or evaluators, as they are values when applied to value arguments.
-/
def constrFunc (c: LConstr IDMeta) (d: LDatatype IDMeta) : LFunc IDMeta :=
  { name := c.name, typeArgs := d.typeArgs, inputs := c.args, output := dataDefault d, isConstr := true }

/-
Generating eliminators is trickier.
-/

/--
Generate `n` strings for argument names for the eliminator. Since there is no body, these strings should not need to be used.
-/
def genArgNames (n: Nat) : List (Identifier IDMeta) :=
  (List.range n).map (fun i => ⟨ "_x_" ++ toString i, Inhabited.default ⟩)

/--
Find `n` type arguments (string) not present in list by enumeration. Inefficient on large inputs.
-/
def freshTypeArgs (n: Nat) (l: List TyIdentifier) : List TyIdentifier :=
  -- Generate n + |l| names, by pigeonhole principle, enough unique ones
  let candidates := List.map (fun n => "$__ty" ++ toString n) (List.range (l.length + n));
  List.filter (fun t => ¬ t ∈ l) candidates

def freshTypeArg (l: List TyIdentifier) : TyIdentifier :=
  match freshTypeArgs 1 l with
  | t :: _ => t
  | _ => ""

def LMonoTy.mkArrow' (mty : LMonoTy) (mtys : LMonoTys) : LMonoTy :=
  match mtys with
  | [] => mty
  | m :: mrest => .arrow m (LMonoTy.mkArrow' mty mrest)

/--
Construct a recursive type argument for the eliminator.
Specifically, determine if a type `ty` contains a strictly positive, uniform occurrence of `t`, if so, replace this occurence with `retTy`.
Note that this does NOT check for strict positivity or uniformity, this is done in TODO.
-/
def genRecTy (t: LDatatype IDMeta) (retTy: LMonoTy)  (ty: LMonoTy) : Option LMonoTy :=
  if ty == dataDefault t then .some retTy else
  match ty with
  | .arrow t1 t2 => (genRecTy t retTy t2).map (fun r => .arrow t1 r)
  | _ => .none

def isRecTy (t: LDatatype IDMeta) (ty: LMonoTy) : Bool :=
  (genRecTy t .int ty).isSome

/--
Generate types for eliminator arguments.
The types are functions taking in 1) each argument of constructor `c` of datatype `d` and 2) recursive results for each recursive argument of `c` and returning an element of type `outputType`.
-/
def elimTy (outputType : LMonoTy) (t: LDatatype IDMeta) (c: LConstr IDMeta): LMonoTy :=
  match c.args with
  | [] => outputType
  | _ :: _ => LMonoTy.mkArrow' outputType (c.args.map Prod.snd ++ (c.args.map (fun x => (genRecTy t outputType x.2).toList)).flatten)

/--
Simulates pattern matching on operator o.
-/
def LExpr.matchOp (e: LExpr LMonoTy IDMeta) (o: Identifier IDMeta) : Option (List (LExpr LMonoTy IDMeta)) :=
  match getLFuncCall e with
  | (.op o1 _, args) => if o == o1 then .some args else .none
  | _ => .none

/--
Determine which constructor, if any, a datatype instance belongs to and get the arguments. Also gives the index in the constructor list as well as the recursive arguments (somewhat redundantly)
-/
def datatypeGetConstr (d: LDatatype IDMeta) (x: LExpr LMonoTy IDMeta) : Option (LConstr IDMeta × Nat × List (LExpr LMonoTy IDMeta) × List (LExpr LMonoTy IDMeta × LMonoTy)) :=
  List.foldr (fun (c, i) acc =>
    match x.matchOp c.name with
    | .some args =>
      -- Get the elements of args corresponding to recursive calls, in order
      let recs := (List.zip args (c.args.map Prod.snd)).filter (fun (_, ty) => isRecTy d ty)

      .some (c, i, args, recs)
    | .none => acc) .none (List.zip d.constrs (List.range d.constrs.length))

def LMonoTy.getArrowArgs (t: LMonoTy) : List LMonoTy :=
  match t with
  | .arrow t1 t2 => t1 :: t2.getArrowArgs
  | _ => []

/--
Determines which category a recursive type argument falls in: either `d(typeArgs)` or `τ₁ → ... → τₙ → d(typeArgs)`. In the later case, returns the `τ` list
-/
def recTyStructure (d: LDatatype IDMeta) (recTy: LMonoTy) : Unit ⊕ (List LMonoTy) :=
  if recTy == dataDefault d then .inl () else .inr (recTy.getArrowArgs)

--TODO: move
def LExpr.absMulti (tys: List LMonoTy) (body: LExpr LMonoTy IDMeta) : LExpr LMonoTy IDMeta :=
  List.foldr (fun ty e => .abs (.some ty) e) body tys

/--
Finds the lambda `bvar` arguments, in order, given an iterated lambda with `n` binders
-/
def getBVars (n: Nat) : List (LExpr LMonoTy IDMeta) :=
  (List.range n).reverse.map .bvar

/--
Construct recursive call of eliminator. Specifically, `recs` are the recursive arguments, in order, while `elimArgs` are the eliminator cases (e.g. for a binary tree with constructor `Node x l r`, where `l` and `r` are subtrees, `recs` is `[l, r]`)

Invariant: `recTy` must either have the form `d(typeArgs)` or `τ₁ → ... → τₙ → d(typeArgs)`. This is enforced by the filter in `dataTypeGetConstr`

TODO: give examples everywhere

-/
def elimRecCall (d: LDatatype IDMeta) (recArg: LExpr LMonoTy IDMeta) (recTy: LMonoTy) (elimArgs: List (LExpr LMonoTy IDMeta)) (elimName : Identifier IDMeta) : LExpr LMonoTy IDMeta :=
  match recTyStructure d recTy with
  | .inl _ => -- Generate eliminator call directly
    (LExpr.op elimName .none).mkApp (recArg :: elimArgs)
  | .inr funArgs => -- Construct lambda, first arg of eliminator is recArg applied to lambda arguments
    LExpr.absMulti funArgs ((LExpr.op elimName .none).mkApp (recArg.mkApp (getBVars funArgs.length) :: elimArgs))





/--
Generate eliminator concrete evaluator. Idea: match on 1st argument (e.g. `x : List α`) to determine constructor and corresponding arguments. If it matches the `n`th constructor, return `n+1`st element of input list applied to constructor arguments and recursive calls.
-/
def elimConcreteEval (d: LDatatype IDMeta) (elimName : Identifier IDMeta) :
  (LExpr LMonoTy IDMeta) → List (LExpr LMonoTy IDMeta) → (LExpr LMonoTy IDMeta) :=
  fun e args =>
    match args with
    | x :: xs =>
      match datatypeGetConstr d x with
      | .some (_, i, a, recs) =>
        match xs[i]? with
        | .some f => f.mkApp (a ++ recs.map (fun (r, rty) => elimRecCall d r rty xs elimName))
        | .none => e
      | .none => e
    | _ => e

/--
The `LFunc` corresponding to the eliminator for datatype `d`, called e.g. `ListElim` for type `List`.
-/
def elimFunc (d: LDatatype IDMeta) : LFunc IDMeta :=
  let outTyId := freshTypeArg d.typeArgs
  let elimName := d.name ++ "Elim";
  { name := elimName, typeArgs := outTyId :: d.typeArgs, inputs := List.zip (genArgNames (d.constrs.length + 1)) (dataDefault d :: d.constrs.map (elimTy (.ftvar outTyId) d)), output := .ftvar outTyId, concreteEval := elimConcreteEval d elimName}

def TypeFactory := Array (LDatatype IDMeta)

def TypeFactory.default : @TypeFactory IDMeta := #[]

/--
Generates the Factory (containing all constructor and eliminator functions) for a single datatype
-/
def LDatatype.genFactory  (d: LDatatype IDMeta) : @Lambda.Factory IDMeta :=
  (elimFunc d :: d.constrs.map (fun c => constrFunc c d)).toArray

/--
Generates the Factory (containing all constructor and eliminator functions) for the given `TypeFactory`
-/
def TypeFactory.genFactory (t: @TypeFactory IDMeta) : Except Format (@Lambda.Factory IDMeta) :=
  t.foldlM (fun f d => f.addFactory d.genFactory) Factory.default

end Lambda

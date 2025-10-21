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

variable {Identifier : Type} [Coe String Identifier] [DecidableEq Identifier] [ToFormat Identifier] [Inhabited Identifier]

/--
A type constructor description. Note that the free type variables in `args` must be a subset of the `typeArgs` of the corresponding datatype.
-/
structure LConstr (Identifier : Type) where
  name : Identifier
  args : List (Identifier × LMonoTy)
deriving Repr, DecidableEq

/--
A datatype description. `typeArgs` contains the free type variables of the given datatype.
-/
structure LDatatype (Identifier : Type) where
  name : String
  typeArgs : List TyIdentifier
  constrs: List (@LConstr Identifier)
deriving Repr, DecidableEq

/--
A datatype applied to arguments
-/
def data (d: LDatatype Identifier) (args: List LMonoTy) : LMonoTy :=
  .tcons d.name args

/--
The default type application for a datatype. E.g. for datatype `type List α = | Nil | Cons α (List α)`, produces LMonoTy `List α`.
-/
def dataDefault (d: LDatatype Identifier) : LMonoTy :=
  data d (d.typeArgs.map .ftvar)

-- TODO could switch to generating names once we have that, can remove Identifier from LConstr

/--
The `LFunc` corresponding to constructor `c` of datatype `d`. Note that constructor functions do not have bodies or evaluators, as they are values when applied to value arguments.
-/
def constrFunc (c: LConstr Identifier) (d: LDatatype Identifier) : LFunc Identifier :=
  { name := c.name, typeArgs := d.typeArgs, inputs := c.args, output := dataDefault d, isConstr := true }

-- TODO: add constructor Bool to LFunc for evaluator and update here

/-
Generating eliminators is trickier.
-/

-- NOTE: can generate dummy arg names for eliminator, since the function doesn't have a body, it is OK

/--
Generate `n` strings for argument names for the eliminator. Since there is no body, these strings should not need to be used.
-/
def genArgNames (n: Nat) : List Identifier := sorry

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
Generate types for eliminator arguments.
The types are functions taking in each constructor argument and returning an element of type `outputType`. Note that there is NO recursive argument (yet), right now this only allows simple case reasoning.
-/
def elimTy (outputType : LMonoTy)  (c: LConstr Identifier): LMonoTy :=
  match c.args with
  | [] => outputType
  | _ :: _ => LMonoTy.mkArrow' outputType (c.args.map Prod.snd)



/--
Simulates pattern matching on operator o. We cannot do true pattern matching because (1) Identifiers are abstract and (2) we must determine the correct number of .app calls and arguments
-/
def LExpr.matchOp (x: LExpr LMonoTy Identifier) (o: Identifier) : Option (List (LExpr LMonoTy Identifier)) :=
  match x with
  | .op o1 _ => if o == o1 then .some [] else .none
  | .app e1 e2 => (e1.matchOp o).bind (fun l => l ++ [e2])
  | _ => .none


/--
Determine which constructor, if any, a datatype instance belongs to and get the arguments. Also gives the index in the constructor list
-/
def datatypeGetConstr (d: LDatatype Identifier) (x: LExpr LMonoTy Identifier) : Option (LConstr Identifier × Nat × List (LExpr LMonoTy Identifier)) :=
  List.foldr (fun (c, i) acc =>
    match x.matchOp c.name with
    | .some args => .some (c, i, args)
    | .none => acc) .none (List.zip d.constrs (List.range d.constrs.length))

def LExpr.appMultiAux (e1: LExpr TypeType Identifier) (args: List (LExpr TypeType Identifier)) : LExpr TypeType Identifier :=
  match args with
  | [] => e1
  | e :: es => .app (e1.appMultiAux es) e

def LExpr.appMulti (e1: LExpr TypeType Identifier) (args: List (LExpr TypeType Identifier)) := e1.appMultiAux args.reverse

/--
Generate eliminator concrete evaluator. Idea: match on 1st argument (e.g. `x : List α`) to determine constructor and corresponding arguments. If it matches the `n`th constructor, return `n+1`th element of input list applied to constructor arguments.
-/
def elimConcreteEval (d: LDatatype Identifier) :
  (LExpr LMonoTy Identifier) → List (LExpr LMonoTy Identifier) → (LExpr LMonoTy Identifier) :=
  fun e args =>
    match args with
    | x :: xs =>
      match datatypeGetConstr d x with
      | .some (_, i, a) =>
        match xs[i]? with
        | .some f => f.appMulti a
        | .none => e
      | .none => e
    | _ => e

/--
The `LFunc` corresponding to the eliminator for datatype `d`, called e.g. `ListElim` for type `List`.
`genArgNames` is temporary
-/
def elimFunc (genArgNames: Nat -> List Identifier) (d: LDatatype Identifier) : LFunc Identifier :=
  let outTyId := freshTypeArg d.typeArgs
  { name := d.name ++ "Elim", typeArgs := d.typeArgs, inputs := List.zip (genArgNames (d.constrs.length + 1)) (dataDefault d :: d.constrs.map (elimTy (.ftvar outTyId))), output := .ftvar outTyId, concreteEval := elimConcreteEval d}

def TypeFactory := Array (LDatatype Identifier)

/--
Generates the Factory (containing all constructor and eliminator functions) for a single datatype
-/
def LDatatype.genFactory (genArgNames: Nat -> List Identifier)  (d: LDatatype Identifier) : @Lambda.Factory Identifier :=
  (elimFunc genArgNames d :: d.constrs.map (fun c => constrFunc c d)).toArray

/--
Generates the Factory (containing all constructor and eliminator functions) for the given `TypeFactory`
-/
def TypeFactory.genFactory (genArgNames: Nat -> List Identifier) (t: @TypeFactory Identifier) : Except Format (@Lambda.Factory Identifier) :=
  t.foldlM (fun f d => f.addFactory (d.genFactory genArgNames)) Factory.default

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Factory

/-!
## Lambda's Type Factory

This module contains Lambda's _type factory_, a mechanism for expressing
inductive datatypes (sum and product types). It synthesizes the corresponding
constructors and eliminators as `LFunc`. It currently does not allow
non-uniform or mutually inductive types.
-/


namespace Lambda

open Std (ToFormat Format format)

---------------------------------------------------------------------

open LTy.Syntax

variable {IDMeta : Type} [DecidableEq IDMeta] [Inhabited IDMeta]

/-
Prefixes for newly generated type and term variables.
See comment for `TEnv.genExprVar` for naming.
Note that `exprPrefix` is designed to avoid clashes with `exprPrefix`
in `LExprTypeEnv.lean`.
-/
def tyPrefix : String := "$__ty"
def exprPrefix : String := "$__tvar"

/--
A type constructor description. The free type variables in `args` must be a
subset of the `typeArgs` of the corresponding datatype.
-/
structure LConstr (IDMeta : Type) where
  name : Identifier IDMeta
  args : List (Identifier IDMeta × LMonoTy)
  testerName : String := "is" ++ name.name
deriving Repr, DecidableEq

instance: ToFormat (LConstr IDMeta) where
  format c := f!"Name:{Format.line}{c.name}{Format.line}\
                 Args:{Format.line}{c.args}{Format.line}\
                 Tester:{Format.line}{c.testerName}{Format.line}"

/--
A datatype description. `typeArgs` contains the free type variables of the
given datatype.
-/
structure LDatatype (IDMeta : Type) where
  name : String
  typeArgs : List TyIdentifier
  constrs: List (@LConstr IDMeta)
  constrs_ne : constrs.length != 0
deriving Repr, DecidableEq

instance : ToFormat (LDatatype IDMeta) where
  format d := f!"type:{Format.line}{d.name}{Format.line}\
              Type Arguments:{Format.line}{d.typeArgs}{Format.line}\
              Constructors:{Format.line}{d.constrs}{Format.line}"

/--
A datatype applied to arguments
-/
def data (d: LDatatype IDMeta) (args: List LMonoTy) : LMonoTy :=
  .tcons d.name args

/--
The default type application for a datatype. E.g. for datatype
`type List α = | Nil | Cons α (List α)`, produces LMonoTy `List α`.
-/
def dataDefault (d: LDatatype IDMeta) : LMonoTy :=
  data d (d.typeArgs.map .ftvar)

---------------------------------------------------------------------

-- Typechecking

/--
Determines whether type name `n` appear in type `t`
-/
def tyNameAppearsIn (n: String) (t: LMonoTy) : Bool :=
  match t with
  | .tcons n1 args => n == n1 || List.any (List.map (tyNameAppearsIn n) args) id
  | _ => false

/--
Determines whether all occurences of type name `n` within type `t` have
arguments `args`. The string `c` appears only for error message information.
-/
def checkUniform (c: String) (n: String) (args: List LMonoTy) (t: LMonoTy) : Except Format Unit :=
  match t with
  | .tcons n1 args1 => if n == n1 && args == args1 then .ok ()
    else if n == n1 then .error f!"Error in constructor {c}: Non-uniform occurrence of {n}, which is applied to {args1} when it should be applied to {args}"
    else List.foldrM (fun t u => do
      let _ ← checkUniform c n args t
      .ok u
      ) () args1
  | _ => .ok ()


/--
Check for strict positivity and uniformity of datatype `d` in type `ty`. The
string `c` appears only for error message information.
-/
def checkStrictPosUnifTy (c: String) (d: LDatatype IDMeta) (ty: LMonoTy) : Except Format Unit :=
  match ty with
  | .arrow t1 t2 =>
    if tyNameAppearsIn d.name t1 then
      .error f!"Error in constructor {c}: Non-strictly positive occurrence of {d.name} in type {ty}"
    else checkStrictPosUnifTy c d t2
  | _ => checkUniform c d.name (d.typeArgs.map .ftvar) ty

/--
Check for strict positivity and uniformity of a datatype
-/
def checkStrictPosUnif (d: LDatatype IDMeta) : Except Format Unit :=
  List.foldrM (fun ⟨name, args, _⟩ _ =>
    List.foldrM (fun ⟨ _, ty ⟩ _ =>
      checkStrictPosUnifTy name.name d ty
    ) () args
  ) () d.constrs

---------------------------------------------------------------------

-- Generating constructors and eliminators

/--
The `LFunc` corresponding to constructor `c` of datatype `d`. Constructor
functions do not have bodies or `concreteEval` functions, as they are values
when applied to value arguments.
-/
def constrFunc (c: LConstr T.IDMeta) (d: LDatatype T.IDMeta) : LFunc T :=
  { name := c.name, typeArgs := d.typeArgs, inputs := c.args, output := dataDefault d, isConstr := true }

/--
Generate `n` strings for argument names for the eliminator. Since there is no
body, these strings do not need to be used.
-/
private def genArgNames (n: Nat) : List (Identifier IDMeta) :=
  (List.range n).map (fun i => ⟨exprPrefix ++ toString i, Inhabited.default⟩)

private def genArgName : Identifier IDMeta :=
  have H: genArgNames 1 ≠ [] := by unfold genArgNames; grind
  List.head (genArgNames 1) H

/--
Find `n` type arguments (string) not present in list by enumeration.
Inefficient on large inputs.
-/
def freshTypeArgs (n: Nat) (l: List TyIdentifier) : List TyIdentifier :=
  -- Generate n + |l| names to ensure enough unique ones
  let candidates := List.map (fun n => tyPrefix ++ toString n) (List.range (l.length + n));
  List.take n (List.filter (fun t => ¬ t ∈ l) candidates)

/--
Find a fresh type argument not present in `l` by enumeration. Relies on the fact
that `freshTypeArgs n` gives a list of exactly `n` fresh type arguments.
-/
def freshTypeArg (l: List TyIdentifier) : TyIdentifier :=
  match freshTypeArgs 1 l with
  | t :: _ => t
  | _ => ""

/--
Construct a recursive type argument for the eliminator.
Specifically, determine if a type `ty` contains a strictly positive, uniform
occurrence of `t`, if so, replace this occurence with `retTy`.

For example, given `ty` (int -> (int -> List α)), datatype List, and `retTy` β,
gives (int -> (int -> β))
-/
def genRecTy (t: LDatatype IDMeta) (retTy: LMonoTy) (ty: LMonoTy) : Option LMonoTy :=
  if ty == dataDefault t then .some retTy else
  match ty with
  | .arrow t1 t2 => (genRecTy t retTy t2).map (fun r => .arrow t1 r)
  | _ => .none

def isRecTy (t: LDatatype IDMeta) (ty: LMonoTy) : Bool :=
  (genRecTy t .int ty).isSome

/--
Generate types for eliminator arguments.
The types are functions taking in 1) each argument of constructor `c` of
datatype `d` and 2) recursive results for each recursive argument of `c` and
returning an element of type `outputType`.

For example, the eliminator type argument for `cons` is α → List α → β → β
-/
def elimTy (outputType : LMonoTy) (t: LDatatype IDMeta) (c: LConstr IDMeta): LMonoTy :=
  match c.args with
  | [] => outputType
  | _ :: _ => LMonoTy.mkArrow' outputType (c.args.map Prod.snd ++ (c.args.map (fun x => (genRecTy t outputType x.2).toList)).flatten)

/--
Simulates pattern matching on operator o.
-/
def LExpr.matchOp {T: LExprParams} [BEq T.Identifier] (e: LExpr T.mono) (o: T.Identifier) : Option (List (LExpr T.mono)) :=
  match getLFuncCall e with
  | (.op _ o1 _, args) => if o == o1 then .some args else .none
  | _ => .none

/--
Determine which constructor, if any, a datatype instance belongs to and get the
arguments. Also gives the index in the constructor list as well as the
recursive arguments (somewhat redundantly)

For example, expression `cons x l` gives constructor `cons`, index `1` (cons is
the second constructor), arguments `[x, l]`, and recursive argument
`[(l, List α)]`
-/
def datatypeGetConstr {T: LExprParams} [BEq T.Identifier] (d: LDatatype T.IDMeta) (x: LExpr T.mono) : Option (LConstr T.IDMeta × Nat × List (LExpr T.mono) × List (LExpr T.mono × LMonoTy)) :=
  List.foldr (fun (c, i) acc =>
    match x.matchOp c.name with
    | .some args =>
      -- Get the elements of args corresponding to recursive calls, in order
      let recs := (List.zip args (c.args.map Prod.snd)).filter (fun (_, ty) => isRecTy d ty)

      .some (c, i, args, recs)
    | .none => acc) .none (List.zip d.constrs (List.range d.constrs.length))

/--
Determines which category a recursive type argument falls in: either `d
(typeArgs)` or `τ₁ → ... → τₙ → d(typeArgs)`.
In the later case, returns the `τ` list
-/
def recTyStructure (d: LDatatype IDMeta) (recTy: LMonoTy) : Unit ⊕ (List LMonoTy) :=
  if recTy == dataDefault d then .inl () else .inr (recTy.getArrowArgs)

/--
Finds the lambda `bvar` arguments, in order, given an iterated lambda with `n`
binders
-/
private def getBVars {T: LExprParams} (m: T.Metadata) (n: Nat) : List (LExpr T.mono) :=
  (List.range n).reverse.map (.bvar m)

/--
Construct recursive call of eliminator. Specifically, `recs` are the recursive
arguments, in order, while `elimArgs` are the eliminator cases (e.g. for a
binary tree with constructor `Node x l r`, where `l` and `r` are subtrees,
`recs` is `[l, r]`)

Invariant: `recTy` must either have the form `d(typeArgs)` or `τ₁ → ... → τₙ → d
(typeArgs)`. This is enforced by `dataTypeGetConstr`

-/
def elimRecCall {T: LExprParams} (d: LDatatype T.IDMeta) (recArg: LExpr T.mono) (recTy: LMonoTy) (elimArgs: List (LExpr T.mono)) (m: T.Metadata) (elimName : Identifier T.IDMeta) : LExpr T.mono :=
  match recTyStructure d recTy with
  | .inl _ => -- Generate eliminator call directly
    (LExpr.op m elimName .none).mkApp m (recArg :: elimArgs)
  | .inr funArgs =>
  /- Construct lambda, first arg of eliminator is recArg applied to lambda
  arguments -/
    LExpr.absMulti m funArgs ((LExpr.op m elimName .none).mkApp m (recArg.mkApp m (getBVars m funArgs.length) :: elimArgs))

/--
Generate eliminator concrete evaluator. Idea: match on 1st argument (e.g.
`x : List α`) to determine constructor and corresponding arguments. If it
matches the `n`th constructor, return `n+1`st element of input list applied to
constructor arguments and recursive calls.

Examples:
1. For `List α`, the generated function behaves as follows:
`List$Elim Nil e1 e2 = e1` and
`List$Elim (x :: xs) e1 e2 = e2 x xs (List$Elim xs e1 e2)`
2. For `tree = | T (int -> tree)`, the generated function is:
`Tree$Elim (T f) e = e f (fun (x: int) => Tree$Elim (f x) e)`

-/
def elimConcreteEval {T: LExprParams} [BEq T.Identifier] (d: LDatatype T.IDMeta) (m: T.Metadata) (elimName : Identifier T.IDMeta) :
  T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono) :=
  fun _ args =>
    match args with
    | x :: xs =>
      match datatypeGetConstr d x with
      | .some (_, i, a, recs) =>
        match xs[i]? with
        | .some f => f.mkApp m (a ++ recs.map (fun (r, rty) => elimRecCall d r rty xs m elimName))
        | .none => .none
      | .none => .none
    | _ => .none

def elimFuncName (d: LDatatype IDMeta) : Identifier IDMeta :=
  d.name ++ "$Elim"

/--
The `LFunc` corresponding to the eliminator for datatype `d`, called e.g.
`List$Elim` for type `List`.
-/
def elimFunc [Inhabited T.IDMeta] [BEq T.Identifier] (d: LDatatype T.IDMeta) (m: T.Metadata) : LFunc T :=
  let outTyId := freshTypeArg d.typeArgs
  { name := elimFuncName d, typeArgs := outTyId :: d.typeArgs, inputs := List.zip (genArgNames (d.constrs.length + 1)) (dataDefault d :: d.constrs.map (elimTy (.ftvar outTyId) d)), output := .ftvar outTyId, concreteEval := elimConcreteEval d m (elimFuncName d)}

---------------------------------------------------------------------

-- Generating testers and destructors

/--
Generate tester body (see `testerFunc`). The body assigns each argument of the
eliminator (fun _ ... _ => b), where b is true for the constructor's index and
false otherwise. This requires knowledge of the number of arguments for each
argument to the eliminator.-/
def testerFuncBody {T : LExprParams} [Inhabited T.IDMeta] (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) (input: LExpr T.mono) (m: T.Metadata) : LExpr T.mono :=
  -- Number of arguments is number of constr args + number of recursive args
  let numargs (c: LConstr T.IDMeta) := c.args.length + ((c.args.map Prod.snd).filter (isRecTy d)).length
  let args := List.map (fun c1 => LExpr.absMultiInfer m (numargs c1) (.boolConst m (c.name.name == c1.name.name))) d.constrs
  .mkApp m (.op m (elimFuncName d) .none) (input :: args)

/--
Generate tester function for a constructor (e.g. `List$isCons` and
`List$isNil`). The semantics of the testers are given via a body,
and they are defined in terms of eliminators. For example:
`List$isNil l := List$Elim l true (fun _ _ _ => false)`
`List$isCons l := List$Elim l false (fun _ _ _ => true)`
-/
def testerFunc {T} [Inhabited T.IDMeta] (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) (m: T.Metadata) : LFunc T :=
  let arg := genArgName
  {name := c.testerName,
   typeArgs := d.typeArgs,
   inputs := [(arg, dataDefault d)],
   output := .bool,
   body := testerFuncBody d c (.fvar m arg .none) m,
   attr := #["inline_if_val"]
  }

/--
Concrete evaluator for destructor: if given instance of the constructor,
the `i`th projection retrieves the `i`th argument of the application
-/
def destructorConcreteEval {T: LExprParams} [BEq T.Identifier] (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) (idx: Nat) :
  List (LExpr T.mono) → Option (LExpr T.mono) :=
  fun args =>
    match args with
    | [x] =>
      (datatypeGetConstr d x).bind (fun (c1, _, a, _) =>
        if c1.name.name == c.name.name
        then a[idx]? else none)
    | _ => none

/--
Generate destructor functions for a constructor, which extract the
constructor components, e.g.
`List$ConsProj0 (Cons h t) = h`
`List$ConsProj1 (Cons h t) = t`
These functions are partial, `List@ConsProj0 Nil` is undefined.
-/
def destructorFuncs {T} [BEq T.Identifier] [Inhabited T.IDMeta]  (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) : List (LFunc T) :=
  c.args.mapIdx (fun i (name, ty) =>
    let arg := genArgName
    {
      name := name,
      typeArgs := d.typeArgs,
      inputs := [(arg, dataDefault d)],
      output := ty,
      concreteEval := some (fun _ => destructorConcreteEval d c i)})


---------------------------------------------------------------------

-- Type Factories

def TypeFactory := Array (LDatatype IDMeta)

instance: ToFormat (@TypeFactory IDMeta) where
  format f := Std.Format.joinSep f.toList f!"{Format.line}"

instance : Inhabited (@TypeFactory IDMeta) where
  default := #[]

def TypeFactory.default : @TypeFactory IDMeta := #[]

/--
Generates the Factory (containing the eliminator, constructors, testers,
and destructors) for a single datatype.
-/
def LDatatype.genFactory {T: LExprParams} [inst: Inhabited T.Metadata] [Inhabited T.IDMeta]  [ToFormat T.IDMeta] [BEq T.Identifier] (d: LDatatype T.IDMeta): Except Format (@Lambda.Factory T) := do
  _ ← checkStrictPosUnif d
  Factory.default.addFactory (
      elimFunc d inst.default ::
      d.constrs.map (fun c => constrFunc c d) ++
      d.constrs.map (fun c => testerFunc d c inst.default) ++
      (d.constrs.map (fun c => destructorFuncs d c)).flatten).toArray

/--
Constructs maps of generated functions for datatype `d`: map of
constructors, testers, and destructors in order. Each maps names to
the datatype and constructor AST.
-/
def LDatatype.genFunctionMaps {T: LExprParams} [Inhabited T.IDMeta] [BEq T.Identifier] (d: LDatatype T.IDMeta) :
  Map String (LDatatype T.IDMeta × LConstr T.IDMeta) ×
  Map String (LDatatype T.IDMeta × LConstr T.IDMeta) ×
  Map String (LDatatype T.IDMeta × LConstr T.IDMeta) :=
  (Map.ofList (d.constrs.map (fun c => (c.name.name, (d, c)))),
   Map.ofList (d.constrs.map (fun c => (c.testerName, (d, c)))),
   Map.ofList (d.constrs.map (fun c =>
      (destructorFuncs d c).map (fun f => (f.name.name, (d, c))))).flatten)

/--
Generates the Factory (containing all constructor and eliminator functions) for the given `TypeFactory`
-/
def TypeFactory.genFactory {T: LExprParams} [inst: Inhabited T.Metadata] [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier] (t: @TypeFactory T.IDMeta) : Except Format (@Lambda.Factory T) :=
  t.foldlM (fun f d => do
    let f' ← d.genFactory
    f.addFactory f') Factory.default

def TypeFactory.getType (F : @TypeFactory IDMeta) (name : String) : Option (LDatatype IDMeta) :=
  F.find? (fun d => d.name == name)

/--
Add an `LDatatype` to an existing `TypeFactory`, checking that no
types are duplicated.
-/
def TypeFactory.addDatatype (t: @TypeFactory IDMeta) (d: LDatatype IDMeta) : Except Format (@TypeFactory IDMeta) :=
  -- Check that type is not redeclared
  match t.getType d.name with
  | none => .ok (t.push d)
  | some d' => .error f!"A datatype of name {d.name} already exists! \
              Redefinitions are not allowed.\n\
              Existing Type: {d'}\n\
              New Type:{d}"


---------------------------------------------------------------------

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.Factory
import Strata.DL.Util.List

/-!
## Lambda's Type Factory

This module contains Lambda's _type factory_, a mechanism for expressing
inductive datatypes (sum and product types). It synthesizes the corresponding
constructors and eliminators as `LFunc`. It currently does not allow
non-uniform or mutually inductive types.
-/


namespace Lambda

open Strata
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

/-- A group of mutually recursive datatypes. -/
abbrev MutualDatatype (IDMeta : Type) := List (LDatatype IDMeta)

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
arguments `args`. `c` appears only for error message information.
-/
def checkUniform (c: Format) (n: String) (args: List LMonoTy) (t: LMonoTy) : Except DiagnosticModel Unit :=
  match t with
  | .tcons n1 args1 => if n == n1 && args == args1 then .ok ()
    else if n == n1 then .error <| DiagnosticModel.fromFormat f!"Error in constructor {c}: Non-uniform occurrence of {n}, which is applied to {args1} when it should be applied to {args}"
    else List.foldrM (fun t u => do
      let _ ← checkUniform c n args t
      .ok u
      ) () args1
  | _ => .ok ()

/--
Check for strict positivity and uniformity of all datatypes in a mutual block
within type `ty`. `c` appears only for error message information.
-/
def checkStrictPosUnifTy (c: Format) (block: MutualDatatype IDMeta) (ty: LMonoTy) : Except DiagnosticModel Unit :=
  match ty with
  | .arrow t1 t2 =>
    -- Check that no datatype in the block appears in the left side of an arrow
    match block.find? (fun d => tyNameAppearsIn d.name t1) with
    | some d => .error <| DiagnosticModel.fromFormat f!"Error in constructor {c}: Non-strictly positive occurrence of {d.name} in type {ty}"
    | none => checkStrictPosUnifTy c block t2
  | _ =>
    -- Check uniformity for all datatypes in the block
    block.foldlM (fun _ d => checkUniform c d.name (d.typeArgs.map .ftvar) ty) ()

/--
Check for strict positivity and uniformity across a mutual block of datatypes
-/
def checkStrictPosUnif (block: MutualDatatype IDMeta) : Except DiagnosticModel Unit :=
  block.foldlM (fun _ d =>
    d.constrs.foldlM (fun _ ⟨name, args, _⟩ =>
      args.foldlM (fun _ ⟨_, ty⟩ =>
        checkStrictPosUnifTy name.name block ty
      ) ()
    ) ()
  ) ()

/--
Validate a mutual block: check non-empty and no duplicate names.
-/
def validateMutualBlock (block: MutualDatatype IDMeta) : Except DiagnosticModel Unit := do
  if block.isEmpty then
    .error <| DiagnosticModel.fromFormat f!"Error: Empty mutual block is not allowed"
  match (block.foldl (fun (o, names) d =>
    if d.name ∈ names then (some d, names) else (o, Std.HashSet.insert names d.name)) (none, ∅)).1 with
  | some dup => .error <| DiagnosticModel.fromFormat f!"Duplicate datataype name in mutual block: {dup}"
  | none => .ok ()

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

---------------------------------------------------------------------

-- Mutual block eliminator generation

/-
In the following, we will use 3 examples to demonstrate different parts:
1. `List α = | Nil | Cons α (List α)` should generate an eliminator of
type `list α → β → (α → List α → β → β) → β` with rules
`List$Elim Nil e1 e2 = e1` and
`List$Elim (x :: xs) e1 e2 = e2 x xs (List$Elim xs e1 e2)`
2. `tree = | T (int -> tree)` should generate an eliminator of type
`tree → ((int → tree) → (int → β)) → β with rule
`Tree$Elim (T f) e = e f (fun (x: int) => Tree$Elim (f x) e)`
3. `RoseTree = R (Forest) with Forest = FNil | FCons RoseTree Forest`
should generate two eliminators:
`RoseTree$Elim : RoseTree → (Forest → β → α) → β → (RoseTree → Forest → α → β → β) → α`
`Forest$Elim : Forest → (Forest → β → α) → β → (RoseTree → Forest → α → β → β) → β`
with behavior:
`RoseTree$Elim (R x) r1 f1 f2 = r1 x (Forest$Elim x r1 f1 f2)`
`Forest$Elim FNil r1 f1 f2 = f1`
`Forest$Elim (Fcons r f) r1 f1 f2 = f2 r f (Rose$Elim r r1 f1 f2) (Forest$Elim f r1 f1 f2)`
-/

/--
Construct a recursive type argument for the eliminator.
Specifically, determine if a type `ty` contains a strictly positive, uniform
occurrence of a datatype in `block`, if so,
replace this occurence with the corresponding variable from `retTyVars`.

Examples:
Single datatype: given `ty` (int -> (int -> List α)), datatype List,
and `retTys` [β], gives (int -> (int -> β))
Mutually recursive type: given `ty` (int -> (int -> RoseTree)) and
`retTys` `[β₁, β₂]`, gives (int -> (int -> β₁))
-/
def genRecTy (block : MutualDatatype IDMeta) (retTyVars : List TyIdentifier) (ty : LMonoTy) : Option LMonoTy :=
  match block.findIdx? (fun d => ty == dataDefault d) with
  | some idx => retTyVars[idx]? |>.map LMonoTy.ftvar
  | none =>
    match ty with
    | .arrow t1 t2 => (genRecTy block retTyVars t2).map (fun r => .arrow t1 r)
    | _ => none

/-- Find which datatype in a mutual block a recursive type refers to. -/
def findRecTy (block : MutualDatatype IDMeta) (ty : LMonoTy) : Option (LDatatype IDMeta) :=
  match ty with
  | .arrow _ t2 => findRecTy block t2
  | _ => block.find? (fun d => ty == dataDefault d)

/-- Check if a type is recursive within a mutual block. -/
def isRecTy (block : MutualDatatype IDMeta) (ty : LMonoTy) : Bool :=
  (findRecTy block ty).isSome



/--
Generate types for eliminator arguments.
The types are functions taking in 1) each argument of constructor `c` of
each datatype in the block `block` (in order) and
2) recursive results for each recursive argument of `c`
It returns an element of type `retTyVars[dtIdx]`, where `dtIdx` is the
index of this constructor in the mutual block

Examples:
1. For `Cons`, the eliminator type argument is `α → List α → β → β`
2. For `FCons`, the eliminator type argument is `RoseTree → Forest → α → β → β`
-/
def elimTy (block : MutualDatatype IDMeta) (retTyVars : List TyIdentifier)
    (dtIdx : Nat) (c : LConstr IDMeta) : LMonoTy :=
  let outputType := retTyVars[dtIdx]? |>.map LMonoTy.ftvar |>.getD (.ftvar "")
  match c.args with
  | [] => outputType
  | _ :: _ =>
    let recTypes := c.args.filterMap fun (_, ty) => genRecTy block retTyVars ty
    LMonoTy.mkArrow' outputType (c.args.map Prod.snd ++ recTypes)

/-- Compute global constructor index within a mutual block.
  E.g. if we have a mutual type with types A, B, C, with constructors
  A1, A2, B1, B2, B3, C1, the global index of B3 is 4. -/
def blockConstrIdx (block : MutualDatatype IDMeta) (dtIdx : Nat) (constrIdx : Nat) : Nat :=
  let prevCount := (block.take dtIdx).foldl (fun acc d => acc + d.constrs.length) 0
  prevCount + constrIdx

/--
Simulates pattern matching on operator o.
-/
def LExpr.matchOp {T: LExprParams} [BEq T.Identifier] (e: LExpr T.mono) (o: T.Identifier) : Option (List (LExpr T.mono)) :=
  match getLFuncCall e with
  | (.op _ o1 _, args) => if o == o1 then .some args else .none
  | _ => .none

/--
Determine the constructor, index, and arguments for a constructor application.
E.g. `Cons x l` gives `Cons`, constructor index `1`, and `[x, l]`.
-/
def datatypeGetConstr {T: LExprParams} [BEq T.Identifier] (d: LDatatype T.IDMeta) (x: LExpr T.mono) : Option (LConstr T.IDMeta × Nat × List (LExpr T.mono)) :=
  List.foldr (fun (c, i) acc =>
    match x.matchOp c.name with
    | .some args =>
      .some (c, i, args)
    | .none => acc) .none (List.zip d.constrs (List.range d.constrs.length))


/--
Determine which datatype and constructor, if any, a datatype instance
belongs to and get the arguments. Also gives the index in the block and
constructor list as well as the recursive arguments

For example, expression `Cons x l` gives constructor `Cons`, datatype
index `0`, constructor index `1` (cons is the second constructor),
arguments `[x, l]`, and recursive argument `[(l, List α)]`
-/
def matchConstr {T: LExprParams} [BEq T.Identifier] (block : MutualDatatype T.IDMeta) (x : LExpr T.mono)
    : Option (Nat × Nat × LConstr T.IDMeta × List (LExpr T.mono) × List (LExpr T.mono × LMonoTy)) :=
  List.zip block (List.range block.length) |>.findSome? fun (d, dtIdx) =>
    (datatypeGetConstr d x).map fun (c, constrIdx, args) =>
      let recs := (List.zip args (c.args.map Prod.snd)).filter (
        fun (_, ty) => isRecTy block ty)
      (dtIdx, constrIdx, c, args, recs)

def elimFuncName (d: LDatatype IDMeta) : Identifier IDMeta :=
  d.name ++ "$Elim"

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
def elimRecCall {T: LExprParams} [Inhabited T.IDMeta] (block : MutualDatatype T.IDMeta) (recArg : LExpr T.mono)
    (recTy : LMonoTy) (elimArgs : List (LExpr T.mono)) (m : T.Metadata) :
    Option (LExpr T.mono) :=
    (findRecTy block recTy).map fun d =>
      let elimName := elimFuncName d
      match recTyStructure d recTy with
      | .inl _ => -- Generate eliminator call directly
        (LExpr.op m elimName .none).mkApp m (recArg :: elimArgs)
      | .inr funArgs =>
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
3. For `RoseTree = R (Forest) with Forest = FNil | FCons RoseTree Forest`,
the generated functions are:
`RoseTree$Elim (R x) r1 f1 f2 = r1 x (Forest$Elim x r1 f1 f2)`
`Forest$Elim FNil r1 f1 f2 = f1`
`Forest$Elim (Fcons r f) r1 f1 f2 = f2 r f (Rose$Elim r r1 f1 f2) (Forest$Elim f r1 f1 f2)`
-/
def elimConcreteEval {T: LExprParams} [BEq T.Identifier] [Inhabited T.IDMeta] (block : MutualDatatype T.IDMeta)
    (m : T.Metadata) : T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono) :=
  fun _ args =>
    match args with
    | x :: xs =>
      match matchConstr block x with
      | some (dtIdx, constrIdx, _, a, recs) =>
        let gIdx := blockConstrIdx block dtIdx constrIdx
        xs[gIdx]?.bind fun f =>
          some (f.mkApp m (a ++ recs.filterMap (fun (r, rty) => elimRecCall block r rty xs m)))
      | none => none
    | _ => none

/--
Generate eliminators for all datatypes in a mutual block.
Each datatype gets its own eliminator, but they share case function arguments
for all constructors across the block.
For example,
`RoseTree$Elim : RoseTree → (Forest → β → α) → β → (RoseTree → Forest → α → β → β) → α`
`Forest$Elim : Forest → (Forest → β → α) → β → (RoseTree → Forest → α → β → β) → β`
-/
def elimFuncs [Inhabited T.IDMeta] [BEq T.Identifier] (block : MutualDatatype T.IDMeta) (m : T.Metadata)
    : List (LFunc T) :=
  if h:  block.isEmpty then [] else
  have hlen : 0 < List.length block := by
    have := @List.isEmpty_iff_length_eq_zero _ block; grind
  let typeArgs := block[0].typeArgs -- OK because all must have same typevars
  let retTyVars := freshTypeArgs block.length typeArgs
  let allConstrs :=
    block.mapIdx (fun dtIdx d => d.constrs.map (dtIdx, ·)) |>.flatten
  let caseTypes := allConstrs.map fun (dtIdx, c) => elimTy block retTyVars dtIdx c
  (block.zip retTyVars).map fun (d, outputTyVar) =>
    { name := elimFuncName d
      typeArgs := retTyVars ++ d.typeArgs
      inputs := List.zip (genArgNames (allConstrs.length + 1)) (dataDefault d :: caseTypes)
      output := .ftvar outputTyVar
      concreteEval := elimConcreteEval block m
      attr := #[eval_if_constr_attr] }

---------------------------------------------------------------------

-- Generating testers and destructors

/--
Generate tester body for mutual blocks. For mutual eliminators, we need case functions
for ALL constructors across the block, not just the constructors of one datatype.
-/
def testerFuncBody {T : LExprParams} [Inhabited T.IDMeta] (block: MutualDatatype T.IDMeta)
    (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) (input: LExpr T.mono) (m: T.Metadata) : LExpr T.mono :=
  -- Number of arguments for a constructor in a mutual block
  let numargs (c: LConstr T.IDMeta) := c.args.length + ((c.args.map Prod.snd).filter (isRecTy block)).length
  let args := block.flatMap (fun d' => d'.constrs.map (fun c1 =>
    LExpr.absMultiInfer m (numargs c1) (.boolConst m (c.name.name == c1.name.name))))
  .mkApp m (.op m (elimFuncName d) .none) (input :: args)

/--
Generate tester function for a constructor in a mutual block.
-/
def testerFunc {T} [Inhabited T.IDMeta] (block: MutualDatatype T.IDMeta)
    (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) (m: T.Metadata) : LFunc T :=
  let arg := genArgName
  {name := c.testerName,
   typeArgs := d.typeArgs,
   inputs := [(arg, dataDefault d)],
   output := .bool,
   body := testerFuncBody block d c (.fvar m arg .none) m,
   attr := #[inline_if_constr_attr]
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
      (datatypeGetConstr d x).bind (fun (c1, _, a) =>
        if c1.name.name == c.name.name
        then a[idx]? else none)
    | _ => none

def destructorFuncName {IDMeta} (d: LDatatype IDMeta) (name: Identifier IDMeta) := d.name ++ ".." ++ name.name

/--
Generate destructor functions for a constructor, which extract the
constructor components, e.g.
`List..head (Cons h t) = h`
`List..tail (Cons h t) = t`
These functions are partial, `List..head Nil` is undefined.
-/
def destructorFuncs {T} [BEq T.Identifier] [Inhabited T.IDMeta]  (d: LDatatype T.IDMeta) (c: LConstr T.IDMeta) : List (LFunc T) :=
  c.args.mapIdx (fun i (name, ty) =>
    let arg := genArgName
    {
      name := destructorFuncName d name,
      typeArgs := d.typeArgs,
      inputs := [(arg, dataDefault d)],
      output := ty,
      concreteEval := some (fun _ => destructorConcreteEval d c i)})


---------------------------------------------------------------------

-- Type Factories

/-- A TypeFactory stores datatypes grouped by mutual recursion. -/
def TypeFactory := Array (MutualDatatype IDMeta)

instance: ToFormat (@TypeFactory IDMeta) where
  format f :=
    let formatBlock (block : MutualDatatype IDMeta) : Format :=
      match block with
      | [d] => format d
      | ds => f!"mutual {Std.Format.joinSep (ds.map format) Format.line} end"
    Std.Format.joinSep (f.toList.map formatBlock) f!"{Format.line}"

instance [Repr IDMeta] : Repr (@TypeFactory IDMeta) where
  reprPrec f n := reprPrec f.toList n

instance : Inhabited (@TypeFactory IDMeta) where
  default := #[]

def TypeFactory.default : @TypeFactory IDMeta := #[]

/-- Get all datatypes in the TypeFactory as a flat list. -/
def TypeFactory.allDatatypes (t : @TypeFactory IDMeta) : List (LDatatype IDMeta) :=
  t.toList.flatten

/-- Find a datatype by name in the TypeFactory. -/
def TypeFactory.getType (F : @TypeFactory IDMeta) (name : String) : Option (LDatatype IDMeta) :=
  F.allDatatypes.find? (fun d => d.name == name)

/-- Get all datatype names in the TypeFactory. -/
def TypeFactory.allTypeNames (t : @TypeFactory IDMeta) : List String :=
  t.allDatatypes.map (·.name)

/--
Get all type constructor names referenced in a type.
-/
def getTypeRefs (ty: LMonoTy) : List String :=
  match ty with
  | .tcons n args => n :: args.flatMap getTypeRefs
  | _ => []

/--
Ensures all type occuring a constructor are only primitive types,
types defined previously, or types in the same mutual block.
-/
def TypeFactory.validateTypeReferences (t : @TypeFactory IDMeta) (block : MutualDatatype IDMeta) (knownTypes : List String) : Except DiagnosticModel Unit := do
  let validNames : Std.HashSet String :=
    Std.HashSet.ofList (knownTypes ++ t.allTypeNames ++ block.map (·.name))
  for d in block do
    for c in d.constrs do
      for (_, ty) in c.args do
        for ref in getTypeRefs ty do
          if !validNames.contains ref then
            throw <| DiagnosticModel.fromFormat f!"Error in datatype {d.name}, constructor {c.name.name}: Undefined type '{ref}'"

/-- Add a mutual block to the TypeFactory, checking for duplicates,
  inconsistent types, and positivity. -/
def TypeFactory.addMutualBlock (t : @TypeFactory IDMeta) (block : MutualDatatype IDMeta) (knownTypes : List String := []) : Except DiagnosticModel (@TypeFactory IDMeta) := do
  -- Check for name clashes within block
  validateMutualBlock block
  -- Check for positivity and uniformity
  checkStrictPosUnif block
  -- Check for duplicate names with existing types
  for d in block do
    match t.getType d.name with
    | some d' => throw <| DiagnosticModel.fromFormat f!"A datatype of name {d.name} already exists! \
                Redefinitions are not allowed.\n\
                Existing Type: {d'}\n\
                New Type:{d}"
    | none => pure ()
  -- Check for consistent type dependencies
  t.validateTypeReferences block knownTypes
  .ok (t.push block)

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
Generates the Factory (containing eliminators, constructors, testers, and destructors)
for a mutual block of datatypes.
-/
def genBlockFactory {T: LExprParams} [inst: Inhabited T.Metadata] [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) : Except DiagnosticModel (@Lambda.Factory T) := do
  if block.isEmpty then return Factory.default
  let elims := elimFuncs block inst.default
  let constrs := block.flatMap (fun d => d.constrs.map (fun c => constrFunc c d))
  let testers := block.flatMap (fun d => d.constrs.map (fun c => testerFunc block d c inst.default))
  let destrs := block.flatMap (fun d => d.constrs.flatMap (fun c => destructorFuncs d c))
  Factory.default.addFactory (elims ++ constrs ++ testers ++ destrs).toArray

/--
Generates the Factory (containing all constructor and eliminator functions) for the given `TypeFactory`.
-/
def TypeFactory.genFactory {T: LExprParams} [inst: Inhabited T.Metadata] [Inhabited T.IDMeta] [ToFormat T.IDMeta] [BEq T.Identifier] (t: @TypeFactory T.IDMeta) : Except DiagnosticModel (@Lambda.Factory T) :=
  t.foldlM (fun f block => do
    let f' ← genBlockFactory block
    f.addFactory f'
  ) Factory.default

---------------------------------------------------------------------

-- Inhabited types

/-
Because we generate destructors, it is vital to ensure that every datatype
is inhabited. Otherwise, we can have the following:
```
type Empty :=.
type List := Nil | Cons (hd: Empty) (tl: List)
```
The only element of `List` is `Nil`, but we also create the destructor
`hd : List → Empty`, which means `hd Nil` has type `Empty`, contradicting the
fact that `Empty` is uninhabited.

However, checking type inhabitation is complicated for several reasons:
1. Datatypes can refer to other datatypes. E.g. `type Bad = B(x: Empty)` is
uninhabited
2. These dependencies need not be linear. For example,
the following datatypes are uninhabited:
```
type Bad1 := B1(x: Bad2)
type Bad2 := B2(x: Bad1)
```
3. Instantiated type parameters matter: `List Empty` is
inhabited, but `Either Empty Empty` is not. Our check is conservative and will
not allow either of these types.

We determine if all types in a TypeFactory are inhabited simulataneously,
memoizing the results.
-/

/-- Stores whether a type is known to be inhabited -/
abbrev inhabMap : Type := Map String Bool

/-
The termination argument follows from the fact that each time a type symbol
is evaluated, it is added to the `seen` set, which by assumption is a subset
of `adts` (which has no duplicates). Therefore, `adts.size - seen.length`
decreases. `ty_inhab` does not change this value but is
structurally recursive over the type arguments. Thus, we use the lexicographic
measure `(adts.size - seen.length, t.size)`.
-/

mutual

/--
Prove that type symbol `ts` is inhabited, assuming
that types `seen` are unknown. All other types are assumed inhabited.
The `List.Nodup` and `⊆` hypotheses are only used to prove termination.
-/
def typesym_inhab (adts: @TypeFactory IDMeta) (seen: List String)
  (hnodup: List.Nodup seen)
  (hsub: seen ⊆ (List.map (fun x => x.name) adts.allDatatypes))
  (ts: String) : StateM inhabMap Bool := do
  -- Check if type is already known to be inhabited
  let m ← get
  match m.find? ts with
  | some b => pure b
  | none =>
    -- If type in `seen`, it is unknown, so we return false
    if hin: List.elem ts seen then pure false
    else
      match ha: adts.getType ts with
      | none => pure true -- Assume all non-datatypes are inhabited
      | some l =>
        -- A datatype is inhabited if it has an inhabited constructor
        let res ← (l.constrs.foldlM (fun accC c => do
          -- A constructor is inhabited if all of its arguments are inhabited
          let constrInhab ← (c.args.foldlM
            (fun accA ty1 =>
                do
                  have hn: List.Nodup (l.name :: seen) := by
                    rw[List.nodup_cons]; constructor
                    . have := List.find?_some ha; grind
                    . assumption
                  have hsub' : (l.name :: seen) ⊆ (List.map (fun x => x.name) adts.allDatatypes) := by
                    apply List.cons_subset.mpr
                    constructor <;> try assumption
                    rw[List.mem_map]; exists l; constructor <;> try grind
                    have := List.mem_of_find?_eq_some ha; grind
                  let b1 ← ty_inhab adts (l.name :: seen) hn hsub' ty1.2
                  pure (accA && b1)
              ) true)
          pure (accC || constrInhab)
          ) false)
        /-
        Type is known: we can add to map
        Only add false if not in a cycle, it may resolve later
        E.g. when checking the `cons` case for `List`, `List` itself is in
        the `seen` set and so will be temporarily marked as uninhabited.
        This should not be memoized.
        -/
        if res || seen.isEmpty then
          let m ← get
          set (m.insert ts res)
        pure res
  termination_by (adts.allDatatypes.length - seen.length, 0)
  decreasing_by
    apply Prod.Lex.left; simp only[List.length]
    apply Nat.sub_succ_lt_self
    have hlen := List.subset_nodup_length hn hsub'; simp_all; omega

def ty_inhab (adts: @TypeFactory IDMeta) (seen: List String)
  (hnodup: List.Nodup seen) (hsub: seen ⊆  (List.map (fun x => x.name) adts.allDatatypes))
  (t: LMonoTy) : StateM inhabMap Bool :=
  match t with
  | .tcons name args => do
      -- name(args) is inhabited if name is inhabited as a typesym
      -- and all args are inhabited as types (note this is conservative)
      let checkTy ← typesym_inhab adts seen hnodup hsub name
      if checkTy then
        args.foldrM (fun ty acc => do
          let x ← ty_inhab adts seen hnodup hsub ty
          pure (x && acc)
        ) true
      else pure false
  | _ => pure true -- Type variables and bitvectors are inhabited
termination_by (adts.allDatatypes.length - seen.length, t.size)
decreasing_by
  . apply Prod.Lex.right; simp only[LMonoTy.size]; omega
  . rename_i h; have := LMonoTy.size_lt_of_mem h;
    apply Prod.Lex.right; simp only[LMonoTy.size]; omega
end

/--
Prove that ADT with name `a` is inhabited. All other types are assumed inhabited.
-/
def adt_inhab  (adts: @TypeFactory IDMeta) (a: String) : StateM inhabMap Bool
  := typesym_inhab adts [] (by grind) (by grind) a

/--
Check that all ADTs in TypeFactory `adts` are inhabited. This uses memoization
to avoid computing the intermediate results more than once. Returns `none` if
all datatypes are inhabited, `some a` for some uninhabited type `a`
-/
def TypeFactory.all_inhab (adts: @TypeFactory IDMeta) : Option String :=
  let x := (List.foldlM (fun (x: Option String) (l: LDatatype IDMeta) =>
    do
      match x with
      | some a => pure (some a)
      | none =>
        let b ← adt_inhab adts l.name
        pure (if b then none else some l.name)
    ) none adts.allDatatypes)
  (StateT.run x []).1

/--
Check that all ADTs in TypeFactory `adts` are inhabited.
-/
def TypeFactory.checkInhab (adts: @TypeFactory IDMeta) : Except DiagnosticModel Unit :=
  match adts.all_inhab with
  | none => .ok ()
  | some a => .error <| DiagnosticModel.fromFormat f!"Error: datatype {a} not inhabited"

---------------------------------------------------------------------

end Lambda

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.Factory
import Strata.DL.Util.Maps

/-! ## Type Environment

Data structures and utilities for type inference/checking of Lambda expressions.
Also see `Strata.DL.Lambda.LExprT`.
-/

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)
open LExpr

---------------------------------------------------------------------

/--
A type alias is syntactic sugar for a type definition. E.g.,
`∀α. FooAlias α := Foo α` is represented in `TypeAlias` as follows; note that
`α` is common to both the alias and its definition.
```
{
  name := "FooAlias"
  typeArgs := ["α"]
  type := LMonoTy.tcons "Foo" [.ftvar "α"]
}
```

IMPORTANT: we expect the type definition to not be an alias itself, to avoid any
cycles. See function `TEnv.addTypeAlias` for a canonical way of adding
well-formed type aliases to the context.
-/
structure TypeAlias ExtraRestrict where
  name : String
  typeArgs : List TyIdentifier
  type : LMonoTy ExtraRestrict
  deriving DecidableEq, Repr, Inhabited

def TypeAlias.toAliasLTy (a : TypeAlias ExtraRestrict) : LTy ExtraRestrict :=
  .forAll a.typeArgs (.tcons a.name (a.typeArgs.map (fun i => .ftvar i)))

instance : ToFormat (TypeAlias ExtraRestrict) where
  format t := f!"{t.toAliasLTy} := {t.type}"

variable {Identifier : Type} [DecidableEq Identifier] [ToFormat Identifier] {ExtraRestrict : Type}

/--
A type context contains two maps: `types` and `aliases`.

The `types` field maps free variables in expressions (i.e., `LExpr.fvar`s) to
their type schemes. This is essentially a stack to account for variable scopes.

The `aliases` field maps type synonyms to their corresponding type definitions.
We expect these type definitions to not be aliases themselves, to avoid any
cycles in the map (see `TEnv.addTypeAlias`).

The `otherIDs` field represents other identifiers in use in the term to ensure any fresh names are unique w.r.t these identifiers as well. Currently used only for bounded int translation but can be used for function identifiers, type names, etc.
-/
structure TContext (Identifier : Type) (ExtraRestrict : Type) where
  types   :  Maps Identifier (LTy ExtraRestrict) := []
  aliases :  List (TypeAlias ExtraRestrict) := []
  otherIDs : List Identifier := [] -- should be set
  deriving DecidableEq, Repr, Inhabited

instance : ToFormat (TContext Identifier ExtraRestrict) where
  format ctx :=
    f!"types:   {ctx.types}\n\
       aliases: {ctx.aliases}\n\
       otherIDs: {ctx.otherIDs}"

/--
Get all the known variables (i.e., `LExpr.fvar`s) in the typing context.
-/
def TContext.knownVars (ctx : (TContext Identifier ExtraRestrict)) : List Identifier :=
  ctx.otherIDs ++ go ctx.types
  where go types :=
  match types with
  | [] => [] | m :: rest => m.keys ++ go rest

def TContext.types.knownTypeVars (types : Maps Identifier (LTy ExtraRestrict)) : List TyIdentifier :=
  match types with
  | [] => []
  | m :: rest => go m ++ knownTypeVars rest
  where go (m : Map Identifier (LTy ExtraRestrict)) :=
    match m with
    | [] => [] | (_, ty) :: rest => LTy.freeVars ty ++ go rest

/--
Get all the known type variables (i.e., free `LMonoTy.ftvar`s) in the typing
context.
-/
def TContext.knownTypeVars (ctx : (TContext Identifier ExtraRestrict)) : List TyIdentifier :=
  types.knownTypeVars ctx.types

/--
Is `x` is a fresh type variable w.r.t. the context?
-/
def TContext.isFresh (tx : TyIdentifier) (Γ : (TContext Identifier ExtraRestrict)) : Prop :=
  ∀ (x : Identifier) (ty : LTy ExtraRestrict),
    Γ.types.find? x = some ty → tx ∉ (LTy.freeVars ty)

/--
Are `xs` fresh type variables w.r.t. the context?
-/
def TContext.allFreshVars (xs : List TyIdentifier) (Γ : (TContext Identifier ExtraRestrict)) : Prop :=
  match xs with
  | [] => True
  | x :: rest => (TContext.isFresh x Γ) ∧ (TContext.allFreshVars rest Γ)

def TContext.types.subst (types : Maps Identifier (LTy ExtraRestrict)) (S : Subst ExtraRestrict) :
  Maps Identifier (LTy ExtraRestrict) :=
  match types with
  | [] => []
  | tmap :: trest =>
    go tmap :: types.subst trest S
  where go (tmap : Map Identifier (LTy ExtraRestrict)) :=
    match tmap with
    | [] => []
    | (x, ty) :: mrest =>
      (x, LTy.subst S ty) :: go mrest

/--
Apply a substitution `S` to the context.
-/
def TContext.subst (T : TContext Identifier ExtraRestrict) (S : Subst ExtraRestrict) : TContext Identifier ExtraRestrict :=
  { T with types := types.subst T.types S }

---------------------------------------------------------------------

structure TGenState where
  tyGen : Nat := 0
  tyPrefix : String := "$__ty"
  exprGen : Nat := 0
  exprPrefix : String := "$__var"
deriving Repr, Inhabited

/--
Typing state.

The typing state does bookkeeping to generate fresh expression and type
variables needed during type inference. It also has a global substitution map
`TState.subst`.

Also see functions `TEnv.genTyVar` and `TEnv.genExprVar`.
-/
structure TState ExtraRestrict where
  genState : TGenState
  substInfo : SubstInfo ExtraRestrict := SubstInfo.empty
  deriving Repr, Inhabited

def TGenState.init : TGenState := {}

def TState.init ExtraRestrict : TState ExtraRestrict := {genState := TGenState.init}

def TGenState.incTyGen (state : TGenState) : TGenState :=
  { state with tyGen := state.tyGen + 1 }

def TGenState.genTySym (state : TGenState) : TyIdentifier × TGenState :=
  let new_idx := state.tyGen
  let state := state.incTyGen
  let new_var := state.tyPrefix ++ toString new_idx
  (new_var, state)

def TGenState.incExprGen (state : TGenState) : TGenState :=
  { state with exprGen := state.exprGen + 1 }

def TGenState.genExprSym (state : TGenState) : String × TGenState :=
  let new_idx := state.exprGen
  let state := state.incExprGen
  let new_var := state.exprPrefix ++ toString new_idx
  (new_var, state)

instance : ToFormat (TState ExtraRestrict) where
  format ts :=
    f!"tyGen: {ts.genState.tyGen}{Format.line}\
       tyPrefix: {ts.genState.tyPrefix}{Format.line}\
       exprGen: {ts.genState.exprGen}{Format.line}\
       exprPrefix: {ts.genState.exprPrefix}{Format.line}\
       subst: {ts.substInfo.subst}"

---------------------------------------------------------------------

/-- Name and arity of a registered type. -/
structure KnownType where
  name : String
  arity : Nat := 0
  deriving Inhabited, Repr, DecidableEq

def KnownType.toLTy (k : KnownType) : LTy :=
  let bvars := (List.range k.arity).map (fun a => toString a)
  let args := bvars.map (fun b => .ftvar b)
  .forAll bvars (.tcons k.name args)

def LTy.toKnownType! [Repr ExtraRestrict] (lty : LTy ExtraRestrict) : KnownType :=
  match lty with
  | .forAll _ (.tcons name args) => { name, arity := args.length }
  | .forAll [] (.bitvec _) => { name := "bitvec", arity := 1 }
  | _ => panic! s!"Unsupported known type: {lty}"

instance  : ToFormat KnownType where
  format k := f!"{k.toLTy}"

/-- Registered types. -/
abbrev KnownTypes := List KnownType

def KnownTypes.keywords (ks : KnownTypes) : List String :=
  ks.map (fun k => k.name)

structure TGenEnv (Identifier : Type) (ExtraRestrict : Type := Empty) where
  context : TContext Identifier ExtraRestrict
  genState : TGenState
deriving Inhabited

/--
A type environment `TEnv` contains a stack of contexts `TContext` to track `LExpr`
variables and their types, a typing state `TState` to track the global
substitution and fresh variable generation, and a `KnownTypes` to track the
supported type constructors. It also has type information about a
factory of user-specified functions, which is used during type checking.
-/
structure TEnv (Identifier : Type) (ExtraRestrict : Type := Empty) where
  genEnv : TGenEnv Identifier ExtraRestrict
  stateSubstInfo: SubstInfo ExtraRestrict := SubstInfo.empty
  functions : @Factory Identifier ExtraRestrict
  knownTypes : KnownTypes
deriving Inhabited

def TEnv.updateContext {Identifier ExtraRestrict} (T: TEnv Identifier ExtraRestrict) (C: TContext Identifier ExtraRestrict) : TEnv Identifier ExtraRestrict :=
  let g := {T.genEnv with context := C}
  {T with genEnv := g}

def TEnv.state {Identifier : Type} {ExtraRestrict : Type} (T: TEnv Identifier ExtraRestrict) : TState ExtraRestrict :=
  let g := {tyGen := T.genEnv.genState.tyGen, tyPrefix := T.genEnv.genState.tyPrefix, exprGen := T.genEnv.genState.exprGen, exprPrefix := T.genEnv.genState.exprPrefix}
  { substInfo := T.stateSubstInfo, genState := g}

def KnownTypes.default : KnownTypes :=
  open LTy.Syntax in
  [t[∀a b. %a → %b],
   t[bool],
   t[int],
   t[string]].map (fun k => k.toKnownType!)

def TGenEnv.default : TGenEnv Identifier ExtraRestrict :=
  open LTy.Syntax in
  { context := {},
    genState := TGenState.init,
  }

def TEnv.default : TEnv Identifier ExtraRestrict :=
  let g := {context := {}, genState := TGenState.init}
  open LTy.Syntax in
  { genEnv := g,
    functions := #[],
    knownTypes := KnownTypes.default
  }

instance : ToFormat (TEnv Identifier ExtraRestrict) where
  format s := f!"context:{Format.line}{s.genEnv.context}\
                 {Format.line}\
                 state:{Format.line}{s.state}\
                 {Format.line}\
                 known types:{Format.line}{s.knownTypes}"

def TEnv.addKnownType (T : TEnv Identifier ExtraRestrict) (k : KnownType) : TEnv Identifier ExtraRestrict :=
  { T with knownTypes := k :: T.knownTypes }

def TEnv.addFactoryFunction (T : TEnv Identifier ExtraRestrict) (fn : LFunc Identifier ExtraRestrict) : TEnv Identifier ExtraRestrict :=
  { T with functions := T.functions.push fn }

def TEnv.addFactoryFunctions (T : TEnv Identifier ExtraRestrict) (fact : @Factory Identifier ExtraRestrict) : TEnv Identifier ExtraRestrict :=
  { T with functions := T.functions.append fact }

/--
Replace the global substitution in `T.state.subst` with `S`.
-/
def TEnv.updateSubst (T : (TEnv Identifier ExtraRestrict)) (S : SubstInfo ExtraRestrict) : (TEnv Identifier ExtraRestrict) :=
  { T with stateSubstInfo := S }

omit [DecidableEq Identifier] [ToFormat Identifier] in
theorem TEnv.SubstWF_of_pushemptySubstScope (T : TEnv Identifier ExtraRestrict) :
  SubstWF (Maps.push T.state.substInfo.subst []) := by
  have h_SubstWF : SubstWF T.state.substInfo.subst := by
    apply T.state.substInfo.isWF
  generalize T.state.substInfo.subst = S at *
  simp_all [SubstWF, Subst.freeVars]
  done

def TEnv.pushEmptySubstScope (T : (TEnv Identifier ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let new_subst := T.state.substInfo.subst.push []
  let newS := { subst := new_subst, isWF := (by rw [TEnv.SubstWF_of_pushemptySubstScope]) }
  { T with stateSubstInfo := newS }

omit [DecidableEq Identifier] [ToFormat Identifier] in
theorem TEnv.SubstWF_of_popSubstScope (T : TEnv Identifier ExtraRestrict) :
  SubstWF (Maps.pop T.state.substInfo.subst) := by
  have h_SubstWF : SubstWF T.state.substInfo.subst := by
    apply T.state.substInfo.isWF
  generalize T.state.substInfo.subst = S at *
  simp_all [Maps.pop]
  split <;> try simp_all
  rename_i ms m mrest
  simp [@SubstWF_of_cons _ m mrest (by assumption)]

def TEnv.popSubstScope (T : (TEnv Identifier ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let new_subst := T.state.substInfo.subst.pop
  let newS := { subst := new_subst, isWF := (by rw [TEnv.SubstWF_of_popSubstScope]) }
  { T with stateSubstInfo := newS }

def TEnv.pushEmptyContext (T : (TEnv Identifier ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let ctx := T.genEnv.context
  let ctx' := { ctx with types := ctx.types.push [] }
  T.updateContext ctx'

def TEnv.popContext (T : (TEnv Identifier ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let ctx := T.genEnv.context
  let ctx' := { ctx with types := ctx.types.pop }
  T.updateContext ctx'

/--
Insert `(x, ty)` in `T.context`.
-/
def TGenEnv.insertInContext (T : (TGenEnv Identifier ExtraRestrict)) (x : Identifier) (ty : LTy ExtraRestrict) : (TGenEnv Identifier ExtraRestrict) :=
  let ctx := T.context
  let ctx' := { ctx with types := ctx.types.insert x ty }
  { T with context := ctx' }

def TEnv.insertInContext (T : (TEnv Identifier ExtraRestrict)) (x : Identifier) (ty : LTy ExtraRestrict) : (TEnv Identifier ExtraRestrict) :=
  { T with genEnv := TGenEnv.insertInContext T.genEnv x ty}

/--
Insert non-type-variable identifier in `T.context`
-/
def TGenEnv.insertIDInContext (T : (TGenEnv Identifier ExtraRestrict)) (x : Identifier) : (TGenEnv Identifier ExtraRestrict) :=
  let ctx := T.context
  let ctx' := { ctx with otherIDs := x :: ctx.otherIDs }
  { T with context := ctx' }

def TEnv.insertIDInContext (T : (TEnv Identifier ExtraRestrict)) (x : Identifier) : (TEnv Identifier ExtraRestrict) :=
  { T with genEnv := TGenEnv.insertIDInContext T.genEnv x}

/--
Insert each element in `map` in `T.context`.
-/
def TEnv.addToContext (T : (TEnv Identifier ExtraRestrict)) (map : Map Identifier (LTy ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let ctx := T.genEnv.context
  let types := List.foldl (fun m (x, v) => m.insert x v) ctx.types map
  let ctx' := { ctx with types := types }
  T.updateContext ctx'

/--
Erase entry for `x` from `T.context`.
-/
def TEnv.eraseFromContext (T : (TEnv Identifier ExtraRestrict)) (x : Identifier) : (TEnv Identifier ExtraRestrict) :=
  let ctx := T.genEnv.context
  let ctx' := { ctx with types := ctx.types.erase x }
  T.updateContext ctx'

def TEnv.freeVarCheck (T : (TEnv Identifier ExtraRestrict)) (e : LExpr (LMonoTy ExtraRestrict) Identifier) (msg : Format) :
  Except Format Unit :=
  let efv := e.freeVars.map (fun (x, _) => x)
  let knownVars := T.genEnv.context.knownVars
  let freeVars := List.filter (fun v => v ∉ knownVars) efv
  match freeVars with
  | [] => .ok ()
  | _ =>
    .error f!"{msg} No free variables are allowed here!\
              {Format.line}\
              Free Variables: {freeVars}"

def TEnv.freeVarChecks (T : (TEnv Identifier ExtraRestrict)) (es : List (LExpr (LMonoTy ExtraRestrict) Identifier)) : Except Format Unit :=
  match es with
  | [] => .ok ()
  | e :: erest => do
    let _ ← freeVarCheck T e f!"[{e}]"
    freeVarChecks T erest

instance : Inhabited (TyIdentifier × TEnv Identifier ExtraRestrict) where
  default := ("$__ty0", TEnv.default)

/-- Variable Generator -/
class HasGen (Identifier : Type) where
  genVar : ∀ {ExtraRestrict}, TGenEnv Identifier ExtraRestrict → Identifier × TGenEnv Identifier ExtraRestrict

/--
Generate a fresh variable (`LExpr.fvar`). This is needed to open the body of an
`LExpr.abs` expression -- i.e., turn the bound variable into a fresh free
variable using `LExpr.varOpen` -- during type inference.

This function is the canonical way of obtaining fresh variables during type
checking. Also, we rely on the parser disallowing Lambda variables to begin with
`$__`, which is reserved for internal use; this is why `TState.exprPrefix` ==
`$__var`.

Together, these restrictions ensure that variables created using
`TEnv.genExprVar` are fresh w.r.t. the Lambda expression.
-/
def TEnv.genExprVar {ExtraRestrict} (T: TGenEnv String ExtraRestrict) : (String × TGenEnv String ExtraRestrict) :=
  let (new_var, state) := T.genState.genExprSym
  let T :={ T with genState := state }
  let known_vars := TContext.knownVars T.context
  if new_var ∈ known_vars then
    panic s!"[TEnv.genExprVar] Generated variable {new_var} is not fresh!\n\
              Context: {format T.context}"
  else
    (new_var, T)

instance : HasGen String where
  genVar := TEnv.genExprVar

/--
Generate a fresh type variable (`ftvar`).

This function is the canonical way of obtaining fresh type variables. This --
along with the restriction that all `ftvar`s in an annotation are implicitly
universally quantified -- ensures that we always get a fresh type variable when
we use `TEnv.genTyVar`.
-/
def TEnv.genTyVar (T : TEnv Identifier ExtraRestrict) : TyIdentifier × (TEnv Identifier ExtraRestrict) :=
  let (new_var, state) := T.genEnv.genState.genTySym
  let g := {T.genEnv with genState := state}
  let T := { T with genEnv := g }
  if new_var ∈ T.genEnv.context.knownTypeVars then
    panic s!"[TEnv.genTyVar] Generated type variable {new_var} is not fresh!\n\
              Context: {format T.genEnv.context}"
  else
    (new_var, T)

/--
Generate `n` fresh type variables (`ftvar`s).
-/
def TEnv.genTyVars (n : Nat) (T : (TEnv Identifier ExtraRestrict)) : List TyIdentifier × (TEnv Identifier ExtraRestrict) :=
  match n with
  | 0 => ([], T)
  | n' + 1 =>
    let (ty, T) := TEnv.genTyVar T
    let (rest_ty, T) := TEnv.genTyVars n' T
    (ty :: rest_ty, T)

/--
Consistently instantiate type variables `ids` in `mtys`.
-/
def LMonoTys.instantiate (ids : List TyIdentifier) (mtys : LMonoTys ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) :
  LMonoTys ExtraRestrict × (TEnv Identifier ExtraRestrict) :=
  let (freshtvs, T) := TEnv.genTyVars ids.length T
  let S := List.zip ids (List.map (fun tv => (LMonoTy.ftvar tv)) freshtvs)
  (LMonoTys.subst [S] mtys, T)

omit [DecidableEq Identifier] in
theorem LMonoTys.instantiate_length :
  (LMonoTys.instantiate (Identifier:=Identifier) ids mty T).fst.length == mty.length := by
  simp [instantiate, LMonoTys.subst_eq_substLogic]
  induction mty <;> simp_all [substLogic]
  rename_i head tail ih
  split <;> simp_all

/--
Instantiate the scheme `ty` by filling in fresh type variables for all
the variables bound by the universal quantifier.

Note: we do not check whether `ty` is a type alias here. See
`LTy.instantiateWithCheck`, which incorporates this check (using
`LTy.resolveAliases`) as well as verifies whether the type is a previously registered
one.
-/
def LTy.instantiate (ty : LTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) : LMonoTy ExtraRestrict × (TEnv Identifier ExtraRestrict) :=
  match ty with
  | .forAll [] mty' => (mty', T)
  | .forAll xs lty' =>
    let (freshtvs, T) := TEnv.genTyVars xs.length T
    let S := List.zip xs (List.map (fun tv => (.ftvar tv)) freshtvs)
    (LMonoTy.subst [S] lty', T)

instance : Inhabited (Option LMonoTy × TEnv Identifier ExtraRestrict) where
  default := (none, TEnv.default)

/--
Return the instantiated definition of `mty` -- which is expected to be
`.tcons name args` --  if it is a type alias registered in the typing
environment `T`.

This function does not descend into the subtrees of `mty`, nor does it check
whether the de-aliased types are registered/known.
-/
def LMonoTy.aliasDef? [DecidableEq ExtraRestrict] (mty : LMonoTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) : (Option (LMonoTy ExtraRestrict) × TEnv Identifier ExtraRestrict) :=
  match mty with
  | .ftvar _ =>
    -- We can't have a free variable be the LHS of an alias definition because
    -- then it will unify with every type.
    (none, T)
  | .bitvec _ =>
    -- A bitvector cannot be a type alias.
    (none, T)
  | .tcons name args r =>
    match T.genEnv.context.aliases.find? (fun a => a.name == name && a.typeArgs.length == args.length) with
    | none => (none, T)
    | some alias =>
      let (lst, T) := LMonoTys.instantiate alias.typeArgs [(.tcons name (alias.typeArgs.map (fun a => .ftvar a))), alias.type] T
      -- (FIXME): Use `LMonoTys.instantiate_length` to remove the `!` below.
      let alias_inst := lst[0]!
      let alias_def := lst[1]!
      match Constraints.unify [(mty, alias_inst)] T.stateSubstInfo with
      | .error e =>
        panic! s!"[LMonoTy.aliasDef?] {e}"
      | .ok S =>
        (alias_def.subst S.subst, T.updateSubst S)

-- Only `FooAlias` is dealiased, not `BarAlias`. Note that the type variables
-- are instantiated appropriately and the global substitution is updated.
-- See `resolveAliases` for a version that also de-aliases `BarAlias`.
/--
info: Ans: some (Foo $__ty0 (BarAlias $__ty0 $__ty0))
Subst:
[(p, $__ty0) ($__ty1, (BarAlias $__ty0 $__ty0))]
-/
#guard_msgs in
open LTy.Syntax in
#eval let (ans, T) := LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %p %p)]
        ( (@TEnv.default String Empty).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]})
      format f!"Ans: {ans}\n\
                Subst:\n{T.state.substInfo.subst}"

/-- info: some (Foo $__ty0 (BarAlias q $__ty0)) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %q %p)]
        ( (@TEnv.default String Empty).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]} )
      |>.fst |> format

/-- info: some int -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myInt]
      ( (@TEnv.default String Empty).updateContext
                  { aliases := [{ typeArgs := [],
                                  name := "myInt",
                                  type := mty[int]}]} )
      |>.fst |> format

/-- info: some bool -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[BadBoolAlias %p %q]
        ( (@TEnv.default String Empty).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "BadBoolAlias",
                                     type := mty[bool]}]} )
      |>.fst |> format

/-- info: none -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myInt]
                    ( (@TEnv.default String Empty).updateContext
                      { aliases := [{
                         typeArgs := ["a"],
                         name := "myInt",
                         type := mty[int]}] })
      |>.fst |> format

/-- info: some (myDef int) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myAlias int bool]
                    ( (@TEnv.default String Empty).updateContext
                      { aliases := [{
                        typeArgs := ["a", "b"],
                        name := "myAlias",
                        type := mty[myDef %a]}] })
      |>.fst |> format

mutual
/--
De-alias `mty`, including at the subtrees.
-/
partial def LMonoTy.resolveAliases [DecidableEq ExtraRestrict] (mty : LMonoTy ExtraRestrict) (T : TEnv Identifier ExtraRestrict) : (Option (LMonoTy ExtraRestrict) × TEnv Identifier ExtraRestrict) :=
  let (maybe_mty, T) := LMonoTy.aliasDef? mty T
  match maybe_mty with
  | some (.tcons name args) =>
    let (args', T) := LMonoTys.resolveAliases args T.genEnv.context.aliases T
    match args' with
    | none => (some (.tcons name args), T)
    | some args' => (some (.tcons name args'), T)
  | some mty' => (some mty', T)
  | none =>
    match mty with
    | .ftvar _ => (some mty, T)
    | .bitvec _ => (some mty, T)
    | .tcons name mtys r =>
      let (maybe_mtys, T) := LMonoTys.resolveAliases mtys T.genEnv.context.aliases T
      match maybe_mtys with
      | none => (none, T)
      | some mtys' => (some (.tcons name mtys' r), T)

/--
De-alias `mtys`, including at the subtrees.
-/
partial def LMonoTys.resolveAliases [DecidableEq ExtraRestrict] (mtys : LMonoTys ExtraRestrict) (aliases : List (TypeAlias ExtraRestrict)) (T : (TEnv Identifier ExtraRestrict)) :
    (Option (LMonoTys ExtraRestrict) × (TEnv Identifier ExtraRestrict)) :=
    match mtys with
    | [] => (some [], T)
    | mty :: mrest =>
      let (mty', T) := LMonoTy.resolveAliases mty T
      let (mrest', T) := LMonoTys.resolveAliases mrest aliases T
      if h : mty'.isSome && mrest'.isSome then
        ((mty'.get (by simp_all) :: mrest'.get (by simp_all)), T)
      else
        (none, T)
end

/--
info: De-aliased type: some (Foo $__ty0 (Bar $__ty3 $__ty3))
Subst:
[(p, $__ty3) ($__ty1, (BarAlias $__ty3 $__ty3)) ($__ty0, $__ty3) ($__ty2, $__ty3)]
-/
#guard_msgs in
open LTy.Syntax in
#eval let (ty, T) := LMonoTy.resolveAliases
        mty[FooAlias %p (BarAlias %p %p)]
        ((@TEnv.default String Empty).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]})
      format f!"De-aliased type: {ty}\n\
                Subst:\n{T.state.substInfo.subst}"

/--
Instantiate and de-alias `ty`, including at the subtrees.
-/
def LTy.resolveAliases [DecidableEq ExtraRestrict] (ty : LTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) : (Option (LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict)) :=
  let (mty, T) := ty.instantiate T
  LMonoTy.resolveAliases mty T

/-- info: some (arrow bool $__ty0) -/
#guard_msgs in
open LTy.Syntax in
#eval LTy.resolveAliases
        t[∀x. (FooAlias %x %x) → %x]
        ((@TEnv.default String Empty).updateContext { aliases := [{
                                        typeArgs := ["x", "y"],
                                        name := "FooAlias",
                                        type := mty[bool]}]} )
      |>.fst |>.format

mutual
/--
Is `ty` an instance of a known type in `ks`? We expect `ty` to be
de-aliased.
-/
def LMonoTy.knownInstance (ty : LMonoTy ExtraRestrict) (ks : KnownTypes) : Bool :=
  match ty with
  | .ftvar _ | .bitvec _ => true
  | .tcons name args _ =>
    (ks.contains { name := name, arity := args.length }) &&
    LMonoTys.knownInstances args ks

/--
Are `tys` instances of some known type in `ks`? We expect all types in
`tys` to be de-aliased.
-/
def LMonoTys.knownInstances (tys : LMonoTys ExtraRestrict) (ks : KnownTypes) : Bool :=
  match tys with
  | [] => true
  | ty :: trest =>
    if LMonoTy.knownInstance ty ks then LMonoTys.knownInstances trest ks else false
end

def isInstanceOfKnownType (ty : LMonoTy ExtraRestrict) (T : TEnv Identifier ExtraRestrict) : Bool :=
  LMonoTy.knownInstance ty T.knownTypes

/--
Instantiate `mty` by replacing all free type variables with fresh ones, and then
perform resolution of type aliases and subsequent checks for registered types.
-/
def LMonoTy.instantiateWithCheck [DecidableEq ExtraRestrict] (mty : LMonoTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) :
    Except Format (LMonoTy ExtraRestrict × (TEnv Identifier ExtraRestrict)) := do
  let ftvs := mty.freeVars
  let (mtys, T) := LMonoTys.instantiate ftvs [mty] T
  let mtyi := mtys[0]!
  let (mtyi, T) := match mtyi.resolveAliases T with
                  | (some ty', T) => (ty', T)
                  | (none, T) => (mtyi, T)
  if isInstanceOfKnownType mtyi T
  then return (mtyi, T)
  else .error f!"Type {mty} is not an instance of a previously registered type!\n\
                 Known Types: {T.knownTypes}"

/--
Instantiate `ty`, with resolution of type aliases to type definitions and checks
for registered types.
-/
def LTy.instantiateWithCheck [DecidableEq ExtraRestrict] (ty : LTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) : Except Format (LMonoTy ExtraRestrict × (TEnv Identifier ExtraRestrict)) := do
  let (mty, T) := match ty.resolveAliases T with
                  | (some ty', T) => (ty', T)
                  | (none, T) => ty.instantiate T
  if isInstanceOfKnownType mty T
  then return (mty, T)
  else .error f!"Type {ty} is not an instance of a previously registered type!\n\
                 Known Types: {T.knownTypes}"

section

open LTy.Syntax

/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[myTy (myTy)]
                            { @TEnv.default String Empty with
                                knownTypes := [LTy.toKnownType! t[∀a. myTy %a],
                                               LTy.toKnownType! t[int]] }

/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[Foo] (@TEnv.default TyIdentifier Empty)

/--
info: error: Type (arrow int Foo) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← t[int → Foo].instantiateWithCheck (@TEnv.default TyIdentifier Empty)
         return format ans

/-- info: ok: (arrow int bool) -/
#guard_msgs in
#eval do let ans ← t[int → bool].instantiateWithCheck (@TEnv.default TyIdentifier Empty)
         return format ans.fst
end

/--
Instantiate the scheme `ty` and apply the global substitution `T.state.subst` to
it.
-/
def LTy.instantiateAndSubst [DecidableEq ExtraRestrict] (ty : LTy ExtraRestrict) (T : (TEnv Identifier ExtraRestrict)) : Except Format ((LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict)) := do
  let (mty, T) ← LTy.instantiateWithCheck ty T
  let mty := LMonoTy.subst T.state.substInfo.subst mty
  return (mty, T)

def LTy.instantiateAndSubsts [DecidableEq ExtraRestrict] (tys : List (LTy ExtraRestrict)) (T : (TEnv Identifier ExtraRestrict)) :
  Except Format (List (LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict)) := do
  match tys with
  | [] => return ([], T)
  | ty :: tyrest =>
    let (mty, T) ← LTy.instantiateAndSubst ty T
    let (mtyrest, T) ← LTy.instantiateAndSubsts tyrest T
    return ((mty :: mtyrest), T)

/--
Get the monotype of variable corresponding to identifier `x` by instantiating
the type and then applying the global substitution.
-/
def Identifier.instantiateAndSubst [DecidableEq ExtraRestrict] (x : Identifier) (T : (TEnv Identifier ExtraRestrict)) :
  Except Format (Option ((LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict))) := do
  match T.genEnv.context.types.find? x with
  | some ty => LTy.instantiateAndSubst ty T
  | none => return none

def Identifier.instantiateAndSubsts [DecidableEq ExtraRestrict] (xs : List Identifier) (T : (TEnv Identifier ExtraRestrict)) :
  Except Format (Option (List (LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict))) := do
  match xs with
  | [] => return some ([], T)
  | x :: xrest =>
    let ans ← instantiateAndSubst x T
    match ans with
    | none => return none
    | some (xty, T) =>
      let ans ← Identifier.instantiateAndSubsts xrest T
      match ans with
      | none => return none
      | some (xtys, T) => return ((xty :: xtys), T)

/-- info: (arrow $__ty0 b) -/
#guard_msgs in
open LTy.Syntax in
#eval format $ (LTy.instantiate t[∀a. %a → %b] (@TEnv.default String Empty)).fst

/--
Instantiate the scheme `∀tyArgs. s` by _consistently_ filling in fresh type
variables for all the variables bound by the universal quantifier.

E.g., the instantiation of `∀a. (x : a) (y : int) (z : a)` must be something
like `(x : _ty0) (y : int) (z : _ty0)`, and not `(x : _ty0) (y : int) (z : _ty1)`.
-/
def LMonoTySignature.instantiate [DecidableEq ExtraRestrict] (T : (TEnv Identifier ExtraRestrict)) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature Identifier ExtraRestrict) :
  Except Format ((@LMonoTySignature Identifier ExtraRestrict) × (TEnv Identifier ExtraRestrict)) := do
  let (mtys, T) := LMonoTys.instantiate tyArgs sig.values T
  let tys := mtys.map (fun mty => (LTy.forAll [] mty))
  let (newtys, T) ← go T tys
  .ok ((sig.keys.zip newtys), T)
  where go (T : (TEnv Identifier ExtraRestrict)) (tys : LTys ExtraRestrict) : Except Format ((LMonoTys ExtraRestrict) × (TEnv Identifier ExtraRestrict)) :=
    match tys with
    | [] => .ok ([], T)
    | t :: trest => do
      let (mt, T) ← LTy.instantiateWithCheck t T
      let (mtrest, T) ← go T trest
      .ok (mt :: mtrest, T)

/--
info: ok: (x : $__ty0) (y : int) (z : $__ty0)
-/
#guard_msgs in
open LTy.Syntax in
#eval do let ans ← (LMonoTySignature.instantiate
                    ((@TEnv.default TyIdentifier Empty).updateContext
                                          { aliases := [{ typeArgs := ["a", "b"],
                                                          name := "myInt",
                                                          type := mty[int]}] })
                    ["a", "b"]
                    [("x", mty[%a]), ("y", mty[myInt %a %b]), ("z", mty[%a])])
         return Signature.format ans.fst

/--
Trivial conversion of a `MonoTySignature` to a `TySignature`, with an empty list
of universally quantified type variables.
-/
def LMonoTySignature.toTrivialLTy (s : @LMonoTySignature Identifier ExtraRestrict) : @LTySignature Identifier ExtraRestrict :=
  s.map (fun (x, ty) => (x, .forAll [] ty))

/--
Generate fresh type variables only for unnannotated identifiers in `ids`,
retaining any pre-existing type annotations.
-/
def TEnv.maybeGenMonoTypes (T : (TEnv Identifier ExtraRestrict)) (ids : (IdentTs Identifier ExtraRestrict)) : List (LMonoTy ExtraRestrict) × (TEnv Identifier ExtraRestrict) :=
  match ids with
  | [] => ([], T)
  | (_x, ty) :: irest =>
    match ty with
    | none =>
      let (xty_id, T) := TEnv.genTyVar T
      let xty := .ftvar xty_id
      let (ans, T) := maybeGenMonoTypes T irest
      (xty :: ans, T)
    | some xty =>
      let (ans, T) := maybeGenMonoTypes T irest
      (xty :: ans, T)

/--
Insert `fvi` (where `fvi` is the `i`-th element of `fvs`) in the oldest context
in `T`, only if `fvi` doesn't already exist in some context in `T`.

If `fvi` has no type annotation, a fresh type variable is put in the context.
-/
def TEnv.addInOldestContext (fvs : (IdentTs Identifier ExtraRestrict)) (T : (TEnv Identifier ExtraRestrict)) : (TEnv Identifier ExtraRestrict) :=
  let (monotys, T) := maybeGenMonoTypes T fvs
  let tys := monotys.map (fun mty => LTy.forAll [] mty)
  let types := T.genEnv.context.types.addInOldest fvs.idents tys
  T.updateContext { T.genEnv.context with types := types }

/--
Add a well-formed `alias` to the context, where the type definition is first
de-aliased.
-/
def TEnv.addTypeAlias [DecidableEq ExtraRestrict] (alias : TypeAlias ExtraRestrict) (T : TEnv Identifier ExtraRestrict) : Except Format (TEnv Identifier ExtraRestrict) := do
  let alias_lty := alias.toAliasLTy
  if !alias.typeArgs.Nodup then
    .error f!"[TEnv.addTypeAlias] Duplicates found in the type arguments!\n\
               Name: {alias.name}\n\
               Type Arguments: {alias.typeArgs}\n\
               Type Definition: {alias.type}"
  else if !((alias.type.freeVars ⊆ alias.typeArgs) &&
            (alias_lty.freeVars ⊆ alias.typeArgs)) then
    .error f!"[TEnv.addTypeAlias] Type definition contains free type arguments!\n\
              Name: {alias.name}\n\
              Type Arguments: {alias.typeArgs}\n\
              Type Definition: {alias.type}"
  else
    let (mtys, T) := LMonoTys.instantiate alias.typeArgs [alias_lty.toMonoTypeUnsafe, alias.type] T
    match mtys with
    | [lhs, rhs] =>
      let newTyArgs := lhs.freeVars
      -- We expect `alias.type` to be a known, legal type, hence the use of
      -- `instantiateWithCheck` below. Note that we only store type
      -- declarations -- not synonyms -- as values in the alias table;
      -- i.e., we don't store a type alias mapped to another type alias.
      let (rhsmty, _) ← (LTy.forAll [] rhs).instantiateWithCheck T
      let new_aliases := { typeArgs := newTyArgs,
                           name := alias.name,
                           type := rhsmty } :: T.genEnv.context.aliases
      let context := { T.genEnv.context with aliases := new_aliases }
      .ok (T.updateContext context)
    | _ => .error f!"[TEnv.addTypeAlias] Implementation error! \n\
                      {alias}"

---------------------------------------------------------------------

end Lambda

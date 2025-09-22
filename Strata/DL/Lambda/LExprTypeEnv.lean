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
structure TypeAlias where
  name : String
  typeArgs : List TyIdentifier
  type : LMonoTy
  deriving DecidableEq, Repr, Inhabited

def TypeAlias.toAliasLTy (a : TypeAlias) : LTy :=
  .forAll a.typeArgs (.tcons a.name (a.typeArgs.map (fun i => .ftvar i)))

instance : ToFormat TypeAlias where
  format t := f!"{t.toAliasLTy} := {t.type}"

variable {T: LExprParams} [DecidableEq T.Identifier] [ToFormat T.Metadata] [ToFormat T.Identifier]

/--
A type context contains two maps: `types` and `aliases`.

The `types` field maps free variables in expressions (i.e., `LExpr.fvar`s) to
their type schemes. This is essentially a stack to account for variable scopes.

The `aliases` field maps type synonyms to their corresponding type definitions.
We expect these type definitions to not be aliases themselves, to avoid any
cycles in the map (see `TEnv.addTypeAlias`).
-/
structure TContext (Identifier : Type) where
  types   :  Maps Identifier LTy := []
  aliases :  List TypeAlias := []
  deriving DecidableEq, Repr

instance {Identifier} [ToFormat Identifier] : ToFormat (TContext Identifier) where
  format ctx :=
    f!"types:   {ctx.types}\n\
       aliases: {ctx.aliases}"

/--
Get all the known variables (i.e., `LExpr.fvar`s) in the typing context.
-/
def TContext.knownVars (ctx : (TContext Identifier)) : List Identifier :=
  go ctx.types
  where go types :=
  match types with
  | [] => [] | m :: rest => m.keys ++ go rest

def TContext.types.knownTypeVars (types : Maps Identifier LTy) : List TyIdentifier :=
  match types with
  | [] => []
  | m :: rest => go m ++ knownTypeVars rest
  where go (m : Map Identifier LTy) :=
    match m with
    | [] => [] | (_, ty) :: rest => LTy.freeVars ty ++ go rest

/--
Get all the known type variables (i.e., free `LMonoTy.ftvar`s) in the typing
context.
-/
def TContext.knownTypeVars (ctx : (TContext Identifier)) : List TyIdentifier :=
  types.knownTypeVars ctx.types

/--
Is `x` is a fresh type variable w.r.t. the context?
-/
def TContext.isFresh (tx : TyIdentifier) (Γ : (TContext T.Identifier)) : Prop :=
  ∀ (x : T.Identifier) (ty : LTy),
    Γ.types.find? x = some ty → tx ∉ (LTy.freeVars ty)

/--
Are `xs` fresh type variables w.r.t. the context?
-/
def TContext.allFreshVars (xs : List TyIdentifier) (Γ : (TContext T.Identifier)) : Prop :=
  match xs with
  | [] => True
  | x :: rest => (TContext.isFresh x Γ) ∧ (TContext.allFreshVars rest Γ)

def TContext.types.subst (types : Maps Identifier LTy) (S : Subst) :
  Maps Identifier LTy :=
  match types with
  | [] => []
  | tmap :: trest =>
    go tmap :: types.subst trest S
  where go (tmap : Map Identifier LTy) :=
    match tmap with
    | [] => []
    | (x, ty) :: mrest =>
      (x, LTy.subst S ty) :: go mrest

/--
Apply a substitution `S` to the context.
-/
def TContext.subst (ctx : TContext Identifier) (S : Subst) : TContext Identifier :=
  { ctx with types := types.subst ctx.types S }

---------------------------------------------------------------------

/--
Typing state.

The typing state does bookkeeping to generate fresh expression and type
variables needed during type inference. It also has a global substitution map
`TState.subst`.

Also see functions `TEnv.genTyVar` and `TEnv.genExprVar`.
-/
structure TState where
  tyGen : Nat := 0
  tyPrefix : String := "$__ty"
  exprGen : Nat := 0
  exprPrefix : String := "$__var"
  substInfo : SubstInfo := SubstInfo.empty
  deriving Repr

def TState.init : TState := {}

def TState.incTyGen (state : TState) : TState :=
  { state with tyGen := state.tyGen + 1 }

def TState.genTySym (state : TState) : TyIdentifier × TState :=
  let new_idx := state.tyGen
  let state := state.incTyGen
  let new_var := state.tyPrefix ++ toString new_idx
  (new_var, state)

def TState.incExprGen (state : TState) : TState :=
  { state with exprGen := state.exprGen + 1 }

def TState.genExprSym (state : TState) : String × TState :=
  let new_idx := state.exprGen
  let state := state.incExprGen
  let new_var := state.exprPrefix ++ toString new_idx
  (new_var, state)

instance : ToFormat TState where
  format ts :=
    f!"tyGen: {ts.tyGen}{Format.line}\
       tyPrefix: {ts.tyPrefix}{Format.line}\
       exprGen: {ts.exprGen}{Format.line}\
       exprPrefix: {ts.exprPrefix}{Format.line}\
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

def LTy.toKnownType! (lty : LTy) : KnownType :=
  match lty with
  | .forAll _ (.tcons name args) => { name, arity := args.length }
  | .forAll [] (.bitvec _) => { name := "bitvec", arity := 1 }
  | _ => panic! s!"Unsupported known type: {lty}"

instance : ToFormat KnownType where
  format k := f!"{k.toLTy}"

/-- Registered types. -/
abbrev KnownTypes := List KnownType

def KnownTypes.keywords (ks : KnownTypes) : List String :=
  ks.map (fun k => k.name)

/--
A type environment `TEnv` contains a stack of contexts `TContext` to track `LExpr`
variables and their types, a typing state `TState` to track the global
substitution and fresh variable generation, and a `KnownTypes` to track the
supported type constructors. It also has type information about a
factory of user-specified functions, which is used during type checking.
-/
structure TEnv (T: LExprParams) where
  context : TContext T.Identifier
  state : TState
  functions : Array (LFunc T)
  knownTypes : KnownTypes

def KnownTypes.default : KnownTypes :=
  open LTy.Syntax in
  [t[∀a b. %a → %b],
   t[bool],
   t[int],
   t[string]].map (fun k => k.toKnownType!)

def TEnv.default {T : LExprParams} : TEnv T :=
  open LTy.Syntax in
  { context := {},
    state := TState.init,
    functions := #[],
    knownTypes := KnownTypes.default
  }

instance : ToFormat (TEnv T) where
  format s := f!"context:{Format.line}{s.context}\
                 {Format.line}\
                 state:{Format.line}{s.state}\
                 {Format.line}\
                 known types:{Format.line}{s.knownTypes}"

def TEnv.addKnownType (Env : TEnv T) (k : KnownType) : TEnv T :=
  { Env with knownTypes := k :: Env.knownTypes }

def TEnv.addFactoryFunction (Env : TEnv T) (fn : LFunc T) : TEnv T :=
  { Env with functions := Env.functions.push fn }

def TEnv.addFactoryFunctions (Env : TEnv T) (fact : Array (LFunc T)) : TEnv T :=
  { Env with functions := Env.functions.append fact }

/--
Replace the global substitution in `T.state.subst` with `S`.
-/
def TEnv.updateSubst {T} (env : (TEnv T)) (S : SubstInfo) : (TEnv T) :=
  { env with state.substInfo := S }

def TEnv.pushEmptyContext [DecidableEq T.Identifier] (env : (TEnv T)) : (TEnv T) :=
  let ctx := env.context
  let ctx' := { ctx with types := ctx.types.push [] }
  { env with context := ctx' }

def TEnv.popContext  (env : (TEnv T)) : (TEnv T) :=
  let ctx := env.context
  let ctx' := { ctx with types := ctx.types.pop }
  { env with context := ctx' }

/--
Insert `(x, ty)` in `T.context`.
-/
def TEnv.insertInContext {T: LExprParams} [DecidableEq T.Identifier] (Env : TEnv T) (x : T.Identifier) (ty : LTy) : (TEnv T) :=
  let ctx := Env.context
  let ctx' := { ctx with types := ctx.types.insert x ty }
  { Env with context := ctx' }

/--
Insert each element in `map` in `T.context`.
-/
def TEnv.addToContext {T: LExprParams} [DecidableEq T.Identifier] (Env : (TEnv T)) (map : Map T.Identifier LTy) : (TEnv T) :=
  let ctx := Env.context
  let types := List.foldl (fun m (x, v) => m.insert x v) ctx.types map
  let ctx' := { ctx with types := types }
  { Env with context := ctx' }

/--
Erase entry for `x` from `T.context`.
-/
def TEnv.eraseFromContext [DecidableEq T.Identifier] (Env : TEnv T) (x : T.Identifier) : (TEnv T) :=
  let ctx := Env.context
  let ctx' := { ctx with types := ctx.types.erase x }
  { Env with context := ctx' }

def TEnv.freeVarCheck [DecidableEq T.Identifier] (Env : TEnv T) (e : LExpr T.mono) (msg : Format) :
  Except Format Unit :=
  let efv := (@freeVars T e).map Prod.fst
  let knownVars := Env.context.knownVars
  let freeVars := List.filter (fun v => v ∉ knownVars) efv
  match freeVars with
  | [] => .ok ()
  | _ =>
    .error f!"{msg} No free variables are allowed here!\
              {Format.line}\
              Free Variables: {freeVars}"

def TEnv.freeVarChecks [DecidableEq T.Identifier] (Env : TEnv T) (es : List (LExpr T.mono)) : Except Format Unit :=
  match es with
  | [] => .ok ()
  | e :: erest => do
    let _ ← freeVarCheck Env e f!"[{e}]"
    freeVarChecks Env erest

instance : Inhabited (TyIdentifier × TEnv T) where
  default := ("$__ty0", TEnv.default)

/-- Variable Generator -/
class HasGen (T : LExprParams) where
  genVar : TEnv T → T.Identifier × TEnv T

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
def TEnv.genExprVar (Env : TEnv ⟨Metadata, String⟩) : (String × TEnv ⟨Metadata, String⟩) :=
  let (new_var, state) := Env.state.genExprSym
  let Env := { Env with state := state }
  let known_vars := TContext.knownVars Env.context
  if new_var ∈ known_vars then
    panic s!"[TEnv.genExprVar] Generated variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    (new_var, Env)

instance : HasGen {Metadata, Identifier := String} where
  genVar := TEnv.genExprVar

/--
Generate a fresh type variable (`ftvar`).

This function is the canonical way of obtaining fresh type variables. This --
along with the restriction that all `ftvar`s in an annotation are implicitly
universally quantified -- ensures that we always get a fresh type variable when
we use `TEnv.genTyVar`.
-/
def TEnv.genTyVar (Env : TEnv T) : TyIdentifier × (TEnv T) :=
  let (new_var, state) := Env.state.genTySym
  let Env := { Env with state := state }
  if new_var ∈ Env.context.knownTypeVars then
    panic s!"[TEnv.genTyVar] Generated type variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    (new_var, Env)

/--
Generate `n` fresh type variables (`ftvar`s).
-/
def TEnv.genTyVars (n : Nat) (Env : (TEnv T)) : List TyIdentifier × (TEnv T) :=
  match n with
  | 0 => ([], Env)
  | n' + 1 =>
    let (ty, Env) := TEnv.genTyVar Env
    let (rest_ty, Env) := TEnv.genTyVars n' Env
    (ty :: rest_ty, Env)

/--
Consistently instantiate type variables `ids` in `mtys`.
-/
def LMonoTys.instantiate (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv T) :
  LMonoTys × (TEnv T) :=
  let (freshtvs, Env) := TEnv.genTyVars ids.length Env
  let S := List.zip ids (List.map (fun tv => (LMonoTy.ftvar tv)) freshtvs)
  (LMonoTys.subst S mtys, Env)

omit [DecidableEq T.Identifier] in
omit [ToFormat T.Metadata] in
theorem LMonoTys.instantiate_length:
  (LMonoTys.instantiate (T:=T) ids mty Env).fst.length == mty.length := by
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
def LTy.instantiate (ty : LTy) (Env : (TEnv T)) : LMonoTy × (TEnv T) :=
  match ty with
  | .forAll [] mty' => (mty', T)
  | .forAll xs lty' =>
    let (freshtvs, Env) := TEnv.genTyVars xs.length Env
    let S := List.zip xs (List.map (fun tv => (.ftvar tv)) freshtvs)
    (LMonoTy.subst S lty', Env)

instance : Inhabited (Option LMonoTy × TEnv T) where
  default := (none, TEnv.default)

/--
Return the instantiated definition of `mty` -- which is expected to be
`.tcons name args` --  if it is a type alias registered in the typing
environment `T`.

This function does not descend into the subtrees of `mty`, nor does it check
whether the de-aliased types are registered/known.
-/
def LMonoTy.aliasDef? (mty : LMonoTy) (Env : (TEnv T)) : (Option LMonoTy × TEnv T) :=
  match mty with
  | .ftvar _ =>
    -- We can't have a free variable be the LHS of an alias definition because
    -- then it will unify with every type.
    (none, Env)
  | .bitvec _ =>
    -- A bitvector cannot be a type alias.
    (none, Env)
  | .tcons name args =>
    match Env.context.aliases.find? (fun a => a.name == name && a.typeArgs.length == args.length) with
    | none => (none, Env)
    | some alias =>
      let (lst, Env) := LMonoTys.instantiate alias.typeArgs [(.tcons name (alias.typeArgs.map (fun a => .ftvar a))), alias.type] Env
      -- (FIXME): Use `LMonoTys.instantiate_length` to remove the `!` below.
      let alias_inst := lst[0]!
      let alias_def := lst[1]!
      match Constraints.unify [(mty, alias_inst)] Env.state.substInfo with
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
($__ty1, (BarAlias $__ty0 $__ty0))
(p, $__ty0)
-/
#guard_msgs in
open LTy.Syntax in
#eval let (ans, T) := LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %p %p)]
        { @TEnv.default String with
          context := { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]} }
      format f!"Ans: {ans}\n\
                Subst:\n{T.state.substInfo.subst}"

/-- info: some (Foo $__ty0 (BarAlias q $__ty0)) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %q %p)]
        { @TEnv.default String with
          context := { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]} }
      |>.fst |> format

/-- info: some int -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myInt]
      { @TEnv.default String with context :=
                  { aliases := [{ typeArgs := [],
                                  name := "myInt",
                                  type := mty[int]}]} }
      |>.fst |> format

/-- info: some bool -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[BadBoolAlias %p %q]
        { @TEnv.default String with
          context := { aliases := [{ typeArgs := ["x", "y"],
                                     name := "BadBoolAlias",
                                     type := mty[bool]}]} }
      |>.fst |> format

/-- info: none -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myInt]
                    { @TEnv.default String with context := { aliases := [{
                         typeArgs := ["a"],
                         name := "myInt",
                         type := mty[int]}] } }
      |>.fst |> format

/-- info: some (myDef int) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myAlias int bool]
                    { @TEnv.default String with
                    context := {
                      aliases := [{
                        typeArgs := ["a", "b"],
                        name := "myAlias",
                        type := mty[myDef %a]}] }}
      |>.fst |> format

mutual
/--
De-alias `mty`, including at the subtrees.
-/
partial def LMonoTy.resolveAliases (mty : LMonoTy) (T : TEnv Identifier) : (Option LMonoTy × TEnv Identifier) :=
  let (maybe_mty, T) := LMonoTy.aliasDef? mty T
  match maybe_mty with
  | some (.tcons name args) =>
    let (args', T) := LMonoTys.resolveAliases args T.context.aliases T
    match args' with
    | none => (some (.tcons name args), T)
    | some args' => (some (.tcons name args'), T)
  | some mty' => (some mty', T)
  | none =>
    match mty with
    | .ftvar _ => (some mty, T)
    | .bitvec _ => (some mty, T)
    | .tcons name mtys =>
      let (maybe_mtys, T) := LMonoTys.resolveAliases mtys T.context.aliases T
      match maybe_mtys with
      | none => (none, T)
      | some mtys' => (some (.tcons name mtys'), T)

/--
De-alias `mtys`, including at the subtrees.
-/
partial def LMonoTys.resolveAliases (mtys : LMonoTys) (aliases : List TypeAlias) (T : (TEnv Identifier)) :
    (Option LMonoTys × (TEnv Identifier)) :=
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
($__ty2, $__ty3)
($__ty0, $__ty3)
($__ty1, (BarAlias $__ty3 $__ty3))
(p, $__ty3)
-/
#guard_msgs in
open LTy.Syntax in
#eval let (ty, T) := LMonoTy.resolveAliases
        mty[FooAlias %p (BarAlias %p %p)]
        { @TEnv.default String with
          context := { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]} }
      format f!"De-aliased type: {ty}\n\
                Subst:\n{T.state.substInfo.subst}"

/--
Instantiate and de-alias `ty`, including at the subtrees.
-/
def LTy.resolveAliases (ty : LTy) (Env : (TEnv T)) : (Option LMonoTy × (TEnv T)) :=
  let (mty, Env) := ty.instantiate Env
  LMonoTy.resolveAliases mty Env

/-- info: some (arrow bool $__ty0) -/
#guard_msgs in
open LTy.Syntax in
#eval LTy.resolveAliases
        t[∀x. (FooAlias %x %x) → %x]
        { @TEnv.default TDefault with context := { aliases := [{
                                        typeArgs := ["x", "y"],
                                        name := "FooAlias",
                                        type := mty[bool]}]} }
      |>.fst |>.format

mutual
/--
Is `ty` an instance of a known type in `ks`? We expect `ty` to be
de-aliased.
-/
def LMonoTy.knownInstance (ty : LMonoTy) (ks : KnownTypes) : Bool :=
  match ty with
  | .ftvar _ | .bitvec _ => true
  | .tcons name args =>
    (ks.contains { name := name, arity := args.length }) &&
    LMonoTys.knownInstances args ks

/--
Are `tys` instances of some known type in `ks`? We expect all types in
`tys` to be de-aliased.
-/
def LMonoTys.knownInstances (tys : LMonoTys) (ks : KnownTypes) : Bool :=
  match tys with
  | [] => true
  | ty :: trest =>
    if LMonoTy.knownInstance ty ks then LMonoTys.knownInstances trest ks else false
end

def isInstanceOfKnownType (ty : LMonoTy) (Env : TEnv T) : Bool :=
  LMonoTy.knownInstance ty Env.knownTypes

/--
Instantiate `mty` by replacing all free type variables with fresh ones, and then
perform resolution of type aliases and subsequent checks for registered types.
-/
def LMonoTy.instantiateWithCheck (mty : LMonoTy) (T : (TEnv Identifier)) :
    Except Format (LMonoTy × (TEnv Identifier)) := do
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
def LTy.instantiateWithCheck (ty : LTy) (Env : (TEnv T)) : Except Format (LMonoTy × (TEnv T)) := do
  let (mty, Env) := match ty.resolveAliases Env with
                  | (some ty', Env) => (ty', Env)
                  | (none, Env) => ty.instantiate Env
  if isInstanceOfKnownType mty Env
  then return (mty, Env)
  else .error f!"Type {ty} is not an instance of a previously registered type!\n\
                 Known Types: {Env.knownTypes}"

section

open LTy.Syntax

/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[myTy (myTy)]
                            { @TEnv.default TDefault with
                                knownTypes := [LTy.toKnownType! t[∀a. myTy %a],
                                               LTy.toKnownType! t[int]] }

abbrev TTyDefault: LExprParams := {Metadata := Unit, Identifier := TyIdentifier}
/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[Foo] (@TEnv.default TTyDefault)

/--
info: error: Type (arrow int Foo) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), bool, int, string]
-/
#guard_msgs in
#eval do let ans ← t[int → Foo].instantiateWithCheck (@TEnv.default TTyDefault)
         return format ans

/-- info: ok: (arrow int bool) -/
#guard_msgs in
#eval do let ans ← t[int → bool].instantiateWithCheck (@TEnv.default TTyDefault)
         return format ans.fst
end

/--
Instantiate the scheme `ty` and apply the global substitution `Env.state.subst` to
it.
-/
def LTy.instantiateAndSubst (ty : LTy) (Env : (TEnv T)) : Except Format (LMonoTy × (TEnv T)) := do
  let (mty, Env) ← LTy.instantiateWithCheck ty Env
  let mty := LMonoTy.subst Env.state.substInfo.subst mty
  return (mty, Env)

def LTy.instantiateAndSubsts (tys : List LTy) (Env : (TEnv T)) :
  Except Format (List LMonoTy × (TEnv T)) := do
  match tys with
  | [] => return ([], Env)
  | ty :: tyrest =>
    let (mty, Env) ← LTy.instantiateAndSubst ty Env
    let (mtyrest, Env) ← LTy.instantiateAndSubsts tyrest Env
    return ((mty :: mtyrest), Env)

/--
Get the monotype of variable corresponding to identifier `x` by instantiating
the type and then applying the global substitution.
-/
def Identifier.instantiateAndSubst (x : T.Identifier) (Env : (TEnv T)) :
  Except Format (Option (LMonoTy × (TEnv T))) := do
  match Env.context.types.find? x with
  | some ty => LTy.instantiateAndSubst ty Env
  | none => return none

def Identifier.instantiateAndSubsts (xs : List T.Identifier) (Env : (TEnv T)) :
  Except Format (Option (List LMonoTy × (TEnv T))) := do
  match xs with
  | [] => return some ([], Env)
  | x :: xrest =>
    let ans ← instantiateAndSubst x Env
    match ans with
    | none => return none
    | some (xty, Env) =>
      let ans ← Identifier.instantiateAndSubsts xrest Env
      match ans with
      | none => return none
      | some (xtys, Env) => return ((xty :: xtys), Env)

/-- info: (arrow $__ty0 b) -/
#guard_msgs in
open LTy.Syntax in
#eval format $ (LTy.instantiate t[∀a. %a → %b] (@TEnv.default TDefault)).fst

/--
Instantiate the scheme `∀tyArgs. s` by _consistently_ filling in fresh type
variables for all the variables bound by the universal quantifier.

E.g., the instantiation of `∀a. (x : a) (y : int) (z : a)` must be something
like `(x : _ty0) (y : int) (z : _ty0)`, and not `(x : _ty0) (y : int) (z : _ty1)`.
-/
def LMonoTySignature.instantiate (Env : (TEnv T)) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature Identifier) :
  Except Format ((@LMonoTySignature Identifier) × (TEnv T)) := do
  let (mtys, Env) := LMonoTys.instantiate tyArgs sig.values Env
  let tys := mtys.map (fun mty => (LTy.forAll [] mty))
  let (newtys, Env) ← go Env tys
  .ok ((sig.keys.zip newtys), Env)
  where go (Env : (TEnv T)) (tys : LTys) : Except Format (LMonoTys × (TEnv T)) :=
    match tys with
    | [] => .ok ([], Env)
    | t :: trest => do
      let (mt, Env) ← LTy.instantiateWithCheck t Env
      let (mtrest, Env) ← go Env trest
      .ok (mt :: mtrest, Env)

/--
info: ok: (x : $__ty0) (y : int) (z : $__ty0)
-/
#guard_msgs in
open LTy.Syntax in
#eval do let ans ← (LMonoTySignature.instantiate
                    { @TEnv.default TTyDefault with context :=
                                          { aliases := [{ typeArgs := ["a", "b"],
                                                          name := "myInt",
                                                          type := mty[int]}] }}
                    ["a", "b"]
                    [("x", mty[%a]), ("y", mty[myInt %a %b]), ("z", mty[%a])])
         return Signature.format ans.fst

/--
Trivial conversion of a `MonoTySignature` to a `TySignature`, with an empty list
of universally quantified type variables.
-/
def LMonoTySignature.toTrivialLTy (s : @LMonoTySignature Identifier) : @LTySignature Identifier :=
  s.map (fun (x, ty) => (x, .forAll [] ty))

/--
Generate fresh type variables only for unnannotated identifiers in `ids`,
retaining any pre-existing type annotations.
-/
def TEnv.maybeGenMonoTypes (Env : (TEnv T)) (ids : (IdentTs Identifier)) : List LMonoTy × (TEnv T) :=
  match ids with
  | [] => ([], Env)
  | (_x, ty) :: irest =>
    match ty with
    | none =>
      let (xty_id, Env) := TEnv.genTyVar Env
      let xty := .ftvar xty_id
      let (ans, Env) := maybeGenMonoTypes Env irest
      (xty :: ans, Env)
    | some xty =>
      let (ans, Env) := maybeGenMonoTypes Env irest
      (xty :: ans, Env)

/--
Insert `fvi` (where `fvi` is the `i`-th element of `fvs`) in the oldest context
in `Env`, only if `fvi` doesn't already exist in some context in `Env`.

If `fvi` has no type annotation, a fresh type variable is put in the context.
-/
def TEnv.addInOldestContext (fvs : (IdentTs T.Identifier)) (Env : (TEnv T)) : (TEnv T) :=
  let (monotys, Env) := maybeGenMonoTypes Env fvs
  let tys := monotys.map (fun mty => LTy.forAll [] mty)
  let types := Env.context.types.addInOldest fvs.idents tys
  { Env with context := { Env.context with types := types } }

/--
Add a well-formed `alias` to the context, where the type definition is first
de-aliased.
-/
def TEnv.addTypeAlias (alias : TypeAlias) (Env : TEnv T) : Except Format (TEnv T) := do
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
    let (mtys, Env) := LMonoTys.instantiate alias.typeArgs [alias_lty.toMonoTypeUnsafe, alias.type] Env
    match mtys with
    | [lhs, rhs] =>
      let newTyArgs := lhs.freeVars
      -- We expect `alias.type` to be a known, legal type, hence the use of
      -- `instantiateWithCheck` below. Note that we only store type
      -- declarations -- not synonyms -- as values in the alias table;
      -- i.e., we don't store a type alias mapped to another type alias.
      let (rhsmty, _) ← (LTy.forAll [] rhs).instantiateWithCheck Env
      let new_aliases := { typeArgs := newTyArgs,
                           name := alias.name,
                           type := rhsmty } :: Env.context.aliases
      let context := { Env.context with aliases := new_aliases }
      .ok { Env with context := context }
    | _ => .error f!"[TEnv.addTypeAlias] Implementation error! \n\
                      {alias}"

---------------------------------------------------------------------

end Lambda

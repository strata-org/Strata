/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTyUnify
import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.TypeFactory
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

variable {T: LExprParams} [DecidableEq T.IDMeta] [ToFormat T.Metadata] [ToFormat T.IDMeta]

/--
A type context describing the types of free variables and the mappings of type
aliases.
-/
structure TContext (IDMeta : Type) where

  /-- A map from free variables in expressions (i.e., `LExpr.fvar`s) to their
  type schemes. This is essentially a stack to account for variable scopes.  -/
  types   :  Maps (Identifier IDMeta) LTy := []

  /-- A map from type synonym names to their corresponding type definitions.  We
  expect these type definitions to not be aliases themselves, to avoid any
  cycles in the map (see `TEnv.addTypeAlias`).  -/
  aliases :  List TypeAlias := []

  deriving DecidableEq, Repr, Inhabited

instance {IDMeta} [ToFormat IDMeta] : ToFormat (TContext IDMeta) where
  format ctx :=
    f!"types:   {ctx.types}\n\
       aliases: {ctx.aliases}"

/--
Get all the known variables (i.e., `LExpr.fvar`s) in the typing context.
-/
def TContext.knownVars (ctx : (TContext IDMeta)) : List (Identifier IDMeta) :=
  go ctx.types
  where go types :=
  match types with
  | [] => [] | m :: rest => m.keys ++ go rest

def TContext.types.knownTypeVars (types : Maps (Identifier IDMeta) LTy) : List TyIdentifier :=
  match types with
  | [] => []
  | m :: rest => go m ++ knownTypeVars rest
  where go (m : Map (Identifier IDMeta) LTy) :=
    match m with
    | [] => [] | (_, ty) :: rest => LTy.freeVars ty ++ go rest

/--
Get all the known type variables (i.e., free `LMonoTy.ftvar`s) in the typing
context.
-/
def TContext.knownTypeVars (ctx : (TContext IDMeta)) : List TyIdentifier :=
  types.knownTypeVars ctx.types

/--
Is `x` is a fresh type variable w.r.t. the context?
-/
def TContext.isFresh (tx : TyIdentifier) (Γ : TContext T.IDMeta) : Prop :=
  ∀ (x : T.Identifier) (ty : LTy),
    Γ.types.find? x = some ty → tx ∉ (LTy.freeVars ty)

/--
Are `xs` fresh type variables w.r.t. the context?
-/
def TContext.allFreshVars (xs : List TyIdentifier) (Γ : (TContext T.IDMeta)) : Prop :=
  match xs with
  | [] => True
  | x :: rest => (TContext.isFresh x Γ) ∧ (TContext.allFreshVars rest Γ)

def TContext.types.subst (types : Maps (Identifier IDMeta) LTy) (S : Subst) :
  Maps (Identifier IDMeta) LTy :=
  match types with
  | [] => []
  | tmap :: trest =>
    go tmap :: types.subst trest S
  where go (tmap : Map (Identifier IDMeta) LTy) :=
    match tmap with
    | [] => []
    | (x, ty) :: mrest =>
      (x, LTy.subst S ty) :: go mrest

/--
Apply a substitution `S` to the context.
-/
def TContext.subst (ctx : TContext IDMeta) (S : Subst) : TContext IDMeta :=
  { ctx with types := types.subst ctx.types S }

---------------------------------------------------------------------

/--
The state of a generator used by typing.
-/
structure TState where
  tyGen : Nat := 0
  tyPrefix : String := "$__ty"
  exprGen : Nat := 0
  exprPrefix : String := "$__var"
deriving Repr, Inhabited

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

---------------------------------------------------------------------

/-- Name and arity of a registered type. -/
def KnownType := Identifier Nat deriving Inhabited, DecidableEq, Repr

def KnownType.arity (k: KnownType) := k.metadata

def KnownType.toLTy (k : KnownType) : LTy :=
  let bvars := (List.range k.arity).map (fun a => toString a)
  let args := bvars.map (fun b => .ftvar b)
  .forAll bvars (.tcons k.name args)

def LTy.toKnownType! (lty : LTy) : KnownType :=
  match lty with
  | .forAll _ (.tcons name args) => { name, metadata := args.length }
  | .forAll [] (.bitvec _) => { name := "bitvec", metadata := 1 }
  | _ => panic! s!"Unsupported known type: {lty}"

instance : ToFormat KnownType where
  format k := f!"{k.toLTy}"

/-- Registered types. -/
abbrev KnownTypes := Identifiers Nat

def makeKnownTypes (l: List KnownType) : KnownTypes :=
  Std.HashMap.ofList (l.map (fun x => (x.name, x.arity)))

def KnownTypes.keywords (ks : KnownTypes) : List String :=
  ks.keys

def KnownTypes.toList (ks: KnownTypes) : List KnownType :=
  (Std.HashMap.toList ks).map (fun x => ⟨x.1, x.2⟩)

def KnownTypes.addWithError (ks: KnownTypes) (x: KnownType) (f: Format) : Except Format KnownTypes :=
  Identifiers.addWithError ks ⟨x.name, x.arity⟩ f

def KnownTypes.contains (ks: KnownTypes) (x: KnownType) : Bool :=
  Identifiers.contains ks ⟨x.name, x.arity⟩

def KnownTypes.containsName (ks: KnownTypes) (x: String) : Bool :=
  Std.HashMap.contains ks x

instance : ToFormat KnownTypes where
  format ks := format (ks.toList)

structure TGenEnv (IDMeta : Type) where
  context : TContext IDMeta
  genState : TState
deriving Inhabited

def LDatatype.toKnownType (d: LDatatype IDMeta) : KnownType :=
  { name := d.name, metadata := d.typeArgs.length}

def TypeFactory.toKnownTypes (t: @TypeFactory IDMeta) : KnownTypes :=
  makeKnownTypes (t.foldr (fun t l => t.toKnownType :: l) [])

/--
A type environment `TEnv` contains
- genEnv: `TGenEnv` to track the generator state as well as the typing context
  (mapping from variables to their types, type aliases, etc)
- stateSubstInfo: `SubstInfo` to track type substitution info.
This is the top-level data structure that is used by type inference functions
such as LExpr.annotate.
-/
structure TEnv (IDMeta : Type) where
  genEnv : TGenEnv IDMeta
  stateSubstInfo: SubstInfo := SubstInfo.empty
deriving Inhabited

/--
Context data that does not change throughout type checking: a
factory of user-specified functions and data structures for ensuring unique
names of types and functions.
Invariant: all functions defined in `TypeFactory.genFactory`
for `datatypes` should be in `functions`.
-/
structure LContext (T: LExprParams) where
  /-- Descriptions of all built-in functions. -/
  functions : @Factory T
  /-- Descriptions of all built-in datatypes. -/
  datatypes : @TypeFactory T.IDMeta
  /-- A list of known built-in types. -/
  knownTypes : KnownTypes
  /-- The set of identifiers that have been seen or generated so far. -/
  idents : Identifiers T.IDMeta
deriving Inhabited

def LContext.empty {IDMeta} : LContext IDMeta :=
  ⟨#[], #[], {}, {}⟩

instance : EmptyCollection (LContext IDMeta) where
  emptyCollection := LContext.empty

def TEnv.context (T: TEnv IDMeta) : TContext IDMeta :=
  T.genEnv.context

def TEnv.updateContext {IDMeta} (T: TEnv IDMeta) (C: TContext IDMeta) : TEnv IDMeta :=
  let g := {T.genEnv with context := C}
  {T with genEnv := g}

/--
Lift stateful computations over `TGenEnv` to stateful computations over `TEnv`
-/
def liftGenEnv {α : Type} (f: TGenEnv IDMeta → α × (TGenEnv IDMeta)) (T: TEnv IDMeta) : α × TEnv IDMeta :=
  let (a, T') := f T.genEnv
  (a, {T with genEnv := T'})

def KnownTypes.default : KnownTypes :=
  open LTy.Syntax in
  makeKnownTypes ([t[∀a b. %a → %b],
   t[bool],
   t[int],
   t[string]].map (fun k => k.toKnownType!))

def TGenEnv.default : TGenEnv IDMeta :=
  { context := {},
    genState := TState.init,
  }

def TEnv.default : TEnv IDMeta :=
  let g := {context := {}, genState := TState.init}
  { genEnv := g}

def LContext.default : LContext T :=
  { functions := #[],
    datatypes := #[],
    knownTypes := KnownTypes.default,
    idents := Identifiers.default }

instance [ToFormat IDMeta] : ToFormat (TEnv IDMeta) where
  format s :=
    let g:TState := {
      tyGen := s.genEnv.genState.tyGen,
      tyPrefix := s.genEnv.genState.tyPrefix,
      exprGen := s.genEnv.genState.exprGen,
      exprPrefix := s.genEnv.genState.exprPrefix
    }
    f!"context:{Format.line}{s.context}\
       {Format.line}\
       state:{Format.line}\
       tyGen: {g.tyGen}{Format.line}\
       tyPrefix: {g.tyPrefix}{Format.line}\
       exprGen: {g.exprGen}{Format.line}\
       exprPrefix: {g.exprPrefix}{Format.line}\
       subst: {s.stateSubstInfo.subst}"

instance : ToFormat (LContext T) where
  format s := f!" known types:{Format.line}{s.knownTypes}\
                 identifiers:{Format.line}{s.idents}"


def LContext.addKnownTypeWithError (C : LContext T) (k : KnownType) (f: Format) : Except Format (LContext T) := do
  .ok {C with knownTypes := (← C.knownTypes.addWithError k f)}

def LContext.addKnownTypes (C : LContext T) (k : KnownTypes) : Except Format (LContext T) := do
  k.foldM (fun T k n => T.addKnownTypeWithError ⟨k, n⟩ f!"Error: type {k} already known") C

def LContext.addIdentWithError (C : LContext T) (i: T.Identifier) (f: Format) : Except Format (LContext T) := do
  let i ← C.idents.addWithError i f
  .ok {C with idents := i}

def LContext.addFactoryFunction (C : LContext T) (fn : LFunc T) : LContext T :=
  { C with functions := C.functions.push fn }

def LContext.addFactoryFunctions (C : LContext T) (fact : @Factory T) : LContext T :=
  { C with functions := C.functions.append fact }

/--
Add a datatype `d` to an `LContext` `C`.
This adds `d` to `C.datatypes`, adds the derived functions
(e.g. eliminators, testers) to `C.functions`, and adds `d` to
`C.knownTypes`. It performs error checking for name clashes.
-/
def LContext.addDatatype [Inhabited T.IDMeta] [Inhabited T.Metadata] (C: LContext T) (d: LDatatype T.IDMeta) : Except Format (LContext T) := do
  -- Ensure not in known types
  if C.knownTypes.containsName d.name then
    .error f!"Cannot name datatype same as known type!\n\
                      {d}\n\
                      KnownTypes' names:\n\
                      {C.knownTypes.keywords}"
  let ds ← C.datatypes.addDatatype d
  -- Add factory functions, checking for name clashes
  let f ← d.genFactory
  let fs ← C.functions.addFactory f
  -- Add datatype names to knownTypes
  let ks ← C.knownTypes.add d.toKnownType
  .ok {C with datatypes := ds, functions := fs, knownTypes := ks}

def LContext.addTypeFactory [Inhabited T.IDMeta] [Inhabited T.Metadata] (C: LContext T) (f: @TypeFactory T.IDMeta) : Except Format (LContext T) :=
  Array.foldlM (fun C d => C.addDatatype d) C f

/--
Replace the global substitution in `T.state.subst` with `S`.
-/
def TEnv.updateSubst (Env : TEnv IDMeta) (S : SubstInfo) : TEnv IDMeta :=
  { Env with stateSubstInfo := S }

theorem TEnv.SubstWF_of_pushemptySubstScope (T : TEnv IDMeta) :
  SubstWF (Maps.push T.stateSubstInfo.subst []) := by
  have h_SubstWF : SubstWF T.stateSubstInfo.subst := by
    apply T.stateSubstInfo.isWF
  generalize T.stateSubstInfo.subst = S at *
  simp_all [SubstWF, Subst.freeVars]
  done

def TEnv.pushEmptySubstScope (T : (TEnv IDMeta)) : (TEnv IDMeta) :=
  let new_subst := T.stateSubstInfo.subst.push []
  let newS := { subst := new_subst, isWF := (by rw [TEnv.SubstWF_of_pushemptySubstScope]) }
  { T with stateSubstInfo := newS }

theorem TEnv.SubstWF_of_popSubstScope (T : TEnv IDMeta) :
  SubstWF (Maps.pop T.stateSubstInfo.subst) := by
  have h_SubstWF : SubstWF T.stateSubstInfo.subst := by
    apply T.stateSubstInfo.isWF
  generalize T.stateSubstInfo.subst = S at *
  simp_all [Maps.pop]
  split <;> try simp_all
  rename_i ms m mrest
  simp [@SubstWF_of_cons m mrest (by assumption)]

def TEnv.popSubstScope (T : (TEnv IDMeta)) : (TEnv IDMeta) :=
  let new_subst := T.stateSubstInfo.subst.pop
  let newS := { subst := new_subst, isWF := (by rw [TEnv.SubstWF_of_popSubstScope]) }
  { T with stateSubstInfo := newS }

def TEnv.pushEmptyContext (T : (TEnv IDMeta)) : (TEnv IDMeta) :=
  let ctx := T.context
  let ctx' := { ctx with types := ctx.types.push [] }
  T.updateContext ctx'

def TEnv.popContext (Env : (TEnv IDMeta)) : (TEnv IDMeta) :=
  let ctx := Env.context
  let ctx' := { ctx with types := ctx.types.pop }
  Env.updateContext ctx'

def TGenEnv.insertInContext [DecidableEq (Identifier IDMeta)] (Env : TGenEnv IDMeta) (x : Identifier IDMeta) (ty : LTy) : TGenEnv IDMeta :=
  let ctx := Env.context
  let ctx' := { ctx with types := ctx.types.insert x ty }
  { Env with context := ctx' }

/--
Insert `(x, ty)` in `T.context`.
-/
def TEnv.insertInContext {T: LExprParams} [DecidableEq T.IDMeta] (Env : TEnv T.IDMeta) (x : T.Identifier) (ty : LTy) : TEnv T.IDMeta :=
  { Env with genEnv := TGenEnv.insertInContext Env.genEnv x ty}

/--
Insert each element in `map` in `T.context`.
-/
def TEnv.addToContext (Env : TEnv T.IDMeta) (map : Map T.Identifier LTy) : TEnv T.IDMeta :=
  let ctx := Env.context
  let types := List.foldl (fun m (x, v) => m.insert x v) ctx.types map
  let ctx' := { ctx with types := types }
  Env.updateContext ctx'

/--
Erase entry for `x` from `T.context`.
-/
def TEnv.eraseFromContext (Env : TEnv T.IDMeta) (x : T.Identifier) : TEnv T.IDMeta :=
  let ctx := Env.context
  let ctx' := { ctx with types := ctx.types.erase x }
  Env.updateContext ctx'

def TEnv.freeVarCheck [DecidableEq T.IDMeta] (Env : TEnv T.IDMeta) (e : LExpr T.mono) (msg : Format) :
  Except Format Unit :=
  let efv := (@freeVars T LMonoTy e).map Prod.fst
  let knownVars := Env.context.knownVars
  let freeVars := List.filter (fun v => v ∉ knownVars) efv
  match freeVars with
  | [] => .ok ()
  | _ =>
    .error f!"{msg} No free variables are allowed here!\
              {Format.line}\
              Free Variables: {freeVars}"

def TEnv.freeVarChecks [DecidableEq T.IDMeta] (Env : TEnv T.IDMeta) (es : List (LExpr T.mono)) : Except Format Unit :=
  match es with
  | [] => .ok ()
  | e :: erest => do
    let _ ← freeVarCheck Env e f!"[{e}]"
    freeVarChecks Env erest

instance : Inhabited (TyIdentifier × TEnv T.IDMeta) where
  default := ("$__ty0", TEnv.default)

instance [Inhabited T.IDMeta] : Inhabited (T.Identifier × TEnv T.IDMeta) where
  default := ⟨⟨"$__ty0", Inhabited.default⟩, TEnv.default ⟩

/-- Variable Generator -/
class HasGen (IDMeta: Type) where
  genVar : TGenEnv IDMeta → (Identifier IDMeta) × TGenEnv IDMeta

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
def TEnv.genExprVar (Env: TGenEnv Unit) : (Identifier Unit × TGenEnv Unit) :=
  let (new_var, state) := Env.genState.genExprSym
  let Env :={ Env with genState := state }
  let known_vars := TContext.knownVars Env.context
  if ⟨new_var, ()⟩ ∈ known_vars then
    panic s!"[TEnv.genExprVar] Generated variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    (new_var, Env)

instance : HasGen Unit where
  genVar := TEnv.genExprVar

/--
Generate a fresh type variable (`ftvar`).

This function is the canonical way of obtaining fresh type variables. This --
along with the restriction that all `ftvar`s in an annotation are implicitly
universally quantified -- ensures that we always get a fresh type variable when
we use `TEnv.genTyVar`.
-/
def TGenEnv.genTyVar [ToFormat IDMeta] (Env : TGenEnv IDMeta) : TyIdentifier × (TGenEnv IDMeta) :=
  let (new_var, state) := Env.genState.genTySym
  let Env := {Env with genState := state}
  if new_var ∈ Env.context.knownTypeVars then
    panic s!"[TEnv.genTyVar] Generated type variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    (new_var, Env)

def TEnv.genTyVar [ToFormat IDMeta] (T : TEnv IDMeta) : TyIdentifier × (TEnv IDMeta) :=
  liftGenEnv TGenEnv.genTyVar T

/--
Generate `n` fresh type variables (`ftvar`s).
-/
def TGenEnv.genTyVars [ToFormat IDMeta] (n : Nat) (Env : TGenEnv IDMeta) : List TyIdentifier × (TGenEnv IDMeta) :=
  match n with
  | 0 => ([], Env)
  | n' + 1 =>
    let (ty, Env) := TGenEnv.genTyVar Env
    let (rest_ty, Env) := TGenEnv.genTyVars n' Env
    (ty :: rest_ty, Env)

/--
Consistently instantiate type variables `ids` in `mtys`.
-/
def LMonoTys.instantiate [ToFormat IDMeta] (ids : List TyIdentifier) (mtys : LMonoTys) (T : TGenEnv IDMeta) :
  LMonoTys × (TGenEnv IDMeta) :=
  let (freshtvs, T) := TGenEnv.genTyVars ids.length T
  let S := List.zip ids (List.map (fun tv => (LMonoTy.ftvar tv)) freshtvs)
  (LMonoTys.subst [S] mtys, T)

def LMonoTys.instantiateEnv [ToFormat IDMeta] (ids : List TyIdentifier) (mtys : LMonoTys) (T : (TEnv IDMeta)) :
  LMonoTys × (TEnv IDMeta) :=
  liftGenEnv (LMonoTys.instantiate ids mtys) T

theorem LMonoTys.instantiate_length [ToFormat IDMeta] :
  (LMonoTys.instantiate (IDMeta:=IDMeta) ids mty Env).fst.length == mty.length := by
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
def LTy.instantiate [ToFormat IDMeta] (ty : LTy) (Env : TGenEnv IDMeta) : LMonoTy × (TGenEnv IDMeta) :=
  match ty with
  | .forAll [] mty' => (mty', Env)
  | .forAll xs lty' =>
    let (freshtvs, Env) := TGenEnv.genTyVars xs.length Env
    let S := List.zip xs (List.map (fun tv => (.ftvar tv)) freshtvs)
    (LMonoTy.subst [S] lty', Env)

instance : Inhabited (Option LMonoTy × TEnv IDMeta) where
  default := (none, TEnv.default)

/--
Return the instantiated definition of `mty` -- which is expected to be
`.tcons name args` --  if it is a type alias registered in the typing
environment `T`.

This function does not descend into the subtrees of `mty`, nor does it check
whether the de-aliased types are registered/known.
-/
def LMonoTy.aliasDef? [ToFormat IDMeta] (mty : LMonoTy) (Env : TEnv IDMeta) : (Option LMonoTy × TEnv IDMeta) :=
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
      let (lst, Env) := LMonoTys.instantiateEnv alias.typeArgs [(.tcons name (alias.typeArgs.map (fun a => .ftvar a))), alias.type] Env
      -- (FIXME): Use `LMonoTys.instantiate_length` to remove the `!` below.
      let alias_inst := lst[0]!
      let alias_def := lst[1]!
      match Constraints.unify [(mty, alias_inst)] Env.stateSubstInfo with
      | .error e =>
        panic! s!"[LMonoTy.aliasDef?] {e}"
      | .ok S =>
        (alias_def.subst S.subst, Env.updateSubst S)

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
#eval let (ans, Env) := LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %p %p)]
        ( (@TEnv.default String).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]})
      format f!"Ans: {ans}\n\
                Subst:\n{Env.stateSubstInfo.subst}"

/-- info: some (Foo $__ty0 (BarAlias q $__ty0)) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[FooAlias %p (BarAlias %q %p)]
        ( (@TEnv.default String).updateContext
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
      ( (@TEnv.default String).updateContext
                  { aliases := [{ typeArgs := [],
                                  name := "myInt",
                                  type := mty[int]}]} )
      |>.fst |> format

/-- info: some bool -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef?
        mty[BadBoolAlias %p %q]
        ( (@TEnv.default String).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "BadBoolAlias",
                                     type := mty[bool]}]} )
      |>.fst |> format

/-- info: none -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myInt]
                    ( (@TEnv.default String).updateContext
                      { aliases := [{
                         typeArgs := ["a"],
                         name := "myInt",
                         type := mty[int]}] })
      |>.fst |> format

/-- info: some (myDef int) -/
#guard_msgs in
open LTy.Syntax in
#eval LMonoTy.aliasDef? mty[myAlias int bool]
                    ( (@TEnv.default String).updateContext
                      { aliases := [{
                        typeArgs := ["a", "b"],
                        name := "myAlias",
                        type := mty[myDef %a]}] })
      |>.fst |> format

mutual
/--
De-alias `mty`, including at the subtrees.
-/
partial def LMonoTy.resolveAliases [ToFormat IDMeta] (mty : LMonoTy) (Env : TEnv IDMeta) : (Option LMonoTy × TEnv IDMeta) :=
  let (maybe_mty, Env) := LMonoTy.aliasDef? mty Env
  match maybe_mty with
  | some (.tcons name args) =>
    let (args', Env) := LMonoTys.resolveAliases args Env.context.aliases Env
    match args' with
    | none => (some (.tcons name args), Env)
    | some args' => (some (.tcons name args'), Env)
  | some mty' => (some mty', Env)
  | none =>
    match mty with
    | .ftvar _ => (some mty, Env)
    | .bitvec _ => (some mty, Env)
    | .tcons name mtys =>
      let (maybe_mtys, Env) := LMonoTys.resolveAliases mtys Env.context.aliases Env
      match maybe_mtys with
      | none => (none, Env)
      | some mtys' => (some (.tcons name mtys'), Env)

/--
De-alias `mtys`, including at the subtrees.
-/
partial def LMonoTys.resolveAliases [ToFormat IDMeta] (mtys : LMonoTys) (aliases : List TypeAlias) (Env : (TEnv IDMeta)) :
    (Option LMonoTys × (TEnv IDMeta)) :=
    match mtys with
    | [] => (some [], Env)
    | mty :: mrest =>
      let (mty', Env) := LMonoTy.resolveAliases mty Env
      let (mrest', Env) := LMonoTys.resolveAliases mrest aliases Env
      if h : mty'.isSome && mrest'.isSome then
        ((mty'.get (by simp_all) :: mrest'.get (by simp_all)), Env)
      else
        (none, Env)
end

/--
info: De-aliased type: some (Foo $__ty0 (Bar $__ty3 $__ty3))
Subst:
[(p, $__ty3) ($__ty1, (BarAlias $__ty3 $__ty3)) ($__ty0, $__ty3) ($__ty2, $__ty3)]
-/
#guard_msgs in
open LTy.Syntax in
#eval let (ty, Env) := LMonoTy.resolveAliases
        mty[FooAlias %p (BarAlias %p %p)]
        ((@TEnv.default String).updateContext
          { aliases := [{ typeArgs := ["x", "y"],
                                     name := "FooAlias",
                                     type := mty[Foo %x %y]},
                                   { typeArgs := ["a", "b"],
                                     name := "BarAlias",
                                     type := mty[Bar %a %b]
                                   }
                                  ]})
      format f!"De-aliased type: {ty}\n\
                Subst:\n{Env.stateSubstInfo.subst}"

/--
Instantiate and de-alias `ty`, including at the subtrees.
-/
def LTy.resolveAliases [ToFormat IDMeta] (ty : LTy) (Env : TEnv IDMeta) : Option LMonoTy × TEnv IDMeta :=
  let (mty, Env') := ty.instantiate Env.genEnv
  let Env := {Env with genEnv := Env'}
  LMonoTy.resolveAliases mty Env

/-- info: some (arrow bool $__ty0) -/
#guard_msgs in
open LTy.Syntax in
#eval LTy.resolveAliases
        t[∀x. (FooAlias %x %x) → %x]
        ((@TEnv.default String).updateContext { aliases := [{
                                        typeArgs := ["x", "y"],
                                        name := "FooAlias",
                                        type := mty[bool]}]} )
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
    (ks.contains { name := name, metadata := args.length }) &&
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

def isInstanceOfKnownType (ty : LMonoTy) (C : LContext IDMeta) : Bool :=
  LMonoTy.knownInstance ty C.knownTypes

/--
Instantiate `mty` by replacing all free type variables with fresh ones, and then
perform resolution of type aliases and subsequent checks for registered types.
-/
def LMonoTy.instantiateWithCheck (mty : LMonoTy) (C: LContext T) (Env : TEnv T.IDMeta) :
    Except Format (LMonoTy × (TEnv T.IDMeta)) := do
  let ftvs := mty.freeVars
  let (mtys, Env) := LMonoTys.instantiateEnv ftvs [mty] Env
  let mtyi := mtys[0]!
  let (mtyi, Env) := match mtyi.resolveAliases Env with
                  | (some ty', Env) => (ty', Env)
                  | (none, Env) => (mtyi, Env)
  if isInstanceOfKnownType mtyi C
  then return (mtyi, Env)
  else .error f!"Type {mty} is not an instance of a previously registered type!\n\
                 Known Types: {C.knownTypes}"

/--
Instantiate `ty`, with resolution of type aliases to type definitions and checks
for registered types.
-/
def LTy.instantiateWithCheck [ToFormat T.IDMeta] (ty : LTy) (C: LContext T) (Env : TEnv T.IDMeta) : Except Format (LMonoTy × TEnv T.IDMeta) := do
  let (mty, Env) := match ty.resolveAliases Env with
                  | (some ty', Env) => (ty', Env)
                  | (none, Env) =>
                    let (ty, Env') := ty.instantiate Env.genEnv
                    (ty, {Env with genEnv := Env'})
  if isInstanceOfKnownType mty C
  then return (mty, Env)
  else .error f!"Type {ty} is not an instance of a previously registered type!\n\
                 Known Types: {C.knownTypes}"

section

open LTy.Syntax

/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[myTy (myTy)]
                            { @LContext.default ⟨Unit, String⟩ with
                                knownTypes := makeKnownTypes [LTy.toKnownType! t[∀a. myTy %a],
                                               LTy.toKnownType! t[int]] }

abbrev TTyDefault: LExprParams := {Metadata := Unit, IDMeta := TyIdentifier}
/-- info: false -/
#guard_msgs in
#eval isInstanceOfKnownType mty[Foo] (@LContext.default TTyDefault)

/--
info: error: Type (arrow int Foo) is not an instance of a previously registered type!
Known Types: [∀[0, 1]. (arrow 0 1), string, int, bool]
-/
#guard_msgs in
#eval do let ans ← t[int → Foo].instantiateWithCheck (@LContext.default TTyDefault) (@TEnv.default TyIdentifier)
         return format ans

/-- info: ok: (arrow int bool) -/
#guard_msgs in
#eval do let ans ← t[int → bool].instantiateWithCheck (@LContext.default TTyDefault) (@TEnv.default TyIdentifier)
         return format ans.fst
end

/--
Instantiate the scheme `ty` and apply the global substitution `Env.state.subst` to
it.
-/
def LTy.instantiateAndSubst (ty : LTy) (C: LContext T) (Env : TEnv T.IDMeta) : Except Format (LMonoTy × TEnv T.IDMeta) := do
  let (mty, Env) ← LTy.instantiateWithCheck ty C Env
  let mty := LMonoTy.subst Env.stateSubstInfo.subst mty
  return (mty, Env)

def LTy.instantiateAndSubsts (tys : List LTy) (C: LContext T) (Env : TEnv T.IDMeta) :
  Except Format (List LMonoTy × TEnv T.IDMeta) := do
  match tys with
  | [] => return ([], Env)
  | ty :: tyrest =>
    let (mty, Env) ← LTy.instantiateAndSubst ty C Env
    let (mtyrest, Env) ← LTy.instantiateAndSubsts tyrest C Env
    return ((mty :: mtyrest), Env)

/--
Get the monotype of variable corresponding to identifier `x` by instantiating
the type and then applying the global substitution.
-/
def Identifier.instantiateAndSubst (x : T.Identifier) (C: LContext T) (Env : TEnv T.IDMeta) :
  Except Format (Option (LMonoTy × TEnv T.IDMeta)) := do
  match Env.context.types.find? x with
  | some ty => LTy.instantiateAndSubst ty C Env
  | none => return none

def Identifier.instantiateAndSubsts (xs : List T.Identifier) (C: LContext T)  (Env :TEnv T.IDMeta) :
  Except Format (Option (List LMonoTy × (TEnv T.IDMeta))) := do
  match xs with
  | [] => return some ([], Env)
  | x :: xrest =>
    let ans ← instantiateAndSubst x C Env
    match ans with
    | none => return none
    | some (xty, Env) =>
      let ans ← Identifier.instantiateAndSubsts xrest C Env
      match ans with
      | none => return none
      | some (xtys, Env) => return ((xty :: xtys), Env)

/-- info: (arrow $__ty0 b) -/
#guard_msgs in
open LTy.Syntax in
#eval format $ (LTy.instantiate t[∀a. %a → %b] (@TGenEnv.default String)).fst

/--
Instantiate the scheme `∀tyArgs. s` by _consistently_ filling in fresh type
variables for all the variables bound by the universal quantifier.

E.g., the instantiation of `∀a. (x : a) (y : int) (z : a)` must be something
like `(x : _ty0) (y : int) (z : _ty0)`, and not `(x : _ty0) (y : int) (z : _ty1)`.
-/
def LMonoTySignature.instantiate (C: LContext T)  (Env : TEnv T.IDMeta) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature T.IDMeta) :
  Except Format ((@LMonoTySignature T.IDMeta) × TEnv T.IDMeta) := do
  let (mtys, Env) := LMonoTys.instantiateEnv tyArgs sig.values Env
  let tys := mtys.map (fun mty => (LTy.forAll [] mty))
  let (newtys, Env) ← go Env tys
  .ok ((sig.keys.zip newtys), Env)
  where go (Env : TEnv T.IDMeta) (tys : LTys) : Except Format (LMonoTys × TEnv T.IDMeta) :=
    match tys with
    | [] => .ok ([], Env)
    | t :: trest => do
      let (mt, Env) ← LTy.instantiateWithCheck t C Env
      let (mtrest, Env) ← go Env trest
      .ok (mt :: mtrest, Env)

/--
info: ok: (x : $__ty0) (y : int) (z : $__ty0)
-/
#guard_msgs in
open LTy.Syntax in
#eval do let ans ← (LMonoTySignature.instantiate (@LContext.default {Metadata := Unit, IDMeta := Unit})
                    ((@TEnv.default Unit).updateContext
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
def LMonoTySignature.toTrivialLTy (s : @LMonoTySignature IDMeta) : @LTySignature IDMeta :=
  s.map (fun (x, ty) => (x, .forAll [] ty))

/--
Generate fresh type variables only for unannotated identifiers in `ids`,
retaining any pre-existing type annotations.
-/
def TEnv.maybeGenMonoTypes [ToFormat IDMeta] (Env : TEnv IDMeta) (ids : IdentTs LMonoTy IDMeta) : List LMonoTy × TEnv IDMeta :=
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
def TEnv.addInOldestContext [ToFormat IDMeta] [DecidableEq IDMeta] (fvs : IdentTs LMonoTy IDMeta) (Env : TEnv IDMeta) : TEnv IDMeta :=
  let (monotys, Env) := maybeGenMonoTypes Env fvs
  let tys := monotys.map (fun mty => LTy.forAll [] mty)
  let types := Env.context.types.addInOldest fvs.idents tys
  Env.updateContext { Env.genEnv.context with types := types }

/--
Add a well-formed `alias` to the context, where the type definition is first
de-aliased.
-/
def TEnv.addTypeAlias (alias : TypeAlias) (C: LContext T) (Env : TEnv T.IDMeta) : Except Format (TEnv T.IDMeta) := do
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
  else if C.knownTypes.containsName alias.name then
    .error f!"This type declaration's name is reserved!\n\
              {alias}\n\
              KnownTypes' names:\n\
              {C.knownTypes.keywords}"
  else
    let (mtys, Env) := LMonoTys.instantiateEnv alias.typeArgs [alias_lty.toMonoTypeUnsafe, alias.type] Env
    match mtys with
    | [lhs, rhs] =>
      let newTyArgs := lhs.freeVars
      -- We expect `alias.type` to be a known, legal type, hence the use of
      -- `instantiateWithCheck` below. Note that we only store type
      -- declarations -- not synonyms -- as values in the alias table;
      -- i.e., we don't store a type alias mapped to another type alias.
      let (rhsmty, _) ← (LTy.forAll [] rhs).instantiateWithCheck C Env
      let new_aliases := { typeArgs := newTyArgs,
                           name := alias.name,
                           type := rhsmty } :: Env.context.aliases
      let context := { Env.context with aliases := new_aliases }
      .ok (Env.updateContext context)
    | _ => .error f!"[TEnv.addTypeAlias] Implementation error! \n\
                      {alias}"

---------------------------------------------------------------------

end Lambda

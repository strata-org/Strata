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
open Strata

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

/-- A type alias is well-formed when every free variable in its body appears
    in its list of type arguments. -/
def TypeAlias.WF (a : TypeAlias) : Prop :=
  ∀ tv, tv ∈ LMonoTy.freeVars a.type → tv ∈ a.typeArgs

mutual
/-- Replace free type variables in `mty` according to a positional mapping
    from `vars` to `vals`. Variables not in `vars` are unchanged. -/
def LMonoTy.openVars (vars : List TyIdentifier) (vals : LMonoTys) (mty : LMonoTy) : LMonoTy :=
  match mty with
  | .ftvar x =>
    match List.zip vars vals |>.find? (fun p => p.1 == x) with
    | some (_, v) => v
    | none => .ftvar x
  | .bitvec n => .bitvec n
  | .tcons name args => .tcons name (LMonoTys.openVars vars vals args)

/-- Apply `openVars` to a list of monotypes. -/
def LMonoTys.openVars (vars : List TyIdentifier) (vals : LMonoTys) (mtys : LMonoTys) : LMonoTys :=
  match mtys with
  | [] => []
  | mty :: rest => LMonoTy.openVars vars vals mty :: LMonoTys.openVars vars vals rest
end

/-- Pure alias expansion: substitute `args` for `a.typeArgs` in `a.type`. -/
def TypeAlias.expand (a : TypeAlias) (args : LMonoTys) : LMonoTy :=
  LMonoTy.openVars a.typeArgs args a.type

/-- There exists an alias in `aliases` that expands `tcons name args` to `mty`. -/
def TypeAlias.expandsTo (aliases : List TypeAlias) (name : String) (args : LMonoTys) (mty : LMonoTy) : Prop :=
  ∃ alias ∈ aliases,
    alias.name = name ∧
    alias.typeArgs.length = args.length ∧
    mty = alias.expand args

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

/-- All type aliases in a context are well-formed. -/
def TContext.AliasesWF (Γ : TContext IDMeta) : Prop :=
  ∀ a, a ∈ Γ.aliases → a.WF

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

/-- Fixed prefix for generated type variable names. -/
def TState.tyPrefix : String := "$__ty"

/--
The state of a generator used by typing.
-/
structure TState where
  tyGen : Nat := 0
  exprGen : Nat := 0
  exprPrefix : String := "$__var"
deriving Repr, Inhabited

def TState.init : TState := {}

def TState.incTyGen (state : TState) : TState :=
  { state with tyGen := state.tyGen + 1 }

def TState.genTySym (state : TState) : TyIdentifier × TState :=
  let new_idx := state.tyGen
  let state := state.incTyGen
  let new_var := TState.tyPrefix ++ toString new_idx
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

def KnownTypes.addWithError (ks: KnownTypes) (x: KnownType) (f: DiagnosticModel) : Except DiagnosticModel KnownTypes :=
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
Context data for type checking: a factory of user-specified functions and
data structures for ensuring unique names of types and functions.

This context is typically constant during expression type checking, but may
be extended during statement type checking when local function declarations
(`funcDecl`) add new functions to the factory.

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
def liftGenEnv {α : Type} (f: TGenEnv IDMeta → Except Format (α × TGenEnv IDMeta)) (T: TEnv IDMeta) : Except Format (α × TEnv IDMeta) :=
  match f T.genEnv with
  | .error e => .error e
  | .ok (a, T') => .ok (a, {T with genEnv := T'})

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
    let g := s.genEnv.genState
    f!"context:{Format.line}{s.context}\
       {Format.line}\
       state:{Format.line}\
       tyGen: {g.tyGen}{Format.line}\
       tyPrefix: {TState.tyPrefix}{Format.line}\
       exprGen: {g.exprGen}{Format.line}\
       exprPrefix: {g.exprPrefix}{Format.line}\
       subst: {s.stateSubstInfo.subst}"

instance : ToFormat (LContext T) where
  format s := f!" known types:{Format.line}{s.knownTypes}\n\
                 identifiers:{Format.line}{s.idents}"


def LContext.addKnownTypeWithError (C : LContext T) (k : KnownType) (f: DiagnosticModel) : Except DiagnosticModel (LContext T) := do
  .ok {C with knownTypes := (← C.knownTypes.addWithError k f)}

def LContext.addKnownTypes (C : LContext T) (k : KnownTypes) : Except DiagnosticModel (LContext T) := do
  k.foldM (fun T k n => T.addKnownTypeWithError ⟨k, n⟩ (DiagnosticModel.fromFormat f!"Error: type {k} already known")) C

def LContext.addIdentWithError (C : LContext T) (i: T.Identifier) (f: DiagnosticModel) : Except DiagnosticModel (LContext T) := do
  let i ← C.idents.addWithError i f
  .ok {C with idents := i}

def LContext.addFactoryFunction (C : LContext T) (fn : LFunc T) : LContext T :=
  { C with functions := C.functions.push fn }

def LContext.addFactoryFunctions (C : LContext T) (fact : @Factory T) : LContext T :=
  { C with functions := C.functions.append fact }

/--
Add a mutual block of datatypes `block` to an `LContext` `C`.
This adds all types to `C.datatypes` and `C.knownTypes`,
adds the derived functions (e.g. eliminators, testers),
and performs error checking for name clashes.
-/
def LContext.addMutualBlock [Inhabited T.IDMeta] [Inhabited T.Metadata] [ToFormat T.IDMeta]
  (C: LContext T) (block: MutualDatatype T.IDMeta) : Except DiagnosticModel (LContext T) := do
  -- Check for name clashes with known types
  for d in block do
    if C.knownTypes.containsName d.name then
      throw <| DiagnosticModel.fromFormat f!"Cannot name datatype same as known type!\n{d}\nKnownTypes' names:\n{C.knownTypes.keywords}"
  let ds ← C.datatypes.addMutualBlock block C.knownTypes.keywords
  -- Add factory functions, checking for name clashes
  let f ← genBlockFactory block
  let fs ← C.functions.addFactory f
  -- Add datatype names to knownTypes
  let ks ← block.foldlM (fun ks d => ks.add d.toKnownType) C.knownTypes
  .ok {C with datatypes := ds, functions := fs, knownTypes := ks}

def LContext.addTypeFactory [Inhabited T.IDMeta] [Inhabited T.Metadata] (C: LContext T) (f: @TypeFactory T.IDMeta) : Except DiagnosticModel (LContext T) :=
  f.foldlM (fun C block => C.addMutualBlock block) C

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

/--
Insert each element in `map` in the newest `T.context`.
-/
def TEnv.addInNewestContext (Env : TEnv T.IDMeta) (map : Map T.Identifier LTy) : TEnv T.IDMeta :=
  let ctx := Env.context
  let types := ctx.types.addInNewest map
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
  genVar : TGenEnv IDMeta → Except Format (Identifier IDMeta × TGenEnv IDMeta)
  /-- `genVar` never decreases the type-variable generator counter. -/
  genVar_tyGen_mono : ∀ (Env : TGenEnv IDMeta) (xv : Identifier IDMeta) (Env' : TGenEnv IDMeta),
    genVar Env = .ok (xv, Env') → Env'.genState.tyGen ≥ Env.genState.tyGen
  /-- `genVar` preserves the context. -/
  genVar_context : ∀ (Env : TGenEnv IDMeta) (xv : Identifier IDMeta) (Env' : TGenEnv IDMeta),
    genVar Env = .ok (xv, Env') → Env'.context = Env.context
  /-- `genVar` produces a variable not in knownVars. -/
  genVar_fresh : ∀ (Env : TGenEnv IDMeta) (xv : Identifier IDMeta) (Env' : TGenEnv IDMeta),
    genVar Env = .ok (xv, Env') → xv ∉ TContext.knownVars Env.context

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
def TEnv.genExprVar (Env: TGenEnv Unit) : Except Format (Identifier Unit × TGenEnv Unit) :=
  let (new_var, state) := Env.genState.genExprSym
  let Env :={ Env with genState := state }
  let known_vars := TContext.knownVars Env.context
  if ⟨new_var, ()⟩ ∈ known_vars then
    .error f!"[TEnv.genExprVar] Generated variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    .ok (new_var, Env)

instance : HasGen Unit where
  genVar := TEnv.genExprVar
  genVar_tyGen_mono := by
    intro Env xv Env' h
    simp [TEnv.genExprVar] at h
    split at h
    · simp at h
    · simp at h
      obtain ⟨_, h_env⟩ := h
      rw [← h_env]
      simp [TState.genExprSym, TState.incExprGen]
  genVar_context := by
    intro Env xv Env' h
    simp [TEnv.genExprVar] at h
    split at h
    · simp at h
    · simp at h; obtain ⟨_, h_env⟩ := h; rw [← h_env]
  genVar_fresh := by
    intro Env xv Env' h
    simp [TEnv.genExprVar] at h
    split at h
    · simp at h
    · rename_i h_not_in; simp at h; obtain ⟨h_xv, _⟩ := h; rw [← h_xv]; exact h_not_in

/-- `liftGenEnv` preserves the context. -/
theorem liftGenEnv_context [HasGen IDMeta] [ToFormat IDMeta]
    (Env : TEnv IDMeta) (xv : Identifier IDMeta) (Env' : TEnv IDMeta)
    (h : liftGenEnv HasGen.genVar Env = .ok (xv, Env')) :
    Env'.context = Env.context := by
  simp only [liftGenEnv] at h
  generalize h_gen : HasGen.genVar Env.genEnv = res at h
  match res with
  | .error _ => simp at h
  | .ok (xv_inner, Env_g) =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp [TEnv.context]
    exact HasGen.genVar_context Env.genEnv xv_inner Env_g h_gen

/-- `liftGenEnv HasGen.genVar` produces a fresh variable. -/
theorem liftGenEnv_genVar_fresh [HasGen IDMeta] [ToFormat IDMeta]
    (Env : TEnv IDMeta) (xv : Identifier IDMeta) (Env' : TEnv IDMeta)
    (h : liftGenEnv HasGen.genVar Env = .ok (xv, Env')) :
    xv ∉ TContext.knownVars Env.context := by
  simp only [liftGenEnv] at h
  generalize h_gen : HasGen.genVar Env.genEnv = res at h
  match res with
  | .error _ => simp at h
  | .ok (xv_inner, Env_g) =>
    simp at h; obtain ⟨h_xv, _⟩ := h; rw [← h_xv]
    exact HasGen.genVar_fresh Env.genEnv xv_inner Env_g h_gen

/--
Generate a fresh type variable (`ftvar`).

This function is the canonical way of obtaining fresh type variables. This --
along with the restriction that all `ftvar`s in an annotation are implicitly
universally quantified -- ensures that we always get a fresh type variable when
we use `TEnv.genTyVar`.
-/
def TGenEnv.genTyVar [ToFormat IDMeta] (Env : TGenEnv IDMeta) : Except Format (TyIdentifier × (TGenEnv IDMeta)) :=
  let (new_var, state) := Env.genState.genTySym
  let Env := {Env with genState := state}
  if new_var ∈ Env.context.knownTypeVars then
    .error f!"[TEnv.genTyVar] Generated type variable {new_var} is not fresh!\n\
              Context: {format Env.context}"
  else
    .ok (new_var, Env)

def TEnv.genTyVar [ToFormat IDMeta] (T : TEnv IDMeta) : Except Format (TyIdentifier × (TEnv IDMeta)) :=
  match TGenEnv.genTyVar T.genEnv with
  | .error e => .error e
  | .ok (a, genEnv') => .ok (a, {T with genEnv := genEnv'})

/--
Generate `n` fresh type variables (`ftvar`s).
-/
def TGenEnv.genTyVars [ToFormat IDMeta] (n : Nat) (Env : TGenEnv IDMeta) : Except Format (List TyIdentifier × (TGenEnv IDMeta)) :=
  match n with
  | 0 => .ok ([], Env)
  | n' + 1 => do
    let (ty, Env) ← TGenEnv.genTyVar Env
    let (rest_ty, Env) ← TGenEnv.genTyVars n' Env
    .ok (ty :: rest_ty, Env)

/--
Consistently instantiate type variables `ids` in `mtys`.
-/
def LMonoTys.instantiate [ToFormat IDMeta] (ids : List TyIdentifier) (mtys : LMonoTys) (T : TGenEnv IDMeta) :
  Except Format (LMonoTys × (TGenEnv IDMeta)) := do
  let (freshtvs, T) ← TGenEnv.genTyVars ids.length T
  let S := List.zip ids (List.map (fun tv => (LMonoTy.ftvar tv)) freshtvs)
  .ok (LMonoTys.subst [S] mtys, T)

def LMonoTys.instantiateEnv [ToFormat IDMeta] (ids : List TyIdentifier) (mtys : LMonoTys) (T : (TEnv IDMeta)) :
  Except Format (LMonoTys × (TEnv IDMeta)) :=
  match LMonoTys.instantiate ids mtys T.genEnv with
  | .error e => .error e
  | .ok (a, genEnv') => .ok (a, {T with genEnv := genEnv'})

private theorem LMonoTys.substLogic_length (S : Subst) (mtys : LMonoTys) :
    (LMonoTys.substLogic S mtys).length = mtys.length := by
  induction mtys with
  | nil => simp [substLogic]
  | cons head tail ih => simp [substLogic]; split <;> simp_all

theorem LMonoTys.instantiate_length [ToFormat IDMeta]
    (ids : List TyIdentifier) (mty : LMonoTys) (Env : TGenEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TGenEnv IDMeta)
    (h : LMonoTys.instantiate ids mty Env = .ok (mtys', Env')) :
    mtys'.length = mty.length := by
  simp [instantiate, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · simp at h
    obtain ⟨h1, _⟩ := h
    rw [← h1, LMonoTys.subst_eq_substLogic]
    exact LMonoTys.substLogic_length _ _

theorem LMonoTys.instantiateEnv_length [ToFormat IDMeta]
    (ids : List TyIdentifier) (mty : LMonoTys) (Env : TEnv IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.instantiateEnv ids mty Env = .ok (mtys', Env')) :
    mtys'.length = mty.length := by
  unfold instantiateEnv at h
  generalize h_inst : instantiate ids mty Env.genEnv = result at h
  match result, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨h1, _⟩ := h
    rw [← h1]
    exact LMonoTys.instantiate_length ids mty Env.genEnv a gE h_inst

/--
Instantiate the scheme `ty` by filling in fresh type variables for all
the variables bound by the universal quantifier.

Note: we do not check whether `ty` is a type alias here. See
`LTy.instantiateWithCheck`, which incorporates this check (using
`LTy.resolveAliases`) as well as verifies whether the type is a previously registered
one.
-/
def LTy.instantiate [ToFormat IDMeta] (ty : LTy) (Env : TGenEnv IDMeta) : Except Format (LMonoTy × (TGenEnv IDMeta)) :=
  match ty with
  | .forAll [] mty' => .ok (mty', Env)
  | .forAll xs lty' => do
    let (freshtvs, Env) ← TGenEnv.genTyVars xs.length Env
    let S := List.zip xs (List.map (fun tv => (.ftvar tv)) freshtvs)
    .ok (LMonoTy.subst [S] lty', Env)

instance : Inhabited (Option LMonoTy × TEnv IDMeta) where
  default := (none, TEnv.default)

/--
Return the instantiated definition of `.tcons name args` if it is a registered
type alias.

This function does not descend into the subtrees of types in `args`, nor does it
check whether the de-aliased types are registered/known.
-/
def LMonoTy.tconsAlias [ToFormat IDMeta] (name : String) (args : LMonoTys)
    (Env : TEnv IDMeta) : Except Format (LMonoTy × TEnv IDMeta) := do
  let inputMty := .tcons name args
  -- Look for a matching alias with same name and arity.
  let matchingAlias := Env.context.aliases.find?
                        (fun a => a.name == name && a.typeArgs.length == args.length)
  match matchingAlias with
  | none => return (inputMty, Env)
  | some alias =>
    -- Create instantiation pair: [alias pattern, alias definition].
    -- The alias pattern and definition share the same type variables here.
    let aliasPattern := .tcons name (alias.typeArgs.map .ftvar)
    let typesToInstantiate := [aliasPattern, alias.type]
    -- Instantiate both types with fresh variables.
    match h_inst : LMonoTys.instantiateEnv alias.typeArgs typesToInstantiate Env with
    | .error e => .error e
    | .ok (instantiatedTypes, updatedEnv) =>
    -- Extract the instantiated pattern and definition using getD to avoid
    -- dependent indexing in proofs. The default is never used since
    -- instantiateEnv preserves length (output has 2 elements).
    let instantiatedPattern := instantiatedTypes.getD 0 inputMty
    let instantiatedDefinition := instantiatedTypes.getD 1 inputMty
    -- Unify the input type with the instantiated alias pattern.
    match Constraints.unify [(inputMty, instantiatedPattern)] updatedEnv.stateSubstInfo with
    | .error e =>
      -- We don't expect this unification to fail; after all,
      -- `instantiatedPattern` is more general than `.tcons name args`.
      .error f!"🚨 Implementation error: \
                 Unification failed in LMonoTy.tconsAlias: {e}"
    | .ok substInfo =>
      -- Apply the substitution to get the final definition.
      let finalDefinition := instantiatedDefinition.subst substInfo.subst
      return (finalDefinition, updatedEnv.updateSubst substInfo)

/--
Return the instantiated definition of `mty` if it is a registered
type alias.

This function does not descend into any subtrees of types in `args`, nor does it
check whether the de-aliased types are registered/known.
-/
def LMonoTy.aliasDef? [ToFormat IDMeta] (mty : LMonoTy) (Env : TEnv IDMeta)
    : Except Format (LMonoTy × TEnv IDMeta) := do
  match mty with
  | .tcons name args => LMonoTy.tconsAlias name args Env
  | .bitvec _ | .ftvar _ => return (mty, Env)

mutual
/--
De-alias `mty`, including at the subtrees.
-/
def LMonoTy.resolveAliases [ToFormat IDMeta] (mty : LMonoTy) (Env : TEnv IDMeta) :
    Except Format (LMonoTy × TEnv IDMeta) := do
  match mty with
  | .ftvar _ =>
    -- Free variables cannot be type aliases (would unify with every type).
    return (mty, Env)
  | .bitvec _ =>
    -- Bitvectors cannot be type aliases.
    return (mty, Env)
  | .tcons name args =>
    let (args', Env) ← LMonoTys.resolveAliases args Env
    let (mty', Env) ← LMonoTy.tconsAlias name args' Env
    return (mty', Env)

/--
De-alias `mtys`, including at the subtrees.
-/
def LMonoTys.resolveAliases [ToFormat IDMeta] (mtys : LMonoTys)
    (Env : (TEnv IDMeta)) : Except Format (LMonoTys × (TEnv IDMeta)) := do
  match mtys with
  | [] => return ([], Env)
  | mty :: mrest =>
    let (mty', Env) ← LMonoTy.resolveAliases mty Env
    let (mrest', Env) ← LMonoTys.resolveAliases mrest Env
    return (mty' :: mrest', Env)
end

/--
Resolve type aliases in a list of constructors.
-/
def LConstrs.resolveAliases [ToFormat IDMeta]
    (constrs : List (LConstr IDMeta)) (Env : TEnv IDMeta) :
    Except Format (List (LConstr IDMeta) × TEnv IDMeta) := do
  constrs.foldrM (fun c (acc, Env) => do
    let (args', Env) ← go c.args Env
    return ({ c with args := args' } :: acc, Env)) ([], Env)
  where go args Env := do
    let names := args.map (·.fst)
    let tys := args.map (·.snd)
    let (tys', Env) ← LMonoTys.resolveAliases tys Env
    let args' := names.zip tys'
    return (args', Env)

theorem LConstrs.resolveAliases_length [ToFormat IDMeta]
  (constrs : List (LConstr IDMeta)) (Env : TEnv IDMeta)
  (result : List (LConstr IDMeta) × TEnv IDMeta)
  (h : LConstrs.resolveAliases constrs Env = .ok result) :
  result.fst.length = constrs.length := by
  simp only [LConstrs.resolveAliases] at h
  induction constrs generalizing result with
  | nil => simp_all [List.foldrM, pure, Except.pure]; grind
  | cons hd tl ih =>
    simp [List.foldrM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure] at h ih
    split at h
    case h_1 => simp_all
    case h_2 x v heq =>
      have ih' := @ih v.fst v.snd heq
      grind

/--
Resolve type aliases in constructor argument types within a mutual datatype block.
-/
def MutualDatatype.resolveAliases [ToFormat IDMeta] (block : MutualDatatype IDMeta) (Env : TEnv IDMeta) :
    Except Format (MutualDatatype IDMeta × TEnv IDMeta) := do
  block.foldrM (fun d (acc, Env) =>
    match h: LConstrs.resolveAliases d.constrs Env with
    | .error e => .error e
    | .ok (constrs', Env) =>
      have h : constrs'.length != 0 := by
        rename_i E
        have Hlen := LConstrs.resolveAliases_length d.constrs E
        rw[h] at Hlen
        cases d; grind
      return ({ d with constrs := constrs', constrs_ne := h } :: acc, Env)) ([], Env)

/--
Instantiate and de-alias `ty`, including at the subtrees.
-/
def LTy.resolveAliases [ToFormat IDMeta] (ty : LTy) (Env : TEnv IDMeta) :
    Except Format (LMonoTy × TEnv IDMeta) := do
  let (mty, genEnv') ← ty.instantiate Env.genEnv
  let Env := {Env with genEnv := genEnv'}
  LMonoTy.resolveAliases mty Env

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

/-- Check whether a type variable name looks like a generated name (`tyPrefix ++ toString n`)
    with `n ≥ tyGen`. Returns `true` if the name is a "future" generated name that should
    not appear in a type at this point. -/
def TState.isFutureGenVar (state : TState) (v : TyIdentifier) : Bool :=
  if v.startsWith TState.tyPrefix then
    match (v.drop TState.tyPrefix.length).toNat? with
    | some n => n >= state.tyGen
    | none => false
  else false

/-- Check that no free variable in `mty` is a future generated name. -/
def LMonoTy.checkNoFutureGenVars (mty : LMonoTy) (state : TState) : Bool :=
  mty.freeVars.all (fun v => !state.isFutureGenVar v)

/--
Instantiate `mty` by replacing all free type variables with fresh ones, and then
perform resolution of type aliases and subsequent checks for registered types.
-/
def LMonoTy.instantiateWithCheck (mty : LMonoTy) (C: LContext T) (Env : TEnv T.IDMeta) :
    Except Format (LMonoTy × (TEnv T.IDMeta)) := do
  let ftvs := mty.freeVars
  match h_inst : LMonoTys.instantiateEnv ftvs [mty] Env with
  | .error e => .error e
  | .ok (instTypes, Env) =>
  have : 0 < instTypes.length := by
    have := LMonoTys.instantiateEnv_length _ _ _ _ _ h_inst; simp at this; omega
  let mtyi := instTypes[0]'(by omega)
  let (mtyi, Env) ← mtyi.resolveAliases Env
  if !LMonoTy.checkNoFutureGenVars mtyi Env.genEnv.genState then
    .error f!"Type {mtyi} contains a type variable that collides with the \
              generator namespace ({TState.tyPrefix}*). This is not allowed."
  else if isInstanceOfKnownType mtyi C
  then return (mtyi, Env)
  else .error f!"Type {mty} is not an instance of a previously registered type!\n\
                 Known Types: {C.knownTypes}"

/--
Instantiate `ty`, with resolution of type aliases to type definitions and checks
for registered types.
-/
def LTy.instantiateWithCheck [ToFormat T.IDMeta] (ty : LTy) (C: LContext T) (Env : TEnv T.IDMeta) :
    Except Format (LMonoTy × TEnv T.IDMeta) := do
  let (mty, Env) ← ty.resolveAliases Env
  if !LMonoTy.checkNoFutureGenVars mty Env.genEnv.genState then
    .error f!"Type {mty} contains a type variable that collides with the \
              generator namespace ({TState.tyPrefix}*). This is not allowed."
  else if isInstanceOfKnownType mty C
  then return (mty, Env)
  else .error f!"Type {ty} is not an instance of a previously registered type!\n\
                 Known Types: {C.knownTypes}"

/--
Instantiate the scheme `ty` and apply the global substitution `Env.state.subst` to
it.
-/
def LTy.instantiateAndSubst (ty : LTy) (C: LContext T) (Env : TEnv T.IDMeta)
    : Except Format (LMonoTy × TEnv T.IDMeta) := do
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

/--
Instantiate the scheme `∀tyArgs. s` by _consistently_ filling in fresh type
variables for all the variables bound by the universal quantifier.

E.g., the instantiation of `∀a. (x : a) (y : int) (z : a)` must be something
like `(x : _ty0) (y : int) (z : _ty0)`, and not `(x : _ty0) (y : int) (z : _ty1)`.
-/
def LMonoTySignature.instantiate (C: LContext T)  (Env : TEnv T.IDMeta) (tyArgs : List TyIdentifier) (sig : @LMonoTySignature T.IDMeta) :
  Except Format ((@LMonoTySignature T.IDMeta) × TEnv T.IDMeta) := do
  let (mtys, Env) ← LMonoTys.instantiateEnv tyArgs sig.values Env
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
Trivial conversion of a `MonoTySignature` to a `TySignature`, with an empty list
of universally quantified type variables.
-/
def LMonoTySignature.toTrivialLTy (s : @LMonoTySignature IDMeta) : @LTySignature IDMeta :=
  s.map (fun (x, ty) => (x, .forAll [] ty))

/--
Generate fresh type variables only for unannotated identifiers in `ids`,
retaining any pre-existing type annotations.
-/
def TEnv.maybeGenMonoTypes [ToFormat IDMeta] (Env : TEnv IDMeta) (ids : IdentTs LMonoTy IDMeta) : Except Format (List LMonoTy × TEnv IDMeta) :=
  match ids with
  | [] => .ok ([], Env)
  | (_x, ty) :: irest =>
    match ty with
    | none => do
      let (xty_id, Env) ← TEnv.genTyVar Env
      let xty := .ftvar xty_id
      let (ans, Env) ← maybeGenMonoTypes Env irest
      .ok (xty :: ans, Env)
    | some xty => do
      let (ans, Env) ← maybeGenMonoTypes Env irest
      .ok (xty :: ans, Env)

/--
Insert `fvi` (where `fvi` is the `i`-th element of `fvs`) in the oldest context
in `Env`, only if `fvi` doesn't already exist in some context in `Env`.

If `fvi` has no type annotation, a fresh type variable is put in the context.
-/
def TEnv.addInOldestContext [ToFormat IDMeta] [DecidableEq IDMeta] (fvs : IdentTs LMonoTy IDMeta) (Env : TEnv IDMeta) : Except Format (TEnv IDMeta) := do
  let (monotys, Env) ← maybeGenMonoTypes Env fvs
  let tys := monotys.map (fun mty => LTy.forAll [] mty)
  let types := Env.context.types.addInOldest fvs.idents tys
  return Env.updateContext { Env.genEnv.context with types := types }

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
    let (mtys, Env) ← LMonoTys.instantiateEnv alias.typeArgs [alias_lty.toMonoTypeUnsafe, alias.type] Env
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

/-! ### Context preservation and freshness lemmas -/

/--
`genTyVar` preserves the context.

Now that `genTyVar` returns `Except Format` (instead of using `panic`),
we can prove this as a theorem: the error branch never produces an
environment, and the success branch only updates `genState`.
-/
theorem TGenEnv.genTyVar_context {IDMeta : Type} [ToFormat IDMeta]
    (Env : TGenEnv IDMeta) (tv : TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVar Env = .ok (tv, Env')) :
    Env'.context = Env.context := by
  simp [TGenEnv.genTyVar] at h
  split at h
  · simp at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]

/-- `genTyVars` preserves the context (by induction, using `genTyVar_context`). -/
theorem TGenEnv.genTyVars_context {IDMeta : Type} [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    Env'.context = Env.context := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
  | succ n ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_gen
      obtain ⟨tv, Env1⟩ := v1; simp at h h_gen
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨tvs', Env2⟩ := v2; simp at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        rw [ih Env1 tvs' Env2 h_rest, TGenEnv.genTyVar_context Env tv Env1 h_gen]

/-- If `Map.find?` returns `ty`, then `freeVars ty ⊆ go m` (the per-map free var collector). -/
private theorem go_knownTypeVars_of_find {T : LExprParams} [DecidableEq T.IDMeta]
    {m : Map (Identifier T.IDMeta) LTy} {x : T.Identifier} {ty : LTy} {tx : TyIdentifier}
    (h_find : Map.find? m x = some ty) (h_mem : tx ∈ LTy.freeVars ty) :
    tx ∈ TContext.types.knownTypeVars.go m := by
  induction m with
  | nil => simp [Map.find?] at h_find
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    simp only [TContext.types.knownTypeVars.go, List.mem_append]
    simp only [Map.find?] at h_find
    split at h_find
    · -- a = x, so b = ty
      left; simp at h_find; rw [h_find]; exact h_mem
    · -- a ≠ x, recurse
      right; exact ih h_find

/-- If `Maps.find?` returns `ty`, then `freeVars ty ⊆ types.knownTypeVars`. -/
private theorem types_knownTypeVars_of_find {T : LExprParams} [DecidableEq T.IDMeta]
    {types : Maps (Identifier T.IDMeta) LTy} {x : T.Identifier} {ty : LTy} {tx : TyIdentifier}
    (h_find : Maps.find? types x = some ty) (h_mem : tx ∈ LTy.freeVars ty) :
    tx ∈ TContext.types.knownTypeVars types := by
  induction types with
  | nil => simp [Maps.find?] at h_find
  | cons m rest ih =>
    simp only [TContext.types.knownTypeVars, List.mem_append]
    cases h_map : Map.find? m x with
    | some v =>
      have h_eq : Maps.find? (m :: rest) x = some v := by
        simp [Maps.find?, h_map]
      rw [h_eq] at h_find
      have := Option.some.inj h_find; subst this
      left; exact go_knownTypeVars_of_find h_map h_mem
    | none =>
      have h_eq : Maps.find? (m :: rest) x = Maps.find? rest x := by
        simp [Maps.find?, h_map]
      rw [h_eq] at h_find
      right; exact ih h_find

/-- If `find?` returns a type `ty` from the context, then `freeVars ty ⊆ knownTypeVars`. -/
theorem TContext.mem_knownTypeVars_of_find {T : LExprParams} [DecidableEq T.IDMeta]
    {Γ : TContext T.IDMeta} {x : T.Identifier} {ty : LTy} {tx : TyIdentifier}
    (h_find : Γ.types.find? x = some ty) (h_mem : tx ∈ LTy.freeVars ty) :
    tx ∈ TContext.knownTypeVars Γ := by
  exact types_knownTypeVars_of_find h_find h_mem

/-- `go` is monotone under map append: appending entries to a map only grows `go`. -/
theorem knownTypeVars_go_append_superset
    {IDMeta : Type} (m extra : Map (Identifier IDMeta) LTy) :
    ∀ v, v ∈ TContext.types.knownTypeVars.go m →
      v ∈ TContext.types.knownTypeVars.go (m ++ extra) := by
  induction m with
  | nil => intro v h; simp [TContext.types.knownTypeVars.go] at h
  | cons p m' ih =>
    intro v h
    obtain ⟨a, b⟩ := p
    simp only [TContext.types.knownTypeVars.go, List.mem_append] at h
    unfold Map at *
    simp only [List.cons_append, TContext.types.knownTypeVars.go, List.mem_append]
    rcases h with h_fv | h_rest
    · left; exact h_fv
    · right; exact ih v h_rest

/-- `knownTypeVars` is monotone: adding types to the context only grows it. -/
theorem TContext.knownTypeVars_addInNewest_superset
    {IDMeta : Type} (types : Maps (Identifier IDMeta) LTy) (x : Identifier IDMeta) (ty : LTy) :
    ∀ v, v ∈ TContext.types.knownTypeVars types →
      v ∈ TContext.types.knownTypeVars (Maps.addInNewest types [(x, ty)]) := by
  cases types with
  | nil => intro v h; simp [TContext.types.knownTypeVars] at h
  | cons m rest =>
    intro v h
    simp only [Maps.addInNewest, Maps.newest, Maps.pop, Maps.push]
    simp only [TContext.types.knownTypeVars, List.mem_append] at h ⊢
    rcases h with h_go | h_rest
    · left; exact knownTypeVars_go_append_superset m [(x, ty)] v h_go
    · right; exact h_rest

/-- If `tx ∉ knownTypeVars Γ`, then `tx` is fresh w.r.t. `Γ`. -/
theorem TContext.isFresh_of_not_mem_knownTypeVars {T : LExprParams} [DecidableEq T.IDMeta]
    {tx : TyIdentifier} {Γ : TContext T.IDMeta}
    (h : tx ∉ TContext.knownTypeVars Γ) :
    TContext.isFresh tx Γ := by
  intro x ty h_find h_mem
  exact h (TContext.mem_knownTypeVars_of_find h_find h_mem)

/-- `genTyVar` produces a type variable that is fresh in the context. -/
theorem TGenEnv.genTyVar_isFresh {T : LExprParams} [DecidableEq T.IDMeta]
    [ToFormat T.IDMeta]
    (Env : TGenEnv T.IDMeta) (tv : TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVar Env = .ok (tv, Env')) :
    TContext.isFresh (T := T) tv Env.context := by
  simp [TGenEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i h_not_in
    simp at h
    obtain ⟨h_tv, _⟩ := h; subst h_tv
    exact TContext.isFresh_of_not_mem_knownTypeVars h_not_in

/-- `TEnv.genTyVar` produces a type variable that is fresh in the context. -/
theorem TEnv.genTyVar_isFresh {T : LExprParams} [DecidableEq T.IDMeta]
    [ToFormat T.IDMeta]
    (Env : TEnv T.IDMeta) (tv : TyIdentifier) (Env' : TEnv T.IDMeta)
    (h : TEnv.genTyVar Env = .ok (tv, Env')) :
    TContext.isFresh tv Env.context := by
  simp [TEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i v h_gen; simp at h; obtain ⟨h_tv, _⟩ := h; subst h_tv
    exact TGenEnv.genTyVar_isFresh Env.genEnv _ v h_gen

/-- `TEnv.genTyVar` preserves the context. -/
theorem TEnv.genTyVar_context {T : LExprParams} [DecidableEq T.IDMeta]
    [ToFormat T.IDMeta]
    (Env : TEnv T.IDMeta) (tv : TyIdentifier) (Env' : TEnv T.IDMeta)
    (h : TEnv.genTyVar Env = .ok (tv, Env')) :
    Env'.context = Env.context := by
  simp [TEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i v h_gen; simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]
    exact TGenEnv.genTyVar_context Env.genEnv _ v h_gen

/-- `TEnv.genTyVar` preserves the substitution. -/
theorem TEnv.genTyVar_subst {T : LExprParams} [DecidableEq T.IDMeta]
    [ToFormat T.IDMeta]
    (Env : TEnv T.IDMeta) (tv : TyIdentifier) (Env' : TEnv T.IDMeta)
    (h : TEnv.genTyVar Env = .ok (tv, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp [TEnv.genTyVar] at h
  split at h
  · simp at h
  · simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]

/-- `genTyVar` produces a variable not in `knownTypeVars`. -/
theorem TGenEnv.genTyVar_not_mem_knownTypeVars [ToFormat IDMeta]
    (Env : TGenEnv IDMeta) (tv : TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVar Env = .ok (tv, Env')) :
    tv ∉ TContext.knownTypeVars Env.context := by
  simp [TGenEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i h_not_in; simp at h; obtain ⟨h_tv, _⟩ := h; subst h_tv; exact h_not_in

/-- `genTyVars` produces variables each not in `knownTypeVars` of the initial environment. -/
theorem TGenEnv.genTyVars_not_mem_knownTypeVars [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    ∀ tv, tv ∈ tvs → tv ∉ TContext.knownTypeVars Env.context := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨h1, _⟩ := h; subst h1
    intro tv hm; exact absurd hm List.not_mem_nil
  | succ n ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_gen1
      obtain ⟨hd, Env1⟩ := v1; simp at h h_gen1
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨tl, Env2⟩ := v2; simp at h
        obtain ⟨h_tvs, _⟩ := h; subst h_tvs
        have h_ctx := TGenEnv.genTyVar_context Env hd Env1 h_gen1
        have h_hd_not := TGenEnv.genTyVar_not_mem_knownTypeVars Env hd Env1 h_gen1
        have h_tl_not := ih Env1 tl Env2 h_rest
        intro tv h_mem
        cases List.mem_cons.mp h_mem with
        | inl h_eq => subst h_eq; exact h_hd_not
        | inr h_rest_mem => rw [h_ctx] at h_tl_not; exact h_tl_not tv h_rest_mem

/-- `genTyVars n` produces exactly `n` fresh type variables. -/
theorem TGenEnv.genTyVars_length {IDMeta : Type} [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    tvs.length = n := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨h1, _⟩ := h; subst h1; simp
  | succ n ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_gen
      obtain ⟨tv, Env1⟩ := v1; simp at h h_gen
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨tvs', Env2⟩ := v2; simp at h
        obtain ⟨h1, _⟩ := h; subst h1
        simp [ih Env1 tvs' Env2 h_rest]

/-- All type variables produced by `genTyVars` are fresh in the context. -/
theorem TGenEnv.genTyVars_allFresh {T : LExprParams} [DecidableEq T.IDMeta]
    [ToFormat T.IDMeta]
    (n : Nat) (Env : TGenEnv T.IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv T.IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    ∀ tv, tv ∈ tvs → TContext.isFresh (T := T) tv Env.context := by
  intro tv h_mem
  exact TContext.isFresh_of_not_mem_knownTypeVars
    (TGenEnv.genTyVars_not_mem_knownTypeVars n Env tvs Env' h tv h_mem)

---------------------------------------------------------------------
-- tyGen monotonicity lemmas
---------------------------------------------------------------------

section TyGenMono

-- These lemmas don't need [ToFormat T.Metadata]; omit it so callers
-- (e.g. in LExprTypeSpec.lean) don't need to provide it.
omit [ToFormat T.Metadata]

/-- `genTyVar` produces `TState.tyPrefix ++ toString tyGen`. -/
theorem genTyVar_name_eq (Env : TEnv T.IDMeta) (tv : TyIdentifier) (Env' : TEnv T.IDMeta)
    (h : TEnv.genTyVar Env = .ok (tv, Env')) :
    tv = TState.tyPrefix ++ toString Env.genEnv.genState.tyGen := by
  -- Step 1: Decompose TEnv.genTyVar into TGenEnv.genTyVar
  simp only [TEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i v h_gen_env
    obtain ⟨a, genEnv'⟩ := v
    simp at h; rw [← h.1]
    -- Step 2: Decompose TGenEnv.genTyVar: it returns genTySym's name
    simp only [TGenEnv.genTyVar] at h_gen_env
    split at h_gen_env
    · simp at h_gen_env
    · simp at h_gen_env; rw [← h_gen_env.1]
      -- Step 3: genTySym.1 = tyPrefix ++ toString tyGen
      simp [TState.genTySym, TState.incTyGen]

/-- `genTyVar` increments `tyGen` by exactly 1. -/
theorem genTyVar_tyGen (Env : TEnv T.IDMeta) (tv : TyIdentifier) (Env' : TEnv T.IDMeta)
    (h : TEnv.genTyVar Env = .ok (tv, Env')) :
    Env'.genEnv.genState.tyGen = Env.genEnv.genState.tyGen + 1 := by
  -- Step 1: Decompose TEnv.genTyVar into TGenEnv.genTyVar
  simp only [TEnv.genTyVar] at h
  split at h
  · simp at h
  · rename_i v h_gen_env
    obtain ⟨a, genEnv'⟩ := v
    simp at h; rw [← h.2]
    -- Step 2: Decompose TGenEnv.genTyVar
    simp only [TGenEnv.genTyVar] at h_gen_env
    split at h_gen_env
    · simp at h_gen_env
    · simp at h_gen_env; rw [← h_gen_env.2.2]
      -- Step 3: genTySym increments tyGen by 1
      simp [TState.genTySym, TState.incTyGen]

/-- `genTyVars n` never decreases `tyGen`. -/
theorem genTyVars_tyGen_mono [ToFormat IDMeta]
    (n : Nat) (Env : TGenEnv IDMeta)
    (tvs : List TyIdentifier) (Env' : TGenEnv IDMeta)
    (h : TGenEnv.genTyVars n Env = .ok (tvs, Env')) :
    Env'.genState.tyGen ≥ Env.genState.tyGen := by
  induction n generalizing Env tvs Env' with
  | zero =>
    simp [TGenEnv.genTyVars] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | succ n ih =>
    simp [TGenEnv.genTyVars, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_gen
      obtain ⟨tv, Env1⟩ := v1; simp at h h_gen
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨tvs', Env2⟩ := v2; simp at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        -- Env.genState.tyGen ≤ Env1.genState.tyGen ≤ Env2.genState.tyGen
        have h1 : Env1.genState.tyGen ≥ Env.genState.tyGen := by
          simp only [TGenEnv.genTyVar] at h_gen
          split at h_gen
          · simp at h_gen
          · simp at h_gen; rw [← h_gen.2]
            simp [TState.genTySym, TState.incTyGen]
        exact Nat.le_trans h1 (ih Env1 tvs' Env2 h_rest)

/-- `LMonoTys.instantiate` never decreases `tyGen`. -/
theorem LMonoTys.instantiate_tyGen_mono [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TGenEnv IDMeta)
    (result : LMonoTys) (Env' : TGenEnv IDMeta)
    (h : LMonoTys.instantiate ids mtys Env = .ok (result, Env')) :
    Env'.genState.tyGen ≥ Env.genState.tyGen := by
  simp [LMonoTys.instantiate, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_gen
    obtain ⟨freshtvs, Env1⟩ := v1; simp at h
    obtain ⟨_, h2⟩ := h; rw [← h2]
    exact genTyVars_tyGen_mono ids.length Env freshtvs Env1 h_gen

/-- `LMonoTys.instantiateEnv` never decreases `tyGen`. -/
theorem LMonoTys.instantiateEnv_tyGen_mono [ToFormat IDMeta]
    (ids : List TyIdentifier) (mtys : LMonoTys) (Env : TEnv IDMeta)
    (result : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.instantiateEnv ids mtys Env = .ok (result, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  unfold LMonoTys.instantiateEnv at h
  generalize h_inst : LMonoTys.instantiate ids mtys Env.genEnv = r at h
  match r, h_inst with
  | .error _, _ => simp at h
  | .ok (a, gE), h_inst =>
    simp at h; obtain ⟨_, h2⟩ := h; rw [← h2]; simp
    exact LMonoTys.instantiate_tyGen_mono ids mtys Env.genEnv a gE h_inst

/-- `LTy.instantiate` never decreases `tyGen`. -/
theorem LTy.instantiate_tyGen_mono [ToFormat IDMeta]
    (ty : LTy) (Env : TGenEnv IDMeta)
    (mty : LMonoTy) (Env' : TGenEnv IDMeta)
    (h : LTy.instantiate ty Env = .ok (mty, Env')) :
    Env'.genState.tyGen ≥ Env.genState.tyGen := by
  cases ty with
  | forAll vars body =>
    cases vars with
    | nil =>
      simp [LTy.instantiate] at h
      obtain ⟨_, h2⟩ := h; subst h2; omega
    | cons v vs =>
      simp [LTy.instantiate, Bind.bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i v1 h_gen
        obtain ⟨freshtvs, Env1⟩ := v1; simp at h
        obtain ⟨_, h2⟩ := h; rw [← h2]
        exact genTyVars_tyGen_mono (v :: vs).length Env freshtvs Env1 h_gen

/-- `tconsAlias` never decreases `tyGen`.
    It calls `instantiateEnv` (which may increment tyGen) then `unify` + `updateSubst`
    (which preserve genEnv). -/
theorem tconsAlias_tyGen_mono
    (name : String) (args : LMonoTys) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.tconsAlias name args Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [LMonoTy.tconsAlias] at h
  -- Case split on whether a matching alias is found
  split at h
  case h_1 =>
    -- No matching alias: Env' = Env
    simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; subst h2; omega
  case h_2 alias_val =>
    -- Matching alias found: calls instantiateEnv then unify + updateSubst
    split at h
    · simp at h
    · rename_i instTypes Env1 h_inst
      -- unify + updateSubst only change stateSubstInfo, not genEnv
      split at h
      · simp at h
      · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; subst h2
        simp [TEnv.updateSubst]
        exact LMonoTys.instantiateEnv_tyGen_mono _ _ Env instTypes Env1 h_inst

/-- `LMonoTy.aliasDef?` never decreases `tyGen`. -/
theorem aliasDef_tyGen_mono
    (mty : LMonoTy) (Env : TEnv T.IDMeta)
    (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.aliasDef? mty Env = .ok (mty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  simp only [LMonoTy.aliasDef?] at h
  split at h
  · exact tconsAlias_tyGen_mono _ _ Env mty' Env' h
  · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; subst h2; omega
  · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h2⟩ := h; subst h2; omega

mutual
/-- `LMonoTy.resolveAliases` never decreases `tyGen`. -/
theorem LMonoTy_resolveAliases_tyGen_mono
    (mty : LMonoTy) (Env : TEnv T.IDMeta)
    (mty' : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mty with
  | .ftvar _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | .bitvec _ =>
    simp [LMonoTy.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | .tcons name args =>
    simp only [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_args
      obtain ⟨args', Env1⟩ := v1; simp at h h_args
      split at h
      · simp at h
      · rename_i v2 h_alias
        obtain ⟨mty'', Env2⟩ := v2; simp at h
        simp [Pure.pure, Except.pure] at h
        obtain ⟨h_mty, h_env⟩ := h; subst h_mty; subst h_env
        exact Nat.le_trans
          (LMonoTys_resolveAliases_tyGen_mono args Env args' Env1 h_args)
          (tconsAlias_tyGen_mono name args' Env1 mty'' Env2 h_alias)

theorem LMonoTys_resolveAliases_tyGen_mono
    (mtys : LMonoTys) (Env : TEnv T.IDMeta)
    (mtys' : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  match mtys with
  | [] =>
    simp [LMonoTys.resolveAliases, Pure.pure, Except.pure] at h
    obtain ⟨_, h2⟩ := h; subst h2; omega
  | mty :: mrest =>
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i v1 h_one
      obtain ⟨mty'', Env1⟩ := v1; simp at h h_one
      split at h
      · simp at h
      · rename_i v2 h_rest
        obtain ⟨mrest', Env2⟩ := v2; simp at h
        simp [Pure.pure, Except.pure] at h
        obtain ⟨_, h_env⟩ := h; subst h_env
        exact Nat.le_trans
          (LMonoTy_resolveAliases_tyGen_mono mty Env mty'' Env1 h_one)
          (LMonoTys_resolveAliases_tyGen_mono mrest Env1 mrest' Env2 h_rest)
end

/-- `LTy.resolveAliases` never decreases `tyGen`. -/
theorem LTy_resolveAliases_tyGen_mono
    (ty : LTy) (Env : TEnv T.IDMeta)
    (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  -- LTy.resolveAliases = LTy.instantiate on genEnv, then LMonoTy.resolveAliases
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_inst
    obtain ⟨mty_mid, genEnv1⟩ := v1; simp at h h_inst
    -- h : mty_mid.resolveAliases {genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo} = .ok (mty, Env')
    have h1 : genEnv1.genState.tyGen ≥ Env.genEnv.genState.tyGen :=
      LTy.instantiate_tyGen_mono ty Env.genEnv mty_mid genEnv1 h_inst
    have h2 : Env'.genEnv.genState.tyGen ≥ genEnv1.genState.tyGen := by
      have := LMonoTy_resolveAliases_tyGen_mono mty_mid
        { Env with genEnv := genEnv1 } mty Env' h
      simp at this; exact this
    exact Nat.le_trans h1 h2

/-- Each sub-function used by `resolveAux` never decreases tyGen.
    This covers `inferConst`, `inferFVar`, `typeBoundVar`, `instantiateWithCheck`,
    `updateSubst`, `eraseFromContext`, `genTyVar`, and `Constraints.unify`.
    The proof for each follows from: genTyVar increments by 1, genTyVars by n,
    unify/updateSubst/eraseFromContext preserve genEnv entirely. -/

theorem LTy_instantiateWithCheck_tyGen_mono
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  -- LTy.instantiateWithCheck = resolveAliases then checkNoFutureGenVars then isInstanceOfKnownType
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i v1 h_resolve
    obtain ⟨mty_res, Env1⟩ := v1; simp at h h_resolve
    split at h  -- checkNoFutureGenVars
    · simp at h
    · split at h  -- isInstanceOfKnownType
      · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h_env⟩ := h; subst h_env
        exact LTy_resolveAliases_tyGen_mono ty Env mty_res Env1 h_resolve
      · simp at h

theorem LMonoTy_instantiateWithCheck_tyGen_mono
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (mty, Env')) :
    Env'.genEnv.genState.tyGen ≥ Env.genEnv.genState.tyGen := by
  -- LMonoTy.instantiateWithCheck = instantiateEnv then resolveAliases then check
  simp only [LMonoTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i instTypes Env1 h_inst
    -- h now has match on resolveAliases
    split at h
    · simp at h
    · rename_i v2 h_resolve
      obtain ⟨mty_res, Env2⟩ := v2; simp at h h_resolve
      split at h  -- checkNoFutureGenVars
      · simp at h
      · split at h  -- isInstanceOfKnownType
        · simp [Pure.pure, Except.pure] at h; obtain ⟨_, h_env⟩ := h; subst h_env
          exact Nat.le_trans
            (LMonoTys.instantiateEnv_tyGen_mono _ _ Env instTypes Env1 h_inst)
            (LMonoTy_resolveAliases_tyGen_mono _ Env1 mty_res Env2 h_resolve)
        · simp at h

end TyGenMono

end Lambda

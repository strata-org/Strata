/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.Expression
import all Strata.Languages.Core.VerifiedSMTGen.Expression
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
public import Strata.DL.SMT.Op
import all Strata.DL.SMT.Op

/-!
# Refactored SMT encoder — `CoreCtx` intermediate language (typing + denotation + well-formedness)

The collected intermediate: `CoreCtx` (reachable functions/vars/axioms/assumptions/distincts over
`Expression.Expr`), its order-aware well-formedness `CoreCtx.WF`, and its denotational validity
`CoreCtx.Valid`. Built on the source `Expression` layer (`HasSimpType`/`simpDenote`).

Order-aware for the definitions (`fnDefs`/`varDefs`): each `fnDef` body is typed against the declared
functions and the strict prefix of earlier `fnDef`s (no forward reference); each `varDef` RHS against
the declared vars, the prefix of earlier `varDef`s, and all functions. Assertions / distincts / the
goal keep the full context.

The SMT-translation-side name preconditions (declared-name distinctness / reserved-prefix avoidance,
non-predefined function names) live in a separate `CoreCtx.NamesWF` bundle in `SharedWF`
(where the `uAT`-dependent `FnNamesNotPredefined` is defined).
-/

open Core Lambda Strata.SMT Std

namespace Core.Refactor

/-! ## Function / variable definitions and the collected context -/

/-- Assumed abstract-type arity table (opaque `.tcons` heads → arity). -/
public abbrev KnownTypeArities : Type := List (String × Nat)

/-- Core-level function definition (non-recursive, with body) → SMT interpreted function (`define-fun`). -/
structure FnDef where
  name : String
  /-- Formal parameters as (source name × type) pairs, in order — the SMT `define-fun` binder ids; the
      body references parameters positionally as `.bvar i`. -/
  params : List (String × LMonoTy)
  retTy : LMonoTy
  body : Expression.Expr
  deriving Inhabited

/-- Parameter types of a function definition, in order. -/
def FnDef.argTys (d : FnDef) : List LMonoTy := d.params.map (·.2)

/-- Source formal-parameter names of a function definition, in order. -/
def FnDef.argNames (d : FnDef) : List String := d.params.map (·.1)

/-- Core-level variable definition (deterministic program variable). -/
structure VarDef where
  name : String
  ty : LMonoTy
  body : Expression.Expr
  deriving Inhabited

/-- The collected context an obligation reduces to (subject of `translate`). -/
structure CoreCtx where
  /-- User datatype declarations, grouped into mutual-recursion blocks (in topological block order) — the
      emission structure `declare-datatype[s]` needs. Populated by collect from the type factory; the
      verified fragment is datatype-free, so this is `[]`. -/
  datatypes : List (List (LDatatype CoreLParams.IDMeta)) := []
  datatypeFuns : Map String (Op.DatatypeFuncs × LConstr CoreLParams.IDMeta) := ∅
  sorts : KnownTypeArities := []
  /-- Uninterpreted (recursive/bodyless) factory functions, `(name, arrow-type)` — `declare-fun`. -/
  fnDecls : FnCtx := []
  /-- Non-recursive functions with bodies → `define-fun`. -/
  fnDefs : List FnDef := []
  fnAxioms : List Expression.Expr := []
  /-- Variable namespace `Φ` (`.fvar` heads) — unmanaged free vars + nondet program vars; `declare-fun`. -/
  varDecls : FVarCtx := []
  varDefs : List VarDef := []
  assumptions : List Expression.Expr := []
  distincts : List (List Expression.Expr) := []
  deriving Inhabited

/-! ## Typing contexts projected from `CoreCtx` -/

/-- The free-variable (`.fvar`, arrow-capable) typing context `Φ`: var decls followed by var defs. -/
def CoreCtx.toΦ (cctx : CoreCtx) : FVarCtx :=
  cctx.varDecls ++ cctx.varDefs.map (fun v => (v.name, v.ty))

/-- The user-function (`.op`-head) typing context `Ψ`: uninterpreted declarations then interpreted
    definitions (arrow reconstructed from `(argTys, retTy)`). -/
def CoreCtx.toΨ (cctx : CoreCtx) : FnCtx :=
  cctx.fnDecls ++ cctx.fnDefs.map (fun d => (d.name, LMonoTy.mkArrow' d.retTy d.argTys))

/-- Every declared/defined symbol name in the context, in emission order — reachable function
    declarations/definitions, opaque sorts, datatype types, and variable declarations/definitions. This
    is the SINGLE source for the quantifier-binder avoid-set (the encoder's `toTranslateEnv.usedNames`
    is defined as this) AND the source-side parameter-freshness hygiene (`TranslateHygiene`), so the two
    can never drift apart — no dependency on any translate-layer construct. -/
def CoreCtx.declaredNames (cctx : CoreCtx) : List String :=
  cctx.fnDecls.map Prod.fst ++ cctx.fnDefs.map (·.name)
  ++ cctx.sorts.map Prod.fst ++ cctx.datatypes.flatMap (·.map (·.name))
  ++ cctx.varDecls.map Prod.fst ++ cctx.varDefs.map (·.name)

/-- Base-typed signature: the stored (possibly arrow) type decomposes to base argument types and a base
    return type. Used for the uninterpreted `fnDecls`/`varDecls` whose types are not otherwise typed. -/
def SigBase (τ : LMonoTy) : Prop :=
  (∀ a ∈ (collectArrowTy τ).1, LExpr.MonoTyIsBase a) ∧ LExpr.MonoTyIsBase (collectArrowTy τ).2

/-! ## Order-aware well-formedness (typing only — SMT-free)
`fnDefs`/`varDefs` are typed against the STRICT PREFIX (emission order) via order-threaded inductives
(mirroring `SMTQuery.IFsWF` / `ProofObligation.PathEntriesWF`); asserts/goal use the full context.
-/

/-- Order-aware typing of the `fnDef` preamble: threads the function context `Ψ` (seeded at `fnDecls`),
    each body typed with NO free vars (`Φ = []` — `varDecls`/`varDefs` are emitted later; post-lift a
    define-fun body references none) against the accumulated `Ψ` + its own params; then this fn's
    signature is appended. Rules out any forward reference to a later `fnDef`. -/
inductive FnDefsWF : FnCtx → List FnDef → Prop where
  | nil {Ψ} : FnDefsWF Ψ []
  | cons {Ψ d rest} :
      LExpr.HasSimpType [] Ψ d.argTys d.body d.retTy →
      (∀ t ∈ d.argTys, LExpr.MonoTyIsBase t) →
      (d.params.map Prod.fst).Nodup →
      (∀ p ∈ d.params, p.1 ∉ Ψ.map Prod.fst) →
      FnDefsWF (Ψ ++ [(d.name, LMonoTy.mkArrow' d.retTy d.argTys)]) rest →
      FnDefsWF Ψ (d :: rest)

/-- Order-aware typing of the `varDef` preamble: threads the var context `Φ` (seeded at `varDecls`), each
    RHS typed against the accumulated `Φ` + the FULL function context `Ψ` (all functions are emitted
    before any `varDef`); then this var's entry is appended. -/
inductive VarDefsWF (Ψ : FnCtx) : FVarCtx → List VarDef → Prop where
  | nil {Φ} : VarDefsWF Ψ Φ []
  | cons {Φ v rest} :
      LExpr.HasSimpType Φ Ψ [] v.body v.ty →
      VarDefsWF Ψ (Φ ++ [(v.name, v.ty)]) rest →
      VarDefsWF Ψ Φ (v :: rest)

/-- Each function definition in a well-formed `FnDefsWF` fold has a context-free typing derivation
    (`HasTypeA`) for its body at its parameter types (bound-variable context `d.argTys`). The threaded
    `Ψ` is irrelevant to `HasTypeA`. -/
theorem FnDefsWF.mem_hasTypeA {Ψ : FnCtx} {fnDefs : List FnDef} (h : FnDefsWF Ψ fnDefs) :
    ∀ d ∈ fnDefs, LExpr.HasTypeA d.argTys d.body d.retTy := by
  induction h with
  | nil => intro d hd; simp at hd
  | @cons Ψ d rest hty _ _ _ _ ih =>
      intro d' hd'
      rcases List.mem_cons.mp hd' with rfl | hd'
      · exact HasSimpType_implies_HasTypeA hty
      · exact ih d' hd'

/-- Each variable definition in a `VarDefsWF` fold has a context-free typing derivation (`HasTypeA`)
    for its RHS, in the empty bound-variable context (`Δ = []`). -/
theorem VarDefsWF.mem_hasTypeA {Ψ : FnCtx} {Φ : FVarCtx} {varDefs : List VarDef}
    (h : VarDefsWF Ψ Φ varDefs) :
    ∀ v ∈ varDefs, LExpr.HasTypeA [] v.body v.ty := by
  induction h with
  | nil => intro v hv; simp at hv
  | @cons Φ v rest hty _ ih =>
      intro v' hv'
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact HasSimpType_implies_HasTypeA hty
      · exact ih v' hv'

structure CoreCtx.WF (cctx : CoreCtx) (goal : Expression.Expr) : Prop where
  /-- Every uninterpreted function declaration has a base-typed signature. -/
  fnDeclsSigBase : ∀ (nm : String) (τ : LMonoTy), (nm, τ) ∈ cctx.fnDecls → SigBase τ
  /-- `fnDef` preamble, order-threaded from `fnDecls` (`Φ = []`). -/
  fnDefsWF : FnDefsWF cctx.fnDecls cctx.fnDefs
  /-- Every uninterpreted variable declaration has a base-typed signature. -/
  varDeclsSigBase : ∀ (nm : String) (τ : LMonoTy), (nm, τ) ∈ cctx.varDecls → SigBase τ
  /-- `varDef` preamble, order-threaded from `varDecls`, over the full function context `toΨ`. -/
  varDefsWF : VarDefsWF cctx.toΨ cctx.varDecls cctx.varDefs
  fnAxiomsWF : ∀ e ∈ cctx.fnAxioms, LExpr.HasSimpType cctx.toΦ cctx.toΨ [] e (.tcons "bool" [])
  assumptionsWF : ∀ e ∈ cctx.assumptions, LExpr.HasSimpType cctx.toΦ cctx.toΨ [] e (.tcons "bool" [])
  distinctsWF : ∀ es ∈ cctx.distincts, 2 ≤ es.length ∧ ∃ τ, LExpr.MonoTyIsBase τ ∧
    ∀ e ∈ es, LExpr.HasSimpType cctx.toΦ cctx.toΨ [] e τ
  goalWF : LExpr.HasSimpType cctx.toΦ cctx.toΨ [] goal (.tcons "bool" [])
  /-- The verified fragment is datatype-free: no datatype declarations. `datatypes` is the primary field;
      `datatypeFuns` (the op-name→constructor cache the collect phase maintains) is downstream of it. -/
  datatypesEmpty : cctx.datatypes = []
  /-- Empty datatype-op cache — the cache-consistency consequence of `datatypesEmpty` (an empty datatype set
      has no ops). Stated directly since there is no `deriveDatatypeFuns` invariant yet; when datatypes enter
      the verified subset this becomes the general `datatypeFuns = deriveDatatypeFuns datatypes`. -/
  datatypeFunsEmpty : cctx.datatypeFuns = ∅

-- `CoreCtx.NamesWF` (the SMT-translation name preconditions) lives in `SharedWF`, where
-- `uAT`/`FnNamesNotPredefined`/`corePredefinedOpToSMTOp` live — it is `uAT`-dependent, so it does not
-- belong in this `uAT`-free source-language file.

/-! ## Denotational validity of a `CoreCtx` (source-model side, gated on `CoreCtx.WF`) -/

/-- The model respects the `define-fun` preamble: each `fnDef`/`varDef`'s interpretation equals the
    denotation of its body. The `simpDenote` gate is the `HasTypeA` extracted from `CoreCtx.WF`'s
    order-threaded typing via `FnDefsWF.mem_hasTypeA` / `VarDefsWF.mem_hasTypeA`. -/
def CoreCtx.DefConsistent (cctx : CoreCtx) (goal : Expression.Expr)
    (hwf : CoreCtx.WF cctx goal)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  (∀ (d : FnDef) (hd : d ∈ cctx.fnDefs)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal d.argTys),
      applyBVarVal d.argTys d.retTy
        (opInterp d.name ((List.foldr LMonoTy.arrow d.retTy d.argTys).substTyVars simpTyVarVal)) bvarVal
      = simpDenote opInterp fvarVal bvarVal d.body d.retTy (hwf.fnDefsWF.mem_hasTypeA d hd)) ∧
  (∀ (v : VarDef) (hv : v ∈ cctx.varDefs),
      fvarVal ⟨v.name, ()⟩ (v.ty.substTyVars simpTyVarVal)
      = simpDenote opInterp fvarVal .nil v.body v.ty (hwf.varDefsWF.mem_hasTypeA v hv))

/-- The model satisfies the persistent assertions (assumptions + function axioms). -/
def CoreCtx.ModelSatisfiesAsserts (cctx : CoreCtx) (goal : Expression.Expr)
    (hwf : CoreCtx.WF cctx goal)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  (∀ e (he : e ∈ cctx.assumptions),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hwf.assumptionsWF e he)) : Bool) = true) ∧
  (∀ e (he : e ∈ cctx.fnAxioms),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hwf.fnAxiomsWF e he)) : Bool) = true)

/-- The model satisfies every distinctness group: its member-denotations are all distinct (`Nodup`). -/
def CoreCtx.ModelSatisfiesDistincts (cctx : CoreCtx) (goal : Expression.Expr)
    (hwf : CoreCtx.WF cctx goal)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  ∀ es (hes : es ∈ cctx.distincts),
    (distinctDenote opInterp fvarVal es (hwf.distinctsWF es hes).2).Nodup

/-- **Denotational validity of a collected `CoreCtx`.** For every consistent model that respects the
    definitions and satisfies the asserts + distincts, the goal denotes `true`. `uAT`/`ufs`-free. -/
def CoreCtx.Valid (cctx : CoreCtx) (goal : Expression.Expr)
    (hwf : CoreCtx.WF cctx goal) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    CoreCtx.DefConsistent cctx goal hwf opInterp fvarVal →
    CoreCtx.ModelSatisfiesAsserts cctx goal hwf opInterp fvarVal →
    CoreCtx.ModelSatisfiesDistincts cctx goal hwf opInterp fvarVal →
    (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) = true

/-- **Denotational unsatisfiability of a collected `CoreCtx`.** The dual of `CoreCtx.Valid`: for every
    consistent model that respects the definitions and satisfies the asserts + distincts, the goal
    denotes `false` (the asserts entail `¬goal`). `uAT`/`ufs`-free. -/
def CoreCtx.Unsat (cctx : CoreCtx) (goal : Expression.Expr)
    (hwf : CoreCtx.WF cctx goal) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    CoreCtx.DefConsistent cctx goal hwf opInterp fvarVal →
    CoreCtx.ModelSatisfiesAsserts cctx goal hwf opInterp fvarVal →
    CoreCtx.ModelSatisfiesDistincts cctx goal hwf opInterp fvarVal →
    (simpDenote opInterp fvarVal .nil goal (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) = false

end Core.Refactor

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core.VerifiedSMTGen.Expression
import all Strata.Languages.Core.VerifiedSMTGen.Expression
public import Strata.DL.Imperative.EvalContext
import all Strata.DL.Imperative.EvalContext
public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.Factory
public import Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.TypeFactory

/-!
# Refactored SMT encoder — `ProofObligation` input language (typing + denotation + well-formedness)

The raw input: an `Imperative.ProofObligation` (path-condition entries + goal) over `Expression.Expr`,
evaluated against a function factory `F` and type factory `tf`. Its order-aware well-formedness
(`PathEntriesWF` + `ProofObligation.WF`) threads the accumulating free-var context entry-by-entry
(assumption / det-var / nondet-var / distinct), each entry well-typed at the context reached so far
against the user-function context `factoryFnCtx F tf`, and its denotational validity is
`ProofObligation.Valid`. `uAT`-free (independent of the SMT array-theory flag).

`factoryFnCtx F tf` is the user-function typing context: `F`'s functions minus predefined ops and minus
datatype ops (the latter carried by `tf` and merged into `F` by `TypeFactory.genFactory`, but emitted
natively rather than via the `.fnOp`/`Ψ` path). So an obligation whose op-heads reference a datatype op
is outside this fragment — `factoryFnCtx_notDatatypeOp` records that every `Ψ` name is a non-datatype op.
-/

open Core Lambda Imperative Std

namespace Core.Refactor

/-! ## Obligation / factory helper contexts -/

-- `funcBvarSubst` is defined in `Expression` (imported above).

/-- All datatype-op names (constructors / testers / safe + unsafe selectors) across the whole type
    factory. These are emitted natively as `.datatype_op` alongside `declare-datatype`, so they are NOT
    part of the user-function space (`factoryFnCtx`) and are skipped by the function-reachability walk. -/
def datatypeOpNames (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : List String :=
  tf.allDatatypes.flatMap fun d =>
    let (c, i, s, u) := d.genFunctionMaps
    c.keys ++ i.keys ++ s.keys ++ u.keys

/-- The factory's **user** functions relative to a type factory `tf`: those whose demangled name is
    neither a predefined operator nor a datatype op. Predefined ops (int/bool/Map/…) are recognised
    `CoreOp`s handled natively; datatype ops (constructors/testers/selectors) — which `TypeFactory.genFactory`
    also merges into `F` — are emitted natively from `declare-datatype`. Neither is resolved through the
    `.fnOp`/`Ψ` typing path, so both are excluded. Order-preserving (`filter`) — the stored
    callee-before-caller order is retained. -/
def Factory.nonPredefined (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : List (LFunc CoreLParams) :=
  F.toArray.toList.filter (fun f =>
    !isPredefinedOp f.name.name &&
    !(Core.NameMangling.demangledBaseName f.name.name ∈ datatypeOpNames tf))

/-- The USER-function typing context `Ψ` a factory contributes (relative to `tf`): every user function
    (`Factory.nonPredefined`, recursive or not, with body or not) mapped to its `(name, arrow-type)`
    signature, in stored order. Full-factory analog of `CoreCtx.toΨ`. The declare-vs-define distinction is
    an SMT *emission* concern, irrelevant to this source-side lookup context — `Ψ`-membership is
    order/split-insensitive. Predefined + datatype ops are excluded (see `nonPredefined`): a source `.op`
    head that is one is typed by `AppSpine.op` (predefined) or emitted natively (datatype), never resolved
    against `Ψ`. -/
def factoryFnCtx (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : FnCtx :=
  (Factory.nonPredefined F tf).map (fun f => (f.name.name, LMonoTy.mkArrow' f.output f.inputs.values))

/-- Membership in `nonPredefined` unpacks to the three defining facts. -/
theorem mem_nonPredefined {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {f : LFunc CoreLParams} :
    f ∈ Factory.nonPredefined F tf ↔
      f ∈ F.toArray.toList ∧ isPredefinedOp f.name.name = false ∧
      Core.NameMangling.demangledBaseName f.name.name ∉ datatypeOpNames tf := by
  unfold Factory.nonPredefined
  rw [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true',
    decide_eq_false_iff_not]

/-- Every user-function name (`factoryFnCtx`) demangles to a NON-datatype op — by construction, since
    `nonPredefined` filters datatype ops out. -/
theorem factoryFnCtx_notDatatypeOp {F : Lambda.Factory CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} {nm : String}
    (h : nm ∈ (factoryFnCtx F tf).map Prod.fst) :
    Core.NameMangling.demangledBaseName nm ∉ datatypeOpNames tf := by
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
  obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hp
  subst hfe; subst hpn
  exact (mem_nonPredefined.mp hf).2.2

/-- **Topological well-typedness of the factory's user functions**, threading the function context `Ψ`
    over the list (`Factory.nonPredefined F`, in stored callee-before-caller order): every function appends its
    own `(name, arrow)` signature for later ones, and each NON-recursive function-with-body has its
    (bvar-lifted) body typed at `Φ = []` (define-fun bodies reference no free var, post-lift), the
    accumulated `Ψ` (only functions declared/defined EARLIER), and its own params. `d`-independent — nothing
    from a `ProofObligation` is needed. Mirrors `CoreCtx.FnDefsWF`. -/
inductive FactoryFnsWF : FnCtx → List (LFunc CoreLParams) → Prop where
  | nil {Ψ} : FactoryFnsWF Ψ []
  | cons {Ψ f rest} :
      (∀ body, f.isRecursive = false → f.body = some body →
        LExpr.HasSimpType [] Ψ f.inputs.values (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output) →
      FactoryFnsWF (Ψ ++ [(f.name.name, LMonoTy.mkArrow' f.output f.inputs.values)]) rest →
      FactoryFnsWF Ψ (f :: rest)

/-- Each non-recursive-with-body factory function's (bvar-lifted) body has a `Δ`-only `HasTypeA` — what
    `Factory.ModelRespects` gates `simpDenote` on. (The threaded `Ψ` is irrelevant to `HasTypeA`.) -/
theorem FactoryFnsWF.mem_hasTypeA {Ψ : FnCtx} {fns : List (LFunc CoreLParams)} (h : FactoryFnsWF Ψ fns) :
    ∀ f ∈ fns, ∀ body, f.isRecursive = false → f.body = some body →
      LExpr.HasTypeA f.inputs.values (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output := by
  induction h with
  | nil => intro f hf; simp at hf
  | @cons Ψ f rest hbody _ ih =>
      intro g hg body hrec hb
      rcases List.mem_cons.mp hg with rfl | hg
      · exact HasSimpType_implies_HasTypeA (hbody body hrec hb)
      · exact ih g hg body hrec hb

/-! ## Order-aware path-condition well-formedness (source mirror of SMTQuery's `IFsWF`) -/

/-- The single-entry context step: a `.varDecl` with a monomorphizable type prepends its `(name, mty)`;
    everything else leaves `Φ` unchanged. -/
def stepCtx (Φ : FVarCtx) : Imperative.PathConditionEntry Expression → FVarCtx
  | (.varDecl name ty _) =>
      match ty.toMonoType? with
      | some mty => (name.name, mty) :: Φ
      | none => Φ
  | _ => Φ

/-- The free-var context reached after processing the entries in order — the left fold of `stepCtx` from
    the EMPTY seed. `ProofObligation.WF` types the entries/goal from this `[]` seed, which already forbids
    unmanaged free variables (every free var must be path-declared); so no seed parameter is needed. -/
def accumFVarCtx (es : List (Imperative.PathConditionEntry Expression)) : FVarCtx :=
  es.foldl stepCtx []

/-- **Single path-condition entry well-formedness** at free-var context `Φ` (the successor context is
    computed by `stepCtx`). A `.varDecl` additionally carries frontend freshness + reserved-name hygiene
    on its bound name. -/
inductive PathEntryWF (Ψ : FnCtx) :
    FVarCtx → Imperative.PathConditionEntry Expression → Prop where
  | assumption {Φ l e} :
      LExpr.HasSimpType Φ Ψ [] e (.tcons "bool" []) →
      PathEntryWF Ψ Φ (.assumption l e)
  | varDeclDet {Φ} {name : Expression.Ident} {ty mty e} :
      ty.toMonoType? = some mty → LExpr.MonoTyIsBase mty →
      LExpr.HasSimpType Φ Ψ [] e mty →
      name.name ∉ (Φ ++ Ψ).map (·.1) →
      (∀ n : Nat, name.name ≠ s!"$__bv{n}") →
      PathEntryWF Ψ Φ (.varDecl name ty (.det e))
  | varDeclNondet {Φ} {name : Expression.Ident} {ty mty} :
      ty.toMonoType? = some mty → LExpr.MonoTyIsBase mty →
      name.name ∉ (Φ ++ Ψ).map (·.1) →
      (∀ n : Nat, name.name ≠ s!"$__bv{n}") →
      PathEntryWF Ψ Φ (.varDecl name ty .nondet)
  | distinct {Φ l es} :
      2 ≤ es.length →
      (∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ) →
      PathEntryWF Ψ Φ (.distinct l es)

/-- **Path-condition list well-formedness**: a chain of `PathEntryWF` steps, threading the free-var
    context via `stepCtx`. -/
inductive PathEntriesWF (Ψ : FnCtx) :
    FVarCtx → List (Imperative.PathConditionEntry Expression) → Prop where
  | nil {Φ} : PathEntriesWF Ψ Φ []
  | cons {Φ entry rest} :
      PathEntryWF Ψ Φ entry →
      PathEntriesWF Ψ (stepCtx Φ entry) rest →
      PathEntriesWF Ψ Φ (entry :: rest)

/-! ## Small-elimination witness extractors (recurse on entry DATA, pull typing out of the witness) -/

/-- Recover the assumption's `bool` typing derivation. -/
def PathEntryWF.asmWitness {Ψ : FnCtx} {Φ : FVarCtx} {l : String} {e : Expression.Expr}
    (h : PathEntryWF Ψ Φ (.assumption l e)) :
    LExpr.HasSimpType Φ Ψ [] e (.tcons "bool" []) :=
  match h with
  | .assumption he => he

/-- Recover the deterministic var-decl's monotype + body typing derivation. -/
def PathEntryWF.detWitness {Ψ : FnCtx} {Φ : FVarCtx} {name : Expression.Ident}
    {ty : Expression.Ty} {e : Expression.Expr}
    (h : PathEntryWF Ψ Φ (.varDecl name ty (.det e))) :
    ∃ mty, ty.toMonoType? = some mty ∧ LExpr.HasSimpType Φ Ψ [] e mty :=
  match h with
  | .varDeclDet hmono _ he _ _ => ⟨_, hmono, he⟩

/-- Recover the distinct group's common base-type typing derivation. -/
def PathEntryWF.dstWitness {Ψ : FnCtx} {Φ : FVarCtx} {l : String}
    {es : List Expression.Expr} (h : PathEntryWF Ψ Φ (.distinct l es)) :
    ∃ τ, LExpr.MonoTyIsBase τ ∧ ∀ e ∈ es, LExpr.HasSimpType Φ Ψ [] e τ :=
  match h with
  | .distinct _ hex => hex

/-- Recover the distinct group's `2 ≤ length` witness. -/
def PathEntryWF.dstLen {Ψ : FnCtx} {Φ : FVarCtx} {l : String}
    {es : List Expression.Expr} (h : PathEntryWF Ψ Φ (.distinct l es)) :
    2 ≤ es.length :=
  match h with
  | .distinct hlen _ => hlen

/-- **Inversion of the `cons` step**, re-indexed at the computed context `stepCtx Φ entry`. -/
theorem PathEntriesWF.consInv {Ψ : FnCtx} {Φ : FVarCtx}
    {entry : Imperative.PathConditionEntry Expression}
    {rest : List (Imperative.PathConditionEntry Expression)}
    (h : PathEntriesWF Ψ Φ (entry :: rest)) :
    PathEntryWF Ψ Φ entry ∧
    PathEntriesWF Ψ (stepCtx Φ entry) rest := by
  cases h with
  | cons hpc hrest => exact ⟨hpc, hrest⟩

/-! ## Source well-formedness bundle (uAT-free) -/

/-- **Well-formedness of a raw proof obligation** — ONLY the two facts intrinsic to the obligation itself:
    its path-condition entries are order-well-typed (against the factory functions `factoryFnCtx F`, from
    the `[]` fvar seed), and its goal is well-typed (bool) at the accumulated context. `uAT`/`tf`/`CoreCtx`-
    free. No unmanaged-free-var precondition is needed: stating both at the `[]` seed already means every
    free variable must be path-declared. Base-typedness of the declared vars is derivable from `entriesWF`
    (`PathEntryWF` forces each `varDecl`'s monotype to be base). Factory well-formedness lives separately
    in `Factory.SimpWF`. -/
structure ProofObligation.WF (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta)
    (d : Imperative.ProofObligation Expression) : Prop where
  entriesWF : PathEntriesWF (factoryFnCtx F tf) [] d.assumptions.flatten
  goalWF : LExpr.HasSimpType (accumFVarCtx d.assumptions.flatten)
    (factoryFnCtx F tf) [] d.obligation (.tcons "bool" [])

/-- Per-function signature hygiene, relative to the ambient function-name set `fnames` (instantiated to
    the whole factory's function names). Base arg/return types + distinct params (the simple-fragment
    monomorphizer guarantees), plus two frontend/monomorphizer NAME-hygiene facts needed for a sound
    `define-fun` emission: the formal-parameter names are disjoint from the function names (`fnParamsFresh`
    — a param shadowing a called function would misdenote the body), and the function name is not a
    reserved quantifier-binder name (`fnNameNotReserved`). -/
structure fnSigSimp (fnames : List String) (f : LFunc CoreLParams) : Prop where
  fnRetBase : LExpr.MonoTyIsBase f.output
  fnArgsBase : ∀ a ∈ f.inputs.values, LExpr.MonoTyIsBase a
  fnParamsWF : (f.inputs.keys.map (·.name)).Nodup
  fnParamsFresh : ∀ p ∈ f.inputs.keys, p.name ∉ fnames
  fnNameNotReserved : ∀ n : Nat, f.name.name ≠ s!"$__bv{n}"

/-- **Simple-fragment well-formedness of a factory** — entirely `ProofObligation`-independent, and ranging
    only over the **user** functions (`Factory.nonPredefined` — built-in ops excluded, since they're handled
    natively and could have non-base signatures). The non-recursive user-function bodies are topologically
    well-typed (`FactoryFnsWF`, each using only earlier functions), the user-function axioms are well-typed
    against the whole user-function context, and the frontend/monomorphizer hygiene holds (base arg/return
    types, distinct params). No "not-predefined" field is needed — `nonPredefined`/
    `factoryFnCtx` are user-only by construction. -/
structure Factory.SimpWF (F : Lambda.Factory CoreLParams)
    (tf : @Lambda.TypeFactory CoreLParams.IDMeta) : Prop where
  fnsWF : FactoryFnsWF [] (Factory.nonPredefined F tf)
  fnAxiomsWF : ∀ f ∈ Factory.nonPredefined F tf, ∀ e ∈ f.axioms,
    LExpr.HasSimpType [] (factoryFnCtx F tf) [] e (.tcons "bool" [])
  fnsSigSimp : ∀ f ∈ Factory.nonPredefined F tf, fnSigSimp ((factoryFnCtx F tf).map Prod.fst) f

/-! ## Model-side denotation, parameterized by the WF typing -/

/-- **A model satisfies a single path-condition entry** (recursion on entry data, typing threaded via
    the witness extractors). Assumption ⟦e⟧=true; det-var pinned to ⟦body⟧; nondet unconstrained; distinct
    group pairwise-≠. -/
def ProofObligation.ModelSatisfiesPC {Ψ : FnCtx} {Φ : FVarCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp)
    (entry : Imperative.PathConditionEntry Expression)
    (h : PathEntryWF Ψ Φ entry) : Prop :=
  match entry, h with
  | .assumption _ e, h =>
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA h.asmWitness) : Bool) = true
  | .varDecl name _ (.det e), h =>
      fvarVal ⟨name.name, ()⟩ (h.detWitness.choose.substTyVars simpTyVarVal)
      = simpDenote opInterp fvarVal .nil e h.detWitness.choose
          (HasSimpType_implies_HasTypeA h.detWitness.choose_spec.2)
  | .varDecl _ _ .nondet, _ => True
  | .distinct _ es, h =>
      (distinctDenote opInterp fvarVal es h.dstWitness).Nodup

/-- **A model satisfies all path conditions**, folding `ModelSatisfiesPC` over the entry list (recursion
    on entry data, threading the context via `stepCtx` and the tail witness via `consInv`). -/
def ProofObligation.ModelSatisfiesPCs {Ψ : FnCtx}
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) :
    (entries : List (Imperative.PathConditionEntry Expression)) → (Φ : FVarCtx) →
    PathEntriesWF Ψ Φ entries → Prop
  | [], _, _ => True
  | entry :: rest, Φ, h =>
      ProofObligation.ModelSatisfiesPC opInterp fvarVal entry h.consInv.1
      ∧ ProofObligation.ModelSatisfiesPCs opInterp fvarVal rest (stepCtx Φ entry) h.consInv.2

/-- **The model respects the factory** (factory-level, `ProofObligation`-free): every non-recursive-with-
    body factory function's `opInterp` image matches its (bvar-lifted) body; every factory axiom denotes
    `true`. Typing gates come from `Factory.SimpWF`. -/
def Factory.ModelRespects (F : Lambda.Factory CoreLParams)
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    (hsimp : Factory.SimpWF F tf)
    (opInterp : Lambda.OpInterp simpTcInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp) : Prop :=
  (∀ (f : LFunc CoreLParams) (hf : f ∈ Factory.nonPredefined F tf) (body : Expression.Expr)
      (hrec : f.isRecursive = false) (hbody : f.body = some body)
      (bvarVal : Lambda.BVarVal simpTcInterp simpTyVarVal f.inputs.values),
      applyBVarVal f.inputs.values f.output
        (opInterp f.name.name
          ((List.foldr LMonoTy.arrow f.output f.inputs.values).substTyVars simpTyVarVal)) bvarVal
      = simpDenote opInterp fvarVal bvarVal (LExpr.substFvarsLifting body (funcBvarSubst f)) f.output
          (hsimp.fnsWF.mem_hasTypeA f hf body hrec hbody)) ∧
  (∀ (f : LFunc CoreLParams) (hf : f ∈ Factory.nonPredefined F tf) (e : Expression.Expr) (he : e ∈ f.axioms),
      (simpDenote opInterp fvarVal .nil e (.tcons "bool" [])
        (HasSimpType_implies_HasTypeA (hsimp.fnAxiomsWF f hf e he)) : Bool) = true)

/-- **Denotational validity of a raw proof obligation.** For every consistent model that respects the
    factory (`Factory.SimpWF`) and satisfies the path conditions, the goal denotes `true`. Every
    denotation is gated by the `WF`/`SimpWF` typing (no `Denotes`-style ∃, no ill-typed vacuity).
    `uAT`/`CoreCtx`-free. -/
def ProofObligation.Valid (F : Lambda.Factory CoreLParams)
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (d : Imperative.ProofObligation Expression)
    (hwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    Factory.ModelRespects F hsimp opInterp fvarVal →
    ProofObligation.ModelSatisfiesPCs opInterp fvarVal d.assumptions.flatten [] hwf.entriesWF →
    (simpDenote opInterp fvarVal .nil d.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) = true

/-- **Denotational unsatisfiability of a raw proof obligation.** The dual of `ProofObligation.Valid`:
    for every consistent model that respects the factory and satisfies the path conditions, the goal
    denotes `false` (the path conditions entail `¬goal`). `uAT`/`CoreCtx`-free. -/
def ProofObligation.Unsat (F : Lambda.Factory CoreLParams)
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (d : Imperative.ProofObligation Expression)
    (hwf : ProofObligation.WF F tf d) (hsimp : Factory.SimpWF F tf) : Prop :=
  ∀ (divByZero modByZero : Int → Int)
    (opInterp : Lambda.OpInterp simpTcInterp) (_hop : OpInterpConsistent divByZero modByZero opInterp)
    (fvarVal : Lambda.FreeVarVal CoreLParams simpTcInterp),
    Factory.ModelRespects F hsimp opInterp fvarVal →
    ProofObligation.ModelSatisfiesPCs opInterp fvarVal d.assumptions.flatten [] hwf.entriesWF →
    (simpDenote opInterp fvarVal .nil d.obligation (.tcons "bool" [])
      (HasSimpType_implies_HasTypeA hwf.goalWF) : Bool) = false

end Core.Refactor

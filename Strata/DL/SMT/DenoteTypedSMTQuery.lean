/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.DL.SMT.Factory
import all Strata.DL.SMT.Factory
public import Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.DenoteTyped
public import Strata.DL.SMT.DenoteTypedProps
import all Strata.DL.SMT.DenoteTypedProps

/-!
# `SMTQuery`: definition, typing, and denotation for an SMT query

The `SMTQuery` record models an SMT query as the production pipeline's SMT emitter groups it (sorts,
datatypes, function declarations/definitions, function axioms, variable declarations/definitions,
assumptions, goal). This file gives its typing (via `Term.typeCheck`), its order-aware well-formedness
`SMTQuery.WF`, and its denotation in terms of (un)satisfiability (`checkSat` / `UnsatWithNegObl`, via
`Term.denoteTyped`). In emission order, every `define-fun` body type-checks against only the context
accumulated up to it (prior declarations + earlier definitions + its own params, no forward references)
and every assertion placed after the declarations and definitions type-checks against the full symbol context.

Scope: the well-formedness judgments type-check terms against an EMPTY sort context (`uss = []`), so
they currently assume the query declares no uninterpreted sorts or datatypes — the `sorts` and
`datatypes` fields are carried for structural fidelity but are not yet threaded into typing/denotation.

Key definitions: `SMTQuery.WF`, `SMTQuery.checkSat`, `SMTQuery.UnsatWithNegObl` / `UnsatWithObl`,
`SMTQuery.EntailsObl` / `EntailsNegObl`. Key results: `SMTQuery.WF.fsTypeCheck`,
`SMTQuery.WF.assertOrLitTypeCheck`.
-/

open Strata.SMT Std

namespace Strata.SMT.DenoteTyped

/-- A datatype constructor's SMT declaration shape: constructor name + typed fields. -/
public structure RConstructor where
  name : String
  args : List (String × TermType)
  deriving Repr, Inhabited

/-- The query record. -/
public structure SMTQuery where
  /-- Uninterpreted sorts (`declare-sort`). -/
  sorts : List Strata.DL.SMT.Sort
  /-- User datatype declarations (`declare-datatype[s]`), in topological/mutual-block order. Emitted
      after `sorts`, since datatype constructors may reference the declared sorts. -/
  datatypes : List (List (String × List String × List RConstructor))
  /-- Uninterpreted functions (`declare-fun`). -/
  fnDecls : List UF
  /-- Interpreted functions (`define-fun`). -/
  fnDefs : List IF
  /-- Function axioms. -/
  fnAxioms : List Term
  /-- Variable declarations (`declare-fun`). -/
  varDecls : List UF
  /-- Variable definitions (nullary `define-fun`). -/
  varDefs : List IF
  /-- Assumptions (including `distinct` terms). These are not fundamentally different from `obl`: both
      are emitted as `(assert <t>)`. `obl` is carried separately only because the last term is frequently
      negated before the satisfiability check; this file provides `UnsatWithNegObl` / `UnsatWithObl` as
      helpers for that case. -/
  assumptions : List Term
  /-- The goal term. -/
  obl : Term
  deriving Inhabited

/-! ## Projections: UF context, define-fun preamble, persistent asserts -/

/-- The `define-fun` preamble: interpreted functions followed by variable definitions. -/
def SMTQuery.fs (q : SMTQuery) : List IF := q.fnDefs ++ q.varDefs

/-- The full UF context: all declared and defined functions, in emission order
    (`fnDecls`, `fnDefs`, `varDecls`, `varDefs`). -/
def SMTQuery.ufs (q : SMTQuery) : UFCtx :=
  q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls ++ q.varDefs.map IF.toUF

/-- The persistent assertions: function axioms followed by assumptions. -/
def SMTQuery.asserts (q : SMTQuery) : List Term := q.fnAxioms ++ q.assumptions

/-! ## UF-context hygiene and lookup -/

/-- SMT symbol names are distinct, and none collides with a reserved `$__bv{n}` binder id. -/
structure UFCtxWF (ufs : UFCtx) : Prop where
  uf_nodup : (ufs.map (·.id)).Nodup
  no_reserved : ∀ n : Nat, s!"$__bv{n}" ∉ ufs.map (·.id)

/-- Look up a UF signature in `ufs` by its printed name (`id`). -/
def lookupUF (ufs : UFCtx) (name : String) : Option UF :=
  ufs.find? (·.id == name)

/-! ## Order-aware well-formedness (SMT-LIB emission faithfulness) -/

/-- Well-formedness of a single `define-fun` at UF context `ufs`: its body type-checks to its declared
    output `f.out` under `ufs` extended with its formal parameters `f.args`. -/
def IF.WF (ufs : UFCtx) (f : IF) : Prop :=
  Term.typeCheck ⟨[], ufs, f.args⟩ f.body = .ok f.out

/-- Well-formedness of a `define-fun` preamble: each function is `IF.WF` against the context accumulated
    so far (prior declarations and earlier definitions) plus its own parameters, so there are no forward
    references. -/
inductive IFsWF : UFCtx → List IF → Prop where
  | nil {ufs} : IFsWF ufs []
  | cons {ufs f rest} :
      IF.WF ufs f →
      IFsWF (ufs ++ [f.toUF]) rest →
      IFsWF ufs (f :: rest)

/-- Well-formedness of an `SMTQuery`: a non-shadowing UF context (`ufsWF`), an order-well-typed
    `define-fun` preamble with no forward references (`fnDefsWF`, `varDefsWF`), and every assertion and
    the goal type-checking to `bool` against the full context (`assertsWF`, `oblWF`). -/
structure SMTQuery.WF (q : SMTQuery) : Prop where
  /-- All declared/defined names are distinct and avoid the reserved binder prefix. -/
  ufsWF : UFCtxWF q.ufs
  /-- Each `fnDef` body type-checks against `fnDecls` and strictly-earlier `fnDefs`. -/
  fnDefsWF : IFsWF q.fnDecls q.fnDefs
  /-- Each `varDef` body type-checks against `fnDecls`, all `fnDefs`, `varDecls`, and strictly-earlier
      `varDefs`. -/
  varDefsWF : IFsWF (q.fnDecls ++ q.fnDefs.map IF.toUF ++ q.varDecls) q.varDefs
  /-- Every persistent assertion type-checks to `bool` against the full context `q.ufs`. -/
  assertsWF : ∀ t ∈ q.asserts, Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool
  /-- The goal type-checks to `bool` against the full context `q.ufs`. -/
  oblWF : Term.typeCheck ⟨[], q.ufs, []⟩ q.obl = .ok .bool

/-! ## Typing at the full context -/

/-- Each function in an `IFsWF ufsBase fs` type-checks at the full context `ufsBase ++ fs.map IF.toUF`. -/
private theorem IFsWF.mem_wf {ufsBase : UFCtx} {fs : List IF} (h : IFsWF ufsBase fs) :
    ∀ f ∈ fs, IF.WF (ufsBase ++ fs.map IF.toUF) f := by
  induction h with
  | nil => intro f hf; simp at hf
  | @cons ufs f rest hf _ ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · unfold IF.WF at hf ⊢
        exact typeCheck_ufs_mono_append hf
      · have hih := ih g hg
        unfold IF.WF at hih ⊢
        simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using hih

/-- Every `define-fun` in `q.fs` type-checks at the full context `q.ufs`. -/
theorem SMTQuery.WF.fsTypeCheck {q : SMTQuery} (hwf : SMTQuery.WF q) :
    ∀ f ∈ q.fs, IF.WF q.ufs f := by
  intro f hf
  rw [SMTQuery.fs, List.mem_append] at hf
  rcases hf with hf | hf
  · have h1 := hwf.fnDefsWF.mem_wf f hf
    unfold IF.WF at h1 ⊢
    have h2 := typeCheck_ufs_mono_append (tail := q.varDecls ++ q.varDefs.map IF.toUF) h1
    simpa only [SMTQuery.ufs, List.append_assoc] using h2
  · have h1 := hwf.varDefsWF.mem_wf f hf
    unfold IF.WF at h1 ⊢
    simpa only [SMTQuery.ufs, List.append_assoc] using h1

/-- Typing of any assertion OR trailing literal, at the full `q.ufs`. -/
theorem SMTQuery.WF.assertOrLitTypeCheck {q : SMTQuery} (hwf : SMTQuery.WF q) {lits : List Term}
    (hlits : ∀ t ∈ lits, Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool)
    {t : Term} (ht : t ∈ q.asserts ++ lits) : Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool := by
  rcases List.mem_append.mp ht with h | h
  · exact hwf.assertsWF t h
  · exact hlits t h

/-- The negated goal `¬obl` type-checks to `bool` at the full context `q.ufs`. -/
theorem SMTQuery.WF.notOblTypeCheck {q : SMTQuery} (hwf : SMTQuery.WF q) :
    Term.typeCheck ⟨[], q.ufs, []⟩ (Term.app (.core .not) [q.obl] .bool) = .ok .bool := by
  simp [Term.typeCheck, hwf.oblWF, bind, Except.bind]

/-! ## Model-side satisfaction (denotation) -/

/-- The trivial sort interpretation, mapping every sort to `Unit`. -/
def defaultσ : SortInterp := fun _ _ => Unit

instance : SortInterp.AllInhabited defaultσ := ⟨fun _ _ => ⟨()⟩⟩

variable {σ : SortInterp} {𝒜 : ArrayTheory} [SortInterp.AllInhabited σ]

/-- Build a `VarEnv` binding the variables `bvs` to an HList of values, with `default` elsewhere. -/
def hlToEnv : (bvs : TermVarCtx) → HList (TermType.denoteTyped σ 𝒜) (bvs.map (·.ty)) → VarEnv σ 𝒜
  | [], _ => fun _ => default
  | v :: rest, hl =>
    match hl with
    | .cons x xs => fun w => if h : w = v then cast (by rw [h]) x else hlToEnv rest xs w

/-- `ufInterp` is consistent with the interpreted function `f`: for every argument valuation, `ufInterp`
    applied to `f`'s UF signature equals the denotation of `f.body` under the environment binding `f`'s
    parameters to those arguments. -/
def IF.UFConsistent {ufs : UFCtx} (f : IF)
    (htc : IF.WF ufs f)
    (ufInterp : UFInterp σ 𝒜) (divByZero modByZero : Int → Int) : Prop :=
  ∀ hl : HList (TermType.denoteTyped σ 𝒜) f.toUF.args,
    UF.applyDenoteTyped σ 𝒜 f.toUF (ufInterp f.toUF) hl
    = Term.denoteTyped ufInterp (hlToEnv f.args hl) divByZero modByZero f.body f.out htc

/-- **`ufInterp` respects the whole `define-fun` preamble `fs`.** -/
def IFs.UFConsistent {ufs : UFCtx} (fs : List IF)
    (htc : ∀ f ∈ fs, IF.WF ufs f)
    (ufInterp : UFInterp σ 𝒜) (divByZero modByZero : Int → Int) : Prop :=
  ∀ (f : IF) (hmem : f ∈ fs),
    IF.UFConsistent f (htc f hmem) ufInterp divByZero modByZero

/-- The SMT variable environment. -/
noncomputable def mkVarEnv : VarEnv defaultσ SmtArrayTheory :=
  fun v => (default : TermType.denoteTyped defaultσ SmtArrayTheory v.ty)

/-- The query is satisfiable together with `lits`: there is a model — a sort interpretation, array
    theory, UF interpretation, and variable environment — that respects the `define-fun` preamble
    (`IFs.UFConsistent`) and makes every persistent assertion and every literal in `lits` denote `true`,
    all typed against the full context `q.ufs`. -/
def SMTQuery.checkSat (q : SMTQuery) (hwf : SMTQuery.WF q) (lits : List Term)
    (hlits : ∀ t ∈ lits, Term.typeCheck ⟨[], q.ufs, []⟩ t = .ok .bool) : Prop :=
  ∃ (σ : SortInterp) (hσ : SortInterp.AllInhabited σ) (𝒜 : ArrayTheory)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) (divByZero modByZero : Int → Int),
    haveI := hσ
    IFs.UFConsistent q.fs hwf.fsTypeCheck ufInterp divByZero modByZero ∧
    (∀ t (ht : t ∈ q.asserts ++ lits),
      Term.denoteTyped ufInterp smtEnv divByZero modByZero t .bool
        (hwf.assertOrLitTypeCheck hlits ht) = true)

/-- The assertions together with `¬obl` are unsatisfiable (equivalently, the assertions entail `obl` —
    see `EntailsObl`). -/
def SMTQuery.UnsatWithNegObl (q : SMTQuery) (hwf : SMTQuery.WF q) : Prop :=
  ¬ q.checkSat hwf [Term.app (.core .not) [q.obl] .bool]
      (fun t ht => by rw [List.mem_singleton] at ht; subst ht; exact hwf.notOblTypeCheck)

/-- The assertions together with `obl` are unsatisfiable (equivalently, the assertions entail `¬obl` —
    see `EntailsNegObl`). -/
def SMTQuery.UnsatWithObl (q : SMTQuery) (hwf : SMTQuery.WF q) : Prop :=
  ¬ q.checkSat hwf [q.obl]
      (fun t ht => by rw [List.mem_singleton] at ht; subst ht; exact hwf.oblWF)

/-- The assertions entail `obl`: in every model respecting the `define-fun` preamble in which all
    persistent assertions denote `true`, `obl` denotes `true`. -/
def SMTQuery.EntailsObl (q : SMTQuery) (hwf : SMTQuery.WF q) : Prop :=
  ∀ (σ : SortInterp) (hσ : SortInterp.AllInhabited σ) (𝒜 : ArrayTheory)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) (divByZero modByZero : Int → Int),
    haveI := hσ
    IFs.UFConsistent q.fs hwf.fsTypeCheck ufInterp divByZero modByZero →
    (∀ t (ht : t ∈ q.asserts),
      Term.denoteTyped ufInterp smtEnv divByZero modByZero t .bool (hwf.assertsWF t ht) = true) →
    Term.denoteTyped ufInterp smtEnv divByZero modByZero q.obl .bool hwf.oblWF = true

/-- The assertions entail `¬obl`: in every model respecting the `define-fun` preamble in which all
    persistent assertions denote `true`, `obl` denotes `false`. -/
def SMTQuery.EntailsNegObl (q : SMTQuery) (hwf : SMTQuery.WF q) : Prop :=
  ∀ (σ : SortInterp) (hσ : SortInterp.AllInhabited σ) (𝒜 : ArrayTheory)
    (ufInterp : UFInterp σ 𝒜) (smtEnv : VarEnv σ 𝒜) (divByZero modByZero : Int → Int),
    haveI := hσ
    IFs.UFConsistent q.fs hwf.fsTypeCheck ufInterp divByZero modByZero →
    (∀ t (ht : t ∈ q.asserts),
      Term.denoteTyped ufInterp smtEnv divByZero modByZero t .bool (hwf.assertsWF t ht) = true) →
    Term.denoteTyped ufInterp smtEnv divByZero modByZero q.obl .bool hwf.oblWF = false

/-! ## Entailment / unsatisfiability equivalences -/

/-- The assertions entail `obl` iff they are unsatisfiable together with `¬obl`. -/
theorem SMTQuery.entailsObl_iff_unsatWithNegObl (q : SMTQuery) (hwf : SMTQuery.WF q) :
    q.EntailsObl hwf ↔ q.UnsatWithNegObl hwf := by
  constructor
  · -- Entails → Unsat
    intro hE hsat
    obtain ⟨σ, hσ, 𝒜, ufInterp, smtEnv, dz, mz, hUF, hall⟩ := hsat
    haveI := hσ
    have hasserts : ∀ t (ht : t ∈ q.asserts),
        Term.denoteTyped ufInterp smtEnv dz mz t .bool (hwf.assertsWF t ht) = true := by
      intro t ht
      exact hall t (List.mem_append.mpr (Or.inl ht))
    have hobl := hE σ hσ 𝒜 ufInterp smtEnv dz mz hUF hasserts
    have hlit := hall (Term.app (.core .not) [q.obl] .bool)
      (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
    rw [Term.denoteTyped_not] at hlit
    simp only [cast_eq] at hlit
    -- `hlit : (! denote q.obl) = true`, with a proof-arg defeq to `hwf.oblWF`
    have key : (! Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF) = true := hlit
    rw [hobl] at key
    simp at key
  · -- Unsat → Entails
    intro hU σ hσ 𝒜 ufInterp smtEnv dz mz hUF hasserts
    haveI := hσ
    rcases Bool.eq_false_or_eq_true
        (Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF) with hb | hb
    · exact hb
    · exfalso
      apply hU
      refine ⟨σ, hσ, 𝒜, ufInterp, smtEnv, dz, mz, hUF, ?_⟩
      intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hasserts t h
      · rw [List.mem_singleton] at h
        subst h
        rw [Term.denoteTyped_not]
        simp only [cast_eq]
        show (! Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF) = true
        rw [hb]
        rfl

/-- The assertions entail `¬obl` iff they are unsatisfiable together with `obl`. -/
theorem SMTQuery.entailsNegObl_iff_unsatWithObl (q : SMTQuery) (hwf : SMTQuery.WF q) :
    q.EntailsNegObl hwf ↔ q.UnsatWithObl hwf := by
  constructor
  · -- EntailsNeg → Unsat
    intro hE hsat
    obtain ⟨σ, hσ, 𝒜, ufInterp, smtEnv, dz, mz, hUF, hall⟩ := hsat
    haveI := hσ
    have hasserts : ∀ t (ht : t ∈ q.asserts),
        Term.denoteTyped ufInterp smtEnv dz mz t .bool (hwf.assertsWF t ht) = true := by
      intro t ht
      exact hall t (List.mem_append.mpr (Or.inl ht))
    have hobl := hE σ hσ 𝒜 ufInterp smtEnv dz mz hUF hasserts
    have hlit := hall q.obl (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
    have key : Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF = true := hlit
    rw [hobl] at key
    simp at key
  · -- Unsat → EntailsNeg
    intro hU σ hσ 𝒜 ufInterp smtEnv dz mz hUF hasserts
    haveI := hσ
    rcases Bool.eq_false_or_eq_true
        (Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF) with hb | hb
    · exfalso
      apply hU
      refine ⟨σ, hσ, 𝒜, ufInterp, smtEnv, dz, mz, hUF, ?_⟩
      intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hasserts t h
      · rw [List.mem_singleton] at h
        subst h
        show Term.denoteTyped ufInterp smtEnv dz mz q.obl .bool hwf.oblWF = true
        exact hb
    · exact hb

end Strata.SMT.DenoteTyped

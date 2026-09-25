/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTriple
import all Strata.Languages.Core.Logic.ContractToHoareTriple

/-! # Discharging a procedure's contract

Ways to establish a `Procedure.contractTriple`, and the bridges that make a concrete
procedure's contract decidable. The definitions being established live in
`Strata.Languages.Core.Logic.ContractToHoareTriple`.

## Key results

- `Procedure.contractTriple_of` — supplies the procedure and body, discharging the
  name lookup and the `.structured` obligation once.
- `Procedure.contractTriple_of_core` and `Procedure.contractTriple_of_core_typed` —
  retain the concrete Core entry facts needed by evaluator-sensitive body proofs.
- `Procedure.contractTriple_nil` and
  `Procedure.contractTriple_nil_of_ensuresAmongRequires` — an empty body meets a
  contract whose non-`free` `ensures` clauses are all among its `requires`.
- `Procedure.contractTriple_singleton_cmd` — a one-command body, reduced to a single
  obligation about that command's `EvalCommand` step.
- `Procedure.preAsPredicate_of_preHoldsAt` and
  `Procedure.not_postAsPredicate_of_postRefutedAt` — the decidable bridges, which let
  a concrete procedure be settled by `decide` / `native_decide` rather than by
  unfolding a translated AST by hand.
- `preAsPredicate_of_eqPairs` and `postAsPredicate_of_eqPairs` — establish contract
  clauses that are equalities between variables with matching canonical bindings.
- `assertionsValid_defaultAssertEvents` — turns true non-`free` contract clauses into
  a valid assertion-event trace.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-- A snapshot of a procedure's non-`free` contract clauses as `assert` events is
assertion-valid whenever every such clause evaluates to `true` in that snapshot. -/
theorem assertionsValid_defaultAssertEvents
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check)
    (h : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ checks.toList → check.attr = Procedure.CheckAttr.Default →
      Expression.eval fac σ check.expr = some HasBool.tt) :
    Trace.AssertionsValid Expression (EvaluatorBasedInterp Expression)
      (defaultAssertEvents fac σ checks) := by
  have key : ∀ (l : List (CoreLabel × Procedure.Check)) (acc : Trace Expression),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ l → check.attr = Procedure.CheckAttr.Default →
        Expression.eval fac σ check.expr = some HasBool.tt) →
      Trace.AssertionsValidFromP Expression (EvaluatorBasedInterp Expression) (fun _ => True) acc
        (l.filterMap fun lc =>
          if lc.2.attr = Procedure.CheckAttr.Default then
            some (Event.assert
              { factory := fac, store := σ, label := lc.1, expr := lc.2.expr,
                metadata := lc.2.md })
          else none) := by
    intro l
    induction l with
    | nil => intro acc _; exact True.intro
    | cons lc rest ih =>
      intro acc hl
      simp only [List.filterMap_cons]
      by_cases hattr : lc.2.attr = Procedure.CheckAttr.Default
      · rw [if_pos hattr]
        exact ⟨fun _ _world _ => hl lc.1 lc.2 List.mem_cons_self hattr,
          ih acc (fun label check hmem => hl label check (List.mem_cons_of_mem _ hmem))⟩
      · rw [if_neg hattr]
        exact ih acc (fun label check hmem => hl label check (List.mem_cons_of_mem _ hmem))
  exact key checks.toList [] h

/-- If every `requires` is an equality between a listed variable pair whose two
bindings hold the same canonical value, all preconditions hold. -/
theorem preAsPredicate_of_eqPairs (proc : Procedure)
    (ρ : Imperative.Env Expression)
    (pairs : List ((Expression.Ident × Option Lambda.LMonoTy) ×
                   (Expression.Ident × Option Lambda.LMonoTy)))
    (hsyn : (proc.spec.preconditions.toList.all fun lc =>
       pairs.any fun p => decide (lc.2.expr =
         Lambda.LExpr.eq () (Lambda.LExpr.fvar () p.1.1 p.1.2)
           (Lambda.LExpr.fvar () p.2.1 p.2.2))) = Bool.true)
    (hstore : ∀ p ∈ pairs, ∃ v, ρ.store p.1.1 = some v ∧ ρ.store p.2.1 = some v ∧
       Lambda.LExpr.isCanonicalValue ρ.factory v = Bool.true) :
    Procedure.preAsPredicate proc ρ := by
  intro label check hmem
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hsyn
  obtain ⟨p, hp, hexpr⟩ := hsyn (label, check) hmem
  obtain ⟨v, h1, h2, hv⟩ := hstore p hp
  rw [hexpr]
  exact Lambda.evalFully_eq_self ρ.factory ρ.store () _ _ v
    (Lambda.evalFully_fvar_of_value ρ.factory ρ.store () p.1.1 p.1.2 v h1 hv)
    (Lambda.evalFully_fvar_of_value ρ.factory ρ.store () p.2.1 p.2.2 v h2 hv)

/-- Postcondition analogue of `preAsPredicate_of_eqPairs`: `free` clauses are
exempt, and each remaining equality follows from matching canonical bindings. -/
theorem postAsPredicate_of_eqPairs (proc : Procedure)
    (ρ : Imperative.Env Expression)
    (pairs : List ((Expression.Ident × Option Lambda.LMonoTy) ×
                   (Expression.Ident × Option Lambda.LMonoTy)))
    (hsyn : (proc.spec.postconditions.toList.all fun lc =>
       decide (lc.2.attr ≠ Procedure.CheckAttr.Default) ||
       pairs.any fun p => decide (lc.2.expr =
         Lambda.LExpr.eq () (Lambda.LExpr.fvar () p.1.1 p.1.2)
           (Lambda.LExpr.fvar () p.2.1 p.2.2))) = Bool.true)
    (hstore : ∀ p ∈ pairs, ∃ v, ρ.store p.1.1 = some v ∧ ρ.store p.2.1 = some v ∧
       Lambda.LExpr.isCanonicalValue ρ.factory v = Bool.true) :
    Procedure.postAsPredicate proc ρ := by
  intro label check hmem hattr
  simp only [List.all_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hsyn
  rcases hsyn (label, check) hmem with hattr' | ⟨p, hp, hexpr⟩
  · exact absurd hattr hattr'
  · obtain ⟨v, h1, h2, hv⟩ := hstore p hp
    rw [hexpr]
    exact Lambda.evalFully_eq_self ρ.factory ρ.store () _ _ v
      (Lambda.evalFully_fvar_of_value ρ.factory ρ.store () p.1.1 p.1.2 v h1 hv)
      (Lambda.evalFully_fvar_of_value ρ.factory ρ.store () p.2.1 p.2.2 v h2 hv)

/-- Build a `contractTriple` from the name lookup, body, and body judgement.
    The factory, old-inout, and input-typing clauses of `contractTriple`'s
    precondition are discarded by weakening, so the body proof needs none of them. -/
theorem Procedure.contractTriple_of (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (h : Triple p.findProcByString? φ params (Procedure.preAsPredicate proc)
      [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  ⟨proc, bss, hproc, hbody,
    consequence p.findProcByString? φ params h (fun _ hρ => hρ.1) (fun _ h => h)⟩

/-- Build a `contractTriple` whose body proof may assume the concrete factory and
    old-inout relation but does not need input-value typing. -/
theorem Procedure.contractTriple_of_core (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (h : Triple p.findProcByString? φ params
      (fun ρ => Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory ∧
        Procedure.oldInoutAsPredicate proc ρ)
      [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  ⟨proc, bss, hproc, hbody,
    consequence p.findProcByString? φ params h
      (fun _ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩) (fun _ hpost => hpost)⟩

/-- Build a `contractTriple` while retaining every entry fact, including values
    matching the types of the procedure's input and inout formals. -/
theorem Procedure.contractTriple_of_core_typed (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (h : Triple p.findProcByString? φ params
      (fun ρ => Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory ∧
        Procedure.oldInoutAsPredicate proc ρ ∧ Procedure.inputAsPredicate proc ρ)
      [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  ⟨proc, bss, hproc, hbody, h⟩

/-- A contract whose every non-`free` `ensures` is literally one of the
    `requires` is met by an empty body: nothing runs, so the precondition still
    holds at the end.

    The workhorse is `skip_block` plus consequence; no reasoning about
    `Expression.eval` is involved, because the same check expression carries
    from the precondition to the postcondition. -/
theorem Procedure.contractTriple_nil (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [])
    (himp : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ∃ (label' : CoreLabel) (check' : Procedure.Check),
        (label', check') ∈ proc.spec.preconditions.toList ∧ check'.expr = check.expr) :
    Procedure.contractTriple φ p params procName := by
  refine Procedure.contractTriple_of φ p params procName proc [] hproc hbody ?_
  refine Core.Logic.Hoare.consequence p.findProcByString? φ params
    (Core.Logic.Hoare.skip p.findProcByString? φ params "" #[]
      (Procedure.preAsPredicate proc))
    (fun _ h => h) (fun ρ hpre label check hmem hattr => ?_)
  obtain ⟨label', check', hmem', hexpr⟩ := himp label check hmem hattr
  rw [← hexpr]
  exact hpre label' check' hmem'


/-- The decidable check `preHoldsAt` discharges the proposition `preAsPredicate`. -/
theorem Procedure.preAsPredicate_of_preHoldsAt {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : Procedure.preHoldsAt proc ρ = Bool.true) :
    Procedure.preAsPredicate proc ρ := by
  intro label check hmem
  simp only [Procedure.preHoldsAt, List.all_eq_true, decide_eq_true_eq] at h
  exact h (label, check) hmem

/-- The decidable check `postRefutedAt` refutes the proposition `postAsPredicate`:
    the clause it finds is a non-`free` `ensures` that does not hold. -/
theorem Procedure.not_postAsPredicate_of_postRefutedAt {proc : Procedure}
    {ρ : Imperative.Env Expression} (h : Procedure.postRefutedAt proc ρ = Bool.true) :
    ¬ Procedure.postAsPredicate proc ρ := by
  simp only [Procedure.postRefutedAt, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨lc, hmem, hattr, hne⟩ := h
  intro hpost
  exact hne (hpost lc.1 lc.2 hmem hattr)

/-- An empty body meets a contract whose non-`free` `ensures` clauses are all among its
    `requires`, with the containment settled by the decidable `ensuresAmongRequires`. -/
theorem Procedure.contractTriple_nil_of_ensuresAmongRequires
    (p : Core.Program) (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [])
    (h : Procedure.ensuresAmongRequires proc = Bool.true) :
    Procedure.contractTriple φ p params procName := by
  refine Procedure.contractTriple_nil φ p params procName proc hproc hbody
    (fun label check hmem hattr => ?_)
  simp only [Procedure.ensuresAmongRequires, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h (label, check) hmem with hattr' | ⟨lc', hmem', hexpr⟩
  · exact absurd hattr hattr'
  · exact ⟨lc'.1, lc'.2, hmem', hexpr⟩


/-- **A one-command body.** The `cmd` rule reduces a contract over `[.cmd c]` to a
    single semantic obligation about `c`. `hsem` receives the precondition clauses,
    concrete factory, and old-inout relation; signature typing is weakened away because
    this constructor does not require it. `hpost_proj` ensures the postcondition names no
    variable declared by `c`, since the block drops those. -/
theorem Procedure.contractTriple_singleton_cmd (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc) (c : Command)
    (hbody : proc.body = .structured [Stmt.cmd c])
    (hsem : ∀ ρ₀ σ' emitted, Procedure.preAsPredicate proc ρ₀ →
      ρ₀.factory = Core.Factory → Procedure.oldInoutAsPredicate proc ρ₀ →
      InitEnvWF params (Stmt.cmd c) ρ₀ →
      EvalCommandE p.findProcByString? φ ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid Expression (EvaluatorBasedInterp Expression) emitted ∧
        (Trace.Reachable Expression (EvaluatorBasedInterp Expression) emitted →
          Procedure.postAsPredicate proc { ρ₀ with store := σ' }))
    (hpost_proj : Imperative.Logic.Hoare.PostWF [Imperative.Stmt.cmd c]
      (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  Procedure.contractTriple_of_core φ p params procName proc _ hproc hbody
    (block p.findProcByString? φ params (by simp [Imperative.Block.noFuncDecl,
        Imperative.Stmt.noFuncDecl])
      (cmd p.findProcByString? φ params c
        (fun ρ => Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory ∧
          Procedure.oldInoutAsPredicate proc ρ)
        (Procedure.postAsPredicate proc)
        (fun ρ₀ σ' emitted hpre hwf hstep =>
          hsem ρ₀ σ' emitted hpre.1 hpre.2.1 hpre.2.2 hwf hstep))
      hpost_proj)


end Hoare

end Core.Logic

end -- public section


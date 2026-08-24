/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTriple
import all Strata.Languages.Core.Logic.ContractToHoareTriple

/-! # Discharging a procedure's contract

Ways to establish a `Procedure.contractTriple`, and the bridges that make a concrete
procedure's contract decidable.  The definitions being established live in
`Strata.Languages.Core.Logic.ContractToHoareTriple`.

## Key results

- `Procedure.contractTriple_of` — supplies the procedure and body, discharging the
  name lookup and the `.structured` obligation once.
- `Procedure.contractTriple_nil` and
  `Procedure.contractTriple_nil_of_ensuresAmongRequires` — an empty body meets a
  contract whose non-`free` `ensures` clauses are all among its `requires`.
- `Procedure.contractTriple_singleton_cmd` — a one-command body, reduced to a single
  obligation about that command's `EvalCommand` step.
- `Procedure.preAsPredicate_of_preHoldsAt` and
  `Procedure.not_postAsPredicate_of_postRefutedAt` — the decidable bridges, which let
  a concrete procedure be settled by `decide` / `native_decide` rather than by
  unfolding a translated AST by hand.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

variable (φ : Expression.Factory → PureFunc Expression → Expression.Factory)

/-- Build a `contractTriple` from the name lookup, the body, and the judgement about
    that body.  The body's `Triple` need only assume `preAsPredicate proc`; the factory
    half of `contractTriple`'s precondition is discarded by weakening, so this is the form
    for a proof that does not need to know which factory it runs on. -/
theorem Procedure.contractTriple_of (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (h : Triple p.findProcByString? φ params (Procedure.preAsPredicate proc)
      [Imperative.Stmt.block "" bss #[]] (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  ⟨proc, bss, hproc, hbody,
    consequence p.findProcByString? φ params h (fun _ hρ => hρ.1) (fun _ h => h)⟩

/-- Build a `contractTriple` whose body proof may *assume* `ρ.factory = Core.Factory`.
    Same as `contractTriple_of` but keeps the factory half of the precondition instead of
    weakening it away — reach for this when the body's proof needs the concrete evaluator's
    operator laws (arithmetic, comparison, boolean negation). -/
theorem Procedure.contractTriple_of_core (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (h : Triple p.findProcByString? φ params
      (fun ρ => Procedure.preAsPredicate proc ρ ∧ ρ.factory = Core.Factory)
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
  refine Strata.Logic.Hoare.consequence (Lang.coreBlock p.findProcByString? φ)
    params
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


/-- **A one-command body.**  The `cmd` rule reduces a contract over `[.cmd c]` to a
    single semantic obligation about `c`, plus `hpost_proj`: the postcondition must not
    name a variable `c` declares, since the procedure block drops those. -/
theorem Procedure.contractTriple_singleton_cmd (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc) (c : Command)
    (hbody : proc.body = .structured [Stmt.cmd c])
    (hsem : ∀ ρ₀ σ' f, Procedure.preAsPredicate proc ρ₀ →
      InitEnvWF params (Stmt.cmd c) ρ₀ →
      EvalCommand p.findProcByString? φ ρ₀.factory ρ₀.store c σ' f →
      Procedure.postAsPredicate proc { ρ₀ with store := σ', hasFailure := f } ∧
        f = Bool.false)
    (hpost_proj : Imperative.Logic.Hoare.PostWF [Imperative.Stmt.cmd c]
      (Procedure.postAsPredicate proc)) :
    Procedure.contractTriple φ p params procName :=
  Procedure.contractTriple_of φ p params procName proc _ hproc hbody
    (block p.findProcByString? φ params (by simp [Imperative.Block.noFuncDecl,
        Imperative.Stmt.noFuncDecl])
      (cmd p.findProcByString? φ params c
        (Procedure.preAsPredicate proc) (Procedure.postAsPredicate proc) hsem)
      hpost_proj)

end Hoare

end Core.Logic

end -- public section


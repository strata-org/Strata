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
  obligation about that command's `EvalCommandE` step.
- `Procedure.checkAsPredicate_of_exprEq` — transfers the reading of a captured check to
  another clause with the same expression.
- `assertionsValid_defaultAssertEvents` — turns non-`free` contract clauses that hold in
  every world into a valid assertion-event trace.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare


/-- A snapshot of a procedure's non-`free` contract clauses as `assert` events is
assertion-valid whenever every such clause holds in every world. -/
theorem assertionsValid_defaultAssertEvents
    (conditionInterp : ConditionInterp Expression)
    (fac : Expression.Factory) (σ : CoreStore)
    (checks : ListMap CoreLabel Procedure.Check)
    (h : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ checks.toList → check.attr = Procedure.CheckAttr.Default →
      ∀ world, conditionInterp.holds world
        { factory := fac, store := σ, label := label, expr := check.expr,
          metadata := check.md }) :
    Trace.AssertionsValid Expression conditionInterp
      (defaultAssertEvents fac σ checks) := by
  have key : ∀ (l : List (CoreLabel × Procedure.Check)) (acc : Trace Expression),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ l → check.attr = Procedure.CheckAttr.Default →
        ∀ world, conditionInterp.holds world
          { factory := fac, store := σ, label := label, expr := check.expr,
            metadata := check.md }) →
      Trace.AssertionsValidFromP Expression conditionInterp (fun _ => True) acc
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
      · rw [ite_eq_left hattr]
        exact ⟨fun _ world _ => hl lc.1 lc.2 List.mem_cons_self hattr world,
          ih acc (fun label check hmem => hl label check (List.mem_cons_of_mem _ hmem))⟩
      · rw [ite_eq_right hattr]
        exact ih acc (fun label check hmem => hl label check (List.mem_cons_of_mem _ hmem))
  exact key checks.toList [] h

/-- Transfer the reading of a captured check to another clause with the same
    expression, given that the environment's runtime factory is over `factory`. -/
theorem Procedure.checkAsPredicate_of_exprEq
    {factory : Lambda.Factory CoreLParams}
    {ρ : Imperative.Env Expression} {label' : CoreLabel} {check' : Procedure.Check}
    (label : CoreLabel) (check : Procedure.Check)
    (hfac : ρ.factory.factory = factory) (hexpr : check'.expr = check.expr)
    (h : Procedure.checkAsPredicate factory ρ label' check') :
    Procedure.checkAsPredicate factory ρ label check := by
  intro world
  rcases h world with ⟨hf, hd⟩ | ⟨hne, _⟩
  · exact Or.inl ⟨hf, hexpr ▸ hd⟩
  · exact absurd hfac hne

/-- Build a `contractTriple` from the name lookup, body, and body judgement.
    The factory, old-inout, and input-typing clauses of `contractTriple`'s
    precondition are discarded by weakening, so the body proof needs only the
    preconditions. -/
theorem Procedure.contractTriple_of (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (Procedure.preAsPredicate (p.factoryBeforeProcedure procName) proc)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName)) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, hchecksTyped, by
    rw [hbody]
    exact Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
      h (fun _ hc => hc.1) (fun _ hpost => hpost)⟩

/-- Build a `contractTriple` whose body proof may assume the concrete factory and
    old-inout relation but does not need runtime input-value typing. The separate
    `hchecksTyped` argument discharges `contractTriple`'s static requirement that each
    contract clause type-check as `bool`. -/
theorem Procedure.contractTriple_of_core (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (fun ρ => Procedure.preAsPredicate (p.factoryBeforeProcedure procName) proc ρ ∧
          ρ.factory.factory = p.factoryBeforeProcedure procName ∧
          Procedure.oldInoutAsPredicate proc ρ)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName)) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, hchecksTyped, by
    rw [hbody]
    exact Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
      h (fun _ hc => ⟨hc.1, hc.2.1, hc.2.2.1⟩) (fun _ hpost => hpost)⟩

/-- Build a `contractTriple` while retaining every entry fact, including values
    matching the types of the procedure's input and inout formals. -/
theorem Procedure.contractTriple_of_core_typed (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (Procedure.contractPre (p.factoryBeforeProcedure procName) proc)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName)) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, hchecksTyped, by rw [hbody]; exact h⟩

/-- A contract whose every non-`free` `ensures` is literally one of the
    `requires` is met by an empty body: nothing runs, so the precondition still
    holds at the end. -/
theorem Procedure.contractTriple_nil (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [])
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (himp : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ∃ (label' : CoreLabel) (check' : Procedure.Check),
        (label', check') ∈ proc.spec.preconditions.toList ∧ check'.expr = check.expr) :
    Procedure.contractTriple p params procName := by
  refine Procedure.contractTriple_of_core_typed p params procName proc [] hproc hbody hchecksTyped
    ?_
  refine Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
    (Core.Logic.Hoare.skip (factory := p.factoryBeforeProcedure procName)
      p.findProcByString? params "" #[]
      (Procedure.contractPre (p.factoryBeforeProcedure procName) proc))
    (fun _ hc => hc)
    (fun ρ hc label check hmem hattr => ?_)
  obtain ⟨label', check', hmem', hexpr⟩ := himp label check hmem hattr
  exact Procedure.checkAsPredicate_of_exprEq label check hc.2.1 hexpr
    (hc.1 label' check' hmem')


/-- An empty body meets a contract whose non-`free` `ensures` clauses are all among its
    `requires`, with the containment settled by the decidable `ensuresAmongRequires`. -/
theorem Procedure.contractTriple_nil_of_ensuresAmongRequires
    (p : Core.Program) (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [])
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Procedure.ensuresAmongRequires proc = Bool.true) :
    Procedure.contractTriple p params procName := by
  refine Procedure.contractTriple_nil p params procName proc hproc hbody hchecksTyped
    (fun label check hmem hattr => ?_)
  simp only [Procedure.ensuresAmongRequires, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h (label, check) hmem with hattr' | ⟨lc', hmem', hexpr⟩
  · exact absurd hattr hattr'
  · exact ⟨lc'.1, lc'.2, hmem', hexpr⟩


/-- A one-command body wrapped in its procedure block.  Mirrors the composition the
    structured `block`/`cmd` rules perform. -/
private theorem triple_block_singleton_cmd
    (π : String → Option Procedure) (factory : Lambda.Factory CoreLParams)
    (params : InitEnvWFParams) (c : Command)
    (Pre Post : Imperative.Env Expression → Prop)
    (hcmd : ∀ ρ₀ σ' emitted, Pre ρ₀ → InitEnvWF params (Stmt.cmd c) ρ₀ →
      EvalCommandE π ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid Expression (DenoteBasedInterp factory) emitted ∧
        (Trace.Reachable Expression (DenoteBasedInterp factory) emitted →
          Post { ρ₀ with store := σ' }))
    (hpost_proj : Imperative.Logic.Hoare.PostWF [Imperative.Stmt.cmd c] Post) :
    Triple π params Pre [Imperative.Stmt.block "" [Stmt.cmd c] #[]] Post
      (factory := factory) :=
  Imperative.Logic.Hoare.singleton (EvalCommandE π)
    InitEnvWF BlockInitEnvWF params params
    (fun _ hb => blockInitEnvWF_singleton hb)
    (Imperative.Logic.Hoare.block (EvalCommandE π)
      InitEnvWF BlockInitEnvWF params params
      (fun he hn hnd => evalCommandE_preserves_none_of_not_def π he hn hnd)
      (fun _ hb => blockInitEnvWF_of_block hb)
      (fun _ hb => blockInitEnvWF_bodyDefsUndefined (blockInitEnvWF_of_block hb))
      (Imperative.Logic.Hoare.singleton (EvalCommandE π)
        InitEnvWF BlockInitEnvWF params params
        (fun _ hb => blockInitEnvWF_singleton hb)
        (Imperative.Logic.Hoare.cmd (EvalCommandE π)
          InitEnvWF params c Pre Post hcmd))
      hpost_proj)


/-- **A one-command body.** The `cmd` rule reduces a contract over `[.cmd c]` to a
    single semantic obligation about `c`. -/
theorem Procedure.contractTriple_singleton_cmd (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc) (c : Command)
    (hbody : proc.body = .structured [Stmt.cmd c])
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (hsem : ∀ ρ₀ σ' emitted,
      Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ₀ →
      InitEnvWF params (Stmt.cmd c) ρ₀ →
      EvalCommandE p.findProcByString? ρ₀.factory ρ₀.store c σ' emitted →
      Trace.AssertionsValid Expression
          (DenoteBasedInterp (p.factoryBeforeProcedure procName)) emitted ∧
        (Trace.Reachable Expression
            (DenoteBasedInterp (p.factoryBeforeProcedure procName)) emitted →
          Procedure.contractPost (p.factoryBeforeProcedure procName) proc
            { ρ₀ with store := σ' }))
    (hpost_proj : Imperative.Logic.Hoare.PostWF [Imperative.Stmt.cmd c]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)) :
    Procedure.contractTriple p params procName :=
  Procedure.contractTriple_of_core_typed p params procName proc _ hproc hbody hchecksTyped
    (triple_block_singleton_cmd p.findProcByString? _ params c
      (Procedure.contractPre (p.factoryBeforeProcedure procName) proc)
      (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
      hsem hpost_proj)


end Hoare

end Core.Logic

end -- public section

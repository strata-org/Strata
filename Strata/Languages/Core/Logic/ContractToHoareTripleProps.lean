/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTriple
import all Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.ProcedureProps

/-! # Discharging a procedure's contract

Ways to establish a `Procedure.contractTriple`, and the bridges that make a concrete
procedure's contract decidable. The definitions being established live in
`Strata.Languages.Core.Logic.ContractToHoareTriple`.

## Key results

- `Procedure.contractTriple_of` — supplies the procedure and body, discharging the
  name lookup and the `.structured` obligation once.
- `Procedure.contractTriple_of_core` and `Procedure.contractTriple_of_core_typed` —
  retain the concrete Core entry facts needed by evaluator-sensitive body proofs.
- `Procedure.contractTriple_of_core_typed_axioms`: also retains the axioms and
  `distinct` declarations visible to the procedure.
- `Procedure.contractTriple_nil` and
  `Procedure.contractTriple_nil_of_ensuresAmongRequires` — an empty body meets a
  contract whose non-`free` `ensures` clauses are all among its `requires`.
- `Procedure.contractTriple_singleton_cmd` — a one-command body, reduced to a single
  obligation about that command's `EvalCommandE` step.
- `Procedure.contractTripleTotal_of_core_typed` — supplies the procedure and body of a
  total-correctness contract, discharging the name lookup and the `.structured` obligation.
- `Procedure.contractTriple_of_contractTripleTotal` — a total-correctness contract gives the
  partial-correctness one.
- `Procedure.contractTripleTotal_iff` — a total-correctness contract is a partial-correctness
  contract and termination with valid assertions of the body
  (`Procedure.bodyTerminatesAndAssertsValid`), for either body kind.
- `Procedure.checkAsPredicate_of_exprEq` — transfers the reading of a captured check to
  another clause with the same expression.
- `assertionsValid_defaultAssertEvents` — turns non-`free` contract clauses that hold in
  every world into a valid assertion-event trace.
- `Procedure.inputAsPredicate_int`, `Procedure.outputAsPredicate_int` — an `int` input or
  output holds an integer at a well-formed entry satisfying the input or output typing;
  `Procedure.outputAsPredicate_of_no_outputs` — a procedure without outputs has its output
  typing everywhere; `Procedure.valueOfTy_of_valueHasType` — a value whose sort is a formal's
  type has that type.
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

/-- For a procedure without type parameters, build a `contractTriple` from the name lookup, body,
    and body judgement. The factory, old-inout, input- and output-typing, and axiom clauses of
    `contractTriple`'s precondition are discarded by weakening, so the body proof needs only the
    preconditions. -/
theorem Procedure.contractTriple_of (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (Procedure.preAsPredicate (p.factoryBeforeProcedure procName) proc)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, Procedure.forall_instance_of_typeArgs_nil hmono ⟨hchecksTyped, by
    rw [hbody]
    exact Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
      h (fun _ hc => hc.1.1) (fun _ hpost => hpost)⟩⟩

/-- For a procedure without type parameters, build a `contractTriple` whose body proof may assume
    the concrete factory and old-inout relation but does not need runtime input- or output-value
    typing. The separate `hchecksTyped` argument discharges `contractTriple`'s static requirement
    that each contract clause type-check as `bool`. -/
theorem Procedure.contractTriple_of_core (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (fun ρ => Procedure.preAsPredicate (p.factoryBeforeProcedure procName) proc ρ ∧
          ρ.factory.factory = p.factoryBeforeProcedure procName ∧
          Procedure.oldInoutAsPredicate proc ρ)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, Procedure.forall_instance_of_typeArgs_nil hmono ⟨hchecksTyped, by
    rw [hbody]
    exact Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
      h (fun _ hc => ⟨hc.1.1, hc.1.2.1, hc.1.2.2.1⟩) (fun _ hpost => hpost)⟩⟩

/-- For a procedure without type parameters, build a `contractTriple` while retaining every entry
    fact: the contract precondition, including values matching the types of the procedure's input,
    inout and output formals, and the axioms and `distinct` declarations visible to the
    procedure. -/
theorem Procedure.contractTriple_of_core_typed_axioms (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (fun ρ => Procedure.contractPre (p.factoryBeforeProcedure procName) proc ρ ∧
          Core.Specification.AxiomsBeforeProcedureDecl procName p ρ)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName :=
  ⟨proc, hproc, Procedure.forall_instance_of_typeArgs_nil hmono
    ⟨hchecksTyped, by rw [hbody]; exact h⟩⟩

/-- For a procedure without type parameters, build a `contractTriple` while retaining every fact of
    the contract precondition, including values matching the types of the procedure's input, inout
    and output formals. The axioms visible to the procedure are discarded by weakening;
    `Procedure.contractTriple_of_core_typed_axioms` retains them. -/
theorem Procedure.contractTriple_of_core_typed (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Triple p.findProcByString? params
        (Procedure.contractPre (p.factoryBeforeProcedure procName) proc)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName :=
  Procedure.contractTriple_of_core_typed_axioms p params procName proc bss hproc hbody
    hchecksTyped
    (Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
      h (fun _ hc => hc.1) (fun _ hpost => hpost)) hmono

/-- For a procedure without type parameters, build a `contractTripleTotal` for a structured body
    from the name lookup, the body, and the body's total triple from entries satisfying the contract
    precondition. The axioms visible to the procedure are discarded by weakening. -/
theorem Procedure.contractTripleTotal_of_core_typed (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (bss : Statements)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : HoareTotal.Triple p.findProcByString? params
        (Procedure.contractPre (p.factoryBeforeProcedure procName) proc)
        [Imperative.Stmt.block "" bss #[]]
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
        (factory := p.factoryBeforeProcedure procName))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTripleTotal p params procName :=
  ⟨proc, hproc, Procedure.forall_instance_of_typeArgs_nil hmono ⟨hchecksTyped, by
    rw [hbody]
    exact HoareTotal.consequence p.findProcByString? params
      h (fun _ hc => hc.1) (fun _ hpost => hpost)⟩⟩

/-- **A total-correctness contract gives the partial-correctness contract.**  Both read
    the same precondition and postcondition, and a total triple gives the partial one. -/
theorem Procedure.contractTriple_of_contractTripleTotal {p : Core.Program}
    {params : InitEnvWFParams} {procName : String}
    (h : Procedure.contractTripleTotal p params procName) :
    Procedure.contractTriple p params procName := by
  obtain ⟨proc₀, hproc, hinsts⟩ := h
  refine ⟨proc₀, hproc, fun tys proc hinst => ?_⟩
  obtain ⟨hchecksTyped, htriple⟩ := hinsts tys proc hinst
  refine ⟨hchecksTyped, ?_⟩
  cases hbody : proc.body with
  | structured bss =>
    rw [hbody] at htriple
    exact Strata.Logic.HoareTotal.TripleWith.to_partial htriple
  | cfg cfg =>
    rw [hbody] at htriple
    exact fun ρEntry => Strata.Logic.HoareTotal.TripleWith.to_partial (htriple ρEntry)
  | abstract => trivial

/-- **A total-correctness contract is a partial-correctness contract and termination.**
    For either body kind, `contractTripleTotal` holds exactly when `contractTriple` does and
    the body terminates with valid assertions from every admitted entry satisfying the
    precondition. -/
theorem Procedure.contractTripleTotal_iff (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) :
    Procedure.contractTripleTotal p params procName ↔
      Procedure.contractTriple p params procName ∧
        Procedure.bodyTerminatesAndAssertsValid p params procName := by
  constructor
  · intro h
    refine ⟨Procedure.contractTriple_of_contractTripleTotal h, ?_⟩
    obtain ⟨proc₀, hproc, hinsts⟩ := h
    refine ⟨proc₀, hproc, fun tys proc hinst => ?_⟩
    obtain ⟨-, htriple⟩ := hinsts tys proc hinst
    cases hbody : proc.body with
    | structured bss =>
      rw [hbody] at htriple
      exact fun ρ hpre hinit => (htriple ρ hpre hinit).1
    | cfg cfg =>
      rw [hbody] at htriple
      exact fun ρ hpre hinit => (htriple ρ ρ ⟨hpre, rfl⟩ hinit).1
    | abstract => trivial
  · rintro ⟨⟨proc₀, hproc, hinsts⟩, proc₀', hproc', hterms⟩
    obtain rfl : proc₀' = proc₀ := Option.some.inj (hproc'.symm.trans hproc)
    refine ⟨proc₀', hproc, fun tys proc' hinst => ?_⟩
    obtain ⟨hchecksTyped, htriple⟩ := hinsts tys proc' hinst
    have hterm := hterms tys proc' hinst
    refine ⟨hchecksTyped, ?_⟩
    cases hbody : proc'.body with
    | structured bss =>
      rw [hbody] at htriple hterm
      exact fun ρ hpre hinit =>
        ⟨hterm ρ hpre hinit, (htriple ρ hpre hinit).2⟩
    | cfg cfg =>
      rw [hbody] at htriple hterm
      exact fun ρEntry ρ hpre hinit =>
        ⟨hterm ρ hpre.1 hinit, (htriple ρEntry ρ hpre hinit).2⟩
    | abstract => trivial

/-- A contract of a procedure without type parameters whose every non-`free` `ensures` is
    literally one of the `requires` is met by an empty body: nothing runs, so the precondition still
    holds at the end. -/
theorem Procedure.contractTriple_nil (p : Core.Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [] opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (himp : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      ∃ (label' : CoreLabel) (check' : Procedure.Check),
        (label', check') ∈ proc.spec.preconditions.toList ∧ check'.expr = check.expr)
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName := by
  refine Procedure.contractTriple_of_core_typed p params procName proc [] hproc hbody
    hchecksTyped (hmono := hmono) ?_
  refine Strata.Logic.Hoare.consequence (EventLang.coreBlock p.findProcByString?) params
    (Core.Logic.Hoare.skip (factory := p.factoryBeforeProcedure procName)
      p.findProcByString? params "" #[]
      (Procedure.contractPre (p.factoryBeforeProcedure procName) proc))
    (fun _ hc => hc)
    (fun ρ hc label check hmem hattr => ?_)
  obtain ⟨label', check', hmem', hexpr⟩ := himp label check hmem hattr
  exact Procedure.checkAsPredicate_of_exprEq label check hc.2.1 hexpr
    (hc.1 label' check' hmem')


/-- An empty body of a procedure without type parameters meets a contract whose non-`free` `ensures`
    clauses are all among its `requires`, with the containment settled by the decidable
    `ensuresAmongRequires`. -/
theorem Procedure.contractTriple_nil_of_ensuresAmongRequires
    (p : Core.Program) (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [] opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (h : Procedure.ensuresAmongRequires proc = Bool.true)
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName := by
  refine Procedure.contractTriple_nil p params procName proc hproc hbody hchecksTyped
    (hmono := hmono)
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


/-- **A one-command body.** For a procedure without type parameters, the `cmd` rule reduces a
    contract over `[.cmd c]` to a single semantic obligation about `c`. -/
theorem Procedure.contractTriple_singleton_cmd (p : Core.Program)
    (params : InitEnvWFParams) (procName : String) (proc : Procedure)
    (hproc : p.findProcByString? procName = some proc) (c : Command)
    (hbody : proc.body = .structured [Stmt.cmd c] opq)
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
        (Procedure.contractPost (p.factoryBeforeProcedure procName) proc))
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName :=
  Procedure.contractTriple_of_core_typed p params procName proc _ hproc hbody hchecksTyped
    (hmono := hmono) (triple_block_singleton_cmd p.findProcByString? _ params c
      (Procedure.contractPre (p.factoryBeforeProcedure procName) proc)
      (Procedure.contractPost (p.factoryBeforeProcedure procName) proc)
      hsem hpost_proj)


/-- An input of type `int` holds an integer of the runtime factory at an entry with a
    well-formed store satisfying the procedure's input typing. -/
theorem Procedure.inputAsPredicate_int {proc : Procedure} {ρ : Imperative.Env Expression}
    (hwf : Imperative.WellFormedStore ρ.store ρ.factory)
    (hin : Procedure.inputAsPredicate proc ρ) (x : Expression.Ident)
    (hx : (x, Lambda.LMonoTy.int) ∈ proc.header.inputs.toList) :
    ∃ k, ρ.store x = some (Lambda.SemValue.ofInt ρ.factory.model.tcInterp k) := by
  obtain ⟨w, hw, hty⟩ := hin x _ hx
  obtain ⟨k, hk⟩ := Lambda.SemValue.exists_ofInt hty
  exact ⟨k, by rw [hw, hk, hwf x w hw]⟩

/-- A procedure without outputs has its output typing in every environment. -/
theorem Procedure.outputAsPredicate_of_no_outputs {proc : Procedure}
    (ρ : Imperative.Env Expression) (h : proc.header.outputs.toList = []) :
    Procedure.outputAsPredicate proc ρ := fun _ _ hmem => by
  rw [h] at hmem
  cases hmem

/-- An output of type `int` holds an integer of the runtime factory in an environment with a
    well-formed store satisfying the procedure's output typing. -/
theorem Procedure.outputAsPredicate_int {proc : Procedure} {ρ : Imperative.Env Expression}
    (hwf : Imperative.WellFormedStore ρ.store ρ.factory)
    (hout : Procedure.outputAsPredicate proc ρ) (x : Expression.Ident)
    (hx : (x, Lambda.LMonoTy.int) ∈ proc.header.outputs.toList) :
    ∃ k, ρ.store x = some (Lambda.SemValue.ofInt ρ.factory.model.tcInterp k) := by
  obtain ⟨w, hw, hty⟩ := hout x _ hx
  obtain ⟨k, hk⟩ := Lambda.SemValue.exists_ofInt hty
  exact ⟨k, by rw [hw, hk, hwf x w hw]⟩

/-- A value of the runtime factory whose sort is `ty` (`Procedure.valueHasType`) has the type
    `ty`. -/
theorem Procedure.valueOfTy_of_valueHasType {f : Expression.Factory} {v : Expression.Val}
    {ty : Lambda.LMonoTy} (hv : Imperative.HasVal.value f v)
    (h : Procedure.valueHasType ty v) :
    Imperative.HasVal.valueOfTy f v (.forAll [] ty) :=
  ⟨hv, by rw [← h]; rfl⟩

end Hoare

end Core.Logic

end -- public section

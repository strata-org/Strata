/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
public import Strata.Languages.Core.InterpreterReachProps
import all Strata.Languages.Core.Logic.ContractToHoareTriple

/-! # Contracts proved by running the body

A straight-line body whose values are all literals can be run with Core's concrete evaluator
(`Core.runLits`, in `InterpreterReach`, with its soundness in `InterpreterReachProps`). This
module relates that run to the program logic: it turns the run into a Hoare triple of
`Core.Logic.Hoare`, and into a proof of the procedure's contract when the postconditions evaluate
to `true` over the literals the run ends with.

## Why this module is in `Logic/` while importing the interpreter

The other modules of `Core/Logic/` (the Hoare logic, its language definition, the contract
triples, the factory and trace interpretations) import no interpreter module, so the program
logic and its soundness do not depend on the interpreter. This module is the one exception. It
belongs in `Logic/` because what it states is program logic: triples (`runLits_triple`) and
contracts (`Procedure.contractTriple_of_meetsContractOnLits`) in `Core.Logic.Hoare`. It
imports the interpreter only to use the run as evidence for them. The exception stays harmless
as long as the module is a leaf of `Logic/`: no other `Logic/` module may import it, so the rest
of `Logic/` stays independent of the interpreter. Results that relate the interpreter to the
logic belong here; results the logic itself needs do not.

Key results:
- `runLits_triple` — a run of a body by `runLits` from `bs` to `bs'` is a triple from the
  environments holding `bs` to those holding `bs'`.
- `Procedure.contractTriple_of_meetsContractOnLits` — a procedure over `Core.Factory` whose body
  runs to a state where its postconditions evaluate to `true` (`Procedure.meetsContractOnLits`)
  meets its contract.
-/

public section

namespace Core.Logic

open Core Imperative Strata.Logic Imperative.Logic

namespace Hoare

/-! ## Contracts of straight-line bodies over literals

A body that `Core.runLits` runs, over literals, to a state where its postconditions evaluate to
`true` meets its contract. -/

/-- The assertion `runLits_triple` carries: the runtime factory is over `Core.Factory` and the
    store holds the literals of `bs`. -/
@[expose] def LitState (bs : LitBinds) (ρ : Imperative.Env Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ LitBinds.Holds ρ.factory.model.tcInterp ρ.store bs

/-- A statement `stepLit` runs is a command, so it exits no block. -/
private theorem exitsCovered_of_stepLit {fuel : Nat} {bs bs' : LitBinds} (s : Statement)
    (h : stepLit fuel bs s = some bs') :
    Imperative.Block.exitsCoveredByBlocks (P := Expression) (CmdT := Command) [] [s] := by
  unfold stepLit at h
  split at h
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩
  · cases h

/-- A command step `stepLit` takes from `bs` to `bs'` is a triple from the environments holding
    `bs` to those holding `bs'`. -/
private theorem stepLit_triple (π : String → Option Procedure) (params : InitEnvWFParams)
    {fuel : Nat} {bs bs' : LitBinds} {s : Statement} (h : stepLit fuel bs s = some bs') :
    Triple π params (LitState bs) [s] (LitState bs') := by
  unfold stepLit at h
  split at h
  · rename_i x e md
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact set π params x e md _ _ fun ρ₀ σ' v hpre hev hup => by
      have hv := Option.some.inj (hev.symm.trans (eval_of_evalLit hpre.1 hpre.2 hc))
      subst hv
      cases hup with
      | update _ hnew hoth => exact ⟨hpre.1, hpre.2.set hnew hoth⟩
  · rename_i x ty e md
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
    exact init π params x ty e md _ _ fun ρ₀ σ' v hpre hev hinit => by
      have hv := Option.some.inj (hev.symm.trans (eval_of_evalLit hpre.1 hpre.2 hc))
      subst hv
      cases hinit with
      | init _ hnew hoth => exact ⟨hpre.1, hpre.2.set hnew hoth⟩
  · cases h

/-- **Straight-line code over literals.**  A run of a body that `runLits` takes from `bs` to
    `bs'` is a triple from the environments holding `bs` to those holding `bs'`. -/
theorem runLits_triple (π : String → Option Procedure) (params : InitEnvWFParams)
    (fuel : Nat) {bs' : LitBinds} :
    ∀ (ss : Statements) (bs : LitBinds), runLits fuel bs ss = some bs' →
      Triple π params (LitState bs) ss (LitState bs')
  | [], bs, h => by
    simp only [runLits, Option.some.injEq] at h
    subst h
    exact Imperative.Logic.Hoare.skip_block (EvalCommandE π) BlockInitEnvWF params _
  | s :: ss, bs, h => by
    obtain ⟨bs₁, h₁, hrun⟩ := Option.bind_eq_some_iff.mp h
    exact seq π params (ss₁ := [s]) (stepLit_triple π params h₁)
      (runLits_triple π params fuel ss bs₁ hrun) (exitsCovered_of_stepLit s h₁)

/-- The literals of `bs` whose names the body `ss` does not declare: what survives leaving the
    procedure block. -/
@[expose] def keepUndeclared (ss : Statements) (bs : LitBinds) : LitBinds :=
  bs.filter fun b =>
    !(Imperative.Block.definedVars (P := Expression) (C := Command) ss true).contains b.1

/-- Leaving the block of `ss` keeps the literals of the names `ss` does not declare. -/
private theorem postWF_keepUndeclared (ss : Statements) (bs : LitBinds) :
    Imperative.Logic.Hoare.PostWF ss (LitState (keepUndeclared ss bs)) := by
  intro ρ ⟨hfac, hρ⟩
  refine ⟨hfac, fun b hb => ?_⟩
  have hnd : b.1 ∉ Imperative.Block.definedVars (P := Expression) (C := Command) ss true := by
    intro hmem
    simp only [keepUndeclared, List.mem_filter, List.contains_iff_mem.mpr hmem,
      Bool.not_true] at hb
    cases hb.2
  show Imperative.dropVars _ ρ.store b.1 = _
  simp only [Imperative.dropVars, ite_eq_right_iff.mpr (fun h => absurd h hnd)]
  exact hρ b hb

/-- Every non-`free` postcondition of `proc` evaluates to `true` over the literals of `bs`.
    Only `Default` postconditions are checked: a contract asks the body to establish those,
    while a free postcondition is only assumed by callers. -/
@[expose] def Procedure.ensuresHoldOnLits (fuel : Nat) (bs : LitBinds) (proc : Procedure) :
    Bool :=
  proc.spec.postconditions.toList.all fun lc =>
    decide (lc.2.attr ≠ Procedure.CheckAttr.Default) ||
      evalLit fuel bs lc.2.expr == some (.boolConst true)

/-- The postconditions `ensuresHoldOnLits` evaluates to `true` hold in every environment holding
    `bs`. -/
private theorem Procedure.contractPost_of_ensuresHoldOnLits {fuel : Nat} {bs : LitBinds}
    {proc : Procedure} (h : Procedure.ensuresHoldOnLits fuel bs proc = Bool.true)
    {ρ : Imperative.Env Expression} (hρ : LitState bs ρ) :
    Procedure.contractPost Core.Factory proc ρ := by
  intro label check hmem hattr world
  simp only [Procedure.ensuresHoldOnLits, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h (label, check) hmem with hne | hev
  · exact absurd hattr hne
  · exact .inl ⟨hρ.1, eval_of_evalLit hρ.1 hρ.2 hev⟩

/-- Whether the body `bss` of `proc` runs over literals from no bindings (`runLits`) to a state
    whose literals, those that survive leaving the procedure block, satisfy the postconditions.

    Starting from no bindings loses nothing. A body that reads an input finds no literal for it,
    so `evalLit` declines, `runLits` returns `none` and the check is `false`. A body that reads
    no input ends in the same literals from every entry store. So when the check succeeds, the
    triple holds without assuming the preconditions, which is stronger than what
    `Procedure.contractTriple` asks for. -/
@[expose] def Procedure.meetsContractOnLits (fuel : Nat) (proc : Procedure) (bss : Statements) :
    Bool :=
  match runLits fuel [] bss with
  | some bs => Procedure.ensuresHoldOnLits fuel (keepUndeclared bss bs) proc
  | none => false

/-- **A contract proved by running the body.** A procedure of `p` without type parameters, over
    `Core.Factory`, whose straight-line body runs over literals to a state where its postconditions
    evaluate to `true` (`meetsContractOnLits`) meets its contract. -/
theorem Procedure.contractTriple_of_meetsContractOnLits (p : Program) (params : InitEnvWFParams)
    (procName : String) (proc : Procedure) (bss : Statements) (fuel : Nat)
    (hproc : p.findProcByString? procName = some proc)
    (hbody : proc.body = .structured bss opq)
    (hchecksTyped : Procedure.contractChecksTyped proc)
    (hfac : p.factoryBeforeProcedure procName = Core.Factory)
    (hchk : Procedure.meetsContractOnLits fuel proc bss = Bool.true)
    (hmono : proc.header.typeArgs = [] := by first | rfl | decide) :
    Procedure.contractTriple p params procName := by
  unfold Procedure.meetsContractOnLits at hchk
  split at hchk
  · rename_i bs hrun
    refine Procedure.contractTriple_of_core p params procName proc bss hproc hbody
      hchecksTyped (hmono := hmono) ?_
    rw [hfac]
    exact consequence p.findProcByString? params
      (block p.findProcByString? params
        (consequence p.findProcByString? params
          (runLits_triple p.findProcByString? params fuel bss [] hrun)
          (fun _ h => ⟨h.2.1, fun _ hb => nomatch hb⟩)
          (fun _ h => ⟨h.1, fun b hb => h.2 b (List.mem_filter.mp hb).1⟩))
        (postWF_keepUndeclared bss bs))
      (fun _ h => h) (fun _ h => Procedure.contractPost_of_ensuresHoldOnLits hchk h)
  · cases hchk

end Hoare

end Core.Logic

end -- public section

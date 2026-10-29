/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LStateProps
import Strata.DL.Imperative.StmtSemanticsProps
import StrataDDM.Integration.Lean.HashCommands

/-! # Reading a Core procedure's contract as a Hoare triple

Each test below writes a Core program in DDM syntax, translates it to
the Core AST, and then reads the procedure's `requires`/`ensures` as the
pre/postcondition of a `Core.Logic.Hoare` triple via
`Procedure.contractTriple`. Eleven procedures are *proved* to meet their contracts and
two are *disproved*.  The bodies range from empty — where the triple is settled
structurally, with no reasoning about individual statements — up to `assume`/`assert`,
if-then-else, a labelled block, a block left by an `exit`, a `while` loop that terminates
(a counting loop `while (int.le(y, 9)) { y := int.add(y, 1) }`, verified to its result
`y == 10` using the concrete `Core.Factory` arithmetic the precondition pins), and a
`while` loop that diverges (a `true` guard) and so meets `ensures false`
vacuously under partial correctness. Another example shows why the contract is read over
the body *wrapped in its procedure block*: a postcondition naming a variable the body
declares fails `PostWF`.

**These tests use `native_decide`** for the steps that inspect a concrete translated
AST, because kernel reduction over one is impractically slow.  A step that can be
discharged without it should be.

This file also opens with focused *event-trace* and *rule-API* tests — assertion
validity, assumption satisfiability, and every `Core.Logic.Hoare` rule at its
expected type — before the contract scenarios below.  Under the event semantics the
triple is read over `StepStmtStarE`; the negative tests instantiate it at a concrete
completed run whose empty trace has satisfiable assumptions, so a refuted
postcondition is a genuine violation rather than a vacuous one.
-/

open Imperative
open StrataDDM (Program)
open Lambda.LExpr.SyntaxMono

namespace Strata

open CoreHoareTestSupport

private def trueCondition : EventArg Core.Expression :=
  { factory := Core.Factory
    store := fun _ => none
    label := "true"
    expr := HasBool.tt
    metadata := #[] }

private def falseCondition : EventArg Core.Expression :=
  { factory := Core.Factory
    store := fun _ => none
    label := "false"
    expr := HasBool.ff
    metadata := #[] }

/-- The captured `true` condition holds in every world of every Core model. -/
private theorem true_holds (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model) :
    (Core.Logic.DenoteBasedInterp model).holds world trueCondition := by
  refine .inl ⟨rfl, ?_⟩
  have hcap : Core.Logic.capturedExpr trueCondition
      = Lambda.LExpr.const () (Lambda.LConst.boolConst true) := rfl
  rw [hcap]
  refine ⟨Lambda.LExpr.typeCheck_to_HasTypeA (by rfl), ?_⟩
  exact Lambda.denote_boolConst _ _ _ _ _ _

/-- The captured `false` condition holds in no world of any Core model. -/
private theorem false_not_holds (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model) :
    ¬ (Core.Logic.DenoteBasedInterp model).holds world falseCondition := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · have hcap : Core.Logic.capturedExpr falseCondition
        = Lambda.LExpr.const () (Lambda.LConst.boolConst false) := rfl
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    exact Bool.false_ne_true ((Lambda.denote_boolConst _ _ _ _ _ _hty).symm.trans hd)
  · exact hne rfl

/-- An assumption can discharge a later assertion. -/
example (model : Lambda.Interp Core.Factory) :
    Trace.AssertionsValid Core.Expression (Core.Logic.DenoteBasedInterp model)
    [.assume falseCondition, .assert falseCondition] :=
  ⟨fun _ _ hassumptions => hassumptions falseCondition (by simp), True.intro⟩

/-- A later assumption cannot discharge an earlier assertion. -/
example (model : Lambda.Interp Core.Factory) :
    ¬ Trace.AssertionsValid Core.Expression (Core.Logic.DenoteBasedInterp model)
    [.assert falseCondition, .assume falseCondition] := by
  intro h
  exact false_not_holds model (someValuation model)
    (h.1 True.intro (someValuation model) (by intro condition hmem; simp at hmem))

/-- Empty Core blocks satisfy the skip triple using the real `StepStmtStarE`
semantics underlying `EventLang.coreBlock`. -/
example (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams) (Pre : Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π params Pre [] Pre :=
  fun _ =>
    Imperative.Logic.Hoare.skip_block (Core.EvalCommandE π)
      Core.Logic.BlockInitEnvWF params Pre

/-- The Core wrapper exposes false-precondition and consequence rules. -/
example (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams) (ss : Core.Statements)
    (Post : Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π params (fun _ => False) ss Post :=
  Core.Logic.Hoare.false_pre π params ss Post

/-! ## Rule API coverage -/

section RuleCoverage

variable (π : String → Option Core.Procedure)
variable (params : Core.Logic.InitEnvWFParams)

example {Pre Pre' Post Post' : Env Core.Expression → Prop} {ss : Core.Statements}
    (h : Core.Logic.Hoare.Triple π params Pre ss Post)
    (hpre : ∀ ρ, Pre' ρ → Pre ρ) (hpost : ∀ ρ, Post ρ → Post' ρ) :
    Core.Logic.Hoare.Triple π params Pre' ss Post' :=
  Core.Logic.Hoare.consequence π params h hpre hpost

example (command : Core.Command) (Pre Post : Env Core.Expression → Prop)
    (h : ∀ (model : Lambda.Interp Core.Factory) ρ₀ σ' emitted,
      Pre ρ₀ → Core.Logic.InitEnvWF params (.cmd command) ρ₀ →
      Core.EvalCommandE π ρ₀.factory ρ₀.store command σ' emitted →
      Trace.AssertionsValid Core.Expression (Core.Logic.DenoteBasedInterp model) emitted ∧
        (Trace.Reachable Core.Expression (Core.Logic.DenoteBasedInterp model) emitted →
          Post { ρ₀ with store := σ' })) :
    Core.Logic.Hoare.Triple π params Pre [.cmd command] Post :=
  Core.Logic.Hoare.cmd π params command Pre Post h

example (x : Core.Expression.Ident) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) (Pre Post : Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Env Core.Expression) (σ' : Core.CoreStore)
      (v : Core.Expression.Expr), Pre ρ₀ →
      Core.Expression.eval ρ₀.factory ρ₀.store e = some v →
      UpdateState Core.Expression ρ₀.store x v σ' → Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre [Core.Statement.set x e md] Post :=
  Core.Logic.Hoare.set π params x e md Pre Post hpost

example (x : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (e : Core.Expression.Expr) (md : MetaData Core.Expression)
    (Pre Post : Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Env Core.Expression) (σ' : Core.CoreStore)
      (v : Core.Expression.Expr), Pre ρ₀ →
      Core.Expression.eval ρ₀.factory ρ₀.store e = some v →
      InitState Core.Expression ρ₀.store x v σ' → Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre
      [Core.Statement.init x ty (.det e) md] Post :=
  Core.Logic.Hoare.init π params x ty e md Pre Post hpost

example {ss : Core.Statements} {label : String} {md : MetaData Core.Expression}
    {Pre Post : Env Core.Expression → Prop}
    (h : Core.Logic.Hoare.Triple π params Pre ss Post)
    (hpost : Imperative.Logic.Hoare.PostWF ss Post) :
    Core.Logic.Hoare.Triple π params Pre [.block label ss md] Post :=
  Core.Logic.Hoare.block π params h hpost

example (label : String) (md : MetaData Core.Expression)
    (Pre : Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π params Pre [.block label [] md] Pre :=
  Core.Logic.Hoare.skip π params label md Pre

example {condition : Core.Expression.Expr} {thenStmts elseStmts : Core.Statements}
    {md : MetaData Core.Expression} {Pre Post : Env Core.Expression → Prop}
    (hthen : Core.Logic.Hoare.Triple π params
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store condition = some HasBool.tt)
      thenStmts Post)
    (helse : Core.Logic.Hoare.Triple π params
      (fun ρ => Pre ρ ∧ Core.Expression.eval ρ.factory ρ.store condition = some HasBool.ff)
      elseStmts Post)
    (hthenWF : Imperative.Logic.Hoare.PostWF thenStmts Post)
    (helseWF : Imperative.Logic.Hoare.PostWF elseStmts Post) :
    Core.Logic.Hoare.Triple π params Pre
      [.ite (.det condition) thenStmts elseStmts md] Post :=
  Core.Logic.Hoare.ite π params hthen helse hthenWF helseWF

example {label : String} {md : MetaData Core.Expression} {ss : Core.Statements}
    (Pre : Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π params Pre (.exit label md :: ss) Pre :=
  Core.Logic.Hoare.exit_cons π params Pre

example {pfx sfx : Core.Statements} {Pre Mid Post : Env Core.Expression → Prop}
    (hpfx : Core.Logic.Hoare.Triple π params Pre pfx Mid)
    (hsfx : Core.Logic.Hoare.Triple π params Mid sfx Post)
    (hnoesc : Block.exitsCoveredByBlocks
      (P := Core.Expression) (CmdT := Core.Command) [] pfx) :
    Core.Logic.Hoare.Triple π params Pre (pfx ++ sfx) Post :=
  Core.Logic.Hoare.seq π params hpfx hsfx hnoesc

end RuleCoverage

/-- An empty-bodied loop exercises `while_rule` over the real event semantics.
The trivial invariant is preserved, the body emits no events, and loop exit
requires the guard to evaluate to false. -/
example (π : String → Option Core.Procedure)

    (params : Core.Logic.InitEnvWFParams) (guard : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Core.Logic.Hoare.Triple π params (fun _ => True)
      [.loop (.det guard) none [] [] md]
      (fun ρ => True ∧ Core.Expression.eval ρ.factory ρ.store guard = some HasBool.ff) :=
  Core.Logic.Hoare.while_rule π params
    (Core.Logic.Hoare.consequence π params
      (fun _ =>
        Imperative.Logic.Hoare.skip_block (Core.EvalCommandE π)
          Core.Logic.BlockInitEnvWF params
          (fun ρ => True ∧ Core.Expression.eval ρ.factory ρ.store guard = some HasBool.tt))
      (fun _ h => h) (fun _ _ => trivial))
    trivial
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by simp [Imperative.Block.definedVars]))


/-! ## Shared setup

The reusable helpers below take the procedure environment as a parameter, since they
hold for *every* one — none of these bodies makes a call or declares a function, so
neither the callee map nor the factory extension can affect the outcome.  The contract
theorems name their program instead, so the environment a call would resolve against is
that program's own `findProcByString?`.

Along the event step relation an empty-body run emits no events, and
`reachable_nil` below packages the fact that the empty trace's assumptions
are satisfiable — the premise the negative tests feed to the triple. -/


/-- Translate a DDM concrete-syntax program to the Core AST.  Each test stores the
    result in a `…PgmAST` definition, so that the procedure environment it passes to
    the logic is literally `Core.Program.findProcByString?` on an AST value — the
    same thing a real verification run uses. -/
private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- The procedure a `contractTriple` obligation hands you is the one the test's
    `…Proc` abbreviation names. -/
private theorem procOf_eq {p : Core.Program} {nm : String} {proc : Core.Procedure}
    (h : p.findProcByString? nm = some proc) : (p.findProcByString? nm).get! = proc := by
  rw [h]; rfl

/-- Gate parameters: no reserved fresh-prefixes, and every name counts as
    declared (so `factoryDeclared` is immediate). -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-! The evaluator diverges on a stuck expression — say `x == 1` with `x` unbound — so
`decide` / `native_decide` hang rather than return `none`.  The refutations below
therefore pick stores in which every clause reduces to a Boolean; refuting a contract
via a *stuck* clause needs a proof, not a computation. -/

private def xIs1Env : Imperative.Env Core.Expression :=
  { store := fun n => if n.name = "x" then some eb[#1] else none
    factory := Core.Factory
    hasFailure := false }

/-- `xIs1Env` holds only values: its single binding is the literal `1`, which is a
    value in every factory.  The well-formedness conditions require this of any
    environment a run starts from. -/
private theorem xIs1Env_storeWellDefined :
    Imperative.WellFormedStore xIs1Env.store Core.Factory := by
  intro n v hn
  show Lambda.LExpr.isValue _ v = true
  simp only [xIs1Env] at hn
  split at hn
  · injection hn with hv
    subst hv
    simp [Lambda.LExpr.isValue]
  · exact absurd hn (by simp)

/-- `xIs1Env` supplies the integer value required by a procedure whose only input
is `x : int`. -/
private theorem inputAsPredicate_xIs1 (proc : Core.Procedure)
    (hinputs : proc.header.inputs.toList =
      [(⟨"x", ()⟩, Lambda.LMonoTy.tcons "int" [])]) :
    Core.Logic.Hoare.Procedure.inputAsPredicate proc xIs1Env := by
  intro id ty hmem
  rw [hinputs] at hmem
  simp only [List.mem_singleton, Prod.mk.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  refine ⟨Lambda.LExpr.const () (.intConst 1), ?_, ?_⟩
  · simp [xIs1Env]
  · exact ⟨1, rfl⟩

/-- The block condition is immediate for an empty body: every clause that mentions
    the statements is vacuous, `Core.Factory` is well-formed, and the store holds
    only values. -/
private theorem blockWF_nil (ρ : Imperative.Env Core.Expression)
    (hfac : ρ.factory = Core.Factory)
    (hsv : Imperative.WellFormedStore ρ.store Core.Factory) :
    Core.Logic.BlockInitEnvWF testParams [Imperative.Stmt.block "" [] #[]] ρ :=
  Core.Logic.blockInitEnvWF_procBlock_nil (hfac.symm ▸ Core.coreFactory_WellFormedSemanticEval)
    (hfac.symm ▸ hsv) rfl (fun _ _ => rfl)

/-- An empty body, wrapped as the procedure block a body actually runs in, returns to
    its own environment: entering and leaving the block projects the store through
    itself.  Stated over the *event* step relation, the run emits no events. -/
private theorem run_procBlock_nil (π : String → Option Core.Procedure)
    (ρ : Imperative.Env Core.Expression) (l : String)
    (md : Imperative.MetaData Core.Expression) :
    Imperative.StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts [Imperative.Stmt.block l [] md] ρ) [] (.terminal ρ) := by
  have heq : ({ ρ with store := Imperative.projectStore ρ.store ρ.store }
      : Imperative.Env Core.Expression) = ρ := by
    simp [Imperative.projectStore_self]
  refine .step _ [] _ [] _ (.step_admin .step_stmts_cons) ?_
  refine .step _ [] _ [] _ (.step_admin (.step_seq_inner .step_block)) ?_
  refine .step _ [] _ [] _ (.step_admin (.step_seq_inner (.step_block_body .step_stmts_nil))) ?_
  refine .step _ [] _ [] _ (.step_admin (.step_seq_inner .step_block_done)) ?_
  refine .step _ [] _ [] _ (.step_admin .step_seq_done) ?_
  rw [heq]
  exact .step _ [] _ [] _ (.step_admin .step_stmts_nil) (.refl _)

/-- The empty trace is reachable. -/
private theorem reachable_nil (model : Lambda.Interp Core.Factory) :
    Trace.Reachable Core.Expression (Core.Logic.DenoteBasedInterp model) [] :=
  ⟨someValuation model, fun _ hc => absurd hc (by simp)⟩

/-- A procedure with no inout parameters satisfies `oldInoutAsPredicate` vacuously — its
    `getInoutParams` keys are empty, so there is no `old`/current pair to relate. -/
private theorem oldInoutAsPredicate_of_no_inout (proc : Core.Procedure)
    (ρ : Imperative.Env Core.Expression)
    (h : ListMap.keys proc.header.getInoutParams = []) :
    Core.Logic.Hoare.Procedure.oldInoutAsPredicate proc ρ := by
  intro id hid; rw [h] at hid; simp at hid

/-! The semantic clauses `preAsPredicate model` / `postAsPredicate model` read a contract
condition in *every* world of a model.  For an equality to a constant whose variable the
store binds, `capturedExpr` substitutes the binding, the clause becomes `κ == κ`, and
`denote_eq_true` settles it.  These helpers package that for pre- and postconditions. -/

/-- A clause `x == κ` holds in every world when the store binds `x` to `κ` and the
    ambient factory is `Core.Factory`. -/
private theorem checkAsPredicate_eqConst (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Core.Expression) (x : Core.Expression.Ident)
    (ty : Option Lambda.LMonoTy) (κ : Lambda.LConst)
    (hfac : ρ.factory = Core.Factory)
    (hstore : ρ.store x = some (Lambda.LExpr.const () κ))
    (label : Core.CoreLabel) (check : Core.Procedure.Check)
    (hexpr : check.expr =
      Lambda.LExpr.eq () (Lambda.LExpr.fvar () x ty) (Lambda.LExpr.const () κ)) :
    Core.Logic.Hoare.Procedure.checkAsPredicate model ρ label check := by
  intro world
  refine .inl ⟨hfac, ?_⟩
  have hcap : Core.Logic.capturedExpr
      { factory := ρ.factory, store := ρ.store, label := label,
        expr := check.expr, metadata := check.md }
      = Lambda.LExpr.eq () (Lambda.LExpr.const () κ) (Lambda.LExpr.const () κ) := by
    rw [hexpr]
    simp [Core.Logic.capturedExpr, Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hstore]
  rw [hcap]
  exact ⟨Lambda.LExpr.HasTypeA.eq Lambda.LExpr.HasTypeA.const Lambda.LExpr.HasTypeA.const,
    Lambda.denote_eq_true HList.nil Lambda.LExpr.HasTypeA.const
      Lambda.LExpr.HasTypeA.const
      (Lambda.LExpr.HasTypeA.eq Lambda.LExpr.HasTypeA.const Lambda.LExpr.HasTypeA.const) rfl⟩

/-- **From store facts to the semantic precondition.**  If every `requires` is `x == κ`
    for a listed `(x, κ)` bound by the store, the model's semantic precondition holds. -/
private theorem preAsPredicate_of_binds (model : Lambda.Interp Core.Factory)
    (proc : Core.Procedure) (ρ : Imperative.Env Core.Expression)
    (binds : List (Core.Expression.Ident × Option Lambda.LMonoTy × Lambda.LConst))
    (hfac : ρ.factory = Core.Factory)
    (hsyn : (proc.spec.preconditions.toList.all fun lc =>
      binds.any fun b => decide (lc.2.expr =
        Lambda.LExpr.eq () (Lambda.LExpr.fvar () b.1 b.2.1)
          (Lambda.LExpr.const () b.2.2))) = Bool.true)
    (hstore : ∀ b ∈ binds, ρ.store b.1 = some (Lambda.LExpr.const () b.2.2)) :
    Core.Logic.Hoare.Procedure.preAsPredicate model proc ρ := by
  intro label check hmem
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hsyn
  obtain ⟨b, hb, hexpr⟩ := hsyn (label, check) hmem
  exact checkAsPredicate_eqConst model ρ b.1 b.2.1 b.2.2 hfac (hstore b hb) label check hexpr

/-- A procedure with no `requires` satisfies the semantic precondition vacuously. -/
private theorem preAsPredicate_of_no_pre (model : Lambda.Interp Core.Factory)
    (proc : Core.Procedure) (ρ : Imperative.Env Core.Expression)
    (h : proc.spec.preconditions.toList = []) :
    Core.Logic.Hoare.Procedure.preAsPredicate model proc ρ := by
  intro label check hmem; rw [h] at hmem; simp at hmem

/-- A captured `1 == 2` cannot denote `true` in any world, since that would force
    `(1 : Int) = 2`. -/
private theorem not_denote_oneEqTwo (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.eq () (Lambda.LExpr.intConst () 1)
        (Lambda.LExpr.intConst () 2)) .bool)
    (htrue : (Lambda.LExpr.denote model.tcInterp model.opInterp world.freeVarVal
      world.tyVarVal .nil (Lambda.LExpr.eq () (Lambda.LExpr.intConst () 1)
        (Lambda.LExpr.intConst () 2)) .bool h : Bool) = true) : False := by
  cases h with
  | eq hleft hright =>
    have htyi := Lambda.HasTypeA.const_inv hleft
    cases htyi
    have heq := Lambda.denote_eq_true_implies_eq .nil hleft hright (.eq hleft hright) htrue
    have hd1 := Lambda.denote_intConst model.tcInterp model.opInterp world.freeVarVal
      world.tyVarVal .nil hleft
    have hd2 := Lambda.denote_intConst model.tcInterp model.opInterp world.freeVarVal
      world.tyVarVal .nil hright
    have : (1 : Int) = 2 := hd1.symm.trans (heq.trans hd2)
    exact absurd this (by decide)


/-! ## A procedure that meets its contract

`requires x == 1` and `ensures x == 1`: the body does nothing, so whatever the
precondition guaranteed on entry still holds on exit. -/

private def keepPgm : Program :=
#strata
program Core;

procedure Keep(x : int)
spec {
  requires x == 1;
  ensures x == 1;
}
{
};
#end

/--
info: program Core;

procedure Keep (x : int)
spec {
  requires [Keep_requires_0]: x == 1;
  ensures [Keep_ensures_1]: x == 1;
  } {

};
-/
-- `whitespace := lax`: the printer indents the blank line of an empty body, which a
-- source docstring cannot carry reliably.
#guard_msgs (whitespace := lax) in
#eval TransM.run Inhabited.default (translateProgram keepPgm) |>.fst

private def keepPgmAST : Core.Program := cstToAST keepPgm

private def keepProc : Core.Procedure :=
  (keepPgmAST.findProcByString? "Keep").get!

/-- The body really is empty. -/
example : keepProc.body = .structured [] := by native_decide

/-- **Valid.**  Every non-`free` `ensures` expression is literally one of the
    `requires`, so the contract holds of the empty body. -/
theorem keep_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple keepPgmAST testParams "Keep" :=
  Core.Logic.Hoare.Procedure.contractTriple_nil_of_ensuresAmongRequires
    keepPgmAST testParams "Keep" keepProc (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)


/-! ## A `free ensures` is not the body's obligation

`requires x == 1`, `ensures x == 1`, and `free ensures x == 99`.  The `free` clause is
*assumed* at call sites rather than proved by the body — exactly as
`Core.Specification.ProcedureAssertsValid` treats it — so `postAsPredicate` filters on
`check.attr = Default` and the contract holds of the empty body even though the
`free` clause is false. -/

private def freeOkPgm : Program :=
#strata
program Core;

procedure FreeOk(x : int)
spec {
  requires x == 1;
  ensures x == 1;
  free ensures x == 99;
}
{
};
#end

/--
info: program Core;

procedure FreeOk (x : int)
spec {
  requires [FreeOk_requires_0]: x == 1;
  ensures [FreeOk_ensures_1]: x == 1;
  free ensures [FreeOk_ensures_2]: x == 99;
  } {

};
-/
-- `whitespace := lax`: see the note on `keepPgm` above.
#guard_msgs (whitespace := lax) in
#eval TransM.run Inhabited.default (translateProgram freeOkPgm) |>.fst

private def freeOkPgmAST : Core.Program := cstToAST freeOkPgm

private def freeOkProc : Core.Procedure :=
  (freeOkPgmAST.findProcByString? "FreeOk").get!

/-- The spec really does contain a `free` clause, and it really is false at a store
    satisfying the `requires` — so the contract below holds *because* `free` clauses
    are excluded, not because every clause happens to be true.  Dropping the
    `= Default` guard in `postAsPredicate` would break `freeOk_meets_contract`. -/
example :
    (freeOkProc.spec.postconditions.toList.any fun lc =>
      decide (lc.2.attr = Core.Procedure.CheckAttr.Free) &&
        decide (Core.Expression.eval Core.Factory xIs1Env.store lc.2.expr ≠
          some (Imperative.HasBool.tt : Core.Expression.Expr))) = true := by
  native_decide

/-- **Valid.**  The one non-`free` `ensures` is among the `requires`. -/
theorem freeOk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple freeOkPgmAST testParams "FreeOk" :=
  Core.Logic.Hoare.Procedure.contractTriple_nil_of_ensuresAmongRequires
    freeOkPgmAST testParams "FreeOk" freeOkProc (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)


/-! ## A procedure that does not: an invalid `ensures`

`ensures x == 2` with no `requires` at all.  Run from a store where `x` holds
`1`, the (empty) precondition is satisfied and the empty body changes nothing, so
the postcondition is simply false. -/

private def noReqPgm : Program :=
#strata
program Core;

procedure NoReq(x : int)
spec {
  ensures x == 2;
}
{
};
#end

private def noReqPgmAST : Core.Program := cstToAST noReqPgm

private def noReqProc : Core.Procedure :=
  (noReqPgmAST.findProcByString? "NoReq").get!

/-- `NoReq` has a non-`free` `ensures` whose captured form at `xIs1Env` (where `x`
    holds `1`) is `1 == 2`. -/
private theorem noReq_post_clause :
    ∃ lc ∈ noReqProc.spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
      Core.Logic.capturedExpr
        { factory := xIs1Env.factory, store := xIs1Env.store, label := lc.1,
          expr := (Prod.snd lc).expr, metadata := (Prod.snd lc).md }
        = Lambda.LExpr.eq () (Lambda.LExpr.intConst () 1) (Lambda.LExpr.intConst () 2) := by
  native_decide

/-- **Invalid.**  A procedure with no `requires` but an `ensures x == 2` does not meet
    its contract: nothing is assumed on entry and the empty body changes nothing, so at
    `xIs1Env` — where `x` holds `1` — the semantic postcondition is refuted on a run whose
    empty trace has satisfiable assumptions. -/
theorem noReq_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple noReqPgmAST testParams "NoReq" := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  obtain ⟨proc, hproc, _htyped, htb⟩ := h
  have hp : proc = noReqProc := (procOf_eq hproc).symm
  subst hp
  have hbody : noReqProc.body = .structured [] := by native_decide
  have htbm := htb model
  rw [hbody] at htbm
  have ⟨_hvalid, hpostF⟩ := htbm xIs1Env xIs1Env []
    ⟨preAsPredicate_of_no_pre model noReqProc xIs1Env (by native_decide), rfl,
      oldInoutAsPredicate_of_no_inout noReqProc xIs1Env (by native_decide),
      inputAsPredicate_xIs1 noReqProc (by native_decide)⟩
    (blockWF_nil xIs1Env rfl xIs1Env_storeWellDefined)
    (.inl (run_procBlock_nil _ xIs1Env "" #[]))
  have hpost : Core.Logic.Hoare.Procedure.postAsPredicate model noReqProc xIs1Env :=
    hpostF (reachable_nil model)
  obtain ⟨⟨label, check⟩, hmem, hattr, hcap⟩ := noReq_post_clause
  rcases hpost label check hmem hattr (someValuation model) with ⟨_, hex⟩ | ⟨hne, _⟩
  · rw [hcap] at hex
    obtain ⟨hty, htrue⟩ := hex
    exact not_denote_oneEqTwo model (someValuation model) hty htrue
  · exact hne rfl


/-! ## A procedure that does not: an `ensures` the `requires` refutes

`requires x == 1` and `ensures x == 2`.  Run from a store where `x` holds `1` the
precondition *is* satisfied, and the empty body still leaves the postcondition
false — this is a genuine contract violation, not a vacuous one. -/

private def offByOnePgm : Program :=
#strata
program Core;

procedure OffByOne(x : int)
spec {
  requires x == 1;
  ensures x == 2;
}
{
};
#end

private def offByOnePgmAST : Core.Program := cstToAST offByOnePgm

private def offByOneProc : Core.Procedure :=
  (offByOnePgmAST.findProcByString? "OffByOne").get!

/-- `OffByOne` has a non-`free` `ensures` whose captured form at `xIs1Env` is `1 == 2`. -/
private theorem offByOne_post_clause :
    ∃ lc ∈ offByOneProc.spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
      Core.Logic.capturedExpr
        { factory := xIs1Env.factory, store := xIs1Env.store, label := lc.1,
          expr := (Prod.snd lc).expr, metadata := (Prod.snd lc).md }
        = Lambda.LExpr.eq () (Lambda.LExpr.intConst () 1) (Lambda.LExpr.intConst () 2) := by
  native_decide

/-- **Invalid.**  A procedure requiring `x == 1` and ensuring `x == 2` does not meet its
    contract: the empty body leaves `x` holding `1`, so the semantic postcondition is
    refuted on a run whose precondition genuinely held. -/
theorem offByOne_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple offByOnePgmAST testParams "OffByOne" := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  obtain ⟨proc, hproc, _htyped, htb⟩ := h
  have hp : proc = offByOneProc := (procOf_eq hproc).symm
  subst hp
  have hbody : offByOneProc.body = .structured [] := by native_decide
  have htbm := htb model
  rw [hbody] at htbm
  have ⟨_hvalid, hpostF⟩ := htbm xIs1Env xIs1Env []
    ⟨preAsPredicate_of_binds model offByOneProc xIs1Env
        [(⟨"x", ()⟩, some (Lambda.LMonoTy.tcons "int" []), Lambda.LConst.intConst 1)] rfl
        (by native_decide)
        (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; simp [xIs1Env]), rfl,
      oldInoutAsPredicate_of_no_inout offByOneProc xIs1Env (by native_decide),
      inputAsPredicate_xIs1 offByOneProc (by native_decide)⟩
    (blockWF_nil xIs1Env rfl xIs1Env_storeWellDefined)
    (.inl (run_procBlock_nil _ xIs1Env "" #[]))
  have hpost : Core.Logic.Hoare.Procedure.postAsPredicate model offByOneProc xIs1Env :=
    hpostF (reachable_nil model)
  obtain ⟨⟨label, check⟩, hmem, hattr, hcap⟩ := offByOne_post_clause
  rcases hpost label check hmem hattr (someValuation model) with ⟨_, hex⟩ | ⟨hne, _⟩
  · rw [hcap] at hex
    obtain ⟨hty, htrue⟩ := hex
    exact not_denote_oneEqTwo model (someValuation model) hty htrue
  · exact hne rfl

/-! ## An ill-typed map-`Select` clause cannot satisfy the side condition

`Procedure.contractChecksTyped` gates each `requires`/`ensures` on
`typeCheck [] · = some .bool`.  A map-`Select` is not Boolean — a selection
type-checks to the map's value type, or to `none` when its operands are untyped — so
a contract carrying one fails the gate and its `contractTriple` is unprovable rather
than vacuously true. -/

/-- An equality containing an unannotated map selection. -/
private def mapSelectClause : Core.Procedure.Check :=
  { expr := .eq ()
      (.app ()
        (.app () (.op () ⟨"select", ()⟩ none)
          (Lambda.LExpr.fvar () ⟨"m", ()⟩
            (some (.tcons "Map" [.int, .int]))))
        (Lambda.LExpr.fvar () ⟨"k", ()⟩ (some .int)))
      (Lambda.LExpr.intConst () 1) }

/-- The unannotated map selection prevents the clause from type-checking as `bool`. -/
example :
    ([(("req" : Core.CoreLabel), mapSelectClause)].all fun lc =>
      decide (Lambda.LExpr.typeCheck [] lc.2.expr = some .bool)) = false := by
  native_decide

/-! ## Helpers for bodies built from `x := <literal>`

`Core.Logic.Hoare.set`/`init` take the value the right-hand side evaluates to; these
specialise them to a literal, and to a variable known to hold one, and re-present the
resulting `UpdateState`/`InitState` as the two store facts the tests below actually use.
Specific to one shape of body rather than part of the logic, so they live here. -/

/-- **`PostWF` for a store fact.**  A postcondition "`x` holds `κ`" survives leaving a
    block as long as the body does not declare `x`: leaving drops exactly what it did
    declare.  Purely syntactic, so `native_decide` settles it at a concrete body. -/
private theorem postWF_store_fact (ss : Core.Statements) (x : Core.Expression.Ident)
    (κ : Lambda.LConst)
    (hnd : x ∉ Imperative.Block.definedVars
      (P := Core.Expression) (C := Core.Command) ss true) :
    Imperative.Logic.Hoare.PostWF ss
      (fun ρ => ρ.store x = some (Lambda.LExpr.const () κ)) := by
  intro ρ hpost
  show Imperative.dropVars _ ρ.store x = _
  simp only [Imperative.dropVars, ite_eq_right hnd]
  exact hpost

/-- `PostWF` for a store fact paired with the factory being `Core.Factory`.  Leaving a
    block drops only declared names from the store and never touches the factory, so both
    conjuncts survive. -/
private theorem postWF_store_fact_factory (ss : Core.Statements) (x : Core.Expression.Ident)
    (κ : Lambda.LConst)
    (hnd : x ∉ Imperative.Block.definedVars
      (P := Core.Expression) (C := Core.Command) ss true) :
    Imperative.Logic.Hoare.PostWF ss
      (fun ρ => ρ.store x = some (Lambda.LExpr.const () κ) ∧ ρ.factory = Core.Factory) := by
  intro ρ hpost
  refine ⟨?_, hpost.2⟩
  show Imperative.dropVars _ ρ.store x = _
  simp only [Imperative.dropVars, ite_eq_right hnd]
  exact hpost.1

/-- `Core.Logic.Hoare.set` at a literal right-hand side. -/
private theorem set_const (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams)
    (x : Core.Expression.Ident) (κ : Lambda.LConst)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore), Pre ρ₀ →
      σ' x = some (Lambda.LExpr.const () κ) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre
      [Core.Statement.set x (Lambda.LExpr.const () κ) md] Post :=
  Core.Logic.Hoare.set π params x _ md Pre Post
    (fun ρ₀ σ' v hpre hev hup => by
      have hv : v = Lambda.LExpr.const () κ := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_const ρ₀.factory ρ₀.store () κ))
      subst hv
      cases hup with
      | update _hold hnew hoth => exact hpost ρ₀ σ' hpre hnew hoth)

/-- `Core.Logic.Hoare.init` at a literal right-hand side. -/
private theorem init_const (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams)
    (x : Core.Expression.Ident) (ty : Core.Expression.Ty) (κ : Lambda.LConst)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore), Pre ρ₀ →
      σ' x = some (Lambda.LExpr.const () κ) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre
      [Core.Statement.init x ty (.det (Lambda.LExpr.const () κ)) md] Post :=
  Core.Logic.Hoare.init π params x ty _ md Pre Post
    (fun ρ₀ σ' v hpre hev hinit => by
      have hv : v = Lambda.LExpr.const () κ := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_const ρ₀.factory ρ₀.store () κ))
      subst hv
      cases hinit with
      | init _hold hnew hoth => exact hpost ρ₀ σ' hpre hnew hoth)

/-- `Core.Logic.Hoare.set` where the right-hand side is a variable known to hold a
    literal; `Lambda.evalFully_fvar_of_value` reads it, needing only that the binding is a
    value — which a literal is, in every factory. -/
private theorem set_fvar (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams)
    (x src : Core.Expression.Ident) (ty : Option Lambda.LMonoTy) (κ : Lambda.LConst)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hsrc : ∀ ρ₀, Pre ρ₀ → ρ₀.store src = some (Lambda.LExpr.const () κ))
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore), Pre ρ₀ →
      σ' x = some (Lambda.LExpr.const () κ) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ' }) :
    Core.Logic.Hoare.Triple π params Pre
      [Core.Statement.set x (Lambda.LExpr.fvar () src ty) md] Post :=
  Core.Logic.Hoare.set π params x _ md Pre Post
    (fun ρ₀ σ' v hpre hev hup => by
      have hv : v = Lambda.LExpr.const () κ := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_fvar_of_value ρ₀.factory ρ₀.store () src ty _
          (hsrc ρ₀ hpre) (Lambda.isValue_const_true _ _ _)))
      subst hv
      cases hup with
      | update _hold hnew hoth => exact hpost ρ₀ σ' hpre hnew hoth)

/-- The type an `int`-typed variable carries in a translated `ensures` clause. -/
private def intTy : Option Lambda.LMonoTy := some (Lambda.LMonoTy.tcons "int" [])

/-- Metadata of a statement list that is a single assignment. -/
private def branchMd (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- Decidable check that every non-`free` `ensures` of `proc` is `x == κ` for some
    `(x, ty, κ)` in `binds`. -/
private def ensuresAllEqConst (proc : Core.Procedure)
    (binds : List (Core.Expression.Ident × Option Lambda.LMonoTy × Lambda.LConst)) : Bool :=
  proc.spec.postconditions.toList.all fun lc =>
    decide (lc.2.attr ≠ Core.Procedure.CheckAttr.Default) ||
      binds.any fun b =>
        decide (lc.2.expr = Lambda.LExpr.eq () (Lambda.LExpr.fvar () b.1 b.2.1)
          (Lambda.LExpr.const () b.2.2))

/-- If every non-`free` `ensures` is `x == κ` for a listed `(x, κ)` bound by
    the store, the model's semantic postcondition holds. -/
private theorem contractPost_of_binds (model : Lambda.Interp Core.Factory)
    (proc : Core.Procedure) (ρ : Imperative.Env Core.Expression)
    (binds : List (Core.Expression.Ident × Option Lambda.LMonoTy × Lambda.LConst))
    (hfac : ρ.factory = Core.Factory)
    (hsyn : ensuresAllEqConst proc binds = Bool.true)
    (hstore : ∀ b ∈ binds, ρ.store b.1 = some (Lambda.LExpr.const () b.2.2)) :
    Core.Logic.Hoare.Procedure.contractPost model proc ρ := by
  intro label check hmem hattr
  simp only [ensuresAllEqConst, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hsyn
  rcases hsyn (label, check) hmem with hattr' | ⟨b, hb, hexpr⟩
  · exact absurd hattr hattr'
  · exact checkAsPredicate_eqConst model ρ b.1 b.2.1 b.2.2 hfac (hstore b hb) label check hexpr

/-- A one-assignment body meets a contract whose non-`free` `ensures` clauses are
    all `x == κ` for the literal being assigned.

    No `PostWF` obligation arises, which matters: the postcondition here is
    store-dependent, and `PostWF` is what the block-*wrapping* rule `block` would
    additionally demand. -/
private theorem contractTriple_set_const (p : Core.Program)
    (params : Core.Logic.InitEnvWFParams) (procName : String)
    (proc : Core.Procedure)
    (hproc : p.findProcByString? procName = some proc)
    (x : Core.Expression.Ident) (ty : Option Lambda.LMonoTy)
    (κ : Lambda.LConst) (md : Imperative.MetaData Core.Expression)
    (hbody : proc.body = .structured [Core.Statement.set x (Lambda.LExpr.const () κ) md])
    (hChecksTyped : Core.Logic.Hoare.Procedure.contractChecksTyped proc)
    (hsyn : ensuresAllEqConst proc [(x, ty, κ)] = Bool.true) :
    Core.Logic.Hoare.Procedure.contractTriple p params procName := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core p params procName proc _ hproc hbody
    hChecksTyped (fun model => ?_)
  refine (Core.Logic.Hoare.block p.findProcByString? params
    (set_const p.findProcByString? params x κ md _ _
      (fun _ρ₀ _σ' hpre hnew _hoth =>
        contractPost_of_binds model proc _ [(x, ty, κ)] hpre.2.1 hsyn
          (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hnew)))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _
      (by simp [Imperative.Block.definedVars,
        Imperative.Stmt.definedVars, Imperative.HasVarsImp.definedVars,
        Core.Command.definedVars, Imperative.Cmd.definedVars]))) model


/-! ## A body with one command

`procedure Set1(out y : int) spec { ensures y == 1; } { y := 1; }`

The smallest contract with a non-empty body, and the first one whose proof has to
say something about `Expression.eval`.  It goes through in two halves.

It is `contractTriple_set_const` above, applied to the translated body.  What
makes it work is the `==` law `Lambda.evalFully_eq_of_evalFully` in
`Strata.DL.Lambda.LExprEvalProps`: `WellFormedSemanticEval` covers negation, values,
free variables and integer comparison but says nothing about `LExpr.eq`, so that law
had to be proved directly against `evalFully` — which does reduce `y == 1` to `true`
when `y` holds `1`, via `Lambda.LExpr.eql`.

The contract holds at every `params` and initial environment satisfying the
condition. -/

private def set1Pgm : Program :=
#strata
program Core;

procedure Set1(out y : int)
spec {
  ensures y == 1;
}
{
  y := 1;
};
#end

/--
info: program Core;

procedure Set1 (out y : int)
spec {
  ensures [Set1_ensures_0]: y == 1;
  } {
  y := 1;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram set1Pgm) |>.fst

private def set1PgmAST : Core.Program := cstToAST set1Pgm

private def set1Proc : Core.Procedure :=
  (set1PgmAST.findProcByString? "Set1").get!

/-- The assignment's metadata records the source span it was translated from, so it
    is projected back out of the AST rather than written down here. -/
private def set1Md : Imperative.MetaData Core.Expression :=
  match set1Proc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- The assigned variable. -/
private def set1Y : Core.Expression.Ident := ⟨"y", ()⟩

/-- The translated body really is the single assignment `y := 1`. -/
private theorem set1_body_eq :
    set1Proc.body = .structured
      [Core.Statement.set set1Y (Lambda.LExpr.const () (.intConst 1)) set1Md] := by
  native_decide

/-- **Valid, and fully proved.**  `Set1` meets its contract: for every initial
    environment satisfying the well-formedness condition,
    the body leaves `y == 1` true and raises no failure. -/
theorem set1_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple set1PgmAST testParams "Set1" :=
  contractTriple_set_const set1PgmAST testParams "Set1" set1Proc
    (by native_decide) set1Y intTy (.intConst 1) set1Md set1_body_eq (by native_decide)
    (by native_decide)


/-! ## A body with two commands

`procedure Set2(out y : int, out z : int)
 spec { ensures y == 1; ensures z == 2; } { y := 1; z := 2; }`

The first test that *composes*, via `seq`.  Two things are worth noticing.

The intermediate assertion is a **store fact**, `ρ.store y = some 1`, not the
`ensures` clause `y == 1`.  Either would do, but carrying the store fact avoids
having to re-establish `y == 1` after `z := 2` has touched the store, which would
need the evaluator's congruence law (`WellFormedSemanticEvalExprCongr`, and with it
`WellFormedStore` of the whole store).  `UpdateState` instead says directly that the
second assignment changes nothing but `z`, so the store fact about `y` survives it,
and the two `==` clauses are read off together at the end by
`postAsPredicate_of_binds`.

so `simp` settles it and the test needs no hypothesis.  The body equation below is
stated as `prefix ++ suffix` so that `seq` applies to it directly. -/

private def set2Pgm : Program :=
#strata
program Core;

procedure Set2(out y : int, out z : int)
spec {
  ensures y == 1;
  ensures z == 2;
}
{
  y := 1;
  z := 2;
};
#end

/--
info: program Core;

procedure Set2 (out y : int, out z : int)
spec {
  ensures [Set2_ensures_0]: y == 1;
  ensures [Set2_ensures_1]: z == 2;
  } {
  y := 1;
  z := 2;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram set2Pgm) |>.fst

private def set2PgmAST : Core.Program := cstToAST set2Pgm

private def set2Proc : Core.Procedure :=
  (set2PgmAST.findProcByString? "Set2").get!

private def set2Y : Core.Expression.Ident := ⟨"y", ()⟩
private def set2Z : Core.Expression.Ident := ⟨"z", ()⟩

/-- Metadata of the `i`-th assignment, projected out of the AST (it records the
    source span, so it is not something to write down here). -/
private def set2Md (i : Nat) : Imperative.MetaData Core.Expression :=
  match set2Proc.body with
  | .structured ss =>
    match ss[i]? with
    | some (Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))) => md
    | _ => #[]
  | _ => #[]

/-- The translated body really is the two assignments, in order. -/
private theorem set2_body_eq :
    set2Proc.body = .structured
      ([Core.Statement.set set2Y (Lambda.LExpr.const () (.intConst 1)) (set2Md 0)] ++
       [Core.Statement.set set2Z (Lambda.LExpr.const () (.intConst 2)) (set2Md 1)]) := by
  native_decide

/-- **Valid, and fully proved.**  `Set2` meets its contract: the body leaves both
    `y == 1` and `z == 2` true and raises no failure. -/
theorem set2_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple set2PgmAST testParams "Set2" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core set2PgmAST testParams
    "Set2" set2Proc _ (by native_decide) set2_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block set2PgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.seq set2PgmAST.findProcByString? testParams
    (Mid := fun ρ => ρ.store set2Y = some (Lambda.LExpr.const () (.intConst 1))
      ∧ ρ.factory = Core.Factory)
    ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 1` establishes the store fact about `y`.
    exact set_const set2PgmAST.findProcByString? testParams set2Y (.intConst 1) (set2Md 0)
      _ _
      (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre.2.1⟩)
  · -- `z := 2` keeps that fact (it only writes `z`) and adds one about `z`.
    refine set_const set2PgmAST.findProcByString? testParams set2Z (.intConst 2)
      (set2Md 1) _ _ (fun ρ₀ σ' hmid hnew hoth => ?_)
    refine contractPost_of_binds model set2Proc _
      [(set2Y, intTy, .intConst 1), (set2Z, intTy, .intConst 2)] hmid.2 (by native_decide) ?_
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with h | h
    · subst h
      show σ' set2Y = _
      rw [hoth set2Y (by decide)]; exact hmid.1
    · subst h; exact hnew


/-! ## A body that declares a variable

`procedure InitVar(out y : int) spec { ensures y == 3; } { var t : int := 3; y := t; }`

`var t : int := 3` is an `init` rather than a `set`: it *defines* `t`, which the
well-formedness condition requires to be undefined beforehand (`InitEnvWF.defsUndefined`) and which
`Block.defUseWellFormed` then treats as defined for the rest of the list.  On the
value side nothing changes — `init_const` and `set_const` have the same shape, because
`InitState` and `UpdateState` differ only in what they demand of the *old* store.

The second statement reads `t`, so this is also the first test where an assignment's
right-hand side is not a literal.  `Lambda.evalFully_fvar_of_value` handles it with
its single premise "the binding read is a value", which the intermediate
store fact supplies. -/

private def initVarPgm : Program :=
#strata
program Core;

procedure InitVar(out y : int)
spec {
  ensures y == 3;
}
{
  var t : int := 3;
  y := t;
};
#end

/--
info: program Core;

procedure InitVar (out y : int)
spec {
  ensures [InitVar_ensures_0]: y == 3;
  } {
  var t : int := 3;
  y := t;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram initVarPgm) |>.fst

private def initVarPgmAST : Core.Program := cstToAST initVarPgm

private def initVarProc : Core.Procedure :=
  (initVarPgmAST.findProcByString? "InitVar").get!

private def initVarT : Core.Expression.Ident := ⟨"t", ()⟩
private def initVarY : Core.Expression.Ident := ⟨"y", ()⟩

/-- The parts of the body that cannot be written down here: the declared type, the
    two source-span metadata records, and `t`'s type annotation at its use site. -/
private def initVarParts :
    Core.Expression.Ty × Imperative.MetaData Core.Expression ×
      Option Lambda.LMonoTy × Imperative.MetaData Core.Expression :=
  match initVarProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.init _ ty _ md0)),
                 Imperative.Stmt.cmd (Imperative.CmdExt.cmd
                   (Imperative.Cmd.set _ (.det (Lambda.LExpr.fvar _ _ sty)) md1))] =>
      (ty, md0, sty, md1)
  | _ => default

private def initVarBody : Core.Statements :=
  [Core.Statement.init initVarT initVarParts.1 (.det (Lambda.LExpr.const () (.intConst 3)))
     initVarParts.2.1] ++
  [Core.Statement.set initVarY (Lambda.LExpr.fvar () initVarT initVarParts.2.2.1)
     initVarParts.2.2.2]

/-- The translated body really is the declaration followed by the assignment. -/
private theorem initVar_body_eq : initVarProc.body = .structured initVarBody := by native_decide

/-- **Valid, and fully proved.**  `var t : int := 3; y := t` leaves `y == 3` true: the
    declaration is carried as a store fact about `t`, which the assignment copies to
    `y`. -/
theorem initVar_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple initVarPgmAST testParams "InitVar" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core initVarPgmAST testParams
    "InitVar" initVarProc _ (by native_decide) initVar_body_eq (by native_decide) (fun model => ?_)
  -- The body declares `t`, which leaving the procedure block drops, so the
  -- postcondition is carried as a store fact about `y` and read off outside the block.
  refine (Core.Logic.Hoare.consequence initVarPgmAST.findProcByString? testParams
    (Core.Logic.Hoare.block initVarPgmAST.findProcByString? testParams
      (Post := fun ρ => ρ.store initVarY = some (Lambda.LExpr.const () (.intConst 3))
        ∧ ρ.factory = Core.Factory)
      ?_
      (postWF_store_fact_factory initVarBody initVarY (.intConst 3) (by native_decide)))
    (fun _ h => h)
    (fun ρ h => contractPost_of_binds model initVarProc ρ [(initVarY, intTy, .intConst 3)] h.2
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h.1))) model
  refine Core.Logic.Hoare.seq initVarPgmAST.findProcByString? testParams
    (Mid := fun ρ => ρ.store initVarT = some (Lambda.LExpr.const () (.intConst 3))
      ∧ ρ.factory = Core.Factory)
    ?_ ?_
    ⟨trivial, trivial⟩
  · -- `var t : int := 3` establishes the store fact about `t`.
    exact init_const initVarPgmAST.findProcByString? testParams initVarT initVarParts.1
      (.intConst 3) initVarParts.2.1 _ _
      (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre.2.1⟩)
  · -- `y := t` copies it to `y`.
    exact set_fvar initVarPgmAST.findProcByString? testParams initVarY initVarT
      initVarParts.2.2.1 (.intConst 3) initVarParts.2.2.2 _ _ (fun _ρ₀ hmid => hmid.1)
      (fun _ρ₀ _σ' hmid hnew _hoth => ⟨hnew, hmid.2⟩)


/-! ## An if-then-else body

`procedure Ite1(x : int, out z : int) spec { ensures z == 1; }
 { if (int.lt(x, 0)) { z := 1; } else { z := 1; } }`

The first test to use `ite`, which needs a `PostWF` per branch: each runs inside a block,
and leaving it drops the names that branch declares.  Neither branch declares `z`, so
`postWF_store_fact` settles both.  `consequence` turns the store fact `z ↦ 1` into the
`ensures` clause at the very end. -/

private def ite1Pgm : Program :=
#strata
program Core;

procedure Ite1(x : int, out z : int)
spec {
  ensures z == 1;
}
{
  if (int.lt(x, 0)) {
    z := 1;
  } else {
    z := 1;
  }
};
#end

/--
info: program Core;

procedure Ite1 (x : int, out z : int)
spec {
  ensures [Ite1_ensures_0]: z == 1;
  } {
  if (int.lt(x, 0)) {
    z := 1;
  } else {
    z := 1;
  }
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram ite1Pgm) |>.fst

private def ite1PgmAST : Core.Program := cstToAST ite1Pgm

private def ite1Proc : Core.Procedure :=
  (ite1PgmAST.findProcByString? "Ite1").get!

private def ite1Z : Core.Expression.Ident := ⟨"z", ()⟩

/-- Condition, branches and metadata, projected out: the condition is a nested
    `Int.Lt` application that there is no point spelling out here. -/
private def ite1Parts :
    Core.Expression.Expr × Core.Statements × Core.Statements ×
      Imperative.MetaData Core.Expression :=
  match ite1Proc.body with
  | .structured [Imperative.Stmt.ite (.det c) tss ess md] => (c, tss, ess, md)
  | _ => default

private def ite1Stmt : Core.Statement :=
  Imperative.Stmt.ite (.det ite1Parts.1) ite1Parts.2.1 ite1Parts.2.2.1 ite1Parts.2.2.2

/-- The translated body really is the single if-then-else. -/
private theorem ite1_body_eq : ite1Proc.body = .structured [ite1Stmt] := by native_decide

/-- The *then* branch really is the single assignment `z := 1`. -/
private theorem ite1Then_eq :
    ite1Parts.2.1 = [Core.Statement.set ite1Z (Lambda.LExpr.const () (.intConst 1))
      (branchMd ite1Parts.2.1)] := by native_decide

/-- The *else* branch really is the same assignment `z := 1`. -/
private theorem ite1Else_eq :
    ite1Parts.2.2.1 = [Core.Statement.set ite1Z (Lambda.LExpr.const () (.intConst 1))
      (branchMd ite1Parts.2.2.1)] := by native_decide

/-- **Valid, and fully proved.**  No hypotheses at all: `ite` carries no
    preservation side condition. -/
theorem ite1_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple ite1PgmAST testParams "Ite1" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core ite1PgmAST testParams
    "Ite1" ite1Proc _ (by native_decide) ite1_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block ite1PgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.consequence ite1PgmAST.findProcByString? testParams
    (Core.Logic.Hoare.ite ite1PgmAST.findProcByString? testParams
      (Post := fun ρ => ρ.store ite1Z = some (Lambda.LExpr.const () (.intConst 1))
        ∧ ρ.factory = Core.Factory)
      ?_ ?_
      (postWF_store_fact_factory ite1Parts.2.1 ite1Z (.intConst 1) (by native_decide))
      (postWF_store_fact_factory ite1Parts.2.2.1 ite1Z (.intConst 1) (by native_decide)))
    (fun _ h => h.2.1)
    (fun ρ h => contractPost_of_binds model ite1Proc ρ [(ite1Z, intTy, .intConst 1)] h.2
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h.1))
  · rw [ite1Then_eq]
    exact set_const ite1PgmAST.findProcByString? testParams ite1Z (.intConst 1)
      (branchMd ite1Parts.2.1) _ _ (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre.1⟩)
  · rw [ite1Else_eq]
    exact set_const ite1PgmAST.findProcByString? testParams ite1Z (.intConst 1)
      (branchMd ite1Parts.2.2.1) _ _ (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre.1⟩)



/-! ## A nested labelled block

`procedure Blk1(out y : int) spec { ensures y == 5; } { blk: { y := 5; } }`

`block` is the rule that wraps a statement list back up as a `block` statement, so
unlike `cmd` (which the one-command test above uses) it demands `PostWF` of the
postcondition.  `PostWF` is stated at the entry store, so it applies directly here, and
the proof is the same store-fact shape as `ite`. -/

private def blk1Pgm : Program :=
#strata
program Core;

procedure Blk1(out y : int)
spec {
  ensures y == 5;
}
{
  blk: {
    y := 5;
  }
};
#end

/--
info: program Core;

procedure Blk1 (out y : int)
spec {
  ensures [Blk1_ensures_0]: y == 5;
  } {
  blk: {
    y := 5;
  }
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram blk1Pgm) |>.fst

private def blk1PgmAST : Core.Program := cstToAST blk1Pgm

private def blk1Proc : Core.Procedure :=
  (blk1PgmAST.findProcByString? "Blk1").get!

private def blk1Y : Core.Expression.Ident := ⟨"y", ()⟩

private def blk1Parts : String × Core.Statements × Imperative.MetaData Core.Expression :=
  match blk1Proc.body with
  | .structured [Imperative.Stmt.block l ss md] => (l, ss, md)
  | _ => default

private def blk1Stmt : Core.Statement :=
  Imperative.Stmt.block blk1Parts.1 blk1Parts.2.1 blk1Parts.2.2

/-- The translated body really is the single labelled block. -/
private theorem blk1_body_eq : blk1Proc.body = .structured [blk1Stmt] := by native_decide

/-- The block's body really is the single assignment `y := 5`. -/
private theorem blk1Inner_eq :
    blk1Parts.2.1 = [Core.Statement.set blk1Y (Lambda.LExpr.const () (.intConst 5))
      (branchMd blk1Parts.2.1)] := by native_decide

/-- **Valid, and fully proved.**  `blk: { y := 5 }` leaves `y == 5` true — the store
    fact survives leaving the block, which is what `PostWF` asks of it. -/
theorem blk1_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple blk1PgmAST testParams "Blk1" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core blk1PgmAST testParams
    "Blk1" blk1Proc _ (by native_decide) blk1_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block blk1PgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.consequence blk1PgmAST.findProcByString? testParams
    (Core.Logic.Hoare.block blk1PgmAST.findProcByString? testParams
      (Post := fun ρ => ρ.store blk1Y = some (Lambda.LExpr.const () (.intConst 5))
        ∧ ρ.factory = Core.Factory)
      ?_
      (postWF_store_fact_factory blk1Parts.2.1 blk1Y (.intConst 5) (by native_decide)))
    (fun _ h => h.2.1)
    (fun ρ h => contractPost_of_binds model blk1Proc ρ [(blk1Y, intTy, .intConst 5)] h.2
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h.1))
  · rw [blk1Inner_eq]
    exact set_const blk1PgmAST.findProcByString? testParams blk1Y (.intConst 5)
      (branchMd blk1Parts.2.1) _ _ (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre⟩)



/-! ## An `exit` caught by its enclosing block

`procedure ExitBlk(out y : int) spec { ensures y == 4; }
 { blk: { y := 4; exit blk; y := 99; } }`

The case the single triple judgement exists for.  The block finishes by *exiting*, not by
running off the end of its body, so the body's triple has to hold at an exiting
configuration — which is what `Triple` admits and what `exit_cons` establishes.  `seq`
cannot reach past the `exit` (it requires its prefix not to escape), and the contract
would be *false* if `y := 99` ran. -/

private def exitBlkPgm : Program :=
#strata
program Core;

procedure ExitBlk(out y : int)
spec {
  ensures y == 4;
}
{
  blk: {
    y := 4;
    exit blk;
    y := 99;
  }
};
#end

private def exitBlkPgmAST : Core.Program := cstToAST exitBlkPgm

private def exitBlkProc : Core.Procedure :=
  (exitBlkPgmAST.findProcByString? "ExitBlk").get!

private def exitBlkY : Core.Expression.Ident := ⟨"y", ()⟩

private def exitBlkParts : String × Core.Statements × Imperative.MetaData Core.Expression :=
  match exitBlkProc.body with
  | .structured [Imperative.Stmt.block l ss md] => (l, ss, md)
  | _ => default

private def exitBlkStmt : Core.Statement :=
  Imperative.Stmt.block exitBlkParts.1 exitBlkParts.2.1 exitBlkParts.2.2

/-- The translated body really is the single labelled block. -/
private theorem exitBlk_body_eq :
    exitBlkProc.body = .structured [exitBlkStmt] := by native_decide

/-- The exit's target label and the three source-span metadata records. -/
private def exitBlkInnerParts :
    Imperative.MetaData Core.Expression × String × Imperative.MetaData Core.Expression ×
      Imperative.MetaData Core.Expression :=
  match exitBlkParts.2.1 with
  | [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
     Imperative.Stmt.exit l md1,
     Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md2))] => (md0, l, md1, md2)
  | _ => default

private def exitBlkInnerBody : Core.Statements :=
  [Core.Statement.set exitBlkY (Lambda.LExpr.const () (.intConst 4)) exitBlkInnerParts.1] ++
  [Imperative.Stmt.exit exitBlkInnerParts.2.1 exitBlkInnerParts.2.2.1,
   Core.Statement.set exitBlkY (Lambda.LExpr.const () (.intConst 99))
     exitBlkInnerParts.2.2.2]

/-- The block's body really is the assignment, the `exit`, and the dead assignment after it. -/
private theorem exitBlkInner_eq :
    exitBlkParts.2.1 = exitBlkInnerBody := by native_decide

/-- **Valid, and fully proved.**  `blk: { y := 4; exit blk; y := 99 }` leaves `y == 4`
    true: the `exit` ends the body at the store fact `y ↦ 4`, and the enclosing block
    catches it. -/
theorem exitBlk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple exitBlkPgmAST testParams "ExitBlk" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core exitBlkPgmAST testParams
    "ExitBlk" exitBlkProc _ (by native_decide) exitBlk_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block exitBlkPgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.consequence exitBlkPgmAST.findProcByString? testParams
    (Core.Logic.Hoare.block exitBlkPgmAST.findProcByString? testParams
      (Post := fun ρ => ρ.store exitBlkY = some (Lambda.LExpr.const () (.intConst 4))
        ∧ ρ.factory = Core.Factory)
      ?_
      (postWF_store_fact_factory exitBlkParts.2.1 exitBlkY (.intConst 4) (by native_decide)))
    (fun _ h => h.2.1)
    (fun ρ h => contractPost_of_binds model exitBlkProc ρ [(exitBlkY, intTy, .intConst 4)] h.2
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h.1))
  · rw [exitBlkInner_eq]
    refine Core.Logic.Hoare.seq exitBlkPgmAST.findProcByString? testParams
      (Mid := fun ρ => ρ.store exitBlkY = some (Lambda.LExpr.const () (.intConst 4))
        ∧ ρ.factory = Core.Factory)
      ?_ ?_
      ⟨trivial, trivial⟩
    · exact set_const exitBlkPgmAST.findProcByString? testParams exitBlkY
        (.intConst 4) exitBlkInnerParts.1 _ _ (fun _ρ₀ _σ' hpre hnew _hoth => ⟨hnew, hpre⟩)
    · exact Core.Logic.Hoare.exit_cons exitBlkPgmAST.findProcByString? testParams _



/-! ## A body with an `assume` and an `assert`

`procedure Chk(x : int) spec { ensures x == 1; } { assume [a]: x == 1; assert [b]: x == 1; }`

The first test whose body is neither an assignment nor a control construct.  Both
commands leave the store alone, so nothing here is a store fact.  Under the event
semantics the `assume` *emits* its condition and the `assert` re-emits it, so
`AssertionsValid` discharges the `assert` from the preceding `assume` on the same
expression in the same trace.  The postcondition `ensures x == 1` is required only when
the emitted assumption is satisfiable; input typing identifies `x` with an integer
literal, and satisfiability of the captured `x == 1` forces that literal to be `1`.

Proved directly from `StepStmtStarE`, inverting the run of the two commands with the
small-step helpers below. -/

section AssumeAssertInversion

variable (π : String → Option Core.Procedure)

/-- Invert the run of `[assume la e mda, assert lb e mdb]`: neither command changes the
    store, so the final environment is the initial one and the trace is the two captured
    events in order. -/
private theorem assume_assert_run_inv
    {la lb : String} {e : Core.Expression.Expr}
    {mda mdb : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {trace : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [Core.Statement.assume la e mda, Core.Statement.assert lb e mdb] ρ)
        trace (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [Core.Statement.assume la e mda, Core.Statement.assert lb e mdb] ρ)
        trace (.exiting lbl ρ')) :
    ρ' = ρ ∧ trace =
      [Event.assume ⟨ρ.factory, ρ.store, la, e, mda⟩,
       Event.assert ⟨ρ.factory, ρ.store, lb, e, mdb⟩] := by
  rcases stmts_append_doneE (Core.EvalCommandE π) [Core.Statement.assume la e mda]
      [Core.Statement.assert lb e mdb] ρ ρ' h with
    ⟨lbl, hexit⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm₁, hfin₂⟩
  · exact absurd hexit (stmts_exitsCoveredByBlocks_noEscapeE (Core.EvalCommandE π)
      [Core.Statement.assume la e mda]
      (by simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks]) ρ lbl ρ')
  · obtain ⟨htr₁, hρ₁⟩ := assume_run_inv π (singleton_run_inv π (.inl hterm₁))
    subst hρ₁
    obtain ⟨htr₂, hρ'⟩ := assert_run_inv π (singleton_run_inv π hfin₂)
    subst hρ'
    subst htr₁; subst htr₂; subst htr
    exact ⟨rfl, rfl⟩

end AssumeAssertInversion


private def chkPgm : Program :=
#strata
program Core;

procedure Chk(x : int)
spec {
  ensures x == 1;
}
{
  assume [a]: x == 1;
  assert [b]: x == 1;
};
#end

private def chkPgmAST : Core.Program := cstToAST chkPgm

private def chkProc : Core.Procedure :=
  (chkPgmAST.findProcByString? "Chk").get!

/-- The assumed expression, and the two source-span metadata records. -/
private def chkParts : Core.Expression.Expr × Imperative.MetaData Core.Expression ×
    Imperative.MetaData Core.Expression :=
  match chkProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.assume _ e md0)),
                 Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.assert _ _ md1))] =>
      (e, md0, md1)
  | _ => default

private def chkBody : Core.Statements :=
  [Core.Statement.assume "a" chkParts.1 chkParts.2.1] ++
  [Core.Statement.assert "b" chkParts.1 chkParts.2.2]

/-- The translated body really is the `assume` then the `assert`, on the same expression. -/
private theorem chk_body_eq : chkProc.body = .structured chkBody := by native_decide

/-- Every `ensures` of `Chk` is the expression captured by the two commands. -/
private theorem chk_ensures_expr :
    ∀ lc ∈ chkProc.spec.postconditions.toList, (Prod.snd lc).expr = chkParts.1 := by
  native_decide

/-- The identifier of `Chk`'s integer input. -/
private def chkX : Core.Expression.Ident := ⟨"x", ()⟩

/-- The condition used by `Chk` is `x == 1`. -/
private theorem chk_expr_shape :
    chkParts.1 = Lambda.LExpr.eq () (Lambda.LExpr.fvar () chkX intTy)
      (Lambda.LExpr.intConst () 1) := by
  native_decide

/-- `x` is the sole integer input of `Chk`. -/
private theorem chk_input_mem :
    (chkX, Lambda.LMonoTy.int) ∈ chkProc.header.inputs.toList := by
  native_decide

/-- **Valid, and fully proved.**  The `assume` supplies the very fact the `ensures`
    asserts, and the `assert` on the same expression is valid because that fact
    precedes it. -/
theorem chk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple chkPgmAST testParams "Chk" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed chkPgmAST testParams
    "Chk" chkProc _ (by native_decide) chk_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block chkPgmAST.findProcByString? testParams
    ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  -- The inner body `[assume x==1, assert x==1]`, proved directly from the event run.
  intro m ρ₀ ρ' trace hpre hwf hrun
  obtain ⟨hρ', htr⟩ := assume_assert_run_inv chkPgmAST.findProcByString? hrun
  subst ρ'
  subst htr
  obtain ⟨_hpre, hfac, _hold, hinput⟩ := hpre
  obtain ⟨v, hx, hv⟩ := hinput chkX Lambda.LMonoTy.int chk_input_mem
  change ∃ i : Int, v = Lambda.LExpr.intConst () i at hv
  obtain ⟨i, rfl⟩ := hv
  refine ⟨?_, fun hreach => ?_⟩
  · -- The assertion is discharged by the preceding assumption on the same expression.
    refine ⟨fun _ world hassum => ?_, trivial⟩
    have ha := hassum ⟨ρ₀.factory, ρ₀.store, "a", chkParts.1, chkParts.2.1⟩ (by simp)
    rcases ha with ⟨_, hex⟩ | ⟨hne, _⟩
    · exact .inl ⟨hfac, hex⟩
    · exact absurd hfac hne
  · -- Reachability forces the input literal to `1`, giving the semantic postcondition.
    obtain ⟨world, hassum⟩ := hreach
    have ha := hassum ⟨ρ₀.factory, ρ₀.store, "a", chkParts.1, chkParts.2.1⟩ (by simp)
    rcases ha with ⟨_, hex⟩ | ⟨hne, _⟩
    · have hcaptured : Core.Logic.capturedExpr
          (⟨ρ₀.factory, ρ₀.store, "a", chkParts.1, chkParts.2.1⟩ :
            Imperative.EventArg Core.Expression) =
          Lambda.LExpr.eq () (Lambda.LExpr.intConst () i) (Lambda.LExpr.intConst () 1) := by
        rw [hfac, chk_expr_shape]
        simp [Core.Logic.capturedExpr, Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hx]
      rw [hcaptured] at hex
      obtain ⟨hty, htrue⟩ := hex
      cases hty with
      | eq hleft hright =>
        have hty := Lambda.HasTypeA.const_inv hleft
        cases hty
        have hi := Lambda.denote_eq_true_implies_eq .nil hleft hright
          (.eq hleft hright) htrue
        change Lambda.LExpr.denote m.tcInterp m.opInterp world.freeVarVal
          world.tyVarVal .nil (Lambda.LExpr.intConst () i) Lambda.LMonoTy.int hleft =
            Lambda.LExpr.denote m.tcInterp m.opInterp world.freeVarVal
              world.tyVarVal .nil (Lambda.LExpr.intConst () 1) Lambda.LMonoTy.int hright at hi
        have hdi := Lambda.denote_intConst m.tcInterp m.opInterp
          world.freeVarVal world.tyVarVal .nil hleft
        have hd1 := Lambda.denote_intConst m.tcInterp m.opInterp
          world.freeVarVal world.tyVarVal .nil hright
        have hi' : i = 1 := hdi.symm.trans (hi.trans hd1)
        subst i
        intro label check hmem _hattr
        exact checkAsPredicate_eqConst model ρ₀ chkX intTy (.intConst 1) hfac hx
          label check ((chk_ensures_expr (label, check) hmem).trans chk_expr_shape)
    · exact absurd hfac hne


/-! ## A while loop that terminates

`procedure LoopTerm(out y : int) spec { ensures y == 10; }
 { y := 0; while (int.le(y, 9)) { y := int.add(y, 1); } }`

A genuine counting loop, *fully verified to its result*: `y` starts at `0`, the body
increments it while `y ≤ 9`, and the contract `y == 10` holds on exit.

This is the payoff of pinning `fac = Core.Factory` in `Procedure.contractTriple`.
With the concrete evaluator fixed, its arithmetic is available — `coreEval_intAdd_numeral`
(`int.add(y, 1)` on `y ↦ n` yields `n + 1`) and `coreEval_intLe_numeral` (`int.le(y, 9)`
yields `n ≤ 9`), both built from the `Int.Add`/`Int.Le` reductions in
`InstWellFormedSemanticsEval`.  So the invariant can *track `y`'s value*:
`(∃ n, y ↦ n ∧ 0 ≤ n ≤ 10) ∧ factory = Core.Factory`.

`y := 0` establishes it (`n = 0`).  The body runs under the guard, which — by
`coreEval_intLe_numeral` — gives `n ≤ 9`, so `int.add(y, 1)` takes `y ↦ n` to `y ↦ n + 1`
with `0 ≤ n + 1 ≤ 10` (`omega`).  On exit `while_rule` supplies the negated guard
`eval guard = ff`, i.e. `¬ (n ≤ 9)`; with `n ≤ 10` this forces `n = 10`, so `y == 10`
evaluates to `true` (`evalFully_eq_self`).  Pinning the factory is essential here: over an
arbitrary well-formed factory the evaluator's value laws for `int.add` and `int.le` are
unspecified, so tracking `y`'s concrete value is only possible against `Core.Factory`. -/

private def loopTermPgm : Program :=
#strata
program Core;

procedure LoopTerm(out y : int)
spec {
  ensures y == 10;
}
{
  y := 0;
  while (int.le(y, 9)) {
    y := int.add(y, 1);
  }
};
#end

private def loopTermPgmAST : Core.Program := cstToAST loopTermPgm

private def loopTermProc : Core.Procedure :=
  (loopTermPgmAST.findProcByString? "LoopTerm").get!

private def loopTermY : Core.Expression.Ident := ⟨"y", ()⟩

private def loopTermParts :
    Imperative.MetaData Core.Expression × Core.Expression.Expr ×
      Option Core.Expression.Expr × List (String × Core.Expression.Expr) ×
      Core.Statements × Imperative.MetaData Core.Expression :=
  match loopTermProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
                 Imperative.Stmt.loop (.det g) m inv body md1] => (md0, g, m, inv, body, md1)
  | _ => default

private def loopTermStmt : Core.Statement :=
  Imperative.Stmt.loop (.det loopTermParts.2.1) loopTermParts.2.2.1 loopTermParts.2.2.2.1
    loopTermParts.2.2.2.2.1 loopTermParts.2.2.2.2.2

private def loopTermBody : Core.Statements :=
  [Core.Statement.set loopTermY (Lambda.LExpr.const () (.intConst 0)) loopTermParts.1] ++
    [loopTermStmt]

/-- The translated body really is the initialisation followed by the loop. -/
private theorem loopTerm_body_eq : loopTermProc.body = .structured loopTermBody := by
  native_decide

/-- The right-hand side and metadata of the loop body's single assignment `y := y + 1`,
    projected out of the AST (the `int.add` application is not worth spelling out here). -/
private def loopTermInnerParts :
    Core.Expression.Expr × Imperative.MetaData Core.Expression :=
  match loopTermParts.2.2.2.2.1 with
  | [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) md))] => (e, md)
  | _ => default

/-- The loop body really is the single assignment `y := y + 1`. -/
private theorem loopTermInner_eq :
    loopTermParts.2.2.2.2.1 =
      [Core.Statement.set loopTermY loopTermInnerParts.1 loopTermInnerParts.2] := by
  native_decide

/-- The translated guard `int.le(y, 9)` in `Core.Factory`'s operator form. -/
private theorem loopTermGuard_shape :
    loopTermParts.2.1 =
      Lambda.LExpr.app () (Lambda.LExpr.app () Core.coreIntLeOpExpr
        (Lambda.LExpr.fvar () loopTermY intTy)) (Lambda.LExpr.const () (Lambda.LConst.intConst 9)) := by
  native_decide

/-- The loop body's assigned expression `int.add(y, 1)` in operator form. -/
private theorem loopTermRhs_shape :
    loopTermInnerParts.1 =
      Lambda.LExpr.app () (Lambda.LExpr.app () Core.coreIntAddOpExpr
        (Lambda.LExpr.fvar () loopTermY intTy)) (Lambda.LExpr.const () (Lambda.LConst.intConst 1)) := by
  native_decide

/-- With `y ↦ n`, the guard evaluates to `n ≤ 9` on `Core.Factory`. -/
private theorem loopTermGuard_eval (σ : Core.CoreStore) (n : Int)
    (hσy : σ loopTermY = some (Lambda.LExpr.intConst () n)) :
    Core.Expression.eval Core.Factory σ loopTermParts.2.1
      = some (Lambda.LExpr.boolConst () (decide (n ≤ 9))) := by
  rw [loopTermGuard_shape]
  exact Core.coreEval_intLe_numeral σ (Lambda.LExpr.fvar () loopTermY intTy) n
    (Lambda.evalFully_fvar_of_value Core.Factory σ () loopTermY intTy _ hσy
      (Lambda.isValue_const_true _ _ _))

/-- With `y ↦ n`, the loop body assigns `n + 1` on `Core.Factory`. -/
private theorem loopTermRhs_eval (σ : Core.CoreStore) (n : Int)
    (hσy : σ loopTermY = some (Lambda.LExpr.intConst () n)) :
    Core.Expression.eval Core.Factory σ loopTermInnerParts.1
      = some (Lambda.LExpr.intConst () (n + 1)) := by
  rw [loopTermRhs_shape]
  exact Core.coreEval_intAdd_numeral σ (Lambda.LExpr.fvar () loopTermY intTy) n
    (Lambda.evalFully_fvar_of_value Core.Factory σ () loopTermY intTy _ hσy
      (Lambda.isValue_const_true _ _ _))

/-- **Valid, and fully proved.**
    `y := 0; while (int.le(y, 9)) { y := int.add(y, 1) }` establishes `y == 10`.

    Because `Procedure.contractTriple` pins `fac = Core.Factory`, the concrete
    evaluator's arithmetic is available (`coreEval_intAdd_numeral`, `coreEval_intLe_numeral`),
    so the invariant tracks `y`'s value: `0 ≤ y ≤ 10` together with the factory being
    `Core.Factory`.  `y := 0` establishes it; the body takes `y ↦ n` (the guard giving
    `n ≤ 9`) to `y ↦ n + 1`, still `≤ 10`; and on exit the negated guard `¬ (y ≤ 9)` with
    `y ≤ 10` forces `y = 10`. -/
theorem loopTerm_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple loopTermPgmAST testParams "LoopTerm" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core loopTermPgmAST testParams
    "LoopTerm" loopTermProc _ (by native_decide) loopTerm_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block loopTermPgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.seq loopTermPgmAST.findProcByString? testParams
    (Mid := fun ρ => (∃ n : Int, ρ.store loopTermY = some (Lambda.LExpr.intConst () n)
        ∧ 0 ≤ n ∧ n ≤ 10) ∧ ρ.factory = Core.Factory)
    ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 0` establishes `0 ≤ y ≤ 10` (and carries the factory through).
    exact set_const loopTermPgmAST.findProcByString? testParams loopTermY (.intConst 0)
      loopTermParts.1 _ _
      (fun _ρ₀ _σ' hpre hnew _hoth => ⟨⟨0, hnew, by decide, by decide⟩, hpre.2.1⟩)
  · -- The loop preserves `0 ≤ y ≤ 10`; the exit's `¬ (y ≤ 9)` then forces `y = 10`.
    refine Core.Logic.Hoare.consequence loopTermPgmAST.findProcByString? testParams
      (Core.Logic.Hoare.while_rule loopTermPgmAST.findProcByString? testParams
        ?_ ?_ ?_)
      (fun _ h => h)
      (fun ρ h => ?_)
    · -- body: `y := int.add(y, 1)` sends `n ≤ 9` to `n + 1 ≤ 10`.
      rw [loopTermInner_eq]
      refine Core.Logic.Hoare.set loopTermPgmAST.findProcByString? testParams loopTermY
        loopTermInnerParts.1 loopTermInnerParts.2 _ _ (fun ρ₀ σ' v hpre hev hup => ?_)
      obtain ⟨⟨n, hσy, hlo, hhi⟩, hfac⟩ := hpre.1
      have hg : Core.Expression.eval Core.Factory ρ₀.store loopTermParts.2.1
          = some Imperative.HasBool.tt := hfac ▸ hpre.2
      have hle9 : n ≤ 9 := by
        have heq : (Imperative.HasBool.tt : Core.Expression.Expr)
            = Lambda.LExpr.boolConst () (decide (n ≤ 9)) :=
          Option.some.inj (hg.symm.trans (loopTermGuard_eval ρ₀.store n hσy))
        cases hdec : decide (n ≤ 9) with
        | true => exact of_decide_eq_true hdec
        | false =>
          rw [hdec] at heq
          exact absurd (show (Imperative.HasBool.tt : Core.Expression.Expr)
            = Imperative.HasBool.ff from heq) Imperative.HasBool.tt_is_not_ff
      have hv : v = Lambda.LExpr.intConst () (n + 1) :=
        Option.some.inj ((hfac ▸ hev).symm.trans (loopTermRhs_eval ρ₀.store n hσy))
      cases hup with
      | update _hold hnew hoth =>
        exact ⟨⟨n + 1, by rw [hv] at hnew; exact hnew, by omega, by omega⟩, hfac⟩
    · -- the loop body contains no `exit`
      rw [loopTermInner_eq]
      exact ⟨trivial, trivial⟩
    · -- `PostWF`: the body declares nothing, so any postcondition survives the block.
      exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide)
    · -- exit: `¬ (y ≤ 9)` and `y ≤ 10` force `y = 10`, so `y == 10` evaluates to `true`.
      obtain ⟨⟨n, hσy, hlo, hhi⟩, hfac⟩ := h.1
      have hg : Core.Expression.eval Core.Factory ρ.store loopTermParts.2.1
          = some Imperative.HasBool.ff := hfac ▸ h.2
      have hng9 : ¬ (n ≤ 9) := by
        have heq : (Imperative.HasBool.ff : Core.Expression.Expr)
            = Lambda.LExpr.boolConst () (decide (n ≤ 9)) :=
          Option.some.inj (hg.symm.trans (loopTermGuard_eval ρ.store n hσy))
        cases hdec : decide (n ≤ 9) with
        | false => exact of_decide_eq_false hdec
        | true =>
          rw [hdec] at heq
          exact absurd (show (Imperative.HasBool.tt : Core.Expression.Expr)
            = Imperative.HasBool.ff from heq.symm) Imperative.HasBool.tt_is_not_ff
      have hn10 : n = 10 := by omega
      subst hn10
      refine contractPost_of_binds model loopTermProc ρ
        [(loopTermY, intTy, .intConst 10)] hfac (by native_decide) ?_
      intro b hb
      simp only [List.mem_singleton] at hb; subst hb
      exact hσy


/-! ## A while loop that never terminates

`procedure LoopForever(out y : int) spec { ensures false; }
 { y := 7; while (true) { y := 7; } }`

A `true` guard makes the loop diverge, so its *terminating* runs are exactly none, and
under partial correctness a procedure that never returns meets *any* contract — including
the unsatisfiable `ensures false`.

The proof pins this on the guard.  `while_rule` returns `Inv ∧ ¬guard` on exit, i.e.
`Inv ρ ∧ Expression.eval fac ρ.store guard = some HasBool.ff`.  The guard is the
literal `true`, which evaluates to `HasBool.tt` in *every* factory (a constant is its own
value — `evalFully_const`, no well-formedness needed), so `= some HasBool.ff` is
`some tt = some ff`, a contradiction.  The exit condition is therefore never satisfied,
and `consequence` turns it into `ensures false`: the postcondition is proved from the
impossibility of exiting, not from any run of the body.  The invariant `y ↦ 7` serves only
to satisfy `while_rule`'s remaining side conditions (`hcov`, `PostWF`);
the exit contradiction is what carries the contract. -/

private def loopForeverPgm : Program :=
#strata
program Core;

procedure LoopForever(out y : int)
spec {
  ensures false;
}
{
  y := 7;
  while (true) {
    y := 7;
  }
};
#end

private def loopForeverPgmAST : Core.Program := cstToAST loopForeverPgm

private def loopForeverProc : Core.Procedure :=
  (loopForeverPgmAST.findProcByString? "LoopForever").get!

private def loopForeverY : Core.Expression.Ident := ⟨"y", ()⟩

private def loopForeverParts :
    Imperative.MetaData Core.Expression × Core.Expression.Expr ×
      Option Core.Expression.Expr × List (String × Core.Expression.Expr) ×
      Core.Statements × Imperative.MetaData Core.Expression :=
  match loopForeverProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
                 Imperative.Stmt.loop (.det g) m inv body md1] => (md0, g, m, inv, body, md1)
  | _ => default

private def loopForeverStmt : Core.Statement :=
  Imperative.Stmt.loop (.det loopForeverParts.2.1) loopForeverParts.2.2.1
    loopForeverParts.2.2.2.1 loopForeverParts.2.2.2.2.1 loopForeverParts.2.2.2.2.2

private def loopForeverBody : Core.Statements :=
  [Core.Statement.set loopForeverY (Lambda.LExpr.const () (.intConst 7)) loopForeverParts.1] ++
    [loopForeverStmt]

/-- The translated body really is the assignment followed by the loop. -/
private theorem loopForever_body_eq : loopForeverProc.body = .structured loopForeverBody := by
  native_decide

/-- The loop body really is the single assignment `y := 7`. -/
private theorem loopForeverInner_eq :
    loopForeverParts.2.2.2.2.1 = [Core.Statement.set loopForeverY
      (Lambda.LExpr.const () (.intConst 7)) (branchMd loopForeverParts.2.2.2.2.1)] := by
  native_decide

/-- The loop guard really is the literal `true`. -/
private theorem loopForeverGuard_eq :
    loopForeverParts.2.1 = Lambda.LExpr.const () (Lambda.LConst.boolConst true) := by
  native_decide

/-- **Valid, and fully proved — vacuously.**  `y := 7; while (true) { y := 7 }` meets
    `ensures false`: the `true` guard never lets the loop exit, so the exit condition
    `while_rule` returns is contradictory, and `ensures false` follows from that
    contradiction.  A partial-correctness contract about a body that never returns. -/
theorem loopForever_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple loopForeverPgmAST testParams "LoopForever" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of loopForeverPgmAST testParams
    "LoopForever" loopForeverProc _ (by native_decide) loopForever_body_eq (by native_decide) (fun model => ?_)
  refine (Core.Logic.Hoare.block loopForeverPgmAST.findProcByString? testParams
    ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))) model
  refine Core.Logic.Hoare.seq loopForeverPgmAST.findProcByString? testParams
    (Mid := fun ρ => ρ.store loopForeverY = some (Lambda.LExpr.const () (.intConst 7)))
    ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 7` establishes the invariant.
    exact set_const loopForeverPgmAST.findProcByString? testParams loopForeverY (.intConst 7)
      loopForeverParts.1 _ _
      (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
  · -- The loop diverges, so its exit condition is unsatisfiable and `ensures false` follows.
    refine Core.Logic.Hoare.consequence loopForeverPgmAST.findProcByString? testParams
      (Core.Logic.Hoare.while_rule loopForeverPgmAST.findProcByString? testParams
        ?_ ?_ ?_)
      (fun _ h => h)
      (fun ρ h => ?_)
    · -- body: re-establish the invariant
      rw [loopForeverInner_eq]
      exact set_const loopForeverPgmAST.findProcByString? testParams loopForeverY (.intConst 7)
        (branchMd loopForeverParts.2.2.2.2.1) _ _ (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
    · -- the body contains no `exit`
      rw [loopForeverInner_eq]
      exact ⟨trivial, trivial⟩
    · exact postWF_store_fact loopForeverParts.2.2.2.2.1 loopForeverY (.intConst 7)
        (by native_decide)
    · -- The exit condition `Inv ∧ ¬guard` is impossible: the `true` guard evaluates to
      -- `HasBool.tt`, not `HasBool.ff`.  From the contradiction, `ensures false` follows.
      exfalso
      have hg : Core.Expression.eval ρ.factory ρ.store loopForeverParts.2.1 =
          some Imperative.HasBool.tt := by
        rw [loopForeverGuard_eq]
        exact Lambda.evalFully_const ρ.factory ρ.store () (Lambda.LConst.boolConst true)
      exact absurd (Option.some.inj (hg.symm.trans h.2)) Imperative.HasBool.tt_is_not_ff

/-! ## A contract about a variable the body declares

`procedure P() spec { ensures x == 1; } { var x : int := 1; }` cannot be proved, and
Core's front end will not even translate it — `x` is not in scope in the spec, so the
source is rejected with `Unknown expr identifier x`.

The same fact at the semantic level is below, and it is why `contractTriple` is stated
over the body *wrapped in its procedure block*: leaving that block drops exactly the
names the body declared, so a postcondition naming one of them fails `PostWF`. -/

example (x : Core.Expression.Ident) (ty : Core.Expression.Ty)
    (md : Imperative.MetaData Core.Expression) :
    ¬ Imperative.Logic.Hoare.PostWF
        [Core.Statement.init x ty (.det (Lambda.LExpr.const () (.intConst 1))) md]
        (fun ρ => ρ.store x = some (Lambda.LExpr.const () (.intConst 1))) := by
  intro h
  have hbad := h
    { store := fun y => if y = x then some (Lambda.LExpr.const () (.intConst 1)) else none, factory := Core.Factory,
      hasFailure := false } (by simp)
  simp [Imperative.dropVars, Imperative.Block.definedVars,
    Imperative.Stmt.definedVars, Imperative.HasVarsImp.definedVars,
    Core.Command.definedVars, Imperative.Cmd.definedVars] at hbad


end Strata

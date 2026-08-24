/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprEvalProps
import StrataDDM.Integration.Lean.HashCommands

/-! # Reading a Core procedure's contract as a Hoare triple

Each test below writes a one-procedure Core program in DDM syntax, translates it to
the Core AST, and then reads the procedure's `requires`/`ensures` as the
pre/postcondition of a `Core.Logic.Hoare` triple via
`Procedure.contractTriple`.  Eleven procedures are *proved* to meet their contracts and
two are *disproved*.  The bodies range from empty — where the triple is settled
structurally, with no reasoning about individual statements — up to `assume`/`assert`,
if-then-else, a labelled block, a block left by an `exit`, a `while` loop that terminates
(a counting loop `while (int.le(y, 9)) { y := int.add(y, 1) }`, verified to its result
`y == 10` using the concrete `Core.Factory` arithmetic the precondition pins), and a
`while` loop that diverges (a `true` guard) and so meets `ensures false`
vacuously under partial correctness.  A final example shows why the contract is read over
the body *wrapped in its procedure block*: a postcondition naming a variable the body
declares fails `PostWF`.

**These tests use `native_decide`** for the steps that inspect a concrete translated
AST, because kernel reduction over one is impractically slow.  A step that can be
discharged without it should be.
-/

open StrataDDM (Program)
open Lambda.LExpr.SyntaxMono

namespace Strata

/-! ## Shared setup

The reusable helpers below take the procedure environment as a parameter, since they
hold for *every* one — none of these bodies makes a call or declares a function, so
neither the callee map nor the factory extension can affect the outcome.  The contract
theorems name their program instead, so the environment a call would resolve against is
that program's own `findProcByString?`. -/

variable (φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression →
  Core.Expression.Factory)

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
    factory := Core.Factory, hasFailure := false }

/-- `xIs1Env` holds only values: its single binding is the literal `1`, which is a
    canonical value in every factory.  The well-formedness conditions require this of any
    environment a run starts from. -/
private theorem xIs1Env_storeWellDefined :
    Imperative.WellFormedStore xIs1Env.store xIs1Env.factory := by
  intro n v hn
  show Lambda.LExpr.isCanonicalValue _ v = true
  simp only [xIs1Env] at hn
  split at hn
  · injection hn with hv
    subst hv
    simp [Lambda.LExpr.isCanonicalValue]
  · exact absurd hn (by simp)

/-- The block condition is immediate for an empty body: every clause that mentions
    the statements is vacuous, `Core.Factory` is well-formed, and the store holds
    only values. -/
private theorem blockWF_nil (ρ : Imperative.Env Core.Expression)
    (hf : ρ.factory = Core.Factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory) :
    Core.Logic.BlockInitEnvWF testParams [Imperative.Stmt.block "" [] #[]] ρ :=
  Core.Logic.blockInitEnvWF_procBlock_nil (hf ▸ Core.coreFactory_WellFormedSemanticEval)
    hsv rfl (fun _ _ => rfl)

/-- An empty body, wrapped as the procedure block a body actually runs in, returns to
    its own environment: entering and leaving the block projects the store through
    itself. -/
private theorem run_procBlock_nil (π : String → Option Core.Procedure)
    (ρ : Imperative.Env Core.Expression) (l : String)
    (md : Imperative.MetaData Core.Expression) :
    Imperative.StepStmtStar Core.Expression (Core.EvalCommand π φ) (Core.EvalPureFunc φ)
      (.stmts [Imperative.Stmt.block l [] md] ρ) (.terminal ρ) := by
  have heq : ({ ρ with store := Imperative.projectStore ρ.store ρ.store, factory := ρ.factory } : Imperative.Env Core.Expression) = ρ := by
    simp [Imperative.projectStore_self]
  have hhead : Imperative.StepStmtStar Core.Expression (Core.EvalCommand π φ)
      (Core.EvalPureFunc φ) (.stmt (Imperative.Stmt.block l [] md) ρ) (.terminal ρ) := by
    refine .step _ _ _ .step_block ?_
    refine .step _ _ _ (.step_block_body .step_stmts_nil) ?_
    refine .step _ _ _ .step_block_done ?_
    rw [heq]
    exact .refl _
  exact ReflTrans_Transitive _ _ _ _
    (Imperative.stmts_cons_step Core.Expression (Core.EvalCommand π φ)
      (Core.EvalPureFunc φ) _ [] ρ ρ hhead)
    (Imperative.evalStmtsSmallNil Core.Expression (Core.EvalCommand π φ)
      (Core.EvalPureFunc φ) ρ)


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
    Core.Logic.Hoare.Procedure.contractTriple φ keepPgmAST testParams "Keep" :=
  Core.Logic.Hoare.Procedure.contractTriple_nil_of_ensuresAmongRequires φ
    keepPgmAST testParams "Keep" keepProc (by native_decide) (by native_decide)
    (by native_decide)


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
        decide (Core.Expression.eval xIs1Env.factory xIs1Env.store lc.2.expr ≠
          some (Imperative.HasBool.tt : Core.Expression.Expr))) = true := by
  native_decide

/-- **Valid.**  The one non-`free` `ensures` is among the `requires`. -/
theorem freeOk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple φ freeOkPgmAST testParams "FreeOk" :=
  Core.Logic.Hoare.Procedure.contractTriple_nil_of_ensuresAmongRequires φ
    freeOkPgmAST testParams "FreeOk" freeOkProc (by native_decide) (by native_decide)
    (by native_decide)


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

/-- **Invalid.**  A procedure with no `requires` but an `ensures x == 2` does not meet
    its contract: nothing is assumed on entry and the empty body changes nothing, so at
    `xIs1Env` — where `x` holds `1` — the postcondition is refuted. -/
theorem noReq_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple φ noReqPgmAST testParams "NoReq" := by
  intro h
  obtain ⟨proc, bss, hproc, hbody, htb⟩ := h
  have hp : proc = noReqProc := (procOf_eq hproc).symm
  subst hp
  have hb : bss = [] := by
    injection hbody.symm.trans (show noReqProc.body = .structured [] by native_decide)
  subst hb
  have ⟨hpost, _⟩ := htb xIs1Env xIs1Env
    ⟨Core.Logic.Hoare.Procedure.preAsPredicate_of_preHoldsAt (by native_decide), rfl⟩
    (blockWF_nil xIs1Env rfl xIs1Env_storeWellDefined) rfl
    (.inl (run_procBlock_nil φ _ xIs1Env "" #[]))
  exact Core.Logic.Hoare.Procedure.not_postAsPredicate_of_postRefutedAt
    (by native_decide) hpost


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

/-- The precondition really is satisfied at `xIs1Env` — so the refutation below
    is not vacuous. -/
example : Core.Logic.Hoare.Procedure.preHoldsAt offByOneProc xIs1Env = true := by native_decide

/-- **Invalid.**  A procedure requiring `x == 1` and ensuring `x == 2` does not meet its
    contract: the empty body leaves `x` holding `1`, so the postcondition is refuted on a
    run whose precondition genuinely held. -/
theorem offByOne_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple φ offByOnePgmAST testParams "OffByOne" := by
  intro h
  obtain ⟨proc, bss, hproc, hbody, htb⟩ := h
  have hp : proc = offByOneProc := (procOf_eq hproc).symm
  subst hp
  have hb : bss = [] := by
    injection hbody.symm.trans (show offByOneProc.body = .structured [] by native_decide)
  subst hb
  have ⟨hpost, _⟩ := htb xIs1Env xIs1Env
    ⟨Core.Logic.Hoare.Procedure.preAsPredicate_of_preHoldsAt (by native_decide), rfl⟩
    (blockWF_nil xIs1Env rfl xIs1Env_storeWellDefined) rfl
    (.inl (run_procBlock_nil φ _ xIs1Env "" #[]))
  exact Core.Logic.Hoare.Procedure.not_postAsPredicate_of_postRefutedAt
    (by native_decide) hpost

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
  simp only [Imperative.dropVars, if_neg hnd]
  exact hpost

/-- `Core.Logic.Hoare.set` at a literal right-hand side. -/
private theorem set_const (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams)
    (x : Core.Expression.Ident) (κ : Lambda.LConst)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore), Pre ρ₀ →
      σ' x = some (Lambda.LExpr.const () κ) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ', hasFailure := Bool.false }) :
    Core.Logic.Hoare.Triple π φ params Pre
      [Core.Statement.set x (Lambda.LExpr.const () κ) md] Post :=
  Core.Logic.Hoare.set π φ params x _ md Pre Post
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
      Post { ρ₀ with store := σ', hasFailure := Bool.false }) :
    Core.Logic.Hoare.Triple π φ params Pre
      [Core.Statement.init x ty (.det (Lambda.LExpr.const () κ)) md] Post :=
  Core.Logic.Hoare.init π φ params x ty _ md Pre Post
    (fun ρ₀ σ' v hpre hev hinit => by
      have hv : v = Lambda.LExpr.const () κ := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_const ρ₀.factory ρ₀.store () κ))
      subst hv
      cases hinit with
      | init _hold hnew hoth => exact hpost ρ₀ σ' hpre hnew hoth)

/-- `Core.Logic.Hoare.set` where the right-hand side is a variable known to hold a
    literal; `Lambda.evalFully_fvar_of_value` reads it, needing only that the binding is a
    canonical value — which a literal is, in every factory. -/
private theorem set_fvar (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams)
    (x src : Core.Expression.Ident) (ty : Option Lambda.LMonoTy) (κ : Lambda.LConst)
    (md : Imperative.MetaData Core.Expression)
    (Pre Post : Imperative.Env Core.Expression → Prop)
    (hsrc : ∀ ρ₀, Pre ρ₀ → ρ₀.store src = some (Lambda.LExpr.const () κ))
    (hpost : ∀ (ρ₀ : Imperative.Env Core.Expression) (σ' : Core.CoreStore), Pre ρ₀ →
      σ' x = some (Lambda.LExpr.const () κ) → (∀ w, x ≠ w → σ' w = ρ₀.store w) →
      Post { ρ₀ with store := σ', hasFailure := Bool.false }) :
    Core.Logic.Hoare.Triple π φ params Pre
      [Core.Statement.set x (Lambda.LExpr.fvar () src ty) md] Post :=
  Core.Logic.Hoare.set π φ params x _ md Pre Post
    (fun ρ₀ σ' v hpre hev hup => by
      have hv : v = Lambda.LExpr.const () κ := (Option.some.injEq _ _).mp
        (hev.symm.trans (Lambda.evalFully_fvar_of_value ρ₀.factory ρ₀.store () src ty _
          (hsrc ρ₀ hpre) (Lambda.isCanonicalValue_const_true _ _ _)))
      subst hv
      cases hup with
      | update _hold hnew hoth => exact hpost ρ₀ σ' hpre hnew hoth)

/-- The type an `int`-typed variable carries in a translated `ensures` clause. -/
private def intTy : Option Lambda.LMonoTy := some (Lambda.LMonoTy.tcons "int" [])

/-- Metadata of a statement list that is a single assignment. -/
private def branchMd (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
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

/-- **From store facts to a postcondition.**  If every non-`free` `ensures` is
    `x == κ` for a listed `(x, κ)`, and the store binds each listed `x` to its `κ`,
    the postcondition holds.  `Lambda.evalFully_eq_self` does the work: both sides
    of the `==` reduce to the same literal. -/
private theorem postAsPredicate_of_binds (proc : Core.Procedure)
    (ρ : Imperative.Env Core.Expression)
    (binds : List (Core.Expression.Ident × Option Lambda.LMonoTy × Lambda.LConst))
    (hsyn : ensuresAllEqConst proc binds = Bool.true)
    (hstore : ∀ b ∈ binds, ρ.store b.1 = some (Lambda.LExpr.const () b.2.2)) :
    Core.Logic.Hoare.Procedure.postAsPredicate proc ρ := by
  intro label check hmem hattr
  simp only [ensuresAllEqConst, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at hsyn
  rcases hsyn (label, check) hmem with hattr' | ⟨b, hb, hexpr⟩
  · exact absurd hattr hattr'
  · rw [hexpr]
    exact Lambda.evalFully_eq_self ρ.factory ρ.store () _ _ (Lambda.LExpr.const () b.2.2)
      (Lambda.evalFully_fvar_of_value ρ.factory ρ.store () b.1 b.2.1 _ (hstore b hb)
        (Lambda.isCanonicalValue_const_true _ _ _))
      (Lambda.evalFully_const ρ.factory ρ.store () b.2.2)

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
    (hsyn : ensuresAllEqConst proc [(x, ty, κ)] = Bool.true) :
    Core.Logic.Hoare.Procedure.contractTriple φ p params procName :=
  Core.Logic.Hoare.Procedure.contractTriple_of φ p params procName proc _ hproc hbody
    (Core.Logic.Hoare.block p.findProcByString? φ params
      (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl])
      (set_const φ p.findProcByString? params x κ md _ _
        (fun _ρ₀ _σ' _hpre hnew _hoth =>
          postAsPredicate_of_binds proc _ [(x, ty, κ)] hsyn
            (fun b hb => by simp only [List.mem_singleton] at hb; subst hb; exact hnew)))
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _
        (by simp [Core.Statement.set, Imperative.Block.definedVars,
          Imperative.Stmt.definedVars, Imperative.HasVarsImp.definedVars,
          Core.Command.definedVars, Imperative.Cmd.definedVars])))


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

The contract holds at every `params`, `φ` and initial environment satisfying the
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
  | .structured [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- The assigned variable. -/
private def set1Y : Core.Expression.Ident := ⟨"y", ()⟩

/-- The translated body really is the single assignment `y := 1`. -/
private theorem set1_body_eq :
    set1Proc.body = .structured
      [Core.Statement.set set1Y (Lambda.LExpr.const () (.intConst 1)) set1Md] := by
  native_decide

/-- **Valid, and fully proved.**  `Set1` meets its contract: for every factory
    extension `φ` and initial environment satisfying the well-formedness condition,
    the body leaves `y == 1` true and raises no failure. -/
theorem set1_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple φ set1PgmAST testParams "Set1" :=
  contractTriple_set_const φ set1PgmAST testParams "Set1" set1Proc
    (by native_decide) set1Y intTy (.intConst 1) set1Md set1_body_eq (by native_decide)


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

`seq` also asks that the prefix declare no function (`Block.noFuncDecl`) — syntactic,
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
    | some (Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md))) => md
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
    Core.Logic.Hoare.Procedure.contractTriple φ set2PgmAST testParams "Set2" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ set2PgmAST testParams
    "Set2" set2Proc _ (by native_decide) set2_body_eq ?_
  refine Core.Logic.Hoare.block set2PgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.seq set2PgmAST.findProcByString? φ testParams
    (Mid := fun ρ => ρ.store set2Y = some (Lambda.LExpr.const () (.intConst 1)))
    (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl]) ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 1` establishes the store fact about `y`.
    exact set_const φ set2PgmAST.findProcByString? testParams set2Y (.intConst 1) (set2Md 0)
      (Core.Logic.Hoare.Procedure.preAsPredicate set2Proc) _
      (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
  · -- `z := 2` keeps that fact (it only writes `z`) and adds one about `z`.
    refine set_const φ set2PgmAST.findProcByString? testParams set2Z (.intConst 2)
      (set2Md 1) _ _ (fun ρ₀ σ' hmid hnew hoth => ?_)
    refine postAsPredicate_of_binds set2Proc _
      [(set2Y, intTy, .intConst 1), (set2Z, intTy, .intConst 2)] (by native_decide) ?_
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with h | h
    · subst h
      show σ' set2Y = _
      rw [hoth set2Y (by decide)]; exact hmid
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
its single premise "the binding read is a canonical value", which the intermediate
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
  | .structured [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.init _ ty _ md0)),
                 Imperative.Stmt.cmd (Core.CmdExt.cmd
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
    Core.Logic.Hoare.Procedure.contractTriple φ initVarPgmAST testParams "InitVar" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ initVarPgmAST testParams
    "InitVar" initVarProc _ (by native_decide) initVar_body_eq ?_
  -- The body declares `t`, which leaving the procedure block drops, so the
  -- postcondition is carried as a store fact about `y` and read off outside the block.
  refine Core.Logic.Hoare.consequence initVarPgmAST.findProcByString? φ testParams
    (Core.Logic.Hoare.block initVarPgmAST.findProcByString? φ testParams
      (Post := fun ρ => ρ.store initVarY = some (Lambda.LExpr.const () (.intConst 3)))
      (by native_decide) ?_
      (postWF_store_fact initVarBody initVarY (.intConst 3) (by native_decide)))
    (fun _ h => h)
    (fun ρ h => postAsPredicate_of_binds initVarProc ρ [(initVarY, intTy, .intConst 3)]
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h))
  refine Core.Logic.Hoare.seq initVarPgmAST.findProcByString? φ testParams
    (Mid := fun ρ => ρ.store initVarT = some (Lambda.LExpr.const () (.intConst 3)))
    (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl]) ?_ ?_
    ⟨trivial, trivial⟩
  · -- `var t : int := 3` establishes the store fact about `t`.
    exact init_const φ initVarPgmAST.findProcByString? testParams initVarT initVarParts.1
      (.intConst 3) initVarParts.2.1
      (Core.Logic.Hoare.Procedure.preAsPredicate initVarProc) _
      (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
  · -- `y := t` copies it to `y`.
    exact set_fvar φ initVarPgmAST.findProcByString? testParams initVarY initVarT
      initVarParts.2.2.1 (.intConst 3) initVarParts.2.2.2 _ _ (fun _ρ₀ hmid => hmid)
      (fun _ρ₀ _σ' _hmid hnew _hoth => hnew)


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
    Core.Logic.Hoare.Procedure.contractTriple φ ite1PgmAST testParams "Ite1" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ ite1PgmAST testParams
    "Ite1" ite1Proc _ (by native_decide) ite1_body_eq ?_
  refine Core.Logic.Hoare.block ite1PgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.consequence ite1PgmAST.findProcByString? φ testParams
    (Core.Logic.Hoare.ite ite1PgmAST.findProcByString? φ testParams
      (Post := fun ρ => ρ.store ite1Z = some (Lambda.LExpr.const () (.intConst 1)))
      (by native_decide) ?_ ?_
      (postWF_store_fact ite1Parts.2.1 ite1Z (.intConst 1) (by native_decide))
      (postWF_store_fact ite1Parts.2.2.1 ite1Z (.intConst 1) (by native_decide)))
    (fun _ h => h)
    (fun ρ h => postAsPredicate_of_binds ite1Proc ρ [(ite1Z, intTy, .intConst 1)]
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h))
  · rw [ite1Then_eq]
    exact set_const φ ite1PgmAST.findProcByString? testParams ite1Z (.intConst 1)
      (branchMd ite1Parts.2.1) _ _ (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
  · rw [ite1Else_eq]
    exact set_const φ ite1PgmAST.findProcByString? testParams ite1Z (.intConst 1)
      (branchMd ite1Parts.2.2.1) _ _ (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)



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
    Core.Logic.Hoare.Procedure.contractTriple φ blk1PgmAST testParams "Blk1" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ blk1PgmAST testParams
    "Blk1" blk1Proc _ (by native_decide) blk1_body_eq ?_
  refine Core.Logic.Hoare.block blk1PgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.consequence blk1PgmAST.findProcByString? φ testParams
    (Core.Logic.Hoare.block blk1PgmAST.findProcByString? φ testParams
      (Post := fun ρ => ρ.store blk1Y = some (Lambda.LExpr.const () (.intConst 5)))
      (by native_decide) ?_
      (postWF_store_fact blk1Parts.2.1 blk1Y (.intConst 5) (by native_decide)))
    (fun _ h => h)
    (fun ρ h => postAsPredicate_of_binds blk1Proc ρ [(blk1Y, intTy, .intConst 5)]
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h))
  · rw [blk1Inner_eq]
    exact set_const φ blk1PgmAST.findProcByString? testParams blk1Y (.intConst 5)
      (branchMd blk1Parts.2.1) _ _ (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)



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
  | [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
     Imperative.Stmt.exit l md1,
     Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md2))] => (md0, l, md1, md2)
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
    Core.Logic.Hoare.Procedure.contractTriple φ exitBlkPgmAST testParams "ExitBlk" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ exitBlkPgmAST testParams
    "ExitBlk" exitBlkProc _ (by native_decide) exitBlk_body_eq ?_
  refine Core.Logic.Hoare.block exitBlkPgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.consequence exitBlkPgmAST.findProcByString? φ testParams
    (Core.Logic.Hoare.block exitBlkPgmAST.findProcByString? φ testParams
      (Post := fun ρ => ρ.store exitBlkY = some (Lambda.LExpr.const () (.intConst 4)))
      (by native_decide) ?_
      (postWF_store_fact exitBlkParts.2.1 exitBlkY (.intConst 4) (by native_decide)))
    (fun _ h => h)
    (fun ρ h => postAsPredicate_of_binds exitBlkProc ρ [(exitBlkY, intTy, .intConst 4)]
      (by native_decide)
      (fun b hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb; exact h))
  · rw [exitBlkInner_eq]
    refine Core.Logic.Hoare.seq exitBlkPgmAST.findProcByString? φ testParams
      (Mid := fun ρ => ρ.store exitBlkY = some (Lambda.LExpr.const () (.intConst 4)))
      (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl]) ?_ ?_
      ⟨trivial, trivial⟩
    · exact set_const φ exitBlkPgmAST.findProcByString? testParams exitBlkY
        (.intConst 4) exitBlkInnerParts.1 _ _ (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
    · exact Core.Logic.Hoare.exit_cons exitBlkPgmAST.findProcByString? φ testParams _



/-! ## A body with an `assume` and an `assert`

`procedure Chk(x : int) spec { ensures x == 1; } { assume [a]: x == 1; assert [b]: x == 1; }`

The first test whose body is neither an assignment nor a control construct.  Both commands
leave the store alone, so nothing here is a store fact: the intermediate assertion is the
*evaluation* fact `x == 1 ⇓ true`, which the `assume` supplies (its rule has no step
otherwise) and which rules out `EvalCmd.eval_assert_fail`, so the `assert` cannot fail. -/

/-- `assume e` leaves the store alone and makes `e ⇓ true` available afterwards: the
    semantics has no step for an assumption that does not hold. -/
private theorem assume_eval (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams) (l : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (Pre : Imperative.Env Core.Expression → Prop) :
    Core.Logic.Hoare.Triple π φ params Pre [Core.Statement.assume l e md]
      (fun ρ => Core.Expression.eval ρ.factory ρ.store e = some Imperative.HasBool.tt) := by
  refine Core.Logic.Hoare.cmd π φ params _ Pre _ (fun _ρ₀ _σ' _f _hpre _hwf hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_assume hev _hwfb => exact ⟨hev, rfl⟩

/-- A passing `assert`: from `e ⇓ true` the failing rule cannot fire, and the store is
    untouched, so the fact survives. -/
private theorem assert_eval (π : String → Option Core.Procedure)
    (params : Core.Logic.InitEnvWFParams) (l : String) (e : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) :
    Core.Logic.Hoare.Triple π φ params
      (fun ρ => Core.Expression.eval ρ.factory ρ.store e = some Imperative.HasBool.tt)
      [Core.Statement.assert l e md]
      (fun ρ => Core.Expression.eval ρ.factory ρ.store e = some Imperative.HasBool.tt) := by
  refine Core.Logic.Hoare.cmd π φ params _ _ _ (fun _ρ₀ _σ' _f hpre _hwf hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_assert_pass hev _hwfb => exact ⟨hev, rfl⟩
    | eval_assert_fail hff _hwfb => exact absurd (hpre.symm.trans hff) (by native_decide)

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
  | .structured [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.assume _ e md0)),
                 Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.assert _ _ md1))] =>
      (e, md0, md1)
  | _ => default

private def chkBody : Core.Statements :=
  [Core.Statement.assume "a" chkParts.1 chkParts.2.1] ++
  [Core.Statement.assert "b" chkParts.1 chkParts.2.2]

/-- The translated body really is the `assume` then the `assert`, on the same expression. -/
private theorem chk_body_eq : chkProc.body = .structured chkBody := by native_decide

/-- **Valid, and fully proved.**  The `assume` supplies the very fact the `ensures`
    asserts, and the `assert` on the same expression cannot fail. -/
theorem chk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple φ chkPgmAST testParams "Chk" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ chkPgmAST testParams
    "Chk" chkProc _ (by native_decide) chk_body_eq ?_
  refine Core.Logic.Hoare.block chkPgmAST.findProcByString? φ testParams
    (by native_decide) ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.consequence chkPgmAST.findProcByString? φ testParams
    (Core.Logic.Hoare.seq chkPgmAST.findProcByString? φ testParams
      (Mid := fun ρ =>
        Core.Expression.eval ρ.factory ρ.store chkParts.1 = some Imperative.HasBool.tt)
      (by native_decide)
      (assume_eval φ chkPgmAST.findProcByString? testParams "a" chkParts.1 chkParts.2.1 _)
      (assert_eval φ chkPgmAST.findProcByString? testParams "b" chkParts.1 chkParts.2.2)
      ⟨trivial, trivial⟩)
    (fun _ h => h)
    (fun ρ h label check hmem _hattr => ?_)
  have hexpr : check.expr = chkParts.1 := by
    have hall : ∀ lc ∈ chkProc.spec.postconditions.toList, (Prod.snd lc).expr = chkParts.1 := by
      native_decide
    exact hall (label, check) hmem
  rw [hexpr]; exact h


/-! ## A while loop that terminates

`procedure LoopTerm(out y : int) spec { ensures y == 10; }
 { y := 0; while (int.le(y, 9)) { y := int.add(y, 1); } }`

A genuine counting loop, *fully verified to its result*: `y` starts at `0`, the body
increments it while `y ≤ 9`, and the contract `y == 10` holds on exit.

This is the payoff of pinning `ρ.factory = Core.Factory` in `Procedure.contractTriple`.
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
  | .structured [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
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
  | [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ (.det e) md))] => (e, md)
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
      (Lambda.isCanonicalValue_const_true _ _ _))

/-- With `y ↦ n`, the loop body assigns `n + 1` on `Core.Factory`. -/
private theorem loopTermRhs_eval (σ : Core.CoreStore) (n : Int)
    (hσy : σ loopTermY = some (Lambda.LExpr.intConst () n)) :
    Core.Expression.eval Core.Factory σ loopTermInnerParts.1
      = some (Lambda.LExpr.intConst () (n + 1)) := by
  rw [loopTermRhs_shape]
  exact Core.coreEval_intAdd_numeral σ (Lambda.LExpr.fvar () loopTermY intTy) n
    (Lambda.evalFully_fvar_of_value Core.Factory σ () loopTermY intTy _ hσy
      (Lambda.isCanonicalValue_const_true _ _ _))

/-- **Valid, and fully proved.**
    `y := 0; while (int.le(y, 9)) { y := int.add(y, 1) }` establishes `y == 10`.

    Because `Procedure.contractTriple` pins `ρ.factory = Core.Factory`, the concrete
    evaluator's arithmetic is available (`coreEval_intAdd_numeral`, `coreEval_intLe_numeral`),
    so the invariant tracks `y`'s value: `0 ≤ y ≤ 10` together with the factory being
    `Core.Factory`.  `y := 0` establishes it; the body takes `y ↦ n` (the guard giving
    `n ≤ 9`) to `y ↦ n + 1`, still `≤ 10`; and on exit the negated guard `¬ (y ≤ 9)` with
    `y ≤ 10` forces `y = 10`. -/
theorem loopTerm_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple φ loopTermPgmAST testParams "LoopTerm" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core φ loopTermPgmAST testParams
    "LoopTerm" loopTermProc _ (by native_decide) loopTerm_body_eq ?_
  refine Core.Logic.Hoare.block loopTermPgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.seq loopTermPgmAST.findProcByString? φ testParams
    (Mid := fun ρ => (∃ n : Int, ρ.store loopTermY = some (Lambda.LExpr.intConst () n)
        ∧ 0 ≤ n ∧ n ≤ 10) ∧ ρ.factory = Core.Factory)
    (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl]) ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 0` establishes `0 ≤ y ≤ 10` (and carries the factory through).
    exact set_const φ loopTermPgmAST.findProcByString? testParams loopTermY (.intConst 0)
      loopTermParts.1 _ _
      (fun _ρ₀ _σ' hpre hnew _hoth => ⟨⟨0, hnew, by decide, by decide⟩, hpre.2⟩)
  · -- The loop preserves `0 ≤ y ≤ 10`; the exit's `¬ (y ≤ 9)` then forces `y = 10`.
    refine Core.Logic.Hoare.consequence loopTermPgmAST.findProcByString? φ testParams
      (Core.Logic.Hoare.while_rule loopTermPgmAST.findProcByString? φ testParams
        (by native_decide) ?_ ?_ ?_)
      (fun _ h => h)
      (fun ρ h label check hmem _hattr => ?_)
    · -- body: `y := int.add(y, 1)` sends `n ≤ 9` to `n + 1 ≤ 10`.
      rw [loopTermInner_eq]
      refine Core.Logic.Hoare.set loopTermPgmAST.findProcByString? φ testParams loopTermY
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
      have hexpr : check.expr =
          Lambda.LExpr.eq () (Lambda.LExpr.fvar () loopTermY intTy)
            (Lambda.LExpr.const () (Lambda.LConst.intConst 10)) := by
        have hall : ∀ lc ∈ loopTermProc.spec.postconditions.toList,
            (Prod.snd lc).expr =
              Lambda.LExpr.eq () (Lambda.LExpr.fvar () loopTermY intTy)
                (Lambda.LExpr.const () (Lambda.LConst.intConst 10)) := by native_decide
        exact hall (label, check) hmem
      rw [hexpr, hfac]
      subst hn10
      exact Lambda.evalFully_eq_self Core.Factory ρ.store () _ _ (Lambda.LExpr.intConst () 10)
        (Lambda.evalFully_fvar_of_value Core.Factory ρ.store () loopTermY intTy _ hσy
          (Lambda.isCanonicalValue_const_true _ _ _))
        (Lambda.evalFully_const Core.Factory ρ.store () (Lambda.LConst.intConst 10))


/-! ## A while loop that never terminates

`procedure LoopForever(out y : int) spec { ensures false; }
 { y := 7; while (true) { y := 7; } }`

A `true` guard makes the loop diverge, so its *terminating* runs are exactly none, and
under partial correctness a procedure that never returns meets *any* contract — including
the unsatisfiable `ensures false`.

The proof pins this on the guard.  `while_rule` returns `Inv ∧ ¬guard` on exit, i.e.
`Inv ρ ∧ Expression.eval ρ.factory ρ.store guard = some HasBool.ff`.  The guard is the
literal `true`, which evaluates to `HasBool.tt` in *every* factory (a constant is its own
value — `evalFully_const`, no well-formedness needed), so `= some HasBool.ff` is
`some tt = some ff`, a contradiction.  The exit condition is therefore never satisfied,
and `consequence` turns it into `ensures false`: the postcondition is proved from the
impossibility of exiting, not from any run of the body.  The invariant `y ↦ 7` serves only
to satisfy `while_rule`'s remaining side conditions (`Block.noFuncDecl`, `hcov`, `PostWF`);
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
  | .structured [Imperative.Stmt.cmd (Core.CmdExt.cmd (Imperative.Cmd.set _ _ md0)),
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
    Core.Logic.Hoare.Procedure.contractTriple φ loopForeverPgmAST testParams "LoopForever" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of φ loopForeverPgmAST testParams
    "LoopForever" loopForeverProc _ (by native_decide) loopForever_body_eq ?_
  refine Core.Logic.Hoare.block loopForeverPgmAST.findProcByString? φ testParams
    (by native_decide) ?_ (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by native_decide))
  refine Core.Logic.Hoare.seq loopForeverPgmAST.findProcByString? φ testParams
    (Mid := fun ρ => ρ.store loopForeverY = some (Lambda.LExpr.const () (.intConst 7)))
    (by simp [Imperative.Block.noFuncDecl, Imperative.Stmt.noFuncDecl]) ?_ ?_
    ⟨trivial, trivial⟩
  · -- `y := 7` establishes the invariant.
    exact set_const φ loopForeverPgmAST.findProcByString? testParams loopForeverY (.intConst 7)
      loopForeverParts.1 (Core.Logic.Hoare.Procedure.preAsPredicate loopForeverProc) _
      (fun _ρ₀ _σ' _hpre hnew _hoth => hnew)
  · -- The loop diverges, so its exit condition is unsatisfiable and `ensures false` follows.
    refine Core.Logic.Hoare.consequence loopForeverPgmAST.findProcByString? φ testParams
      (Core.Logic.Hoare.while_rule loopForeverPgmAST.findProcByString? φ testParams
        (by native_decide) ?_ ?_ ?_)
      (fun _ h => h)
      (fun ρ h => ?_)
    · -- body: re-establish the invariant
      rw [loopForeverInner_eq]
      exact set_const φ loopForeverPgmAST.findProcByString? testParams loopForeverY (.intConst 7)
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
    { store := fun y => if y = x then some (Lambda.LExpr.const () (.intConst 1)) else none,
      factory := Core.Factory, hasFailure := false } (by simp)
  simp [Imperative.dropVars, Core.Statement.init, Imperative.Block.definedVars,
    Imperative.Stmt.definedVars, Imperative.HasVarsImp.definedVars,
    Core.Command.definedVars, Imperative.Cmd.definedVars] at hbad


end Strata


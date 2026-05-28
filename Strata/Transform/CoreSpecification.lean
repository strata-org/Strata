/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Transform.Specification
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Options
public import Strata.Languages.Core.Verifier
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.Factory

public section

/-! # Core-Level Specification

Bridges Core procedures to the generic Imperative specification framework
(`AssertValidWhen`, `AllAssertsValidWhen`).

## Overview

- **`Lang.core`** — the `Lang Expression` bundle for Core small-step semantics
- **`ProcEnvWF`** — well-formedness condition on the initial verification env
- **`AssertValidInProcedure`** — `AssertValidWhen` on the verification statement
- **`AssertSatisfiableInProcedure`** — `AssertSatisfiableWhen` on the verification statement
- **`ProcedureAssertsValid`** — assert validity + postconditions + hasFailure on termination
- **`ProcedureAssertsSatisfiable`** — existential dual: some run reaches each
  assert with a passing expression and some terminating run satisfies the
  postconditions (the natural target for bug-finding modes)
-/

namespace Core

/-- A `String → Option Procedure` view of a `Program`, suitable for use as
    the `π` argument to the Core small-step semantics.

    `Program.find?` returns `Option Decl` and is keyed on `Expression.Ident`
    (a `CoreIdent`). This variant takes a raw `String` (matching the
    `String → Option Procedure` shape that small-step semantics expects)
    and projects the resulting declaration to its `Procedure`. -/
@[expose] def Program.findProcByString?
    (p : Program) (n : String) : Option Procedure :=
  (p.find? .proc ⟨n, ()⟩).bind Decl.getProc?

end Core

namespace Core.Specification

open Core Imperative

/-! ## Core `Lang` bundle -/

/-- Store-well-formedness needed for a statement `s` to execute in env `ρ` without
    getting stuck. -/
structure InitEnvWF (reserved : List String)
    (declaredFuncs : Expression.Ident → Bool)
    (s : Statement) (ρ : Imperative.Env Expression) :
    Prop where
  readWritesDefined : ∀ n ∈ Stmt.touchedVars s, n ∉ Stmt.definedVars s false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Stmt.definedVars s false, (ρ.store n).isNone
  /-- Source's `definedVars` don't use any of the reserved prefixes. -/
  definedVarsNotReserved : ∀ n ∈ Stmt.definedVars s false, ∀ p ∈ reserved,
    ¬ p.toList.isPrefixOf n.name.toList
  /-- Source's `funcDeclNames` don't use any of the reserved prefixes.
      `funcDecl` names live in the evaluator (not the store), so they aren't
      covered by `definedVarsNotReserved`. -/
  funcDeclNamesNotReserved : ∀ n ∈ Stmt.funcDeclNames s false, ∀ p ∈ reserved,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfVal  : WellFormedSemanticEvalVal ρ.eval
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  wfInt : WellFormedSemanticEvalInt ρ.eval
  evalCong : WellFormedCoreEvalCong ρ.eval
  exprCongr : WellFormedSemanticEvalExprCongr ρ.eval
  defUseOk : Stmt.defUseWellFormed (fun n => (ρ.store n).isSome) declaredFuncs s = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    declaredFuncs ⟨s, ()⟩ = Bool.true

/-- Block-level analog of `InitEnvWF`: well-formedness for executing a block of
    statements `bss` from env `ρ`. -/
structure BlockInitEnvWF (reserved : List String)
    (declaredFuncs : Expression.Ident → Bool)
    (bss : Statements)
    (ρ : Imperative.Env Expression) : Prop where
  readWritesDefined : ∀ n ∈ Block.touchedVars bss, n ∉ Block.definedVars bss false →
    (ρ.store n).isSome
  defsUndefined : ∀ n ∈ Block.definedVars bss false, (ρ.store n).isNone
  definedVarsNotReserved : ∀ n ∈ Block.definedVars bss false, ∀ p ∈ reserved,
    ¬ p.toList.isPrefixOf n.name.toList
  funcDeclNamesNotReserved : ∀ n ∈ Block.funcDeclNames bss false, ∀ p ∈ reserved,
    ¬ p.toList.isPrefixOf n.name.toList
  reservedFresh : ∀ n, (ρ.store n).isSome →
    ∀ p ∈ reserved, ¬ p.toList.isPrefixOf n.name.toList
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfVal  : WellFormedSemanticEvalVal ρ.eval
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  wfInt : WellFormedSemanticEvalInt ρ.eval
  evalCong : WellFormedCoreEvalCong ρ.eval
  exprCongr : WellFormedSemanticEvalExprCongr ρ.eval
  defUseOk : Block.defUseWellFormed (fun n => (ρ.store n).isSome) declaredFuncs bss = Bool.true
  factoryDeclared : ∀ s, Core.isNameInFactory s = Bool.true →
    declaredFuncs ⟨s, ()⟩ = Bool.true

/-! ## Core factory-membership lemmas

Used by transforms (e.g. `LoopElim`) that synthesize references to standard
ops to discharge the `factoryDeclared` precondition for those specific ops. -/

theorem boolNot_isNameInFactory :
    Core.isNameInFactory "Bool.Not" = Bool.true := by native_decide

theorem intLt_isNameInFactory :
    Core.isNameInFactory "Int.Lt" = Bool.true := by native_decide

/-- The `Lang Expression` bundle for Core small-step semantics. -/
@[expose] def Lang.core
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval) :
    Imperative.Specification.Lang Expression :=
  Imperative.Specification.Lang.imperative
    Expression Command (EvalCommand π φ) (EvalPureFunc φ) coreIsAtAssert
    InitEnvWF

/-! ## Well-formed program state at the entry of procedure -/

/-- The list of variables that must have been declared,
    to make execution of the body of this procedure not stuck.
    outputs are included because the body refers to the output variables without
    initialization.
    Old snapshot variables for in-out parameters (those appearing in both
    inputs and outputs) are included because the body or spec of the
    procedure may refer to those with "old g".  -/
@[expose] def procVerifyInitIdents (proc : Procedure) : List Expression.Ident :=
  ListMap.keys proc.header.inputs ++
  ListMap.keys proc.header.outputs ++
  (ListMap.keys proc.header.getInoutParams).map (fun id => CoreIdent.mkOld id.name)

/-- A well-formed initial environment for executing the procedure body.
    This captures the state after inputs, outputs, modified globals have been
    initialized and preconditions assumed.
    The well-formed environment also includes old snapshots in store -/
structure ProcEnvWF (proc : Procedure) (ρ : Imperative.Env Expression) : Prop where
  wfVar  : WellFormedSemanticEvalVar ρ.eval
  wfBool : WellFormedSemanticEvalBool ρ.eval
  wfCong : WellFormedCoreEvalCong ρ.eval
  wfExprCongr : WellFormedSemanticEvalExprCongr ρ.eval
  storeDefined : ∀ id ∈ procVerifyInitIdents proc, (ρ.store id).isSome
  -- When a procedure is called, the value of "old g" must be equal to "g"
  -- for in-out parameters.
  oldInoutMatchesInout : ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store id = ρ.store (CoreIdent.mkOld id.name)
  -- Precondition holds in the body, and input state had no failure.
  preconditionsHold : ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    ρ.eval ρ.store check.expr = some HasBool.tt
  noFailure : ρ.hasFailure = Bool.false

/-! ## Axioms and distincts visible to a procedure

A program also contains `axiom` declarations (boolean expressions that holds
globally) and `distinct` declarations (lists of expressions whose values must differ).
For verification, the initial environment of a procedure must satisfy the
axioms and distincts that have been declared *before* the procedure in the
program. -/

/-- Walks a list of declarations and accumulates the axioms/distincts that
    precede the first `.proc` declaration whose name matches `entryProcName`.
    Used as the recursive workhorse of `AxiomsBeforeProcedureDecl`. -/
@[expose] def AxiomsBeforeProcedureDecl.go
    (entryProcName : String) (ρ₀ : Imperative.Env Expression) :
    List Decl → Prop
  | [] => True
  | .ax a _ :: rest =>
      ρ₀.eval ρ₀.store a.e = some HasBool.tt ∧
      AxiomsBeforeProcedureDecl.go entryProcName ρ₀ rest
  | .distinct _ es _ :: rest =>
      List.Pairwise (fun e₁ e₂ => ρ₀.eval ρ₀.store e₁ ≠ ρ₀.eval ρ₀.store e₂) es ∧
      AxiomsBeforeProcedureDecl.go entryProcName ρ₀ rest
  | .proc proc _ :: rest =>
      -- Stop walking once the entry procedure is reached.
      if proc.header.name.name = entryProcName then True
      else AxiomsBeforeProcedureDecl.go entryProcName ρ₀ rest
  | _ :: rest =>
      AxiomsBeforeProcedureDecl.go entryProcName ρ₀ rest

/-- The initial environment `ρ₀` satisfies all axioms and `distinct`
    declarations that appear in `p.decls` before the procedure named
    `entryProcName`.

    For each preceding `.ax a _`, `ρ₀.eval ρ₀.store a.e = some tt` (mirrors
    `ProcEnvWF.preconditionsHold`). For each preceding `.distinct _ es _`,
    the expressions in `es` evaluate to pairwise distinct values under `ρ₀`. -/
@[expose] def AxiomsBeforeProcedureDecl
    (entryProcName : String) (p : Program)
    (ρ₀ : Imperative.Env Expression) : Prop :=
  AxiomsBeforeProcedureDecl.go entryProcName ρ₀ p.decls

/-! ## Procedure correctness -/

variable (φ : CoreEval → PureFunc Expression → CoreEval)

/-- A specific assertion `a` in procedure `proc` is valid for initial program
    states that satisfy `ProcEnvWF proc` and the program-level axioms and
    distincts visible to `entryProcName` (`AxiomsBeforeProcedureDecl`). -/
@[expose] def AssertValidInProcedure
    (entryProcName : String) (p : Program) (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  match proc.body with
  | .structured ss =>
    Imperative.Specification.AssertValidWhen (Specification.Lang.core p.findProcByString? φ)
      (fun ρ₀ => ProcEnvWF proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀)
      (Stmt.block "" ss #[]) a
  -- CFG bodies don't yet have a small-step semantics, so there is nothing to
  -- certify.  We pick `False` rather than `True` to be conservative: a CFG
  -- procedure cannot be claimed asserts-valid (and hence cannot be proven
  -- `ProcedureAssertsValid`) until CFG bodies gain an executable semantics.
  -- This is sound against the current proofs because the only producer of
  -- `ProcedureAssertsValid` (`procBodyVerify_procedureCorrect`) is gated on
  -- `procToVerifyStmt` succeeding, which forces `proc.body = .structured _`
  -- (see `procToVerifyStmt_is_structured`), so this arm is never entered.
  | .cfg _ => False

/-- A specific assertion `a` in procedure `proc` is satisfiable: some initial
    program state satisfying `ProcEnvWF proc` and `AxiomsBeforeProcedureDecl`
    reaches a configuration at the assert with the expression evaluating to
    `tt`.

    Same `body`-shape treatment as `AssertValidInProcedure`: structured bodies
    use the small-step semantics; CFG bodies are vacuously *not* satisfiable
    (we use `False`) until CFG semantics is defined. -/
@[expose] def AssertSatisfiableInProcedure
    (entryProcName : String) (p : Program) (proc : Procedure)
    (a : Imperative.AssertId Expression) : Prop :=
  match proc.body with
  | .structured ss =>
    Imperative.Specification.AssertSatisfiableWhen (Specification.Lang.core p.findProcByString? φ)
      (fun ρ₀ => ProcEnvWF proc ρ₀ ∧ AxiomsBeforeProcedureDecl entryProcName p ρ₀)
      (Stmt.block "" ss #[]) a
  | .cfg _ => False

/-- The procedure named `entryProcName` (looked up in `p` via
    `Program.findProcByString?`) has every assert valid and its postconditions
    valid on termination.

    0. The procedure exists in `p` (`procedureExists`);

    1. Every reachable assert in the procedure body evaluates to `true`
       (`AssertValidInProcedure`);

    2. Postcondition: When the procedure body terminates from a `ProcEnvWF`
       initial environment, every non-free postcondition holds and
       `hasFailure` stays `false`.

    This is partial correctness: if the program has an infinite loop, the
    postcondition is considered to be satisfied. Since total correctness is
    a conjunction of partial correctness and termination, having partial
    correctness-only definition here is useful.

    A possibly more succinct style of ProcedureAssertsValid is using Hoare
    triple (`Hoare.Triple` in Specification.lean). Since `Hoare.Triple` also
    uses partial correctness, this seems natural. However, there is a very
    subtle issue due to the fact that programs can also have `assert`s in the
    middle of procedures, which leads `Hoare.Triple` to too weak notion to use
    for us.

    For example, let's consider this program:

    ```
    procedure P()
    spec { ensures false; }
    { while true {};
    };
    ```

    Since the program iterates indefinitely, the postcondition is considered
    met in our partial correctness definition; hence the contract is true.
    This is OK.

    However, if we slightly extend the body of P to include `assert false`:

    ```
    procedure P()
    spec { ensures false; }
    { assert false; // -- A
      while true {};
    };
    ```

    We know that the assert A does not hold. However, if we use `Hoare.Triple` which
    inspects asserts and postconditions *only if the code terminates*,
    we end up accepting this procedure P as 'correct'.

    Therefore, we define ProcedureAssertsValid as a structure with three fields:
    (0) the procedure exists in `p`,
    (1) assert validity in the body, and
    (2) postcondition validity on termination.
-/
structure ProcedureAssertsValid (entryProcName : String) (p : Program) : Prop where
  /-- (0) The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are valid. -/
  assertsValid : ∀ proc, p.findProcByString? entryProcName = some proc →
    ∀ a, AssertValidInProcedure φ entryProcName p proc a
  /-- (2) The postconditions hold on termination.
      Uses `CoreBodyExec` to abstract over both structured and CFG bodies.
      For structured bodies, the terminal eval `δ'` comes from the terminal
      `Env` (may differ from `δ` due to `funcDecl` extensions). For CFG
      bodies, `δ' = δ` since `CoreCFGStepStar` does not track eval changes.

      Note that postconditionsValid doesn't have to describe the validity of
      postconditions of other procedures called during execution of
      `entryProcName` because `call_sem` of `EvalCommand` will have the
      postcondition check (for the particular input of procedure invocation)
      already. -/
  postconditionsValid : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∀ (ρ₀ : Imperative.Env Expression),
      ProcEnvWF proc ρ₀ →
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ →
      ∀ (σ' : CoreStore) (δ' : CoreEval) (failed : Bool),
        CoreBodyExec p.findProcByString? φ proc.body ρ₀.store ρ₀.eval σ' δ' failed →
        (∀ (label : CoreLabel) (check : Procedure.Check),
          (label, check) ∈ proc.spec.postconditions.toList →
          check.attr = Procedure.CheckAttr.Default →
          δ' σ' check.expr = some HasBool.tt) ∧
        failed = Bool.false

/-- The existential dual of `ProcedureAssertsValid`, intended as the target
    for bug-finding–style analyses.

    0. The procedure exists in `p`;
    1. Every assert in the body is *satisfiable*: some `ProcEnvWF` initial
       environment reaches a configuration at the assert with the expression
       evaluating to `tt`;
    2. The postconditions are *satisfiable*: some terminating run from a
       `ProcEnvWF` initial environment makes every non-free postcondition
       evaluate to `tt` and leaves `hasFailure = false`. -/
structure ProcedureAssertsSatisfiable (entryProcName : String) (p : Program) : Prop where
  /-- (0) The procedure name resolves in `p`. -/
  procedureExists : ∃ proc, p.findProcByString? entryProcName = some proc
  /-- (1) The asserts in the body of the procedure are satisfiable. -/
  assertsSatisfiable : ∀ proc, p.findProcByString? entryProcName = some proc →
    ∀ a, AssertSatisfiableInProcedure φ entryProcName p proc a
  /-- (2) Some terminating run satisfies all postconditions.
      Note that postconditionsSatisfiable doesn't have to describe the satisfiability of postconditions
      of other procedures called during execution of entryProcName because call_sem of EvalCommand
      will have the postcondition check (for the particular input of procedure invocation)
      already.
  -/
  postconditionsSatisfiable : ∀ proc, p.findProcByString? entryProcName = some proc →
    WF.WFProcedureProp p proc →
    ∃ (ρ₀ : Imperative.Env Expression) (σ' : CoreStore) (δ' : CoreEval),
      ProcEnvWF proc ρ₀ ∧
      AxiomsBeforeProcedureDecl entryProcName p ρ₀ ∧
      CoreBodyExec p.findProcByString? φ proc.body ρ₀.store ρ₀.eval σ' δ' false ∧
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ proc.spec.postconditions.toList →
        check.attr = Procedure.CheckAttr.Default →
        δ' σ' check.expr = some HasBool.tt)

/-! ## Analysis -/

namespace Analysis

/-- A program input to a contract checker: the procedure names to consider as
    entry points, paired with the enclosing program. -/
structure CoreVerifierInput where
  entryPoints: String → Prop
  prog : Program

/-- An analysis whose desirable property under each `VerificationMode` is:

    * `.deductive` — `ProcedureAssertsValid` (universal: every assert valid
      and every terminating run satisfies the postconditions);
    * `.bugFinding` — `ProcedureAssertsSatisfiable` (existential dual: some
      run reaches each assert and some terminating run satisfies the
      postconditions);
    * `.bugFindingAssumingCompleteSpec` — `False` (not yet specified).

    The diagnostic is a `VCResults` array; the `analyze` function
    additionally receives the `VerificationMode` so it can shape the
    obligations it produces, and `pass` reports success on every `VCResult`
    under the given mode. -/
def CoreVerifierModel
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (mode : VerificationMode)
    (analyze : VerificationMode → CoreVerifierInput → VCResults) :
    Imperative.Specification.Analysis CoreVerifierInput VCResults :=
  { desirableProperty := fun input =>
      match mode with
      | .deductive =>
        forall procName, input.entryPoints procName
          → ProcedureAssertsValid φ procName input.prog
      | .bugFinding =>
        forall procName, input.entryPoints procName
          → ProcedureAssertsSatisfiable φ procName input.prog
      | .bugFindingAssumingCompleteSpec =>
        -- bugFinding, but postcondition being checked with validity
        -- TODO!
        False
    analyze := analyze mode
    pass := fun results =>
      match mode with
      | .deductive => ∀ r ∈ results, VCResult.isSuccess r = Bool.true
      | .bugFinding => ∀ r ∈ results, VCResult.isBugFindingSuccess r = Bool.true
      | .bugFindingAssumingCompleteSpec => False }

end Analysis

end Core.Specification

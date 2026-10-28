/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.LangDef
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

The entry conditions of a Core procedure: `ProcEnvWF`, the well-formed program
state at its entry, and `AxiomsBeforeProcedureDecl`, the axioms and distincts
visible to it. What it means for a procedure to be correct, and for Core's
verifier to be correct, is in `Strata.Languages.Core.Analysis.ProcedureCorrectness`.
The `Lang` bundles themselves (`Lang.core`, `Lang.coreBlock`) and their gates
(`InitEnvWFParams`, `InitEnvWF`, `BlockInitEnvWF`) live in
`Strata.Languages.Core.Logic.LangDef`.
-/

namespace Core.Specification

open Core Core.Logic Imperative Strata.Logic Imperative.Logic

/-! ## Well-formed program state at the entry of procedure -/

/-- The variables (paired with their declared monomorphic types) that must
    have been declared to make execution of the body of this procedure not
    stuck.

    inputs and outputs are included because the body refers to those variables
    without initialization.  Old snapshot variables for in-out parameters
    (those appearing in both inputs and outputs) are included because the body
    or spec of the procedure may refer to those with "old g".

    Each entry pairs the identifier with the type at which its initial value
    must be well-typed.  For an in-out parameter's old snapshot the type is the
    parameter's original declared type. -/
@[expose] def procVerifyInitIdents (proc : Procedure) :
    List (Expression.Ident × Lambda.LMonoTy) :=
  proc.header.inputs.toList ++
  proc.header.outputs.toList ++
  (proc.header.getInoutParams.toList).map (fun (id, ty) => (CoreIdent.mkOld id.name, ty))

/-- A well-formed initial environment for executing the procedure body.
    This captures the state after inputs, outputs, modified globals have been
    initialized and preconditions assumed.
    The well-formed environment also includes old snapshots in store, and the
    body is well formed to run from it under `params`.

    Procedure-correctness properties quantify over these environments, so they
    say nothing when `params` admits none. For example, with
    `declaredFuncs := fun _ => false`, `factoryDeclared` fails for every
    environment, and every procedure, even one with `ensures false`, satisfies
    them. Choose `params` so that it admits the program's entry environments. -/
structure ProcEnvWF (params : InitEnvWFParams) (proc : Procedure)
    (ρ : Imperative.Env Expression)
    extends WellFormedSemanticEval (P := Expression) ρ.factory where
  -- The verification env's store holds only values (true of reachable stores).
  -- The factory is read from the environment (`ρ.factory`).
  storeValues : Imperative.WellFormedStore ρ.store ρ.factory
  -- Every variable required by the body holds a value of its declared type
  -- in the initial verification environment.
  storeDefinedAndWellTyped : ∀ id ty, (id, ty) ∈ procVerifyInitIdents proc →
    ∃ v, ρ.store id = some v ∧
      HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty)
  -- When a procedure is called, the value of "old g" must be equal to "g"
  -- for in-out parameters.
  oldInoutMatchesInout : ∀ id ∈ ListMap.keys proc.header.getInoutParams,
    ρ.store id = ρ.store (CoreIdent.mkOld id.name)
  -- Precondition holds in the body, and input state had no failure.
  preconditionsHold : ∀ (label : CoreLabel) (check : Procedure.Check),
    (label, check) ∈ proc.spec.preconditions.toList →
    Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt
  noFailure : ρ.hasFailure = Bool.false
  /-- A structured body, as the block the procedure's specifications wrap it
      in, is well formed to run from `ρ`. -/
  structuredBodyWF : ∀ ss, proc.body = .structured ss →
    BlockInitEnvWF params [Stmt.block "" ss #[]] ρ
  /-- A CFG body is well formed to run from `ρ`. -/
  cfgBodyWF : ∀ cfg, proc.body = .cfg cfg → CFGInitEnvWF params cfg ρ

/-! ## Axioms and distincts visible to a procedure

A program also contains `axiom` declarations (boolean expressions that holds
globally) and `distinct` declarations (lists of expressions whose values must differ).
For verification, the initial environment of a procedure must satisfy the
axioms and distincts that have been declared *before* the procedure in the
program. -/

/-- Declarations in `p` that appear strictly before the procedure named
    `entryProcName`. -/
@[expose] def declsBefore (entryProcName : String) (p : Program) : List Decl :=
  p.decls.takeWhile fun d =>
    match d with
    | .proc proc _ => proc.header.name.name != entryProcName
    | _ => true

/-- The initial environment `ρ₀` satisfies all axioms and `distinct`
    declarations that appear in `p.decls` before the procedure named
    `entryProcName`. -/
@[expose] def AxiomsBeforeProcedureDecl
    (entryProcName : String) (p : Program)
    (ρ₀ : Imperative.Env Expression) : Prop :=
  (declsBefore entryProcName p).foldr
    (fun d acc =>
      match d with
      | .ax a _ =>
          Expression.eval ρ₀.factory ρ₀.store a.e = some HasBool.tt ∧ acc
      | .distinct _ es _ =>
          List.Pairwise (fun e₁ e₂ =>
            Expression.eval ρ₀.factory ρ₀.store e₁ ≠ Expression.eval ρ₀.factory ρ₀.store e₂) es ∧ acc
      | _ => acc)
    True

end Core.Specification

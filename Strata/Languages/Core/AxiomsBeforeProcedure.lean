/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.StatementSemantics

public section

/-! # Axioms and distincts visible to a procedure

A program also contains `axiom` declarations (boolean expressions that holds
globally) and `distinct` declarations (lists of expressions whose values must differ).
For verification, the initial environment of a procedure must satisfy the
axioms and distincts that have been declared *before* the procedure in the
program.

`AxiomsBeforeProcedureDecl` is an entry assumption of both readings of a
procedure's correctness: `Core.Specification.ProcEntryEnv` and
`Core.Logic.Hoare.Procedure.contractTriple`. It depends only on the program and
the evaluator, so it lives below both. -/

namespace Core.Specification

open Core Imperative

/-- The initial environment `ρ₀` satisfies all axioms and `distinct`
    declarations that appear in `p.decls` before the procedure named
    `entryProcName`. -/
@[expose] def AxiomsBeforeProcedureDecl
    (entryProcName : String) (p : Program)
    (ρ₀ : Imperative.Env Expression) : Prop :=
  (p.declsBeforeProcedure entryProcName).foldr
    (fun d acc =>
      match d with
      | .ax a _ =>
          Expression.eval ρ₀.factory ρ₀.store a.e = some (HasBool.ttVal ρ₀.factory) ∧ acc
      | .distinct _ es _ =>
          List.Pairwise (fun e₁ e₂ =>
            Expression.eval ρ₀.factory ρ₀.store e₁ ≠ Expression.eval ρ₀.factory ρ₀.store e₂) es ∧ acc
      | _ => acc)
    True

end Core.Specification

end -- public section

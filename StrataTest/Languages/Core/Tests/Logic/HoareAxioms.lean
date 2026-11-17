/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.Transform.CoreSpecificationProps
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # Hoare contracts that rest on an axiom

`Procedure.contractTriple` assumes, at the procedure's entry, the axioms declared
before the procedure. The example below declares a constant `c` with no definition,
so its value differs from model to model, and an axiom `c > 0`. The procedure
`Witness` has an empty body and ensures `c > 0`: the contract holds only because of
the axiom.

## Key results

- `witness_meets_contract`: `Witness` satisfies its contract, by the axiom.
- `witness_contract`: the same fact in the form of the `contract` field of
  `Core.Specification.ProcedureAssertsValidOnTraces.denote`, from
  `Core.Specification.contract_of_contractTriple`.
-/

open StrataDDM (Program)

namespace Strata.HoareAxiomsTest

open Strata.HoareUtils (testParams)

/-- Normalize the source locations of procedure and axiom expressions to
    `Core.valueLoc`, so the axiom and the `ensures` clause, written alike, are the
    same expression. -/
private def eraseProgLocs (pr : Core.Program) : Core.Program :=
  { pr with decls := pr.decls.map fun d => match d with
      | .proc proc md => .proc (Core.Procedure.mapExprs Core.eraseLocs proc) md
      | .ax a md => .ax { a with e := Core.eraseLocs a.e } md
      | other => other }

private def cstToAST (p : Program) : Core.Program :=
  eraseProgLocs (TransM.run Inhabited.default (translateProgram p)).fst

private def axiomPgm : Program :=
#strata
program Core;

const c : int;
axiom [c_pos]: int.gt(c, 0);

procedure Witness()
spec {
  ensures int.gt(c, 0);
}
{
};
#end

private def axiomAST : Core.Program := cstToAST axiomPgm
private abbrev witnessProc : Core.Procedure :=
  (axiomAST.findProcByString? "Witness").get!

/-- `Witness` has one `ensures` clause, not marked `free`, so its contract is not
    empty. -/
private theorem witness_ensures :
    (witnessProc.spec.postconditions.toList.map fun lc =>
      decide (lc.2.attr = Core.Procedure.CheckAttr.Default)) = [true] := by
  native_decide

/-- Every non-`free` `ensures` of `Witness` is the expression of an axiom declared
    before it. -/
private theorem ensures_among_axioms :
    (witnessProc.spec.postconditions.toList.all fun lc =>
      (axiomAST.declsBeforeProcedure "Witness").any fun d =>
        match d with
        | .ax a _ => decide (a.e = lc.2.expr)
        | _ => false) = true := by
  native_decide

/-- **`Witness` meets its contract.** The body is empty, so the postcondition `c > 0`
    is read in the entry environment, where the axiom `c_pos` says it evaluates to
    `true`. Without the axiom assumption of `contractTriple` the contract would not
    hold: a model may interpret `c` as `0`. -/
theorem witness_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple axiomAST testParams "Witness" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed_axioms axiomAST testParams
    "Witness" witnessProc [] (by native_decide) (by native_decide) (by native_decide) ?_
  refine Core.Logic.Hoare.consequence _ _
    (Core.Logic.Hoare.skip axiomAST.findProcByString? testParams "" #[] _)
    (fun _ h => h) (fun ρ ⟨hpre, haxioms⟩ => ?_)
  intro label check hmem _ _
  have hall := ensures_among_axioms
  simp only [List.all_eq_true, List.any_eq_true] at hall
  obtain ⟨d, hd, hexpr⟩ := hall (label, check) hmem
  cases d <;> simp only [decide_eq_true_eq, Bool.false_eq_true] at hexpr
  rename_i a md
  exact .inl ⟨hpre.2.1, hexpr ▸ haxioms.eval_of_mem hd⟩

/-- **The contract of procedure correctness for `Witness`.** From every entry
    environment that satisfies the axiom, every finished run of the body, followed by
    the postcondition as an assertion, is assertion-valid. -/
theorem witness_contract (ss : Core.Statements)
    (hbody : witnessProc.body = .structured ss)
    (ρ₀ ρ' : Imperative.Env Core.Expression) (trace : Imperative.Trace Core.Expression)
    (hentry : Core.Specification.ProcEntryEnv testParams "Witness" axiomAST witnessProc ρ₀)
    (hrun : (Core.Logic.EventLang.coreBlock axiomAST.findProcByString?).TerminatesAt
      [Imperative.Stmt.block "" ss #[]] ρ₀ trace ρ') :
    Imperative.Trace.AssertionsValid Core.Expression
      (Core.Logic.DenoteBasedInterp (axiomAST.factoryBeforeProcedure "Witness"))
      (trace ++ Core.Specification.postconditionEvents witnessProc ρ') :=
  Core.Specification.contract_of_contractTriple witness_meets_contract witnessProc ss
    (by native_decide) hbody ρ₀ ρ' trace hentry hrun

end Strata.HoareAxiomsTest

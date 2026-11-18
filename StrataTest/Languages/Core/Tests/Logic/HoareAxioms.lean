/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Strata.Languages.Core.Analysis.ProcedureCorrectnessHoareConnection
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # Hoare contracts that rest on an axiom or a `distinct` declaration

`Procedure.contractTriple` assumes, at the procedure's entry, the axioms and `distinct`
declarations placed before the procedure, and no other.

## An axiom a contract rests on

A constant `c` with no definition, whose value differs from model to model, an axiom
`c > 0`, and a procedure `Witness` with an empty body that ensures `c > 0`.

- `witness_meets_contract`: `Witness` satisfies its contract, by the axiom.
- `witness_contract`: the same fact in the form of the `contract` field of
  `Core.Specification.ProcedureAssertsValidOnTraces.denote`, from
  `Core.Specification.contract_of_contractTriple`.

## The position of a declaration decides

A procedure with an empty body that ensures `false` meets its contract only if its
entry assumption is contradictory. The same contradictory declaration is placed once
before the procedure and once after it.

- `early_meets_contract`, `late_violates_contract`: the axiom `false`.
- `clash_meets_contract`, `lateClash_violates_contract`: the declaration
  `distinct [a, a]` of a constant `a`.

## A `distinct` declaration at the entry

- `apart_entry`: with `distinct [a, b]` before the procedure, the constants `a` and
  `b` have different values at every entry the contract triple admits.
-/

open StrataDDM (Program)

namespace Strata.HoareAxiomsTest

open Strata.HoareUtils

/-! ## An axiom a contract rests on -/

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
private abbrev witnessProc : Core.Procedure := procOf axiomAST "Witness"

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

/-! ## The position of a declaration decides -/

/-- A procedure with an empty body meets its contract when the declarations before it
    cannot all hold. -/
private theorem contractTriple_of_entry_absurd (p : Core.Program) (n : String)
    (hproc : p.findProcByString? n = some (procOf p n))
    (hbody : (procOf p n).body = .structured [])
    (htyped : Core.Logic.Hoare.Procedure.contractChecksTyped (procOf p n))
    (habsurd : ∀ ρ, ¬ Core.Specification.AxiomsBeforeProcedureDecl n p ρ) :
    Core.Logic.Hoare.Procedure.contractTriple p testParams n := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed_axioms p testParams n
    (procOf p n) [] hproc hbody htyped ?_
  exact Core.Logic.Hoare.consequence _ _
    (Core.Logic.Hoare.skip p.findProcByString? testParams "" #[] (fun _ => False))
    (fun ρ h => habsurd ρ h.2) (fun _ h => h.elim)

/-- A procedure with no parameter, no `requires`, an empty body and a non-`free`
    `ensures false` does not meet its contract when no axiom or `distinct` declaration
    precedes it: the run from the empty store ends where it starts, and `false` does
    not hold there. -/
private theorem not_contractTriple_ensures_false (p : Core.Program) (n : String)
    (hfactory : p.factoryBeforeProcedure n = Core.Factory)
    (hproc : p.findProcByString? n = some (procOf p n))
    (hbody : (procOf p n).body = .structured [])
    (hpre : (procOf p n).spec.preconditions.toList = [])
    (hinout : ListMap.keys (procOf p n).header.getInoutParams = [])
    (hinputs : (procOf p n).header.inputs.toList = [])
    (hpost : ∃ lc ∈ (procOf p n).spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default ∧
      (Prod.snd lc).expr = Lambda.LExpr.boolConst Core.valueLoc false)
    (haxioms : ∀ ρ, Core.Specification.AxiomsBeforeProcedureDecl n p ρ) :
    ¬ Core.Logic.Hoare.Procedure.contractTriple p testParams n := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory] at h
  obtain ⟨proc, hproc', _htyped, htb⟩ := h
  obtain rfl : proc = procOf p n := Option.some.inj (hproc'.symm.trans hproc)
  rw [hbody] at htb
  let ρ : Imperative.Env Core.Expression :=
    { store := fun _ => none, factory := boolFactory model }
  have ⟨_hvalid, hpostF⟩ := htb ρ ρ []
    ⟨⟨preAsPredicate_of_no_pre _ _ ρ hpre, rfl,
      oldInoutAsPredicate_of_no_inout _ ρ hinout,
      fun id ty hmem => by rw [hinputs] at hmem; cases hmem⟩, haxioms ρ⟩
    (blockWF_nil ρ rfl (fun _ _ hn => by cases hn))
    (.inl (run_procBlock_nil _ ρ "" #[]))
  obtain ⟨⟨label, check⟩, hmem, hattr, hexpr⟩ := hpost
  rcases hpostF (reachable_nil _) label check hmem hattr (someValuation _) with
    ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (Imperative.HasBool.ttVal ρ.factory) at hex
    rw [hexpr, Core.eval_boolConst] at hex
    exact Imperative.HasBool.ttVal_ne_ffVal _ (Option.some.inj hex).symm
  · exact hne rfl

/-- The integer constant named `x`, as the translation writes it. -/
private abbrev constOp (x : String) : Core.Expression.Expr :=
  .op Core.valueLoc ⟨x, ()⟩ (some intMono)

/-- The axiom `false` holds in no environment. -/
private theorem absurd_of_axiom_false {p : Core.Program} {n : String}
    (hax : ((p.declsBeforeProcedure n).any fun d =>
      match d with
      | .ax a _ => decide (a.e = Lambda.LExpr.boolConst Core.valueLoc false)
      | _ => false) = true)
    (ρ : Imperative.Env Core.Expression) :
    ¬ Core.Specification.AxiomsBeforeProcedureDecl n p ρ := by
  intro h
  obtain ⟨d, hd, he⟩ := List.any_eq_true.mp hax
  cases d <;> simp only [decide_eq_true_eq, Bool.false_eq_true] at he
  have hev := h.eval_of_mem hd
  rw [he, Core.eval_boolConst] at hev
  exact Imperative.HasBool.ttVal_ne_ffVal _ (Option.some.inj hev).symm

/-- The declaration `distinct [a, a]` holds in no environment. -/
private theorem absurd_of_distinct_same {p : Core.Program} {n : String}
    (hd : ((p.declsBeforeProcedure n).any fun d =>
      match d with
      | .distinct _ es _ => decide (es = [constOp "a", constOp "a"])
      | _ => false) = true)
    (ρ : Imperative.Env Core.Expression) :
    ¬ Core.Specification.AxiomsBeforeProcedureDecl n p ρ := by
  intro h
  obtain ⟨d, hmem, he⟩ := List.any_eq_true.mp hd
  cases d <;> simp only [decide_eq_true_eq, Bool.false_eq_true] at he
  have hpw := h.pairwise_of_mem hmem
  rw [he] at hpw
  exact (List.pairwise_cons.mp hpw).1 _ List.mem_cons_self rfl

/-! ### The axiom `false` -/

private def earlyPgm : Program :=
#strata
program Core;

axiom [contra]: false;

procedure Early()
spec {
  ensures false;
}
{
};
#end

private def earlyAST : Core.Program := cstToAST earlyPgm

/-- **`Early` meets its contract**, because the axiom before it is assumed at its
    entry and cannot hold. -/
theorem early_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple earlyAST testParams "Early" :=
  contractTriple_of_entry_absurd earlyAST "Early" (by native_decide) (by native_decide)
    (by native_decide) (absurd_of_axiom_false (by native_decide))

private def latePgm : Program :=
#strata
program Core;

procedure Late()
spec {
  ensures false;
}
{
};

axiom [contra]: false;
#end

private def lateAST : Core.Program := cstToAST latePgm

/-- The axiom of `latePgm` is in the program, and is not among the declarations
    before `Late`. -/
private theorem late_axiom_after :
    (lateAST.decls.any fun d =>
      match d with
      | .ax a _ => decide (a.e = Lambda.LExpr.boolConst Core.valueLoc false)
      | _ => false) = true ∧
    ((lateAST.declsBeforeProcedure "Late").all fun d =>
      match d with
      | .ax _ _ | .distinct _ _ _ => false
      | _ => true) = true := by
  native_decide

/-- **`Late` does not meet its contract.** The axiom `false` comes after the
    procedure, so it is not assumed at the entry, and the postcondition `false` fails
    on a run of the empty body. -/
theorem late_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple lateAST testParams "Late" :=
  not_contractTriple_ensures_false lateAST "Late"
    (Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms late_axiom_after.2)

/-! ### The declaration `distinct [a, a]` -/

private def clashPgm : Program :=
#strata
program Core;

const a : int;
distinct [same]: [a, a];

procedure Clash()
spec {
  ensures false;
}
{
};
#end

private def clashAST : Core.Program := cstToAST clashPgm

/-- **`Clash` meets its contract**, because the `distinct` declaration before it is
    assumed at its entry and cannot hold. -/
theorem clash_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple clashAST testParams "Clash" :=
  contractTriple_of_entry_absurd clashAST "Clash" (by native_decide) (by native_decide)
    (by native_decide) (absurd_of_distinct_same (by native_decide))

private def lateClashPgm : Program :=
#strata
program Core;

procedure LateClash()
spec {
  ensures false;
}
{
};

const a : int;
distinct [same]: [a, a];
#end

private def lateClashAST : Core.Program := cstToAST lateClashPgm

/-- The `distinct` declaration of `lateClashPgm` is in the program, and is not among
    the declarations before `LateClash`; neither is its constant. -/
private theorem lateClash_distinct_after :
    (lateClashAST.decls.any fun d =>
      match d with
      | .distinct _ es _ => decide (es = [constOp "a", constOp "a"])
      | _ => false) = true ∧
    ((lateClashAST.declsBeforeProcedure "LateClash").all fun d =>
      match d with
      | .ax _ _ | .distinct _ _ _ => false
      | _ => true) = true := by
  native_decide

/-- **`LateClash` does not meet its contract.** The `distinct` declaration comes
    after the procedure, so it is not assumed at the entry. -/
theorem lateClash_violates_contract :
    ¬ Core.Logic.Hoare.Procedure.contractTriple lateClashAST testParams "LateClash" :=
  not_contractTriple_ensures_false lateClashAST "LateClash"
    (Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
    (Core.Specification.axiomsBeforeProcedureDecl_of_noAxioms lateClash_distinct_after.2)

/-! ## A `distinct` declaration at the entry -/

private def apartPgm : Program :=
#strata
program Core;

const a : int;
const b : int;
distinct [ab]: [a, b];

procedure Apart()
spec {
  ensures a != b;
}
{
};
#end

private def apartAST : Core.Program := cstToAST apartPgm

/-- `distinct [a, b]` is among the declarations before `Apart`. -/
private theorem apart_distinct_before :
    ((apartAST.declsBeforeProcedure "Apart").any fun d =>
      match d with
      | .distinct _ es _ => decide (es = [constOp "a", constOp "b"])
      | _ => false) = true := by
  native_decide

/-- **The constants `a` and `b` differ at the entry of `Apart`.** Every environment
    that satisfies the entry assumption of the contract triple of `Apart` gives the
    two constants different values. -/
theorem apart_entry (ρ : Imperative.Env Core.Expression)
    (h : Core.Specification.AxiomsBeforeProcedureDecl "Apart" apartAST ρ) :
    Core.Expression.eval ρ.factory ρ.store (constOp "a") ≠
      Core.Expression.eval ρ.factory ρ.store (constOp "b") := by
  obtain ⟨d, hmem, he⟩ := List.any_eq_true.mp apart_distinct_before
  cases d <;> simp only [decide_eq_true_eq, Bool.false_eq_true] at he
  have hpw := h.pairwise_of_mem hmem
  rw [he] at hpw
  exact (List.pairwise_cons.mp hpw).1 _ List.mem_cons_self

end Strata.HoareAxiomsTest

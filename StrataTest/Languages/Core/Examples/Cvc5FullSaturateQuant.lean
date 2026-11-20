/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

/-! ## cvc5's enumerative quantifier instantiation (`--full-saturate-quant`)

The axiom's only trigger is `p(x + 1)`, which E-matching cannot match against `p(7)`: cvc5 by
default answers `unknown` with reason `incomplete`. Enumerative instantiation (`x := 6`) proves
the assertion. -/

def fullSaturateQuantPgm :=
#strata
program Core;

function p (x : int) : bool;
axiom [p_step]: forall x : int :: { p(int.add(x, 1)) } int.gt(x, 5) ==> p(int.add(x, 1));

procedure Check()
{
  assert [p7]: p(7);
};
#end

/-! By default the assertion is unknown. -/

/--
info:
Obligation: p7
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm (options := Core.VerifyOptions.quiet)

/-! `cvc5FullSaturateQuant` proves it, on the per-obligation and on the incremental backend. -/

/--
info:
Obligation: p7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5FullSaturateQuant := true })

/--
info:
Obligation: p7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5FullSaturateQuant := true,
                                                     incremental := true })

/-! `cvc5RetryFullSaturateQuant` reruns the `unknown (incomplete)` query with the fallback and
takes its proof, with or without its own time limit. -/

/--
info:
Obligation: p7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true })

/--
info:
Obligation: p7
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true,
                                                     cvc5RetryTimeout := 2 })

/-! Under `incremental` there is no retry, so the option has no effect: the assertion stays
`unknown`. -/

/--
info:
Obligation: p7
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true,
                                                     incremental := true })

/-! The same holds when `alwaysGenerateSMT` sends the queries of an `incremental` run through
files: the run's verdict does not depend on whether its SMT files are kept. -/

/--
info:
Obligation: p7
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true,
                                                     incremental := true,
                                                     alwaysGenerateSMT := true })

/-! With `checkLevel := .full` the query file holds the satisfiability check, then the validity
check. The probe asks for the reason of the last check, the validity check's `unknown`
(`incomplete`), so the retry runs. The retry drops the satisfiability check, which cvc5 cannot
close under `--full-saturate-quant` (`p(7)` with the axiom is satisfiable), and proves the
validity check. The satisfiability check keeps its first `unknown`, so the verdict is "always
true if reached": validity is proved and reachability is unknown. That is the full-mode verdict
for a proved assertion whose reachability cvc5 does not settle, not a weaker result. -/

/--
info:
Obligation: p7
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .full })

/--
info:
Obligation: p7
Property: assert
Result: ✔️ always true if reached
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantPgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true,
                                                     checkLevel := .full })

/-! A constant named `Validity` puts a `; Validity` comment line among the declarations. The
retry still drops the satisfiability check and proves the validity check. -/

def fullSaturateQuantMarkerNamePgm :=
#strata
program Core;

function p (x : int) : bool;
const Validity : int;
axiom [p_step]: forall x : int :: { p(int.add(x, 1)) } int.gt(x, 5) ==> p(int.add(x, 1));
axiom [v7]: Validity == 7;

procedure Check()
{
  assert [p7]: p(Validity);
};
#end

/--
info:
Obligation: p7
Property: assert
Result: ✔️ always true if reached
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantMarkerNamePgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true,
                                                     checkLevel := .full })

/-! The retry never refutes: a false assertion that cvc5 leaves `unknown` stays `unknown`,
since only an `unsat` retry is taken. -/

def fullSaturateQuantFalsePgm :=
#strata
program Core;

function q (x : int) : bool;
axiom [q_step]: forall x : int :: { q(int.add(x, 1)) } int.gt(x, 5) ==> q(int.add(x, 1));

procedure Check()
{
  assert [q5]: q(5);
};
#end

/--
info:
Obligation: q5
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify fullSaturateQuantFalsePgm
        (options := { Core.VerifyOptions.quiet with cvc5RetryFullSaturateQuant := true })

/-! ## The solver flags -/

#guard !(_root_.Core.SMT.getSolverFlags Core.VerifyOptions.default).contains "--full-saturate-quant"
#guard (_root_.Core.SMT.getSolverFlags { Core.VerifyOptions.default with cvc5FullSaturateQuant := true }).contains
  "--full-saturate-quant"
#guard !(_root_.Core.SMT.getSolverFlags
  { Core.VerifyOptions.default with solver := "z3", cvc5FullSaturateQuant := true }).contains
  "--full-saturate-quant"
#guard (_root_.Core.SMT.incrementalLaunch { Core.VerifyOptions.default with cvc5FullSaturateQuant := true }).flags.contains
  "--full-saturate-quant"
#guard _root_.Core.SMT.cvc5RetryFlags Core.VerifyOptions.default == #[]
#guard _root_.Core.SMT.cvc5RetryFlags { Core.VerifyOptions.default with cvc5RetryFullSaturateQuant := true } ==
  #["--full-saturate-quant"]
#guard _root_.Core.SMT.cvc5RetryFlags
  { Core.VerifyOptions.default with cvc5RetryFullSaturateQuant := true, cvc5RetryTimeout := 2 } ==
  #["--full-saturate-quant", "--tlimit=2000"]
#guard _root_.Core.SMT.cvc5RetryFlags
  { Core.VerifyOptions.default with solver := "z3", cvc5RetryFullSaturateQuant := true } == #[]
#guard _root_.Core.SMT.cvc5RetryFlags
  { Core.VerifyOptions.default with cvc5RetryFullSaturateQuant := true, incremental := true } == #[]
-- With no query limit (`solverTimeout := 0`) the retry still gets a finite one.
#guard _root_.Core.SMT.cvc5RetryFlags
  { Core.VerifyOptions.default with cvc5RetryFullSaturateQuant := true, solverTimeout := 0 } ==
  #["--full-saturate-quant", s!"--tlimit={Core.VerifyOptions.default.solverTimeout * 1000}"]
#guard _root_.Core.SMT.cvc5RetryFlags
  { Core.VerifyOptions.default with cvc5RetryFullSaturateQuant := true, solverTimeout := 0,
                                    cvc5RetryTimeout := 3 } ==
  #["--full-saturate-quant", "--tlimit=3000"]

/-! ## The retry takes only `unsat`

`Imperative.SMT.retryVerdict first retried`: an `unsat` retry is a proof; a retried `sat` or
`unknown` keeps the first `unknown`, with its candidate model, so the retry never adds a
refutation. -/

private abbrev R := Imperative.SMT.Result String

#guard (Imperative.SMT.retryVerdict (.unknown none : R) .unsat) == .unsat
#guard (Imperative.SMT.retryVerdict (.unknown none : R) (.sat [])) == .unknown none
#guard (Imperative.SMT.retryVerdict (.unknown (some []) : R) (.sat [])) == .unknown (some [])
#guard (Imperative.SMT.retryVerdict (.unknown none : R) (.unknown none)) == .unknown none

#guard Imperative.SMT.reasonUnknownIsIncomplete "unknown\n(:reason-unknown incomplete)\n"

/-! A retry that fails (here, one whose query file is missing) leaves the first verdict. -/

/-- info: ❓ unknown, kept -/
#guard_msgs in
#eval show IO Unit from do
  let r ← Imperative.SMT.orFirst (some (.unknown none : R))
    (do let _ ← IO.FS.readFile "/nonexistent/cvc5-retry-test.smt2"; pure (some .unsat))
  IO.println (if r == some (.unknown none) then "❓ unknown, kept" else "changed")
#guard !Imperative.SMT.reasonUnknownIsIncomplete "unknown\n(:reason-unknown timeout)\n"
#guard !Imperative.SMT.reasonUnknownIsIncomplete "unknown\n(:reason-unknown resourceout)\n"
-- The text inside a model value is not the response.
#guard !Imperative.SMT.reasonUnknownIsIncomplete
  "unknown\n((s \"(:reason-unknown incomplete)\"))\n(:reason-unknown timeout)\n"

/-! ## The retried file keeps only the validity check -/

#guard Imperative.SMT.validityCheckOnly
    "(declare-fun x () Int)\n; Satisfiability\n(check-sat-assuming (g))\n(get-value (x))\n; Validity\n(check-sat-assuming ((not g)))\n(get-value (x))\n" ==
  some "(declare-fun x () Int)\n; Validity\n(check-sat-assuming ((not g)))\n(get-value (x))\n"
#guard Imperative.SMT.validityCheckOnly
    "(declare-fun x () Int)\n; Validity\n(assert (not g))\n(check-sat)\n" == none
-- The markers in the wrong order: the cut gives up.
#guard Imperative.SMT.validityCheckOnly
    "(declare-fun x () Int)\n; Validity\n(check-sat-assuming ((not g)))\n; Satisfiability\n(check-sat-assuming (g))\n" == none
-- A marker line before the check block (a declaration's comment, or a quoted symbol
-- spanning lines) does not move the cut.
#guard Imperative.SMT.validityCheckOnly
    "(set-logic ALL)\n; Validity\n(declare-fun Validity () Int)\n; Satisfiability\n(check-sat-assuming (g))\n; Validity\n(check-sat-assuming ((not g)))\n" ==
  some "(set-logic ALL)\n; Validity\n(declare-fun Validity () Int)\n; Validity\n(check-sat-assuming ((not g)))\n"
#guard Imperative.SMT.validityCheckOnly
    "(set-logic ALL)\n; Satisfiability\n(declare-fun Satisfiability () Int)\n; Satisfiability\n(check-sat-assuming (g))\n; Validity\n(check-sat-assuming ((not g)))\n" ==
  some "(set-logic ALL)\n; Satisfiability\n(declare-fun Satisfiability () Int)\n; Validity\n(check-sat-assuming ((not g)))\n"
#guard Imperative.SMT.validityCheckOnly
    "(declare-fun |a\n; Validity\nb| () Int)\n; Satisfiability\n(check-sat-assuming (g))\n; Validity\n(check-sat-assuming ((not g)))\n" ==
  some "(declare-fun |a\n; Validity\nb| () Int)\n; Validity\n(check-sat-assuming ((not g)))\n"
#guard Imperative.SMT.validityCheckOnly
    "(declare-fun |a\n; Satisfiability\nb| () Int)\n; Satisfiability\n(check-sat-assuming (g))\n; Validity\n(check-sat-assuming ((not g)))\n" ==
  some "(declare-fun |a\n; Satisfiability\nb| () Int)\n; Validity\n(check-sat-assuming ((not g)))\n"
-- A second marker line inside the check block: the cut gives up.
#guard Imperative.SMT.validityCheckOnly
    "(set-logic ALL)\n; Satisfiability\n(check-sat-assuming (g))\n(get-value (|a\n; Validity\nb|))\n; Validity\n(check-sat-assuming ((not g)))\n" == none
-- The marker text inside a symbol on one line is not a marker line.
#guard Imperative.SMT.validityCheckOnly
    "(declare-fun |; Validity| () Int)\n; Satisfiability\n(check-sat-assuming (g))\n; Validity\n(check-sat-assuming ((not g)))\n" ==
  some "(declare-fun |; Validity| () Int)\n; Validity\n(check-sat-assuming ((not g)))\n"

end Strata
end
---------------------------------------------------------------------

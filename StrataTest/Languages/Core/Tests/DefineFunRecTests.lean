/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# `recursiveFnsAsDefineFunRec`: recursive functions as `define-fun-rec`

By default a recursive function is encoded as an uninterpreted function with
per-constructor axioms (see `Core.generateRecursiveAxioms`).  That is the right
encoding for proving, but the solver cannot *evaluate* such a function while
searching for a model, so a false obligation whose counterexample must be
computed through the function comes back `unknown`.

With `recursiveFnsAsDefineFunRec` the definition is emitted as `define-fun-rec`
and, with cvc5's `fmf-fun` option, the solver synthesises the constructor term
directly.

The program is the binary-nat library: `pos` (`xH = 1`, `xO(h) = 2h`,
`xI(h) = 2h + 1`), `nat` (`N0`, `Npos(p)`), the recursive `pos.toInt` /
`pos.fromInt` bridge, and the operators defined over `toInt` images.  The
obligation asks for `a` with `toInt(a) = 73` and `toInt(a + b) = 200` such that
`toInt(b) = 0`; the only counterexample is `b = 127`.
-/

namespace Strata.DefineFunRecTest

open StrataDDM (Program)

def natSumPgm : Program :=
#strata
program Core;

datatype pos () {
  xH(),
  xO(xO_h: pos),
  xI(xI_h: pos)
};
datatype nat () {
  N0(),
  Npos(val: pos)
};

rec
function pos.toInt (@[cases] p : pos) : int {
  if pos..isxH(p) then 1
  else if pos..isxO(p) then int.mul(2, pos.toInt(pos..xO_h(p)))
  else int.add(int.mul(2, pos.toInt(pos..xI_h(p))), 1)
}
;

rec
function pos.fromInt (x : int) : pos
decreases x
{
  if int.le(x, 1) then xH()
  else if int.mod(x, 2) == 0 then xO(pos.fromInt(int.div(x, 2)))
  else xI(pos.fromInt(int.div(x, 2)))
}
;

function nat.toInt (n : nat) : int {
  if nat..isN0(n) then 0 else pos.toInt(nat..val(n))
}
function nat.fromInt (x : int) : nat {
  if int.le(x, 0) then N0() else Npos(pos.fromInt(x))
}
function nat.add (a : nat, b : nat) : nat {
  nat.fromInt(int.add(nat.toInt(a), nat.toInt(b)))
}

procedure test_sum_counterexample (a : nat, b : nat) spec {
  requires nat.toInt(a) == 73;
  requires nat.toInt(nat.add(a, b)) == 200;
  ensures nat.toInt(b) == 0;
}
{
  assert [b_is_zero]: nat.toInt(b) == 0;
};

#end

---------------------------------------------------------------------
-- Default encoding: the false obligation is reported as `unknown` — sound,
-- but not a counterexample: the candidate model shown (`a = 2`, `b = 3`)
-- violates the `requires`.
---------------------------------------------------------------------

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: b_is_zero
Property: assert
Result: ❓ unknown

Obligation: test_sum_counterexample_ensures_2
Property: assert
Result: ❓ unknown-/
#guard_msgs in
#eval Core.verify natSumPgm (options := Core.VerifyOptions.quiet)

---------------------------------------------------------------------
-- `define-fun-rec` alone is not enough, and is deliberately not pinned here.
--
-- Measured with cvc5 1.3.4: the ten provable obligations still pass with the
-- definition in place of the per-constructor axioms, so proving is unaffected.
-- The two false obligations come back as a solver timeout rather than a
-- counterexample, because model search over a recursive definition needs
-- `fmf-fun`. A timeout is a property of the budget and the machine, not of the
-- encoding, so pinning one would make this suite fail for reasons unrelated to
-- the feature. The next block pins the outcome that does characterise it.
---------------------------------------------------------------------

---------------------------------------------------------------------
-- `define-fun-rec` + `fmf-fun`: the obligation goes from `unknown` to a
-- certified `fail`, with the model `a = 73`, `b = 127`.
--
-- Only the verdicts are pinned, not the model. `a` and `b` are forced by the
-- preconditions (`toInt a = 73` and `toInt (a + b) = 200`), but the model also
-- assigns the unconstrained variables of the query, and nothing obliges a
-- solver to pick the same values for those twice. The verdict is what the
-- feature promises; the values are in this comment instead.
--
-- `fmf-fun` is a model-finding mode and weakens proving — here the two `pos.toInt_terminates` goals come back `unknown`
-- — so a client should enable it only when re-querying an obligation that
-- was `unknown`, not on the primary pass.
---------------------------------------------------------------------

/-- info:
Obligation: pos.toInt_body_calls_pos..xO_h_0
Property: assert
Result: ✅ pass

Obligation: pos.toInt_body_calls_pos..xI_h_1
Property: assert
Result: ✅ pass

Obligation: pos.toInt_terminates_0
Property: assert
Result: ❓ unknown

Obligation: pos.toInt_terminates_1
Property: assert
Result: ❓ unknown

Obligation: pos.fromInt_terminates_0
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_1
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_2
Property: assert
Result: ✅ pass

Obligation: pos.fromInt_terminates_3
Property: assert
Result: ✅ pass

Obligation: nat.toInt_body_calls_nat..val_0
Property: assert
Result: ✅ pass

Obligation: b_is_zero
Property: assert
Result: ❌ fail

Obligation: test_sum_counterexample_ensures_2
Property: assert
Result: ❌ fail-/
#guard_msgs in
#eval Core.verify natSumPgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  solverOptions := #[("fmf-fun", "true")],
                  -- well within budget standalone; generous so the pin is
                  -- stable when the suite runs solver processes in parallel
                  solverTimeout := 60 })

---------------------------------------------------------------------
-- `obligationsToVerify`: re-query just the obligation that was `unknown`.
-- This is the intended client pattern: primary pass with the default
-- encoding, then only the unknown obligations again with `define-fun-rec`
-- + `fmf-fun`, so the weaker proving mode never touches the others.
---------------------------------------------------------------------

/-- info:
Obligation: b_is_zero
Property: assert
Result: ❌ fail-/
#guard_msgs in
#eval Core.verify natSumPgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  solverOptions := #[("fmf-fun", "true")],
                  solverTimeout := 60,
                  obligationsToVerify := some ["b_is_zero"] })

end Strata.DefineFunRecTest

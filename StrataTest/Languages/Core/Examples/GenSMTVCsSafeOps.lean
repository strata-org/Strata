/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)

/-!
## `gen_smt_vcs`: a safe operator equals its plain operator outside its precondition

Each axiom names the value of a safe operator applied outside its precondition, and each
assertion states that it is the value of the plain operator at the same arguments. The encoder
gives the safe and the plain operator the same SMT term, so `gen_smt_vcs` gives both the same
denotation, and each goal follows from the axiom it restates. No goal states a value at a zero
divisor, so the proof does not depend on how the denotation treats one. The calls are in axioms,
which carry no well-formedness check, so the program has no obligation that the call is outside
the precondition.

The cases are closed by name, so a dropped or an unexpected obligation fails the proof.
-/

namespace Strata

private def safeEqPlainPgm : Program :=
#strata
program Core;

const x : bv W8;
const a : int;
const ksdiv : bv W8;
const ksmod : bv W8;
const kadd : bv W8;
const kneg : bv W8;
const kdiv : int;
const kmod : int;
const kdivT : int;
const kmodT : int;
axiom [sdiv]: ksdiv == bv8.safeSDiv(x, bv{8}(0));
axiom [smod]: ksmod == bv8.safeSMod(bv{8}(128), bv{8}(255));
axiom [add]: kadd == bv8.safeAdd(bv{8}(127), x);
axiom [neg]: kneg == bv8.safeNeg(bv{8}(128));
axiom [div]: kdiv == int.safeDiv(a, 0);
axiom [mod]: kmod == int.safeMod(a, 0);
axiom [divT]: kdivT == int.safeDivT(a, 0);
axiom [modT]: kmodT == int.safeModT(a, 0);

procedure P()
{
  assert [sdivPlain]: ksdiv == bv8.sDiv(x, bv{8}(0));
  assert [smodPlain]: ksmod == bv8.sMod(bv{8}(128), bv{8}(255));
  assert [addPlain]: kadd == bv8.add(bv{8}(127), x);
  assert [negPlain]: kneg == bv8.neg(bv{8}(128));
  assert [divPlain]: kdiv == int.div(a, 0);
  assert [modPlain]: kmod == int.mod(a, 0);
  assert [divTPlain]: kdivT == int.divT(a, 0);
  assert [modTPlain]: kmodT == int.modT(a, 0);
};
#end

theorem safeEqPlain : smtVCsCorrect safeEqPlainPgm := by
  gen_smt_vcs
  case sdivPlain => intros; assumption
  case smodPlain => intros; assumption
  case addPlain => intros; assumption
  case negPlain => intros; assumption
  case divPlain => intros; assumption
  case modPlain => intros; assumption
  case divTPlain => intros; assumption
  case modTPlain => intros; assumption

end Strata

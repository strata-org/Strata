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
-- `recursiveFnsAsDefineFunRec`: the recursive functions are emitted as
-- `define-fun-rec`.
---------------------------------------------------------------------

/-- The functions emitted as `define-fun-rec`, in order, in the query written
    for obligation `label` of `pgm`, by the source name in the comment the
    encoder emits before each definition (the SMT name is uniquified). -/
private def defineFunRecNames (pgm : Program) (options : Core.VerifyOptions)
    (label : String) : IO (List String) := do
  let vcDir : System.FilePath := "_test_vcs_define_fun_rec"
  if ← vcDir.pathExists then
    IO.FS.removeDirAll vcDir
  IO.FS.createDirAll vcDir
  let _ ← Core.verify pgm (options := { options with
    skipSolver := true, vcDirectory := vcDir,
    obligationsToVerify := some [label] })
  let mut names := []
  for e in ← vcDir.readDir do
    if e.fileName.endsWith ".smt2" then
      let mut prev := ""
      for line in (← IO.FS.readFile e.path).splitOn "\n" do
        if line.startsWith "(define-fun-rec " then
          names := names ++ [(prev.dropPrefix "; ").toString]
        prev := line
  IO.FS.removeDirAll vcDir
  return names

/-- info: [] -/
#guard_msgs in
#eval defineFunRecNames natSumPgm Core.VerifyOptions.quiet "b_is_zero"

/-- info: ["pos.toInt", "pos.fromInt"] -/
#guard_msgs in
#eval defineFunRecNames natSumPgm
  { Core.VerifyOptions.quiet with recursiveFnsAsDefineFunRec := true }
  "b_is_zero"

---------------------------------------------------------------------
-- With `define-fun-rec` in place of the axioms, the provable obligations still
-- pass. The false ones are not run (`obligationsToVerify`): finding their
-- counterexample needs cvc5's `fmf-fun`, and without it the solver times out.
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
Result: ✅ pass-/
#guard_msgs in
#eval Core.verify natSumPgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  obligationsToVerify := some [
                    "pos.toInt_body_calls_pos..xO_h_0",
                    "pos.toInt_body_calls_pos..xI_h_1",
                    "pos.toInt_terminates_0", "pos.toInt_terminates_1",
                    "pos.fromInt_terminates_0", "pos.fromInt_terminates_1",
                    "pos.fromInt_terminates_2", "pos.fromInt_terminates_3",
                    "nat.toInt_body_calls_nat..val_0"] })

---------------------------------------------------------------------
-- A recursive function may call another recursive function: the callee is
-- emitted first. `sumLens` calls `listLen`; procedure `P` reaches `listLen`
-- only through `sumLens`, procedure `Both` also directly. Each procedure is
-- verified on its own, so that one does not affect the other's encoding.
---------------------------------------------------------------------

def recCalleePgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
datatype LL { LNil(), LCons(lhd: IntList, ltl: LL) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else int.add(1, listLen(IntList..tl(xs)))
};

rec function sumLens (@[cases] xss : LL) : int
{
  if LL..isLNil(xss) then 0 else int.add(listLen(LL..lhd(xss)), sumLens(LL..ltl(xss)))
};

procedure P(xss : LL)
spec { requires xss == LCons(Nil(), LNil()); }
{
  assert [onlyOuter]: sumLens(xss) == 0;
};

procedure Both(xs : IntList, xss : LL)
spec { requires listLen(xs) == 0; requires xss == LCons(Nil(), LNil()); }
{
  assert [both]: sumLens(xss) == listLen(xs);
};
#end

/-- info: ["listLen", "sumLens"] -/
#guard_msgs in
#eval defineFunRecNames recCalleePgm
  { Core.VerifyOptions.quiet with
      recursiveFnsAsDefineFunRec := true, proceduresToVerify := some ["P"] }
  "onlyOuter"

/-- info:
Obligation: onlyOuter
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Core.verify recCalleePgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  proceduresToVerify := some ["P"] })

/-- info:
Obligation: both
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Core.verify recCalleePgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  proceduresToVerify := some ["Both"] })

---------------------------------------------------------------------
-- Mutual recursion would need `define-funs-rec`, which is not supported yet.
---------------------------------------------------------------------

def mutualRecPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

procedure Q(n : MyNat)
spec { requires n == Succ(Succ(Zero())); }
{
  assert [twoEven]: isEven(n);
};
#end

/-- info:
Obligation: twoEven
Property: assert
Result: 🚨 SMT Encoding Error! recursiveFnsAsDefineFunRec: 'isOdd' and 'isEven' are mutually recursive; define-funs-rec is not supported yet.-/
#guard_msgs in
#eval Core.verify mutualRecPgm
  (options := { Core.VerifyOptions.quiet with
                  recursiveFnsAsDefineFunRec := true,
                  proceduresToVerify := some ["Q"] })

end Strata.DefineFunRecTest

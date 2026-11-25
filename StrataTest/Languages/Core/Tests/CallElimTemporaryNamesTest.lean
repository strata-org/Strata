/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # A program variable named like a call elimination temporary keeps its value

Call elimination saves a call's arguments, the pre-call values of its outputs and the `old`
values of its `inout` parameters in temporaries named `$__callElimTmp_arg_N`,
`$__callElimTmp_<out>_N` and `$__callElimOld_<x>_N`. Each procedure below declares a variable
with the name the first such temporary would get. Type checking then records call elimination's
prefix, so call elimination takes its slow path (`Transform.withClaimedPrefixes`), and the
temporaries take other names, so the variable keeps its value across the call:
the `_ok` assertion is proved and the `_bad` assertion is not, under symbolic evaluation and under
`--vcgen symexec`. A `_bad` result rests on the callee's contract, so it is `unknown`, not
`failed`; a temporary that overwrote the variable would make it `proved`.
-/

meta section

namespace Core.CallElimTemporaryNamesTest

/-- `ArgClash` declares `$__callElimTmp_arg_0`, the name of the temporary for the argument `7`. -/
private def pgm :=
#strata
program Core;

procedure g(x : int, out y : int)
spec {
  ensures (y == int.add(x, 1));
}
{
  y := int.add(x, 1);
};

procedure ArgClash(n : int, out r : int)
{
  var $__callElimTmp_arg_0 : int := 5;
  call g(7, out r);
  assert [arg_ok]: ($__callElimTmp_arg_0 == 5);
  assert [arg_bad]: ($__callElimTmp_arg_0 == 7);
};
#end

/-- `OutClash` declares `$__callElimTmp_r_1`, the name of the temporary for the value of the
    output `r` before the call. -/
private def outPgm :=
#strata
program Core;

procedure g(x : int, out y : int)
spec {
  ensures (y == int.add(x, 1));
}
{
  y := int.add(x, 1);
};

procedure OutClash(n : int, out r : int)
{
  var $__callElimTmp_r_1 : int := 5;
  r := 3;
  call g(7, out r);
  assert [out_ok]: ($__callElimTmp_r_1 == 5);
  assert [out_bad]: ($__callElimTmp_r_1 == 3);
};
#end

/-- `OldClash` declares `$__callElimOld_x_2`, the name of the temporary for `old x` in `inc`'s
    postcondition. -/
private def oldPgm :=
#strata
program Core;

procedure inc(inout x : int)
spec {
  ensures (x == int.add(old x, 1));
}
{
  x := int.add(x, 1);
};

procedure OldClash(inout x : int)
{
  var $__callElimOld_x_2 : int := 5;
  call inc(inout x);
  assert [old_ok]: ($__callElimOld_x_2 == 5);
  assert [old_bad]: ($__callElimOld_x_2 == int.sub(x, 1));
};
#end

/-- An `out` argument named like the argument temporary: the postcondition of `g` stays
    `$__callElimTmp_arg_0 == 7 + 1` instead of becoming the false
    `$__callElimTmp_arg_0 == $__callElimTmp_arg_0 + 1`, which would make every later assertion
    pass. -/
private def outArgPgm :=
#strata
program Core;

procedure g(x : int, out y : int)
spec {
  ensures (y == int.add(x, 1));
}
{
  y := int.add(x, 1);
};

procedure OutArg()
{
  var $__callElimTmp_arg_0 : int := 0;
  call g(7, out $__callElimTmp_arg_0);
  assert [outarg_ok]: ($__callElimTmp_arg_0 == 8);
  assert [outarg_bad]: ($__callElimTmp_arg_0 == 100);
};
#end

/-- A nullary function named like the argument temporary keeps its axiom across the call. The
    temporary avoids declaration names as a precaution; symbolic evaluation already replaces the
    temporary by its value before encoding, so this case also holds without that precaution. -/
private def fnPgm :=
#strata
program Core;

function $__callElimTmp_arg_0(): int;
axiom [five]: ($__callElimTmp_arg_0 == 5);

procedure g(x : int, out y : int)
spec {
  ensures (y == int.add(x, 1));
}
{
  y := int.add(x, 1);
};

procedure FnClash(out r : int)
{
  call g(7, out r);
  assert [fn_ok]: ($__callElimTmp_arg_0 == 5);
  assert [fn_bad]: ($__callElimTmp_arg_0 == 7);
};
#end

/-- Symbolic evaluation, and `--vcgen symexec` per path. -/
private def modes : List (String × Core.VerifyOptions) :=
  [("symbolic", .quiet),
   ("symexec", { Core.VerifyOptions.quiet with symExec := some .never })]

/-- For each of `modes`, one line `mode: ` followed by `label verdict` for every obligation
    of `p`. -/
private def printVerdicts (p : StrataDDM.SourcedProgram) : IO Unit := do
  for (mode, opts) in modes do
    let rs ← Strata.Core.verify p (options := opts)
    let vs := rs.toList.map fun r =>
      let v := if r.isSuccess then "proved" else if r.isFailure then "failed" else "unknown"
      s!"{r.obligation.label} {v}"
    IO.println s!"{mode}: {", ".intercalate vs}"

/--
info: symbolic: g_ensures_0 proved, arg_ok proved, arg_bad unknown
symexec: g_ensures_0 proved, arg_ok proved, arg_bad unknown
-/
#guard_msgs in
#eval printVerdicts pgm

/--
info: symbolic: g_ensures_0 proved, out_ok proved, out_bad unknown
symexec: g_ensures_0 proved, out_ok proved, out_bad unknown
-/
#guard_msgs in
#eval printVerdicts outPgm

/--
info: symbolic: inc_ensures_0 proved, old_ok proved, old_bad unknown
symexec: inc_ensures_0 proved, old_ok proved, old_bad unknown
-/
#guard_msgs in
#eval printVerdicts oldPgm

/--
info: symbolic: g_ensures_0 proved, outarg_ok proved, outarg_bad unknown
symexec: g_ensures_0 proved, outarg_ok proved, outarg_bad unknown
-/
#guard_msgs in
#eval printVerdicts outArgPgm

/--
info: symbolic: g_ensures_0 proved, fn_ok proved, fn_bad unknown
symexec: g_ensures_0 proved, fn_ok proved, fn_bad unknown
-/
#guard_msgs in
#eval printVerdicts fnPgm

end Core.CallElimTemporaryNamesTest

end

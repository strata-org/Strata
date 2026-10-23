/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # `inline` stays on a function that reaches a lambda through a call

Expanding `h` is what erases the lambda it passes to `app`, so `h` keeps `inline`. `g`
builds no lambda itself but calls `h`, and nothing else expands that call: `simplify`
declines `g(int.add(a, b))`, whose parameter is used twice on a non-value argument, and
symbolic evaluation would see a weakened attribute. So `g` keeps `inline` too, and the
default pipeline verifies the program instead of failing to encode `h`. -/

meta section

namespace Strata.LambdaInlineTest

private def pgm :=
#strata
program Core;
inline function app (f : int -> int, v : int) : int { f(v) }
inline function h (v : int) : int { app(fun y : int => int.add(y, 1), v) }
inline function g (v : int) : int { int.add(h(v), h(v)) }
procedure R (a : int, b : int)
{
  assume int.ge(a, 0);
  assume int.ge(b, 0);
  assert [r]: int.ge(g(int.add(a, b)), 2);
};
#end

/--
info:
Obligation: r
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify pgm (options := Core.VerifyOptions.quiet)

/-! # `inline` stays on a function whose body needs literal arguments

`re.loop` takes its bounds as SMT indices, so `rep`'s body encodes only once a call is
expanded with a literal `n`. `rep(s, 2)` uses `s` twice on the non-value argument
`str.concat(a, b)`, so `simplify` declines the expansion; `rep` keeps `inline`, so
symbolic evaluation expands the call with `n = 2` and the program verifies instead of
failing to encode `re.loop`. -/

private def loopPgm :=
#strata
program Core;
inline function rep (s : string, n : int) : bool {
  str.in.re(s, re.loop(str.to.re(s), 1, n))
}
procedure Q (a : string, b : string)
{
  assert [q]: rep(str.concat(a, b), 2);
};
#end

/--
info:
Obligation: q
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify loopPgm (options := Core.VerifyOptions.quiet)

end Strata.LambdaInlineTest

end

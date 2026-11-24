/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier

/-! # The `VCs:` listing under `--vcgen wp`

With `verbose` at `debug`, `--vcgen wp` lists its obligations as symbolic evaluation
does, each with the definitions it reads: `a` reads the first definition of `y`, which both arms
of the branch read; the guard of the branch and the merged `y` are read once and inlined into
`a`, and `u` into `b`, which reads no definition. -/

namespace Strata.WPListingTest

/-- Two assertions that read disjoint definitions, one of them through a branch. -/
def listingPgm :=
#strata
program Core;
procedure P(x : int, out y : int)
{
  var u : int := int.add(x, 2);
  y := int.add(x, 1);
  if (int.gt(x, 0)) { y := int.add(y, 1); }
  assume [pos]: (int.gt(x, 0));
  assert [a]: (int.gt(y, 1));
  assert [b]: (int.gt(u, 1));
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a
Property: assert
Definitions:
y@3 := int.add(x@0, 1)
Assumptions:
pos: int.gt(x@0, 0)
Obligation:
int.gt(if int.gt(x@0, 0) then int.add(y@3, 1) else y@3, 1)

Label: b
Property: assert
Assumptions:
pos: int.gt(x@0, 0)
Obligation:
int.gt(int.add(x@0, 2), 1)

Wrote problem to _test_wplisting_vcs/a_0.smt2.
Wrote problem to _test_wplisting_vcs/b_1.smt2.
-/
#guard_msgs in
#eval do
  let vcDir : System.FilePath := "_test_wplisting_vcs"
  IO.FS.createDirAll vcDir
  let _ ← Core.verify listingPgm
    (options := { Core.VerifyOptions.default with
      vcgen := .wp, verbose := .debug, vcDirectory := vcDir })
  IO.FS.removeDirAll vcDir

end Strata.WPListingTest

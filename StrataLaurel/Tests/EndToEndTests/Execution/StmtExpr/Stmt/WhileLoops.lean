/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure countDown()
  entry
  opaque
{
    var i: int := 3;
    while(i > 0)
      invariant i >= 0
    {
        i := i - 1
    };
    assert i == 0
};

procedure countUp()
  entry
  opaque
{
    var n: int := 5;
    var i: int := 0;
    while(i < n)
      invariant i >= 0
      invariant i <= n
    {
        i := i + 1
    };
    assert i == n
};
#end

/-! ## Loop-invariant failures point at the specific invariant

These negative tests pin each failing loop invariant's diagnostic to that
invariant's own source range (per-invariant source ranges threaded through
loop elimination), rather than the whole loop. -/

-- No Core interpreter: it does not check loop invariants, so the annotated invariant failure never fires.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure badInitialInvariant()
  opaque
{
    var i: int := -1;
    while(i < 10)
      invariant i >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1
    }
};

procedure runAll()
  entry
  opaque
{
    badInitialInvariant()
};
#end

-- No Core interpreter: it does not check loop invariants, so the annotated invariant failure never fires.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure secondInvariantFails()
  opaque
{
    var i: int := 0;
    var j: int := -1;
    while(i < 10)
      invariant i >= 0
      invariant j >= 0
//              ^^^^^^ error: assertion does not hold
    {
        i := i + 1;
        j := j + 1
    }
};

procedure runAll()
  entry
  opaque
{
    secondInvariantFails()
};
#end

/-! ## An invariant is checked against the live state when the condition assigns

The loop head is reached after the condition's assignment has been lifted out, so
the invariant must be verified against the assigned value. Getting this wrong is
silent in the dangerous direction: substituting the pre-assignment snapshot into
the invariant made the false invariant below verify clean, dropping the proof
obligation entirely. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure invariantHoldsOnLiveValue()
  entry
  opaque
{
    var x: int := 1;
    while({ x := 5; x } < 0)
      invariant x == 5
    {
    };
    assert x == 5
};
#end

-- No Core interpreter: it does not check loop invariants, so the annotated invariant failure never fires.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure invariantFailsOnLiveValue()
  opaque
{
    var x: int := 1;
    while({ x := 5; x } < 0)
      invariant x == 1
//              ^^^^^^ error: assertion does not hold
    {
    }
};

procedure runAll()
  entry
  opaque
{
  invariantFailsOnLiveValue()
};
#end

/-! A divergent loop stops on the Laurel interpreter's step budget rather than
running on. -/

/-- error: out of fuel
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure spin()
  entry
  opaque
{
  var i: int := 0;
  while (true) {
    i := i + 1
  }
};
#end

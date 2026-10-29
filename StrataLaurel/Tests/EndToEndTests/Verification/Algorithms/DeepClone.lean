/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Algorithms.BenchmarkOptions

open StrataTest.Util
open StrataTest.Util.Algorithms
open Strata

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

composite Node {
  var value: int
  var hasLeft: bool
  var left: Node
  var hasRight: bool
  var right: Node
}

procedure deepClone(n: Node) returns (res: Node)
  opaque
  ensures res != n
  ensures res#value == n#value
  ensures res#hasLeft == n#hasLeft
  ensures res#hasRight == n#hasRight
  ensures res#hasLeft ==> res#left != n#left
  ensures res#hasRight ==> res#right != n#right
{
  var c: Node := new Node;
  c#value := n#value;
  c#hasLeft := n#hasLeft;
  c#hasRight := n#hasRight;
  if n#hasLeft then { var l: Node := deepClone(n#left); c#left := l };
  if n#hasRight then { var r: Node := deepClone(n#right); c#right := r };
  res := c
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Node {
  var value: int
  var hasLeft: bool
  var left: Node
  var hasRight: bool
  var right: Node
}

procedure deepClone(n: Node) returns (res: Node)
  opaque
  ensures res != n
  ensures res#value == n#value
  ensures res#hasLeft == n#hasLeft
  ensures res#hasRight == n#hasRight
  ensures res#hasLeft ==> res#left != n#left
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures res#hasRight ==> res#right != n#right
{
  var c: Node := new Node;
  c#value := n#value;
  c#hasLeft := n#hasLeft;
  c#hasRight := n#hasRight;
  if n#hasLeft then { c#left := n#left };
  if n#hasRight then { var r: Node := deepClone(n#right); c#right := r };
  res := c
};
#end

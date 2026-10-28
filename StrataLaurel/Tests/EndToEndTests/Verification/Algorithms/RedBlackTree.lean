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

datatype Tree {
  Leaf(),
  Node(red: bool, key: int, left: Tree, right: Tree)
}

procedure ordered(t: Tree, lo: int, hi: int): bool;
procedure blackHeight(t: Tree, b: int): bool;
procedure contains(t: Tree, x: int): bool;

procedure isRed(t: Tree): bool
{
  Tree..isNode(t) && Tree..red!(t)
};

procedure treeAxioms(): bool
{
  (forall(lo: int) => forall(hi: int) => ordered(Leaf(), lo, hi))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(lo: int) => forall(hi: int) =>
        ordered(Node(c, k, l, r), lo, hi) == (lo < k && k < hi && ordered(l, lo, k) && ordered(r, k, hi)))
  && (forall(b: int) => blackHeight(Leaf(), b) == (b == 0))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(b: int) =>
        blackHeight(Node(c, k, l, r), b) ==
          (!isRed(r) && !(c && isRed(l))
           && blackHeight(l, if c then b else b - 1) && blackHeight(r, if c then b else b - 1)))
  && (forall(x: int) => !contains(Leaf(), x))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(x: int) =>
        contains(Node(c, k, l, r), x) == (k == x || contains(l, x) || contains(r, x)))
};

procedure rotateLeft(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires isRed(Tree..right!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == Tree..red!(h)
  ensures Tree..key!(res) == Tree..key!(Tree..right!(h))
  ensures Tree..left!(res) == Node(true, Tree..key!(h), Tree..left!(h), Tree..left!(Tree..right!(h)))
  ensures Tree..right!(res) == Tree..right!(Tree..right!(h))
{
  var x: Tree := Tree..right!(h);
  res := Node(Tree..red!(h), Tree..key!(x),
              Node(true, Tree..key!(h), Tree..left!(h), Tree..left!(x)),
              Tree..right!(x))
};

procedure rotateRight(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires isRed(Tree..left!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == Tree..red!(h)
  ensures Tree..key!(res) == Tree..key!(Tree..left!(h))
  ensures Tree..left!(res) == Tree..left!(Tree..left!(h))
  ensures Tree..right!(res) == Node(true, Tree..key!(h), Tree..right!(Tree..left!(h)), Tree..right!(h))
{
  var x: Tree := Tree..left!(h);
  res := Node(Tree..red!(h), Tree..key!(x),
              Tree..left!(x),
              Node(true, Tree..key!(h), Tree..right!(x), Tree..right!(h)))
};

procedure flip(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires Tree..isNode(Tree..left!(h))
  requires Tree..isNode(Tree..right!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == !Tree..red!(h)
  ensures Tree..key!(res) == Tree..key!(h)
  ensures Tree..left!(res) == Node(!Tree..red!(Tree..left!(h)), Tree..key!(Tree..left!(h)), Tree..left!(Tree..left!(h)), Tree..right!(Tree..left!(h)))
  ensures Tree..right!(res) == Node(!Tree..red!(Tree..right!(h)), Tree..key!(Tree..right!(h)), Tree..left!(Tree..right!(h)), Tree..right!(Tree..right!(h)))
{
  var l: Tree := Tree..left!(h);
  var r: Tree := Tree..right!(h);
  res := Node(!Tree..red!(h), Tree..key!(h),
              Node(!Tree..red!(l), Tree..key!(l), Tree..left!(l), Tree..right!(l)),
              Node(!Tree..red!(r), Tree..key!(r), Tree..left!(r), Tree..right!(r)))
};

procedure insertAt(h: Tree, x: int) returns (res: Tree)
  requires treeAxioms()
  opaque
  ensures Tree..isNode(res)
  ensures contains(res, x)
{
  if Tree..isLeaf(h) then { res := Node(true, x, Leaf(), Leaf()) }
  else {
    var t: Tree := h;
    if x < Tree..key!(h) then {
      var l: Tree := insertAt(Tree..left!(h), x);
      t := Node(Tree..red!(h), Tree..key!(h), l, Tree..right!(h))
    } else if x > Tree..key!(h) then {
      var r: Tree := insertAt(Tree..right!(h), x);
      t := Node(Tree..red!(h), Tree..key!(h), Tree..left!(h), r)
    };
    if isRed(Tree..right!(t)) && !isRed(Tree..left!(t)) then { t := rotateLeft(t) };
    if isRed(Tree..left!(t)) && isRed(Tree..left!(Tree..left!(t))) then { t := rotateRight(t) };
    if isRed(Tree..left!(t)) && isRed(Tree..right!(t)) then { t := flip(t) };
    res := t
  }
};

procedure insert(root: Tree, x: int, b: int, lo: int, hi: int) returns (res: Tree)
  requires treeAxioms()
  requires ordered(root, lo, hi)
  requires lo < x
  requires x < hi
  requires !isRed(root)
  requires blackHeight(root, b)
  opaque
  ensures ordered(res, lo, hi)
//        ^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures !isRed(res)
  ensures blackHeight(res, b) || blackHeight(res, b + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures contains(res, x)
{
  var t: Tree := insertAt(root, x);
  res := Node(false, Tree..key!(t), Tree..left!(t), Tree..right!(t))
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

datatype Tree {
  Leaf(),
  Node(red: bool, key: int, left: Tree, right: Tree)
}

procedure ordered(t: Tree, lo: int, hi: int): bool;
procedure blackHeight(t: Tree, b: int): bool;
procedure contains(t: Tree, x: int): bool;

procedure isRed(t: Tree): bool
{
  Tree..isNode(t) && Tree..red!(t)
};

procedure treeAxioms(): bool
{
  (forall(lo: int) => forall(hi: int) => ordered(Leaf(), lo, hi))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(lo: int) => forall(hi: int) =>
        ordered(Node(c, k, l, r), lo, hi) == (lo < k && k < hi && ordered(l, lo, k) && ordered(r, k, hi)))
  && (forall(b: int) => blackHeight(Leaf(), b) == (b == 0))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(b: int) =>
        blackHeight(Node(c, k, l, r), b) ==
          (!isRed(r) && !(c && isRed(l))
           && blackHeight(l, if c then b else b - 1) && blackHeight(r, if c then b else b - 1)))
  && (forall(x: int) => !contains(Leaf(), x))
  && (forall(c: bool) => forall(k: int) => forall(l: Tree) => forall(r: Tree) => forall(x: int) =>
        contains(Node(c, k, l, r), x) == (k == x || contains(l, x) || contains(r, x)))
};

procedure rotateLeft(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires isRed(Tree..right!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == Tree..red!(h)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition does not hold
  ensures Tree..key!(res) == Tree..key!(Tree..right!(h))
  ensures Tree..left!(res) == Node(true, Tree..key!(h), Tree..left!(h), Tree..left!(Tree..right!(h)))
  ensures Tree..right!(res) == Tree..right!(Tree..right!(h))
{
  var x: Tree := Tree..right!(h);
  res := Node(true, Tree..key!(x),
              Node(true, Tree..key!(h), Tree..left!(h), Tree..left!(x)),
              Tree..right!(x))
};

procedure rotateRight(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires isRed(Tree..left!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == Tree..red!(h)
  ensures Tree..key!(res) == Tree..key!(Tree..left!(h))
  ensures Tree..left!(res) == Tree..left!(Tree..left!(h))
  ensures Tree..right!(res) == Node(true, Tree..key!(h), Tree..right!(Tree..left!(h)), Tree..right!(h))
{
  var x: Tree := Tree..left!(h);
  res := Node(Tree..red!(h), Tree..key!(x),
              Tree..left!(x),
              Node(true, Tree..key!(h), Tree..right!(x), Tree..right!(h)))
};

procedure flip(h: Tree) returns (res: Tree)
  requires Tree..isNode(h)
  requires Tree..isNode(Tree..left!(h))
  requires Tree..isNode(Tree..right!(h))
  opaque
  ensures Tree..isNode(res)
  ensures Tree..red!(res) == !Tree..red!(h)
  ensures Tree..key!(res) == Tree..key!(h)
  ensures Tree..left!(res) == Node(!Tree..red!(Tree..left!(h)), Tree..key!(Tree..left!(h)), Tree..left!(Tree..left!(h)), Tree..right!(Tree..left!(h)))
  ensures Tree..right!(res) == Node(!Tree..red!(Tree..right!(h)), Tree..key!(Tree..right!(h)), Tree..left!(Tree..right!(h)), Tree..right!(Tree..right!(h)))
{
  var l: Tree := Tree..left!(h);
  var r: Tree := Tree..right!(h);
  res := Node(!Tree..red!(h), Tree..key!(h),
              Node(!Tree..red!(l), Tree..key!(l), Tree..left!(l), Tree..right!(l)),
              Node(!Tree..red!(r), Tree..key!(r), Tree..left!(r), Tree..right!(r)))
};

procedure insertAt(h: Tree, x: int) returns (res: Tree)
  requires treeAxioms()
  opaque
  ensures Tree..isNode(res)
  ensures contains(res, x)
{
  if Tree..isLeaf(h) then { res := Node(true, x, Leaf(), Leaf()) }
  else {
    var t: Tree := h;
    if x < Tree..key!(h) then {
      var l: Tree := insertAt(Tree..left!(h), x);
      t := Node(Tree..red!(h), Tree..key!(h), l, Tree..right!(h))
    } else if x > Tree..key!(h) then {
      var r: Tree := insertAt(Tree..right!(h), x);
      t := Node(Tree..red!(h), Tree..key!(h), Tree..left!(h), r)
    };
    if isRed(Tree..right!(t)) && !isRed(Tree..left!(t)) then { t := rotateLeft(t) };
    if isRed(Tree..left!(t)) && isRed(Tree..left!(Tree..left!(t))) then { t := rotateRight(t) };
    if isRed(Tree..left!(t)) && isRed(Tree..right!(t)) then { t := flip(t) };
    res := t
  }
};

procedure insert(root: Tree, x: int, b: int, lo: int, hi: int) returns (res: Tree)
  requires treeAxioms()
  requires ordered(root, lo, hi)
  requires lo < x
  requires x < hi
  requires !isRed(root)
  requires blackHeight(root, b)
  opaque
  ensures ordered(res, lo, hi)
//        ^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures !isRed(res)
  ensures blackHeight(res, b) || blackHeight(res, b + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures contains(res, x)
{
  var t: Tree := insertAt(root, x);
  res := Node(false, Tree..key!(t), Tree..left!(t), Tree..right!(t))
};
#end

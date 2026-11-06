program Core;

// An example for axiom pruning (`--remove-irrelevant-axioms precise`).
//
// Each uninterpreted function `fI` has one axiom. The procedure first assumes
// one fact about every function, so the assertions after it share a path
// condition that mentions every function. Under the precise mode the relevance
// query of each assertion is seeded with the function names of that whole path
// condition, so every axiom stays relevant; each assertion follows from its own
// function's axiom.
//
// The timing test StrataTestExtra/Transform/IrrelevantAxiomsScaling.lean
// checks this program with 800 functions and 40 assertions and bounds the time
// the pruning takes.

function f0(x : int) : int; axiom [f0_pos]: forall x : int :: int.gt(f0(x), 0);
function f1(x : int) : int; axiom [f1_pos]: forall x : int :: int.gt(f1(x), 0);
function f2(x : int) : int; axiom [f2_pos]: forall x : int :: int.gt(f2(x), 0);
function f3(x : int) : int; axiom [f3_pos]: forall x : int :: int.gt(f3(x), 0);
function f4(x : int) : int; axiom [f4_pos]: forall x : int :: int.gt(f4(x), 0);
function f5(x : int) : int; axiom [f5_pos]: forall x : int :: int.gt(f5(x), 0);
function f6(x : int) : int; axiom [f6_pos]: forall x : int :: int.gt(f6(x), 0);
function f7(x : int) : int; axiom [f7_pos]: forall x : int :: int.gt(f7(x), 0);
function f8(x : int) : int; axiom [f8_pos]: forall x : int :: int.gt(f8(x), 0);
function f9(x : int) : int; axiom [f9_pos]: forall x : int :: int.gt(f9(x), 0);

procedure SharedPath()
{
  var v0 : int; assume [h0]: int.gt(f0(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v0, 1), 2), 3), 4), 5), 6), 7), 8)), 0);
  var v1 : int; assume [h1]: int.gt(f1(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v1, 1), 2), 3), 4), 5), 6), 7), 8)), 1);
  var v2 : int; assume [h2]: int.gt(f2(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v2, 1), 2), 3), 4), 5), 6), 7), 8)), 2);
  var v3 : int; assume [h3]: int.gt(f3(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v3, 1), 2), 3), 4), 5), 6), 7), 8)), 3);
  var v4 : int; assume [h4]: int.gt(f4(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v4, 1), 2), 3), 4), 5), 6), 7), 8)), 4);
  var v5 : int; assume [h5]: int.gt(f5(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v5, 1), 2), 3), 4), 5), 6), 7), 8)), 5);
  var v6 : int; assume [h6]: int.gt(f6(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v6, 1), 2), 3), 4), 5), 6), 7), 8)), 6);
  var v7 : int; assume [h7]: int.gt(f7(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v7, 1), 2), 3), 4), 5), 6), 7), 8)), 7);
  var v8 : int; assume [h8]: int.gt(f8(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v8, 1), 2), 3), 4), 5), 6), 7), 8)), 8);
  var v9 : int; assume [h9]: int.gt(f9(int.add(int.add(int.add(int.add(int.add(int.add(int.add(int.add(v9, 1), 2), 3), 4), 5), 6), 7), 8)), 9);
  assert [g0]: int.gt(f0(0), 0);
  assert [g1]: int.gt(f1(1), 0);
  assert [g2]: int.gt(f2(2), 0);
};

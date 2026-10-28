/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top {
  var xValue: int
}

composite Left extends Top {}
composite Right extends Top {}
composite Bottom extends Left, Right {}

procedure diamondField(b: Bottom)
  opaque
  modifies b
{
  b#xValue := 1
//  ^^^^^^ error: fields that are inherited multiple times can not be accessed.
};
#end

/-! ## The diamond check reaches every position a field access can occupy

The case above reads the ambiguous field from a statement in a top-level procedure — the
position the check was originally written for. It also has to reach three others, because
the driver walks whole procedures and the walk is total:

* inside an INSTANCE METHOD's body (methods are only lifted to `staticProcedures` later, so
  a driver that looked at `staticProcedures` alone would miss them);
* inside a QUANTIFIER body (a sub-expression, not a statement);
* inside a `requires` CLAUSE (a procedure position that is not the body at all).

Each rejection is paired with a UNIQUELY-inherited twin in the same position. Without the
twins, a check that rejected every inherited access — not just the ambiguous ones — would
look correct here.

The ambiguous halves are rejected — the diamond check fires during Laurel→Core, so there is
no program left to run and they stay verification-only. Of the twins, the instance-method one
below gets an `entry` and runs; the quantifier and `requires` twins do not, because the
position they pin is one no interpreter evaluates (the harness ignores `assume`s, and a
precondition is checked against whatever state a driver would have had to set up itself). -/

-- Ambiguous read inside an instance method's body.
-- Verification-only: the diamond check rejects this program during Laurel→Core, so neither
-- interpreter has anything to run. Its accepting twin below does run.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top2<T> { var f: T }
composite L2<T> extends Top2<T> { }
composite R2<T> extends Top2<T> { }
composite D2<T> extends L2<T>, R2<T> {
  procedure getF(self: D2<T>) returns (r: T)
    opaque
    ensures 1 == 1
  {
    r := self#f
//            ^ error: fields that are inherited multiple times can not be accessed.
  };
}
procedure useD2()
  opaque
  modifies *
{
  var d: D2<int> := new D2<int>;
  assert 1 == 1
};
#end

-- Twin: the same read, but `f` is inherited through ONE path, so it must be accepted.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Top3<T> { var f: T }
composite Mid3<T> extends Top3<T> { }
composite D3<T> extends Mid3<T> {
  procedure getF(self: D3<T>) returns (r: T)
    opaque
    ensures 1 == 1
  {
    r := self#f
  };
}
procedure useD3()
  entry
  opaque
  modifies *
{
  var d: D3<int> := new D3<int>;
  assert 1 == 1
};
#end

-- Ambiguous read inside a QUANTIFIER body: a sub-expression position, reached because the
-- check traverses with `mapStmtExprM` rather than matching statement forms.
-- Verification-only: the program is rejected during Laurel→Core.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top4 { var f: int }
composite L4 extends Top4 { }
composite R4 extends Top4 { }
composite D4 extends L4, R4 { }
procedure quantifiedDiamondRead(d: D4)
  opaque
{
  assume forall(i: int) => d#f >= 0;
//                           ^ error: fields that are inherited multiple times can not be accessed.
  assert 1 == 1
};
#end

-- Twin: uniquely inherited, same quantifier position.
-- Verification-only even though this twin is ACCEPTED: the read it pins sits inside a
-- quantifier under an `assume`, and the interpreter paths evaluate neither (the harness sets
-- `ignoreAssumes`, and a quantifier is not evaluated at all), so a driver would execute
-- nothing of the position under test.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top5 { var f: int }
composite Mid5 extends Top5 { }
composite D5 extends Mid5 { }
procedure quantifiedUniqueRead(d: D5)
  opaque
{
  assume forall(i: int) => d#f >= 0;
  assert 1 == 1
};
#end

-- Ambiguous read in a `requires` clause: a procedure position outside the body entirely.
-- Verification-only: the program is rejected during Laurel→Core.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top6 { var f: int }
composite L6 extends Top6 { }
composite R6 extends Top6 { }
composite D6 extends L6, R6 { }
procedure preconditionDiamondRead(d: D6)
  requires d#f >= 0
//           ^ error: fields that are inherited multiple times can not be accessed.
  opaque
  ensures 1 == 1
{ };
#end

-- Twin: uniquely inherited, same precondition position.
-- Verification-only even though this twin is ACCEPTED: the read it pins is in a `requires`
-- clause of a procedure that takes the object as a parameter, so the only way to reach it is a
-- driver that first writes the field itself — which would pin the driver's state, not the
-- inherited read.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top7 { var f: int }
composite Mid7 extends Top7 { }
composite D7 extends Mid7 { }
procedure preconditionUniqueRead(d: D7)
  requires d#f >= 0
  opaque
  ensures 1 == 1
{ };
#end

-- Both at once: an ambiguous read in an INSTANCE METHOD's precondition — a non-body position
-- of a not-yet-lifted procedure, which needs the walk to be total in both dimensions.
-- Verification-only: the program is rejected during Laurel→Core.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Top8 { var f: int }
composite L8 extends Top8 { }
composite R8 extends Top8 { }
composite E8 extends L8, R8 {
  procedure m(self: E8) returns (r: int)
    requires self#f >= 0
//                ^ error: fields that are inherited multiple times can not be accessed.
    opaque
    ensures 1 == 1
  { r := 0 };
}
procedure callerE8(e: E8)
  opaque
{
  assert 1 == 1
};
#end

-- Only the AMBIGUOUS field is rejected, not inheritance on a diamond-shaped hierarchy as
-- such: `lf` is declared on the `L` side alone, so on a `D<int>` that also has an ambiguous
-- `f` available it still reads back the value written to it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Top9<T> { var f: T }
composite L9<T> extends Top9<T> { var lf: int }
composite R9<T> extends Top9<T> { }
composite D9<T> extends L9<T> { var df: int }
procedure uniquelyInheritedOnDiamondShape()
  entry
  opaque
  modifies *
{
  var d: D9<int> := new D9<int>;
  d#lf := 5;
  assert d#lf == 5
};
#end

/-! ## Upcasting to the WRONG supertype

A child's supertype is computed by applying the `extends` remap — `substitutedAncestors` —
not by pairing the child's type arguments with the parent's parameters positionally. The
three shapes below are the ones where those two answers differ, so each is a case a
non-substituting check would wrongly ACCEPT:

* same base name, different argument: `Box<int>`'s parent is `Base<int>`, not `Base<bool>`;
* a remap: `P2<int, bool>`'s parent is `Pair<bool, int>` — the plausible-looking
  `Pair<int, bool>` is precisely what a positional check would produce;
* a concretization: `Box<bool>`'s parent is `Base<int>`, since the parent's argument does not
  depend on the child's at all.

Each accepting counterpart — reading a value back THROUGH the correct parent-typed variable —
is in `Execution/Types/Composites/Inheritance.lean`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite BaseU<T> { var tag: T }
composite BoxU2<T> extends BaseU<T> { var val: T }

procedure upcastWrongInstantiation()
  opaque
  modifies *
{
  var b: BoxU2<int> := new BoxU2<int>;
  var p: BaseU<bool> := b;
//                      ^ error: expected 'BaseU<bool>', got 'BoxU2<int>'
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite PairU<A, B> { var fst: A
 var snd: B }
composite P2U<A, B> extends PairU<B, A> { var extra: int }

procedure upcastWrongRemapTarget()
  opaque
  modifies *
{
  var x: P2U<int, bool> := new P2U<int, bool>;
  var p: PairU<int, bool> := x;
//                           ^ error: expected 'PairU<int, bool>', got 'P2U<int, bool>'
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite BaseV<S> { var b: S }
composite BoxV<T> extends BaseV<int> { var v: T }

procedure upcastWrongConcretizationTarget()
  opaque
  modifies *
{
  var x: BoxV<bool> := new BoxV<bool>;
  var p: BaseV<bool> := x;
//                      ^ error: expected 'BaseV<bool>', got 'BoxV<bool>'
  assert 1 == 1
};
#end

-- An UNRELATED target: `Other<int>` is not an ancestor of `BoxU2<int>` at all. The control
-- for the three cases above, which all involve a genuine ancestor at the wrong arguments —
-- without it, a check that rejected every upcast would look correct.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Other<T> { var o: T }
composite BaseW<T> { var tag: T }
composite BoxW2<T> extends BaseW<T> { var val: T }

procedure upcastToUnrelatedType()
  opaque
  modifies *
{
  var b: BoxW2<int> := new BoxW2<int>;
  var p: Other<int> := b;
//                     ^ error: expected 'Other<int>', got 'BoxW2<int>'
  assert 1 == 1
};
#end

/-! ## A CONCRETE composite extending a generic INSTANTIATION

`IntBox extends Box<int>` is the other direction from the cases above: the child has no type
parameters, but its parent is a monomorph that has to be emitted before it. So the topological
sort has to order a concrete composite after a generated one — and transitively, through a
`Super extends IntBox extends Box<int>` chain where the monomorph is two levels up.

Subtyping compares the SUBSTITUTED ancestor with invariant arguments, so `IntBox`'s only
`Box` supertype is `Box<int>`; `Box<bool>` and a swapped `Pair<bool, int>` are both rejected.
The accepting cases are in `Execution/Types/Composites/Inheritance.lean`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite BoxI<T> { var val: T }
composite IntBox extends BoxI<int> { var w: int }

procedure concreteChildUpcastWrongInstantiation()
  opaque
  modifies *
{
  var ib: IntBox := new IntBox;
  var b: BoxI<bool> := ib;
//                     ^^ error: expected 'BoxI<bool>', got 'IntBox'
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite PairS<A, B> { var a: A
 var b: B }
composite W extends PairS<int, bool> { var w: int }

procedure concreteChildUpcastSwappedArguments()
  opaque
  modifies *
{
  var x: W := new W;
  var p: PairS<bool, int> := x;
//                           ^ error: expected 'PairS<bool, int>', got 'W'
  assert 1 == 1
};
#end

-- A diamond-inherited field read on a GENERIC receiver. The receiver's type is `.Applied`
-- (`D<int>`), so the diamond check has to peel it to the base name before looking at the
-- ancestors. Missing that, the access slips past pre-monomorphization and resurfaces as an
-- internal error when the monomorph re-resolves — a rejection reported as a compiler bug.
#eval testLaurelResolution <|
#strata
program Laurel;
composite TopG<T> { var f: T }
composite LG<T> extends TopG<T> { }
composite RG<T> extends TopG<T> { }
composite DG<T> extends LG<T>, RG<T> { }

procedure diamondFieldOnGenericReceiver()
  opaque
  modifies *
{
  var d: DG<int> := new DG<int>;
  var x: int := d#f;
//                ^ error: fields that are inherited multiple times can not be accessed.
  assert 1 == 1
};
#end

/-! ## An inherited generic METHOD on a diamond

`DG<int>` reaches `GBaseG` at both `GBaseG<bool>` and `GBaseG<int>`, so `innerG` has no single
type argument at it, however the receiver is typed: through a constrained type, a generic field or
a generic call's result (also one with a hole argument), and under an `if`, a block, an assignment
or an `old`. The error is at the receiver, and once for a generic body cloned twice. A parameter
that mentions no type variable takes the diamond by an upcast. An unused `var h: H<…>` makes its
procedure monomorphized, without which neither of the last two cases would be checked. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite GBaseG<T> { var v: T }
composite MidG extends GBaseG<bool> { }
composite LG<X> extends GBaseG<X> { }
composite DG<X> extends MidG, LG<X> { }
constrained CD = d: DG<int> where true witness <??>
composite H<X> { var d: DG<X> }
composite K<X> { var h: H<X> }
procedure mkDG<X>(x: X) returns (r: DG<X>) opaque;
procedure mkDGh<X>(x: X, y: X) returns (r: DG<X>) opaque;
procedure innerG<T>(p: GBaseG<T>) returns (r: T) opaque { r := p#v };

procedure constrainedReceiver(c: CD) opaque {
  var g: int := innerG(c)
//                     ^ error: 'CD' reaches 'GBaseG' at both 'GBaseG<bool>' and 'GBaseG<int>'
};

procedure fieldReceiver(k: K<int>) opaque {
  var g: int := innerG(k#h#d)
//                         ^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure callResultReceiver() opaque {
  var g: int := innerG(mkDG(1))
//                     ^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure holeBuiltReceiver() opaque {
  var g: int := innerG(mkDGh(1, <?>))
//                     ^^^^^^^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure ifCallReceiver(b: bool) opaque {
  var g: int := innerG(if b then mkDG(1) else mkDG(1))
//                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure blockFieldReceiver(h: H<int>) opaque {
  var g: int := innerG({ h#d })
//                     ^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure assignCallReceiver() opaque {
  var e: DG<int>;
  var g: int := innerG(e := mkDG(1))
//                     ^^^^^^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure oldFieldReceiver(h: H<int>) opaque modifies h {
  h#d := mkDG(2);
  var g: int := innerG(old(h#d))
//                     ^^^^^^^^ error: 'DG<int>' reaches 'GBaseG' at both
};

procedure inGenericBody<S>(x: S, d: DG<int>) returns (r: S) opaque {
  var h: H<S>;
  var g: int := innerG(d);
//                     ^ error: 'DG<int>' reaches 'GBaseG' at both
  r := x
};

procedure callsItTwice(d: DG<int>) opaque {
  var a: int := inGenericBody(1, d);
  var b: bool := inGenericBody(true, d)
};

procedure upcastOnly<T>(b: GBaseG<bool>, x: T) returns (r: T)
  opaque ensures r == x { var h: H<T>; r := x };

procedure noTypeArgumentAtStake(d: DG<int>) opaque {
  var r: int := upcastOnly(d, 1);
  assert r == 1
};
#end

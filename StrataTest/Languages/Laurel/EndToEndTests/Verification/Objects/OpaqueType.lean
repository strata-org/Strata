/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel
import StrataDDM.Integration.Lean.HashCommands

open StrataTest.Util
open Strata

/-
Opaque types (`opaque Name<T…>`): a named, optionally generic type with NO
constructors whose implementation is *native* rather than written in Laurel.

Unlike a datatype, an opaque type lowers to a Core opaque type constructor
(`Core.TypeDecl.con`, i.e. an SMT `declare-sort`) rather than to
`Core.TypeDecl.data`. That distinction is the whole point: Core's `LDatatype`
requires a non-empty constructor list, so a zero-constructor *datatype* is given a
synthetic unit constructor and collapses to a SINGLETON — every value of it
provably equal. An opaque type keeps its values distinct, which is what any
natively-implemented type (a set, a sequence, a handle) needs.

A Laurel program can therefore pass opaque values around, store them, and compare
them, but cannot take them apart: the only operations are the procedures declared
over the type.

An opaque type's name reaches SMT verbatim as a `declare-sort`, so it can collide with
a sort the solver already claims. These cases are named `Handle`/`Token` for that
reason: `Bag` (say) is cvc5's built-in multiset sort, and under stable safe-mode a term
of type `(Bag Int)` is rejected with "Logic restricted in stable mode", surfacing as an
SMT crash rather than a Laurel diagnostic. Nothing currently guards against this.
-/

/-! ## Values of an opaque type are distinct

The essential property, and the one a zero-constructor datatype gets wrong. If
`Handle` were lowered as a datatype it would carry a single nullary constructor and
`a == b` would be *provable*. Instead the solver refutes it — "does not hold" (a
counterexample exists), not merely "could not be proved". -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Handle

procedure distinctValues(a: Handle, b: Handle)
  opaque
{
  assert a == b
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## An opaque sort is inhabited and equality on it behaves

Reflexivity holds (it is a real sort), and an opaque value survives a round trip
through a polymorphic identity — the `ftvar`/`declare-sort` unification path. -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Handle

procedure id<T>(x: T): T { return x };

procedure reflexive(a: Handle)
  opaque
{
  assert a == a;
  assert id(a) == a
};
#end

/-! ## Generic opaque types

`opaque Token<T>` — the type parameter is a real Core sort argument (`declare-sort`
arity 1), neither erased nor monomorphized, exactly like a generic datatype's. A
`Token<int>` flows through polymorphic code and back. -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Token<T>

procedure id<T>(x: T): T { return x };

procedure typeArgsFlow(si: Token<int>, sb: Token<bool>)
  opaque
{
  assert id(si) == si;
  assert id(sb) == sb
};
#end

/-! Must-fail twin: two distinct `Token<int>` parameters are not equal, so the block
    above passes on real reasoning about the sort rather than on everything of an
    opaque type collapsing to one value. -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Token<T>

procedure notAllEqual(si: Token<int>, sj: Token<int>)
  opaque
{
  assert si == sj
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A generic opaque type must be applied to its type arguments

Same rule as a generic datatype: leaving the argument implicit would let first use
elsewhere fix it, order-dependently. -/
#eval testLaurelResolution <|
#strata
program Laurel;
opaque Token<T>

procedure bare(s: Token)
//                ^^^^^ error: generic opaque type 'Token' must be applied to 1 type argument(s)
  opaque
{
};
#end

/-! ## Arity is checked in both directions

A NON-generic opaque type applied to arguments, and a generic one applied at the
wrong arity. Both are rejected in Laurel rather than reaching Core as a
wrong-arity `declare-sort`. -/
#eval testLaurelResolution <|
#strata
program Laurel;
opaque Handle
opaque Token<T>

procedure notGeneric(h: Handle<int>)
//                      ^^^^^^^^^^^ error: type 'Handle' is not generic and cannot be applied to type arguments
  opaque
{
};

procedure wrongArity(s: Token<int, bool>)
//                      ^^^^^^^^^^^^^^^^ error: generic opaque type 'Token' expects 1 type argument(s) but 2 were provided
  opaque
{
};
#end

/-! ## An opaque value is not a heap reference

Only genuine composites are heap references, so `isCompositeParam` tests `isComposite`: an
opaque parameter attracts no `Composite..ref!` well-formedness clauses. Mixing an opaque
parameter with composite field access is the ordinary case, so this must verify. -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Handle
composite Counter { var value: int }

procedure touchComposite(h: Handle, c: Counter)
  opaque
  modifies c
{
  c#value := c#value + 1
};

procedure readComposite(h: Handle, c: Counter) returns (r: int)
  opaque
{
  return c#value
};
#end

/-! ## An opaque type is boxable as a composite field

A field's type decides its heap box variant. An opaque type gets its own variant carrying
its own sort, like a datatype, so reading and writing an opaque-typed composite field
round-trips at the opaque sort rather than at `Composite`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
opaque Handle
composite Container { var h: Handle }

procedure setField(c: Container, x: Handle)
  opaque
  modifies c
{
  c#h := x
};

procedure getField(c: Container) returns (r: Handle)
  opaque
{
  return c#h
};

// Round trip: what was written is what is read back.
procedure writeThenRead(c: Container, x: Handle)
  opaque
  modifies c
{
  c#h := x;
  assert c#h == x
};
#end

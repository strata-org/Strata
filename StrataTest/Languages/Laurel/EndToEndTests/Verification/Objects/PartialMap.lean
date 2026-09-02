/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel
import StrataDDM.Integration.Lean.HashCommands

open StrataTest.Util
open Strata

/-!
# Partial maps

`Map<K, V>` is a built-in: `CoreDefinitionsForLaurel` declares it plus its operations. Nothing
here declares anything — these programs use the prelude.

Unlike `Set`, `Map` is not a Core sort with axioms. It is a type *alias* for one total map to a
presence-carrying datatype,

    type Map<K, V> = TotalMap K ($MapEntry<V>)

so there are no map axioms at all: `mapSet`/`mapGet`/`mapRemove`/`mapContains` are ordinary
Laurel procedures whose bodies are `update`/`select` plus datatype constructors, testers and
selectors — the prelude's own text, not a lowering rule. Under
`--use-array-theory` those total-map terms are the SMT array theory's own `select`/`store`.
(`mapEmpty()` is Core's `mapConst`, which keeps its own select-of-const axiom in both
encodings — `(as const (Array …))` is a cvc5 extension that rejects symbolic arguments, so it
is not used.)

Maps are immutable with value semantics: `mapSet`/`mapRemove` return a new map and never
modify their argument, so no heap reasoning is involved.

`mapGet` is total but unconstrained on an absent key, mirroring `select` on a `TotalMap` —
the "unspecified value" blocks below pin that it is genuinely unconstrained rather than
accidentally pinned to something.
-/

/-! ## Membership after set and remove -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure setThenContains(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  assert mapContains(mapSet(m, k, v), k)
};

procedure removeThenNotContains(m: Map<int, bool>, k: int)
  opaque
{
  assert !mapContains(mapRemove(m, k), k)
};

// A different key is unaffected — the "preserve" half, and what makes this a map rather
// than a black box.
procedure otherKeyUnaffected(m: Map<int, bool>, j: int, k: int, v: bool)
  requires j != k
  opaque
{
  assert mapContains(mapSet(m, k, v), j) == mapContains(m, j);
  assert mapContains(mapRemove(m, k), j) == mapContains(m, j);
  assert mapGet(mapSet(m, k, v), j) == mapGet(m, j)
};

// Immutability: the operand is not modified.
procedure operandUnchanged(m: Map<int, bool>, k: int, j: int, v: bool)
  opaque
{
  var before: bool := mapContains(m, j);
  var n: Map<int, bool> := mapSet(m, k, v);
  assert mapContains(m, j) == before
};

// The empty map has no keys. Its key and value types come from the declared type of the
// binding, since no argument determines them.
procedure emptyHasNoKeys(k: int)
  opaque
{
  var e: Map<int, bool> := mapEmpty();
  assert !mapContains(e, k)
};
#end

/-! ## Reading back what was written -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure getAfterSet(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  assert mapGet(mapSet(m, k, v), k) == v
};

// The last write to a key wins.
procedure lastWriteWins(m: Map<int, bool>, k: int, v: bool, w: bool)
  opaque
{
  assert mapGet(mapSet(mapSet(m, k, v), k, w), k) == w
};

// Set-then-remove-then-set: removal does not leave the old value visible.
procedure setAfterRemove(m: Map<int, bool>, k: int, v: bool, w: bool)
  opaque
{
  var m1: Map<int, bool> := mapSet(m, k, v);
  var m2: Map<int, bool> := mapRemove(m1, k);
  var m3: Map<int, bool> := mapSet(m2, k, w);
  assert mapContains(m3, k);
  assert mapGet(m3, k) == w
};

// Building a map up from empty, nested rather than through intermediate bindings: the type
// arguments of the inner `mapEmpty()` are recovered by inference, not from a declared type.
procedure nestedFromEmpty(k: int, j: int)
  requires j != k
  opaque
{
  var m: Map<int, int> := mapSet(mapSet(mapEmpty(), k, 7), j, 9);
  assert mapGet(m, k) == 7;
  assert mapGet(m, j) == 9;
  assert mapContains(m, k) && mapContains(m, j)
};
#end

/-! ## Maps are generic

The key and value types are real Core type arguments, so `Map<int, bool>` and
`Map<bool, int>` are different types and the operations instantiate per call site. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure genericKeyAndValueTypes(mib: Map<int, bool>, mbi: Map<bool, int>, i: int, b: bool)
  opaque
{
  assert mapContains(mapSet(mib, i, b), i);
  assert mapContains(mapSet(mbi, b, i), b);
  assert mapGet(mapSet(mib, i, b), i) == b;
  assert mapGet(mapSet(mbi, b, i), b) == i
};

// A map as a map's value type: `$MapEntry` nests, since it is an ordinary datatype.
procedure nestedMapValue(m: Map<int, Map<int, bool>>, k: int, inner: Map<int, bool>)
  opaque
{
  assert mapContains(mapSet(m, k, inner), k);
  assert mapGet(mapSet(m, k, inner), k) == inner
};
#end

/-! ## Extensional equality

This is the property the representation is chosen for. Absence is *canonical*: a removed key
holds `$MapAbsent()`, exactly what an untouched key already holds. So two maps are equal
precisely when they have the same keys mapped to the same values — no operand carries
unobservable state that `==` could wrongly distinguish.

All of it is provable under the DEFAULT encoding — the total map's own axioms plus canonical
absence suffice, with no need for `--use-array-theory`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Removing a key just written is the same map as removing it from the original.
procedure removeAfterSetIsRemove(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  assert mapRemove(mapSet(m, k, v), k) == mapRemove(m, k)
};

// Writing the value a key already holds changes nothing.
procedure setIsIdempotent(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  var m1: Map<int, bool> := mapSet(m, k, v);
  assert mapSet(m1, k, v) == m1
};

// Removing a key twice is the same as removing it once.
procedure removeIsIdempotent(m: Map<int, bool>, k: int)
  opaque
{
  var m1: Map<int, bool> := mapRemove(m, k);
  assert mapRemove(m1, k) == m1
};

// Removing an absent key is a no-op, so the empty map is unchanged by removal.
procedure removeFromEmpty(k: int)
  opaque
{
  var e: Map<int, bool> := mapEmpty();
  assert mapRemove(e, k) == e
};

// Insertion ORDER does not matter — the sharpest consequence of canonical absence.
procedure insertionOrderIrrelevant(m: Map<int, bool>)
  opaque
{
  assert mapSet(mapSet(m, 1, true), 2, false) == mapSet(mapSet(m, 2, false), 1, true)
};

// The same, built up from the empty map: two maps with the same keys and values are equal
// however they were constructed.
procedure builtInEitherOrderFromEmpty()
  opaque
{
  var m1: Map<int, bool> := mapSet(mapSet(mapEmpty(), 1, true), 2, false);
  var m2: Map<int, bool> := mapSet(mapSet(mapEmpty(), 2, false), 1, true);
  assert m1 == m2
};
#end
/-! ## ... and maps that differ are provably distinct

The other half of extensional equality, and the guard against reading the block above as
better news than it is. An encoding that proved *every* pair of maps equal would satisfy those
laws too, and would be unsound. Pinning both directions is what makes `==` on `Map<K, V>`
decided rather than merely permissive. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Same key set, different value at one key.
procedure distinctValuesAreDistinct(m: Map<int, bool>)
  opaque
{
  assert mapSet(m, 1, true) != mapSet(m, 1, false)
};

// Same values where both are present, but different key sets.
procedure distinctKeySetsAreDistinct(m: Map<int, bool>)
  opaque
{
  assert mapSet(m, 1, true) != mapRemove(mapSet(m, 1, true), 1)
};
#end

/-! ## The same laws under the SMT array theory

`--use-array-theory` encodes the underlying total map as a real SMT array — a different
encoding path, with the array theory's own `ext` axiom doing the work instead of the McCarthy
axioms. The laws have to hold there too, and nothing else in this file exercises that path.
Two representatives, one from each direction; the exhaustive set is covered above. -/
#eval testLaurelVerification
    (options := { defaultLaurelTestOptions with
      verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := true } }) <|
#strata
program Laurel;
procedure orderIrrelevantUnderArrayTheory(m: Map<int, bool>)
  opaque
{
  assert mapSet(mapSet(m, 1, true), 2, false) == mapSet(mapSet(m, 2, false), 1, true)
};

procedure distinctValuesUnderArrayTheory(m: Map<int, bool>)
  opaque
{
  assert mapSet(m, 1, true) != mapSet(m, 1, false)
};
#end

/-! ## A partial map as a composite field

A field is boxed through the heap like any other: `HeapParameterization` synthesizes a `$Box`
variant per field-type instantiation, carrying the map as its payload. `TypeAliasElim` runs
first, so the payload type is already `TotalMap K ($MapEntry V)` and `$MapEntry` is ordered
before `$Box` by the ordinary traversal — no pass is told about the representation.

The first procedure uses no map operations at all, so it isolates the boxing itself. -/
#eval testLaurelVerification <|
#strata
program Laurel;
composite H { var m: Map<int, bool> }

procedure fieldRoundTrips(h: H, g: H)
  opaque
  modifies h
{
  h#m := g#m;
  assert h#m == g#m
};

procedure fieldWithOps(h: H, k: int)
  opaque
  modifies h
{
  h#m := mapSet(h#m, k, true);
  assert mapContains(h#m, k);
  assert mapGet(h#m, k)
};

// A NESTED partial map as a field: the alias has to expand under itself, so the payload is
// `TotalMap int ($MapEntry (TotalMap int ($MapEntry bool)))`. Nothing else crosses both axes —
// the non-field tests nest but are not boxed, and the field tests above are boxed but not
// nested.
composite N { var mm: Map<int, Map<int, bool>> }

procedure nestedFieldRoundTrips(n: N, inner: Map<int, bool>, k: int)
  opaque
  modifies n
{
  n#mm := mapSet(n#mm, k, inner);
  assert mapContains(n#mm, k);
  assert mapGet(n#mm, k) == inner
};

// A total and a partial map as fields of ONE composite, at the same key and value types. Both
// are `.TMap` after alias expansion, so they tag as `TotalMap$a2$int$bool` and
// `TotalMap$a2$int$$MapEntry$a1$bool`: distinct only because the value types differ. Were they
// to coincide, both fields would name the same `$Box` variant and a read of one would unwrap
// the other's payload.
composite Both {
  var total: TotalMap int bool
  var partial: Map<int, bool>
}

procedure bothKindsStayDistinct()
  opaque
{
  var b: Both := new Both;
  b#total := update(b#total, 1, true);
  b#partial := mapSet(b#partial, 1, false);
  assert select(b#total, 1);
  assert mapContains(b#partial, 1);
  assert !mapGet(b#partial, 1)
};
#end

/-! ## The alias is transparent

`Map<K, V>` and its expansion are one type, so they are interchangeable and the total-map
primitives apply directly to a partial map. That is a consequence of aliasing rather than an
oversight — an `opaque` type would have hidden the representation — and it is what lets the
prelude's own signatures spell the expansion out while user code writes `Map<K, V>`. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Declared with the expansion, called with the alias.
procedure containsViaExpansion(m: TotalMap int ($MapEntry<bool>), k: int): bool
{
  return mapContains(m, k)
};

procedure aliasAndExpansionAgree(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  assert containsViaExpansion(mapSet(m, k, v), k)
};

// `select` reads the entry out of a partial map directly.
procedure representationIsVisible(m: Map<int, bool>, k: int, v: bool)
  opaque
{
  assert $MapEntry..is$MapPresent(select(mapSet(m, k, v), k))
};
#end

/-! ## A user alias over a partial map

`Map<K, V>` is itself an alias, so an alias over it expands transitively. This also covers the
alias reaching re-resolution: `resolveUnorderedCore` both registers aliases and puts them in the
type lattice's `unfoldMap`, without which the name either fails to resolve at all or resolves
without unfolding and then will not match the primitive it expands to. -/
#eval testLaurelVerification <|
#strata
program Laurel;
type IntBoolMap = Map<int, bool>

procedure viaUserAlias(m: IntBoolMap, k: int, v: bool)
  opaque
{
  assert mapContains(mapSet(m, k, v), k);
  assert mapGet(mapSet(m, k, v), k) == v
};

// The alias and its expansion are interchangeable in both directions.
procedure userAliasMatchesMap(m: IntBoolMap, n: Map<int, bool>, k: int)
  opaque
{
  assume m == n;
  assert mapContains(m, k) == mapContains(n, k)
};
#end

/-! ## An undetermined value type is a user error, not a compiler bug

`mapEmpty()` binds neither `K` nor `V` from arguments, and `mapContains` mentions `V` nowhere
in its own signature — so if the use site does not supply it either, nothing does. Such a call
is rejected in `LaurelToCoreSchemaPass` with an actionable message. Left alone it would reach
the SMT encoder as a free type variable and be reported as `strata-bug: … should be fully
monomorphic`, blaming the compiler for a program that is genuinely ambiguous.

The positive cases above pin the other half: a nested `mapEmpty()` under `mapSet` is determined
by the value argument, and an annotated binding supplies both parameters, so neither is
flagged. -/
#eval testLaurelVerification <|
#strata
program Laurel;
procedure valueTypeUndetermined(k: int)
  opaque
{
  assert !mapContains(mapEmpty(), k)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^ error: cannot infer the value type of the map passed to 'mapContains': 'mapContains' does not mention it and nothing at this use site supplies it. Bind the map to an annotated variable first, e.g. `var m: Map<int, bool> := mapEmpty()`.
};

// Same through a chain that also leaves `V` open: `mapRemove` returns the map, so it
// propagates the ambiguity rather than resolving it.
procedure valueTypeUndeterminedThroughRemove(k: int)
  opaque
{
  assert !mapContains(mapRemove(mapEmpty(), k), k)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: cannot infer the value type of the map passed to 'mapContains': 'mapContains' does not mention it and nothing at this use site supplies it. Bind the map to an annotated variable first, e.g. `var m: Map<int, bool> := mapEmpty()`.
};
#end

/-! ## Must-fail twins

Each pins that the encoding says only what it should. Without these the blocks above could
be passing because `mapContains`/`mapGet` are over-constrained. -/
#eval testLaurelVerification <|
#strata
program Laurel;
// Writing `k` says nothing about the membership of a different key `j`.
procedure setDoesNotAddOtherKeys(m: Map<int, bool>, j: int, k: int, v: bool)
  requires j != k
  opaque
{
  assert mapContains(mapSet(m, k, v), j)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// `mapGet` on an absent key is UNCONSTRAINED, not some default: nothing can be proved
// about it. (If this ever verifies, `mapGet` has been given a value off-domain.)
procedure getOnAbsentKeyIsUnspecified(m: Map<int, bool>, k: int)
  requires !mapContains(m, k)
  opaque
{
  assert mapGet(m, k)
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Nor is it constrained to the *other* boolean.
procedure getOnAbsentKeyIsNotFalse(m: Map<int, bool>, k: int)
  requires !mapContains(m, k)
  opaque
{
  assert !mapGet(m, k)
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// A removed key's old value is not recoverable.
procedure removedValueIsGone(m: Map<int, bool>, k: int)
  requires mapContains(m, k)
  requires mapGet(m, k)
  opaque
{
  assert mapGet(mapRemove(m, k), k)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// Membership of one key says nothing about another.
procedure containsIsPerKey(m: Map<int, bool>, j: int, k: int)
  requires mapContains(m, k)
  requires j != k
  opaque
{
  assert mapContains(m, j)
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

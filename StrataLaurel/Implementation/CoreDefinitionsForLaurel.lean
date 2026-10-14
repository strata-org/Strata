/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import StrataDDM.Integration.Lean.HashCommands -- shake: keep
public import StrataLaurel.Implementation.LaurelAST
import StrataLaurel.Implementation.Grammar.ConcreteToAbstractTreeTranslator
import StrataLaurel.Implementation.Grammar.LaurelGrammar

namespace Strata.Laurel

public section

/--
Core built-in definitions expressed in Laurel syntax.

Includes:
- Total-map primitives (`select`, `update`, `mapConst`) — polymorphic operations on
  `TotalMap`, Core's total map (an SMT array).
- The partial `Map<K, V>` and its operations, built on top of `TotalMap`.
- Type-specific external operators (`intAdd`, `realAdd`, etc.) — the Core primitives.
- Overloaded transparent wrappers (`add`, `sub`, etc.) — dispatching to the
  type-specific externals. The parser emits `StaticCall "add"` and resolution
  picks the right overload based on argument types.

The map primitives and the equality wrappers carry generic signatures
(`select<K,V>(map: TotalMap K V, key: K) : V`). Resolution instantiates them per call site
from the actual argument types (`callSiteTypeSubst`), so `select` on a `TotalMap int bool`
reports `bool`. A bare `.TVar` there would be a gradual wildcard under `isConsistent`,
leaving every use of the result unchecked.

The generic `Result` datatype that the exceptional-channel lowering targets is
*not* part of this always-on prelude: it is injected by `EliminateExceptions`
only when a program actually uses exceptions (see `resultDefinitions`), so a
program that never throws does not carry it.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

datatype LaurelResolutionErrorPlaceholder {}
datatype Float64IsNotSupportedYet {}
datatype LaurelUnit { MkLaurelUnit() }

// These are internal stand-ins for Core's native, already-polymorphic TOTAL-map primitives
// (the real signatures live in Core.Factory). Declared `external`, they are filtered out
// before Core translation and never reach Core; calls resolve to the Core primitives by
// name. Nothing observes these signatures at translation time, but resolution does: the generic
// form lets a call site infer `K`/`V` from its actual arguments (`callSiteTypeSubst`) and report
// a concrete result type. The polymorphism callers ultimately rely on is the Core primitives' own.
procedure select<K, V>(map: TotalMap K V, key: K) : V
  external;

procedure update<K, V>(map: TotalMap K V, key: K, value: V) : TotalMap K V
  external;

// `K` is not determined by the single value argument, so it comes from the CHECK direction:
// resolution matches this declared return type against the expected type at the call site
// (`var m: TotalMap int bool := mapConst(false)` binds `K ↦ int`) and reports an error when
// nothing determines it. `LaurelToCoreSchemaPass` then reads it off the binding.
procedure mapConst<K, V>(value: V) : TotalMap K V
  external;

// --- Immutable sets ---
//
// `Set` is an `opaque` type naming Core's native `Set` sort (see `setTy` in `Core.Factory`
// for what that sort is and why it is not a `TotalMap T bool` alias).
//
// Declared `external`, so these never reach Core as functions; each call is lowered to the
// corresponding Core `Set.*` op by `coreSetOpName?`. The spellings differ (`setInsert` vs
// `Set.insert`) only because a Laurel identifier cannot contain a `.`.
//
// `setEmpty`'s element type is not determined by any argument, so — like `mapConst`'s key — it
// is bound by resolution's check direction from the declared type at the use site
// (`var s: Set<int> := setEmpty()`), and is a resolution error when nothing supplies it.
opaque Set<T>

procedure setEmpty<T>() : Set<T> external;
procedure setContains<T>(s: Set<T>, x: T) : bool external;
procedure setInsert<T>(s: Set<T>, x: T) : Set<T> external;
procedure setRemove<T>(s: Set<T>, x: T) : Set<T> external;
procedure setUnion<T>(s: Set<T>, t: Set<T>) : Set<T> external;
procedure setIntersect<T>(s: Set<T>, t: Set<T>) : Set<T> external;
procedure setDifference<T>(s: Set<T>, t: Set<T>) : Set<T> external;

// --- Partial maps ---
//
// `Map<K, V>` is a PARTIAL map: a key may be absent. It is an alias, not a sort of its own —
// one total map to a datatype recording presence. `$MapEntry` is `$`-prefixed because it is
// an implementation detail, not something to be written in source.
//
// `TypeAliasElim` expands the alias before the heap and ordering passes, so every pass that
// walks a `HighType` sees `$MapEntry` structurally and none of them needs to know about the
// representation.
//
// Absence is canonical: `mapRemove` stores `$MapAbsent()`, which is what an untouched key
// already holds, so `==` on two `Map<K, V>` values is extensional map equality.
//
// `mapGet` is TOTAL but unconstrained on an absent key, mirroring `select` on a `TotalMap`.
// It reads through the unsafe `$MapEntry..value!`; the safe destructor carries an
// `is$MapPresent` precondition, which would make every read a proof obligation.
datatype $MapEntry<V> {
  $MapAbsent(),
  $MapPresent(value: V)
}

type Map<K, V> = TotalMap K ($MapEntry<V>)

// The only operation with no map argument, so nothing here binds `K` or `V`. A body would need
// to name `mapConst`'s key type, which Laurel cannot do at a call, so this one is lowered in
// `LaurelToCoreSchemaPass` from the declared type at the use site
// (`var m: Map<int, bool> := mapEmpty()`), as for `setEmpty`.
procedure mapEmpty<K, V>() : Map<K, V> external;

procedure mapContains<K, V>(m: Map<K, V>, k: K) : bool
{
  return $MapEntry..is$MapPresent(select(m, k))
};

procedure mapGet<K, V>(m: Map<K, V>, k: K) : V
{
  return $MapEntry..value!(select(m, k))
};

procedure mapSet<K, V>(m: Map<K, V>, k: K, v: V) : Map<K, V>
{
  return update(m, k, $MapPresent(v))
};

procedure mapRemove<K, V>(m: Map<K, V>, k: K) : Map<K, V>
{
  return update(m, k, $MapAbsent())
};

opaque Sequence<T>

procedure seqEmpty<T>() : Sequence<T> external;
procedure seqLength<T>(s: Sequence<T>) : int external;
procedure seqSelect<T>(s: Sequence<T>, i: int) : T
  requires 0 <= i && i < seqLength(s)
  external;
procedure seqBuild<T>(s: Sequence<T>, v: T) : Sequence<T> external;
procedure seqUpdate<T>(s: Sequence<T>, i: int, v: T) : Sequence<T>
  requires 0 <= i && i < seqLength(s)
  external;
procedure seqAppend<T>(s: Sequence<T>, t: Sequence<T>) : Sequence<T> external;
procedure seqContains<T>(s: Sequence<T>, v: T) : bool external;
procedure seqTake<T>(s: Sequence<T>, n: int) : Sequence<T>
  requires 0 <= n && n <= seqLength(s)
  external;
procedure seqDrop<T>(s: Sequence<T>, n: int) : Sequence<T>
  requires 0 <= n && n <= seqLength(s)
  external;

// --- Type-specific external operators (Core primitives) ---

// Integer arithmetic
procedure $intAdd(x: int, y: int) : int external;
procedure $intSub(x: int, y: int) : int external;
procedure $intMul(x: int, y: int) : int external;
procedure $intDiv(x: int, y: int) : int external;
procedure $intSafeDiv(x: int, y: int) : int external;
procedure $intMod(x: int, y: int) : int external;
procedure $intSafeMod(x: int, y: int) : int external;
procedure $intDivT(x: int, y: int) : int external;
procedure $intSafeDivT(x: int, y: int) : int external;
procedure $intModT(x: int, y: int) : int external;
procedure $intSafeModT(x: int, y: int) : int external;
procedure $intNeg(x: int) : int external;

// Integer comparisons
procedure $intLt(x: int, y: int) : bool external;
procedure $intLe(x: int, y: int) : bool external;
procedure $intGt(x: int, y: int) : bool external;
procedure $intGe(x: int, y: int) : bool external;

// Real arithmetic
procedure $realAdd(x: real, y: real) : real external;
procedure $realSub(x: real, y: real) : real external;
procedure $realMul(x: real, y: real) : real external;
procedure $realDiv(x: real, y: real) : real external;
procedure $realNeg(x: real) : real external;

// Real comparisons
procedure $realLt(x: real, y: real) : bool external;
procedure $realLe(x: real, y: real) : bool external;
procedure $realGt(x: real, y: real) : bool external;
procedure $realGe(x: real, y: real) : bool external;

// Bitvector comparisons, per width.
//
// Bitvector types are width-parameterized, so unlike `int`/`real` they cannot be
// covered by a single overload. Core generates its bitvector operators per width
// (`Bv32.SLt`, …) for widths 1, 8, 16, 32, 64 and 128 (see `Factory.lean`'s
// `DefBVOpFuncExprs`); the wrappers below cover 1 through 64, so a comparison at
// any other width — including the 128 that Core does support — reports "no overload
// matches" rather than silently mistranslating.
//
// These are the *signed* comparisons, which preserves the previous behaviour:
// before operators became procedure calls, a bitvector comparison was lowered to
// the *integer* operator (`intLt`), i.e. signed. Laurel's `bv n` carries no
// signedness, so an unsigned comparison is not currently expressible.
procedure $bv1SLt(x: bv 1, y: bv 1) : bool external;
procedure $bv1SLe(x: bv 1, y: bv 1) : bool external;
procedure $bv1SGt(x: bv 1, y: bv 1) : bool external;
procedure $bv1SGe(x: bv 1, y: bv 1) : bool external;
procedure $bv8SLt(x: bv 8, y: bv 8) : bool external;
procedure $bv8SLe(x: bv 8, y: bv 8) : bool external;
procedure $bv8SGt(x: bv 8, y: bv 8) : bool external;
procedure $bv8SGe(x: bv 8, y: bv 8) : bool external;
procedure $bv16SLt(x: bv 16, y: bv 16) : bool external;
procedure $bv16SLe(x: bv 16, y: bv 16) : bool external;
procedure $bv16SGt(x: bv 16, y: bv 16) : bool external;
procedure $bv16SGe(x: bv 16, y: bv 16) : bool external;
procedure $bv32SLt(x: bv 32, y: bv 32) : bool external;
procedure $bv32SLe(x: bv 32, y: bv 32) : bool external;
procedure $bv32SGt(x: bv 32, y: bv 32) : bool external;
procedure $bv32SGe(x: bv 32, y: bv 32) : bool external;
procedure $bv64SLt(x: bv 64, y: bv 64) : bool external;
procedure $bv64SLe(x: bv 64, y: bv 64) : bool external;
procedure $bv64SGt(x: bv 64, y: bv 64) : bool external;
procedure $bv64SGe(x: bv 64, y: bv 64) : bool external;

// Bitvector bitwise operations and int<->bv conversions, per width.
//
// Core's `Bv{W}.And/Or/Xor/Not/Shl/UShr/SShr` operations and the three casts
// `Bv{W}.ToInt` (signed), `Bv{W}.ToUInt` (unsigned) and `Int.ToBv{W}` are
// exposed here for widths 1 through 128 -- the full set Core supports, unlike
// the comparison wrappers above which stop at 64.
//
// `$intToBv{W}` is TRUNCATING: it is SMT-LIB's `(_ int_to_bv W)`, i.e.
// `x mod 2^W`, so an out-of-range operand wraps silently rather than being
// rejected. The int-level wrappers below carry the range `requires` that
// makes the round trip exact; a caller using these primitives directly owns
// that obligation itself.
procedure $intToBv1(x: int) : bv 1 external;
procedure $bv1ToInt(b: bv 1) : int external;
procedure $bv1ToUInt(b: bv 1) : int external;
procedure $intToBv8(x: int) : bv 8 external;
procedure $bv8ToInt(b: bv 8) : int external;
procedure $bv8ToUInt(b: bv 8) : int external;
procedure $intToBv16(x: int) : bv 16 external;
procedure $bv16ToInt(b: bv 16) : int external;
procedure $bv16ToUInt(b: bv 16) : int external;
procedure $intToBv32(x: int) : bv 32 external;
procedure $bv32ToInt(b: bv 32) : int external;
procedure $bv32ToUInt(b: bv 32) : int external;
procedure $intToBv64(x: int) : bv 64 external;
procedure $bv64ToInt(b: bv 64) : int external;
procedure $bv64ToUInt(b: bv 64) : int external;
procedure $intToBv128(x: int) : bv 128 external;
procedure $bv128ToInt(b: bv 128) : int external;
procedure $bv128ToUInt(b: bv 128) : int external;

procedure $bv1And(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1Or(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1Xor(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1Shl(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1UShr(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1SShr(x: bv 1, y: bv 1) : bv 1 external;
procedure $bv1Not(x: bv 1) : bv 1 external;
procedure $bv8And(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8Or(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8Xor(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8Shl(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8UShr(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8SShr(x: bv 8, y: bv 8) : bv 8 external;
procedure $bv8Not(x: bv 8) : bv 8 external;
procedure $bv16And(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16Or(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16Xor(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16Shl(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16UShr(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16SShr(x: bv 16, y: bv 16) : bv 16 external;
procedure $bv16Not(x: bv 16) : bv 16 external;
procedure $bv32And(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32Or(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32Xor(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32Shl(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32UShr(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32SShr(x: bv 32, y: bv 32) : bv 32 external;
procedure $bv32Not(x: bv 32) : bv 32 external;
procedure $bv64And(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64Or(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64Xor(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64Shl(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64UShr(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64SShr(x: bv 64, y: bv 64) : bv 64 external;
procedure $bv64Not(x: bv 64) : bv 64 external;
procedure $bv128And(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128Or(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128Xor(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128Shl(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128UShr(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128SShr(x: bv 128, y: bv 128) : bv 128 external;
procedure $bv128Not(x: bv 128) : bv 128 external;

// Boolean operations
procedure $boolNot(x: bool) : bool external;
procedure $boolAnd(x: bool, y: bool) : bool external;
procedure $boolOr(x: bool, y: bool) : bool external;
procedure $boolImplies(x: bool, y: bool) : bool external;

// String ordering. Core has exactly TWO ordering operators on `string`
// (`Str.Lt`, `Str.Le` — `Factory.lean`), both lowered to the SMT string theory's
// `str.<` / `str.<=`, i.e. the lexicographic order over code-point sequences.
// There is no `Str.Gt`/`Str.Ge`, so the `$gt`/`$ge` string overloads below are
// defined by SWAPPING the operands rather than by a third and fourth delegate:
// `x > y` is `y < x` and `x >= y` is `y <= x`. That identity is exact for a total
// order, which `str.<` is (`Fundamentals/StringOrdering.lean` pins totality,
// irreflexivity and antisymmetry over symbolic operands, so the swap is not
// taken on faith).
procedure $strLt(x: string, y: string) : bool external;
procedure $strLe(x: string, y: string) : bool external;

// --- Integer bitwise operations, as width- and signedness-explicit procedures ---
//
// These are the bounded-integer surface. They are PROCEDURES, not operator
// overloads, and deliberately so: `&`, `|` and `^` already have Laurel meanings
// (`$and` and `$or` at `bool`, `$strConcat` at `string`), and an `int` overload
// of `&` could carry no width, while a bitwise operation on a bounded integer
// needs one. A spelling that silently picked a width would be exactly the quiet
// semantic choice these names avoid.
//
// Semantics. `$bit<Op><Sign><W>(x, y)` is the two's-complement bitwise <Op> of
// `x` and `y` at width `W`, read back SIGNED (`S`) or UNSIGNED (`U`). The
// `requires` pins the operands to the width's range, which is what makes the
// `$intToBv<W>` round trip exact rather than truncating; a caller outside that
// range is REJECTED, not wrapped.
//
// There is no overflow question: a bitwise and/or/xor of two values in a width's
// range is itself in that range, so unlike `+`/`*` these carry no overflow
// obligation and no wraparound. The `ensures`-free contract is deliberate --
// the range of the result follows from the encoding (`$bv<W>ToUInt`'s result is
// in `[0, 2^W)` by its sort, and the signed form re-centres that interval with
// arithmetic), so a caller gets it without the prelude asserting it.
//
// The signed forms do NOT use `$bv<W>ToInt`. Measured: `sbv_to_int` at width 32
// and above is a solver cliff for cvc5 1.3.4 -- even the FALSE property
// `sbv_to_int(b) >= 0` times out at 60 s rather than yielding a countermodel,
// and the true lower bound `sbv_to_int(b) >= -2^31` times out in three different
// phrasings. `ubv_to_int` has no such problem in either direction. So the signed
// value is recovered from the UNSIGNED one by re-centring:
//
//     s = ((u + 2^(W-1)) mod 2^W) - 2^(W-1)
//
// which is exact (`mod` here is `Int.Mod`, Euclidean, so non-negative for a
// positive modulus) and whose range is an arithmetic consequence the solver
// discharges. `$intMod` is called directly rather than through `%` so the
// literal modulus does not add a `divisor is non-zero` obligation to every
// program that uses a bitwise operation.
//
// NOT provided, each because it needs no primitive:
//   * complement -- `-x - 1` signed, `2^W - 1 - x` unsigned. Pure arithmetic.
//   * AND-NOT -- `$bitAnd...(x, <complement of y>)` with the above.
//   * `x >> k` and `x << k` for a CONSTANT k -- `x / 2^k` (Laurel's `/` is floor
//     division for a positive divisor, matching arithmetic shift right) and
//     `x * 2^k`. Keeping `<<` as a multiplication is what preserves the
//     "overflow is a reported obligation, not wraparound" posture; a bitvector
//     `<<` WRAPS (`$bv8Shl` of 128 by 1 is 0, measured), which is a different
//     semantics and is not silently substituted here.
//   * `x >> s` for a VARIABLE s -- composable from `$bv<W>SShr`/`$bv<W>UShr` and
//     the conversions above, including `2^s` itself as `$bv<W>Shl` of 1 by s.
//     Left to the caller because the shift amount's own range obligation and
//     the semantics for `s >= W` are front-end decisions.

procedure $bitAndU8(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint8"
  requires x <= 255 summary "left operand fits uint8"
  requires y >= 0 summary "right operand fits uint8"
  requires y <= 255 summary "right operand fits uint8"
  return $bv8ToUInt($bv8And($intToBv8(x), $intToBv8(y)));
procedure $bitAndS8(x: int, y: int) : int
  requires x >= -128 summary "left operand fits int8"
  requires x <= 127 summary "left operand fits int8"
  requires y >= -128 summary "right operand fits int8"
  requires y <= 127 summary "right operand fits int8"
  return $intMod($bv8ToUInt($bv8And($intToBv8(x), $intToBv8(y))) + 128, 256) - 128;

procedure $bitOrU8(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint8"
  requires x <= 255 summary "left operand fits uint8"
  requires y >= 0 summary "right operand fits uint8"
  requires y <= 255 summary "right operand fits uint8"
  return $bv8ToUInt($bv8Or($intToBv8(x), $intToBv8(y)));
procedure $bitOrS8(x: int, y: int) : int
  requires x >= -128 summary "left operand fits int8"
  requires x <= 127 summary "left operand fits int8"
  requires y >= -128 summary "right operand fits int8"
  requires y <= 127 summary "right operand fits int8"
  return $intMod($bv8ToUInt($bv8Or($intToBv8(x), $intToBv8(y))) + 128, 256) - 128;

procedure $bitXorU8(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint8"
  requires x <= 255 summary "left operand fits uint8"
  requires y >= 0 summary "right operand fits uint8"
  requires y <= 255 summary "right operand fits uint8"
  return $bv8ToUInt($bv8Xor($intToBv8(x), $intToBv8(y)));
procedure $bitXorS8(x: int, y: int) : int
  requires x >= -128 summary "left operand fits int8"
  requires x <= 127 summary "left operand fits int8"
  requires y >= -128 summary "right operand fits int8"
  requires y <= 127 summary "right operand fits int8"
  return $intMod($bv8ToUInt($bv8Xor($intToBv8(x), $intToBv8(y))) + 128, 256) - 128;

procedure $bitAndU16(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint16"
  requires x <= 65535 summary "left operand fits uint16"
  requires y >= 0 summary "right operand fits uint16"
  requires y <= 65535 summary "right operand fits uint16"
  return $bv16ToUInt($bv16And($intToBv16(x), $intToBv16(y)));
procedure $bitAndS16(x: int, y: int) : int
  requires x >= -32768 summary "left operand fits int16"
  requires x <= 32767 summary "left operand fits int16"
  requires y >= -32768 summary "right operand fits int16"
  requires y <= 32767 summary "right operand fits int16"
  return $intMod($bv16ToUInt($bv16And($intToBv16(x), $intToBv16(y))) + 32768, 65536) - 32768;

procedure $bitOrU16(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint16"
  requires x <= 65535 summary "left operand fits uint16"
  requires y >= 0 summary "right operand fits uint16"
  requires y <= 65535 summary "right operand fits uint16"
  return $bv16ToUInt($bv16Or($intToBv16(x), $intToBv16(y)));
procedure $bitOrS16(x: int, y: int) : int
  requires x >= -32768 summary "left operand fits int16"
  requires x <= 32767 summary "left operand fits int16"
  requires y >= -32768 summary "right operand fits int16"
  requires y <= 32767 summary "right operand fits int16"
  return $intMod($bv16ToUInt($bv16Or($intToBv16(x), $intToBv16(y))) + 32768, 65536) - 32768;

procedure $bitXorU16(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint16"
  requires x <= 65535 summary "left operand fits uint16"
  requires y >= 0 summary "right operand fits uint16"
  requires y <= 65535 summary "right operand fits uint16"
  return $bv16ToUInt($bv16Xor($intToBv16(x), $intToBv16(y)));
procedure $bitXorS16(x: int, y: int) : int
  requires x >= -32768 summary "left operand fits int16"
  requires x <= 32767 summary "left operand fits int16"
  requires y >= -32768 summary "right operand fits int16"
  requires y <= 32767 summary "right operand fits int16"
  return $intMod($bv16ToUInt($bv16Xor($intToBv16(x), $intToBv16(y))) + 32768, 65536) - 32768;

procedure $bitAndU32(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint32"
  requires x <= 4294967295 summary "left operand fits uint32"
  requires y >= 0 summary "right operand fits uint32"
  requires y <= 4294967295 summary "right operand fits uint32"
  return $bv32ToUInt($bv32And($intToBv32(x), $intToBv32(y)));
procedure $bitAndS32(x: int, y: int) : int
  requires x >= -2147483648 summary "left operand fits int32"
  requires x <= 2147483647 summary "left operand fits int32"
  requires y >= -2147483648 summary "right operand fits int32"
  requires y <= 2147483647 summary "right operand fits int32"
  return $intMod($bv32ToUInt($bv32And($intToBv32(x), $intToBv32(y))) + 2147483648, 4294967296) - 2147483648;

procedure $bitOrU32(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint32"
  requires x <= 4294967295 summary "left operand fits uint32"
  requires y >= 0 summary "right operand fits uint32"
  requires y <= 4294967295 summary "right operand fits uint32"
  return $bv32ToUInt($bv32Or($intToBv32(x), $intToBv32(y)));
procedure $bitOrS32(x: int, y: int) : int
  requires x >= -2147483648 summary "left operand fits int32"
  requires x <= 2147483647 summary "left operand fits int32"
  requires y >= -2147483648 summary "right operand fits int32"
  requires y <= 2147483647 summary "right operand fits int32"
  return $intMod($bv32ToUInt($bv32Or($intToBv32(x), $intToBv32(y))) + 2147483648, 4294967296) - 2147483648;

procedure $bitXorU32(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint32"
  requires x <= 4294967295 summary "left operand fits uint32"
  requires y >= 0 summary "right operand fits uint32"
  requires y <= 4294967295 summary "right operand fits uint32"
  return $bv32ToUInt($bv32Xor($intToBv32(x), $intToBv32(y)));
procedure $bitXorS32(x: int, y: int) : int
  requires x >= -2147483648 summary "left operand fits int32"
  requires x <= 2147483647 summary "left operand fits int32"
  requires y >= -2147483648 summary "right operand fits int32"
  requires y <= 2147483647 summary "right operand fits int32"
  return $intMod($bv32ToUInt($bv32Xor($intToBv32(x), $intToBv32(y))) + 2147483648, 4294967296) - 2147483648;

procedure $bitAndU64(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint64"
  requires x <= 18446744073709551615 summary "left operand fits uint64"
  requires y >= 0 summary "right operand fits uint64"
  requires y <= 18446744073709551615 summary "right operand fits uint64"
  return $bv64ToUInt($bv64And($intToBv64(x), $intToBv64(y)));
procedure $bitAndS64(x: int, y: int) : int
  requires x >= -9223372036854775808 summary "left operand fits int64"
  requires x <= 9223372036854775807 summary "left operand fits int64"
  requires y >= -9223372036854775808 summary "right operand fits int64"
  requires y <= 9223372036854775807 summary "right operand fits int64"
  return $intMod($bv64ToUInt($bv64And($intToBv64(x), $intToBv64(y))) + 9223372036854775808, 18446744073709551616) - 9223372036854775808;

procedure $bitOrU64(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint64"
  requires x <= 18446744073709551615 summary "left operand fits uint64"
  requires y >= 0 summary "right operand fits uint64"
  requires y <= 18446744073709551615 summary "right operand fits uint64"
  return $bv64ToUInt($bv64Or($intToBv64(x), $intToBv64(y)));
procedure $bitOrS64(x: int, y: int) : int
  requires x >= -9223372036854775808 summary "left operand fits int64"
  requires x <= 9223372036854775807 summary "left operand fits int64"
  requires y >= -9223372036854775808 summary "right operand fits int64"
  requires y <= 9223372036854775807 summary "right operand fits int64"
  return $intMod($bv64ToUInt($bv64Or($intToBv64(x), $intToBv64(y))) + 9223372036854775808, 18446744073709551616) - 9223372036854775808;

procedure $bitXorU64(x: int, y: int) : int
  requires x >= 0 summary "left operand fits uint64"
  requires x <= 18446744073709551615 summary "left operand fits uint64"
  requires y >= 0 summary "right operand fits uint64"
  requires y <= 18446744073709551615 summary "right operand fits uint64"
  return $bv64ToUInt($bv64Xor($intToBv64(x), $intToBv64(y)));
procedure $bitXorS64(x: int, y: int) : int
  requires x >= -9223372036854775808 summary "left operand fits int64"
  requires x <= 9223372036854775807 summary "left operand fits int64"
  requires y >= -9223372036854775808 summary "right operand fits int64"
  requires y <= 9223372036854775807 summary "right operand fits int64"
  return $intMod($bv64ToUInt($bv64Xor($intToBv64(x), $intToBv64(y))) + 9223372036854775808, 18446744073709551616) - 9223372036854775808;

// Short-circuit boolean operations, string concatenation and equality have no
// separate delegate: the operator wrapper's own reserved name (`$andThen`,
// `$orElse`, `$strConcat`, `$eq`, `$neq`) is already the name
// `LaurelToCoreSchemaPass` recognizes, so they are declared `external` at the
// wrapper site below rather than delegated to a second procedure.

// --- Overloaded operator wrappers ($ prefix = reserved namespace) ---
// The parser emits StaticCall "$add" for "+", etc. Resolution picks the overload.

// Arithmetic (int overload)
procedure $add(x: int, y: int) : int
  return $intAdd(x, y);
procedure $sub(x: int, y: int) : int
  return $intSub(x, y);
procedure $mul(x: int, y: int) : int
  return $intMul(x, y);
procedure $div(x: int, y: int) : int
  requires y != 0 summary "divisor is non-zero"
  return $intSafeDiv(x, y);
procedure $mod(x: int, y: int) : int
  requires y != 0 summary "modulus is non-zero"
  return $intSafeMod(x, y);
procedure $divT(x: int, y: int) : int
  requires y != 0 summary "divisor is non-zero"
  return $intSafeDivT(x, y);
procedure $modT(x: int, y: int) : int
  requires y != 0 summary "modulus is non-zero"
  return $intSafeModT(x, y);
procedure $neg(x: int) : int
  return $intNeg(x);

// Arithmetic (real overload)
procedure $add(x: real, y: real) : real
  return $realAdd(x, y);
procedure $sub(x: real, y: real) : real
  return $realSub(x, y);
procedure $mul(x: real, y: real) : real
  return $realMul(x, y);
procedure $div(x: real, y: real) : real
  return $realDiv(x, y);
procedure $neg(x: real) : real
  return $realNeg(x);

// Comparisons (int overload)
procedure $lt(x: int, y: int) : bool
  return $intLt(x, y);
procedure $le(x: int, y: int) : bool
  return $intLe(x, y);
procedure $gt(x: int, y: int) : bool
  return $intGt(x, y);
procedure $ge(x: int, y: int) : bool
  return $intGe(x, y);

// Comparisons (real overload)
procedure $lt(x: real, y: real) : bool
  return $realLt(x, y);
procedure $le(x: real, y: real) : bool
  return $realLe(x, y);
procedure $gt(x: real, y: real) : bool
  return $realGt(x, y);
procedure $ge(x: real, y: real) : bool
  return $realGe(x, y);

// Comparisons (bitvector overloads, one per Core-supported width — see the
// `bv*S*` externals above for why these are per-width and signed).
procedure $lt(x: bv 1, y: bv 1) : bool
  return $bv1SLt(x, y);
procedure $le(x: bv 1, y: bv 1) : bool
  return $bv1SLe(x, y);
procedure $gt(x: bv 1, y: bv 1) : bool
  return $bv1SGt(x, y);
procedure $ge(x: bv 1, y: bv 1) : bool
  return $bv1SGe(x, y);
procedure $lt(x: bv 8, y: bv 8) : bool
  return $bv8SLt(x, y);
procedure $le(x: bv 8, y: bv 8) : bool
  return $bv8SLe(x, y);
procedure $gt(x: bv 8, y: bv 8) : bool
  return $bv8SGt(x, y);
procedure $ge(x: bv 8, y: bv 8) : bool
  return $bv8SGe(x, y);
procedure $lt(x: bv 16, y: bv 16) : bool
  return $bv16SLt(x, y);
procedure $le(x: bv 16, y: bv 16) : bool
  return $bv16SLe(x, y);
procedure $gt(x: bv 16, y: bv 16) : bool
  return $bv16SGt(x, y);
procedure $ge(x: bv 16, y: bv 16) : bool
  return $bv16SGe(x, y);
procedure $lt(x: bv 32, y: bv 32) : bool
  return $bv32SLt(x, y);
procedure $le(x: bv 32, y: bv 32) : bool
  return $bv32SLe(x, y);
procedure $gt(x: bv 32, y: bv 32) : bool
  return $bv32SGt(x, y);
procedure $ge(x: bv 32, y: bv 32) : bool
  return $bv32SGe(x, y);
procedure $lt(x: bv 64, y: bv 64) : bool
  return $bv64SLt(x, y);
procedure $le(x: bv 64, y: bv 64) : bool
  return $bv64SLe(x, y);
procedure $gt(x: bv 64, y: bv 64) : bool
  return $bv64SGt(x, y);
procedure $ge(x: bv 64, y: bv 64) : bool
  return $bv64SGe(x, y);

// Comparisons (string overload) — lexicographic over code points, see `$strLt`.
//
// Adding these four cannot make an existing `$lt`/`$le`/`$gt`/`$ge` call site
// ambiguous: overload selection is by operand type, and `string` is disjoint from
// `int`, `real` and every `bv n`. The one call shape that *is* ambiguous — both
// before and after — is a comparison whose operands have a TYPE VARIABLE type
// (`a > b` on `a: T`), because a type variable selects no overload at all; that is
// a pre-existing property of the overload set, not something this adds.
procedure $lt(x: string, y: string) : bool
  return $strLt(x, y);
procedure $le(x: string, y: string) : bool
  return $strLe(x, y);
procedure $gt(x: string, y: string) : bool
  return $strLt(y, x);
procedure $ge(x: string, y: string) : bool
  return $strLe(y, x);

// Boolean
procedure $not(x: bool) : bool
  return $boolNot(x);
procedure $and(x: bool, y: bool) : bool
  return $boolAnd(x, y);
procedure $or(x: bool, y: bool) : bool
  return $boolOr(x, y);
procedure $implies(x: bool, y: bool) : bool
  return $boolImplies(x, y);
procedure $andThen(x: bool, y: bool) : bool external;
procedure $orElse(x: bool, y: bool) : bool external;

// Equality. `T` binds from the operands at each call site, so `1 == true` is a type error.
// These stay `external`: a transparent body would carry this signature into Core and fail to
// unify against `Composite`, `$Box`, `bool`, … , whereas `LaurelToCoreSchemaPass` lowers the
// wrapper straight to Core's polymorphic equality, which is what holds at every type. The
// generic signature is a resolution-time device and gives no such single definition —
// composites monomorphize per instantiation, poly type variables freshen per call site.
// `Synth.staticCall` additionally guards the operand SHAPES (`MultiValuedExpr`, `TVoid`) and
// phrases a type-argument conflict as `==`/`!=`, neither of which a signature can state.
procedure $eq<T>(x: T, y: T) : bool external;
procedure $neq<T>(x: T, y: T) : bool external;

// String
procedure $strConcat(x: string, y: string) : string external;

// Havoc the entire heap: a bodiless `opaque modifies *` procedure whose
// `modifies *` lets the heap change arbitrarily while its monotonic-counter
// postcondition still holds across the change. Emitted to model an arbitrary
// environment step on the heap.
procedure $havocHeap()
  opaque
  modifies *;

#end

/--
The core map operation definitions as a `Laurel.Program`, parsed at compile time.
-/
public def coreDefinitionsForLaurel : Program :=
  match TransM.run
      (.file "StrataLaurel/Implementation/CoreDefinitionsForLaurel.lean")
      (parseProgram coreDefinitionsForLaurelDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: CoreDefinitionsForLaurel parse error: {e}"; default

/--
The generic `Result<Val, Err>` datatype that the exceptional-channel lowering
targets. `EliminateExceptions` injects it into a program's types *only* when the
program uses exceptions (a `throws` procedure, a `throw`, or a call to a throwing
procedure), so a program that never throws does not carry it. It is a plain
datatype (free for SMT), so it does not perturb heap reasoning.
-/
def resultDefinitionsDDM :=
#strata
program Laurel;

datatype Result<Val, Err> {
  Good(value: Val),
  Bad(err: Err)
}

#end

/-- The `Result` datatype definition as a `Laurel.Program`, parsed at compile time. -/
def resultDefinitions : Program :=
  match TransM.run
      (.file "StrataLaurel/Implementation/CoreDefinitionsForLaurel.lean")
      (parseProgram resultDefinitionsDDM) (synthesized := true) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: resultDefinitions parse error: {e}"; default

/-- Whether the shared names in `LaurelAST` (`exnResultDatatypeName` and friends)
    still describe the datatype defined above.

    The definition is DDM source, so it cannot be built from those names; this
    checks the other direction instead. `EliminateExceptions` builds the encoding
    and `ModifiesClauses` consumes it, both through the shared names, so a rename
    in the source above that is not mirrored there would desync them — with no
    build failure, since every spelling is just a string.

    Pinned by a `#guard` in `StrataTest/.../UnitTests/ExceptionResultNamesTest.lean`
    rather than here: this module cannot evaluate it at elaboration time, because
    `resultDefinitions` runs the DDM parser, whose IR is not available to the
    interpreter while this library is still being compiled. -/
def resultDefinitionsMatchSharedNames : Bool :=
  match resultDefinitions.types.filterMap
      (fun t => match t with | .Datatype dt => some dt | _ => none) with
  | [dt] =>
      dt.name.text == exnResultDatatypeName
        && dt.constructors.map (fun c => c.name.text)
             == [exnResultGoodCtor, exnResultBadCtor]
        && dt.constructors.flatMap (fun c => c.args.map (fun a => a.name.text))
             == [exnResultValueField, exnResultErrField]
        -- The member names the passes use must be the ones resolution will
        -- generate for this datatype's own constructors and fields.
        && dt.constructors.map dt.testerName == [exnResultIsGood, exnResultIsBad]
        && dt.constructors.flatMap (fun c => c.args.map dt.destructorName)
             == [exnResultValue, exnResultErr]
  | _ => false

/-- The datatype's *own* names, labelled and in the order
    `resultDefinitionsMatchSharedNames` compares them.

    Exposed so a test can pin the concrete strings rather than only a single boolean.
    When a rename desyncs the DDM source above from the shared names in `LaurelAST`,
    a golden over this list names the aspect that moved; `#guard` on the boolean can
    only report that something did. -/
def resultDefinitionNames : List (String × String) :=
  match resultDefinitions.types.filterMap
      (fun t => match t with | .Datatype dt => some dt | _ => none) with
  | [dt] =>
      [ ("datatype",     dt.name.text),
        ("constructors", ", ".intercalate (dt.constructors.map (fun c => c.name.text))),
        ("fields",       ", ".intercalate
                           (dt.constructors.flatMap (fun c => c.args.map (fun a => a.name.text)))),
        ("testers",      ", ".intercalate (dt.constructors.map dt.testerName)),
        ("destructors",  ", ".intercalate
                           (dt.constructors.flatMap (fun c => c.args.map dt.destructorName))) ]
  | _ => [("error", "expected exactly one datatype in resultDefinitions")]

end -- public section

end Strata.Laurel

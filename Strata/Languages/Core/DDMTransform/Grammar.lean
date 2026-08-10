/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/- NOTE: This grammar is the source of truth for Core.st syntax. If you change
   keywords, operators, types, or built-in functions here, regenerate the
   editor syntax files by running:
     lake env lean --run editors/GenSyntax.lean all
-/
module

public import StrataDDM.HNF
public import StrataDDM.Integration.Lean.OfAstM
import StrataDDM.Integration.Lean -- shake: keep

---------------------------------------------------------------------
public section
namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

-- Sequence operations and lambda/application syntax increase the grammar size enough
-- to require higher recursion and heartbeat limits.
set_option maxRecDepth 20000
set_option maxHeartbeats 400000

/- DDM support for parsing and pretty-printing Strata Core -/

#dialect
dialect Core;

// Core runs its own type inference (`LExpr.resolve`), so DDM's type checker
// is skipped here. Implicit type-parameter slots are left as placeholders for
// `resolve` to fill from the arguments.
dialect_option typecheck off;

// ═══════════════════════════════════════════════════════════════════
// TYPES & BINDING
// ═══════════════════════════════════════════════════════════════════

// ---- Metadata annotations: @[key, key = value, ...] ----
category MetadataAnnValue;
op mdAnnValStr (s : Str) : MetadataAnnValue => s;
op mdAnnValExpr (e : Expr) : MetadataAnnValue => "(" e ")";

category MetadataAnnKey;
op mdAnnKeyBare (name : Ident) : MetadataAnnKey => name;
op mdAnnKeyPrefixed (dialect : Ident, name : Ident) : MetadataAnnKey =>
  dialect "." name;

category MetadataAnnEntry;
op mdAnnFlag (key : MetadataAnnKey) : MetadataAnnEntry => key;
op mdAnnKV (key : MetadataAnnKey, value : MetadataAnnValue) : MetadataAnnEntry =>
  key " = " value;

category MetadataAnn;
op mdAnn (entries : CommaSepBy MetadataAnnEntry) : MetadataAnn => "@[" entries "] ";

// Declare Strata Core-specific metadata for datatype declarations
metadata declareDatatype (name : Ident, typeParams : Ident,
constructors : Ident, testerTemplate : FunctionTemplate,
accessorTemplate : FunctionTemplate,
unsafeAccessorTemplate : FunctionTemplate);

// ---- Types ----
type bool;
type int;
type string;
type regex;
type real;
// A bitvector type is `bv W`, where `W` is a width marker `W1 … W128`; a
// concrete type is written `bv W8`. Widths are types (not numbers) because a
// type-declaration parameter must be a type. The width marker is only valid as
// the argument to `bv`: `translateLMonoTy` maps `bv W8` to a width-8 bitvector
// and rejects a bare marker. Operators are polymorphic in `W` (see the wrappers
// below), so each family is one op over `bv W` rather than one per width.
type bv (n : Type);
type W1;
type W8;
type W16;
type W32;
type W64;
type W128;
type Map (dom : Type, range : Type);
type Sequence (elem : Type);

// ---- Type variables and binders ----
category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

category Bind;
@[declare(v, tp)]
op bind_mk (v : Ident, targs : Option TypeArgs, @[scope(targs)] tp : Type) : Bind =>
  v " : " targs tp;

category DeclList;
@[scope(b)]
op declAtom (b : Bind) : DeclList => b;
@[scope(b)]
op declPush (dl : DeclList, @[scope(dl)] b : Bind) : DeclList => dl:0 ", " b:0;

category MonoBind;
@[declare(v, tp)]
op mono_bind_mk (v : Ident, tp : Type) : MonoBind =>
  v " : " tp;

category MonoDeclList;
@[scope(b)]
op monoDeclAtom (b : MonoBind) : MonoDeclList => b;
@[scope(b)]
op monoDeclPush (dl : MonoDeclList, @[scope(dl)] b : MonoBind) : MonoDeclList =>
  dl:0 ", " b:0;

// ═══════════════════════════════════════════════════════════════════
// EXPRESSIONS
// ═══════════════════════════════════════════════════════════════════

// ---- Numeric literals ----
fn natToInt (n : Num) : int => n;
fn bv1Lit (n : Num) : bv W1 => "bv{1}" "(" n ")";
fn bv8Lit (n : Num) : bv W8 => "bv{8}" "(" n ")";
fn bv16Lit (n : Num) : bv W16 => "bv{16}" "(" n ")";
fn bv32Lit (n : Num) : bv W32 => "bv{32}" "(" n ")";
fn bv64Lit (n : Num) : bv W64 => "bv{64}" "(" n ")";
fn bv128Lit (n : Num) : bv W128 => "bv{128}" "(" n ")";

// ---- int -> bitvector casts ----
// One fn per width: the result width has no operand to infer it from, so it is
// fixed by the fn rather than a polymorphic `W`.
fn as_bv1   (e : int) : bv W1   => "as_bv1"   "(" e ")";
fn as_bv8   (e : int) : bv W8   => "as_bv8"   "(" e ")";
fn as_bv16  (e : int) : bv W16  => "as_bv16"  "(" e ")";
fn as_bv32  (e : int) : bv W32  => "as_bv32"  "(" e ")";
fn as_bv64  (e : int) : bv W64  => "as_bv64"  "(" e ")";
fn as_bv128 (e : int) : bv W128 => "as_bv128" "(" e ")";
// ---- String and real literals ----
fn strLit (s : Str) : string => s;
fn realLit (d : Decimal) : real => d;
// Exact rational literal `frac{num, den}`, used to print reals whose value has
// no terminating decimal representation (e.g. `1/3`). The leading token is
// `frac{` (containing `{`, like the `bv{N}` literals) rather than a bare `frac`
// keyword, so `frac` stays a valid identifier and does not collide with a
// user-declared function named `frac`. The brace form also avoids a collision
// with `safediv_expr`, which owns the infix `/` token.
fn fracLit (num : Num, den : Num) : real => "frac{" num ", " den "}";

// ---- Conditional and old-state ----
fn if (tp : Type, c : bool, t : tp, f : tp) : tp => @[prec(2)] "if " c:0 " then " t:0 " else " f:0;

fn old (tp : Type, v : tp) : tp => "old " v;

// ---- Maps ----
fn map_get (K : Type, V : Type, m : Map K V, k : K) : V => m "[" k "]";
fn map_set (K : Type, V : Type, m : Map K V, k : K, v : V) : Map K V =>
  m "[" k ":=" v "]";
// map_const uses explicit key-type annotation syntax: the key type cannot be
// inferred from the single value argument, so it is written `mapConst<K>(v)`.
// The value type V is inferred from `v`.
fn map_const (K : Type, V : Type, v : V) : Map K V => "mapConst" "<" K ">" "(" v ")";

// ---- Sequences ----
// seq_empty uses explicit type annotation syntax since there are no value
// arguments to infer the type parameter from.
fn seq_empty (A : Type) : Sequence A => "Sequence.empty" "<" A ">" "(" ")";
fn seq_length (A : Type, s : Sequence A) : int => "Sequence.length" "(" s ")";
fn seq_select (A : Type, s : Sequence A, i : int) : A => "Sequence.select" "(" s ", " i ")";
fn seq_append (A : Type, s1 : Sequence A, s2 : Sequence A) : Sequence A =>
  "Sequence.append" "(" s1 ", " s2 ")";
fn seq_build (A : Type, s : Sequence A, v : A) : Sequence A =>
  "Sequence.build" "(" s ", " v ")";
fn seq_update (A : Type, s : Sequence A, i : int, v : A) : Sequence A =>
  "Sequence.update" "(" s ", " i ", " v ")";
fn seq_contains (A : Type, s : Sequence A, v : A) : bool =>
  "Sequence.contains" "(" s ", " v ")";
fn seq_take (A : Type, s : Sequence A, n : int) : Sequence A =>
  "Sequence.take" "(" s ", " n ")";
fn seq_drop (A : Type, s : Sequence A, n : int) : Sequence A =>
  "Sequence.drop" "(" s ", " n ")";

// ---- Strings ----
// FIXME: Define polymorphic length and concat functions?
fn str_len (a : string) : int => "str.len" "(" a  ")";
fn str_concat (a : string, b : string) : string => "str.concat" "(" a ", " b ")";
fn str_substr (a : string, i : int, n : int) : string => "str.substr" "(" a ", " i ", " n ")";
fn str_toregex (a : string) : regex => "str.to.re" "(" a ")";
fn str_inregex (s : string, a : regex) : bool => "str.in.re" "(" s ", " a ")";
fn str_prefixof (s : string, t : string) : bool => "str.prefixof" "(" s ", " t ")";
fn str_suffixof (s : string, t : string) : bool => "str.suffixof" "(" s ", " t ")";
fn str_contains (s : string, t : string) : bool => "str.contains" "(" s ", " t ")";
fn str_indexof (s : string, t : string, i : int) : int => "str.indexof" "(" s ", " t ", " i ")";
fn str_replace (s : string, t : string, u : string) : string => "str.replace" "(" s ", " t ", " u ")";
fn str_at (s : string, i : int) : string => "str.at" "(" s ", " i ")";
fn str_lt (s : string, t : string) : bool => "str.lt" "(" s ", " t ")";
fn str_le (s : string, t : string) : bool => "str.le" "(" s ", " t ")";
// ---- Regexes ----
fn re_allchar () : regex => "re.allchar" "(" ")";
fn re_all () : regex => "re.all" "(" ")";
fn re_range (s1 : string, s2 : string) : regex => "re.range" "(" s1 ", " s2 ")";
fn re_concat (r1 : regex, r2 : regex) : regex => "re.concat" "(" r1 ", " r2 ")";
fn re_star (r : regex) : regex => "re.*" "(" r ")";
fn re_plus (r : regex) : regex => "re.+" "(" r ")";
fn re_loop (r : regex, i : int, j : int) : regex => "re.loop" "(" r ", " i ", " j")";
fn re_union (r1 : regex, r2 : regex) : regex => "re.union" "(" r1 ", " r2 ")";
fn re_inter (r1 : regex, r2 : regex) : regex => "re.inter" "(" r1 ", " r2 ")";
fn re_comp (r : regex) : regex => "re.comp" "(" r ")";
fn re_none () : regex => "re.none" "(" ")";

// ---- Booleans ----
fn btrue : bool => "true";
fn bfalse : bool => "false";
fn not (b : bool) : bool => "!" b;
fn equiv (a : bool, b : bool) : bool => @[prec(4)] a " <==> " b;
fn implies (a : bool, b : bool) : bool => @[prec(5), rightassoc] a " ==> " b;
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a " && " b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a " || " b;

// ---- Equality ----
fn equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " != " b;

// ---- UnaryArithInt ----
category UnaryArithInt;
op int_neg : UnaryArithInt => "int.neg";
fn unaryArithInt (f : UnaryArithInt, a : int) : int => f "(" a ")";

// ---- UnaryArithReal ----
category UnaryArithReal;
op real_neg : UnaryArithReal => "real.neg";
fn unaryArithReal (f : UnaryArithReal, a : real) : real => f "(" a ")";

// ---- UnaryArithBv (width-polymorphic: a : bv W -> bv W) ----
category UnaryArithBv;
op bv1_neg : UnaryArithBv => "bv1.neg";
op bv1_not : UnaryArithBv => "bv1.not";
op bv8_neg : UnaryArithBv => "bv8.neg";
op bv8_not : UnaryArithBv => "bv8.not";
op bv16_neg : UnaryArithBv => "bv16.neg";
op bv16_not : UnaryArithBv => "bv16.not";
op bv32_neg : UnaryArithBv => "bv32.neg";
op bv32_not : UnaryArithBv => "bv32.not";
op bv64_neg : UnaryArithBv => "bv64.neg";
op bv128_neg : UnaryArithBv => "bv128.neg";
op bv64_not : UnaryArithBv => "bv64.not";
op bv128_not : UnaryArithBv => "bv128.not";
fn unaryArithBv (W : Type, f : UnaryArithBv, a : bv W) : bv W => f "(" a ")";

// ---- UnarySafeBv (width-polymorphic) ----
category UnarySafeBv;
op bv1_safeNeg : UnarySafeBv => "bv1.safeNeg";
op bv1_safeUNeg : UnarySafeBv => "bv1.safeUNeg";
op bv8_safeNeg : UnarySafeBv => "bv8.safeNeg";
op bv8_safeUNeg : UnarySafeBv => "bv8.safeUNeg";
op bv16_safeNeg : UnarySafeBv => "bv16.safeNeg";
op bv16_safeUNeg : UnarySafeBv => "bv16.safeUNeg";
op bv32_safeNeg : UnarySafeBv => "bv32.safeNeg";
op bv32_safeUNeg : UnarySafeBv => "bv32.safeUNeg";
op bv64_safeNeg : UnarySafeBv => "bv64.safeNeg";
op bv128_safeNeg : UnarySafeBv => "bv128.safeNeg";
op bv64_safeUNeg : UnarySafeBv => "bv64.safeUNeg";
op bv128_safeUNeg : UnarySafeBv => "bv128.safeUNeg";
fn unarySafeBv (W : Type, f : UnarySafeBv, a : bv W) : bv W => f "(" a ")";

// ---- UnaryOverflowBv (width-polymorphic: a : bv W -> bool) ----
category UnaryOverflowBv;
op bv1_sNegOverflow : UnaryOverflowBv => "bv1.sNegOverflow";
op bv1_uNegOverflow : UnaryOverflowBv => "bv1.uNegOverflow";
op bv8_sNegOverflow : UnaryOverflowBv => "bv8.sNegOverflow";
op bv8_uNegOverflow : UnaryOverflowBv => "bv8.uNegOverflow";
op bv16_sNegOverflow : UnaryOverflowBv => "bv16.sNegOverflow";
op bv16_uNegOverflow : UnaryOverflowBv => "bv16.uNegOverflow";
op bv32_sNegOverflow : UnaryOverflowBv => "bv32.sNegOverflow";
op bv32_uNegOverflow : UnaryOverflowBv => "bv32.uNegOverflow";
op bv64_sNegOverflow : UnaryOverflowBv => "bv64.sNegOverflow";
op bv128_sNegOverflow : UnaryOverflowBv => "bv128.sNegOverflow";
op bv64_uNegOverflow : UnaryOverflowBv => "bv64.uNegOverflow";
op bv128_uNegOverflow : UnaryOverflowBv => "bv128.uNegOverflow";
fn unaryOverflowBv (W : Type, f : UnaryOverflowBv, a : bv W) : bool => f "(" a ")";

// ---- CastBv (width-polymorphic: a : bv W -> int) ----
category CastBv;
op bv1_toUInt : CastBv => "bv1.toUInt";
op bv1_toInt : CastBv => "bv1.toInt";
op bv8_toUInt : CastBv => "bv8.toUInt";
op bv8_toInt : CastBv => "bv8.toInt";
op bv16_toUInt : CastBv => "bv16.toUInt";
op bv16_toInt : CastBv => "bv16.toInt";
op bv32_toUInt : CastBv => "bv32.toUInt";
op bv32_toInt : CastBv => "bv32.toInt";
op bv64_toUInt : CastBv => "bv64.toUInt";
op bv64_toInt : CastBv => "bv64.toInt";
op bv128_toUInt : CastBv => "bv128.toUInt";
op bv128_toInt : CastBv => "bv128.toInt";
fn castBv (W : Type, f : CastBv, a : bv W) : int => f "(" a ")";

// ---- BinaryArithBasicInt ----
category BinaryArithBasicInt;
op int_add : BinaryArithBasicInt => "int.add";
op int_sub : BinaryArithBasicInt => "int.sub";
op int_mul : BinaryArithBasicInt => "int.mul";
fn binaryArithBasicInt (f : BinaryArithBasicInt, a : int, b : int) : int => f "(" a ", " b ")";

// ---- BinaryArithBasicReal ----
category BinaryArithBasicReal;
op real_add : BinaryArithBasicReal => "real.add";
op real_sub : BinaryArithBasicReal => "real.sub";
op real_mul : BinaryArithBasicReal => "real.mul";
fn binaryArithBasicReal (f : BinaryArithBasicReal, a : real, b : real) : real => f "(" a ", " b ")";

// ---- BinaryArithBasicBv (width-polymorphic: a b : bv W -> bv W) ----
category BinaryArithBasicBv;
op bv1_add : BinaryArithBasicBv => "bv1.add";
op bv1_sub : BinaryArithBasicBv => "bv1.sub";
op bv1_mul : BinaryArithBasicBv => "bv1.mul";
op bv8_add : BinaryArithBasicBv => "bv8.add";
op bv8_sub : BinaryArithBasicBv => "bv8.sub";
op bv8_mul : BinaryArithBasicBv => "bv8.mul";
op bv16_add : BinaryArithBasicBv => "bv16.add";
op bv16_sub : BinaryArithBasicBv => "bv16.sub";
op bv16_mul : BinaryArithBasicBv => "bv16.mul";
op bv32_add : BinaryArithBasicBv => "bv32.add";
op bv32_sub : BinaryArithBasicBv => "bv32.sub";
op bv32_mul : BinaryArithBasicBv => "bv32.mul";
op bv64_add : BinaryArithBasicBv => "bv64.add";
op bv128_add : BinaryArithBasicBv => "bv128.add";
op bv64_sub : BinaryArithBasicBv => "bv64.sub";
op bv128_sub : BinaryArithBasicBv => "bv128.sub";
op bv64_mul : BinaryArithBasicBv => "bv64.mul";
op bv128_mul : BinaryArithBasicBv => "bv128.mul";
fn binaryArithBasicBv (W : Type, f : BinaryArithBasicBv, a : bv W, b : bv W) : bv W => f "(" a ", " b ")";

// ---- BinaryArithDivModInt ----
category BinaryArithDivModInt;
op int_div : BinaryArithDivModInt => "int.div";
op int_mod : BinaryArithDivModInt => "int.mod";
fn binaryArithDivModInt (f : BinaryArithDivModInt, a : int, b : int) : int => f "(" a ", " b ")";

// ---- BinaryArithDivModReal ----
category BinaryArithDivModReal;
op real_div : BinaryArithDivModReal => "real.div";
fn binaryArithDivModReal (f : BinaryArithDivModReal, a : real, b : real) : real => f "(" a ", " b ")";

// ---- BinaryArithDivModBv (width-polymorphic) ----
category BinaryArithDivModBv;
op bv1_uDiv : BinaryArithDivModBv => "bv1.uDiv";
op bv1_uMod : BinaryArithDivModBv => "bv1.uMod";
op bv1_sDiv : BinaryArithDivModBv => "bv1.sDiv";
op bv1_sMod : BinaryArithDivModBv => "bv1.sMod";
op bv8_uDiv : BinaryArithDivModBv => "bv8.uDiv";
op bv8_uMod : BinaryArithDivModBv => "bv8.uMod";
op bv8_sDiv : BinaryArithDivModBv => "bv8.sDiv";
op bv8_sMod : BinaryArithDivModBv => "bv8.sMod";
op bv16_uDiv : BinaryArithDivModBv => "bv16.uDiv";
op bv16_uMod : BinaryArithDivModBv => "bv16.uMod";
op bv16_sDiv : BinaryArithDivModBv => "bv16.sDiv";
op bv16_sMod : BinaryArithDivModBv => "bv16.sMod";
op bv32_uDiv : BinaryArithDivModBv => "bv32.uDiv";
op bv32_uMod : BinaryArithDivModBv => "bv32.uMod";
op bv32_sDiv : BinaryArithDivModBv => "bv32.sDiv";
op bv32_sMod : BinaryArithDivModBv => "bv32.sMod";
op bv64_uDiv : BinaryArithDivModBv => "bv64.uDiv";
op bv128_uDiv : BinaryArithDivModBv => "bv128.uDiv";
op bv64_uMod : BinaryArithDivModBv => "bv64.uMod";
op bv128_uMod : BinaryArithDivModBv => "bv128.uMod";
op bv64_sDiv : BinaryArithDivModBv => "bv64.sDiv";
op bv128_sDiv : BinaryArithDivModBv => "bv128.sDiv";
op bv64_sMod : BinaryArithDivModBv => "bv64.sMod";
op bv128_sMod : BinaryArithDivModBv => "bv128.sMod";
fn binaryArithDivModBv (W : Type, f : BinaryArithDivModBv, a : bv W, b : bv W) : bv W => f "(" a ", " b ")";

// ---- BinaryBitwiseBv (width-polymorphic) ----
category BinaryBitwiseBv;
op bv1_and : BinaryBitwiseBv => "bv1.and";
op bv1_or : BinaryBitwiseBv => "bv1.or";
op bv1_xor : BinaryBitwiseBv => "bv1.xor";
op bv1_shl : BinaryBitwiseBv => "bv1.shl";
op bv1_uShr : BinaryBitwiseBv => "bv1.uShr";
op bv1_sShr : BinaryBitwiseBv => "bv1.sShr";
op bv8_and : BinaryBitwiseBv => "bv8.and";
op bv8_or : BinaryBitwiseBv => "bv8.or";
op bv8_xor : BinaryBitwiseBv => "bv8.xor";
op bv8_shl : BinaryBitwiseBv => "bv8.shl";
op bv8_uShr : BinaryBitwiseBv => "bv8.uShr";
op bv8_sShr : BinaryBitwiseBv => "bv8.sShr";
op bv16_and : BinaryBitwiseBv => "bv16.and";
op bv16_or : BinaryBitwiseBv => "bv16.or";
op bv16_xor : BinaryBitwiseBv => "bv16.xor";
op bv16_shl : BinaryBitwiseBv => "bv16.shl";
op bv16_uShr : BinaryBitwiseBv => "bv16.uShr";
op bv16_sShr : BinaryBitwiseBv => "bv16.sShr";
op bv32_and : BinaryBitwiseBv => "bv32.and";
op bv32_or : BinaryBitwiseBv => "bv32.or";
op bv32_xor : BinaryBitwiseBv => "bv32.xor";
op bv32_shl : BinaryBitwiseBv => "bv32.shl";
op bv32_uShr : BinaryBitwiseBv => "bv32.uShr";
op bv32_sShr : BinaryBitwiseBv => "bv32.sShr";
op bv64_and : BinaryBitwiseBv => "bv64.and";
op bv128_and : BinaryBitwiseBv => "bv128.and";
op bv64_or : BinaryBitwiseBv => "bv64.or";
op bv128_or : BinaryBitwiseBv => "bv128.or";
op bv64_xor : BinaryBitwiseBv => "bv64.xor";
op bv128_xor : BinaryBitwiseBv => "bv128.xor";
op bv64_shl : BinaryBitwiseBv => "bv64.shl";
op bv128_shl : BinaryBitwiseBv => "bv128.shl";
op bv64_uShr : BinaryBitwiseBv => "bv64.uShr";
op bv128_uShr : BinaryBitwiseBv => "bv128.uShr";
op bv64_sShr : BinaryBitwiseBv => "bv64.sShr";
op bv128_sShr : BinaryBitwiseBv => "bv128.sShr";
fn binaryBitwiseBv (W : Type, f : BinaryBitwiseBv, a : bv W, b : bv W) : bv W => f "(" a ", " b ")";

// ---- BinarySafeInt ----
category BinarySafeInt;
op int_safeDiv : BinarySafeInt => "int.safeDiv";
op int_safeMod : BinarySafeInt => "int.safeMod";
fn binarySafeInt (f : BinarySafeInt, a : int, b : int) : int => f "(" a ", " b ")";

// ---- BinarySafeBv (width-polymorphic) ----
category BinarySafeBv;
op bv1_safeAdd : BinarySafeBv => "bv1.safeAdd";
op bv1_safeSub : BinarySafeBv => "bv1.safeSub";
op bv1_safeMul : BinarySafeBv => "bv1.safeMul";
op bv1_safeUAdd : BinarySafeBv => "bv1.safeUAdd";
op bv1_safeUSub : BinarySafeBv => "bv1.safeUSub";
op bv1_safeUMul : BinarySafeBv => "bv1.safeUMul";
op bv1_safeSDiv : BinarySafeBv => "bv1.safeSDiv";
op bv1_safeSMod : BinarySafeBv => "bv1.safeSMod";
op bv8_safeAdd : BinarySafeBv => "bv8.safeAdd";
op bv8_safeSub : BinarySafeBv => "bv8.safeSub";
op bv8_safeMul : BinarySafeBv => "bv8.safeMul";
op bv8_safeUAdd : BinarySafeBv => "bv8.safeUAdd";
op bv8_safeUSub : BinarySafeBv => "bv8.safeUSub";
op bv8_safeUMul : BinarySafeBv => "bv8.safeUMul";
op bv8_safeSDiv : BinarySafeBv => "bv8.safeSDiv";
op bv8_safeSMod : BinarySafeBv => "bv8.safeSMod";
op bv16_safeAdd : BinarySafeBv => "bv16.safeAdd";
op bv16_safeSub : BinarySafeBv => "bv16.safeSub";
op bv16_safeMul : BinarySafeBv => "bv16.safeMul";
op bv16_safeUAdd : BinarySafeBv => "bv16.safeUAdd";
op bv16_safeUSub : BinarySafeBv => "bv16.safeUSub";
op bv16_safeUMul : BinarySafeBv => "bv16.safeUMul";
op bv16_safeSDiv : BinarySafeBv => "bv16.safeSDiv";
op bv16_safeSMod : BinarySafeBv => "bv16.safeSMod";
op bv32_safeAdd : BinarySafeBv => "bv32.safeAdd";
op bv32_safeSub : BinarySafeBv => "bv32.safeSub";
op bv32_safeMul : BinarySafeBv => "bv32.safeMul";
op bv32_safeUAdd : BinarySafeBv => "bv32.safeUAdd";
op bv32_safeUSub : BinarySafeBv => "bv32.safeUSub";
op bv32_safeUMul : BinarySafeBv => "bv32.safeUMul";
op bv32_safeSDiv : BinarySafeBv => "bv32.safeSDiv";
op bv32_safeSMod : BinarySafeBv => "bv32.safeSMod";
op bv64_safeAdd : BinarySafeBv => "bv64.safeAdd";
op bv128_safeAdd : BinarySafeBv => "bv128.safeAdd";
op bv64_safeSub : BinarySafeBv => "bv64.safeSub";
op bv128_safeSub : BinarySafeBv => "bv128.safeSub";
op bv64_safeMul : BinarySafeBv => "bv64.safeMul";
op bv128_safeMul : BinarySafeBv => "bv128.safeMul";
op bv64_safeUAdd : BinarySafeBv => "bv64.safeUAdd";
op bv128_safeUAdd : BinarySafeBv => "bv128.safeUAdd";
op bv64_safeUSub : BinarySafeBv => "bv64.safeUSub";
op bv128_safeUSub : BinarySafeBv => "bv128.safeUSub";
op bv64_safeUMul : BinarySafeBv => "bv64.safeUMul";
op bv128_safeUMul : BinarySafeBv => "bv128.safeUMul";
op bv64_safeSDiv : BinarySafeBv => "bv64.safeSDiv";
op bv128_safeSDiv : BinarySafeBv => "bv128.safeSDiv";
op bv64_safeSMod : BinarySafeBv => "bv64.safeSMod";
op bv128_safeSMod : BinarySafeBv => "bv128.safeSMod";
fn binarySafeBv (W : Type, f : BinarySafeBv, a : bv W, b : bv W) : bv W => f "(" a ", " b ")";

// ---- BinaryTruncInt ----
category BinaryTruncInt;
op int_divT : BinaryTruncInt => "int.divT";
op int_modT : BinaryTruncInt => "int.modT";
op int_safeDivT : BinaryTruncInt => "int.safeDivT";
op int_safeModT : BinaryTruncInt => "int.safeModT";
fn binaryTruncInt (f : BinaryTruncInt, a : int, b : int) : int => f "(" a ", " b ")";

// ---- BinaryCmpBaseInt ----
category BinaryCmpBaseInt;
op int_le : BinaryCmpBaseInt => "int.le";
op int_lt : BinaryCmpBaseInt => "int.lt";
op int_ge : BinaryCmpBaseInt => "int.ge";
op int_gt : BinaryCmpBaseInt => "int.gt";
fn binaryCmpBaseInt (f : BinaryCmpBaseInt, a : int, b : int) : bool => f "(" a ", " b ")";

// ---- BinaryCmpBaseReal ----
category BinaryCmpBaseReal;
op real_le : BinaryCmpBaseReal => "real.le";
op real_lt : BinaryCmpBaseReal => "real.lt";
op real_ge : BinaryCmpBaseReal => "real.ge";
op real_gt : BinaryCmpBaseReal => "real.gt";
fn binaryCmpBaseReal (f : BinaryCmpBaseReal, a : real, b : real) : bool => f "(" a ", " b ")";

// ---- BinaryCmpBaseBv (width-polymorphic: a b : bv W -> bool) ----
category BinaryCmpBaseBv;
op bv1_uLe : BinaryCmpBaseBv => "bv1.uLe";
op bv1_uLt : BinaryCmpBaseBv => "bv1.uLt";
op bv1_uGe : BinaryCmpBaseBv => "bv1.uGe";
op bv1_uGt : BinaryCmpBaseBv => "bv1.uGt";
op bv8_uLe : BinaryCmpBaseBv => "bv8.uLe";
op bv8_uLt : BinaryCmpBaseBv => "bv8.uLt";
op bv8_uGe : BinaryCmpBaseBv => "bv8.uGe";
op bv8_uGt : BinaryCmpBaseBv => "bv8.uGt";
op bv16_uLe : BinaryCmpBaseBv => "bv16.uLe";
op bv16_uLt : BinaryCmpBaseBv => "bv16.uLt";
op bv16_uGe : BinaryCmpBaseBv => "bv16.uGe";
op bv16_uGt : BinaryCmpBaseBv => "bv16.uGt";
op bv32_uLe : BinaryCmpBaseBv => "bv32.uLe";
op bv32_uLt : BinaryCmpBaseBv => "bv32.uLt";
op bv32_uGe : BinaryCmpBaseBv => "bv32.uGe";
op bv32_uGt : BinaryCmpBaseBv => "bv32.uGt";
op bv64_uLe : BinaryCmpBaseBv => "bv64.uLe";
op bv128_uLe : BinaryCmpBaseBv => "bv128.uLe";
op bv64_uLt : BinaryCmpBaseBv => "bv64.uLt";
op bv128_uLt : BinaryCmpBaseBv => "bv128.uLt";
op bv64_uGe : BinaryCmpBaseBv => "bv64.uGe";
op bv128_uGe : BinaryCmpBaseBv => "bv128.uGe";
op bv64_uGt : BinaryCmpBaseBv => "bv64.uGt";
op bv128_uGt : BinaryCmpBaseBv => "bv128.uGt";
fn binaryCmpBaseBv (W : Type, f : BinaryCmpBaseBv, a : bv W, b : bv W) : bool => f "(" a ", " b ")";

// ---- BinaryCmpSignedBv (width-polymorphic) ----
category BinaryCmpSignedBv;
op bv1_sLe : BinaryCmpSignedBv => "bv1.sLe";
op bv1_sLt : BinaryCmpSignedBv => "bv1.sLt";
op bv1_sGe : BinaryCmpSignedBv => "bv1.sGe";
op bv1_sGt : BinaryCmpSignedBv => "bv1.sGt";
op bv8_sLe : BinaryCmpSignedBv => "bv8.sLe";
op bv8_sLt : BinaryCmpSignedBv => "bv8.sLt";
op bv8_sGe : BinaryCmpSignedBv => "bv8.sGe";
op bv8_sGt : BinaryCmpSignedBv => "bv8.sGt";
op bv16_sLe : BinaryCmpSignedBv => "bv16.sLe";
op bv16_sLt : BinaryCmpSignedBv => "bv16.sLt";
op bv16_sGe : BinaryCmpSignedBv => "bv16.sGe";
op bv16_sGt : BinaryCmpSignedBv => "bv16.sGt";
op bv32_sLe : BinaryCmpSignedBv => "bv32.sLe";
op bv32_sLt : BinaryCmpSignedBv => "bv32.sLt";
op bv32_sGe : BinaryCmpSignedBv => "bv32.sGe";
op bv32_sGt : BinaryCmpSignedBv => "bv32.sGt";
op bv64_sLe : BinaryCmpSignedBv => "bv64.sLe";
op bv128_sLe : BinaryCmpSignedBv => "bv128.sLe";
op bv64_sLt : BinaryCmpSignedBv => "bv64.sLt";
op bv128_sLt : BinaryCmpSignedBv => "bv128.sLt";
op bv64_sGe : BinaryCmpSignedBv => "bv64.sGe";
op bv128_sGe : BinaryCmpSignedBv => "bv128.sGe";
op bv64_sGt : BinaryCmpSignedBv => "bv64.sGt";
op bv128_sGt : BinaryCmpSignedBv => "bv128.sGt";
fn binaryCmpSignedBv (W : Type, f : BinaryCmpSignedBv, a : bv W, b : bv W) : bool => f "(" a ", " b ")";

// ---- BinaryOverflowBv (width-polymorphic: a b : bv W -> bool) ----
category BinaryOverflowBv;
op bv1_sAddOverflow : BinaryOverflowBv => "bv1.sAddOverflow";
op bv1_sSubOverflow : BinaryOverflowBv => "bv1.sSubOverflow";
op bv1_sMulOverflow : BinaryOverflowBv => "bv1.sMulOverflow";
op bv1_sDivOverflow : BinaryOverflowBv => "bv1.sDivOverflow";
op bv1_uAddOverflow : BinaryOverflowBv => "bv1.uAddOverflow";
op bv1_uSubOverflow : BinaryOverflowBv => "bv1.uSubOverflow";
op bv1_uMulOverflow : BinaryOverflowBv => "bv1.uMulOverflow";
op bv8_sAddOverflow : BinaryOverflowBv => "bv8.sAddOverflow";
op bv8_sSubOverflow : BinaryOverflowBv => "bv8.sSubOverflow";
op bv8_sMulOverflow : BinaryOverflowBv => "bv8.sMulOverflow";
op bv8_sDivOverflow : BinaryOverflowBv => "bv8.sDivOverflow";
op bv8_uAddOverflow : BinaryOverflowBv => "bv8.uAddOverflow";
op bv8_uSubOverflow : BinaryOverflowBv => "bv8.uSubOverflow";
op bv8_uMulOverflow : BinaryOverflowBv => "bv8.uMulOverflow";
op bv16_sAddOverflow : BinaryOverflowBv => "bv16.sAddOverflow";
op bv16_sSubOverflow : BinaryOverflowBv => "bv16.sSubOverflow";
op bv16_sMulOverflow : BinaryOverflowBv => "bv16.sMulOverflow";
op bv16_sDivOverflow : BinaryOverflowBv => "bv16.sDivOverflow";
op bv16_uAddOverflow : BinaryOverflowBv => "bv16.uAddOverflow";
op bv16_uSubOverflow : BinaryOverflowBv => "bv16.uSubOverflow";
op bv16_uMulOverflow : BinaryOverflowBv => "bv16.uMulOverflow";
op bv32_sAddOverflow : BinaryOverflowBv => "bv32.sAddOverflow";
op bv32_sSubOverflow : BinaryOverflowBv => "bv32.sSubOverflow";
op bv32_sMulOverflow : BinaryOverflowBv => "bv32.sMulOverflow";
op bv32_sDivOverflow : BinaryOverflowBv => "bv32.sDivOverflow";
op bv32_uAddOverflow : BinaryOverflowBv => "bv32.uAddOverflow";
op bv32_uSubOverflow : BinaryOverflowBv => "bv32.uSubOverflow";
op bv32_uMulOverflow : BinaryOverflowBv => "bv32.uMulOverflow";
op bv64_sAddOverflow : BinaryOverflowBv => "bv64.sAddOverflow";
op bv128_sAddOverflow : BinaryOverflowBv => "bv128.sAddOverflow";
op bv64_sSubOverflow : BinaryOverflowBv => "bv64.sSubOverflow";
op bv128_sSubOverflow : BinaryOverflowBv => "bv128.sSubOverflow";
op bv64_sMulOverflow : BinaryOverflowBv => "bv64.sMulOverflow";
op bv128_sMulOverflow : BinaryOverflowBv => "bv128.sMulOverflow";
op bv64_sDivOverflow : BinaryOverflowBv => "bv64.sDivOverflow";
op bv128_sDivOverflow : BinaryOverflowBv => "bv128.sDivOverflow";
op bv64_uAddOverflow : BinaryOverflowBv => "bv64.uAddOverflow";
op bv128_uAddOverflow : BinaryOverflowBv => "bv128.uAddOverflow";
op bv64_uSubOverflow : BinaryOverflowBv => "bv64.uSubOverflow";
op bv128_uSubOverflow : BinaryOverflowBv => "bv128.uSubOverflow";
op bv64_uMulOverflow : BinaryOverflowBv => "bv64.uMulOverflow";
op bv128_uMulOverflow : BinaryOverflowBv => "bv128.uMulOverflow";
fn binaryOverflowBv (W : Type, f : BinaryOverflowBv, a : bv W, b : bv W) : bool => f "(" a ", " b ")";

// ---- Bitvector concat and extract ----
fn bvconcat8 (a : bv W8, b : bv W8) : bv W16 => "bvconcat{8}{8}" "(" a ", " b ")";
fn bvconcat16 (a : bv W16, b : bv W16) : bv W32 => "bvconcat{16}{16}" "(" a ", " b ")";
fn bvconcat32 (a : bv W32, b : bv W32) : bv W64 => "bvconcat{32}{32}" "(" a ", " b ")";

fn bvextract_7_7 (a : bv W8) : bv W1 => "bvextract{7}{7}{8}" "(" a ")";
fn bvextract_15_15 (a : bv W16) : bv W1 => "bvextract{15}{15}{16}" "(" a ")";
fn bvextract_31_31 (a : bv W32) : bv W1 => "bvextract{31}{31}{32}" "(" a ")";
fn bvextract_7_0_16 (a : bv W16) : bv W8 => "bvextract{7}{0}{16}" "(" a ")";
fn bvextract_7_0_32 (a : bv W32) : bv W8 => "bvextract{7}{0}{32}" "(" a ")";
fn bvextract_15_0_32 (a : bv W32) : bv W16 => "bvextract{15}{0}{32}" "(" a ")";
fn bvextract_7_0_64 (a : bv W64) : bv W8 => "bvextract{7}{0}{64}" "(" a ")";
fn bvextract_15_0_64 (a : bv W64) : bv W16 => "bvextract{15}{0}{64}" "(" a ")";
fn bvextract_31_0_64 (a : bv W64) : bv W32 => "bvextract{31}{0}{64}" "(" a ")";

// ---- Quantifiers and binders ----
category TriggerGroup;
category Triggers;
op trigger (exprs : CommaSepBy Expr) : TriggerGroup =>
  " { " exprs " }\n  ";
op triggersAtom (group : TriggerGroup) : Triggers =>
  group;
op triggersPush (triggers : Triggers, group : TriggerGroup) : Triggers =>
  triggers group;

// Lambda abstraction
fn lambda (tp : Type, d : DeclList, @[scope(d)] body : tp) : fnOf(d, tp) =>
  "fun " d " => " body:3;

// "have" binding: `have x : T = v in body`. Syntactic sugar for a lambda
// application `(fun x : T => body) v`; `x` is in scope only in `body`. The
// binder is a single-element `DeclList`, reusing the same scoping machinery as
// `lambda`/`forall`.
fn have_expr (tp : Type, resTp : Type, d : DeclList, val : tp, @[scope(d)] body : resTp) : resTp =>
  @[prec(2)] "have " d " = " val:0 " in " body:3;

// Application of an expression to an argument
fn apply_expr (inTp : Type, outTp : Type, f : inTp -> outTp, x : inTp) : outTp =>
  "(" f ")" "(" x ")";

// Quantifiers without triggers
fn forall (d : DeclList, @[scope(d)] b : bool) : bool =>
  "forall " d " :: " b:3;
fn exists (d : DeclList, @[scope(d)] b : bool) : bool =>
  "exists " d " :: " b:3;

// Quantifiers with triggers
fn forallT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "forall " d " :: " triggers indent(2, b:3);
fn existsT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "exists " d " :: " triggers indent(2, b:3);

// ═══════════════════════════════════════════════════════════════════
// STATEMENTS
// ═══════════════════════════════════════════════════════════════════

// ---- Assignment targets ----
category Lhs;
op lhsIdent (v : Ident) : Lhs => v;
op lhsArray (tp : Type, a : Lhs, idx : tp) : Lhs => a "[" idx "]";

// ---- Statements (var, assign, assume/assert, if, call, blocks) ----
category Statement;
category Block;
category Else;
category Label;

op label (l : Ident) : Label => "[" l "]: ";

@[scope(dl)]
op varStatement (annots : Option MetadataAnn, dl : DeclList) : Statement => annots:0 "var " dl ";";
@[declare(v, tp)]
op initStatement (annots : Option MetadataAnn, tp : Type, v : Ident, e : tp) : Statement => annots:0 "var " v " : " tp " := " e ";";
op assign (annots : Option MetadataAnn, tp : Type, v : Lhs, e : tp) : Statement => annots:0 v:0 " := " e ";";
op assume (annots : Option MetadataAnn, label : Option Label, c : bool) : Statement =>
  annots:0 "assume " label c ";";
op assert (annots : Option MetadataAnn, label : Option Label, c : bool) : Statement =>
  annots:0 "assert " label c ";";
op cover (annots : Option MetadataAnn, label : Option Label, c : bool) : Statement =>
  annots:0 "cover " label c ";";
category ExprOrNondet;
op condDet (c : bool) : ExprOrNondet => "(" c ")";
op condNondet : ExprOrNondet => "*";

op if_statement (annots : Option MetadataAnn, c : ExprOrNondet, t : Block, f : Else) : Statement => annots:0 "if " c:0 " " t:0 f:0;
op else0 () : Else =>;
op else1 (f : Block) : Else => " else " f:0;
op havoc_statement (annots : Option MetadataAnn, v : Ident) : Statement => annots:0 "havoc " v ";";

// ---- Loops (invariants, measure, while) ----
category Invariant;
op invariant (label : Option Label, e : Expr) : Invariant => "invariant" label e ";";

category Invariants;
op nilInvariants : Invariants => ;
op consInvariants(label : Option Label, e : Expr, is : Invariants) : Invariants =>
  "invariant " label e "\n" is:0;

category Measure;
op measure_mk (e : Expr) : Measure => "decreases " e "\n";

op while_statement (annots : Option MetadataAnn, c : ExprOrNondet, m : Option Measure, is : Invariants, body : Block) : Statement =>
  annots:0 "while " c:0 "\n" m:0 is body:0;

category CallArg;
op callArgExpr (e : Expr) : CallArg => e;
op callArgOut (v : Ident) : CallArg => "out " v;
op callArgInout (v : Ident) : CallArg => "inout " v;

op call_statement (annots : Option MetadataAnn, f : Ident, args : CommaSepBy CallArg) : Statement =>
   annots:0 "call " f "(" args ")" ";";

@[scope(c)]
op block (c : NewlineSepBy Statement) : Block => "{\n  " indent(2, c) "\n}";
op block_statement (annots : Option MetadataAnn, label : Ident, b : Block) : Statement => annots:0 label ": " b:0;
op exit_statement (annots : Option MetadataAnn, label : Ident) : Statement => annots:0 "exit " label ";";

// ═══════════════════════════════════════════════════════════════════
// DECLARATIONS & PROGRAMS
// ═══════════════════════════════════════════════════════════════════

// ---- Procedure specs (requires / ensures) ----
category SpecElt;
category Free;
op free () : Free => "free ";
op ensures_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free?:0 "ensures " label b ";\n";
op requires_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free?:0 "requires " label b ";\n";

category Spec;
op spec_mk (elts : Seq SpecElt) : Spec => "spec " indent(2, "{\n" elts "} ");

// ---- Procedure parameter bindings ----
category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name " : " tp:0;
@[declare(name, tp)]
op outBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "out " name " : " tp:0;
@[declare(name, tp)]
op inoutBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "inout " name " : " tp:0;
@[declare(name, tp)]
op casesBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "@[cases] " name " : " tp:0;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => " (" bindings ")";

// ---- Commands (procedures, type/const/function declarations, programs) ----
op command_procedure (annots : Option MetadataAnn,
                      name : Ident,
                      typeArgs : Option TypeArgs,
                      @[scope(typeArgs)] b : Bindings,
                      @[scope(b)] s: Option Spec,
                      @[scope(b)] body : Option Block) :
  Command =>
  @[prec(10)] annots:0 "procedure " name typeArgs b "\n"
              s body ";\n";

// (FIXME) Change when DDM supports type declarations like so:
// type Array a;
// instead of
// type Array (a : Type);
// where the former is what Boogie does.
@[declareType(name, some args)]
op command_typedecl (annots : Option MetadataAnn, name : Ident, args : Option Bindings) : Command =>
  annots:0 "type " name args ";\n";

@[aliasType(name, some args, rhs)]
op command_typesynonym (annots : Option MetadataAnn,
                        name : Ident,
                        args : Option Bindings,
                        targs : Option TypeArgs,
                        @[scope(args)] rhs : Type) : Command =>
  annots:0 "type " name args " := " targs rhs ";\n";

@[declare(name, r)]
op command_constdecl (annots : Option MetadataAnn,
                      name : Ident,
                      typeArgs : Option TypeArgs,
                      r : Type) : Command =>
  annots:0 "const " name ":" typeArgs r ";\n";

@[declareFn(name, b, r)]
op command_fndecl (annots : Option MetadataAnn,
                   name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope(typeArgs)] r : Type) : Command =>
  annots:0 "function " name typeArgs b " : " r ";\n";

category Inline;
op inline () : Inline => "inline ";

// Note: when editing command_fndef, consider whether recfn_decl needs
// matching edits.
@[declareFn(name, b, r)]
op command_fndef (annots : Option MetadataAnn,
                  name : Ident,
                  typeArgs : Option TypeArgs,
                  @[scope(typeArgs)] b : Bindings,
                  @[scope(typeArgs)] r : Type,
                  @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
                  @[scope(b)] c : r,
                  // Prefer adding the inline attribute here so
                  // that the order of the arguments in the fndecl and fndef
                  // agree.
                  inline? : Option Inline) : Command =>
  annots:0 inline? "function " name typeArgs b " : " r indent(2, preconds) " {\n  " indent(2, c) "\n}\n";

// Recursive (and mutually recursive) function declarations.
// A single recursive function is a 1-element block, just like datatypes.
category RecFnDecl;

@[declareFn(name, b, r)]
op recfn_decl (name : Ident,
               typeArgs : Option TypeArgs,
               @[scope(typeArgs)] b : Bindings,
               @[scope(typeArgs)] r : Type,
               @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
               @[scope(b)] decreases : Option Measure,
               @[scope(b)] c : r) : RecFnDecl =>
  "function " name typeArgs b " : " r indent(2, preconds) "\n" indent(2, decreases) "{\n  " indent(2, c) "\n}";

@[scope(recfns), preRegisterFunctions(recfns)]
op command_recfndefs (annots : Option MetadataAnn, recfns : NewlineSepBy RecFnDecl) : Command =>
  annots:0 "rec " recfns ";\n";

// Function declaration statement
@[declareFn(name, b, r)]
op funcDecl_statement (annots : Option MetadataAnn,
                       name : Ident,
                       typeArgs : Option TypeArgs,
                       @[scope(typeArgs)] b : Bindings,
                       @[scope(typeArgs)] r : Type,
                       @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
                       @[scope(b)] body : r,
                       inline? : Option Inline) : Statement =>
  annots:0 inline? "function " name typeArgs b " : " r indent(2, preconds) " { " body " }";

// Type declaration statement
@[declareScopedType(name, some args)]
op typeDecl_statement (annots : Option MetadataAnn, name : Ident, args : Option Bindings) : Statement =>
  annots:0 "type " name args ";";

op command_axiom (annots : Option MetadataAnn, label : Option Label, e : bool) : Command =>
  annots:0 "axiom " label e ";\n";

op command_distinct (annots : Option MetadataAnn, label : Option Label, exprs : CommaSepBy Expr) : Command =>
  annots:0 "distinct " label "[" exprs "]" ";\n";

// Top-level block command for parsing statements directly
op command_block (b : Block) : Command =>
  b ";\n";

// =====================================================================
// Datatype Syntax Categories
// =====================================================================

// Constructor syntax for datatypes
category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) :
    Constructor => name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => "\n  " c:0;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor)
    : ConstructorList => cl:0 ",\n  " c:0;

// preRegisterTypes on command_datatypes handles bringing datatype names into
// scope; @[scopeTVar(typeParams)] brings type parameters into scope for constructors.
category DatatypeDecl;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.datatype, .literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType),
    perField([.datatype, .literal "..", .field, .literal "!"], [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                  typeParams : Option Bindings,
                  @[scopeTVar(typeParams)] constructors : ConstructorList)
      : DatatypeDecl =>
      "datatype " name typeParams " {" constructors "\n}";

// Unified datatype command: one or more datatype declarations separated by
// newlines, ending with a semicolon.
//
// `@[nonempty]` is load-bearing: see
// https://github.com/strata-org/Strata/issues/1146.
@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (annots : Option MetadataAnn, @[nonempty] datatypes : NewlineSepBy DatatypeDecl) : Command =>
  annots:0 datatypes ";\n";

// =====================================================================
// CFG (Unstructured Control Flow) Syntax
// =====================================================================

// Transfer commands: how a basic block ends
category Transfer;

// Unconditional goto: exactly one target.
op transfer_goto (label : Ident) : Transfer =>
  "goto " label ";";

// Nondeterministic goto: exactly two targets chosen nondeterministically.
op transfer_nondet_goto (label1 : Ident, label2 : Ident) : Transfer =>
  "goto " label1 ", " label2 ";";

// Conditional goto (deterministic: condition selects between two targets)
// NOTE: We use "branch" instead of "if" to avoid ambiguity with the
// structured if-statement syntax. The DDM parser registers tokens globally,
// so "if (" in Transfer would conflict with "if (" in Statement.
op transfer_cond_goto (c : Expr, lt : Ident, lf : Ident) : Transfer =>
  "branch (" c ") goto " lt " else " "goto " lf ";";

// Return/finish (terminate execution)
op transfer_return : Transfer =>
  "return;";

// A single CFG basic block: label, commands, transfer
category CFGBlock;
@[scope(cmds)]
op cfg_block (label : Ident, cmds : Seq Statement, tr : Transfer) : CFGBlock =>
  label ":" " {\n" indent(2, cmds) "  " tr "\n}";

// A list of CFG blocks
category CFGBlocks;
op cfg_blocks_one (b : CFGBlock) : CFGBlocks => b;
// `@[scope(b)]` makes `b`'s declarations visible to every textually-later
// block. Visibility is purely left-to-right in source order — it is not
// goto/dominance aware, so a block cannot see declarations in a block written
// after it, even when the control-flow graph reaches it only via that later
// block. If a later block re-declares a propagated name it silently shadows
// the earlier one (ordinary nested-scope shadowing). Nothing downstream acts
// on these declarations yet (the translator stubs CFG procedures), so name
// resolution is currently the only consumer of this contract.
op cfg_blocks_cons (b : CFGBlock, @[scope(b)] rest : CFGBlocks) : CFGBlocks =>
  b "\n" rest;

// CFG body: entry label + blocks
category CFGBody;
op cfg_body (entry : Ident, blocks : CFGBlocks) : CFGBody =>
  "cfg " entry " {\n" indent(2, blocks) "\n}";

// Procedure with CFG body
op command_cfg_procedure (annots : Option MetadataAnn,
                          name : Ident,
                          typeArgs : Option TypeArgs,
                          @[scope(typeArgs)] b : Bindings,
                          @[scope(b)] s : Option Spec,
                          @[scope(b)] body : CFGBody) :
  Command =>
  @[prec(10)] annots:0 "procedure " name typeArgs b "\n"
              s body ";\n";

#end

---------------------------------------------------------------------

namespace CoreDDM

#strata_gen Core

end CoreDDM

---------------------------------------------------------------------

end Strata
end

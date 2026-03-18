// Boogie program verifier version 3.5.3.0, Copyright (c) 2003-2014, Microsoft.
// Command Line Options:  -typeEncoding:m -timeLimit:200 -removeEmptyBlocks:0  /inferModifies -printModel:1 /printModelToFile:model.dmp 

var otherfile.$heap: $heap_type where otherfile.$good_heap(otherfile.$heap);

var otherfile.$arrSizeHeap: [ref]java_int where otherfile.$goodArrSizeHeap(otherfile.$arrSizeHeap);

var otherfile.$stringSizeHeap: stringSizeHeap_type;

var otherfile.$boolArrHeap: boolArrHeap_type;

var otherfile.$refArrHeap: refArrHeap_type;

var otherfile.$floatArrHeap: floatArrHeap_type;

var otherfile.$doubleArrHeap: doubleArrHeap_type;

var otherfile.$intArrHeap: intArrHeap_type;

var otherfile.$charArrHeap: charArrHeap_type;

var otherfile.$byteArrHeap: byteArrHeap_type;

var otherfile.$shortArrHeap: shortArrHeap_type;

var otherfile.$longArrHeap: longArrHeap_type;

var otherfile.$stringValueHeap: stringValueHeap_type;

const unique otherfile.$null: ref;

const unique otherfile.$type: Field javaType;

const unique otherfile.$alloc: Field bool;

const unique otherfile.$charArrayType: javaType;

const unique otherfile.$boolArrayType: javaType;

const unique otherfile.$byteArrayType: javaType;

const unique otherfile.$shortArrayType: javaType;

const unique otherfile.$intArrayType: javaType;

const unique otherfile.$longArrayType: javaType;

const unique otherfile.$floatArrayType: javaType;

const unique otherfile.$doubleArrayType: javaType;

const otherfile.FLOAT_ONE: java_float;

const otherfile.FLOAT_ZERO: java_float;

const otherfile.DOUBLE_ZERO: java_double;

const otherfile.DOUBLE_ONE: java_double;

const otherfile.CHAR_DEFAULT: java_char;

const otherfile.CHAR_MIN: java_char;

const otherfile.CHAR_MAX: java_char;

const otherfile.BYTE_DEFAULT: java_byte;

const otherfile.BYTE_MIN: java_byte;

const otherfile.BYTE_MAX: java_byte;

const otherfile.BYTE_ZERO: java_byte;

const otherfile.BYTE_ONE: java_byte;

const otherfile.SHORT_DEFAULT: java_short;

const otherfile.SHORT_MIN: java_short;

const otherfile.SHORT_MAX: java_short;

const otherfile.SHORT_ZERO: java_short;

const otherfile.SHORT_ONE: java_short;

const otherfile.INT_DEFAULT: java_int;

const otherfile.INT_MIN: java_int;

const otherfile.INT_MAX: java_int;

const otherfile.INT_ONE: java_int;

const otherfile.INT_ZERO: java_int;

const otherfile.INT_NEG_ONE: java_int;

const otherfile.LONG_DEFAULT: java_long;

const otherfile.LONG_MIN: java_long;

const otherfile.LONG_MAX: java_long;

const otherfile.LONG_ZERO: java_long;

const otherfile.LONG_ONE: java_long;

const {:sourceloc "SameV.java", -1, -1, -1, -1} unique otherfile.Object: javaType;

const {:sourceloc "SameV.java", -1, -1, -1, -1} unique otherfile.benchmarks.REVE.limit2.Neq.SameV: javaType;

function otherfile.$extends(arg_0: javaType, arg_1: javaType) : bool;

function otherfile.$good_heap(arg_0: $heap_type) : bool;

function otherfile.$arrayType(t: javaType) : javaType;

function otherfile.$goodArrSizeHeap(x: [ref]java_int) : bool;

function {:inline} otherfile.$byteToBool(x: java_byte) : bool
{
  (if x == otherfile.BYTE_ZERO then false else true)
}

function {:inline} otherfile.$shortToBool(x: java_short) : bool
{
  (if x == otherfile.SHORT_ZERO then false else true)
}

function {:inline} otherfile.$intToBool(x: java_int) : bool
{
  (if x == otherfile.INT_ZERO then false else true)
}

function {:inline} otherfile.$longToBool(x: java_long) : bool
{
  (if x == otherfile.LONG_ZERO then false else true)
}

function {:inline} otherfile.$floatToBool(x: java_float) : bool
{
  (if x == otherfile.FLOAT_ZERO then false else true)
}

function {:inline} otherfile.$doubleToBool(x: java_double) : bool
{
  (if x == otherfile.DOUBLE_ZERO then false else true)
}

function {:inline} otherfile.$refToBool(x: ref) : bool
{
  (if x == otherfile.$null then false else true)
}

function {:inline} otherfile.$boolToByte(x: bool) : java_byte
{
  (if x <==> true then otherfile.BYTE_ONE else otherfile.BYTE_ZERO)
}

function {:inline} otherfile.$boolToShort(x: bool) : java_short
{
  (if x <==> true then otherfile.SHORT_ONE else otherfile.SHORT_ZERO)
}

function {:inline} otherfile.$boolToInt(x: bool) : java_int
{
  (if x <==> true then otherfile.INT_ONE else otherfile.INT_ZERO)
}

function {:inline} otherfile.$boolToLong(x: bool) : java_long
{
  (if x <==> true then otherfile.LONG_ONE else otherfile.LONG_ZERO)
}

function {:inline} otherfile.$boolToFloat(x: bool) : java_float
{
  (if x <==> true then otherfile.FLOAT_ONE else otherfile.FLOAT_ZERO)
}

function {:inline} otherfile.$boolToDouble(x: bool) : java_double
{
  (if x <==> true then otherfile.DOUBLE_ONE else otherfile.DOUBLE_ZERO)
}

function {:inline} otherfile.$xorBool(p1: bool, p2: bool) : bool
{
  !p1 || p2
}

function {:inline} otherfile.$orBool(p1: bool, p2: bool) : bool
{
  p1 || p2
}

function {:inline} otherfile.$andBool(p1: bool, p2: bool) : bool
{
  p1 && p2
}

function {:inline} otherfile.$notBool(p1: bool) : bool
{
  !p1
}

function otherfile.$cmpBool(x: bool, y: bool) : java_int;

function otherfile.$cmpRef(x: ref, y: ref) : java_int;

function otherfile.getType(c: java_char) : java_int;

function otherfile.$floatInfinity() : java_float;

function otherfile.$floatNegInfinity() : java_float;

function otherfile.$floatNaN() : java_float;

function otherfile.$doubleInfinity() : java_double;

function otherfile.$doubleNegInfinity() : java_double;

function otherfile.$doubleNaN() : java_double;

function {:inline} otherfile.$ltFloat(x: java_float, y: java_float) : bool
{
  (if x < y then true else false)
}

function {:inline} otherfile.$leFloat(x: java_float, y: java_float) : bool
{
  (if x <= y then true else false)
}

function {:inline} otherfile.$gtFloat(x: java_float, y: java_float) : bool
{
  (if x > y then true else false)
}

function {:inline} otherfile.$geFloat(x: java_float, y: java_float) : bool
{
  (if x >= y then true else false)
}

function {:inline} otherfile.$ltDouble(x: java_double, y: java_double) : bool
{
  (if x < y then true else false)
}

function {:inline} otherfile.$leDouble(x: java_double, y: java_double) : bool
{
  (if x <= y then true else false)
}

function {:inline} otherfile.$gtDouble(x: java_double, y: java_double) : bool
{
  (if x > y then true else false)
}

function {:inline} otherfile.$geDouble(x: java_double, y: java_double) : bool
{
  (if x >= y then true else false)
}

function {:inline} otherfile.$cmpFloat(x: java_float, y: java_float) : java_int
{
  (if otherfile.$gtFloat(x, y) then otherfile.INT_ONE else (if otherfile.$ltFloat(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:inline} otherfile.$cmpDouble(x: java_double, y: java_double) : java_int
{
  (if otherfile.$gtDouble(x, y) then otherfile.INT_ONE else (if otherfile.$ltDouble(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:inline} otherfile.$addFloat(x: java_float, y: java_float) : java_float
{
  x + y
}

function {:inline} otherfile.$subFloat(x: java_float, y: java_float) : java_float
{
  x - y
}

function {:inline} otherfile.$mulFloat(x: java_float, y: java_float) : java_float
{
  x * y
}

function otherfile.$divFloat(x: java_float, y: java_float) : java_float;

function otherfile.$modFloat(x: java_float, y: java_float) : java_float;

function {:inline} otherfile.$negateFloat(x: java_float) : java_float
{
  0e0 - x
}

function {:inline} otherfile.$addDouble(x: java_double, y: java_double) : java_double
{
  x + y
}

function {:inline} otherfile.$subDouble(x: java_double, y: java_double) : java_double
{
  x - y
}

function {:inline} otherfile.$mulDouble(x: java_double, y: java_double) : java_double
{
  x * y
}

function otherfile.$divDouble(x: java_double, y: java_double) : java_double;

function otherfile.$modDouble(x: java_double, y: java_double) : java_double;

function {:inline} otherfile.$negateDouble(x: java_double) : java_double
{
  0e0 - x
}

function {:inline} otherfile.$doubleToFloat(x: java_double) : java_float
{
  x
}

function {:inline} otherfile.$floatToDouble(x: java_float) : java_double
{
  x
}

function {:inline} otherfile.$realToFloat(x: real) : java_float
{
  x
}

function {:inline} otherfile.$realToDouble(x: real) : java_double
{
  x
}

function {:bvbuiltin "bvshl"} otherfile.LEFT_SHIFT_CHAR(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvashr"} otherfile.RIGHT_SHIFT_CHAR(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvlshr"} otherfile.LRIGHT_SHIFT_CHAR(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvadd"} otherfile.$addChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvsub"} otherfile.$subChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvmul"} otherfile.$mulChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvudiv"} otherfile.$divChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvurem"} otherfile.$modChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvneg"} otherfile.$negChar(p1: java_char) : java_char;

function {:bvbuiltin "bvor"} otherfile.$bitOrChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvand"} otherfile.$bitAndChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvxor"} otherfile.$xorChar(p1: java_char, p2: java_char) : java_char;

function {:bvbuiltin "bvnot"} otherfile.$notChar(p1: java_char) : java_char;

function otherfile.$shlChar(p1: java_char, p2: java_char) : java_char
uses {
axiom (forall p1: java_char, p2: java_char :: { otherfile.$shlChar(p1, p2): java_char } otherfile.$shlChar(p1, p2): java_char == otherfile.LEFT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));
}

function otherfile.$shrChar(p1: java_char, p2: java_char) : java_char
uses {
axiom (forall p1: java_char, p2: java_char :: { otherfile.$shrChar(p1, p2): java_char } otherfile.$shrChar(p1, p2): java_char == otherfile.RIGHT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));
}

function otherfile.$ushrChar(p1: java_char, p2: java_char) : java_char
uses {
axiom (forall p1: java_char, p2: java_char :: { otherfile.$ushrChar(p1, p2): java_char } otherfile.$ushrChar(p1, p2): java_char == otherfile.LRIGHT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));
}

function {:bvbuiltin "bvult"} otherfile.$ltChar(p1: java_char, p2: java_char) : bool;

function {:bvbuiltin "bvule"} otherfile.$leChar(p1: java_char, p2: java_char) : bool;

function {:bvbuiltin "bvugt"} otherfile.$gtChar(p1: java_char, p2: java_char) : bool;

function {:bvbuiltin "bvuge"} otherfile.$geChar(p1: java_char, p2: java_char) : bool;

function {:inline} otherfile.$cmpChar(x: java_char, y: java_char) : java_int
{
  (if otherfile.$gtChar(x, y) then otherfile.INT_ONE else (if otherfile.$ltChar(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:bvbuiltin "bvshl"} otherfile.LEFT_SHIFT_BYTE(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvashr"} otherfile.RIGHT_SHIFT_BYTE(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvlshr"} otherfile.LRIGHT_SHIFT_BYTE(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvadd"} otherfile.$addByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvsub"} otherfile.$subByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvmul"} otherfile.$mulByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvsdiv"} otherfile.$divByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvsrem"} otherfile.$modByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvneg"} otherfile.$negByte(p1: java_byte) : java_byte;

function {:bvbuiltin "bvor"} otherfile.$bitOrByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvand"} otherfile.$bitAndByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvxor"} otherfile.$xorByte(p1: java_byte, p2: java_byte) : java_byte;

function {:bvbuiltin "bvnot"} otherfile.$notByte(p1: java_byte) : java_byte;

function {:inline} otherfile.$shlByte(p1: java_byte, p2: java_byte) : java_byte
{
  otherfile.LEFT_SHIFT_BYTE(p1, otherfile.$bitAndByte(p2, 31bv8))
}

function {:inline} otherfile.$shrByte(p1: java_byte, p2: java_byte) : java_byte
{
  otherfile.RIGHT_SHIFT_BYTE(p1, otherfile.$bitAndByte(p2, 31bv8))
}

function {:inline} otherfile.$ushrByte(p1: java_byte, p2: java_byte) : java_byte
{
  otherfile.LRIGHT_SHIFT_BYTE(p1, otherfile.$bitAndByte(p2, 31bv8))
}

function {:bvbuiltin "bvslt"} otherfile.$ltByte(p1: java_byte, p2: java_byte) : bool;

function {:bvbuiltin "bvsle"} otherfile.$leByte(p1: java_byte, p2: java_byte) : bool;

function {:bvbuiltin "bvsgt"} otherfile.$gtByte(p1: java_byte, p2: java_byte) : bool;

function {:bvbuiltin "bvsge"} otherfile.$geByte(p1: java_byte, p2: java_byte) : bool;

function {:inline} otherfile.$cmpByte(x: java_byte, y: java_byte) : java_int
{
  (if otherfile.$gtByte(x, y) then otherfile.INT_ONE else (if otherfile.$ltByte(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:bvbuiltin "bvshl"} otherfile.LEFT_SHIFT_SHORT(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvashr"} otherfile.RIGHT_SHIFT_SHORT(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvlshr"} otherfile.LRIGHT_SHIFT_SHORT(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvadd"} otherfile.$addShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvsub"} otherfile.$subShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvmul"} otherfile.$mulShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvsdiv"} otherfile.$divShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvsrem"} otherfile.$modShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvneg"} otherfile.$negShort(p1: java_short) : java_short;

function {:bvbuiltin "bvor"} otherfile.$bitOrShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvand"} otherfile.$bitAndShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvxor"} otherfile.$xorShort(p1: java_short, p2: java_short) : java_short;

function {:bvbuiltin "bvnot"} otherfile.$notShort(p1: java_short) : java_short;

function {:inline} otherfile.$shlShort(p1: java_short, p2: java_short) : java_short
{
  otherfile.LEFT_SHIFT_SHORT(p1, otherfile.$bitAndShort(p2, 31bv16))
}

function {:inline} otherfile.$shrShort(p1: java_short, p2: java_short) : java_short
{
  otherfile.RIGHT_SHIFT_SHORT(p1, otherfile.$bitAndShort(p2, 31bv16))
}

function {:inline} otherfile.$ushrShort(p1: java_short, p2: java_short) : java_short
{
  otherfile.LRIGHT_SHIFT_SHORT(p1, otherfile.$bitAndShort(p2, 31bv16))
}

function {:bvbuiltin "bvslt"} otherfile.$ltShort(p1: java_short, p2: java_short) : bool;

function {:bvbuiltin "bvsle"} otherfile.$leShort(p1: java_short, p2: java_short) : bool;

function {:bvbuiltin "bvsgt"} otherfile.$gtShort(p1: java_short, p2: java_short) : bool;

function {:bvbuiltin "bvsge"} otherfile.$geShort(p1: java_short, p2: java_short) : bool;

function {:inline} otherfile.$cmpShort(x: java_short, y: java_short) : java_int
{
  (if otherfile.$gtShort(x, y) then otherfile.INT_ONE else (if otherfile.$ltShort(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:bvbuiltin "bvshl"} otherfile.LEFT_SHIFT_INT(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvashr"} otherfile.RIGHT_SHIFT_INT(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvlshr"} otherfile.LRIGHT_SHIFT_INT(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvadd"} otherfile.$addInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvsub"} otherfile.$subInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvmul"} otherfile.$mulInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvsdiv"} otherfile.$divInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvsrem"} otherfile.$modInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvneg"} otherfile.$negInt(p1: java_int) : java_int;

function {:bvbuiltin "bvor"} otherfile.$bitOrInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvand"} otherfile.$bitAndInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvxor"} otherfile.$xorInt(p1: java_int, p2: java_int) : java_int;

function {:bvbuiltin "bvnot"} otherfile.$notInt(p1: java_int) : java_int;

function {:inline} otherfile.$shlInt(p1: java_int, p2: java_int) : java_int
{
  otherfile.LEFT_SHIFT_INT(p1, otherfile.$bitAndInt(p2, 31bv32))
}

function {:inline} otherfile.$shrInt(p1: java_int, p2: java_int) : java_int
{
  otherfile.RIGHT_SHIFT_INT(p1, otherfile.$bitAndInt(p2, 31bv32))
}

function {:inline} otherfile.$ushrInt(p1: java_int, p2: java_int) : java_int
{
  otherfile.LRIGHT_SHIFT_INT(p1, otherfile.$bitAndInt(p2, 31bv32))
}

function {:bvbuiltin "bvslt"} otherfile.$ltInt(p1: java_int, p2: java_int) : bool;

function {:bvbuiltin "bvsle"} otherfile.$leInt(p1: java_int, p2: java_int) : bool;

function {:bvbuiltin "bvsgt"} otherfile.$gtInt(p1: java_int, p2: java_int) : bool;

function {:bvbuiltin "bvsge"} otherfile.$geInt(p1: java_int, p2: java_int) : bool;

function {:inline} otherfile.$cmpInt(x: java_int, y: java_int) : java_int
{
  (if otherfile.$gtInt(x, y) then otherfile.INT_ONE else (if otherfile.$ltInt(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:bvbuiltin "bvshl"} otherfile.LEFT_SHIFT_LONG(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvashr"} otherfile.RIGHT_SHIFT_LONG(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvlshr"} otherfile.LRIGHT_SHIFT_LONG(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvadd"} otherfile.$addLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvsub"} otherfile.$subLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvmul"} otherfile.$mulLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvsdiv"} otherfile.$divLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvsrem"} otherfile.$modLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvneg"} otherfile.$negLong(p1: java_long) : java_long;

function {:bvbuiltin "bvor"} otherfile.$bitOrLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvand"} otherfile.$bitAndLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvxor"} otherfile.$xorLong(p1: java_long, p2: java_long) : java_long;

function {:bvbuiltin "bvnot"} otherfile.$notLong(p1: java_long) : java_long;

function {:inline} otherfile.$shlLong(p1: java_long, p2: java_long) : java_long
{
  otherfile.LEFT_SHIFT_LONG(p1, otherfile.$bitAndLong(p2, 63bv64))
}

function {:inline} otherfile.$shrLong(p1: java_long, p2: java_long) : java_long
{
  otherfile.RIGHT_SHIFT_LONG(p1, otherfile.$bitAndLong(p2, 63bv64))
}

function {:inline} otherfile.$ushrLong(p1: java_long, p2: java_long) : java_long
{
  otherfile.LRIGHT_SHIFT_LONG(p1, otherfile.$bitAndLong(p2, 63bv64))
}

function {:bvbuiltin "bvslt"} otherfile.$ltLong(p1: java_long, p2: java_long) : bool;

function {:bvbuiltin "bvsle"} otherfile.$leLong(p1: java_long, p2: java_long) : bool;

function {:bvbuiltin "bvsgt"} otherfile.$gtLong(p1: java_long, p2: java_long) : bool;

function {:bvbuiltin "bvsge"} otherfile.$geLong(p1: java_long, p2: java_long) : bool;

function {:inline} otherfile.$cmpLong(x: java_long, y: java_long) : java_int
{
  (if otherfile.$gtLong(x, y) then otherfile.INT_ONE else (if otherfile.$ltLong(x, y) then otherfile.INT_NEG_ONE else otherfile.INT_ZERO))
}

function {:bvbuiltin "concat"} otherfile.CONCAT8(p1: bv8, p2: bv8) : bv16;

function {:bvbuiltin "concat"} otherfile.CONCAT16(p1: bv16, p2: bv16) : bv32;

function {:bvbuiltin "concat"} otherfile.CONCAT32(p1: bv32, p2: bv32) : bv64;

function {:bvbuiltin "(_ extract 7 7)"} otherfile.GET_MSB8(p1: bv8) : bv1;

function {:bvbuiltin "(_ extract 15 15)"} otherfile.GET_MSB16(p1: bv16) : bv1;

function {:bvbuiltin "(_ extract 31 31)"} otherfile.GET_MSB32(p1: bv32) : bv1;

function {:bvbuiltin "(_ extract 31 0)"} otherfile.GET_LOWER32(p1: bv64) : bv32;

function {:bvbuiltin "(_ extract 15 0)"} otherfile.GET_LOWER16(p1: bv32) : bv16;

function {:bvbuiltin "(_ extract 7 0)"} otherfile.GET_LOWER8(p1: bv16) : bv8;

function {:bvbuiltin "(_ extract 7 0)"} otherfile.GET_LOWER8_32(p1: bv32) : bv8;

function {:bvbuiltin "(_ extract 7 0)"} otherfile.GET_LOWER8_64(p1: bv64) : bv8;

function {:bvbuiltin "(_ extract 15 0)"} otherfile.GET_LOWER16_64(p1: bv64) : bv16;

function {:bvbuiltin "(_ extract 31 0)"} otherfile.GET_LOWER32_64(p1: bv64) : bv32;

function {:inline} otherfile.$charToByte(x: java_char) : java_byte
{
  otherfile.GET_LOWER8(x)
}

function {:inline} otherfile.$charToShort(x: java_char) : java_short
{
  otherfile.GET_LOWER16(otherfile.CONCAT16(0bv16, x))
}

function {:inline} otherfile.$charToInt(x: java_char) : java_int
{
  otherfile.CONCAT16(0bv16, x)
}

function {:inline} otherfile.$charToLong(x: java_char) : java_long
{
  otherfile.CONCAT32(0bv32, otherfile.CONCAT16(0bv16, x))
}

function {:inline} otherfile.$byteToChar(x: java_byte) : java_char
{
  (if otherfile.GET_MSB8(x) == 1bv1 then otherfile.CONCAT8(255bv8, x) else otherfile.CONCAT8(0bv8, x))
}

function {:inline} otherfile.$byteToShort(x: java_byte) : java_short
{
  (if otherfile.GET_MSB8(x) == 1bv1 then otherfile.CONCAT8(255bv8, x) else otherfile.CONCAT8(0bv8, x))
}

function {:inline} otherfile.$byteToInt(x: java_byte) : java_int
{
  (if otherfile.GET_MSB8(x) == 1bv1 then otherfile.CONCAT16(65535bv16, otherfile.CONCAT8(255bv8, x)) else otherfile.CONCAT16(0bv16, otherfile.CONCAT8(0bv8, x)))
}

function {:inline} otherfile.$byteToLong(x: java_byte) : java_long
{
  (if otherfile.GET_MSB8(x) == 1bv1 then otherfile.CONCAT32(4294967295bv32, otherfile.CONCAT16(65535bv16, otherfile.CONCAT8(255bv8, x))) else otherfile.CONCAT32(0bv32, otherfile.CONCAT16(0bv16, otherfile.CONCAT8(0bv8, x))))
}

function {:inline} otherfile.$shortToChar(x: java_short) : java_char
{
  x
}

function {:inline} otherfile.$shortToByte(x: java_short) : java_byte
{
  otherfile.GET_LOWER8(x)
}

function {:inline} otherfile.$shortToInt(x: java_short) : java_int
{
  (if otherfile.GET_MSB16(x) == 1bv1 then otherfile.CONCAT16(65535bv16, x) else otherfile.CONCAT16(0bv16, x))
}

function {:inline} otherfile.$shortToLong(x: java_short) : java_long
{
  (if otherfile.GET_MSB16(x) == 1bv1 then otherfile.CONCAT32(4294967295bv32, otherfile.CONCAT16(65535bv16, x)) else otherfile.CONCAT32(0bv32, otherfile.CONCAT16(0bv16, x)))
}

function {:inline} otherfile.$intToChar(x: java_int) : java_char
{
  otherfile.GET_LOWER16(x)
}

function {:inline} otherfile.$intToByte(x: java_int) : java_byte
{
  otherfile.GET_LOWER8_32(x)
}

function {:inline} otherfile.$intToShort(x: java_int) : java_short
{
  otherfile.GET_LOWER16(x)
}

function {:inline} otherfile.$intToLong(x: java_int) : java_long
{
  (if otherfile.GET_MSB32(x) == 1bv1 then otherfile.CONCAT32(4294967295bv32, x) else otherfile.CONCAT32(0bv32, x))
}

function {:inline} otherfile.$longToChar(x: java_long) : java_char
{
  otherfile.GET_LOWER16_64(x)
}

function {:inline} otherfile.$longToByte(x: java_long) : java_byte
{
  otherfile.GET_LOWER8_64(x)
}

function {:inline} otherfile.$longToShort(x: java_long) : java_short
{
  otherfile.GET_LOWER16_64(x)
}

function {:inline} otherfile.$longToInt(x: java_long) : java_int
{
  otherfile.GET_LOWER32_64(x)
}

function {:inline} otherfile.$bintToByte(x: bv8) : java_byte
{
  x
}

function {:inline} otherfile.$bintToShort(x: bv16) : java_short
{
  x
}

function {:inline} otherfile.$bintToInt(x: bv32) : java_int
{
  x
}

function {:inline} otherfile.$bintToLong(x: bv64) : java_long
{
  x
}

function {:inline} otherfile.$bintToChar(x: bv16) : java_char
{
  x
}

function otherfile.$charToFloat(x: java_char) : java_float;

function otherfile.$charToDouble(x: java_char) : java_double;

function otherfile.$byteToFloat(x: java_byte) : java_float;

function otherfile.$byteToDouble(x: java_byte) : java_double;

function otherfile.$shortToFloat(x: java_short) : java_float;

function otherfile.$shortToDouble(x: java_short) : java_double;

function otherfile.$intToFloat(x: java_int) : java_float;

function otherfile.$intToDouble(x: java_int) : java_double;

function otherfile.$longToFloat(x: java_long) : java_float;

function otherfile.$longToDouble(x: java_long) : java_double;

function otherfile.$floatToChar(x: java_float) : java_char;

function otherfile.$doubleToChar(x: java_double) : java_char;

function otherfile.$floatToByte(x: java_float) : java_byte;

function otherfile.$doubleToByte(x: java_double) : java_byte;

function otherfile.$floatToShort(x: java_float) : java_short;

function otherfile.$doubleToShort(x: java_double) : java_short;

function otherfile.$floatToInt(x: java_float) : java_int;

function otherfile.$doubleToInt(x: java_double) : java_int;

function otherfile.$floatToLong(x: java_float) : java_long;

function otherfile.$doubleToLong(x: java_double) : java_long;

axiom (forall c: javaType :: { otherfile.$extends(c, c) } otherfile.$extends(c, c));

axiom (forall a: javaType, b: javaType, c: javaType :: { otherfile.$extends(a, b), otherfile.$extends(b, c) } otherfile.$extends(a, b) && otherfile.$extends(b, c) ==> otherfile.$extends(a, c));

axiom (forall a: javaType, b: javaType :: { otherfile.$extends(a, b), otherfile.$extends(b, a) } otherfile.$extends(a, b) && otherfile.$extends(b, a) ==> a == b);

axiom (forall h: $heap_type :: otherfile.$good_heap(h) ==> (forall t: javaType :: otherfile.$extends(h[otherfile.$null][otherfile.$type], t)));

axiom (forall h: [ref]java_int :: otherfile.$goodArrSizeHeap(h) ==> (forall r: ref :: otherfile.$geInt(h[r], otherfile.INT_ZERO)));

axiom otherfile.FLOAT_ONE == otherfile.$realToFloat(0e0);

axiom otherfile.FLOAT_ZERO == otherfile.$realToFloat(1e0);

axiom otherfile.DOUBLE_ZERO == otherfile.$realToDouble(0e0);

axiom otherfile.DOUBLE_ONE == otherfile.$realToDouble(1e0);

axiom otherfile.CHAR_DEFAULT == 0bv16;

axiom otherfile.CHAR_MIN == 0bv16;

axiom otherfile.CHAR_MAX == 65535bv16;

axiom otherfile.BYTE_DEFAULT == 0bv8;

axiom otherfile.BYTE_MIN == 128bv8;

axiom otherfile.BYTE_MAX == 127bv8;

axiom otherfile.BYTE_ZERO == 0bv8;

axiom otherfile.BYTE_ONE == 1bv8;

axiom otherfile.SHORT_DEFAULT == 0bv16;

axiom otherfile.SHORT_MIN == 32768bv16;

axiom otherfile.SHORT_MAX == 32767bv16;

axiom otherfile.SHORT_ZERO == 0bv16;

axiom otherfile.SHORT_ONE == 1bv16;

axiom otherfile.INT_DEFAULT == 0bv32;

axiom otherfile.INT_MIN == 2147483648bv32;

axiom otherfile.INT_MAX == 2147483647bv32;

axiom otherfile.INT_ONE == 1bv32;

axiom otherfile.INT_ZERO == 0bv32;

axiom otherfile.INT_NEG_ONE == 4294967295bv32;

axiom otherfile.LONG_DEFAULT == 0bv64;

axiom otherfile.LONG_MIN == 9223372036854775808bv64;

axiom otherfile.LONG_MAX == 9223372036854775807bv64;

axiom otherfile.LONG_ZERO == 0bv64;

axiom otherfile.LONG_ONE == 1bv64;

axiom otherfile.$extends(otherfile.benchmarks.REVE.limit2.Neq.SameV, otherfile.Object);

procedure {:prefix "otherfile"} otherfile.$initIntArray($obj: ref);
  modifies otherfile.$intArrHeap;
  free ensures (forall i: java_int :: otherfile.$leInt(otherfile.INT_MIN, i) && otherfile.$leInt(i, otherfile.INT_MAX) ==> otherfile.$intArrHeap[$obj][i] == otherfile.INT_ZERO);
  free ensures (forall o: ref :: o != $obj ==> old(otherfile.$intArrHeap)[o] == otherfile.$intArrHeap[o]);
  free ensures otherfile.$intArrHeap == _uf_otherfile.$initIntArray_otherfile.$intArrHeap($obj, old(otherfile.$intArrHeap));



procedure {:prefix "otherfile"} otherfile.$new(obj_type: javaType) returns ($obj: ref);
  modifies otherfile.$heap;
  free ensures old(otherfile.$heap)[$obj][otherfile.$alloc] <==> false;
  free ensures (forall<T> o: ref, f: Field T :: { otherfile.$heap[o][f] } o != $obj ==> otherfile.$heap[o][f] == old(otherfile.$heap)[o][f]);
  free ensures otherfile.$heap[$obj][otherfile.$type] == obj_type;
  free ensures $obj != otherfile.$null;
  free ensures otherfile.$heap[$obj][otherfile.$alloc] <==> true;
  free ensures $obj == _uf_otherfile.$new_$obj(obj_type, old(otherfile.$heap));
  free ensures otherfile.$heap == _uf_otherfile.$new_otherfile.$heap(obj_type, old(otherfile.$heap));



procedure {:prefix "otherfile"} otherfile.Object$clone$LObject$LObject($this: ref) returns ($other: ref);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures otherfile.$heap[$other][otherfile.$alloc] <==> true;
  free ensures otherfile.$heap[$other][otherfile.$type] == otherfile.$heap[$this][otherfile.$type];
  free ensures $other != otherfile.$null;
  free ensures $other == _uf_otherfile.Object$clone$LObject$LObject_$other($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$heap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$arrSizeHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringSizeHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$boolArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$refArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$floatArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$doubleArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$intArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$charArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$byteArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$shortArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$longArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringValueHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:prefix "otherfile"} otherfile.$initStringValue($obj: ref);
  modifies otherfile.$stringValueHeap;
  free ensures (forall o: ref :: o != $obj ==> old(otherfile.$stringValueHeap)[o] == otherfile.$stringValueHeap[o]);
  free ensures (forall i: java_int :: otherfile.$leInt(otherfile.INT_MIN, i) && otherfile.$leInt(i, otherfile.INT_MAX) ==> otherfile.$stringValueHeap[$obj][i] == otherfile.CHAR_MIN);
  free ensures otherfile.$stringValueHeap == _uf_otherfile.$initStringValue_otherfile.$stringValueHeap($obj, old(otherfile.$stringValueHeap));



procedure {:prefix "otherfile"} otherfile.String$charAt$$lp$I$rp$$C($this: ref, $index: java_int) returns ($return: java_char, $exception: ref);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures otherfile.$geInt($index, otherfile.INT_ZERO) && otherfile.$ltInt($index, otherfile.$stringSizeHeap[$this]) ==> $return == otherfile.$stringValueHeap[$this][$index];
  free ensures otherfile.$leInt($index, otherfile.INT_ZERO) || otherfile.$geInt($index, otherfile.$stringSizeHeap[$this]) ==> $exception != otherfile.$null;
  free ensures $return == _uf_otherfile.String$charAt$$lp$I$rp$$C_$return($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures $exception == _uf_otherfile.String$charAt$$lp$I$rp$$C_$exception($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$heap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$arrSizeHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringSizeHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$boolArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$refArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$floatArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$doubleArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$intArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$charArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$byteArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$shortArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$longArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringValueHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:prefix "otherfile"} otherfile.String$compareTo$I($this: ref, $other: ref) returns ($return: java_int);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures $return == _uf_otherfile.String$compareTo$I_$return($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.String$compareTo$I_otherfile.$heap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.String$compareTo$I_otherfile.$arrSizeHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.String$compareTo$I_otherfile.$stringSizeHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$boolArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$refArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$floatArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$doubleArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$intArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$charArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$byteArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$shortArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$longArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.String$compareTo$I_otherfile.$stringValueHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:inline 1} otherfile.Character$getType$$lp$C$rp$$I($in_parameter__0: java_char) returns ($return: java_int, $exception: ref);
  free ensures $return == _uf_otherfile.Character$getType$$lp$C$rp$$I_$return($in_parameter__0);
  free ensures $exception == _uf_otherfile.Character$getType$$lp$C$rp$$I_$exception($in_parameter__0);



procedure {:prefix "otherfile"} otherfile.benchmarks.REVE.limit2.Neq.SameV$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref);
  modifies otherfile.$refArrHeap, otherfile.$arrSizeHeap, otherfile.$stringValueHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$charArrHeap, otherfile.$floatArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$heap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$byteArrHeap;



procedure {:prefix "otherfile"} otherfile.Object$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref);
  modifies otherfile.$refArrHeap, otherfile.$arrSizeHeap, otherfile.$stringValueHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$charArrHeap, otherfile.$floatArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$heap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$byteArrHeap;



procedure {:prefix "otherfile"} otherfile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I($this: ref, $in_parameter__0: java_int) returns ($return: java_int, $exception: ref);



implementation {:inline 1} otherfile.Character$getType$$lp$C$rp$$I($in_parameter__0: java_char) returns ($return: java_int, $exception: ref)
{
  anon0:
    $return := otherfile.getType($in_parameter__0);
    $exception := otherfile.$null;
    return;
}



implementation otherfile.benchmarks.REVE.limit2.Neq.SameV$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref)
{
  var l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$: ref;

  anon0:
    $exception := otherfile.$null;
    assume {:sourceloc "SameV.java", -1, -1, -1, -1} $this != otherfile.$null;
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$ := $this;
    assert {:sourceloc "SameV.java", 2, -1, -1, -1} true;
    call $exception := otherfile.Object$$la$init$ra$$$lp$$rp$$V(l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$);
    goto anon3_Then, anon3_Else;

  anon3_Then:
    assume {:partition} $exception != otherfile.$null;
    return;

  anon3_Else:
    assume {:partition} $exception == otherfile.$null;
    goto anon2;

  anon2:
    assert {:sourceloc "SameV.java", 2, -1, -1, -1} true;
    goto block1;

  block1:
    return;
}



implementation otherfile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I($this: ref, $in_parameter__0: java_int) returns ($return: java_int, $exception: ref)
{
  var l2#2$$lp$I$rp$: java_int;
  var l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$: ref;
  var l2$$lp$Z$rp$: bool;
  var l1$$lp$I$rp$: java_int;
  var $stack3$$lp$I$rp$: java_int;

  anon0:
    $return := 0bv32;
    $exception := otherfile.$null;
    assume {:sourceloc "SameV.java", -1, -1, -1, -1} $this != otherfile.$null;
    assume otherfile.$leInt(otherfile.INT_MIN, $in_parameter__0) && otherfile.$leInt($in_parameter__0, otherfile.INT_MAX);
    assume otherfile.$leInt(otherfile.INT_MIN, $return) && otherfile.$leInt($return, otherfile.INT_MAX);
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$ := $this;
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l1$$lp$I$rp$ := $in_parameter__0;
    assert {:sourceloc "SameV.java", 5, -1, -1, -1} true;
    l2$$lp$Z$rp$ := otherfile.$intToBool(0bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} true;
    goto anon9_Then, anon9_Else;

  anon9_Then:
    assume {:partition} otherfile.$gtInt(l1$$lp$I$rp$, 1bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} {:comment "thenblock"} true;
    goto block2;

  anon9_Else:
    assume {:partition} !otherfile.$gtInt(l1$$lp$I$rp$, 1bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} {:comment "elseblock"} true;
    goto anon3;

  anon3:
    assert {:sourceloc "SameV.java", 7, -1, -1, -1} true;
    l2#2$$lp$I$rp$ := l1$$lp$I$rp$;
    assert {:sourceloc "SameV.java", 7, -1, -1, -1} true;
    goto block3;

  block2:
    assert {:sourceloc "SameV.java", 9, -1, -1, -1} true;
    $stack3$$lp$I$rp$ := otherfile.$subInt(l1$$lp$I$rp$, 1bv32);
    assert {:sourceloc "SameV.java", 9, -1, -1, -1} true;
    call l2#2$$lp$I$rp$, $exception := otherfile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I(l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$, $stack3$$lp$I$rp$);
    goto anon10_Then, anon10_Else;

  anon10_Then:
    assume {:partition} $exception != otherfile.$null;
    return;

  anon10_Else:
    assume {:partition} $exception == otherfile.$null;
    goto anon5;

  anon5:
    assume otherfile.$leInt(otherfile.INT_MIN, l2#2$$lp$I$rp$) && otherfile.$leInt(l2#2$$lp$I$rp$, otherfile.INT_MAX);
    assert {:sourceloc "SameV.java", 10, -1, -1, -1} true;
    l2#2$$lp$I$rp$ := otherfile.$addInt(l1$$lp$I$rp$, l2#2$$lp$I$rp$);
    assert {:sourceloc "SameV.java", 11, -1, -1, -1} true;
    goto anon11_Then, anon11_Else;

  anon11_Then:
    assume {:partition} l1$$lp$I$rp$ != 10bv32;
    assert {:sourceloc "SameV.java", 11, -1, -1, -1} {:comment "thenblock"} true;
    goto block3;

  anon11_Else:
    assume {:partition} l1$$lp$I$rp$ == 10bv32;
    assert {:sourceloc "SameV.java", 11, -1, -1, -1} {:comment "elseblock"} true;
    goto anon8;

  anon8:
    assert {:sourceloc "SameV.java", 12, -1, -1, -1} true;
    l2#2$$lp$I$rp$ := 10bv32;
    goto block3;

  block3:
    assert {:sourceloc "SameV.java", 15, -1, -1, -1} true;
    $return := l2#2$$lp$I$rp$;
    goto block4;

  block4:
    return;
}



var reffile.$heap: $heap_type where otherfile.$good_heap(reffile.$heap);

var reffile.$arrSizeHeap: [ref]java_int where otherfile.$goodArrSizeHeap(reffile.$arrSizeHeap);

var reffile.$stringSizeHeap: stringSizeHeap_type;

var reffile.$boolArrHeap: boolArrHeap_type;

var reffile.$refArrHeap: refArrHeap_type;

var reffile.$floatArrHeap: floatArrHeap_type;

var reffile.$doubleArrHeap: doubleArrHeap_type;

var reffile.$intArrHeap: intArrHeap_type;

var reffile.$charArrHeap: charArrHeap_type;

var reffile.$byteArrHeap: byteArrHeap_type;

var reffile.$shortArrHeap: shortArrHeap_type;

var reffile.$longArrHeap: longArrHeap_type;

var reffile.$stringValueHeap: stringValueHeap_type;

const unique reffile.$null: ref;

const unique reffile.$type: Field javaType;

const unique reffile.$alloc: Field bool;

const unique reffile.$charArrayType: javaType;

const unique reffile.$boolArrayType: javaType;

const unique reffile.$byteArrayType: javaType;

const unique reffile.$shortArrayType: javaType;

const unique reffile.$intArrayType: javaType;

const unique reffile.$longArrayType: javaType;

const unique reffile.$floatArrayType: javaType;

const unique reffile.$doubleArrayType: javaType;

const reffile.FLOAT_ONE: java_float;

const reffile.FLOAT_ZERO: java_float;

const reffile.DOUBLE_ZERO: java_double;

const reffile.DOUBLE_ONE: java_double;

const reffile.CHAR_DEFAULT: java_char;

const reffile.CHAR_MIN: java_char;

const reffile.CHAR_MAX: java_char;

const reffile.BYTE_DEFAULT: java_byte;

const reffile.BYTE_MIN: java_byte;

const reffile.BYTE_MAX: java_byte;

const reffile.BYTE_ZERO: java_byte;

const reffile.BYTE_ONE: java_byte;

const reffile.SHORT_DEFAULT: java_short;

const reffile.SHORT_MIN: java_short;

const reffile.SHORT_MAX: java_short;

const reffile.SHORT_ZERO: java_short;

const reffile.SHORT_ONE: java_short;

const reffile.INT_DEFAULT: java_int;

const reffile.INT_MIN: java_int;

const reffile.INT_MAX: java_int;

const reffile.INT_ONE: java_int;

const reffile.INT_ZERO: java_int;

const reffile.INT_NEG_ONE: java_int;

const reffile.LONG_DEFAULT: java_long;

const reffile.LONG_MIN: java_long;

const reffile.LONG_MAX: java_long;

const reffile.LONG_ZERO: java_long;

const reffile.LONG_ONE: java_long;

const {:sourceloc "SameV.java", -1, -1, -1, -1} unique reffile.Object: javaType;

const {:sourceloc "SameV.java", -1, -1, -1, -1} unique reffile.benchmarks.REVE.limit2.Neq.SameV: javaType;

axiom (forall p1: java_char, p2: java_char :: { otherfile.$shlChar(p1, p2): java_char } otherfile.$shlChar(p1, p2): java_char == otherfile.LEFT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));

axiom (forall p1: java_char, p2: java_char :: { otherfile.$shrChar(p1, p2): java_char } otherfile.$shrChar(p1, p2): java_char == otherfile.RIGHT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));

axiom (forall p1: java_char, p2: java_char :: { otherfile.$ushrChar(p1, p2): java_char } otherfile.$ushrChar(p1, p2): java_char == otherfile.LRIGHT_SHIFT_CHAR(p1, otherfile.$bitAndChar(p2, 31bv16)));

axiom (forall c: javaType :: { otherfile.$extends(c, c) } otherfile.$extends(c, c));

axiom (forall a: javaType, b: javaType, c: javaType :: { otherfile.$extends(a, b), otherfile.$extends(b, c) } otherfile.$extends(a, b) && otherfile.$extends(b, c) ==> otherfile.$extends(a, c));

axiom (forall a: javaType, b: javaType :: { otherfile.$extends(a, b), otherfile.$extends(b, a) } otherfile.$extends(a, b) && otherfile.$extends(b, a) ==> a == b);

axiom (forall h: $heap_type :: otherfile.$good_heap(h) ==> (forall t: javaType :: otherfile.$extends(h[otherfile.$null][otherfile.$type], t)));

axiom (forall h: [ref]java_int :: otherfile.$goodArrSizeHeap(h) ==> (forall r: ref :: otherfile.$geInt(h[r], otherfile.INT_ZERO)));

axiom otherfile.FLOAT_ONE == otherfile.$realToFloat(0e0);

axiom otherfile.FLOAT_ZERO == otherfile.$realToFloat(1e0);

axiom otherfile.DOUBLE_ZERO == otherfile.$realToDouble(0e0);

axiom otherfile.DOUBLE_ONE == otherfile.$realToDouble(1e0);

axiom otherfile.CHAR_DEFAULT == 0bv16;

axiom otherfile.CHAR_MIN == 0bv16;

axiom otherfile.CHAR_MAX == 65535bv16;

axiom otherfile.BYTE_DEFAULT == 0bv8;

axiom otherfile.BYTE_MIN == 128bv8;

axiom otherfile.BYTE_MAX == 127bv8;

axiom otherfile.BYTE_ZERO == 0bv8;

axiom otherfile.BYTE_ONE == 1bv8;

axiom otherfile.SHORT_DEFAULT == 0bv16;

axiom otherfile.SHORT_MIN == 32768bv16;

axiom otherfile.SHORT_MAX == 32767bv16;

axiom otherfile.SHORT_ZERO == 0bv16;

axiom otherfile.SHORT_ONE == 1bv16;

axiom otherfile.INT_DEFAULT == 0bv32;

axiom otherfile.INT_MIN == 2147483648bv32;

axiom otherfile.INT_MAX == 2147483647bv32;

axiom otherfile.INT_ONE == 1bv32;

axiom otherfile.INT_ZERO == 0bv32;

axiom otherfile.INT_NEG_ONE == 4294967295bv32;

axiom otherfile.LONG_DEFAULT == 0bv64;

axiom otherfile.LONG_MIN == 9223372036854775808bv64;

axiom otherfile.LONG_MAX == 9223372036854775807bv64;

axiom otherfile.LONG_ZERO == 0bv64;

axiom otherfile.LONG_ONE == 1bv64;

axiom otherfile.$extends(otherfile.benchmarks.REVE.limit2.Neq.SameV, otherfile.Object);

procedure {:prefix "reffile"} reffile.$initIntArray($obj: ref);
  modifies otherfile.$intArrHeap;
  free ensures (forall o: ref :: o != $obj ==> old(otherfile.$intArrHeap)[o] == otherfile.$intArrHeap[o]);
  free ensures (forall i: java_int :: otherfile.$leInt(otherfile.INT_MIN, i) && otherfile.$leInt(i, otherfile.INT_MAX) ==> otherfile.$intArrHeap[$obj][i] == otherfile.INT_ZERO);
  free ensures otherfile.$intArrHeap == _uf_otherfile.$initIntArray_otherfile.$intArrHeap($obj, old(otherfile.$intArrHeap));



procedure {:prefix "reffile"} reffile.$new(obj_type: javaType) returns ($obj: ref);
  modifies otherfile.$heap;
  free ensures otherfile.$heap[$obj][otherfile.$type] == obj_type;
  free ensures $obj != otherfile.$null;
  free ensures old(otherfile.$heap)[$obj][otherfile.$alloc] <==> false;
  free ensures (forall<T> o: ref, f: Field T :: { otherfile.$heap[o][f] } o != $obj ==> otherfile.$heap[o][f] == old(otherfile.$heap)[o][f]);
  free ensures otherfile.$heap[$obj][otherfile.$alloc] <==> true;
  free ensures $obj == _uf_otherfile.$new_$obj(obj_type, old(otherfile.$heap));
  free ensures otherfile.$heap == _uf_otherfile.$new_otherfile.$heap(obj_type, old(otherfile.$heap));



procedure {:prefix "reffile"} reffile.Object$clone$LObject$LObject($this: ref) returns ($other: ref);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures otherfile.$heap[$other][otherfile.$alloc] <==> true;
  free ensures otherfile.$heap[$other][otherfile.$type] == otherfile.$heap[$this][otherfile.$type];
  free ensures $other != otherfile.$null;
  free ensures $other == _uf_otherfile.Object$clone$LObject$LObject_$other($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$heap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$arrSizeHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringSizeHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$boolArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$refArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$floatArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$doubleArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$intArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$charArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$byteArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$shortArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$longArrHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringValueHeap($this, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:prefix "reffile"} reffile.$initStringValue($obj: ref);
  modifies otherfile.$stringValueHeap;
  free ensures (forall i: java_int :: otherfile.$leInt(otherfile.INT_MIN, i) && otherfile.$leInt(i, otherfile.INT_MAX) ==> otherfile.$stringValueHeap[$obj][i] == otherfile.CHAR_MIN);
  free ensures (forall o: ref :: o != $obj ==> old(otherfile.$stringValueHeap)[o] == otherfile.$stringValueHeap[o]);
  free ensures otherfile.$stringValueHeap == _uf_otherfile.$initStringValue_otherfile.$stringValueHeap($obj, old(otherfile.$stringValueHeap));



procedure {:prefix "reffile"} reffile.String$charAt$$lp$I$rp$$C($this: ref, $index: java_int) returns ($return: java_char, $exception: ref);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures otherfile.$geInt($index, otherfile.INT_ZERO) && otherfile.$ltInt($index, otherfile.$stringSizeHeap[$this]) ==> $return == otherfile.$stringValueHeap[$this][$index];
  free ensures otherfile.$leInt($index, otherfile.INT_ZERO) || otherfile.$geInt($index, otherfile.$stringSizeHeap[$this]) ==> $exception != otherfile.$null;
  free ensures $return == _uf_otherfile.String$charAt$$lp$I$rp$$C_$return($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures $exception == _uf_otherfile.String$charAt$$lp$I$rp$$C_$exception($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$heap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$arrSizeHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringSizeHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$boolArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$refArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$floatArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$doubleArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$intArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$charArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$byteArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$shortArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$longArrHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringValueHeap($this, $index, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:prefix "reffile"} reffile.String$compareTo$I($this: ref, $other: ref) returns ($return: java_int);
  modifies otherfile.$heap, otherfile.$arrSizeHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$refArrHeap, otherfile.$floatArrHeap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$charArrHeap, otherfile.$byteArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$stringValueHeap;
  free ensures $return == _uf_otherfile.String$compareTo$I_$return($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$heap == _uf_otherfile.String$compareTo$I_otherfile.$heap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$arrSizeHeap == _uf_otherfile.String$compareTo$I_otherfile.$arrSizeHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringSizeHeap == _uf_otherfile.String$compareTo$I_otherfile.$stringSizeHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$boolArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$boolArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$refArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$refArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$floatArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$floatArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$doubleArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$doubleArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$intArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$intArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$charArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$charArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$byteArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$byteArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$shortArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$shortArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$longArrHeap == _uf_otherfile.String$compareTo$I_otherfile.$longArrHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));
  free ensures otherfile.$stringValueHeap == _uf_otherfile.String$compareTo$I_otherfile.$stringValueHeap($this, $other, old(otherfile.$heap), old(otherfile.$arrSizeHeap), old(otherfile.$stringSizeHeap), old(otherfile.$boolArrHeap), old(otherfile.$refArrHeap), old(otherfile.$floatArrHeap), old(otherfile.$doubleArrHeap), old(otherfile.$intArrHeap), old(otherfile.$charArrHeap), old(otherfile.$byteArrHeap), old(otherfile.$shortArrHeap), old(otherfile.$longArrHeap), old(otherfile.$stringValueHeap));



procedure {:inline 1} reffile.Character$getType$$lp$C$rp$$I($in_parameter__0: java_char) returns ($return: java_int, $exception: ref);
  free ensures $return == _uf_otherfile.Character$getType$$lp$C$rp$$I_$return($in_parameter__0);
  free ensures $exception == _uf_otherfile.Character$getType$$lp$C$rp$$I_$exception($in_parameter__0);



procedure {:prefix "reffile"} reffile.benchmarks.REVE.limit2.Neq.SameV$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref);
  modifies otherfile.$refArrHeap, otherfile.$arrSizeHeap, otherfile.$stringValueHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$charArrHeap, otherfile.$floatArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$heap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$byteArrHeap;



procedure {:prefix "reffile"} reffile.Object$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref);
  modifies otherfile.$refArrHeap, otherfile.$arrSizeHeap, otherfile.$stringValueHeap, otherfile.$stringSizeHeap, otherfile.$boolArrHeap, otherfile.$charArrHeap, otherfile.$floatArrHeap, otherfile.$shortArrHeap, otherfile.$longArrHeap, otherfile.$heap, otherfile.$doubleArrHeap, otherfile.$intArrHeap, otherfile.$byteArrHeap;



procedure {:prefix "reffile"} reffile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I($this: ref, $in_parameter__0: java_int) returns ($return: java_int, $exception: ref);



implementation {:inline 1} reffile.Character$getType$$lp$C$rp$$I($in_parameter__0: java_char) returns ($return: java_int, $exception: ref)
{
  anon0:
    $return := otherfile.getType($in_parameter__0);
    $exception := otherfile.$null;
    return;
}



implementation reffile.benchmarks.REVE.limit2.Neq.SameV$$la$init$ra$$$lp$$rp$$V($this: ref) returns ($exception: ref)
{
  var l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$: ref;

  anon0:
    $exception := otherfile.$null;
    assume {:sourceloc "SameV.java", -1, -1, -1, -1} $this != otherfile.$null;
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$ := $this;
    assert {:sourceloc "SameV.java", 2, -1, -1, -1} true;
    call $exception := reffile.Object$$la$init$ra$$$lp$$rp$$V(l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$);
    goto anon3_Then, anon3_Else;

  anon3_Then:
    assume {:partition} $exception != otherfile.$null;
    return;

  anon3_Else:
    assume {:partition} $exception == otherfile.$null;
    goto anon2;

  anon2:
    assert {:sourceloc "SameV.java", 2, -1, -1, -1} true;
    goto block1;

  block1:
    return;
}



implementation reffile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I($this: ref, $in_parameter__0: java_int) returns ($return: java_int, $exception: ref)
{
  var l1$$lp$I$rp$: java_int;
  var l2$$lp$Z$rp$: bool;
  var l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$: ref;
  var $stack3$$lp$I$rp$: java_int;
  var l2#2$$lp$I$rp$: java_int;

  anon0:
    $return := 0bv32;
    $exception := otherfile.$null;
    assume {:sourceloc "SameV.java", -1, -1, -1, -1} $this != otherfile.$null;
    assume otherfile.$leInt(otherfile.INT_MIN, $return) && otherfile.$leInt($return, otherfile.INT_MAX);
    assume otherfile.$leInt(otherfile.INT_MIN, $in_parameter__0) && otherfile.$leInt($in_parameter__0, otherfile.INT_MAX);
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$ := $this;
    assert {:sourceloc "SameV.java", -1, -1, -1, -1} true;
    l1$$lp$I$rp$ := $in_parameter__0;
    assert {:sourceloc "SameV.java", 5, -1, -1, -1} true;
    l2$$lp$Z$rp$ := otherfile.$intToBool(0bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} true;
    goto anon6_Then, anon6_Else;

  anon6_Then:
    assume {:partition} otherfile.$gtInt(l1$$lp$I$rp$, 0bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} {:comment "thenblock"} true;
    goto block2;

  anon6_Else:
    assume {:partition} !otherfile.$gtInt(l1$$lp$I$rp$, 0bv32);
    assert {:sourceloc "SameV.java", 6, -1, -1, -1} {:comment "elseblock"} true;
    goto anon3;

  anon3:
    assert {:sourceloc "SameV.java", 7, -1, -1, -1} true;
    l2#2$$lp$I$rp$ := l1$$lp$I$rp$;
    assert {:sourceloc "SameV.java", 7, -1, -1, -1} true;
    goto block3;

  block2:
    assert {:sourceloc "SameV.java", 9, -1, -1, -1} true;
    $stack3$$lp$I$rp$ := otherfile.$subInt(l1$$lp$I$rp$, 1bv32);
    assert {:sourceloc "SameV.java", 9, -1, -1, -1} true;
    call l2#2$$lp$I$rp$, $exception := reffile.benchmarks.REVE.limit2.Neq.SameV$f$$lp$I$rp$$I(l0$$lp$Lbenchmarks.REVE.limit2.Neq.SameV$$rp$, $stack3$$lp$I$rp$);
    goto anon7_Then, anon7_Else;

  anon7_Then:
    assume {:partition} $exception != otherfile.$null;
    return;

  anon7_Else:
    assume {:partition} $exception == otherfile.$null;
    goto anon5;

  anon5:
    assume otherfile.$leInt(otherfile.INT_MIN, l2#2$$lp$I$rp$) && otherfile.$leInt(l2#2$$lp$I$rp$, otherfile.INT_MAX);
    assert {:sourceloc "SameV.java", 10, -1, -1, -1} true;
    l2#2$$lp$I$rp$ := otherfile.$addInt(l1$$lp$I$rp$, l2#2$$lp$I$rp$);
    goto block3;

  block3:
    assert {:sourceloc "SameV.java", 12, -1, -1, -1} true;
    $return := l2#2$$lp$I$rp$;
    goto block4;

  block4:
    return;
}



type ref;

type javaType;

type Field _;

type $heap_type = <$GenericType__0>[ref][Field $GenericType__0]$GenericType__0;

type stringSizeHeap_type = [ref]java_int;

type boolArrHeap_type = [ref][java_int]bool;

type refArrHeap_type = [ref][java_int]ref;

type floatArrHeap_type = [ref][java_int]java_float;

type doubleArrHeap_type = [ref][java_int]java_double;

type intArrHeap_type = [ref][java_int]java_int;

type charArrHeap_type = [ref][java_int]java_char;

type byteArrHeap_type = [ref][java_int]java_byte;

type shortArrHeap_type = [ref][java_int]java_short;

type longArrHeap_type = [ref][java_int]java_long;

type stringValueHeap_type = [ref][java_int]java_char;

type java_float = real;

type java_double = real;

type java_byte = bv8;

type java_short = bv16;

type java_int = bv32;

type java_long = bv64;

type java_char = bv16;

function _uf_otherfile.$initIntArray_otherfile.$intArrHeap(arg_0: ref, arg_1: intArrHeap_type) : intArrHeap_type;

function _uf_reffile.$initIntArray_otherfile.$intArrHeap(arg_0: ref, arg_1: intArrHeap_type) : intArrHeap_type;

function _uf_otherfile.$new_$obj(arg_0: javaType, arg_1: $heap_type) : ref;

function _uf_otherfile.$new_otherfile.$heap(arg_0: javaType, arg_1: $heap_type) : $heap_type;

function _uf_reffile.$new_$obj(arg_0: javaType, arg_1: $heap_type) : ref;

function _uf_reffile.$new_otherfile.$heap(arg_0: javaType, arg_1: $heap_type) : $heap_type;

function _uf_otherfile.Object$clone$LObject$LObject_$other(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : ref;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$heap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : $heap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$arrSizeHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : [ref]java_int;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringSizeHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : stringSizeHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$boolArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : boolArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$refArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : refArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$floatArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : floatArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$doubleArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : doubleArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$intArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : intArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$charArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : charArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$byteArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : byteArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$shortArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : shortArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$longArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : longArrHeap_type;

function _uf_otherfile.Object$clone$LObject$LObject_otherfile.$stringValueHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : stringValueHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_$other(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : ref;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$heap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : $heap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$arrSizeHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : [ref]java_int;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$stringSizeHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : stringSizeHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$boolArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : boolArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$refArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : refArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$floatArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : floatArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$doubleArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : doubleArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$intArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : intArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$charArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : charArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$byteArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : byteArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$shortArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : shortArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$longArrHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : longArrHeap_type;

function _uf_reffile.Object$clone$LObject$LObject_otherfile.$stringValueHeap(arg_0: ref, arg_1: $heap_type, arg_2: [ref]java_int, arg_3: stringSizeHeap_type, arg_4: boolArrHeap_type, arg_5: refArrHeap_type, arg_6: floatArrHeap_type, arg_7: doubleArrHeap_type, arg_8: intArrHeap_type, arg_9: charArrHeap_type, arg_10: byteArrHeap_type, arg_11: shortArrHeap_type, arg_12: longArrHeap_type, arg_13: stringValueHeap_type) : stringValueHeap_type;

function _uf_otherfile.$initStringValue_otherfile.$stringValueHeap(arg_0: ref, arg_1: stringValueHeap_type) : stringValueHeap_type;

function _uf_reffile.$initStringValue_otherfile.$stringValueHeap(arg_0: ref, arg_1: stringValueHeap_type) : stringValueHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_$return(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : java_char;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_$exception(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : ref;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$heap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : $heap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$arrSizeHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : [ref]java_int;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringSizeHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringSizeHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$boolArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : boolArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$refArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : refArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$floatArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : floatArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$doubleArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : doubleArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$intArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : intArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$charArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : charArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$byteArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : byteArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$shortArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : shortArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$longArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : longArrHeap_type;

function _uf_otherfile.String$charAt$$lp$I$rp$$C_otherfile.$stringValueHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringValueHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_$return(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : java_char;

function _uf_reffile.String$charAt$$lp$I$rp$$C_$exception(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : ref;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$heap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : $heap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$arrSizeHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : [ref]java_int;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$stringSizeHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringSizeHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$boolArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : boolArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$refArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : refArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$floatArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : floatArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$doubleArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : doubleArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$intArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : intArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$charArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : charArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$byteArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : byteArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$shortArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : shortArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$longArrHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : longArrHeap_type;

function _uf_reffile.String$charAt$$lp$I$rp$$C_otherfile.$stringValueHeap(arg_0: ref, arg_1: java_int, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringValueHeap_type;

function _uf_otherfile.String$compareTo$I_$return(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : java_int;

function _uf_otherfile.String$compareTo$I_otherfile.$heap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : $heap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$arrSizeHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : [ref]java_int;

function _uf_otherfile.String$compareTo$I_otherfile.$stringSizeHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringSizeHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$boolArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : boolArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$refArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : refArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$floatArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : floatArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$doubleArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : doubleArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$intArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : intArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$charArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : charArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$byteArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : byteArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$shortArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : shortArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$longArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : longArrHeap_type;

function _uf_otherfile.String$compareTo$I_otherfile.$stringValueHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringValueHeap_type;

function _uf_reffile.String$compareTo$I_$return(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : java_int;

function _uf_reffile.String$compareTo$I_otherfile.$heap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : $heap_type;

function _uf_reffile.String$compareTo$I_otherfile.$arrSizeHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : [ref]java_int;

function _uf_reffile.String$compareTo$I_otherfile.$stringSizeHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringSizeHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$boolArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : boolArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$refArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : refArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$floatArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : floatArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$doubleArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : doubleArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$intArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : intArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$charArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : charArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$byteArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : byteArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$shortArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : shortArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$longArrHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : longArrHeap_type;

function _uf_reffile.String$compareTo$I_otherfile.$stringValueHeap(arg_0: ref, arg_1: ref, arg_2: $heap_type, arg_3: [ref]java_int, arg_4: stringSizeHeap_type, arg_5: boolArrHeap_type, arg_6: refArrHeap_type, arg_7: floatArrHeap_type, arg_8: doubleArrHeap_type, arg_9: intArrHeap_type, arg_10: charArrHeap_type, arg_11: byteArrHeap_type, arg_12: shortArrHeap_type, arg_13: longArrHeap_type, arg_14: stringValueHeap_type) : stringValueHeap_type;

function _uf_otherfile.Character$getType$$lp$C$rp$$I_$return(arg_0: java_char) : java_int;

function _uf_otherfile.Character$getType$$lp$C$rp$$I_$exception(arg_0: java_char) : ref;

function _uf_reffile.Character$getType$$lp$C$rp$$I_$return(arg_0: java_char) : java_int;

function _uf_reffile.Character$getType$$lp$C$rp$$I_$exception(arg_0: java_char) : ref;

var Output_of_reffile.Character$getType$$lp$C$rp$$I_$return: java_int;

var Output_of_otherfile.Character$getType$$lp$C$rp$$I_$return: java_int;

var Output_of_reffile.Character$getType$$lp$C$rp$$I_$exception: ref;

var Output_of_otherfile.Character$getType$$lp$C$rp$$I_$exception: ref;

procedure EQ_CharactergetTypelpCrpI($in_parameter__0: java_char) returns (AA_TEMP50: bool, AA_TEMP51: bool);
  modifies Output_of_reffile.Character$getType$$lp$C$rp$$I_$return, Output_of_otherfile.Character$getType$$lp$C$rp$$I_$return, Output_of_reffile.Character$getType$$lp$C$rp$$I_$exception, Output_of_otherfile.Character$getType$$lp$C$rp$$I_$exception;
  ensures AA_TEMP51 && AA_TEMP50;



implementation EQ_CharactergetTypelpCrpI($in_parameter__0: java_char) returns (AA_TEMP50: bool, AA_TEMP51: bool)
{
  var AA_TEMP20: java_int;
  var AA_TEMP21: ref;
  var AA_TEMP30: java_char;
  var AA_TEMP40: java_char;
  var $return: java_int;
  var $exception: ref;

  AA_INSTR_EQ_BODY:
    AA_TEMP30 := $in_parameter__0;
    AA_TEMP40 := $in_parameter__0;
    call $return, $exception := reffile.Character$getType$$lp$C$rp$$I($in_parameter__0);
    AA_TEMP20 := $return;
    AA_TEMP21 := $exception;
    call $return, $exception := otherfile.Character$getType$$lp$C$rp$$I($in_parameter__0);
    Output_of_reffile.Character$getType$$lp$C$rp$$I_$return := AA_TEMP20;
    Output_of_otherfile.Character$getType$$lp$C$rp$$I_$return := $return;
    Output_of_reffile.Character$getType$$lp$C$rp$$I_$exception := AA_TEMP21;
    Output_of_otherfile.Character$getType$$lp$C$rp$$I_$exception := $exception;
    havoc AA_TEMP50, AA_TEMP51;
    AA_TEMP50, AA_TEMP51 := AA_TEMP50 || AA_TEMP20 == $return, AA_TEMP51 || AA_TEMP21 == $exception;
    assume {:captureState "final_state"} true;
    return;
}



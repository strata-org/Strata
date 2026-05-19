import Strata.MetaVerifier

open Strata

private def from_bytes_mod_order_wide_minimal_program : Strata.Program :=
#strata
program Boole;

 type Set (T : Type);
 function Seq_len<T> (s : Sequence T) : int {
  Sequence.length(s)
}
 function Seq_lib_insert<T> (s : Sequence T, i : int, val : T) : Sequence T {
  Sequence.append(Sequence.build(Sequence.take(s, i), val), Sequence.drop(s, i))
}
 function Seq_new<T> (len : int, f : int -> T) : Sequence T;
 function Seq_lib_map<T, U> (s : Sequence T, f : int -> T -> U) : Sequence U;
 function Seq_lib_map_values<T, U> (s : Sequence T, f : T -> U) : Sequence U;
 function Seq_lib_filter<T> (s : Sequence T, p : T -> bool) : Sequence T;
 function Seq_lib_sort_by<T> (s : Sequence T, less : T -> T -> bool) : Sequence T;
 function Seq_lib_to_set<T> (s : Sequence T) : Set T;
 function Set_finite<T> (s : Set T) : bool;
 datatype scalar {
  scalar_ctor(bytes : Sequence bv8)
};
 datatype scalar52 {
  scalar52_ctor(limbs : Sequence bv64)
};
 function Seq_subrange<A> (self : Sequence A, start_inclusive : int, end_exclusive : int) : Sequence A;
 function Array_spec_array_as_slice<T> (ar : Sequence T) : Sequence T;
 function Arithmetic_Power2_pow2 (e : int) : int;
 function is_uniform_bytes (bytes : Sequence bv8) : bool;
 function is_uniform_scalar (s : scalar) : bool;
 rec function bytes_seq_as_nat (bytes : Sequence bv8) : int
   decreases Sequence.length(bytes)
 {
   if Sequence.length(bytes) == 0 then 0 else (Sequence.select(bytes, 0) as_int) + Arithmetic_Power2_pow2(8) * bytes_seq_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))
 }
 ;
 function u8_32_as_nat (bytes : Sequence bv8) : int;
 function group_order () : int;
 function group_canonical (n : int) : int;
 rec function seq_as_nat_52 (limbs : Sequence bv64) : int
   decreases Sequence.length(limbs)
 {
   if Sequence.length(limbs) == 0 then 0 else (Sequence.select(limbs, 0) as_int) + seq_as_nat_52(Sequence.subrange(limbs, 1, Sequence.length(limbs))) * Arithmetic_Power2_pow2(52)
 }
 ;
 function limbs52_as_nat (limbs : Sequence bv64) : int {
  seq_as_nat_52(limbs)
}
 function scalar52_as_nat (s : scalar52) : int {
  limbs52_as_nat(Array_spec_array_as_slice(scalar52..limbs(s)))
}
 function limbs_bounded (s : scalar52) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(scalar52..limbs(s), i) < bv{64}(1) << bv{64}(52)
}
 function is_canonical_scalar52 (s : scalar52) : bool {
  limbs_bounded(s) && scalar52_as_nat(s) < group_order
}
 function is_canonical_scalar (s : scalar) : bool {
  u8_32_as_nat(scalar..bytes(s)) < group_order && Sequence.select(scalar..bytes(s), 31) <= bv{8}(127)
}
 function scalar_as_canonical (s : scalar) : int {
  group_canonical(u8_32_as_nat(scalar..bytes(s)))
}
 procedure Impl__2_clone (self : scalar52) returns (_pct_return : scalar52)
spec {
  ensures _pct_return == self;
  } {
  _pct_return := self;
  exit Impl__2_clone;
};
 procedure Impl__3_from_bytes_wide (bytes : Sequence bv8) returns (s : scalar52)
spec {
  ensures is_canonical_scalar52(s);
  ensures scalar52_as_nat(s) == group_canonical(bytes_seq_as_nat(bytes));
  } {
  assume false;
  s := scalar52_ctor(Sequence.of_bv64[bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0), bv{64}(0)]);
  exit Impl__3_from_bytes_wide;
};
 procedure Impl__3_pack (self : scalar52) returns (result : scalar)
spec {
  requires limbs_bounded(self);
  ensures u8_32_as_nat(scalar..bytes(result)) == scalar52_as_nat(self) mod Arithmetic_Power2_pow2(256);
  ensures scalar52_as_nat(self) < group_order ==> is_canonical_scalar(result);
  } {
  assume false;
  result := scalar_ctor(scalar..bytes(result));
  exit Impl__3_pack;
};
 procedure Impl__4_from_bytes_mod_order_wide (input : Sequence bv8) returns (result : scalar)
spec {
  ensures scalar_as_canonical(result) == group_canonical(bytes_seq_as_nat(input));
  ensures is_canonical_scalar(result);
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  var tmp1 : int;
  var tmp2 : int;
  var tmp3 : int;
  var tmp4 : int;
  var tmp5 : int;
  var tmp6 : int;
  var unpacked : scalar52;
  call unpacked := Impl__3_from_bytes_wide(input);
  call result := Impl__3_pack(unpacked);
  call lemma_group_order_smaller_than_pow256();
  call lemma_scalar52_lt_pow2_256_if_canonical(unpacked);
  tmp1 := scalar52_as_nat(unpacked);
  tmp2 := Arithmetic_Power2_pow2(256);
  call Arithmetic_Div_mod_lemma_small_mod(tmp1, tmp2);
  tmp3 := bytes_seq_as_nat(input);
  tmp4 := group_order;
  call Arithmetic_Div_mod_lemma_mod_bound(tmp3, tmp4);
  tmp5 := u8_32_as_nat(scalar..bytes(result));
  tmp6 := group_order;
  call Arithmetic_Div_mod_lemma_small_mod(tmp5, tmp6);
  call axiom_uniform_mod_reduction(input, result);
  result := result;
  exit Impl__4_from_bytes_mod_order_wide;
};
 procedure Arithmetic_Div_mod_lemma_small_mod (x : int, m : int) returns ()
spec {
  requires x < m;
  requires 0 < m;
  ensures x mod m == x;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_mod_bound (x : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures 0 <= x mod m && x mod m < m;
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_adds (e1 : int, e2 : int) returns ()
spec {
  ensures Arithmetic_Power2_pow2(e1 + e2) == Arithmetic_Power2_pow2(e1) * Arithmetic_Power2_pow2(e2);
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_strictly_increases (e1 : int, e2 : int) returns ()
spec {
  requires e1 < e2;
  ensures Arithmetic_Power2_pow2(e1) < Arithmetic_Power2_pow2(e2);
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma2_to64 () returns ()
spec {
  ensures Arithmetic_Power2_pow2(0) == 1;
  ensures Arithmetic_Power2_pow2(1) == 2;
  ensures Arithmetic_Power2_pow2(2) == 4;
  ensures Arithmetic_Power2_pow2(3) == 8;
  ensures Arithmetic_Power2_pow2(4) == 16;
  ensures Arithmetic_Power2_pow2(5) == 32;
  ensures Arithmetic_Power2_pow2(6) == 64;
  ensures Arithmetic_Power2_pow2(7) == 128;
  ensures Arithmetic_Power2_pow2(8) == 256;
  ensures Arithmetic_Power2_pow2(9) == 512;
  ensures Arithmetic_Power2_pow2(10) == 1024;
  ensures Arithmetic_Power2_pow2(11) == 2048;
  ensures Arithmetic_Power2_pow2(12) == 4096;
  ensures Arithmetic_Power2_pow2(13) == 8192;
  ensures Arithmetic_Power2_pow2(14) == 16384;
  ensures Arithmetic_Power2_pow2(15) == 32768;
  ensures Arithmetic_Power2_pow2(16) == 65536;
  ensures Arithmetic_Power2_pow2(17) == 131072;
  ensures Arithmetic_Power2_pow2(18) == 262144;
  ensures Arithmetic_Power2_pow2(19) == 524288;
  ensures Arithmetic_Power2_pow2(20) == 1048576;
  ensures Arithmetic_Power2_pow2(21) == 2097152;
  ensures Arithmetic_Power2_pow2(22) == 4194304;
  ensures Arithmetic_Power2_pow2(23) == 8388608;
  ensures Arithmetic_Power2_pow2(24) == 16777216;
  ensures Arithmetic_Power2_pow2(25) == 33554432;
  ensures Arithmetic_Power2_pow2(26) == 67108864;
  ensures Arithmetic_Power2_pow2(27) == 134217728;
  ensures Arithmetic_Power2_pow2(28) == 268435456;
  ensures Arithmetic_Power2_pow2(29) == 536870912;
  ensures Arithmetic_Power2_pow2(30) == 1073741824;
  ensures Arithmetic_Power2_pow2(31) == 2147483648;
  ensures Arithmetic_Power2_pow2(32) == 4294967296;
  ensures Arithmetic_Power2_pow2(64) == 18446744073709551616;
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma2_to64_rest () returns ()
spec {
  ensures Arithmetic_Power2_pow2(33) == 8589934592;
  ensures Arithmetic_Power2_pow2(34) == 17179869184;
  ensures Arithmetic_Power2_pow2(35) == 34359738368;
  ensures Arithmetic_Power2_pow2(36) == 68719476736;
  ensures Arithmetic_Power2_pow2(37) == 137438953472;
  ensures Arithmetic_Power2_pow2(38) == 274877906944;
  ensures Arithmetic_Power2_pow2(39) == 549755813888;
  ensures Arithmetic_Power2_pow2(40) == 1099511627776;
  ensures Arithmetic_Power2_pow2(41) == 2199023255552;
  ensures Arithmetic_Power2_pow2(42) == 4398046511104;
  ensures Arithmetic_Power2_pow2(43) == 8796093022208;
  ensures Arithmetic_Power2_pow2(44) == 17592186044416;
  ensures Arithmetic_Power2_pow2(45) == 35184372088832;
  ensures Arithmetic_Power2_pow2(46) == 70368744177664;
  ensures Arithmetic_Power2_pow2(47) == 140737488355328;
  ensures Arithmetic_Power2_pow2(48) == 281474976710656;
  ensures Arithmetic_Power2_pow2(49) == 562949953421312;
  ensures Arithmetic_Power2_pow2(50) == 1125899906842624;
  ensures Arithmetic_Power2_pow2(51) == 2251799813685248;
  ensures Arithmetic_Power2_pow2(52) == 4503599627370496;
  ensures Arithmetic_Power2_pow2(53) == 9007199254740992;
  ensures Arithmetic_Power2_pow2(54) == 18014398509481984;
  ensures Arithmetic_Power2_pow2(55) == 36028797018963968;
  ensures Arithmetic_Power2_pow2(56) == 72057594037927936;
  ensures Arithmetic_Power2_pow2(57) == 144115188075855872;
  ensures Arithmetic_Power2_pow2(58) == 288230376151711744;
  ensures Arithmetic_Power2_pow2(59) == 576460752303423488;
  ensures Arithmetic_Power2_pow2(60) == 1152921504606846976;
  ensures Arithmetic_Power2_pow2(61) == 2305843009213693952;
  ensures Arithmetic_Power2_pow2(62) == 4611686018427387904;
  ensures Arithmetic_Power2_pow2(63) == 9223372036854775808;
  ensures Arithmetic_Power2_pow2(64) == 18446744073709551616;
  } {
  assume false;
};
 procedure lemma_group_order_bound () returns ()
spec {
  ensures group_order < Arithmetic_Power2_pow2(255);
  } {
  assume 27742317777372353535851937790883648493 < 85070591730234615865843651857942052864;
  call Arithmetic_Power2_lemma2_to64_rest();
  assert Arithmetic_Power2_pow2(63) == 9223372036854775808;
  assume Arithmetic_Power2_pow2(63) == 9223372036854775808;
  call Arithmetic_Power2_lemma_pow2_adds(63, 63);
  assert Arithmetic_Power2_pow2(126) == 85070591730234615865843651857942052864;
  assert 27742317777372353535851937790883648493 < Arithmetic_Power2_pow2(126);
  call Arithmetic_Power2_lemma_pow2_strictly_increases(126, 252);
  assert group_order < Arithmetic_Power2_pow2(252) + Arithmetic_Power2_pow2(252);
  call Arithmetic_Power2_lemma_pow2_adds(1, 252);
  call Arithmetic_Power2_lemma2_to64();
  assert Arithmetic_Power2_pow2(252) + Arithmetic_Power2_pow2(252) == Arithmetic_Power2_pow2(253);
  assume Arithmetic_Power2_pow2(252) + Arithmetic_Power2_pow2(252) == Arithmetic_Power2_pow2(253);
  call Arithmetic_Power2_lemma_pow2_strictly_increases(253, 255);
  exit lemma_group_order_bound;
};
 procedure lemma_group_order_smaller_than_pow256 () returns ()
spec {
  ensures group_order < Arithmetic_Power2_pow2(256);
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(255, 256);
  exit lemma_group_order_smaller_than_pow256;
};
 procedure lemma_scalar52_lt_pow2_256_if_canonical (a : scalar52) returns ()
spec {
  requires limbs_bounded(a);
  requires scalar52_as_nat(a) < group_order;
  ensures scalar52_as_nat(a) < Arithmetic_Power2_pow2(256);
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(255, 256);
  exit lemma_scalar52_lt_pow2_256_if_canonical;
};
 procedure axiom_uniform_mod_reduction (input : Sequence bv8, result : scalar) returns ()
spec {
  requires scalar_as_canonical(result) == bytes_seq_as_nat(input) mod group_order;
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  assume false;
  exit axiom_uniform_mod_reduction;
};
#end

#eval Strata.Boole.verify "cvc5" from_bytes_mod_order_wide_minimal_program (options := .quiet)

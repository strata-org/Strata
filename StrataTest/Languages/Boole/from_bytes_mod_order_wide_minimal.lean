/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def from_bytes_mod_order_wide_minimal_program : Strata.Program :=
#strata
program Boole;

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
 function group_order () : int {
  7237005577332262213973186563042994240857116359379907606001950938285454250989
}
 function group_canonical (n : int) : int {
  n mod group_order
}
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
  assume Arithmetic_Power2_pow2(252) == 7237005577332262213973186563042994240829374041602535252466099000494570602496;
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

/-- info:
Obligation: bytes_seq_as_nat_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_Sequence.take_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.drop_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.take_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_terminates_0
Property: assert
Result: ✅ pass

Obligation: seq_as_nat_52_terminates_1
Property: assert
Result: ✅ pass

Obligation: scalar52_as_nat_body_calls_scalar52..limbs_0
Property: assert
Result: ✅ pass

Obligation: limbs_bounded_body_calls_scalar52..limbs_0
Property: assert
Result: ✅ pass

Obligation: limbs_bounded_body_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: is_canonical_scalar_body_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: is_canonical_scalar_body_calls_scalar..bytes_1
Property: assert
Result: ✅ pass

Obligation: is_canonical_scalar_body_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: scalar_as_canonical_body_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: Impl__2_clone_ensures_0_2284
Property: assert
Result: ✅ pass

Obligation: Impl__3_from_bytes_wide_ensures_1_2457
Property: assert
Result: ✅ pass

Obligation: Impl__3_from_bytes_wide_ensures_2_2493
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_post_Impl__3_pack_ensures_5_2826_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: set_result_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_ensures_5_2826
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_ensures_6_2930
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__3_pack_requires_4_2794_25
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Impl__3_pack_ensures_5_2826_26_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_lemma_scalar52_lt_pow2_256_if_canonical_requires_102_10186_19
Property: assert
Result: ✅ pass

Obligation: callElimAssert_lemma_scalar52_lt_pow2_256_if_canonical_requires_103_10215_20
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_11_4298_15
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_12_4316_16
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_mod_bound_requires_15_4466_11
Property: assert
Result: ✅ pass

Obligation: set_tmp5_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_11_4298_6
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_12_4316_7
Property: assert
Result: ✅ pass

Obligation: callElimAssert_axiom_uniform_mod_reduction_requires_105_10574_2
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_8_3204
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_9_3287
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_10_3326
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Div_mod_lemma_small_mod_ensures_13_4334
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Div_mod_lemma_mod_bound_ensures_16_4484
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma_pow2_adds_ensures_18_4632
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma_pow2_strictly_increases_ensures_21_4877
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_23_5031
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_24_5073
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_25_5115
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_26_5157
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_27_5199
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_28_5242
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_29_5285
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_30_5328
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_31_5372
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_32_5416
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_33_5460
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_34_5506
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_35_5552
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_36_5598
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_37_5644
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_38_5691
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_39_5738
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_40_5785
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_41_5833
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_42_5881
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_43_5929
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_44_5978
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_45_6027
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_46_6076
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_47_6125
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_48_6175
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_49_6225
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_50_6275
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_51_6326
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_52_6377
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_53_6428
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_54_6480
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_55_6532
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_ensures_56_6584
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_58_6738
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_59_6790
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_60_6843
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_61_6896
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_62_6949
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_63_7003
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_64_7057
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_65_7111
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_66_7166
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_67_7221
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_68_7276
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_69_7331
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_70_7387
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_71_7443
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_72_7499
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_73_7556
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_74_7613
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_75_7670
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_76_7728
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_77_7786
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_78_7844
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_79_7902
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_80_7961
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_81_8020
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_82_8079
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_83_8139
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_84_8199
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_85_8259
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_86_8320
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_87_8381
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_88_8442
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma2_to64_rest_ensures_89_8503
Property: assert
Result: ✅ pass

Obligation: assert_93_8840
Property: assert
Result: ✅ pass

Obligation: assert_95_9010
Property: assert
Result: ✅ pass

Obligation: assert_96_9090
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_20_4857_75
Property: assert
Result: ✅ pass

Obligation: assert_98_9353
Property: assert
Result: ✅ pass

Obligation: assert_99_9525
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_20_4857_34
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_bound_ensures_91_8646
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_20_4857_114
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_smaller_than_pow256_ensures_101_9894
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_20_4857_119
Property: assert
Result: ✅ pass

Obligation: lemma_scalar52_lt_pow2_256_if_canonical_ensures_104_10260
Property: assert
Result: ✅ pass

Obligation: axiom_uniform_mod_reduction_ensures_106_10657
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" from_bytes_mod_order_wide_minimal_program (options := .quiet)

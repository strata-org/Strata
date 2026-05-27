/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def from_bytes_mod_order_wide_minimal_program : Strata.Program :=
#strata
program Boole;

 type nat;
 function nat.toInt (n : nat) : int;
 function nat.fromIntAux (x : int) : nat;
 function nat.fromInt (x : int) : nat requires 0 <= x;
   {
  nat.fromIntAux(x)
}
 axiom [nat_nonneg]: forall n : nat :: 0 <= nat.toInt(n);
 axiom [nat_fromInt_toInt]: forall x : int :: 0 <= x ==> nat.toInt(nat.fromInt(x)) == x;
 axiom [nat_toInt_fromInt]: forall n : nat :: nat.fromInt(nat.toInt(n)) == n;
 function nat.add (a : nat, b : nat) : nat {
  nat.fromInt(nat.toInt(a) + nat.toInt(b))
}
 function nat.sub (a : nat, b : nat) : nat requires nat.toInt(b) <= nat.toInt(a);
   {
  nat.fromInt(nat.toInt(a) - nat.toInt(b))
}
 function nat.mul (a : nat, b : nat) : nat {
  nat.fromInt(nat.toInt(a) * nat.toInt(b))
}
 function nat.div (a : nat, b : nat) : nat requires nat.toInt(b) != 0;
   {
  nat.fromInt(nat.toInt(a) div nat.toInt(b))
}
 function nat.lt (a : nat, b : nat) : bool {
  nat.toInt(a) < nat.toInt(b)
}
 function nat.le (a : nat, b : nat) : bool {
  nat.toInt(a) <= nat.toInt(b)
}
 function nat.gt (a : nat, b : nat) : bool {
  nat.toInt(a) > nat.toInt(b)
}
 function nat.ge (a : nat, b : nat) : bool {
  nat.toInt(a) >= nat.toInt(b)
}
 function bv64_to_nat_u (x : bv64) : nat;
 const Seq_map_empty_0:Sequence nat;
 axiom Sequence.length(Seq_map_empty_0) == 0;
 function Seq_map_closure_0 (_i : int, x : bv64) : nat {
  bv64_to_nat_u(x)
}
 rec function Seq_map_rec_0 (s : Sequence bv64, n : int) : Sequence nat
decreases n
  {
  if n <= 0 then Seq_map_empty_0 else Sequence.build(Seq_map_rec_0(s, n - 1), Seq_map_closure_0(n - 1, Sequence.select(s, n - 1)))
};
 datatype scalar52 {
  scalar52_ctor(limbs : Sequence bv64)
};
 datatype scalar {
  scalar_ctor(bytes : Sequence bv8)
};
 function Array_spec_array_as_slice<T> (ar : Sequence T) : Sequence T;
 function Arithmetic_Power2_pow2 (e : nat) : nat;
 function is_uniform_bytes (bytes : Sequence bv8) : bool;
 function is_uniform_scalar (s : scalar) : bool;
 rec function bytes_seq_as_nat (bytes : Sequence bv8) : nat
decreases Sequence.length(bytes)
  {
  if Sequence.length(bytes) == 0 then nat.fromInt(0) else nat.fromInt(Sequence.select(bytes, 0) as_int + nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(8))) * nat.toInt(bytes_seq_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))))
};
 rec function u8_32_as_nat (bytes : Sequence bv8) : nat
decreases Sequence.length(bytes)
  {
  if Sequence.length(bytes) == 0 then nat.fromInt(0) else nat.add(nat.fromInt((Sequence.select(bytes, 0) as_int)), nat.mul(Arithmetic_Power2_pow2(nat.fromInt(8)), u8_32_as_nat(Sequence.subrange(bytes, 1, Sequence.length(bytes)))))
};
 function group_order () : nat {
  nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), nat.fromInt(27742317777372353535851937790883648493))
}
 function group_canonical (n : nat) : nat {
  nat.fromInt(nat.toInt(n) mod nat.toInt(group_order))
}
 rec function seq_as_nat_52 (limbs : Sequence nat) : nat
decreases Sequence.length(limbs)
  {
  if Sequence.length(limbs) == 0 then nat.fromInt(0) else nat.add(Sequence.select(limbs, 0), nat.mul(seq_as_nat_52(Sequence.subrange(limbs, 1, Sequence.length(limbs))), Arithmetic_Power2_pow2(nat.fromInt(52))))
};
 function limbs52_as_nat (limbs : Sequence bv64) : nat {
  seq_as_nat_52(Seq_map_rec_0(limbs, Sequence.length(limbs)))
}
 function scalar52_as_nat (s : scalar52) : nat {
  limbs52_as_nat(Array_spec_array_as_slice(scalar52..limbs(s)))
}
 function limbs_bounded (s : scalar52) : bool {
  ∀ i : int :: 0 <= i && i < 5 ==> Sequence.select(scalar52..limbs(s), i) < bv{64}(1) << bv{64}(52)
}
 function is_canonical_scalar52 (s : scalar52) : bool {
  limbs_bounded(s) && nat.lt(scalar52_as_nat(s), group_order)
}
 function is_canonical_scalar (s : scalar) : bool {
  nat.lt(u8_32_as_nat(scalar..bytes(s)), group_order) && Sequence.select(scalar..bytes(s), 31) <= bv{8}(127)
}
 function scalar_as_canonical (s : scalar) : nat {
  group_canonical(u8_32_as_nat(scalar..bytes(s)))
}
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
  ensures nat.toInt(u8_32_as_nat(scalar..bytes(result))) == nat.toInt(scalar52_as_nat(self)) mod nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(256)));
  ensures nat.lt(scalar52_as_nat(self), group_order) ==> is_canonical_scalar(result);
  } {
  assume false;
  result := scalar_ctor(Sequence.of_bv8[bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0), bv{8}(0)]);
  exit Impl__3_pack;
};
 procedure Impl__4_from_bytes_mod_order_wide (input : Sequence bv8) returns (result : scalar)
spec {
  ensures scalar_as_canonical(result) == group_canonical(bytes_seq_as_nat(input));
  ensures is_canonical_scalar(result);
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  var tmp1 : nat;
  var tmp2 : nat;
  var tmp3 : nat;
  var tmp4 : nat;
  var tmp5 : nat;
  var tmp6 : nat;
  var unpacked : scalar52;
  call unpacked := Impl__3_from_bytes_wide(input);

  call result := Impl__3_pack(unpacked);

  call lemma_group_order_smaller_than_pow256();
  call lemma_scalar52_lt_pow2_256_if_canonical(unpacked);
  tmp1 := scalar52_as_nat(unpacked);
  tmp2 := Arithmetic_Power2_pow2(nat.fromInt(256));
  call Arithmetic_Div_mod_lemma_small_mod(tmp1, tmp2);
  tmp3 := bytes_seq_as_nat(input);
  tmp4 := group_order;
  call Arithmetic_Div_mod_lemma_mod_bound(nat.toInt(tmp3), nat.toInt(tmp4));
  tmp5 := u8_32_as_nat(scalar..bytes(result));
  tmp6 := group_order;
  call Arithmetic_Div_mod_lemma_small_mod(tmp5, tmp6);
  call axiom_uniform_mod_reduction(input, result);
  result := result;
  exit Impl__4_from_bytes_mod_order_wide;
};
 procedure Arithmetic_Div_mod_lemma_small_mod (x : nat, m : nat) returns ()
spec {
  requires nat.lt(x, m);
  requires 0 < nat.toInt(m);
  ensures nat.toInt(x) mod nat.toInt(m) == nat.toInt(x);
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
 procedure Arithmetic_Power2_lemma_pow2_adds (e1 : nat, e2 : nat) returns ()
spec {
  ensures Arithmetic_Power2_pow2(nat.add(e1, e2)) == nat.mul(Arithmetic_Power2_pow2(e1), Arithmetic_Power2_pow2(e2));
  } {
  assume false;
};
 procedure Arithmetic_Power2_lemma_pow2_strictly_increases (e1 : nat, e2 : nat) returns ()
spec {
  requires nat.lt(e1, e2);
  ensures nat.lt(Arithmetic_Power2_pow2(e1), Arithmetic_Power2_pow2(e2));
  } {
  assume false;
};
 axiom [Arithmetic_Power2_lemma2_to64_0]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(0))) == 1;
 axiom [Arithmetic_Power2_lemma2_to64_1]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(1))) == 2;
 axiom [Arithmetic_Power2_lemma2_to64_2]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(2))) == 4;
 axiom [Arithmetic_Power2_lemma2_to64_3]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(3))) == 8;
 axiom [Arithmetic_Power2_lemma2_to64_4]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(4))) == 16;
 axiom [Arithmetic_Power2_lemma2_to64_5]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(5))) == 32;
 axiom [Arithmetic_Power2_lemma2_to64_6]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(6))) == 64;
 axiom [Arithmetic_Power2_lemma2_to64_7]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(7))) == 128;
 axiom [Arithmetic_Power2_lemma2_to64_8]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(8))) == 256;
 axiom [Arithmetic_Power2_lemma2_to64_9]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(9))) == 512;
 axiom [Arithmetic_Power2_lemma2_to64_10]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(10))) == 1024;
 axiom [Arithmetic_Power2_lemma2_to64_11]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(11))) == 2048;
 axiom [Arithmetic_Power2_lemma2_to64_12]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(12))) == 4096;
 axiom [Arithmetic_Power2_lemma2_to64_13]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(13))) == 8192;
 axiom [Arithmetic_Power2_lemma2_to64_14]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(14))) == 16384;
 axiom [Arithmetic_Power2_lemma2_to64_15]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(15))) == 32768;
 axiom [Arithmetic_Power2_lemma2_to64_16]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(16))) == 65536;
 axiom [Arithmetic_Power2_lemma2_to64_17]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(17))) == 131072;
 axiom [Arithmetic_Power2_lemma2_to64_18]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(18))) == 262144;
 axiom [Arithmetic_Power2_lemma2_to64_19]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(19))) == 524288;
 axiom [Arithmetic_Power2_lemma2_to64_20]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(20))) == 1048576;
 axiom [Arithmetic_Power2_lemma2_to64_21]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(21))) == 2097152;
 axiom [Arithmetic_Power2_lemma2_to64_22]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(22))) == 4194304;
 axiom [Arithmetic_Power2_lemma2_to64_23]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(23))) == 8388608;
 axiom [Arithmetic_Power2_lemma2_to64_24]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(24))) == 16777216;
 axiom [Arithmetic_Power2_lemma2_to64_25]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(25))) == 33554432;
 axiom [Arithmetic_Power2_lemma2_to64_26]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(26))) == 67108864;
 axiom [Arithmetic_Power2_lemma2_to64_27]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(27))) == 134217728;
 axiom [Arithmetic_Power2_lemma2_to64_28]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(28))) == 268435456;
 axiom [Arithmetic_Power2_lemma2_to64_29]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(29))) == 536870912;
 axiom [Arithmetic_Power2_lemma2_to64_30]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(30))) == 1073741824;
 axiom [Arithmetic_Power2_lemma2_to64_31]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(31))) == 2147483648;
 axiom [Arithmetic_Power2_lemma2_to64_32]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(32))) == 4294967296;
 axiom [Arithmetic_Power2_lemma2_to64_33]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
 axiom [Arithmetic_Power2_lemma2_to64_rest_0]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(33))) == 8589934592;
 axiom [Arithmetic_Power2_lemma2_to64_rest_1]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(34))) == 17179869184;
 axiom [Arithmetic_Power2_lemma2_to64_rest_2]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(35))) == 34359738368;
 axiom [Arithmetic_Power2_lemma2_to64_rest_3]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(36))) == 68719476736;
 axiom [Arithmetic_Power2_lemma2_to64_rest_4]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(37))) == 137438953472;
 axiom [Arithmetic_Power2_lemma2_to64_rest_5]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(38))) == 274877906944;
 axiom [Arithmetic_Power2_lemma2_to64_rest_6]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(39))) == 549755813888;
 axiom [Arithmetic_Power2_lemma2_to64_rest_7]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(40))) == 1099511627776;
 axiom [Arithmetic_Power2_lemma2_to64_rest_8]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(41))) == 2199023255552;
 axiom [Arithmetic_Power2_lemma2_to64_rest_9]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(42))) == 4398046511104;
 axiom [Arithmetic_Power2_lemma2_to64_rest_10]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(43))) == 8796093022208;
 axiom [Arithmetic_Power2_lemma2_to64_rest_11]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(44))) == 17592186044416;
 axiom [Arithmetic_Power2_lemma2_to64_rest_12]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(45))) == 35184372088832;
 axiom [Arithmetic_Power2_lemma2_to64_rest_13]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(46))) == 70368744177664;
 axiom [Arithmetic_Power2_lemma2_to64_rest_14]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(47))) == 140737488355328;
 axiom [Arithmetic_Power2_lemma2_to64_rest_15]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(48))) == 281474976710656;
 axiom [Arithmetic_Power2_lemma2_to64_rest_16]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(49))) == 562949953421312;
 axiom [Arithmetic_Power2_lemma2_to64_rest_17]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(50))) == 1125899906842624;
 axiom [Arithmetic_Power2_lemma2_to64_rest_18]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(51))) == 2251799813685248;
 axiom [Arithmetic_Power2_lemma2_to64_rest_19]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(52))) == 4503599627370496;
 axiom [Arithmetic_Power2_lemma2_to64_rest_20]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(53))) == 9007199254740992;
 axiom [Arithmetic_Power2_lemma2_to64_rest_21]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(54))) == 18014398509481984;
 axiom [Arithmetic_Power2_lemma2_to64_rest_22]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(55))) == 36028797018963968;
 axiom [Arithmetic_Power2_lemma2_to64_rest_23]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(56))) == 72057594037927936;
 axiom [Arithmetic_Power2_lemma2_to64_rest_24]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(57))) == 144115188075855872;
 axiom [Arithmetic_Power2_lemma2_to64_rest_25]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(58))) == 288230376151711744;
 axiom [Arithmetic_Power2_lemma2_to64_rest_26]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(59))) == 576460752303423488;
 axiom [Arithmetic_Power2_lemma2_to64_rest_27]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(60))) == 1152921504606846976;
 axiom [Arithmetic_Power2_lemma2_to64_rest_28]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(61))) == 2305843009213693952;
 axiom [Arithmetic_Power2_lemma2_to64_rest_29]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(62))) == 4611686018427387904;
 axiom [Arithmetic_Power2_lemma2_to64_rest_30]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
 axiom [Arithmetic_Power2_lemma2_to64_rest_31]: nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(64))) == 18446744073709551616;
 procedure lemma_group_order_bound () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(255)));
  } {
  assume 27742317777372353535851937790883648493 < 85070591730234615865843651857942052864;
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  assume nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(63))) == 9223372036854775808;
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(63), nat.fromInt(63));
  assert nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126))) == 85070591730234615865843651857942052864;
  assert 27742317777372353535851937790883648493 < nat.toInt(Arithmetic_Power2_pow2(nat.fromInt(126)));
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(126), nat.fromInt(252));
  assert nat.lt(group_order, nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))));
  call Arithmetic_Power2_lemma_pow2_adds(nat.fromInt(1), nat.fromInt(252));
  assert nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))) == Arithmetic_Power2_pow2(nat.fromInt(253));
  assume nat.add(Arithmetic_Power2_pow2(nat.fromInt(252)), Arithmetic_Power2_pow2(nat.fromInt(252))) == Arithmetic_Power2_pow2(nat.fromInt(253));
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(253), nat.fromInt(255));
  exit lemma_group_order_bound;
};
 procedure lemma_group_order_smaller_than_pow256 () returns ()
spec {
  ensures nat.lt(group_order, Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(255), nat.fromInt(256));
  exit lemma_group_order_smaller_than_pow256;
};
 procedure lemma_scalar52_lt_pow2_256_if_canonical (a : scalar52) returns ()
spec {
  requires limbs_bounded(a);
  requires nat.lt(scalar52_as_nat(a), group_order);
  ensures nat.lt(scalar52_as_nat(a), Arithmetic_Power2_pow2(nat.fromInt(256)));
  } {
  call lemma_group_order_bound();
  call Arithmetic_Power2_lemma_pow2_strictly_increases(nat.fromInt(255), nat.fromInt(256));
  exit lemma_scalar52_lt_pow2_256_if_canonical;
};
 procedure axiom_uniform_mod_reduction (input : Sequence bv8, result : scalar) returns ()
spec {
  requires nat.toInt(scalar_as_canonical(result)) == nat.toInt(bytes_seq_as_nat(input)) mod nat.toInt(group_order);
  ensures is_uniform_bytes(input) ==> is_uniform_scalar(result);
  } {
  assume false;
  exit axiom_uniform_mod_reduction;
};
#end

/-- info:
Obligation: nat.add_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: nat.sub_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: nat.mul_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: nat.div_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: Seq_map_rec_0_body_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ❓ unknown

Obligation: Seq_map_rec_0_terminates_0
Property: assert
Result: ✅ pass

Obligation: Seq_map_rec_0_terminates_1
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_nat.fromInt_2
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_Sequence.drop_3
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_Sequence.take_4
Property: out-of-bounds access check
Result: ✅ pass

Obligation: bytes_seq_as_nat_body_calls_nat.fromInt_5
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: bytes_seq_as_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_nat.fromInt_2
Property: assert
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_nat.fromInt_3
Property: assert
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_Sequence.drop_4
Property: out-of-bounds access check
Result: ✅ pass

Obligation: u8_32_as_nat_body_calls_Sequence.take_5
Property: out-of-bounds access check
Result: ✅ pass

Obligation: u8_32_as_nat_terminates_0
Property: assert
Result: ✅ pass

Obligation: u8_32_as_nat_terminates_1
Property: assert
Result: ✅ pass

Obligation: group_order_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: group_order_body_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: group_canonical_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.drop_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_Sequence.take_3
Property: out-of-bounds access check
Result: ✅ pass

Obligation: seq_as_nat_52_body_calls_nat.fromInt_4
Property: assert
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

Obligation: Impl__3_from_bytes_wide_ensures_4_4219
Property: assert
Result: ✅ pass

Obligation: Impl__3_from_bytes_wide_ensures_5_4255
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_post_Impl__3_pack_ensures_8_4588_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_post_Impl__3_pack_ensures_8_4588_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_ensures_8_4588
Property: assert
Result: ✅ pass

Obligation: Impl__3_pack_ensures_9_4738
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Impl__3_pack_requires_7_4556_25
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Impl__3_pack_ensures_8_4588_26_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Impl__3_pack_ensures_8_4588_26_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_lemma_group_order_smaller_than_pow256_ensures_35_16016_22_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_lemma_scalar52_lt_pow2_256_if_canonical_requires_36_16354_19
Property: assert
Result: ✅ pass

Obligation: callElimAssert_lemma_scalar52_lt_pow2_256_if_canonical_requires_37_16383_20
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_lemma_scalar52_lt_pow2_256_if_canonical_ensures_38_16435_21_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: set_tmp2_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_14_6464_15
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_15_6489_16
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_mod_bound_requires_18_6683_11
Property: assert
Result: ✅ pass

Obligation: set_tmp5_calls_scalar..bytes_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_14_6464_6
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Div_mod_lemma_small_mod_requires_15_6489_7
Property: assert
Result: ✅ pass

Obligation: callElimAssert_axiom_uniform_mod_reduction_requires_39_16795_2
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_11_5333
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_12_5416
Property: assert
Result: ✅ pass

Obligation: Impl__4_from_bytes_mod_order_wide_ensures_13_5455
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Div_mod_lemma_small_mod_ensures_16_6518
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Div_mod_lemma_mod_bound_ensures_19_6701
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma_pow2_adds_ensures_21_6849
Property: assert
Result: ✅ pass

Obligation: Arithmetic_Power2_lemma_pow2_strictly_increases_ensures_24_7117
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_bound_post_lemma_group_order_bound_ensures_26_14616_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_28_14785_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_28_14785
Property: assert
Result: ✅ pass

Obligation: assume_assume_29_14869_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_30_15029_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_30_15029
Property: assert
Result: ✅ pass

Obligation: assert_assert_31_15133_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_31_15133
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_23_7090_41
Property: assert
Result: ✅ pass

Obligation: assert_assert_32_15328_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_32_15328_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: assert_32_15328
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_33_15527_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assert_assert_33_15527_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: assert_assert_33_15527_calls_nat.fromInt_2
Property: assert
Result: ✅ pass

Obligation: assert_33_15527
Property: assert
Result: ✅ pass

Obligation: assume_assume_34_15673_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assume_assume_34_15673_calls_nat.fromInt_1
Property: assert
Result: ✅ pass

Obligation: assume_assume_34_15673_calls_nat.fromInt_2
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_23_7090_34
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_bound_ensures_26_14616
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_smaller_than_pow256_post_lemma_group_order_smaller_than_pow256_ensures_35_16016_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_lemma_group_order_bound_ensures_26_14616_50_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_23_7090_48
Property: assert
Result: ✅ pass

Obligation: lemma_group_order_smaller_than_pow256_ensures_35_16016
Property: assert
Result: ✅ pass

Obligation: lemma_scalar52_lt_pow2_256_if_canonical_post_lemma_scalar52_lt_pow2_256_if_canonical_ensures_38_16435_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_lemma_group_order_bound_ensures_26_14616_55_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: init_calls_nat.fromInt_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Arithmetic_Power2_lemma_pow2_strictly_increases_requires_23_7090_53
Property: assert
Result: ✅ pass

Obligation: lemma_scalar52_lt_pow2_256_if_canonical_ensures_38_16435
Property: assert
Result: ✅ pass

Obligation: axiom_uniform_mod_reduction_ensures_40_16911
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" from_bytes_mod_order_wide_minimal_program (options := .quiet)

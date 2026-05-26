/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def one_time_pad_map_program : Strata.Program :=
#strata
program Boole;

type Array := Map int int;

procedure Encrypt(key : Array, message : Array, len : int)
  returns (cipher : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> cipher[i] == key[i] + message[i]);
}
{
  for i : int := 0 to (len-1) by 1
    invariant ∀ j:int . 0 <= j && j < i ==> cipher[j] == key[j] + message[j]
  {
    cipher[i] := key[i] + message[i];
  }
};

procedure Decrypt(key : Array, message : Array, len : int)
  returns (cipher : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> cipher[i] == message[i] - key[i]);
}
{
  for i : int := 0 to (len-1) by 1
    invariant ∀ j:int . 0 <= j && j < i ==> cipher[j] == message[j] - key[j]
  {
    cipher[i] := message[i] - key[i];
  }
};

procedure RoundTrip(key : Array, message : Array, len : int)
  returns (roundtrip : Array)
spec
{
  ensures (∀ i:int . 0 <= i && i < len ==> roundtrip[i] == message[i]);
}
{
  var encrypted : Array;
  call encrypted := Encrypt(key, message, len);
  call roundtrip := Decrypt(key, encrypted, len);
};

#end

theorem one_time_pad_map_program_smt_vcs_correct : Strata.smtVCsCorrect one_time_pad_map_program := by
  gen_smt_vcs
  all_goals (first | grind | decide)



private def one_time_pad_ll_program : Strata.Program :=
#strata
program Boole;

datatype List () { Nil(), Cons(head: int, tail: List) };

// Structural same-length check: axiom directly exposes isCons(message) when key is Cons,
// avoiding indirect Len counting arguments that SMT solvers cannot resolve.
rec function SameLen (@[cases] key : List, message : List) : bool
{
  if List..isNil(key) then List..isNil(message)
  else List..isCons(message) && SameLen(List..tail!(key), List..tail!(message))
};

rec function EncryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head(key) + List..head!(message),
    EncryptSpec(List..tail(key), List..tail!(message))
  )
};

rec function DecryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head!(message) - List..head(key),
    DecryptSpec(List..tail(key), List..tail!(message))
  )
};

procedure Encrypt(key : List, message : List, out cipher : List)
spec
{
  requires SameLen(key, message);
  ensures cipher == EncryptSpec(key, message);
  ensures SameLen(key, cipher);
}
{
  if (List..isNil(key)) {
    cipher := Nil();
  } else {
    var t : List;
    call Encrypt(List..tail!(key), List..tail!(message), out t);
    cipher := Cons(List..head!(key) + List..head!(message), t);
  }
};

procedure Decrypt(key : List, message : List, out result : List)
spec
{
  requires SameLen(key, message);
  ensures result == DecryptSpec(key, message);
}
{
  if (List..isNil(key)) {
    result := Nil();
  } else {
    var t : List;
    call Decrypt(List..tail!(key), List..tail!(message), out t);
    result := Cons(List..head!(message) - List..head!(key), t);
  }
};

// Lemma: decrypting an encrypted message recovers the original, proven by structural induction.
procedure RoundTripLemma(key : List, message : List)
spec
{
  requires SameLen(key, message);
  ensures DecryptSpec(key, EncryptSpec(key, message)) == message;
}
{
  if (List..isCons(key)) {
    call RoundTripLemma(List..tail!(key), List..tail!(message));
  }
};

procedure RoundTrip(key : List, message : List, out roundtrip : List)
spec
{
  requires SameLen(key, message);
  ensures roundtrip == message;
}
{
  var encrypted : List;
  call Encrypt(key, message, out encrypted);
  call Decrypt(key, encrypted, out roundtrip);
  call RoundTripLemma(key, message);
};

#end

/--
info:
Obligation: SameLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_body_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_body_calls_List..tail_1
Property: assert
Result: ✅ pass

Obligation: EncryptSpec_terminates_0
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_body_calls_List..head_0
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_body_calls_List..tail_1
Property: assert
Result: ✅ pass

Obligation: DecryptSpec_terminates_0
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_3
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_1
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_2
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_0_9
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_1
Property: assert
Result: ✅ pass

Obligation: callElimAssert_RoundTripLemma_requires_0_13
Property: assert
Result: ✅ pass

Obligation: RoundTripLemma_ensures_1
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_27
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_0_22
Property: assert
Result: ✅ pass

Obligation: callElimAssert_RoundTripLemma_requires_0_17
Property: assert
Result: ✅ pass

Obligation: RoundTrip_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify one_time_pad_ll_program (options := .quiet)



private def one_time_pad_seq_program : Strata.Program :=
#strata
program Boole;

procedure Encrypt(key : Sequence int, message : Sequence int, len : int, out cipher : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(cipher) == len;
  ensures (forall i : int :: 0 <= i && i < len ==>
    Sequence.select(cipher, i) == Sequence.select(key, i) + Sequence.select(message, i));
}
{
  cipher := Sequence.take(key, 0);
  var i : int;
  i := 0;
  while (i < len)
    decreases len - i
    invariant 0 <= i
    invariant i <= len
    invariant Sequence.length(cipher) == i
    invariant (forall j : int :: 0 <= j && j < i ==>
      Sequence.select(cipher, j) == Sequence.select(key, j) + Sequence.select(message, j))
  {
    cipher := Sequence.build(cipher, Sequence.select(key, i) + Sequence.select(message, i));
    i := i + 1;
  }
};

procedure Decrypt(key : Sequence int, message : Sequence int, len : int, out result : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(result) == len;
  ensures (forall i : int :: 0 <= i && i < len ==>
    Sequence.select(result, i) == Sequence.select(message, i) - Sequence.select(key, i));
}
{
  result := Sequence.take(key, 0);
  var i : int;
  i := 0;
  while (i < len)
    decreases len - i
    invariant 0 <= i
    invariant i <= len
    invariant Sequence.length(result) == i
    invariant (forall j : int :: 0 <= j && j < i ==>
      Sequence.select(result, j) == Sequence.select(message, j) - Sequence.select(key, j))
  {
    result := Sequence.build(result, Sequence.select(message, i) - Sequence.select(key, i));
    i := i + 1;
  }
};

procedure RoundTrip(key : Sequence int, message : Sequence int, len : int, out roundtrip : Sequence int)
spec
{
  requires 0 <= len;
  requires Sequence.length(key) >= len;
  requires Sequence.length(message) >= len;
  ensures Sequence.length(roundtrip) == len;
  ensures (forall i : int :: 0 <= i && i < len ==> Sequence.select(roundtrip, i) == Sequence.select(message, i));
}
{
  var encrypted : Sequence int;
  call Encrypt(key, message, len, out encrypted);
  call Decrypt(key, encrypted, len, out roundtrip);
};

#end

/--
info:
Obligation: Encrypt_post_Encrypt_ensures_4_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Encrypt_post_Encrypt_ensures_4_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Encrypt_post_Encrypt_ensures_4_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_cipher_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_3
Property: assert
Result: ✅ pass

Obligation: Encrypt_ensures_4
Property: assert
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_4_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_4_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: Decrypt_post_Decrypt_ensures_4_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_result_calls_Sequence.take_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: loop_invariant_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_lb_0
Property: assert
Result: ✅ pass

Obligation: set_result_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: set_result_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_2
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_3
Property: assert
Result: ✅ pass

Obligation: measure_decrease_0
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_3
Property: assert
Result: ✅ pass

Obligation: Decrypt_ensures_4
Property: assert
Result: ✅ pass

Obligation: RoundTrip_post_RoundTrip_ensures_4_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: RoundTrip_post_RoundTrip_ensures_4_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_0_13
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_1_14
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Encrypt_requires_2_15
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_17_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_17_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Encrypt_ensures_4_17_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_0_4
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_1_5
Property: assert
Result: ✅ pass

Obligation: callElimAssert_Decrypt_requires_2_6
Property: assert
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_4_8_calls_Sequence.select_0
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_4_8_calls_Sequence.select_1
Property: out-of-bounds access check
Result: ✅ pass

Obligation: assume_callElimAssume_Decrypt_ensures_4_8_calls_Sequence.select_2
Property: out-of-bounds access check
Result: ✅ pass

Obligation: RoundTrip_ensures_3
Property: assert
Result: ✅ pass

Obligation: RoundTrip_ensures_4
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify one_time_pad_seq_program (options := .quiet)

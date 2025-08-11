/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

-- Inspired by
-- https://github.com/boogie-org/boogie/blob/4eaf87ecc900e52ae794caa65620b35d5f645ba6/Test/strings/BasicOperators.bpl

-- (TODO) Add support for :builtin attribute?

def strEnv :=
#strata
program Boogie;

procedure main() returns () {

    var s1 : string, s2 : string, s3 : string;

    assert [concrete_string_test]: ("abc" == "abc");

    assume [s1_len]: str.len(s1) == 3;
    assume [s2_len]: str.len(s2) == 3;
    assume [s1_s2_concat_eq_s3]: str.concat(s1, s2) == s3;

    assert [s1_s2_len_sum_eq_s3_len]: str.len(s1) + str.len(s2) == str.len(s3);
};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: concrete_string_test
Assumptions:
Proof Obligation:
#true

Label: s1_s2_len_sum_eq_s3_len
Assumptions:
(s1_len, ((~Str.Length init_s1_0) == #3))
(s2_len, ((~Str.Length init_s2_1) == #3)) (s1_s2_concat_eq_s3, (((~Str.Concat init_s1_0) init_s2_1) == init_s3_2))
Proof Obligation:
(((~Int.Add (~Str.Length init_s1_0)) (~Str.Length init_s2_1)) == (~Str.Length init_s3_2))

Wrote problem to vcs/concrete_string_test.smt2.
Wrote problem to vcs/s1_s2_len_sum_eq_s3_len.smt2.
---
info:
Obligation: concrete_string_test
Result: verified

Obligation: s1_s2_len_sum_eq_s3_len
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" strEnv

---------------------------------------------------------------------

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Inspired by
-- https://github.com/boogie-org/boogie/blob/4eaf87ecc900e52ae794caa65620b35d5f645ba6/Test/strings/BasicOperators.bpl

-- (TODO) Add support for :builtin attribute?

def strPgm :=
#strata
program Core;

procedure main() returns () {

    var s1 : string, s2 : string, s3 : string;

    assert [concrete_string_test]: ("abc" == "abc");

    assume [s1_len]: str.len(s1) == 3;
    assume [s2_len]: str.len(s2) == 3;
    assume [s1_s2_concat_eq_s3]: str.concat(s1, s2) == s3;

    assert [s1_s2_len_sum_eq_s3_len]: str.len(s1) + str.len(s2) == str.len(s3);

    assert [substr_of_concat]: (str.substr(str.concat(s1,s2), 0, str.len(s1)) == s1);

    assert [substr_of_concat_concrete_test]: (str.substr("testing123", 2, 0) == "");
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: concrete_string_test
Property: assert
Obligation:
true

Label: s1_s2_len_sum_eq_s3_len
Property: assert
Assumptions:
s1_len: str.len(init_s1_0) == 3
s2_len: str.len(init_s2_1) == 3
s1_s2_concat_eq_s3: str.concat(init_s1_0, init_s2_1) == init_s3_2
Obligation:
str.len(init_s1_0) + str.len(init_s2_1) == str.len(init_s3_2)

Label: substr_of_concat
Property: assert
Assumptions:
s1_len: str.len(init_s1_0) == 3
s2_len: str.len(init_s2_1) == 3
s1_s2_concat_eq_s3: str.concat(init_s1_0, init_s2_1) == init_s3_2
Obligation:
str.substr(str.concat(init_s1_0, init_s2_1), 0, str.len(init_s1_0)) == init_s1_0

Label: substr_of_concat_concrete_test
Property: assert
Assumptions:
s1_len: str.len(init_s1_0) == 3
s2_len: str.len(init_s2_1) == 3
s1_s2_concat_eq_s3: str.concat(init_s1_0, init_s2_1) == init_s3_2
Obligation:
str.substr("testing123", 2, 0) == ""

---
info:
Obligation: concrete_string_test
Property: assert
Result: ✅ pass

Obligation: s1_s2_len_sum_eq_s3_len
Property: assert
Result: ✅ pass

Obligation: substr_of_concat
Property: assert
Result: ✅ pass

Obligation: substr_of_concat_concrete_test
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strPgm

---------------------------------------------------------------------

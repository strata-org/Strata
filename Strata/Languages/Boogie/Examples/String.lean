/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

-- Inspired by
-- https://github.com/boogie-org/boogie/blob/4eaf87ecc900e52ae794caa65620b35d5f645ba6/Test/strings/BasicOperators.bpl

-- (TODO) Add support for :builtin attribute?

def strEnv : Environment :=
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


Obligation concrete_string_test proved via evaluation!


VCs:
Label: s1_s2_len_sum_eq_s3_len
Assumptions:
(s1_len, ((~Str.Length init_s1_0) == #3))
(s2_len, ((~Str.Length init_s2_1) == #3)) (s1_s2_concat_eq_s3, (((~Str.Concat init_s1_0) init_s2_1) == init_s3_2))
Proof Obligation:
(((~Int.Add (~Str.Length init_s1_0)) (~Str.Length init_s2_1)) == (~Str.Length init_s3_2))

Wrote problem to vcs/s1_s2_len_sum_eq_s3_len.smt2.
---
info:
Obligation: s1_s2_len_sum_eq_s3_len
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" strEnv

---------------------------------------------------------------------

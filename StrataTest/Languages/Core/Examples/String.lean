/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

-- Inspired by
-- https://github.com/boogie-org/boogie/blob/4eaf87ecc900e52ae794caa65620b35d5f645ba6/Test/strings/BasicOperators.bpl

-- (TODO) Add support for :builtin attribute?

def strPgm :=
#strata
program Core;

procedure main() {

    var s1 : string, s2 : string, s3 : string;

    assert [concrete_string_test]: ("abc" == "abc");

    assume [s1_len]: str.len(s1) == 3;
    assume [s2_len]: str.len(s2) == 3;
    assume [s1_s2_concat_eq_s3]: str.concat(s1, s2) == s3;

    assert [s1_s2_len_sum_eq_s3_len]: str.len(s1) + str.len(s2) == str.len(s3);

    assert [substr_of_concat]: (str.substr(str.concat(s1,s2), 0, str.len(s1)) == s1);

    assert [substr_of_concat_concrete_test]: (str.substr("testing123", 2, 0) == "");

    assert [prefixof_concrete_true]: str.prefixof("abc", "abcdef");
    assert [prefixof_concrete_false]: !str.prefixof("xyz", "abcdef");
    assert [suffixof_concrete_true]: str.suffixof("def", "abcdef");
    assert [suffixof_concrete_false]: !str.suffixof("xyz", "abcdef");

    assert [contains_concrete_true]: str.contains("abcdef", "cd");
    assert [contains_concrete_false]: !str.contains("abcdef", "xy");
    assert [indexof_concrete]: str.indexof("abcdef", "cd", 0) == 2;
    assert [at_concrete]: str.at("abc", 0) == "a";
    assert [replace_concrete]: str.replace("abcabc", "a", "x") == "xbcabc";
    assert [lt_concrete_true]: str.lt("abc", "abd");
    assert [le_concrete_true]: str.le("abc", "abc");

    // SMT-LIB edge-case conventions (out-of-range indexof/at, absent/empty
    // replace pattern, lt irreflexivity). These pin the backend semantics.
    assert [indexof_neg_offset]: str.indexof("abcdef", "cd", -1) == -1;
    assert [indexof_absent]: str.indexof("abcdef", "xy", 0) == -1;
    assert [at_oob]: str.at("abc", 5) == "";
    assert [at_neg]: str.at("abc", -1) == "";
    assert [replace_absent]: str.replace("abcabc", "xy", "z") == "abcabc";
    assert [replace_empty_pat]: str.replace("abc", "", "z") == "zabc";
    assert [lt_irrefl]: !str.lt("abc", "abc");

    // Empty-operand conventions: the empty string is a substring of any string,
    // and searching for the empty string returns the offset when it is in range
    // (0 <= i <= len) and -1 once the offset exceeds the length.
    assert [contains_empty]: str.contains("abc", "");
    assert [indexof_empty_inrange]: str.indexof("abc", "", 0) == 0;
    assert [indexof_empty_beyond_len]: str.indexof("abc", "", 5) == -1;
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
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.len(s1) + str.len(s2) == str.len(s3)

Label: substr_of_concat
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.substr(str.concat(s1, s2), 0, str.len(s1)) == s1

Label: substr_of_concat_concrete_test
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.substr("testing123", 2, 0) == ""

Label: prefixof_concrete_true
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
true

Label: prefixof_concrete_false
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
true

Label: suffixof_concrete_true
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
true

Label: suffixof_concrete_false
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
true

Label: contains_concrete_true
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.contains("abcdef", "cd")

Label: contains_concrete_false
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
!(str.contains("abcdef", "xy"))

Label: indexof_concrete
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.indexof("abcdef", "cd", 0) == 2

Label: at_concrete
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.at("abc", 0) == "a"

Label: replace_concrete
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.replace("abcabc", "a", "x") == "xbcabc"

Label: lt_concrete_true
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.lt("abc", "abd")

Label: le_concrete_true
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.le("abc", "abc")

Label: indexof_neg_offset
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.indexof("abcdef", "cd", -1) == -1

Label: indexof_absent
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.indexof("abcdef", "xy", 0) == -1

Label: at_oob
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.at("abc", 5) == ""

Label: at_neg
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.at("abc", -1) == ""

Label: replace_absent
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.replace("abcabc", "xy", "z") == "abcabc"

Label: replace_empty_pat
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.replace("abc", "", "z") == "zabc"

Label: lt_irrefl
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
!(str.lt("abc", "abc"))

Label: contains_empty
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.contains("abc", "")

Label: indexof_empty_inrange
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.indexof("abc", "", 0) == 0

Label: indexof_empty_beyond_len
Property: assert
Assumptions:
s1_len: str.len(s1) == 3
s2_len: str.len(s2) == 3
s1_s2_concat_eq_s3: str.concat(s1, s2) == s3
Obligation:
str.indexof("abc", "", 5) == -1

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

Obligation: prefixof_concrete_true
Property: assert
Result: ✅ pass

Obligation: prefixof_concrete_false
Property: assert
Result: ✅ pass

Obligation: suffixof_concrete_true
Property: assert
Result: ✅ pass

Obligation: suffixof_concrete_false
Property: assert
Result: ✅ pass

Obligation: contains_concrete_true
Property: assert
Result: ✅ pass

Obligation: contains_concrete_false
Property: assert
Result: ✅ pass

Obligation: indexof_concrete
Property: assert
Result: ✅ pass

Obligation: at_concrete
Property: assert
Result: ✅ pass

Obligation: replace_concrete
Property: assert
Result: ✅ pass

Obligation: lt_concrete_true
Property: assert
Result: ✅ pass

Obligation: le_concrete_true
Property: assert
Result: ✅ pass

Obligation: indexof_neg_offset
Property: assert
Result: ✅ pass

Obligation: indexof_absent
Property: assert
Result: ✅ pass

Obligation: at_oob
Property: assert
Result: ✅ pass

Obligation: at_neg
Property: assert
Result: ✅ pass

Obligation: replace_absent
Property: assert
Result: ✅ pass

Obligation: replace_empty_pat
Property: assert
Result: ✅ pass

Obligation: lt_irrefl
Property: assert
Result: ✅ pass

Obligation: contains_empty
Property: assert
Result: ✅ pass

Obligation: indexof_empty_inrange
Property: assert
Result: ✅ pass

Obligation: indexof_empty_beyond_len
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify strPgm

end Strata
end
---------------------------------------------------------------------

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def regexPgm1 :=
#strata
program Core;

function cannot_end_with_period () : regex {
  re.comp(re.concat (re.* (re.all()), str.to.re(".")))
}

function optionally_a () : regex {
    re.loop(str.to.re("a"), 0, 1)
}

function ok_chars_regex () : regex {
    re.loop(
        re.union(re.range("a", "z"),
            re.union(re.range("0", "9"),
                     re.union(str.to.re("."),
                              str.to.re("-")))),
        1, 10)
}

procedure main() returns () {

    assert [hello_dot_ends_with_period]:    (!(str.in.re("hello.", cannot_end_with_period())));
    assert [dot_ends_with_period]:          (!(str.in.re(".",      cannot_end_with_period())));
    assert [bye_exclaim_no_end_with_period]:  (str.in.re("bye!",   cannot_end_with_period()));

    assert [ok_chars_str]:                    (str.in.re("test-str-1", ok_chars_regex()));
    assert [cannot_contain_exclaim]:        (!(str.in.re("test-str!", ok_chars_regex())));
    assert [has_to_be_at_least_1_char]:     (!(str.in.re("", ok_chars_regex())));
    assert [cannot_exceed_10_chars]:        (!(str.in.re("0123456789a", ok_chars_regex())));

    assert [optionally_a_check1]:             (str.in.re("a", optionally_a()));
    assert [optionally_a_check2]:           (!(str.in.re("b", optionally_a())));
};
#end


/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" regexPgm1

---------------------------------------------------------------------

def regexPgm2 :=
#strata
program Core;

function bad_re_loop (n : int) : regex {
    re.loop(re.range("a", "z"), 1, n)
}

procedure main(n : int) returns () {

    var n1 : int;
    n1 := 1;

    assert (!(str.in.re("0123456789a", bad_re_loop(n))));

    // NOTE: If `bad_re_loop` was inlined, we wouldn't get this
    // SMT encoding error because then `n1` would be replaced by
    // `1` by the time `re.loop` is encoded.
    assert (str.in.re("a", bad_re_loop(n1)));

};
#end

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" regexPgm2

---------------------------------------------------------------------

def regexPgm3 :=
#strata
program Core;

procedure main(n : int) returns () {

    var s : string;
    assert (!(str.in.re(s, re.none())));

};
#end

/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" regexPgm3

---------------------------------------------------------------------

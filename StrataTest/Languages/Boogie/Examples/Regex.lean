/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def regexPgm1 :=
#strata
program Boogie;

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


/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: hello_dot_ends_with_period
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #hello.) ~cannot_end_with_period))

Label: dot_ends_with_period
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #.) ~cannot_end_with_period))

Label: bye_exclaim_no_end_with_period
Assumptions:


Proof Obligation:
((~Str.InRegEx #bye!) ~cannot_end_with_period)

Label: ok_chars_str
Assumptions:


Proof Obligation:
((~Str.InRegEx #test-str-1) ~ok_chars_regex)

Label: cannot_contain_exclaim
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #test-str!) ~ok_chars_regex))

Label: has_to_be_at_least_1_char
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #) ~ok_chars_regex))

Label: cannot_exceed_10_chars
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #0123456789a) ~ok_chars_regex))

Label: optionally_a_check1
Assumptions:


Proof Obligation:
((~Str.InRegEx #a) ~optionally_a)

Label: optionally_a_check2
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #b) ~optionally_a))

Wrote problem to vcs/hello_dot_ends_with_period.smt2.
Wrote problem to vcs/dot_ends_with_period.smt2.
Wrote problem to vcs/bye_exclaim_no_end_with_period.smt2.
Wrote problem to vcs/ok_chars_str.smt2.
Wrote problem to vcs/cannot_contain_exclaim.smt2.
Wrote problem to vcs/has_to_be_at_least_1_char.smt2.
Wrote problem to vcs/cannot_exceed_10_chars.smt2.
Wrote problem to vcs/optionally_a_check1.smt2.
Wrote problem to vcs/optionally_a_check2.smt2.
---
info:
Obligation: hello_dot_ends_with_period
Result: verified

Obligation: dot_ends_with_period
Result: verified

Obligation: bye_exclaim_no_end_with_period
Result: verified

Obligation: ok_chars_str
Result: verified

Obligation: cannot_contain_exclaim
Result: verified

Obligation: has_to_be_at_least_1_char
Result: verified

Obligation: cannot_exceed_10_chars
Result: verified

Obligation: optionally_a_check1
Result: verified

Obligation: optionally_a_check2
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" regexPgm1

---------------------------------------------------------------------

def regexPgm2 :=
#strata
program Boogie;

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

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))

Label: assert_1
Assumptions:


Proof Obligation:
((~Str.InRegEx #a) (~bad_re_loop #1))

[Error] SMT Encoding error for obligation assert_0: ⏎
Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Evaluated program: func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (n1 : int) := init_n1_0
n1 := #1
assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
assert [assert_1] ((~Str.InRegEx #a) (~bad_re_loop #1))



[Error] SMT Encoding error for obligation assert_1: ⏎
Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Evaluated program: func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (n1 : int) := init_n1_0
n1 := #1
assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
assert [assert_1] ((~Str.InRegEx #a) (~bad_re_loop #1))



---
info:
Obligation: assert_0
Result: err [Error] SMT Encoding error for obligation assert_0: ⏎
Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Evaluated program: func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (n1 : int) := init_n1_0
n1 := #1
assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
assert [assert_1] ((~Str.InRegEx #a) (~bad_re_loop #1))




Obligation: assert_1
Result: err [Error] SMT Encoding error for obligation assert_1: ⏎
Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Evaluated program: func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (n1 : int) := init_n1_0
n1 := #1
assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
assert [assert_1] ((~Str.InRegEx #a) (~bad_re_loop #1))
-/
#guard_msgs in
#eval verify "cvc5" regexPgm2

---------------------------------------------------------------------

def regexPgm3 :=
#strata
program Boogie;

procedure main(n : int) returns () {

    var s : string;
    assert (!(str.in.re(s, re.none())));

};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx init_s_0) ~Re.None))

Wrote problem to vcs/assert_0.smt2.
---
info:
Obligation: assert_0
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" regexPgm3

---------------------------------------------------------------------

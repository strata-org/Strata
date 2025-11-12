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

Wrote problem to vcs/hello_dot_ends_with_period.smt2.
Wrote problem to vcs/dot_ends_with_period.smt2.
Wrote problem to vcs/bye_exclaim_no_end_with_period.smt2.
Wrote problem to vcs/ok_chars_str.smt2.
Wrote problem to vcs/cannot_contain_exclaim.smt2.
Wrote problem to vcs/has_to_be_at_least_1_char.smt2.
Wrote problem to vcs/cannot_exceed_10_chars.smt2.
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

    assert (!(str.in.re("0123456789a", bad_re_loop(n))));

};
#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: assert_0
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))

[Error] SMT Encoding error for obligation assert_0: ⏎
Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Evaluated program: func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))



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
body: assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
-/
#guard_msgs in
#eval verify "cvc5" regexPgm2

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
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #hello.) ~cannot_end_with_period))

Label: dot_ends_with_period
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #.) ~cannot_end_with_period))

Label: bye_exclaim_no_end_with_period
Property: assert
Assumptions:


Proof Obligation:
((~Str.InRegEx #bye!) ~cannot_end_with_period)

Label: ok_chars_str
Property: assert
Assumptions:


Proof Obligation:
((~Str.InRegEx #test-str-1) ~ok_chars_regex)

Label: cannot_contain_exclaim
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #test-str!) ~ok_chars_regex))

Label: has_to_be_at_least_1_char
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #) ~ok_chars_regex))

Label: cannot_exceed_10_chars
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #0123456789a) ~ok_chars_regex))

Label: optionally_a_check1
Property: assert
Assumptions:


Proof Obligation:
((~Str.InRegEx #a) ~optionally_a)

Label: optionally_a_check2
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #b) ~optionally_a))

---
info:
Obligation: hello_dot_ends_with_period
Property: assert
Result: ✅ pass

Obligation: dot_ends_with_period
Property: assert
Result: ✅ pass

Obligation: bye_exclaim_no_end_with_period
Property: assert
Result: ✅ pass

Obligation: ok_chars_str
Property: assert
Result: ✅ pass

Obligation: cannot_contain_exclaim
Property: assert
Result: ✅ pass

Obligation: has_to_be_at_least_1_char
Property: assert
Result: ✅ pass

Obligation: cannot_exceed_10_chars
Property: assert
Result: ✅ pass

Obligation: optionally_a_check1
Property: assert
Result: ✅ pass

Obligation: optionally_a_check2
Property: assert
Result: ✅ pass
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
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))

Label: assert_1
Property: assert
Assumptions:


Proof Obligation:
((~Str.InRegEx #a) (~bad_re_loop #1))



Result: Obligation: assert_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)


Evaluated program:
func bad_re_loop :  ((n : int)) → regex :=
  (((((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) (((~Re.Range : (arrow string (arrow string regex))) #a) #z)) #1) (n : int)))
(procedure main :  ((n : int)) → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: init (n1 : int) := init_n1_0
n1 := #1
assert [assert_0] (~Bool.Not ((~Str.InRegEx #0123456789a) (~bad_re_loop $__n0)))
assert [assert_1] ((~Str.InRegEx #a) (~bad_re_loop #1))



Result: Obligation: assert_1
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)


Evaluated program:
func bad_re_loop :  ((n : int)) → regex :=
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
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)

Obligation: assert_1
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (((~Re.Loop ((~Re.Range #a) #z)) #1) %0)
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
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not ((~Str.InRegEx init_s_0) ~Re.None))

---
info:
Obligation: assert_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" regexPgm3

---------------------------------------------------------------------

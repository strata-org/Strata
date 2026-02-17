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


/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: hello_dot_ends_with_period
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #hello. ~cannot_end_with_period))

Label: dot_ends_with_period
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #. ~cannot_end_with_period))

Label: bye_exclaim_no_end_with_period
Property: assert
Assumptions:


Proof Obligation:
(~Str.InRegEx #bye! ~cannot_end_with_period)

Label: ok_chars_str
Property: assert
Assumptions:


Proof Obligation:
(~Str.InRegEx #test-str-1 ~ok_chars_regex)

Label: cannot_contain_exclaim
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #test-str! ~ok_chars_regex))

Label: has_to_be_at_least_1_char
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx # ~ok_chars_regex))

Label: cannot_exceed_10_chars
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #0123456789a ~ok_chars_regex))

Label: optionally_a_check1
Property: assert
Assumptions:


Proof Obligation:
(~Str.InRegEx #a ~optionally_a)

Label: optionally_a_check2
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #b ~optionally_a))



Obligation hello_dot_ends_with_period: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: 


Evaluated program:
func cannot_end_with_period :  () → regex :=
  (((~Re.Comp : (arrow regex regex))
   ((~Re.Concat : (arrow regex (arrow regex regex)))
    ((~Re.Star : (arrow regex regex)) (~Re.All : regex))
    ((~Str.ToRegEx : (arrow string regex)) #.))))
func optionally_a :  () → regex :=
  (((~Re.Loop : (arrow regex (arrow int (arrow int regex)))) ((~Str.ToRegEx : (arrow string regex)) #a) #0 #1))
func ok_chars_regex :  () → regex :=
  (((~Re.Loop : (arrow regex (arrow int (arrow int regex))))
   ((~Re.Union : (arrow regex (arrow regex regex)))
    ((~Re.Range : (arrow string (arrow string regex))) #a #z)
    ((~Re.Union : (arrow regex (arrow regex regex)))
     ((~Re.Range : (arrow string (arrow string regex))) #0 #9)
     ((~Re.Union : (arrow regex (arrow regex regex)))
      ((~Str.ToRegEx : (arrow string regex)) #.)
      ((~Str.ToRegEx : (arrow string regex)) #-))))
   #1
   #10))
procedure main :  () → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    assert [hello_dot_ends_with_period] (~Bool.Not (~Str.InRegEx #hello. ~cannot_end_with_period))
    assert [dot_ends_with_period] (~Bool.Not (~Str.InRegEx #. ~cannot_end_with_period))
    assert [bye_exclaim_no_end_with_period] (~Str.InRegEx #bye! ~cannot_end_with_period)
    assert [ok_chars_str] (~Str.InRegEx #test-str-1 ~ok_chars_regex)
    assert [cannot_contain_exclaim] (~Bool.Not (~Str.InRegEx #test-str! ~ok_chars_regex))
    assert [has_to_be_at_least_1_char] (~Bool.Not (~Str.InRegEx # ~ok_chars_regex))
    assert [cannot_exceed_10_chars] (~Bool.Not (~Str.InRegEx #0123456789a ~ok_chars_regex))
    assert [optionally_a_check1] (~Str.InRegEx #a ~optionally_a)
    assert [optionally_a_check2] (~Bool.Not (~Str.InRegEx #b ~optionally_a))
  }
}
---
-/
#guard_msgs in
#eval verify regexPgm1

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

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))

Label: assert_1
Property: assert
Assumptions:


Proof Obligation:
(~Str.InRegEx #a (~bad_re_loop #1))



Result: Obligation: assert_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)


Evaluated program:
func bad_re_loop :  ((n : int)) → regex :=
  (((~Re.Loop : (arrow regex (arrow int (arrow int regex))))
   ((~Re.Range : (arrow string (arrow string regex))) #a #z)
   #1
   (n : int)))
procedure main :  ((n : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (n1 : int) := some init_n1_0
    n1 := #1
    assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))
    assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))
  }
}


Result: Obligation: assert_1
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)


Evaluated program:
func bad_re_loop :  ((n : int)) → regex :=
  (((~Re.Loop : (arrow regex (arrow int (arrow int regex))))
   ((~Re.Range : (arrow string (arrow string regex))) #a #z)
   #1
   (n : int)))
procedure main :  ((n : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (n1 : int) := some init_n1_0
    n1 := #1
    assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))
    assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))
  }
}
---
info:
Obligation: assert_0
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)

Obligation: assert_1
Property: assert
Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.
Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)
-/
#guard_msgs in
#eval verify regexPgm2

---------------------------------------------------------------------

def regexPgm3 :=
#strata
program Core;

procedure main(n : int) returns () {

    var s : string;
    assert (!(str.in.re(s, re.none())));

};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: assert_0
Property: assert
Assumptions:


Proof Obligation:
(~Bool.Not (~Str.InRegEx init_s_0 ~Re.None))



Obligation assert_0: SMT Solver Invocation Error!

Error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: t)))\n  procedure main :  ((n : int)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (n1 : int) := init_n1_0\n+     init (n1 : int) := some init_n1_0\n      n1 := #1\n      assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))\n      assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))\n    }\n  }\n \n \n  Result: Obligation: assert_1\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n \n \n  Evaluated program:\n  func bad_re_loop :  ((n : int)) → regex :=\n    (((~Re.Loop : (arrow regex (arrow int (arrow int regex))))\n     ((~Re.Range : (arrow string (arrow string regex))) #a #z)\n     #1\n     (n : int)))\n  procedure main :  ((n : int)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (n1 : int) := init_n1_0\n+     init (n1 : int) := some init_n1_0\n      n1 := #1\n      assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))\n      assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))\n    }\n  }\n  ---\n  info:\n  Obligation: assert_0\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n \n  Obligation: assert_1\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n","endPos":{"column":11,"line":278},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Regex.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":278},"severity":"error"}



Evaluated program:
procedure main :  ((n : int)) → ()
  modifies: []
  preconditions: 
  postconditions: 
{
  {
    init (s : string) := some init_s_0
    assert [assert_0] (~Bool.Not (~Str.InRegEx init_s_0 ~Re.None))
  }
}
---
error: stderr:could not execute external process 'cvc5'
 
Ensure cvc5 is on your PATH or use --solver to specify another SMT solver.
solver stdout: t)))\n  procedure main :  ((n : int)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (n1 : int) := init_n1_0\n+     init (n1 : int) := some init_n1_0\n      n1 := #1\n      assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))\n      assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))\n    }\n  }\n \n \n  Result: Obligation: assert_1\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n \n \n  Evaluated program:\n  func bad_re_loop :  ((n : int)) → regex :=\n    (((~Re.Loop : (arrow regex (arrow int (arrow int regex))))\n     ((~Re.Range : (arrow string (arrow string regex))) #a #z)\n     #1\n     (n : int)))\n  procedure main :  ((n : int)) → ()\n    modifies: []\n    preconditions: \n    postconditions: \n  {\n    {\n-     init (n1 : int) := init_n1_0\n+     init (n1 : int) := some init_n1_0\n      n1 := #1\n      assert [assert_0] (~Bool.Not (~Str.InRegEx #0123456789a (~bad_re_loop $__n0)))\n      assert [assert_1] (~Str.InRegEx #a (~bad_re_loop #1))\n    }\n  }\n  ---\n  info:\n  Obligation: assert_0\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n \n  Obligation: assert_1\n  Property: assert\n  Result: 🚨 Implementation Error! SMT Encoding Error! Natural numbers expected as indices for re.loop.\n  Original expression: (~Re.Loop (~Re.Range #a #z) #1 %0)\n","endPos":{"column":11,"line":278},"fileName":"/local/home/mimayere/strata2/StrataTest/Languages/Core/Examples/Regex.lean","isSilent":false,"keepFullRange":false,"kind":"[anonymous]","pos":{"column":0,"line":278},"severity":"error"}
-/
#guard_msgs in
#eval verify regexPgm3

---------------------------------------------------------------------

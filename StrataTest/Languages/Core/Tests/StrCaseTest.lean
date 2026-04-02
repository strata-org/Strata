/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Tests for Str.ToLower and Str.ToUpper

Covers two complementary aspects for each operation:

1. **Concrete evaluation** – `str.tolower` / `str.toupper` on literal strings
   is constant-folded by the evaluator's `concreteEval`; the SMT solver is
   never invoked.

2. **Symbolic reasoning** – when the argument is a symbolic variable the
   three axioms registered in `Factory.lean` are the only source of
   knowledge for the solver:
   - *Idempotence*: `f(f(s)) == f(s)`
   - *Length preservation*: `len(f(s)) == len(s)`
   - *Concat distributivity*: `f(s1 ++ s2) == f(s1) ++ f(s2)`
-/

namespace Strata

---------------------------------------------------------------------
-- Str.ToLower
---------------------------------------------------------------------

---------------------------------------------------------------------
-- 1a. Concrete evaluation (toLower)
---------------------------------------------------------------------

def strToLowerConcretePgm :=
#strata
program Core;

procedure main() returns () {

    // Basic ASCII case-folding
    assert [basic_lower]: str.tolower("Hello World") == "hello world";

    // Already-lowercase is a no-op
    assert [already_lower]: str.tolower("abc") == "abc";

    // Digits and punctuation are unchanged
    assert [symbols_unchanged]: str.tolower("abc123!") == "abc123!";

    // Empty string
    assert [empty_lower]: str.tolower("") == "";

    // Concrete idempotence (two calls on a literal)
    assert [concrete_idempotent]:
        str.tolower(str.tolower("MiXeD")) == str.tolower("MiXeD");
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: basic_lower
Property: assert
Obligation:
true

Label: already_lower
Property: assert
Obligation:
true

Label: symbols_unchanged
Property: assert
Obligation:
true

Label: empty_lower
Property: assert
Obligation:
true

Label: concrete_idempotent
Property: assert
Obligation:
true

---
info:
Obligation: basic_lower
Property: assert
Result: ✅ pass

Obligation: already_lower
Property: assert
Result: ✅ pass

Obligation: symbols_unchanged
Property: assert
Result: ✅ pass

Obligation: empty_lower
Property: assert
Result: ✅ pass

Obligation: concrete_idempotent
Property: assert
Result: ✅ pass
-/
#guard_msgs in -- Use .debug option here to show that no SMT files are generated
#eval verify strToLowerConcretePgm (options := .debug)

---------------------------------------------------------------------
-- 2a. Idempotence axiom (toLower)
---------------------------------------------------------------------

def strToLowerIdempotentPgm :=
#strata
program Core;

procedure main() returns () {

    var s : string;

    // Direct: toLower(toLower(s)) == toLower(s)
    assert [idempotent]:
        str.tolower(str.tolower(s)) == str.tolower(s);

    // Derived: if t is defined as toLower(s), then toLower(t) == t.
    // Requires substituting the assume into the idempotence axiom.
    var t : string;
    assume [t_is_lower]: t == str.tolower(s);
    assert [lower_of_lower_eq_t]: str.tolower(t) == t;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: idempotent
Property: assert
Obligation:
str.tolower(str.tolower($__s0)) == str.tolower($__s0)

Label: lower_of_lower_eq_t
Property: assert
Assumptions:
t_is_lower: $__t1 == str.tolower($__s0)
Obligation:
str.tolower($__t1) == $__t1

---
info:
Obligation: idempotent
Property: assert
Result: ✅ pass

Obligation: lower_of_lower_eq_t
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToLowerIdempotentPgm

---------------------------------------------------------------------
-- 3a. Length-preservation axiom (toLower)
---------------------------------------------------------------------

def strToLowerLengthPgm :=
#strata
program Core;

procedure main() returns () {

    var s : string;

    // Unconditional: length is always preserved
    assert [lower_preserves_length]:
        str.len(str.tolower(s)) == str.len(s);

    // With a concrete length assumption the same axiom should fire
    assume [s_len_5]: str.len(s) == 5;
    assert [lower_len_still_5]:
        str.len(str.tolower(s)) == 5;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: lower_preserves_length
Property: assert
Obligation:
str.len(str.tolower($__s0)) == str.len($__s0)

Label: lower_len_still_5
Property: assert
Assumptions:
s_len_5: str.len($__s0) == 5
Obligation:
str.len(str.tolower($__s0)) == 5

---
info:
Obligation: lower_preserves_length
Property: assert
Result: ✅ pass

Obligation: lower_len_still_5
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToLowerLengthPgm

---------------------------------------------------------------------
-- 4a. Concat-distributivity axiom (toLower)
---------------------------------------------------------------------

def strToLowerConcatPgm :=
#strata
program Core;

procedure main() returns () {

    var s1 : string, s2 : string;

    // Direct distributivity
    assert [lower_distributes_concat]:
        str.tolower(str.concat(s1, s2)) ==
        str.concat(str.tolower(s1), str.tolower(s2));

    // Combined: len(toLower(s1 ++ s2)) == len(s1) + len(s2).
    // Proof chain:
    //   distributivity  : toLower(s1++s2) == toLower(s1)++toLower(s2)
    //   SMT str theory  : len(toLower(s1)++toLower(s2)) == len(toLower(s1))+len(toLower(s2))
    //   len-preservation : len(toLower(si)) == len(si)
    assert [lower_concat_length]:
        str.len(str.tolower(str.concat(s1, s2))) ==
        str.len(s1) + str.len(s2);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: lower_distributes_concat
Property: assert
Obligation:
str.tolower(str.concat($__s10, $__s21)) == str.concat(str.tolower($__s10), str.tolower($__s21))

Label: lower_concat_length
Property: assert
Obligation:
str.len(str.tolower(str.concat($__s10, $__s21))) == str.len($__s10) + str.len($__s21)

---
info:
Obligation: lower_distributes_concat
Property: assert
Result: ✅ pass

Obligation: lower_concat_length
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToLowerConcatPgm

---------------------------------------------------------------------
-- Str.ToUpper
---------------------------------------------------------------------

---------------------------------------------------------------------
-- 1b. Concrete evaluation (toUpper)
---------------------------------------------------------------------

def strToUpperConcretePgm :=
#strata
program Core;

procedure main() returns () {

    // Basic ASCII case-folding
    assert [basic_upper]: str.toupper("Hello World") == "HELLO WORLD";

    // Already-uppercase is a no-op
    assert [already_upper]: str.toupper("ABC") == "ABC";

    // Digits and punctuation are unchanged
    assert [symbols_unchanged]: str.toupper("abc123!") == "ABC123!";

    // Empty string
    assert [empty_upper]: str.toupper("") == "";

    // Concrete idempotence (two calls on a literal)
    assert [concrete_idempotent]:
        str.toupper(str.toupper("MiXeD")) == str.toupper("MiXeD");
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: basic_upper
Property: assert
Obligation:
true

Label: already_upper
Property: assert
Obligation:
true

Label: symbols_unchanged
Property: assert
Obligation:
true

Label: empty_upper
Property: assert
Obligation:
true

Label: concrete_idempotent
Property: assert
Obligation:
true

---
info:
Obligation: basic_upper
Property: assert
Result: ✅ pass

Obligation: already_upper
Property: assert
Result: ✅ pass

Obligation: symbols_unchanged
Property: assert
Result: ✅ pass

Obligation: empty_upper
Property: assert
Result: ✅ pass

Obligation: concrete_idempotent
Property: assert
Result: ✅ pass
-/
#guard_msgs in -- Use .debug option here to show that no SMT files are generated
#eval verify strToUpperConcretePgm (options := .debug)

---------------------------------------------------------------------
-- 2b. Idempotence axiom (toUpper)
---------------------------------------------------------------------

def strToUpperIdempotentPgm :=
#strata
program Core;

procedure main() returns () {

    var s : string;

    // Direct: toUpper(toUpper(s)) == toUpper(s)
    assert [idempotent]:
        str.toupper(str.toupper(s)) == str.toupper(s);

    // Derived: if t is defined as toUpper(s), then toUpper(t) == t.
    // Requires substituting the assume into the idempotence axiom.
    var t : string;
    assume [t_is_upper]: t == str.toupper(s);
    assert [upper_of_upper_eq_t]: str.toupper(t) == t;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: idempotent
Property: assert
Obligation:
str.toupper(str.toupper($__s0)) == str.toupper($__s0)

Label: upper_of_upper_eq_t
Property: assert
Assumptions:
t_is_upper: $__t1 == str.toupper($__s0)
Obligation:
str.toupper($__t1) == $__t1

---
info:
Obligation: idempotent
Property: assert
Result: ✅ pass

Obligation: upper_of_upper_eq_t
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToUpperIdempotentPgm

---------------------------------------------------------------------
-- 3b. Length-preservation axiom (toUpper)
---------------------------------------------------------------------

def strToUpperLengthPgm :=
#strata
program Core;

procedure main() returns () {

    var s : string;

    // Unconditional: length is always preserved
    assert [upper_preserves_length]:
        str.len(str.toupper(s)) == str.len(s);

    // With a concrete length assumption the same axiom should fire
    assume [s_len_5]: str.len(s) == 5;
    assert [upper_len_still_5]:
        str.len(str.toupper(s)) == 5;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: upper_preserves_length
Property: assert
Obligation:
str.len(str.toupper($__s0)) == str.len($__s0)

Label: upper_len_still_5
Property: assert
Assumptions:
s_len_5: str.len($__s0) == 5
Obligation:
str.len(str.toupper($__s0)) == 5

---
info:
Obligation: upper_preserves_length
Property: assert
Result: ✅ pass

Obligation: upper_len_still_5
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToUpperLengthPgm

---------------------------------------------------------------------
-- 4b. Concat-distributivity axiom (toUpper)
---------------------------------------------------------------------

def strToUpperConcatPgm :=
#strata
program Core;

procedure main() returns () {

    var s1 : string, s2 : string;

    // Direct distributivity
    assert [upper_distributes_concat]:
        str.toupper(str.concat(s1, s2)) ==
        str.concat(str.toupper(s1), str.toupper(s2));

    // Combined: len(toUpper(s1 ++ s2)) == len(s1) + len(s2).
    // Proof chain:
    //   distributivity  : toUpper(s1++s2) == toUpper(s1)++toUpper(s2)
    //   SMT str theory  : len(toUpper(s1)++toUpper(s2)) == len(toUpper(s1))+len(toUpper(s2))
    //   len-preservation : len(toUpper(si)) == len(si)
    assert [upper_concat_length]:
        str.len(str.toupper(str.concat(s1, s2))) ==
        str.len(s1) + str.len(s2);
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: upper_distributes_concat
Property: assert
Obligation:
str.toupper(str.concat($__s10, $__s21)) == str.concat(str.toupper($__s10), str.toupper($__s21))

Label: upper_concat_length
Property: assert
Obligation:
str.len(str.toupper(str.concat($__s10, $__s21))) == str.len($__s10) + str.len($__s21)

---
info:
Obligation: upper_distributes_concat
Property: assert
Result: ✅ pass

Obligation: upper_concat_length
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify strToUpperConcatPgm

end Strata

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReParser

/-! ## Tests for Python Regex ReParser -/

namespace Strata.Python

section parseCharClass

/-- info: Except.ok (Strata.Python.RegexAST.range 'A' 'z', { byteIdx := 5 }) -/
#guard_msgs in
#eval parseCharClass "[A-z]" ⟨0⟩
/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [a-Z]: start character 'a' is greater than end character 'Z'"
  "[a-Z]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[a-Z]" ⟨0⟩

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [a-0]: start character 'a' is greater than end character '0'"
  "[a-0]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[a-0]" ⟨0⟩

/--
info: Except.ok (Strata.Python.RegexAST.union
   (Strata.Python.RegexAST.union (Strata.Python.RegexAST.range 'a' 'z') (Strata.Python.RegexAST.range '0' '9'))
   (Strata.Python.RegexAST.range 'A' 'Z'),
 { byteIdx := 11 })
-/
#guard_msgs in
#eval parseCharClass "[a-z0-9A-Z]" ⟨0⟩
/--
info: Except.ok (Strata.Python.RegexAST.union (Strata.Python.RegexAST.char '0') (Strata.Python.RegexAST.range 'a' 'z'),
 { byteIdx := 6 })
-/
#guard_msgs in
#eval parseCharClass "[0a-z]" ⟨0⟩
/-- info: Except.ok (Strata.Python.RegexAST.char 'a', { byteIdx := 3 }) -/
#guard_msgs in
#eval parseCharClass "[a]" ⟨0⟩
/--
info: Except.error (Strata.Python.ParseError.patternError "Expected '[' at start of character class" "a" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseCharClass "a" ⟨0⟩

end parseCharClass

section Test.parseBounds

/-- info: Except.ok (23, 23, { byteIdx := 4 }) -/
#guard_msgs in
#eval parseBounds "{23}" ⟨0⟩
/-- info: Except.ok (100, 100, { byteIdx := 9 }) -/
#guard_msgs in
#eval parseBounds "{100,100}" ⟨0⟩
/--
info: Except.error (Strata.Python.ParseError.patternError "Expected '{' at start of bounds" "abc" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseBounds "abc" ⟨0⟩
/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100"
  "{100,2}"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseBounds "{100,2}" ⟨0⟩

end Test.parseBounds

section Test.parseTop

/--
info: Except.ok (Strata.Python.RegexAST.union
  (Strata.Python.RegexAST.union (Strata.Python.RegexAST.char '1') (Strata.Python.RegexAST.range '0' '1'))
  (Strata.Python.RegexAST.char '5'))
-/
#guard_msgs in
/-
Cross-checked with:
>>> re._parser.parse('[10-15]')
[(IN, [(LITERAL, 49), (RANGE, (48, 49)), (LITERAL, 53)])]
-/
#eval parseTop "[10-15]"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.char 'a')
  (Strata.Python.RegexAST.optional (Strata.Python.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "ab?"

/-- info: Except.ok (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)) -/
#guard_msgs in
#eval parseTop ".*"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.concat
        (Strata.Python.RegexAST.concat
          (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar))
          (Strata.Python.RegexAST.char '.'))
        (Strata.Python.RegexAST.char '.'))
      (Strata.Python.RegexAST.anychar))
    (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)))
  (Strata.Python.RegexAST.char 'x'))
-/
#guard_msgs in
#eval parseTop ".*\\.\\...*x"

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Quantifier '{' at position 2 has nothing to quantify"
  ".*{1,10}"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop ".*{1,10}"

/-- info: Except.ok (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)) -/
#guard_msgs in
#eval parseTop ".*"

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Quantifier '*' at position 0 has nothing to quantify"
  "*abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "*abc"

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Quantifier '+' at position 0 has nothing to quantify"
  "+abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "+abc"

/-- info: Except.ok (Strata.Python.RegexAST.loop (Strata.Python.RegexAST.range 'a' 'z') 1 10) -/
#guard_msgs in
#eval parseTop "[a-z]{1,10}"

/-- info: Except.ok (Strata.Python.RegexAST.loop (Strata.Python.RegexAST.range 'a' 'z') 10 10) -/
#guard_msgs in
#eval parseTop "[a-z]{10}"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.anchor_start)
      (Strata.Python.RegexAST.union (Strata.Python.RegexAST.range 'a' 'z') (Strata.Python.RegexAST.range '0' '9')))
    (Strata.Python.RegexAST.loop
      (Strata.Python.RegexAST.union
        (Strata.Python.RegexAST.union
          (Strata.Python.RegexAST.union (Strata.Python.RegexAST.range 'a' 'z') (Strata.Python.RegexAST.range '0' '9'))
          (Strata.Python.RegexAST.char '.'))
        (Strata.Python.RegexAST.char '-'))
      1
      10))
  (Strata.Python.RegexAST.anchor_end))
-/
#guard_msgs in
#eval parseTop "^[a-z0-9][a-z0-9.-]{1,10}$"

-- Test escape sequences (need \\ in Lean strings to get single \)
/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.concat
        (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar))
        (Strata.Python.RegexAST.char '.'))
      (Strata.Python.RegexAST.char '.'))
    (Strata.Python.RegexAST.anychar))
  (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)))
-/
#guard_msgs in
#eval parseTop ".*\\.\\...*"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.concat
        (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.anchor_start) (Strata.Python.RegexAST.char 'x'))
        (Strata.Python.RegexAST.char 'n'))
      (Strata.Python.RegexAST.char '-'))
    (Strata.Python.RegexAST.char '-'))
  (Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)))
-/
#guard_msgs in
#eval parseTop "^xn--.*"

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [x-c]: start character 'x' is greater than end character 'c'"
  "[x-c]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "[x-c]"

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [1-0]: start character '1' is greater than end character '0'"
  "[51-08]"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop "[51-08]"

/--
info: Except.ok (Strata.Python.RegexAST.group
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b'))
    (Strata.Python.RegexAST.char 'c')))
-/
#guard_msgs in
#eval parseTop "(abc)"

/--
info: Except.ok (Strata.Python.RegexAST.group
  (Strata.Python.RegexAST.union (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "(a|b)"

/--
info: Except.ok (Strata.Python.RegexAST.union
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.anchor_start) (Strata.Python.RegexAST.char 'a'))
    (Strata.Python.RegexAST.anchor_end))
  (Strata.Python.RegexAST.concat
    (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.anchor_start) (Strata.Python.RegexAST.char 'b'))
    (Strata.Python.RegexAST.anchor_end)))
-/
#guard_msgs in
#eval parseTop "^a$|^b$"

/--
info: Except.ok (Strata.Python.RegexAST.union
  (Strata.Python.RegexAST.group
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.anchor_start) (Strata.Python.RegexAST.char 'a'))
      (Strata.Python.RegexAST.anchor_end)))
  (Strata.Python.RegexAST.group
    (Strata.Python.RegexAST.concat
      (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.anchor_start) (Strata.Python.RegexAST.char 'b'))
      (Strata.Python.RegexAST.anchor_end))))
-/
#guard_msgs in
#eval parseTop "(^a$)|(^b$)"

/--
info: Except.ok (Strata.Python.RegexAST.star
  (Strata.Python.RegexAST.group
    (Strata.Python.RegexAST.union
      (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b'))
      (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'c') (Strata.Python.RegexAST.char 'd')))))
-/
#guard_msgs in
#eval parseTop "(ab|cd)*"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.char 'a')
  (Strata.Python.RegexAST.optional (Strata.Python.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "ab?"

/-- info: Except.ok (Strata.Python.RegexAST.optional (Strata.Python.RegexAST.range 'a' 'z')) -/
#guard_msgs in
#eval parseTop "[a-z]?"

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Positive lookahead (?=...) is not supported"
  "(?=test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?=test)"

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Negative lookahead (?!...) is not supported"
  "(?!silly-)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?!silly-)"

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?:abc)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?:abc)"

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?P<name>test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?P<name>test)"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\d is not supported" "\\d+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\d+"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\w is not supported" "\\w*" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\w*"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\s is not supported" "\\s+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\s+"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Escape sequence \\n is not supported" "test\\n" { byteIdx := 4 })
-/
#guard_msgs in
#eval parseTop "test\\n"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Backreference \\1 is not supported" "(a)\\1" { byteIdx := 3 })
-/
#guard_msgs in
#eval parseTop "(a)\\1"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier *? is not supported" "a*?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a*?"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier +? is not supported" "a+?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a+?"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier ?? is not supported" "a??" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a??"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier *+ is not supported" "a*+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a*+"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier ++ is not supported" "a++" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a++"

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier ?+ is not supported" "a?+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a?+"

/--
info: Except.ok (Strata.Python.RegexAST.union
  (Strata.Python.RegexAST.empty)
  (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'x') (Strata.Python.RegexAST.char 'y')))
-/
#guard_msgs in
#eval parseTop "|xy"

/--
info: Except.ok (Strata.Python.RegexAST.concat
  (Strata.Python.RegexAST.char 'a')
  (Strata.Python.RegexAST.group
    (Strata.Python.RegexAST.union (Strata.Python.RegexAST.empty) (Strata.Python.RegexAST.char 'b'))))
-/
#guard_msgs in
#eval parseTop "a(|b)"

/--
info: Except.error (Strata.Python.ParseError.patternError "Unbalanced parenthesis" "x)" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "x)"

/--
info: Except.error (Strata.Python.ParseError.patternError "Unbalanced parenthesis" "())" { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop "())"

end Test.parseTop

end Strata.Python

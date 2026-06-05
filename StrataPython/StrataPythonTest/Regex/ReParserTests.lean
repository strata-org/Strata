/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.Regex.ReParser

meta section

/-! ## Tests for Python Regex ReParser -/

namespace StrataPython

section parseCharClass

/-- info: Except.ok (StrataPython.RegexAST.range 'A' 'z', { byteIdx := 5 }) -/
#guard_msgs in
#eval parseCharClass "[A-z]" ⟨0⟩
/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid character range [a-Z]: start character 'a' is greater than end character 'Z'"
  "[a-Z]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[a-Z]" ⟨0⟩

/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid character range [a-0]: start character 'a' is greater than end character '0'"
  "[a-0]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[a-0]" ⟨0⟩

/--
info: Except.ok (StrataPython.RegexAST.union
   (StrataPython.RegexAST.union (StrataPython.RegexAST.range 'a' 'z') (StrataPython.RegexAST.range '0' '9'))
   (StrataPython.RegexAST.range 'A' 'Z'),
 { byteIdx := 11 })
-/
#guard_msgs in
#eval parseCharClass "[a-z0-9A-Z]" ⟨0⟩
/--
info: Except.ok (StrataPython.RegexAST.union (StrataPython.RegexAST.char '0') (StrataPython.RegexAST.range 'a' 'z'),
 { byteIdx := 6 })
-/
#guard_msgs in
#eval parseCharClass "[0a-z]" ⟨0⟩
/-- info: Except.ok (StrataPython.RegexAST.char 'a', { byteIdx := 3 }) -/
#guard_msgs in
#eval parseCharClass "[a]" ⟨0⟩
/--
info: Except.error (StrataPython.ParseError.patternError "Expected '[' at start of character class" "a" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseCharClass "a" ⟨0⟩

-- Incomplete escape sequences
/--
info: Except.error (StrataPython.ParseError.patternError
  "Incomplete escape sequence in character class"
  "[a\\"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseCharClass "[a\\" ⟨0⟩

-- Escape sequences inside character classes
/-- info: Except.ok (StrataPython.RegexAST.char '.', { byteIdx := 4 }) -/
#guard_msgs in
#eval parseCharClass "[\\.] " ⟨0⟩  -- trailing space so string is valid; byteIdx 4 = past ']'

/-- info: Except.ok (StrataPython.RegexAST.char '-', { byteIdx := 4 }) -/
#guard_msgs in
#eval parseCharClass "[\\-] " ⟨0⟩  -- trailing space so string is valid; byteIdx 4 = past ']'

/--
info: Except.ok (StrataPython.RegexAST.union (StrataPython.RegexAST.char '.') (StrataPython.RegexAST.char '-'),
 { byteIdx := 6 })
-/
#guard_msgs in
#eval parseCharClass "[\\.\\-]" ⟨0⟩

-- Escape as range start: [\.-z] = range from '.' to 'z'
/-- info: Except.ok (StrataPython.RegexAST.range '.' 'z', { byteIdx := 6 }) -/
#guard_msgs in
#eval parseCharClass "[\\.-z]" ⟨0⟩

-- Escape as range start with invalid bounds: [\.-,] errors (. > ,)
/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid character range [.-,]: start character '.' is greater than end character ','"
  "[\\.-,]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[\\.-,]" ⟨0⟩

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Special sequence \\d in character class is not supported"
  "[\\d]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[\\d]" ⟨0⟩

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Escape sequence \\n in character class is not supported"
  "[\\n]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseCharClass "[\\n]" ⟨0⟩

end parseCharClass

section Test.parseBounds

/-- info: Except.ok (23, 23, { byteIdx := 4 }) -/
#guard_msgs in
#eval parseBounds "{23}" ⟨0⟩
/-- info: Except.ok (100, 100, { byteIdx := 9 }) -/
#guard_msgs in
#eval parseBounds "{100,100}" ⟨0⟩
/--
info: Except.error (StrataPython.ParseError.patternError "Expected '{' at start of bounds" "abc" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseBounds "abc" ⟨0⟩
/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100"
  "{100,2}"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseBounds "{100,2}" ⟨0⟩

end Test.parseBounds

section Test.parseTop

/--
info: Except.ok (StrataPython.RegexAST.union
  (StrataPython.RegexAST.union (StrataPython.RegexAST.char '1') (StrataPython.RegexAST.range '0' '1'))
  (StrataPython.RegexAST.char '5'))
-/
#guard_msgs in
/-
Cross-checked with:
>>> re._parser.parse('[10-15]')
[(IN, [(LITERAL, 49), (RANGE, (48, 49)), (LITERAL, 53)])]
-/
#eval parseTop "[10-15]"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.char 'a')
  (StrataPython.RegexAST.optional (StrataPython.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "ab?"

/-- info: Except.ok (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar)) -/
#guard_msgs in
#eval parseTop ".*"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.concat
        (StrataPython.RegexAST.concat
          (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar))
          (StrataPython.RegexAST.char '.'))
        (StrataPython.RegexAST.char '.'))
      (StrataPython.RegexAST.anychar))
    (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar)))
  (StrataPython.RegexAST.char 'x'))
-/
#guard_msgs in
#eval parseTop ".*\\.\\...*x"

/--
info: Except.error (StrataPython.ParseError.patternError
  "Quantifier '{' at position 2 has nothing to quantify"
  ".*{1,10}"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop ".*{1,10}"

/-- info: Except.ok (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar)) -/
#guard_msgs in
#eval parseTop ".*"

/--
info: Except.error (StrataPython.ParseError.patternError
  "Quantifier '*' at position 0 has nothing to quantify"
  "*abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "*abc"

/--
info: Except.error (StrataPython.ParseError.patternError
  "Quantifier '+' at position 0 has nothing to quantify"
  "+abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "+abc"

/-- info: Except.ok (StrataPython.RegexAST.loop (StrataPython.RegexAST.range 'a' 'z') 1 10) -/
#guard_msgs in
#eval parseTop "[a-z]{1,10}"

/-- info: Except.ok (StrataPython.RegexAST.loop (StrataPython.RegexAST.range 'a' 'z') 10 10) -/
#guard_msgs in
#eval parseTop "[a-z]{10}"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.anchor_start)
      (StrataPython.RegexAST.union (StrataPython.RegexAST.range 'a' 'z') (StrataPython.RegexAST.range '0' '9')))
    (StrataPython.RegexAST.loop
      (StrataPython.RegexAST.union
        (StrataPython.RegexAST.union
          (StrataPython.RegexAST.union (StrataPython.RegexAST.range 'a' 'z') (StrataPython.RegexAST.range '0' '9'))
          (StrataPython.RegexAST.char '.'))
        (StrataPython.RegexAST.char '-'))
      1
      10))
  (StrataPython.RegexAST.anchor_end))
-/
#guard_msgs in
#eval parseTop "^[a-z0-9][a-z0-9.-]{1,10}$"

-- Incomplete escape sequence at top level
/--
info: Except.error (StrataPython.ParseError.patternError "Incomplete escape sequence" "\\" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\"

-- Test escape sequences (need \\ in Lean strings to get single \)
/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.concat
        (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar))
        (StrataPython.RegexAST.char '.'))
      (StrataPython.RegexAST.char '.'))
    (StrataPython.RegexAST.anychar))
  (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar)))
-/
#guard_msgs in
#eval parseTop ".*\\.\\...*"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.concat
        (StrataPython.RegexAST.concat (StrataPython.RegexAST.anchor_start) (StrataPython.RegexAST.char 'x'))
        (StrataPython.RegexAST.char 'n'))
      (StrataPython.RegexAST.char '-'))
    (StrataPython.RegexAST.char '-'))
  (StrataPython.RegexAST.star (StrataPython.RegexAST.anychar)))
-/
#guard_msgs in
#eval parseTop "^xn--.*"

/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid character range [x-c]: start character 'x' is greater than end character 'c'"
  "[x-c]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "[x-c]"

/--
info: Except.error (StrataPython.ParseError.patternError
  "Invalid character range [1-0]: start character '1' is greater than end character '0'"
  "[51-08]"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop "[51-08]"

/--
info: Except.ok (StrataPython.RegexAST.group
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat (StrataPython.RegexAST.char 'a') (StrataPython.RegexAST.char 'b'))
    (StrataPython.RegexAST.char 'c')))
-/
#guard_msgs in
#eval parseTop "(abc)"

/--
info: Except.ok (StrataPython.RegexAST.group
  (StrataPython.RegexAST.union (StrataPython.RegexAST.char 'a') (StrataPython.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "(a|b)"

/--
info: Except.ok (StrataPython.RegexAST.union
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat (StrataPython.RegexAST.anchor_start) (StrataPython.RegexAST.char 'a'))
    (StrataPython.RegexAST.anchor_end))
  (StrataPython.RegexAST.concat
    (StrataPython.RegexAST.concat (StrataPython.RegexAST.anchor_start) (StrataPython.RegexAST.char 'b'))
    (StrataPython.RegexAST.anchor_end)))
-/
#guard_msgs in
#eval parseTop "^a$|^b$"

/--
info: Except.ok (StrataPython.RegexAST.union
  (StrataPython.RegexAST.group
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.concat (StrataPython.RegexAST.anchor_start) (StrataPython.RegexAST.char 'a'))
      (StrataPython.RegexAST.anchor_end)))
  (StrataPython.RegexAST.group
    (StrataPython.RegexAST.concat
      (StrataPython.RegexAST.concat (StrataPython.RegexAST.anchor_start) (StrataPython.RegexAST.char 'b'))
      (StrataPython.RegexAST.anchor_end))))
-/
#guard_msgs in
#eval parseTop "(^a$)|(^b$)"

/--
info: Except.ok (StrataPython.RegexAST.star
  (StrataPython.RegexAST.group
    (StrataPython.RegexAST.union
      (StrataPython.RegexAST.concat (StrataPython.RegexAST.char 'a') (StrataPython.RegexAST.char 'b'))
      (StrataPython.RegexAST.concat (StrataPython.RegexAST.char 'c') (StrataPython.RegexAST.char 'd')))))
-/
#guard_msgs in
#eval parseTop "(ab|cd)*"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.char 'a')
  (StrataPython.RegexAST.optional (StrataPython.RegexAST.char 'b')))
-/
#guard_msgs in
#eval parseTop "ab?"

/-- info: Except.ok (StrataPython.RegexAST.optional (StrataPython.RegexAST.range 'a' 'z')) -/
#guard_msgs in
#eval parseTop "[a-z]?"

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Positive lookahead (?=...) is not supported"
  "(?=test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?=test)"

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Negative lookahead (?!...) is not supported"
  "(?!silly-)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?!silly-)"

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?:abc)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?:abc)"

/--
info: Except.error (StrataPython.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?P<name>test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "(?P<name>test)"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Special sequence \\d is not supported" "\\d+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\d+"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Special sequence \\w is not supported" "\\w*" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\w*"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Special sequence \\s is not supported" "\\s+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseTop "\\s+"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Escape sequence \\n is not supported" "test\\n" { byteIdx := 4 })
-/
#guard_msgs in
#eval parseTop "test\\n"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Backreference \\1 is not supported" "(a)\\1" { byteIdx := 3 })
-/
#guard_msgs in
#eval parseTop "(a)\\1"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Non-greedy quantifier *? is not supported" "a*?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a*?"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Non-greedy quantifier +? is not supported" "a+?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a+?"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Non-greedy quantifier ?? is not supported" "a??" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a??"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Possessive quantifier *+ is not supported" "a*+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a*+"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Possessive quantifier ++ is not supported" "a++" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a++"

/--
info: Except.error (StrataPython.ParseError.unimplemented "Possessive quantifier ?+ is not supported" "a?+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "a?+"

/--
info: Except.ok (StrataPython.RegexAST.union
  (StrataPython.RegexAST.empty)
  (StrataPython.RegexAST.concat (StrataPython.RegexAST.char 'x') (StrataPython.RegexAST.char 'y')))
-/
#guard_msgs in
#eval parseTop "|xy"

/--
info: Except.ok (StrataPython.RegexAST.concat
  (StrataPython.RegexAST.char 'a')
  (StrataPython.RegexAST.group
    (StrataPython.RegexAST.union (StrataPython.RegexAST.empty) (StrataPython.RegexAST.char 'b'))))
-/
#guard_msgs in
#eval parseTop "a(|b)"

/--
info: Except.error (StrataPython.ParseError.patternError "Unbalanced parenthesis" "x)" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseTop "x)"

/--
info: Except.error (StrataPython.ParseError.patternError "Unbalanced parenthesis" "())" { byteIdx := 2 })
-/
#guard_msgs in
#eval parseTop "())"

end Test.parseTop

end StrataPython
end

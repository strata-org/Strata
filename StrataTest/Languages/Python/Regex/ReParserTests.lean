/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReParser

/-! ## Tests for Python Regex ReParser -/

namespace Strata.Python

section Test.parseCharClass

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

end Test.parseCharClass

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

end Test.parseTop

end Strata.Python

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Strata
namespace Python

/-
Parser and translator for some basic regular expression patterns supported by
Python's `re` library
Ref.: https://docs.python.org/3/library/re.html

Also see
https://github.com/python/cpython/blob/759a048d4bea522fda2fe929be0fba1650c62b0e/Lib/re/_parser.py
for a reference implementation.
-/

-------------------------------------------------------------------------------

inductive ParseError where
  /--
    `patternError` is raised when Python's `re.patternError` exception is
    raised.
    [Reference: Python's re exceptions](https://docs.python.org/3/library/re.html#exceptions):

    "Exception raised when a string passed to one of the functions here is not a
    valid regular expression (for example, it might contain unmatched
    parentheses) or when some other error occurs during compilation or matching.
    It is never an error if a string contains no match for a pattern."
  -/
  | patternError  (message : String) (pattern : String) (pos : String.Pos)
  /--
  `unimplemented` is raised whenever we don't support some regex operations
  (e.g., lookahead assertions).
  -/
  | unimplemented (message : String) (pattern : String) (pos : String.Pos)
  deriving Repr

def ParseError.toString : ParseError → String
  | .patternError msg pat pos => s!"Pattern error at position {pos.byteIdx}: {msg} in pattern '{pat}'"
  | .unimplemented msg pat pos => s!"Unimplemented at position {pos.byteIdx}: {msg} in pattern '{pat}'"

instance : ToString ParseError where
  toString := ParseError.toString

-------------------------------------------------------------------------------

/--
Regular Expression Nodes
-/
inductive RegexAST where
  /-- Single literal character: `a` -/
  | char : Char → RegexAST
  /-- Character range: `[a-z]` -/
  | range : Char → Char → RegexAST
  /-- Alternation: `a|b` -/
  | union : RegexAST → RegexAST → RegexAST
  /-- Concatenation: `ab` -/
  | concat : RegexAST → RegexAST → RegexAST
  /-- Any character: `.` -/
  | anychar : RegexAST
  /-- Zero or more: `a*` -/
  | star : RegexAST → RegexAST
  /-- One or more: `a+` -/
  | plus : RegexAST → RegexAST
  /-- Zero or one: `a?` -/
  | optional : RegexAST → RegexAST
  /-- Bounded repetition: `a{n,m}` -/
  | loop : RegexAST → Nat → Nat → RegexAST
  /-- Start of string: `^` -/
  | anchor_start : RegexAST
  /-- End of string: `$` -/
  | anchor_end : RegexAST
  /-- Grouping: `(abc)` -/
  | group : RegexAST → RegexAST
  /-- Empty string: `()` or `""` -/
  | empty : RegexAST
  /-- Complement: `[^a-z]` -/
  | complement : RegexAST → RegexAST
  deriving Inhabited, Repr

-------------------------------------------------------------------------------

/-- Parse character class like [a-z], [0-9], etc. into union of ranges and chars. -/
def parseCharClass (s : String) (pos : String.Pos) : Except ParseError (RegexAST × String.Pos) := do
  if s.get? pos != some '[' then throw (.patternError "Expected '[' at start of character class" s pos)
  let mut i := s.next pos

  -- Check for complement (negation) with leading ^
  let isComplement := !s.atEnd i && s.get? i == some '^'
  if isComplement then
    i := s.next i

  let mut result : Option RegexAST := none

  -- Process each element in the character class.
  while !s.atEnd i && s.get? i != some ']' do
    let some c1 := s.get? i | throw (.patternError "Invalid character in class" s i)
    let i1 := s.next i
    -- Check for range pattern: c1-c2.
    if !s.atEnd i1 && s.get? i1 == some '-' then
      let i2 := s.next i1
      if !s.atEnd i2 && s.get? i2 != some ']' then
        let some c2 := s.get? i2 | throw (.patternError "Invalid character in range" s i2)
        if c1 > c2 then
          throw (.patternError s!"Invalid character range [{c1}-{c2}]: \
                                  start character '{c1}' is greater than end character '{c2}'" s i)
        let r := RegexAST.range c1 c2
        -- Union with previous elements.
        result := some (match result with | none => r | some prev => RegexAST.union prev r)
        i := s.next i2
        continue
    -- Single character.
    let r := RegexAST.char c1
    result := some (match result with | none => r | some prev => RegexAST.union prev r)
    i := s.next i

  let some ast := result | throw (.patternError "Empty character class" s pos)
  let finalAst := if isComplement then RegexAST.complement ast else ast
  pure (finalAst, s.next i)

-------------------------------------------------------------------------------

/-- Parse numeric repeats like `{10}` or `{1,10}` into min and max bounds -/
def parseBounds (s : String) (pos : String.Pos) : Except ParseError (Nat × Nat × String.Pos) := do
  if s.get? pos != some '{' then throw (.patternError "Expected '{' at start of bounds" s pos)
  let mut i := s.next pos
  let mut numStr := ""

  -- Parse first number.
  while !s.atEnd i && (s.get? i).any Char.isDigit do
    numStr := numStr.push ((s.get? i).get!)
    i := s.next i

  let some n := numStr.toNat? | throw (.patternError "Invalid minimum bound" s pos)

  -- Check for comma (range) or closing brace (exact count).
  match s.get? i with
  | some '}' => pure (n, n, s.next i)  -- {n} means exactly n times.
  | some ',' =>
    i := s.next i
    -- Parse maximum bound
    numStr := ""
    while !s.atEnd i && (s.get? i).any Char.isDigit do
      numStr := numStr.push ((s.get? i).get!)
      i := s.next i
    let some max := numStr.toNat? | throw (.patternError "Invalid maximum bound" s i)
    if s.get? i != some '}' then throw (.patternError "Expected '}' at end of bounds" s i)
    -- Validate bounds order
    if max < n then
      throw (.patternError s!"Invalid repeat bounds \{{n},{max}}: \
                              maximum {max} is less than minimum {n}" s pos)
    pure (n, max, s.next i)
  | _ => throw (.patternError "Invalid bounds syntax" s i)

-------------------------------------------------------------------------------

mutual
/-- Parse group (content between parentheses) with alternation (`|`) support. -/
partial def parseGroup (s : String) (pos : String.Pos) : Except ParseError (RegexAST × String.Pos) := do
  if s.get? pos != some '(' then throw (.patternError "Expected '(' at start of group" s pos)
  let mut i := s.next pos

  -- Check for extension notation (?...
  if !s.atEnd i && s.get? i == some '?' then
    let i1 := s.next i
    if !s.atEnd i1 then
      match s.get? i1 with
      | some '=' => throw (.unimplemented "Positive lookahead (?=...) is not supported" s pos)
      | some '!' => throw (.unimplemented "Negative lookahead (?!...) is not supported" s pos)
      | _ => throw (.unimplemented "Extension notation (?...) is not supported" s pos)

  let mut alternatives : List (List RegexAST) := [[]]

  -- Parse elements until we hit ')'.
  while !s.atEnd i && s.get? i != some ')' do
    if s.get? i == some '|' then
      -- Start new alternative.
      alternatives := [] :: alternatives
      i := s.next i
    else
      let (ast, nextPos) ← parseRegex s i
      -- Add to current alternative.
      alternatives := match alternatives with
        | [] => [[ast]]
        | head :: tail => (ast :: head) :: tail
      i := nextPos

  if s.get? i != some ')' then throw (.patternError "Unclosed group: missing ')'" s i)

  -- Build result: concatenate each alternative, then union them.
  let concatAlternatives := alternatives.reverse.filterMap fun alt =>
    match alt.reverse with
    | [] => none
    | [single] => some single
    | head :: tail => some (tail.foldl RegexAST.concat head)

  match concatAlternatives with
  | [] =>
    -- Empty group matches empty string.
    pure (.group .empty, s.next i)
  | [single] => pure (RegexAST.group single, s.next i)
  | head :: tail =>
    let grouped := tail.foldl RegexAST.union head
    pure (.group grouped, s.next i)

/-- Parse single regex element with optional numeric repeat bounds. -/
partial def parseRegex (s : String) (pos : String.Pos) : Except ParseError (RegexAST × String.Pos) := do
  if s.atEnd pos then throw (.patternError "Unexpected end of regex" s pos)

  let some c := s.get? pos | throw (.patternError "Invalid position" s pos)

  -- Detect invalid quantifier at start
  if c == '*' || c == '+' || c == '{' || c == '?' then
    throw (.patternError s!"Quantifier '{c}' at position {pos} has nothing to quantify" s pos)

  -- Parse base element (anchor, char class, group, anychar, escape, or single char).
  let (base, nextPos) ← match c with
    | '^' => pure (RegexAST.anchor_start, s.next pos)
    | '$' => pure (RegexAST.anchor_end, s.next pos)
    | '[' => parseCharClass s pos
    | '(' => parseGroup s pos
    | '.' => pure (RegexAST.anychar, s.next pos)
    | '\\' =>
      -- Handle escape sequence.
      -- Note: Python uses a single backslash as an escape character, but Lean
      -- strings need to escape that. After DDMification, we will see two
      -- backslashes in Strata for every Python backslash.
      let nextPos := s.next pos
      if s.atEnd nextPos then throw (.patternError "Incomplete escape sequence at end of regex" s pos)
      let some escapedChar := s.get? nextPos | throw (.patternError "Invalid escape position" s nextPos)
      -- Check for special sequences (unsupported right now).
      match escapedChar with
      | 'A' | 'b' | 'B' | 'd' | 'D' | 's' | 'S' | 'w' | 'W' | 'z' | 'Z' =>
        throw (.unimplemented s!"Special sequence \\{escapedChar} is not supported" s pos)
      | 'a' | 'f' | 'n' | 'N' | 'r' | 't' | 'u' | 'U' | 'v' | 'x' =>
        throw (.unimplemented s!"Escape sequence \\{escapedChar} is not supported" s pos)
      | c =>
        if c.isDigit then
          throw (.unimplemented s!"Backreference \\{c} is not supported" s pos)
        else
          pure (RegexAST.char escapedChar, s.next nextPos)
    | _ => pure (RegexAST.char c, s.next pos)

  -- Check for numeric repeat suffix on base element (but not on anchors)
  match base with
  | .anchor_start | .anchor_end => pure (base, nextPos)
  | _ =>
    if !s.atEnd nextPos then
      match s.get? nextPos with
      | some '{' =>
        let (min, max, finalPos) ← parseBounds s nextPos
        pure (RegexAST.loop base min max, finalPos)
      | some '*' =>
        let afterStar := s.next nextPos
        if !s.atEnd afterStar then
          match s.get? afterStar with
          | some '?' => throw (.unimplemented "Non-greedy quantifier *? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier *+ is not supported" s nextPos)
          | _ => pure (RegexAST.star base, afterStar)
        else pure (RegexAST.star base, afterStar)
      | some '+' =>
        let afterPlus := s.next nextPos
        if !s.atEnd afterPlus then
          match s.get? afterPlus with
          | some '?' => throw (.unimplemented "Non-greedy quantifier +? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier ++ is not supported" s nextPos)
          | _ => pure (RegexAST.plus base, afterPlus)
        else pure (RegexAST.plus base, afterPlus)
      | some '?' =>
        let afterQuestion := s.next nextPos
        if !s.atEnd afterQuestion then
          match s.get? afterQuestion with
          | some '?' => throw (.unimplemented "Non-greedy quantifier ?? is not supported" s nextPos)
          | some '+' => throw (.unimplemented "Possessive quantifier ?+ is not supported" s nextPos)
          | _ => pure (RegexAST.optional base, afterQuestion)
        else pure (RegexAST.optional base, afterQuestion)
      | _ => pure (base, nextPos)
    else
      pure (base, nextPos)
end

/--
Parse entire regex string into list of AST nodes.
-/
partial def parseAll (s : String) (pos : String.Pos) (acc : List RegexAST) :
    Except ParseError (List RegexAST) :=
  if s.atEnd pos then pure acc.reverse
  else do
    let (ast, nextPos) ← parseRegex s pos
    parseAll s nextPos (ast :: acc)

/--
Parse entire regex string into a single concatenated RegexAST node
-/
def parseTop (s : String) : Except ParseError RegexAST := do
  let asts ← parseAll s 0 []
  match asts with
  | [] => pure (.group .empty)
  | [single] => pure single
  | head :: tail => pure (tail.foldl RegexAST.concat head)

-------------------------------------------------------------------------------

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
info: Except.ok [Strata.Python.RegexAST.union
   (Strata.Python.RegexAST.union (Strata.Python.RegexAST.char '1') (Strata.Python.RegexAST.range '0' '1'))
   (Strata.Python.RegexAST.char '5')]
-/
#guard_msgs in
/-
Cross-checked with:
>>> re._parser.parse('[10-15]')
[(IN, [(LITERAL, 49), (RANGE, (48, 49)), (LITERAL, 53)])]
-/
#eval parseAll "[10-15]" 0 []

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
#eval parseAll ".*{1,10}" 0 []

/-- info: Except.ok [Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)] -/
#guard_msgs in
#eval parseAll ".*" 0 []

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Quantifier '*' at position 0 has nothing to quantify"
  "*abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "*abc" 0 []

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Quantifier '+' at position 0 has nothing to quantify"
  "+abc"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "+abc" 0 []

/-- info: Except.ok [Strata.Python.RegexAST.loop (Strata.Python.RegexAST.range 'a' 'z') 1 10] -/
#guard_msgs in
#eval parseAll "[a-z]{1,10}" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.loop (Strata.Python.RegexAST.range 'a' 'z') 10 10]
-/
#guard_msgs in
#eval parseAll "[a-z]{10}" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.anchor_start,
 Strata.Python.RegexAST.union (Strata.Python.RegexAST.range 'a' 'z') (Strata.Python.RegexAST.range '0' '9'),
 Strata.Python.RegexAST.loop
   (Strata.Python.RegexAST.union
     (Strata.Python.RegexAST.union
       (Strata.Python.RegexAST.union (Strata.Python.RegexAST.range 'a' 'z') (Strata.Python.RegexAST.range '0' '9'))
       (Strata.Python.RegexAST.char '.'))
     (Strata.Python.RegexAST.char '-'))
   1
   10,
 Strata.Python.RegexAST.anchor_end]
-/
#guard_msgs in
#eval parseAll "^[a-z0-9][a-z0-9.-]{1,10}$" 0 []

-- Test escape sequences (need \\ in Lean strings to get single \)
/--
info: Except.ok [Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar),
 Strata.Python.RegexAST.char '.',
 Strata.Python.RegexAST.char '.',
 Strata.Python.RegexAST.anychar,
 Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)]
-/
#guard_msgs in
#eval parseAll ".*\\.\\...*" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.anchor_start,
 Strata.Python.RegexAST.char 'x',
 Strata.Python.RegexAST.char 'n',
 Strata.Python.RegexAST.char '-',
 Strata.Python.RegexAST.char '-',
 Strata.Python.RegexAST.star (Strata.Python.RegexAST.anychar)]
-/
#guard_msgs in
#eval parseAll "^xn--.*" 0 []

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [x-c]: start character 'x' is greater than end character 'c'"
  "[x-c]"
  { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "[x-c]" 0 []

/--
info: Except.error (Strata.Python.ParseError.patternError
  "Invalid character range [1-0]: start character '1' is greater than end character '0'"
  "[51-08]"
  { byteIdx := 2 })
-/
#guard_msgs in
#eval parseAll "[51-08]" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.group
   (Strata.Python.RegexAST.concat
     (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b'))
     (Strata.Python.RegexAST.char 'c'))]
-/
#guard_msgs in
#eval parseAll "(abc)" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.group
   (Strata.Python.RegexAST.union (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b'))]
-/
#guard_msgs in
#eval parseAll "(a|b)" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.star
   (Strata.Python.RegexAST.group
     (Strata.Python.RegexAST.union
       (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'a') (Strata.Python.RegexAST.char 'b'))
       (Strata.Python.RegexAST.concat (Strata.Python.RegexAST.char 'c') (Strata.Python.RegexAST.char 'd'))))]
-/
#guard_msgs in
#eval parseAll "(ab|cd)*" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.char 'a', Strata.Python.RegexAST.optional (Strata.Python.RegexAST.char 'b')]
-/
#guard_msgs in
#eval parseAll "ab?" 0 []

/--
info: Except.ok [Strata.Python.RegexAST.optional (Strata.Python.RegexAST.range 'a' 'z')]
-/
#guard_msgs in
#eval parseAll "[a-z]?" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Positive lookahead (?=...) is not supported"
  "(?=test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "(?=test)" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Negative lookahead (?!...) is not supported"
  "(?!silly-)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "(?!silly-)" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?:abc)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "(?:abc)" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented
  "Extension notation (?...) is not supported"
  "(?P<name>test)"
  { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "(?P<name>test)" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\d is not supported" "\\d+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "\\d+" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\w is not supported" "\\w*" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "\\w*" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Special sequence \\s is not supported" "\\s+" { byteIdx := 0 })
-/
#guard_msgs in
#eval parseAll "\\s+" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Escape sequence \\n is not supported" "test\\n" { byteIdx := 4 })
-/
#guard_msgs in
#eval parseAll "test\\n" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Backreference \\1 is not supported" "(a)\\1" { byteIdx := 3 })
-/
#guard_msgs in
#eval parseAll "(a)\\1" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier *? is not supported" "a*?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a*?" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier +? is not supported" "a+?" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a+?" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Non-greedy quantifier ?? is not supported" "a??" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a??" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier *+ is not supported" "a*+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a*+" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier ++ is not supported" "a++" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a++" 0 []

/--
info: Except.error (Strata.Python.ParseError.unimplemented "Possessive quantifier ?+ is not supported" "a?+" { byteIdx := 1 })
-/
#guard_msgs in
#eval parseAll "a?+" 0 []

end Test.parseTop

-------------------------------------------------------------------------------
end Strata.Python

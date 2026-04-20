/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReToCore
import Strata.Languages.Core.DDMTransform.ASTtoCST

namespace Strata.Python.Tests

open Strata.Python

private def pythonRegexToCoreEraseTypes (r : String) (mode : MatchMode := MatchMode.fullmatch) :=
  let (exp, err) := pythonRegexToCore r mode
  (exp.eraseTypes, err)

/--
info: ((~Re.Concat
  (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b))
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
   (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab.*" -- Encoded as `ab(|.|..*.)`

/--
info: ((~Re.Concat
  (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b))
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) (~Re.Concat (~Str.ToRegEx #c) (~Str.ToRegEx #)))
   (~Re.Concat
    (~Re.Concat (~Re.Concat (~Str.ToRegEx #c) ~Re.None) (~Re.Star (~Re.Concat (~Str.ToRegEx #c) ~Re.None)))
    (~Re.Concat (~Str.ToRegEx #c) (~Str.ToRegEx #))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab(c$)*"

/--
info: ((~Re.Concat
  (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b))
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #c)) (~Str.ToRegEx #)))
   (~Re.Concat
    (~Re.Concat
     (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #c)) ~Re.None)
     (~Re.Star (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #c)) ~Re.None)))
    (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #c)) (~Str.ToRegEx #))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab(^c$)*"

/--
info: ((~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab"

/--
info: ((~Re.Union (~Str.ToRegEx #a) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "a|b"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "^ab"

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #b)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "^ab$"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "(a$)b"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)) (~Str.ToRegEx #a))
   (~Str.ToRegEx #))
  (~Str.ToRegEx #)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^^^a$$"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #)
  (~Re.Concat
   (~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
   (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^(^^a$$)"

/--
info: ((~Re.Union
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #b)) (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^a$)|(^b$)"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #c)
  (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat ~Re.None (~Str.ToRegEx #b)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c((^a)|(^b))"

/--
info: ((~Re.Concat
  (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
  (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b$))c"

/--
info: ((~Re.Concat (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b))c"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #c)
  (~Re.Union
   (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #))
   (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #b)) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c((a$)|(^b$))"

/--
info: ((~Re.Concat (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b))c"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^$b"

/--
info: ((~Re.Union
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #b))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$|^$b"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Str.ToRegEx #c)
   (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None)))
  (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c(^a|b$)d"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Str.ToRegEx #c)
   (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None)))
  (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(c(^a|b$))d"

/--
info: ((~Re.Concat
  (~Re.Union (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
  (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #c)) (~Re.Concat (~Str.ToRegEx #d) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^a|b$)(^c|d$)"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Re.Union (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
   ~Re.None)
  (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((^a|b$)^)c"

/--
info: ((~Re.Concat (~Re.Union (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^|$)c"

/--
info: ((~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^^"

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^$$^"

/--
info: ((~Re.Concat (~Re.Union (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^|$)^"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$" .fullmatch

/--
info: (~Re.All,
 some Pattern error at position 1: Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100 in pattern 'x{100,2}')
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "x{100,2}" .fullmatch

-- (unmatchable)
/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a^b" .fullmatch

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a^b" .fullmatch

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a$b" .fullmatch

/-- info: ((~Re.Inter ~Re.AllChar (~Re.Comp (~Str.ToRegEx #b))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^b]" .fullmatch

/--
info: ((~Re.Inter ~Re.AllChar (~Re.Comp (~Re.Range #A #Z))), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^A-Z]" .fullmatch

/-- info: ((~Re.Inter ~Re.AllChar (~Re.Comp (~Str.ToRegEx #^))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^^]" .fullmatch

/-- info: ((~Str.ToRegEx #a), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .fullmatch

/--
info: ((~Re.Union
  (~Str.ToRegEx #a)
  (~Re.Concat
   (~Str.ToRegEx #a)
   (~Re.Union
    (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
    (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .match

-- search mode tests
/--
info: ((~Re.Union
  (~Str.ToRegEx #a)
  (~Re.Union
   (~Re.Concat
    (~Str.ToRegEx #a)
    (~Re.Union
     (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
     (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar)))
   (~Re.Union
    (~Re.Concat
     (~Re.Union
      (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
      (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
     (~Str.ToRegEx #a))
    (~Re.Concat
     (~Re.Union
      (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
      (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
     (~Re.Concat
      (~Str.ToRegEx #a)
      (~Re.Union
       (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
       (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))))))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .search

/--
info: ((~Re.Union
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
  (~Re.Union
   (~Re.Concat
    (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) ~Re.None)
    (~Re.Union
     (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
     (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar)))
   (~Re.Union
    (~Re.Concat
     (~Re.Union
      (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
      (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
     (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Str.ToRegEx #)))
    (~Re.Concat
     (~Re.Union
      (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
      (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
     (~Re.Concat
      (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #a)) ~Re.None)
      (~Re.Union
       (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
       (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))))))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$" .search

/--
info: ((~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a" .fullmatch

end Strata.Python.Tests

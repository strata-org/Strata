/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.Regex.ReToCore

namespace Strata.Python.Tests

open Strata.Python

/--
info: ((~Re.Concat
  (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b))
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
   (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "ab.*" -- Encoded as `ab(|.|..*.)`

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
#eval Std.format$ pythonRegexToCore "ab(c$)*"

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
#eval Std.format$ pythonRegexToCore "ab(^c$)*"

/--
info: ((~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "ab"

/--
info: ((~Re.Union (~Str.ToRegEx #a) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "a|b"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "^ab"

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #b)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "^ab$"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCore "(a$)b"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)) (~Str.ToRegEx #a))
   (~Str.ToRegEx #))
  (~Str.ToRegEx #)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^^^a$$"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #)
  (~Re.Concat
   (~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
   (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^(^^a$$)"

/--
info: ((~Re.Union
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #b)) (~Str.ToRegEx #))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "(^a$)|(^b$)"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #c)
  (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat ~Re.None (~Str.ToRegEx #b)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "c((^a)|(^b))"

/--
info: ((~Re.Concat
  (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
  (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "((a$)|(b$))c"

/--
info: ((~Re.Concat (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "((a$)|(b))c"

/--
info: ((~Re.Concat
  (~Str.ToRegEx #c)
  (~Re.Union
   (~Re.Concat (~Str.ToRegEx #a) (~Str.ToRegEx #))
   (~Re.Concat (~Re.Concat ~Re.None (~Str.ToRegEx #b)) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "c((a$)|(^b$))"

/--
info: ((~Re.Concat (~Re.Union (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "((a$)|(b))c"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^$b"

/--
info: ((~Re.Union
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
  (~Re.Concat (~Re.Concat (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #b))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^a$|^$b"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Str.ToRegEx #c)
   (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None)))
  (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "c(^a|b$)d"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Str.ToRegEx #c)
   (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None)))
  (~Str.ToRegEx #d)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "(c(^a|b$))d"

/--
info: ((~Re.Concat
  (~Re.Union (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
  (~Re.Union (~Re.Concat ~Re.None (~Str.ToRegEx #c)) (~Re.Concat (~Str.ToRegEx #d) (~Str.ToRegEx #)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "(^a|b$)(^c|d$)"

/--
info: ((~Re.Concat
  (~Re.Concat
   (~Re.Union (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Re.Concat (~Str.ToRegEx #b) ~Re.None))
   ~Re.None)
  (~Str.ToRegEx #c)),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "((^a|b$)^)c"

/--
info: ((~Re.Concat (~Re.Union (~Str.ToRegEx #) ~Re.None) (~Str.ToRegEx #c)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "(^|$)c"

/--
info: ((~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^^"

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^$$^"

/--
info: ((~Re.Concat (~Re.Union (~Str.ToRegEx #) (~Str.ToRegEx #)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "(^|$)^"

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^a$" .fullmatch

/--
info: (~Re.All,
 some Pattern error at position 1: Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100 in pattern 'x{100,2}')
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "x{100,2}" .fullmatch

-- (unmatchable)
/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "a^b" .fullmatch

/--
info: ((~Re.Concat (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^a^b" .fullmatch

/--
info: ((~Re.Concat (~Re.Concat (~Str.ToRegEx #a) ~Re.None) (~Str.ToRegEx #b)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "a$b" .fullmatch

/-- info: ((~Re.Comp (~Str.ToRegEx #b)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "[^b]" .fullmatch

/--
info: ((~Re.Comp (~Re.Range #A #Z)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "[^A-Z]" .fullmatch

/-- info: ((~Re.Comp (~Str.ToRegEx #^)), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "[^^]" .fullmatch

/-- info: ((~Str.ToRegEx #a), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "a" .fullmatch

/--
info: ((~Re.Concat
  (~Str.ToRegEx #a)
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
   (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "a" .match

-- search mode tests
/--
info: ((~Re.Concat
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
   (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
  (~Re.Concat
   (~Str.ToRegEx #a)
   (~Re.Union
    (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
    (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "a" .search

/--
info: ((~Re.Concat
  (~Re.Union
   (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
   (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar))
  (~Re.Concat
   (~Re.Concat (~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)) (~Str.ToRegEx #))
   (~Re.Union
    (~Re.Union (~Str.ToRegEx #) ~Re.AllChar)
    (~Re.Concat (~Re.Concat ~Re.AllChar (~Re.Star ~Re.AllChar)) ~Re.AllChar)))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^a$" .search

/--
info: ((~Re.Concat (~Str.ToRegEx #) (~Str.ToRegEx #a)), none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCore "^a" .fullmatch

end Strata.Python.Tests

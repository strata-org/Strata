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
info: (re.concat(re.concat(str.to.re("a"), str.to.re("b")), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar()))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab.*" -- Encoded as `ab(|.|..*.)`

/--
info: (re.concat(re.concat(str.to.re("a"), str.to.re("b")), re.union(re.union(str.to.re(""), re.concat(str.to.re("c"), str.to.re(""))), re.concat(re.concat(re.concat(str.to.re("c"), re.none()), re.*(re.concat(str.to.re("c"), re.none()))), re.concat(str.to.re("c"), str.to.re(""))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab(c$)*"

/--
info: (re.concat(re.concat(str.to.re("a"), str.to.re("b")), re.union(re.union(str.to.re(""), re.concat(re.concat(re.none(), str.to.re("c")), str.to.re(""))), re.concat(re.concat(re.concat(re.concat(re.none(), str.to.re("c")), re.none()), re.*(re.concat(re.concat(re.none(), str.to.re("c")), re.none()))), re.concat(re.concat(re.none(), str.to.re("c")), str.to.re(""))))),
 none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab(^c$)*"

/-- info: (re.concat(str.to.re("a"), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "ab"

/-- info: (re.union(str.to.re("a"), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "a|b"

/-- info: (re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "^ab"

/--
info: (re.concat(re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("b")), str.to.re("")), none)
-/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "^ab$"

/-- info: (re.concat(re.concat(str.to.re("a"), re.none()), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format$ pythonRegexToCoreEraseTypes "(a$)b"

/--
info: (re.concat(re.concat(re.concat(re.concat(re.concat(str.to.re(""), str.to.re("")), str.to.re("")), str.to.re("a")), str.to.re("")), str.to.re("")),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^^^a$$"

/--
info: (re.concat(str.to.re(""), re.concat(re.concat(re.concat(re.concat(str.to.re(""), str.to.re("")), str.to.re("a")), str.to.re("")), str.to.re(""))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^(^^a$$)"

/--
info: (re.union(re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("")), re.concat(re.concat(str.to.re(""), str.to.re("b")), str.to.re(""))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^a$)|(^b$)"

/-- info: (re.concat(str.to.re("c"), re.union(re.concat(re.none(), str.to.re("a")), re.concat(re.none(), str.to.re("b")))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c((^a)|(^b))"

/-- info: (re.concat(re.union(re.concat(str.to.re("a"), re.none()), re.concat(str.to.re("b"), re.none())), str.to.re("c")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b$))c"

/-- info: (re.concat(re.union(re.concat(str.to.re("a"), re.none()), str.to.re("b")), str.to.re("c")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b))c"

/--
info: (re.concat(str.to.re("c"), re.union(re.concat(str.to.re("a"), str.to.re("")), re.concat(re.concat(re.none(), str.to.re("b")), str.to.re("")))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c((a$)|(^b$))"

/-- info: (re.concat(re.union(re.concat(str.to.re("a"), re.none()), str.to.re("b")), str.to.re("c")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((a$)|(b))c"

/-- info: (re.concat(re.concat(str.to.re(""), re.none()), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^$b"

/--
info: (re.union(re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("")), re.concat(re.concat(str.to.re(""), re.none()), str.to.re("b"))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$|^$b"

/--
info: (re.concat(re.concat(str.to.re("c"), re.union(re.concat(re.none(), str.to.re("a")), re.concat(str.to.re("b"), re.none()))), str.to.re("d")),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "c(^a|b$)d"

/--
info: (re.concat(re.concat(str.to.re("c"), re.union(re.concat(re.none(), str.to.re("a")), re.concat(str.to.re("b"), re.none()))), str.to.re("d")),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(c(^a|b$))d"

/--
info: (re.concat(re.union(re.concat(str.to.re(""), str.to.re("a")), re.concat(str.to.re("b"), re.none())), re.union(re.concat(re.none(), str.to.re("c")), re.concat(str.to.re("d"), str.to.re("")))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^a|b$)(^c|d$)"

/--
info: (re.concat(re.concat(re.union(re.concat(str.to.re(""), str.to.re("a")), re.concat(str.to.re("b"), re.none())), re.none()), str.to.re("c")),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "((^a|b$)^)c"

/-- info: (re.concat(re.union(str.to.re(""), re.none()), str.to.re("c")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^|$)c"

/-- info: (re.concat(str.to.re(""), str.to.re("")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^^"

/-- info: (re.concat(re.concat(re.concat(str.to.re(""), str.to.re("")), str.to.re("")), str.to.re("")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^$$^"

/-- info: (re.concat(re.union(str.to.re(""), str.to.re("")), str.to.re("")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "(^|$)^"

/-- info: (re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$" .fullmatch

/--
info: (re.all(),
 some Pattern error at position 1: Invalid repeat bounds {100,2}: maximum 2 is less than minimum 100 in pattern 'x{100,2}')
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "x{100,2}" .fullmatch

-- (unmatchable)
/-- info: (re.concat(re.concat(str.to.re("a"), re.none()), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a^b" .fullmatch

/-- info: (re.concat(re.concat(re.concat(str.to.re(""), str.to.re("a")), re.none()), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a^b" .fullmatch

/-- info: (re.concat(re.concat(str.to.re("a"), re.none()), str.to.re("b")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a$b" .fullmatch

/-- info: (re.inter(re.allchar(), re.comp(str.to.re("b"))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^b]" .fullmatch

/-- info: (re.inter(re.allchar(), re.comp(re.range("A", "Z"))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^A-Z]" .fullmatch

/-- info: (re.inter(re.allchar(), re.comp(str.to.re("^"))), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "[^^]" .fullmatch

/-- info: (str.to.re("a"), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .fullmatch

/--
info: (re.union(str.to.re("a"), re.concat(str.to.re("a"), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar())))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .match

-- search mode tests
/--
info: (re.union(str.to.re("a"), re.union(re.concat(str.to.re("a"), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar()))), re.union(re.concat(re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar())), str.to.re("a")), re.concat(re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar())), re.concat(str.to.re("a"), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar()))))))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "a" .search

/--
info: (re.union(re.concat(re.concat(str.to.re(""), str.to.re("a")), str.to.re("")), re.union(re.concat(re.concat(re.concat(str.to.re(""), str.to.re("a")), re.none()), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar()))), re.union(re.concat(re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar())), re.concat(re.concat(re.none(), str.to.re("a")), str.to.re(""))), re.concat(re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar())), re.concat(re.concat(re.concat(re.none(), str.to.re("a")), re.none()), re.union(re.union(str.to.re(""), re.allchar()), re.concat(re.concat(re.allchar(), re.*(re.allchar())), re.allchar()))))))),
 none)
-/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a$" .search

/-- info: (re.concat(str.to.re(""), str.to.re("a")), none) -/
#guard_msgs in
#eval Std.format $ pythonRegexToCoreEraseTypes "^a" .fullmatch

end Strata.Python.Tests

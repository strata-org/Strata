/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean
meta import StrataDDM.Util.Format
meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate

meta section

open Core
open Core.Transform
open Strata

def translate (t : StrataDDM.SourcedProgram) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ## Printer parenthesization round-trip

An `if … then … else …` expression parses its `else`-branch greedily (at
precedence 0), so when it is the left operand of a binary operator the printer
must parenthesize it; otherwise `(if c then a else b) == r` would re-parse as
`if c then a else (b == r)` and change meaning. -/

def IteUnderEq :=
#strata
program Core;
procedure main(r : int) {
  assert [a]: (if r == 0 then 1 else 2) == r;
};
#end

-- The printed `assert` keeps the parentheses around the `if` (without them the
-- text would re-parse as `if r == 0 then 1 else (2 == r)`).
/-- info: PARENS-OK -/
#guard_msgs in
#eval
  let printed := toString (translate IteUnderEq)
  IO.println (if (printed.splitOn "(if r == 0 then 1 else 2) == r").length > 1 then "PARENS-OK"
              else s!"MISSING-PARENS: {printed}")

end

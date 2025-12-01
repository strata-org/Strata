/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelParser
import Strata.Languages.Laurel.Translator

namespace Laurel

open Laurel.Parser

def testAssertFalse : IO Unit := do
  let content <- IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

  match parseProgram content with
  | Except.error err =>
    IO.println s!"Parse failed: {err}"
  | Except.ok prog =>
    IO.println "Parse succeeded"
    let results <- verify "cvc5" prog
    IO.println s!"{results}"

#guard_msgs in
#eval! testAssertFalse

end Laurel
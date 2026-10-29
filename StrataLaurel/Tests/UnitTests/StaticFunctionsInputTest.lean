/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Implementation
import StrataLaurel.Implementation.LaurelCompilationPipeline

open Strata

namespace Strata.Laurel

private def helperSource := r"
procedure helper(x: int): int { return x + 1 };
"

private def report (program : LaurelProgram) : IO Unit := do
  let (core, diags) ← translate {} program
  IO.println s!"core produced: {core.isSome}"
  for d in diags do
    IO.println s!"{d.kind}: {d.message}"

/--
info: core produced: false
userError: 'helper' is a static function; an input program may not declare static functions, which the transparency pass introduces
-/
#guard_msgs in
#eval do
  let p ← (Strata.parseLaurelText "<static-functions-input-test>" helperSource : IO LaurelProgram)
  report { p with staticProcedures := [], staticFunctions := p.staticProcedures }

/--
info: core produced: true
-/
#guard_msgs in
#eval do
  let p ← (Strata.parseLaurelText "<static-functions-input-test>" helperSource : IO LaurelProgram)
  report p

end Laurel

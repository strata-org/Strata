/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.SimpleAPI

/-! # Concrete Python Interpreter via Strata

Executes a Python program by translating it through the
Python → Laurel → Core pipeline and then running the Core interpreter.
-/

namespace Strata

/-- Run the Python → Laurel → Core → Interpret pipeline on a Python Ion file. -/
def pyInterpret
    (pythonIonPath : String)
    (dispatchModules : Array String := #[])
    (pyspecModules : Array String := #[])
    (specDir : System.FilePath := ".")
    (fuel : Nat := Core.defaultFuel)
    : EIO String Core.InterpResult := do
  let (core, _diags) ← pyTranslateLaurel pythonIonPath dispatchModules pyspecModules (specDir := specDir)
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core
      (moreFns := Strata.Python.ReFactory) with
    | .ok prog => pure prog
    | .error e => throw s!"Core type checking failed: {e.message}"
  let E ← match Core.initConcreteEnv core fuel with
    | .ok e => pure e
    | .error e => throw s!"init failed: {e.message}"
  return Core.interpProcedure E "__main__"

/-- Run the Python → Core (direct) → Interpret pipeline on a Python Ion file. -/
def pyInterpretDirect
    (pythonIonPath : String)
    (fuel : Nat := Core.defaultFuel)
    : IO Core.InterpResult := do
  let core ← pythonDirectToCore pythonIonPath
  let core ← match Core.typeCheck Core.VerifyOptions.quiet core with
    | .ok prog => pure prog
    | .error e => throw <| .userError s!"Core type checking failed: {e.message}"
  let E ← match Core.initConcreteEnv core fuel with
    | .ok e => pure e
    | .error e => throw <| .userError s!"init failed: {e.message}"
  return Core.interpProcedure E "__main__"

end Strata

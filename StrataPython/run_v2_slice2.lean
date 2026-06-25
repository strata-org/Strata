import StrataPython.PySpecPipeline
open Strata StrataPython

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  match ← pyAnalyzeV2ToCore path with
  | .error msg => IO.println s!"PIPELINE ERROR: {msg}"
  | .ok (some core, errs) =>
    IO.println s!"REACHED CORE — {core.decls.length} Core decls, {errs.length} diagnostics"
  | .ok (none, errs) =>
    IO.println s!"NO CORE — {errs.length} diagnostics"
    let mut i := 0
    for e in errs do
      if i ≥ 10 ∧ i < 25 then IO.println s!"  [{i}] {e.message}"
      i := i + 1

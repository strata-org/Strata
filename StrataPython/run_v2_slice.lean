import StrataPython.PySpecPipeline
open Strata StrataPython

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  IO.println s!"=== pyAnalyzeV2ToCore on {path} ==="
  match ← pyAnalyzeV2ToCore path with
  | .error msg => IO.println s!"PIPELINE ERROR: {msg}"
  | .ok (some core, errs) =>
    IO.println s!"REACHED CORE — {core.decls.length} Core decls, {errs.length} diagnostics"
    for e in errs.take 10 do IO.println s!"  diag: {repr e}"
  | .ok (none, errs) =>
    IO.println s!"NO CORE — {errs.length} diagnostics"
    let mut i := 0
    for e in errs do
      if i < 10 then IO.println s!"  [{i}] {repr e}"
      i := i + 1

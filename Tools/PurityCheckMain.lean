import Lean
import Strata.Util.PurityTracker
open Strata.PurityTracker

def checkPath (path : String) : IO Unit := do
  let contents ← IO.FS.readFile path
  let r ← checkFile contents path
  if r.isEmpty then
    IO.println s!"PURE:   {path}"
  else
    IO.println s!"IMPURE: {path} — {r.toList}"

def main (args : List String) : IO UInt32 := do
  for arg in args do
    checkPath arg
  return 0

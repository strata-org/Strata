import Strata.Languages.Boogie.DDMTransform.Parse

def main : IO Unit := do
  IO.FS.writeBinFile "output.ion" Strata.Boogie.toIon

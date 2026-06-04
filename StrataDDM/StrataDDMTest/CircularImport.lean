/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects

open StrataDDM

namespace Strata.Test.CircularImport

/--
info: 1 error(s) in StrataDDMTest/testdata/CircA.dialect.st:
  2:7: 1 error(s) in StrataDDMTest/testdata/CircB.dialect.st:
  2:7: Circular import detected: CircA -> CircB -> CircA
-/
#guard_msgs in
#eval show IO _ from do
  let preloaded := Elab.LoadedDialects.builtin
  let fm ← DialectFileMap.new preloaded
  let fm ← match ← fm.add "StrataDDMTest/testdata" |>.toBaseIO with
    | .ok fm => pure fm
    | .error msg => do IO.println msg; pure fm
  match ← Elab.loadDialect fm "CircA" with
  | .ok _ => IO.println "unexpected success"
  | .error msg => IO.println msg

/--
info: 1 error(s) in StrataDDMTest/testdata/CircSelf.dialect.st:
  2:7: Dialect CircSelf already open.
-/
#guard_msgs in
#eval show IO _ from do
  let preloaded := Elab.LoadedDialects.builtin
  let fm ← DialectFileMap.new preloaded
  let fm ← match ← fm.add "StrataDDMTest/testdata" |>.toBaseIO with
    | .ok fm => pure fm
    | .error msg => do IO.println msg; pure fm
  match ← Elab.loadDialect fm "CircSelf" with
  | .ok _ => IO.println "unexpected success"
  | .error msg => IO.println msg

/--
info: 1 error(s) in StrataDDMTest/testdata/CircX.dialect.st:
  2:7: 1 error(s) in StrataDDMTest/testdata/CircY.dialect.st:
  2:7: 1 error(s) in StrataDDMTest/testdata/CircZ.dialect.st:
  2:7: Circular import detected: CircX -> CircY -> CircZ -> CircX
-/
#guard_msgs in
#eval show IO _ from do
  let preloaded := Elab.LoadedDialects.builtin
  let fm ← DialectFileMap.new preloaded
  let fm ← match ← fm.add "StrataDDMTest/testdata" |>.toBaseIO with
    | .ok fm => pure fm
    | .error msg => do IO.println msg; pure fm
  match ← Elab.loadDialect fm "CircX" with
  | .ok _ => IO.println "unexpected success"
  | .error msg => IO.println msg

end Strata.Test.CircularImport

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Elab
meta import Strata.DDM.BuiltinDialects

namespace Strata.Test.CircularImport

/--
info: 1 error(s) in StrataTest/DDM/testdata/CircA.dialect.st:
  2:7: 1 error(s) in StrataTest/DDM/testdata/CircB.dialect.st:
  2:7: Circular import detected: CircA -> CircB -> CircA
-/
#guard_msgs in
#eval show IO _ from do
  let preloaded := Elab.LoadedDialects.builtin
  let fm ← DialectFileMap.new preloaded
  let fm ← match ← fm.add "StrataTest/DDM/testdata" |>.toBaseIO with
    | .ok fm => pure fm
    | .error msg => do IO.println msg; pure fm
  match ← Elab.loadDialect fm "CircA" with
  | .ok _ => IO.println "unexpected success"
  | .error msg => IO.println msg

end Strata.Test.CircularImport

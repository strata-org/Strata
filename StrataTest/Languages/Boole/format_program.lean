/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.Verify
import Strata.DDM.Elab

/-!
Regression test for `Boole.formatProgram`.

`Boole.Program` stores type references as fvar indices into a `GlobalContext`.
When a `Boole.Program` is converted back to a `Strata.Program` via `prog.toAst`,
the resulting program wraps everything in a single `Boole.prog` container op.
That container has no binding specs, so its `globalContext` is empty, which causes
fvar indices to be printed as `fvar!N` instead of their real names.

`Boole.formatProgram` fixes this by accepting the `GlobalContext` and `DialectMap`
from the *original* `Strata.Program` and passing them directly into the `FormatContext`.
-/

open Strata

private def vec_program : Strata.Program :=
#strata
program Boole;

datatype Vec (T: Type) { Vec_ctor(Vec_data: Map bv64 T, Vec_len: bv64)};

function Vec_len<T>(v: Vec T): bv64 {
  Vec..Vec_len(v)
}

function Vec_index<T>(v: Vec T, i: bv64): T {
  (Vec..Vec_data(v))[i]
}

procedure main () returns ()
{
};
#end

-- `Boole.formatProgram` must not produce any `fvar!N` tokens: every free variable
-- reference should resolve to its declared name via the provided `GlobalContext`.
#guard
  let prog := (Boole.getProgram vec_program).toOption.get!
  let formatted := (Boole.formatProgram prog vec_program.globalContext vec_program.dialects).pretty
  -- No fvar!N tokens: every free variable reference resolves via the GlobalContext.
  !formatted.contains "fvar!" &&
  -- Declared names appear in the formatted output.
  formatted.contains "Vec" &&
  formatted.contains "Vec..Vec_len" &&
  formatted.contains "Vec..Vec_data"

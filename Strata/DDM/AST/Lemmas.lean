/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST

import all Strata.DDM.AST

public section
namespace Strata.Program

@[simp]
theorem create_dialects (d : DialectMap) (dn : DialectName) (cmds : Array Operation) :
    (create d dn cmds).dialects = d := by dsimp [create]

@[simp]
theorem create_dialect (d : DialectMap) (dn : DialectName) (cmds : Array Operation) :
    (create d dn cmds).dialect = dn := by dsimp [create]

@[simp]
theorem create_commands (d : DialectMap) (dn : DialectName) (cmds : Array Operation) :
    (create d dn cmds).commands = cmds := by dsimp [create]

end Strata.Program
end

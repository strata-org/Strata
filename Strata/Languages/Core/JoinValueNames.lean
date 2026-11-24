/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Names of the symbols the path explorer gives merged values

At a join, the path explorer (`--vcgen symexec`) names each merged value by a fresh symbol and
defines it in the path condition (`SymExec.nameJoinValues`); its output program declares each
by an `init` (`SymExec.newAssumes`). Those symbols' names start with `defaultJoinPrefix`, and their
definitions' labels with `joinValueLabelPrefix`. This module holds only the names.
-/

namespace Core.SymExec

public section

/-- The default prefix of the symbols the path explorer names merged values with at a join,
    extended by underscores until no name the procedure uses starts with it (`choosePrefix`). -/
def defaultJoinPrefix : String := "$__join"

/-- Whether `name` starts with `defaultJoinPrefix`, as every symbol the path explorer names a
    merged value with does. The test is by name alone, so it also holds of a program variable
    with such a name. -/
def isJoinValueName (name : String) : Bool := name.startsWith defaultJoinPrefix

/-- The start of the label of the path-condition entry that defines a join symbol
    (`SymExec.joinValueLabel`). -/
def joinValueLabelPrefix : String := "<join_value: "

/-- Whether `label` is the label of a join symbol's definition (`joinValueLabelPrefix`). -/
def isJoinValueLabel (label : String) : Bool := label.startsWith joinValueLabelPrefix

end -- public section

end Core.SymExec

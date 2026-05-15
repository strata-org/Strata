/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

/-!
# Exit Semantics: Structural Properties of Well-Formedness

Thin wrappers over `Stmt.exitsCoveredByBlocks` that give the structural
consequences of well-formedness descriptive names,
so downstream proofs can cite them directly.

See `docs/design/exit-semantics/spec.md` §4.2.
-/

namespace Imperative

section WellFormedness

variable {P : PureExpr} {CmdT : Type}

/-- Under well-formedness,
    every `exit (some L)` sub-statement has its label
    present in the enclosing label list.

    This follows directly from the definition of
    `Stmt.exitsCoveredByBlocks` —
    the `.exit (some l) _` case reduces to `some l ∈ labels`.

    Realizes spec §4.2. -/
public theorem exit_target_in_labels
    {labels : List (Option String)} {L : String} {md : MetaData P}
    (hwf : @Stmt.exitsCoveredByBlocks P CmdT labels (.exit (.some L) md)) :
    .some L ∈ labels := hwf

/-- Under well-formedness,
    every `exit none` sub-statement has a non-empty enclosing label list.

    Like `exit_target_in_labels`, this follows directly from the
    definition of `Stmt.exitsCoveredByBlocks`. -/
public theorem exit_none_has_enclosing
    {labels : List (Option String)} {md : MetaData P}
    (hwf : @Stmt.exitsCoveredByBlocks P CmdT labels (.exit .none md)) :
    labels.length > 0 := hwf

end WellFormedness

end Imperative

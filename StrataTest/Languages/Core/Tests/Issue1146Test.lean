/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
# Regression: empty `command_datatypes` no longer sneaks through the parser

Before the fix for https://github.com/strata-org/Strata/issues/1146, the
`command_datatypes` op used `NewlineSepBy DatatypeDecl` without `@[nonempty]`,
so the grammar would silently match just the trailing `;\n`. A user writing
a stray `;` after a `function` body (whose grammar has no trailing semicolon)
produced a phantom `command_datatypes` with zero datatypes. That phantom then
tripped an assertion in `translateDatatypes` at `gen_smt_vcs` time with a
large panic backtrace (via `TransM.error`, which calls `panic` internally).

The fix marks `datatypes` as `@[nonempty]`, so the stray `;` surfaces as a
parse error at the source location it actually appears, and a program that
mixes a datatype and a function no longer panics during VC generation.

These tests pin both halves of the contract:

1. The canonical form (datatype + function, no stray `;`) parses and
   `gen_smt_vcs` completes without error.

2. The form from the original issue (trailing `;` after the function body)
   yields a clean parse error rather than a panic.
-/

namespace Strata.Issue1146Test

/-! ## Canonical form succeeds -/

-- A minimal program mixing a datatype and a function, matching the shape of
-- the issue's repro but with the stray `;` removed. This should parse and
-- reach `gen_smt_vcs` without panicking.
private def datatypeAndFunction : Strata.Program :=
#strata
program Core;

datatype List () { Nil() };

function Len (xs : List) : int
{
  0
}
#end

-- No VCs are generated (the function has no assertions), so `gen_smt_vcs`
-- discharges the goal directly. Before the fix this panicked with
-- "Datatype block must contain at least one datatype".
example : Strata.smtVCsCorrect datatypeAndFunction := by
  gen_smt_vcs

/-! ## Stray trailing `;` after a function body is a parse error

If the `@[nonempty]` annotation on `command_datatypes`'s `datatypes` field is
removed, the parser will silently accept the stray `;` as an empty datatype
block, and the panic at `gen_smt_vcs` time returns. Pin the exact parse-error
message here so that regression is caught at elaboration.

Note: the message text enumerates valid continuations at this source
position (`'function'`, `Core.Block`, and — from the `@[nonempty]`
annotation — `expected at least one element`). If a new top-level command
production is added to the Core grammar, the enumeration will change and
this docstring will need to be updated along with it. -/

/--
error: unexpected token ';'; expected 'function', Core.Block or expected at least one element
-/
#guard_msgs in
def strayTrailingSemi : Strata.Program :=
#strata
program Core;

datatype List () { Nil() };

function Len (xs : List) : int
{
  0
};
#end

end Strata.Issue1146Test

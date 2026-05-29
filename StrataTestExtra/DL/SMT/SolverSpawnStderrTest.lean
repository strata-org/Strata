/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DL.SMT.Solver

/-! ## Regression test: Solver.spawn does not SIGPIPE on large stderr output

Issue #1241: When the solver writes a large amount to stderr, the parent must
not leave an unread pipe that fills up and causes SIGPIPE. With `stderr :=
.inherit`, the solver's stderr goes directly to the parent's stderr stream,
so the pipe buffer cannot fill.

This test spawns a bash process that writes ~200 KB to stderr and then acts as
a trivial solver on stdin/stdout. If the old `.piped` stderr were used, the
process would be killed by SIGPIPE before it could respond on stdout.
-/

open Strata.SMT

/--
info: solver responded: sat
-/
#guard_msgs in
#eval do
  -- The script writes 200 KB of diagnostics to stderr, then echoes "sat" for
  -- any input line (simulating a solver that produces verbose diagnostics).
  let solver ← Solver.spawn "/bin/bash" #["-c",
    "yes diag | head -c 200000 >&2; read _line; echo sat"]
  -- Send a command and read the response.
  solver.smtLibInput.putStr "(check-sat)\n"
  solver.smtLibInput.flush
  let response ← match solver.smtLibOutput with
    | some out => out.getLine
    | none => pure ""
  IO.println s!"solver responded: {response.trimAscii}"

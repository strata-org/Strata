/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

namespace Strata.TestUtil

/-- Run `f` in a fresh, empty temporary directory, then remove it, also when `f`
throws.

The directory comes from `IO.FS.withTempDir`: it is unique to this run and has
mode 0700. It is created under the first of `TMPDIR`, `TMP`, `TEMP` and
`TEMPDIR` that is set, or `/tmp` when none is. So no other run can share it,
whether a concurrent build in another workspace or in the same one, a hand run
of the test file, or the editor re-elaborating it, and no other user can
pre-create it. A run that is killed before its cleanup may leave its directory
(a `tmp.XXXX` under that parent) behind.

`IO.FS.withTempDir` crashes the whole process, rather than throwing, when that
parent directory does not exist, so the variable that names it is checked first
and a missing directory fails with an error naming the variable. -/
public def withTestDir [Monad m] [MonadFinally m] [MonadLiftT IO m]
    (f : System.FilePath → m α) : m α := do
  (do
    for var in ["TMPDIR", "TMP", "TEMP", "TEMPDIR"] do
      if let some tmp ← IO.getEnv var then
        unless ← System.FilePath.isDir tmp do
          throw <| IO.userError s!"{var} is set to {tmp}, which is not an \
            existing directory, so no temporary test directory can be created"
        return
    : IO Unit)
  -- `withTempDir` keeps a relative variable's value relative, and tests hand the
  -- path to subprocesses that run with another working directory.
  IO.FS.withTempDir fun dir => do f (← IO.FS.realPath dir)

end Strata.TestUtil

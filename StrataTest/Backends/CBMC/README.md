# CBMC tests

`run_cbmc_tests.sh` runs the CBMC test suites listed in its `SUITES` array and
exits with the number of failed suites. To add a test, add it to one of the
suites or add a suite to the array.

Requirements: `cbmc`, `goto-cc`, `goto-instrument`, `symtab2gb` and `z3` on
`PATH`, and `lake build strataLaurel laurelToCBMC` done. The `cbmc` on `PATH`
must be the version named in `patches/CBMC_VERSION`; on a mismatch the script
fails, or prints `SKIP` and exits 0 when `CBMC_TESTS_SKIP_IF_MISSING=1`.

## How it is run

- **Required-tool CI:** `lake test` runs
  `StrataTestExtra/Backends/CBMC/RunCBMCTests.lean`, which calls the script.
  The required-tool build sets `CBMC_TESTS_REQUIRED=1` and provides the `cbmc`
  named in `patches/CBMC_VERSION`; with that variable set, a missing CBMC tool
  or a `cbmc` of another version fails the build.
- **Plain `lake test`** (`CBMC_TESTS_REQUIRED` unset): if any required tool is
  not on `PATH`, or `cbmc` is not the version in `patches/CBMC_VERSION`, the
  script prints `SKIP` and the test passes. The test runner
  prints a child's output only on failure, so the `SKIP` line does not appear
  in the `lake test` log; run the script directly to see it.
- **GitHub CI configuration:** `patches/CBMC_VERSION` and
  `patches/*.patch` provide the inputs needed to build CBMC from source without
  duplicating the version or patch list in the workflow.

## CBMC version and patches

`patches/` describes the CBMC version and source changes required by the tests:

- `patches/CBMC_VERSION` names the upstream CBMC tag (`cbmc-6.11.0`).
- `patches/*.patch` are the source changes on top of that tag. There are
  currently no patches.

The version file and patch files define the intended source build. Each test
environment is responsible for providing that version and applying that patch
set.

The script checks only that the `cbmc` on `PATH` reports the version in
`CBMC_VERSION`; it cannot detect whether patches were applied. An environment
that runs the script with a different CBMC version fails, or skips with
`CBMC_TESTS_SKIP_IF_MISSING=1`, before the suites run.

A patched build reports the same version number as an unpatched build. Solver
versions, operating systems and compilers may also differ between environments;
the suites compare verdicts, not solver output.

To change the CBMC version or add a patch, update `patches/` together with the
Strata change that needs it. Each patch must apply with `git apply` to the tag
named in `CBMC_VERSION`. Every environment that runs the suites as required
tests must move to the new version in the same change, since the version check
fails them otherwise; environments that run them as optional tests skip until
they are updated.

## Skipped checks

Known gaps on CBMC 6.11.0 that no suite covers:

- Quantified assertions: CBMC 6.11.0 reports `FAILURE` for a true quantified
  assertion such as `assert forall(x: int) => x + 1 > x`. A false quantified
  assertion also reports `FAILURE`, so the gap is spurious failures, not
  spurious successes. No suite asserts a quantified property.
- Bounds checks on integer-indexed arrays: no suite exercises array indexing,
  so CBMC 6.11.0's behaviour there is untested.
- `test_strings.lr.st` has no expectations in
  `StrataLaurel/Tests/CBMC/tests/cbmc_expected.txt`, so the runner skips it.
  CBMC 6.11 does not know the string operation names Strata emits
  (`Str.Concat`, ...). Requires Strata to emit CBMC's `cprover_string_*` names
  and CBMC to include https://github.com/diffblue/cbmc/pull/9138.
- `contracts/test_contracts_e2e.sh` runs its `goto-instrument --dfcc` and
  `cbmc` checks only with `CBMC_CONTRACTS_RUN_DFCC=1`; by default it checks
  GOTO structure, not verification verdicts. `laurelAnalyzeToGoto` emits GOTO
  bodies for the generated `$pre`/`$post` functions while typing their symbols
  `mathematical_function`; `cbmc` and `goto-instrument --dfcc` abort on them
  with `to_code_type` during function-pointer removal. The fix belongs in
  `Strata/Backends/CBMC/GOTO/CoreToGOTOPipeline.lean`.

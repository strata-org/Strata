# CBMC tests

`run_cbmc_tests.sh` runs the CBMC test suites listed in its `SUITES` array and
exits with the number of failed suites. To add a test, add it to one of the
suites or add a suite to the array.

Requirements: `cbmc`, `goto-cc`, `goto-instrument`, `symtab2gb` and `z3` on
`PATH`, and `lake build strataLaurel laurelToCBMC` done.

## How it is run

- **Brazil build:** `lake test` runs
  `StrataTestExtra/Backends/CBMC/RunCBMCTests.lean`, which calls the script.
  CBMC is the `CBMC = 6.x_strata` build tool in `Config`.
  `build-tools/bin/strata-build` exits with an error if `cbmc` is not on `PATH`
  and sets `CBMC_TESTS_REQUIRED=1`, so a missing CBMC tool fails the build.
- **Plain `lake test`** (`CBMC_TESTS_REQUIRED` unset): if any required tool is
  not on `PATH`, the script prints `SKIP` and the test passes. The test runner
  prints a child's output only on failure, so the `SKIP` line does not appear
  in the `lake test` log; run the script directly to see it.
- **GitHub CI:** `.github/workflows/cbmc.yml` (GitHub repository only)
  installs CBMC 6.11.0, builds Strata and calls the script:

  ```yaml
  - uses: actions/checkout@v6
  - uses: ./.github/actions/install-cvc5
  - uses: ./.github/actions/install-z3
  - name: Install CBMC
    shell: bash
    run: |
      set -eu
      wget -q https://github.com/diffblue/cbmc/releases/download/cbmc-6.11.0/ubuntu-24.04-cbmc-6.11.0-Linux.deb
      sudo dpkg -i ubuntu-24.04-cbmc-6.11.0-Linux.deb
  - uses: leanprover/lean-action@v1
    with:
      auto-config: false
      build: true
      use-github-cache: false
  - run: StrataTest/Backends/CBMC/run_cbmc_tests.sh
  ```

## Skipped checks

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

# Promote 32 Passing Pending Tests to Main Suite

## Date: 2026-04-14

## What was done
Moved 32 `.py` test files (and their `.python.st.ion` companions) from
`StrataTest/Languages/Python/tests/pending/` to `tests/`, then generated
expected Laurel output.

## Key decisions
- Some ion files were already in `tests/` (pre-generated during earlier work),
  while others were only in `pending/`. The move script correctly handled both
  cases by using `[ -f ... ] && mv`.

## Pitfalls encountered
- `run_py_analyze.sh --update` only processes tests that already have an
  `expected_laurel/<name>.expected` file. For the 18 tests whose ion files
  came from `pending/`, no expected file existed yet. Fix: `touch` empty
  expected files first, then re-run `--update`.
- The script discovers tests via `tests/test_*.py` glob but gates on
  `[ -f "$expected_file" ]` before running analysis. This is by design
  (pending tests use a separate `--pending` flag), but means newly promoted
  tests need their expected file bootstrapped.

## Verification
- All 189 tests (including the 32 promoted) pass with exit code 0.
- No ERROR output in the test run.

## For next agent
- If promoting more pending tests, remember to create empty `.expected`
  files before running `--update`, or the script silently skips them.
- Total test count went from ~157 to 189 after this promotion.

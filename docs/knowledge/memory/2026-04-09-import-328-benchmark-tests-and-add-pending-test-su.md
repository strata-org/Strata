# Import 328 Benchmark Tests and Add Pending Test Support

## What was done
- Copied 326 test `.py` and `.ion` files from 3 benchmark subdirectories into `StrataTest/Languages/Python/tests/`
- Skipped 2 files (`test_if_elif.py`, `test_list_slice.py`) that already existed
- Generated 106 new `.expected` files for tests that pass with 0 failed, 0 inconclusive
- Updated `run_py_analyze.sh` with `--pending` flag

## Key decisions
- Used actual analysis results (110 OK in benchmarks) rather than the stated 117
- 2 of the 110 "OK" tests (`test_crash_while_true_break`, `test_flag_pattern`) now show inconclusive results on current Strata — left as pending
- Copied `.ion` files alongside `.py` files to avoid re-parsing overhead

## Counts
- Total test files: 382 (56 original + 326 new)
- Expected files: 156 (50 original + 106 new)
- Pending tests: 227 (77 error, 150 imprecise)

## Pitfalls
- The benchmark `analysis_output` was generated with a different Strata build; 2 tests regressed to inconclusive
- The `--pending` flag uses `timeout 20` to avoid hanging on slow tests
- Pending error detection checks exit code AND output for error keywords

## Test runner behavior
- `bash run_py_analyze.sh laurel` — runs only tests with `.expected` files (unchanged behavior)
- `bash run_py_analyze.sh laurel --pending` — also runs pending tests, reports summary, exit 0

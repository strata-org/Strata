# Move Pending Tests to tests/pending/ Subdirectory

## What was done
- Created `StrataTest/Languages/Python/tests/pending/` directory
- Moved 227 test files (`.py` + `.python.st.ion`) without matching `.expected` files into `tests/pending/`
- Updated `run_py_analyze.sh`: removed inline pending logic from main loop, added separate loop scanning `tests/pending/`

## Key decisions
- The main loop now only processes `tests/test_*.py` (all of which have expected files)
- The `--pending` flag triggers a separate loop over `tests/pending/test_*.py`
- Ion files for pending tests are generated into `tests/pending/` (same dir as the `.py` files)

## File counts after change
- `tests/`: 155 `test_*.py` files (all have `.expected` files)
- `tests/pending/`: 229 `test_*.py` files
- `expected_laurel/`: 156 `.expected` files (155 main + 1 `.user_errors.expected`)
- Total: 384 test files

## Pitfalls
- One expected file (`test_user_error_metadata.user_errors.expected`) is a secondary expected file, not a primary one — don't count it as a "missing test"
- The `--filter` flag works for both main and pending tests

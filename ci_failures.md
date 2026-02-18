# CI Failures to Fix

## Status Check
Last checked: 2026-02-18T14:59:26

## Current CI Status
All checks appear to be passing according to `gh pr checks`.

## Action Items
1. Merge latest main (which has DDM printer changes)
2. Re-run tests locally or trigger new CI
3. Collect actual failures
4. Fix files one by one

## Notes
- Main now uses DDM printer instead of original printer
- Need to adapt test expectations accordingly


## TODO
- [ ] Core CST should support parsing variable declarations without RHS
- [ ] Add example test in StrataTest for parsing declarations without RHS

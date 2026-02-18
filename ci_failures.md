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


## Current Failures (2026-02-18T16:10:00)
Files needing test expectation updates to remove 'some':
1. StrataTest/Languages/Core/CmdEvalTests.lean (lines 58, 102)
2. StrataTest/Languages/Core/StatementEvalTests.lean (line 352)
3. StrataTest/Languages/Core/StatementTypeTests.lean (lines 26, 129, 196)
4. StrataTest/Languages/C_Simp/Examples/SimpleTest.lean (line 76)
5. StrataTest/DL/Imperative/FormatStmtTest.lean (line 32)
6. StrataTest/DL/Imperative/ArithType.lean (lines 134, 166, 201)
7. StrataTest/DL/Imperative/ArithEval.lean (lines 196, 224)

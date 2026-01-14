# Remaining PR Review Comments - Action Plan

## Integrate B3 Verification into StrataVerify

**Reviewer:** shigoel  
**Comments:**
1. "Wondering if you can put this in StrataVerify.lean instead of StrataMain.lean (which I think of as being specific to Python work right now, even though it's not explicitly stated as such)."
2. "Consider reusing StrataVerify, which ought to be the entrypoint of such cmd line tools."

**Current State:**
- `verifyB3Command` exists in `StrataMain.lean` (alongside Python commands)
- `StrataVerifyB3.lean` is a separate standalone executable
- `StrataVerify.lean` handles Boogie and C_Simp verification

**Goal:**
Make B3 a first-class verification target in StrataVerify, just like Boogie and C_Simp.

**Implementation Plan:**

1. **Add B3 support to StrataVerify.lean:**
   - ✅ Add import: `import Strata.Languages.B3.Verifier.Program`
   - ✅ Add B3CST dialect to loaded dialects
   - ✅ Update usage message to include `.b3.st` files
   - Add B3 verification logic in the main verification flow
   - Detect `.b3.st` or `.b3cst.st` files and route to B3 verification

2. **Remove verifyB3Command from StrataMain.lean:**
   - Delete the `verifyB3Command` definition
   - Remove it from `commandList`
   - Keep StrataMain focused on Python-specific utilities

3. **Delete StrataVerifyB3.lean:**
   - Remove the standalone executable file
   - Update lakefile.toml to remove the StrataVerifyB3 executable entry

4. **Test:**
   - Verify that `lake exe StrataVerify Examples/file.b3.st` works
   - Ensure Boogie and C_Simp verification still work
   - Check that the build completes successfully

**User Experience After Changes:**
```bash
# Unified verification interface
lake exe StrataVerify Examples/SimpleProc.boogie.st
lake exe StrataVerify Examples/LoopSimple.csimp.st  
lake exe StrataVerify Examples/SomeFile.b3.st       # New!
```

**Status:**
- ✅ Imports added
- ✅ Dialect added
- ✅ Usage message updated
- ⏳ Need to add B3 verification logic
- ⏳ Need to remove verifyB3Command from StrataMain
- ⏳ Need to delete StrataVerifyB3.lean
- ⏳ Need to update lakefile.toml

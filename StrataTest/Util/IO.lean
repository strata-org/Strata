/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Util.IO

-- Test that readInputSource can read from a regular file
def testReadFile : IO Unit := do
  IO.FS.withTempFile fun _handle tempPath => do
    -- Write test content to the temporary file
    IO.FS.writeFile tempPath "Hello from file"
    
    -- Read it back using our utility
    let content ← Strata.Util.readInputSource tempPath.toString
    
    -- Verify content
    if content != "Hello from file" then
      throw (IO.Error.userError "File read failed")

/--
info: File read test passed
-/
#guard_msgs in
#eval do
  testReadFile
  IO.println "File read test passed"

-- Test that readBinInputSource can read from a regular file
def testReadBinFile : IO Unit := do
  IO.FS.withTempFile fun _handle tempPath => do
    -- Write test content to the temporary file
    let testData := "Binary test data".toUTF8
    IO.FS.writeBinFile tempPath testData
    
    -- Read it back using our utility
    let content ← Strata.Util.readBinInputSource tempPath.toString
    
    -- Verify content
    if content != testData then
      throw (IO.Error.userError "Binary file read failed")

/--
info: Binary file read test passed
-/
#guard_msgs in
#eval do
  testReadBinFile
  IO.println "Binary file read test passed"

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Util.IO

-- Test that readInputSource can read from a regular file
def testReadFile : IO Unit := do
  -- Create a temporary test file
  let testPath := "test_io_temp.txt"
  IO.FS.writeFile testPath "Hello from file"
  
  -- Read it back using our utility
  let content ← Strata.Util.readInputSource testPath
  
  -- Clean up
  IO.FS.removeFile testPath
  
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
  -- Create a temporary test file
  let testPath := "test_io_bin_temp.txt"
  let testData := "Binary test data".toUTF8
  IO.FS.writeBinFile testPath testData
  
  -- Read it back using our utility
  let content ← Strata.Util.readBinInputSource testPath
  
  -- Clean up
  IO.FS.removeFile testPath
  
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

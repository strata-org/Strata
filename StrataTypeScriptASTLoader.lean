/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.TypeScript.js_ast

-- Simple AST loader that tests if TypeScript AST JSON can be loaded into Lean structures
-- Returns success/failure without translation or execution

def test_load_typescript_ast (filename : String) : IO Bool := do
  try
    -- Try to load AST from JSON file into TS_File structure
    IO.println s!"Loading AST from: {filename}"

    -- First, let's see what the JSON looks like
    let contents ← IO.FS.readFile filename
    IO.println s!"JSON content preview (first 200 chars): {contents.take 200}..."

    -- Try to parse as generic JSON first
    let json ← match Lean.Json.parse contents with
      | Except.ok json => do
        IO.println s!"JSON parsed successfully"
        pure json
      | Except.error err => do
        IO.println s!"JSON parsing failed: {err}"
        throw (IO.userError s!"Failed to parse JSON: {err}")

    -- Now try to convert to TS_File
    let result : Except String TS_File := Lean.FromJson.fromJson? json
    match result with
      | Except.ok file => do
        IO.println s!"SUCCESS: Converted to TS_File with {file.program.body.size} statements"
        return true
      | Except.error err => do
        IO.println s!"TS_File conversion failed: {err}"
        return false

  catch e =>
    -- Any exception means loading failed
    IO.println s!"FAILED: {e}"
    return false

def main (args : List String) : IO Unit := do
  match args with
  | [filename] => do
    let success ← test_load_typescript_ast filename
    if success then
      IO.println "AST_LOAD_SUCCESS"
      -- Exit with success code
    else
      IO.println "AST_LOAD_FAILED"
      -- Exit with failure code
      IO.Process.exit 1
  | _ =>
    IO.println "Usage: StrataTypeScriptASTLoader filename.json"
    IO.println "Tests if TypeScript AST JSON can be loaded into Lean structures"
    IO.Process.exit 1

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Data.Json.Basic
import Lean.Data.Json.Printer

public section

/-! Streaming JSON writer that avoids stack overflow on large values. -/

/-- Write a `Lean.Json` value to a file handle without building an intermediate string. -/
partial def writeJsonTo (h : IO.FS.Handle) : Lean.Json → IO Unit
  | .null => h.putStr "null"
  | .bool b => h.putStr (if b then "true" else "false")
  | .num n => h.putStr (toString n)
  | .str s => h.putStr (Lean.Json.renderString s)
  | .arr elems => do
    h.putStr "["
    for i in [:elems.size] do
      if i > 0 then h.putStr ","
      writeJsonTo h elems[i]!
    h.putStr "]"
  | .obj kvs => do
    h.putStr "{"
    let _ ← kvs.foldlM (init := true) fun first k v => do
      if !first then h.putStr ","
      h.putStr (Lean.Json.renderString k)
      h.putStr ":"
      writeJsonTo h v
      pure false
    h.putStr "}"

/-- Write a `Lean.Json` value to a file, ensuring the handle is flushed even on exception. -/
def writeJsonFile (path : String) (json : Lean.Json) : IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  try
    writeJsonTo h json
  finally
    h.flush

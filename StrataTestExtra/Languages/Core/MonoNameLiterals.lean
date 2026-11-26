/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## The names of monomorphization's copies are built and read in one module

A copy's name is `P#<escaped base>#<types>`, with the prefix `P` monomorphization chooses
(`Core.NameMangling.choosePrefix`). Only `Strata/Languages/Core/NameMangling.lean` may spell
the prefix or take a copy's name apart: every other module goes through its functions
(`mangleFuncName`, `copyName`, `demangleFuncName`, `demangledBaseName`), and a module that
decides what a function means reads the copy mark (`FuncAttr.monoCopyOf`), not the name.
This test reads the sources and fails on a string literal containing `$__mono` outside that
module, in code (comments and docstrings may name the prefix). -/

namespace Strata.MonoNameLiterals

/-- The `.lean` files under `dir`, recursively. -/
partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then out := out ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then out := out.push e.path
  return out

/-- The lines of `text` that are code, each with the part of it outside comments: `/- … -/`
    comments and docstrings (nested) and `--` comments are dropped, and string literals are
    kept. One pass over the characters, so a comment marker inside a string literal or a
    character literal, or a quote inside a comment, does not change what is code. -/
def codeLines (text : String) : List (Nat × String) := Id.run do
  let cs := text.toList.toArray
  let mut out : List (Nat × String) := []
  let mut line : List Char := []
  let mut lineNo := 1
  let mut depth := 0
  let mut inStr := false
  let mut esc := false
  let mut lineComment := false
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if c == '\n' then
      let l := String.ofList line.reverse
      if !l.trimAscii.isEmpty then out := (lineNo, l) :: out
      line := []; lineNo := lineNo + 1; lineComment := false; esc := false
      i := i + 1
    else if lineComment then i := i + 1
    else if depth > 0 then
      if c == '/' && next == some '-' then depth := depth + 1; i := i + 2
      else if c == '-' && next == some '/' then depth := depth - 1; i := i + 2
      else i := i + 1
    else if inStr then
      line := c :: line
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
      i := i + 1
    else if c == '/' && next == some '-' then depth := 1; i := i + 2
    else if c == '-' && next == some '-' then lineComment := true; i := i + 2
    else if c == '\'' && next == some '"' && cs[i + 2]? == some '\'' then
      -- The character literal `'"'`.
      line := '\'' :: '"' :: '\'' :: line; i := i + 3
    else if c == '\'' && next == some '\\' && cs[i + 3]? == some '\'' then
      -- An escaped character literal such as `'\"'`.
      line := cs[i + 3]! :: cs[i + 2]! :: '\\' :: '\'' :: line; i := i + 4
    else
      if c == '"' then inStr := true
      line := c :: line
      i := i + 1
  let l := String.ofList line.reverse
  if !l.trimAscii.isEmpty then out := (lineNo, l) :: out
  return out.reverse

/-- The code lines of the sources under `roots` that hold `$__mono` in a string literal,
    outside `NameMangling.lean`. Fails if a root does not exist or if no `NameMangling.lean`
    was found, so a scan of the wrong directory cannot pass by finding nothing. -/
def offenders (roots : List System.FilePath) : IO (List String) := do
  let mut out := []
  let mut sawNameMangling := false
  for root in roots do
    if !(← root.pathExists) then
      throw (IO.userError s!"MonoNameLiterals: source root {root} not found")
    for f in ← leanFiles root do
      if f.fileName == some "NameMangling.lean" then
        sawNameMangling := true
        continue
      let text ← IO.FS.readFile f
      for (n, line) in codeLines text do
        -- Comments are dropped, and no Lean identifier starts with `$`, so `$__mono` in code is
        -- in a string literal, possibly one that started on an earlier line.
        if (line.splitOn "$__mono").length > 1 then
          out := s!"{f}:{n}: {line.trimAscii}" :: out
  unless sawNameMangling do
    throw (IO.userError "MonoNameLiterals: NameMangling.lean not found under the source roots")
  return out.reverse

-- A literal ending in an escaped backslash closes, so the `--` after it starts a comment.
#guard codeLines "x := \"a\\\\\" -- c" == [(1, "x := \"a\\\\\" ")]
#guard codeLines "x := \"a\\\" -- b\" -- c" == [(1, "x := \"a\\\" -- b\" ")]
-- Code before a comment a line opens, or after one it closes, is scanned; the comment is not.
#guard codeLines "def x := 1 /- note -/" == [(1, "def x := 1 ")]
#guard codeLines "/- a\n b -/ def y := 2\ndef z := 3" == [(2, " def y := 2"), (3, "def z := 3")]
#guard codeLines "/-- doc -/\ndef w := 4 -- note" == [(2, "def w := 4 ")]
-- A comment marker inside a string or character literal is not a comment.
#guard codeLines "let s := \"x /- y\"\nlet t := 1" == [(1, "let s := \"x /- y\""), (2, "let t := 1")]
#guard codeLines "if c == '\"' then \"$m\" else 0" == [(1, "if c == '\"' then \"$m\" else 0")]

-- A string literal that spans lines keeps its later lines as code.
#guard codeLines "def s := \"a\n  $__mono#f\"" == [(1, "def s := \"a"), (2, "  $__mono#f\"")]

/-- info: offenders: [] -/
#guard_msgs in
#eval show IO Unit from do
  let o ← offenders ["Strata", "StrataLaurel", "StrataCortex"]
  IO.println s!"offenders: {o}"

end Strata.MonoNameLiterals

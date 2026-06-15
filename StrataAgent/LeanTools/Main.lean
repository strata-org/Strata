/-
  SwarmAgentTools — Base64-RPC for Lean file analysis

  A long-lived process that reads commands from stdin (base64-encoded payloads)
  and writes single-line JSON responses to stdout. Avoids Lean startup cost
  (~3-5s) on repeated calls by staying alive between commands.

  Inspired by the itp-interface project:
    https://github.com/trishullab/itp-interface
  (see TacticParser/Main.lean for the original stdin/stdout loop pattern)

  We chose Base64-RPC over JSON-RPC because:
  - JSON-RPC is bulky and has encoding issues with special characters in Lean
    source code (backslashes, unicode, string interpolation with braces)
  - The Lean REPL tool (which uses JSON) frequently hits escaping bugs where
    Lean syntax characters get mangled in transit
  - Base64 encoding is lossless for arbitrary byte content — no escaping needed
  - The protocol is trivial: one line in, one line out, command prefix for routing

  Protocol:
    Input:  "<command_pad><base64_content>" (one line, command left-padded to 15 chars)
    Output: single-line JSON
    "exit" or empty line terminates.

  Commands:
    count_sorries  <base64(file_path)>  → {"total":N,"sorry_decls":["name",...]}
    list_theorems  <base64(file_path)>  → {"theorems":[{"name":"X","status":"sorry|proved"},...]}
    check_imports  <base64(file_path)>  → {"imports":["Mod.Name",...]}
    check_compiles <base64(file_path)>  → {"success":bool,"has_sorry":bool,"has_error":bool}

  Build:  lake build SwarmAgentTools
  Run:    .lake/build/bin/SwarmAgentTools
-/
import StrataAgent.LeanTools.Base64

open IO

namespace StrataAgent.LeanTools

-- ─── Command names and parsing ──────────────────────────────────────────────
-- All command names are exactly 15 characters. No padding needed.

def commandNames : List String := [
  "count__sorries_",
  "list__theorems_",
  "check__imports_",
  "check__compile_",
  "split_theorems_",
  "check___axioms_",
  "thm_signature__",
  "thm_depends_on_",
  "sorry_positions"
]

def commandMaxPad : Nat := 15

structure Request where
  command : String
  content : String
  deriving Inhabited

def parseRequest (line : String) : Option Request :=
  let trimmed := line.trimAscii.toString
  if trimmed.length < commandMaxPad then none
  else
    let cmd := (trimmed.take commandMaxPad).toString
    let payload := (trimmed.drop commandMaxPad).toString
    -- Decode base64 payload
    match Base64.decode payload with
    | .ok decoded => some { command := cmd, content := decoded }
    | .error _ => some { command := cmd, content := payload }

-- ─── Comment stripping (from itp-interface LineParser) ──────────────────────

/-- Strip comments from text. Returns the byte offset where non-comment content starts.
    Handles nested block comments /- ... -/ and line comments --. -/
partial def trimComment (text : String) (state : Nat := 0) (depth : Nat := 0) : Nat :=
  if text.startsWith "--" && state == 0 then
    let endOfLine := text.find (fun c => c == '\n')
    let remaining := (text.drop endOfLine.offset.byteIdx).toString
    endOfLine.offset.byteIdx + trimComment remaining 0 depth
  else if text.startsWith "/-" && state == 0 then
    let remaining := (text.drop 2).toString
    (trimComment remaining 1 (depth + 1)) + 2
  else if text.startsWith "-/" && state == 1 then
    let newDepth := depth - 1
    let newState := if newDepth == 0 then 0 else 1
    let remaining := (text.drop 2).toString
    (trimComment remaining newState newDepth) + 2
  else if text.isEmpty then
    0
  else if state == 1 then
    let remaining := (text.drop 1).toString
    (trimComment remaining state depth) + 1
  else
    0

/-- Remove all comments from content, returning only code. -/
private def stripComments (content : String) : String := Id.run do
  let mut result : String := ""
  let mut remaining := content
  while !remaining.isEmpty do
    let skip := trimComment remaining
    if skip > 0 then
      remaining := (remaining.drop skip).toString
    else
      -- Take one line of code
      let nextNewline := remaining.find (fun c => c == '\n')
      let lineEnd := nextNewline.offset.byteIdx + 1
      result := result ++ (remaining.take lineEnd).toString
      remaining := (remaining.drop lineEnd).toString
  result

-- ─── String helpers ─────────────────────────────────────────────────────────

private def strContains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

-- ─── File analysis ──────────────────────────────────────────────────────────

private def countSorries (content : String) : (Nat × Array String) := Id.run do
  let lines := content.splitOn "\n"
  let mut total : Nat := 0
  let mut currentThm : String := ""
  let mut thmHasSorry : Bool := false
  let mut sorryDecls : Array String := #[]

  for line in lines do
    let trimmed := line.trimAsciiStart.toString
    if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " then
      if currentThm != "" && thmHasSorry then
        sorryDecls := sorryDecls.push currentThm
      let parts := trimmed.splitOn " "
      let idx := if trimmed.startsWith "private" then 2 else 1
      currentThm := if h : idx < parts.length then
        let raw := parts[idx]
        (raw.takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
      else ""
      thmHasSorry := false

    if !(trimmed.startsWith "--") then
      let beforeComment := (trimmed.splitOn "--")[0]!
      let sorryCount := (beforeComment.splitOn "sorry").length - 1
      if sorryCount > 0 then
        total := total + sorryCount
        thmHasSorry := true

  if currentThm != "" && thmHasSorry then
    sorryDecls := sorryDecls.push currentThm

  (total, sorryDecls)

private def listTheorems (content : String) : Array (String × String) := Id.run do
  let lines := content.splitOn "\n"
  let mut results : Array (String × String) := #[]
  let mut currentThm : String := ""
  let mut currentBlock : String := ""

  for line in lines do
    let trimmed := line.trimAsciiStart.toString
    if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " then
      if currentThm != "" then
        let status := if strContains currentBlock "sorry" then "sorry" else "proved"
        results := results.push (currentThm, status)
      let parts := trimmed.splitOn " "
      let idx := if trimmed.startsWith "private" then 2 else 1
      currentThm := if h : idx < parts.length then
        ((parts[idx]).takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
      else ""
      currentBlock := ""
    else if currentThm != "" then
      currentBlock := currentBlock ++ line ++ "\n"

  if currentThm != "" then
    let status := if strContains currentBlock "sorry" then "sorry" else "proved"
    results := results.push (currentThm, status)

  results

private def extractImports (content : String) : Array String := Id.run do
  let lines := content.splitOn "\n"
  let mut imports : Array String := #[]
  for line in lines do
    let trimmed := line.trimAsciiStart.toString
    if trimmed.startsWith "import " then
      imports := imports.push (trimmed.drop 7).trimAsciiStart.toString
  imports

-- ─── Command handlers ────────────────────────────────────────────────────────

private def handleCountSorries (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    let (total, sorryDecls) := countSorries content
    let declsJson := String.intercalate "," (sorryDecls.toList.map (fun s => s!"\"{jsonEscape s}\""))
    return s!"\{\"total\":{total},\"sorry_decls\":[{declsJson}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleListTheorems (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    let thms := listTheorems content
    let items := String.intercalate "," (thms.toList.map fun (n, s) =>
      s!"\{\"name\":\"{jsonEscape n}\",\"status\":\"{s}\"}")
    return s!"\{\"theorems\":[{items}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleCheckImports (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    let imports := extractImports content
    let items := String.intercalate "," (imports.toList.map (fun s => s!"\"{jsonEscape s}\""))
    return s!"\{\"imports\":[{items}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleSplitTheorems (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    let lines := content.splitOn "\n"
    let mut blocks : Array (String × Nat × Nat × Bool) := #[]  -- (name, startLine, endLine, hasSorry)
    let mut currentThm : String := ""
    let mut currentStart : Nat := 0
    let mut currentBlock : String := ""

    for i in [:lines.length] do
      let line := lines[i]!
      let trimmed := line.trimAsciiStart.toString
      if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " then
        -- Save previous theorem
        if currentThm != "" then
          let hasSorry := strContains currentBlock "sorry"
          blocks := blocks.push (currentThm, currentStart, i - 1, hasSorry)
        -- Start new theorem
        let parts := trimmed.splitOn " "
        let idx := if trimmed.startsWith "private" then 2 else 1
        currentThm := if h : idx < parts.length then
          ((parts[idx]).takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
        else ""
        currentStart := i
        currentBlock := line ++ "\n"
      else if currentThm != "" then
        currentBlock := currentBlock ++ line ++ "\n"

    -- Save last theorem
    if currentThm != "" then
      let hasSorry := strContains currentBlock "sorry"
      blocks := blocks.push (currentThm, currentStart, lines.length - 1, hasSorry)

    let items := String.intercalate "," (blocks.toList.map fun (n, s, e, hs) =>
      s!"\{\"name\":\"{jsonEscape n}\",\"start\":{s},\"end\":{e},\"has_sorry\":{hs}}")
    return s!"\{\"blocks\":[{items}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleThmSignature (input : String) : IO String := do
  -- Input format: "file_path:theorem_name"
  try
    let parts := input.splitOn ":"
    if parts.length < 2 then
      return "{\"error\":\"expected file_path:theorem_name\"}"
    let filePath := parts[0]!
    let thmName := (String.intercalate ":" (parts.drop 1)).trimAsciiStart.toString
    let content ← FS.readFile ⟨filePath⟩
    let code := stripComments content
    let lines := code.splitOn "\n"
    -- Find the theorem declaration line
    let mut found := false
    let mut sigLines : Array String := #[]
    let mut collecting := false
    for line in lines do
      let trimmed := line.trimAsciiStart.toString
      if !collecting then
        -- Look for "theorem <name>" or "private theorem <name>"
        if (trimmed.startsWith s!"theorem {thmName}") ||
           (trimmed.startsWith s!"private theorem {thmName}") then
          collecting := true
          sigLines := sigLines.push line
      else
        -- Collect until we hit ":= by" or ":= " (proof body start)
        if strContains line ":= by" || strContains line ":= " then
          -- Include up to but not including the proof body
          let beforeProof := (line.splitOn ":=")[0]!
          if !beforeProof.trimAsciiStart.toString.isEmpty then
            sigLines := sigLines.push beforeProof
          found := true
          break
        else if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " ||
                trimmed.startsWith "def " || trimmed.startsWith "axiom " then
          -- Hit another declaration before finding := , signature was on one line
          found := true
          break
        else
          sigLines := sigLines.push line
    if !found && !sigLines.isEmpty then
      found := true
    if !found then
      return s!"\{\"error\":\"theorem '{jsonEscape thmName}' not found\"}"
    let sig := String.intercalate "\n" sigLines.toList
    return s!"\{\"name\":\"{jsonEscape thmName}\",\"signature\":\"{jsonEscape sig}\"}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleThmDependsOn (input : String) : IO String := do
  -- Input format: "file_path:theorem_name"
  -- Returns which other theorems in the same file are referenced in the proof body
  try
    let parts := input.splitOn ":"
    if parts.length < 2 then
      return "{\"error\":\"expected file_path:theorem_name\"}"
    let filePath := parts[0]!
    let thmName := (String.intercalate ":" (parts.drop 1)).trimAsciiStart.toString
    let content ← FS.readFile ⟨filePath⟩
    let code := stripComments content
    let lines := code.splitOn "\n"

    -- First pass: collect all theorem/def names in the file
    let mut allNames : Array String := #[]
    for line in lines do
      let trimmed := line.trimAsciiStart.toString
      if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " ||
         trimmed.startsWith "def " || trimmed.startsWith "private def " then
        let parts := trimmed.splitOn " "
        let idx := if trimmed.startsWith "private" then 2 else 1
        if h : idx < parts.length then
          let name := ((parts[idx]).takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
          if !name.isEmpty then
            allNames := allNames.push name

    -- Second pass: find the target theorem's proof body
    let mut inBody := false
    let mut bodyLines : Array String := #[]
    let mut foundStart := false
    for line in lines do
      let trimmed := line.trimAsciiStart.toString
      if !foundStart then
        if (trimmed.startsWith s!"theorem {thmName}") ||
           (trimmed.startsWith s!"private theorem {thmName}") then
          foundStart := true
          -- Check if := is on the same line
          if strContains line ":= by" || strContains line ":= " then
            let afterProof := (line.splitOn ":=")
            if h : 1 < afterProof.length then
              bodyLines := bodyLines.push afterProof[1]
            inBody := true
      else if !inBody then
        -- Still in signature, look for :=
        if strContains line ":= by" || strContains line ":= " then
          let afterProof := (line.splitOn ":=")
          if h : 1 < afterProof.length then
            bodyLines := bodyLines.push afterProof[1]
          inBody := true
      else
        -- In body — stop at next top-level declaration
        if trimmed.startsWith "theorem " || trimmed.startsWith "private theorem " ||
           trimmed.startsWith "def " || trimmed.startsWith "axiom " then
          break
        bodyLines := bodyLines.push line

    -- Check which names from the file appear in the proof body
    let body := String.intercalate "\n" bodyLines.toList
    let mut uses : Array String := #[]
    for name in allNames do
      if name != thmName && strContains body name then
        uses := uses.push name

    let usesJson := String.intercalate "," (uses.toList.map (fun s => s!"\"{jsonEscape s}\""))
    return s!"\{\"theorem\":\"{jsonEscape thmName}\",\"uses\":[{usesJson}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleSorryPositions (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    let code := stripComments content
    let lines := code.splitOn "\n"
    let mut positions : Array (Nat × Nat) := #[]
    for i in [:lines.length] do
      let line := lines[i]!
      -- Find all "sorry" occurrences in this line
      let mut searchFrom : Nat := 0
      let mut searching := true
      while searching do
        let remaining := (line.drop searchFrom).toString
        let idx := remaining.splitOn "sorry"
        if idx.length > 1 then
          -- Found one at position searchFrom + length_of_first_part
          let col := searchFrom + (idx[0]!).length
          positions := positions.push (i, col)
          searchFrom := col + 5  -- skip past "sorry"
        else
          searching := false
    let items := String.intercalate "," (positions.toList.map fun (l, c) =>
      s!"\{\"line\":{l},\"col\":{c}}")
    return s!"\{\"positions\":[{items}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleCheckAxioms (filePath : String) : IO String := do
  try
    let content ← FS.readFile ⟨filePath⟩
    -- Strip all comments first — definitive, not fooled by axiom in comments
    let code := stripComments content
    let lines := code.splitOn "\n"
    let mut axiomNames : Array String := #[]
    for line in lines do
      let trimmed := line.trimAsciiStart.toString
      -- Direct: "axiom name ..."
      if trimmed.startsWith "axiom " then
        let parts := (trimmed.drop 6).trimAsciiStart.toString.splitOn " "
        if h : 0 < parts.length then
          let name := ((parts[0]).takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
          if !name.isEmpty then
            axiomNames := axiomNames.push name
      -- With modifier: "private axiom ...", "protected axiom ...", etc
      else if trimmed.startsWith "private axiom " || trimmed.startsWith "protected axiom " ||
              trimmed.startsWith "noncomputable axiom " then
        let afterAxiom := ((trimmed.splitOn " axiom ")[1]!).trimAsciiStart.toString
        let parts := afterAxiom.splitOn " "
        if h : 0 < parts.length then
          let name := ((parts[0]).takeWhile (fun c => c != ':' && c != '(' && c != '{')).toString
          if !name.isEmpty then
            axiomNames := axiomNames.push name
    let hasAxiom := !axiomNames.isEmpty
    let namesJson := String.intercalate "," (axiomNames.toList.map (fun s => s!"\"{jsonEscape s}\""))
    return s!"\{\"has_axiom\":{hasAxiom},\"axiom_names\":[{namesJson}]}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

private def handleCheckCompiles (filePath : String) : IO String := do
  try
    let child ← Process.spawn {
      cmd := "lake"
      args := #["env", "lean", filePath]
      stdout := .piped
      stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let hasSorry := strContains stderr "sorry"
    let hasError := (stderr.splitOn "\n").any fun line =>
      strContains line ": error:" && !(strContains line "sorry")
    let success := exitCode == 0 || !hasError
    return s!"\{\"success\":{success},\"has_sorry\":{hasSorry},\"has_error\":{hasError}}"
  catch e =>
    return s!"\{\"error\":\"{jsonEscape (toString e)}\"}"

end StrataAgent.LeanTools

-- ─── Main (must be at top level for the linker) ─────────────────────────────

open StrataAgent.LeanTools in
unsafe def main (_args : List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "{\"status\":\"ready\"}"
  stdout.flush

  let mut running := true
  while running do
    let line ← stdin.getLine
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty || trimmed == "exit" then
      running := false
    else
      match parseRequest trimmed with
      | none =>
        stdout.putStrLn "{\"error\":\"parse_failed\"}"
        stdout.flush
      | some req =>
        let result ← match req.command with
          | "count__sorries_" => handleCountSorries req.content
          | "list__theorems_" => handleListTheorems req.content
          | "check__imports_" => handleCheckImports req.content
          | "check__compile_" => handleCheckCompiles req.content
          | "split_theorems_" => handleSplitTheorems req.content
          | "check___axioms_" => handleCheckAxioms req.content
          | "thm_signature__" => handleThmSignature req.content
          | "thm_depends_on_" => handleThmDependsOn req.content
          | "sorry_positions" => handleSorryPositions req.content
          | cmd => pure s!"\{\"error\":\"unknown command: {jsonEscape cmd}\"}"
        stdout.putStrLn result
        stdout.flush

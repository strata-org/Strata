/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Laurel.Grammar

/-!
# Auto-generate editor syntax highlighting from Strata DDM grammars

Usage:
  lake env lean --run editors/GenSyntax.lean vscode      # TextMate grammars (VSCode)
  lake env lean --run editors/GenSyntax.lean emacs       # Emacs major modes
  lake env lean --run editors/GenSyntax.lean vim         # Vim/Neovim regex syntax + ftdetect
  lake env lean --run editors/GenSyntax.lean treesitter  # tree-sitter grammar.js + highlight queries
  lake env lean --run editors/GenSyntax.lean all         # everything

Each backend is generated for every dialect in `targets` (currently Core and
Laurel).  Two extraction strategies feed the backends:

* `extractSyntaxInfo`  — Core: types come from `type` decls, keywords/operators
  from `fn` decls.  Static patterns (comments, strings, …) are hardcoded.
* `extractLaurelInfo`  — Laurel: the grammar declares *everything* as `op`s in
  syntax categories, so tokens are harvested from op literals by shape
  (category `LaurelType` → types; alphabetic runs → keywords; operator-character
  runs → symbol operators).

The `vscode`/`emacs`/`vim` backends are lexical (regex token classification via
`SyntaxInfo`).  The `treesitter` backend is structural: it walks the `SyntaxDef`
data of every op/fn to emit a real grammar with operator precedence/associativity.
-/

open Strata CoreDDM StrataDDM StrataDDM.Elab

/-! ## Extract syntax tokens from a Dialect object -/

partial def extractAtomStrs : SyntaxDefAtom → List String
  | .str s => [s]
  | .indent _ atoms => atoms.toList.flatMap extractAtomStrs
  | .ident _ _ => []

def extractStrLiterals : SyntaxDef → List String
  | .std atoms _ => atoms.toList.flatMap extractAtomStrs
  | .passthrough => []

def strip (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c != ' ' && c != '\n'))

structure SyntaxInfo where
  types : List String
  keywords : List String
  wordOperators : List String  -- div, mod, sdiv, smod
  constants : List String      -- true, false
  builtinFunctions : List String
  symbolOperators : List String

def extractSyntaxInfo (d : Dialect) : SyntaxInfo :=
  let types := d.declarations.filterMap fun
    | Decl.type td => some td.name
    | _ => none
  let rawOpKeywords := d.declarations.flatMap fun
    | Decl.op od => (extractStrLiterals od.syntaxDef).filter
        (fun s => (strip s).length > 0 && (strip s).all Char.isAlpha) |>.map strip |>.toArray
    | _ => #[]
  let fnEntries := d.declarations.filterMap fun
    | Decl.function fd => some (fd.name, extractStrLiterals fd.syntaxDef |>.map strip |>.filter (·.length > 0))
    | _ => none
  -- Function names with explicit classification (handled by dedicated branches below)
  let constantFnNames := ["btrue", "bfalse"]
  let keywordFnNames := ["forall", "forallT", "exists", "existsT", "old"]
  -- Auto-detect literal constructors by naming convention (*Lit suffix)
  let isLiteralCtor (name : String) : Bool := name.endsWith "Lit"
  -- Internal functions: not user-visible operators or keywords
  let internalFns := ["natToInt",  -- literal conversion function
                      "if"]        -- control keyword from ops, not a function-level operator
  -- Combined skip predicate for both classification folds
  let shouldSkip (name : String) : Bool :=
    constantFnNames.contains name || keywordFnNames.contains name ||
    isLiteralCtor name || internalFns.contains name
  let init : List String × List String × List String × List String :=
    ([], [], [], [])
  let classified := fnEntries.foldl (init := init)
    fun acc entry =>
      let (constants, fnKeywords, wordOps, builtins) := acc
      let name := entry.1
      let strs := entry.2
      -- Constants: functions that produce boolean literal tokens
      if constantFnNames.contains name then
        (constants ++ strs.filter (·.all Char.isAlpha), fnKeywords, wordOps, builtins)
      -- Keywords: quantifiers, old, etc.
      else if keywordFnNames.contains name then
        (constants, fnKeywords ++ strs.filter (·.all Char.isAlpha), wordOps, builtins)
      -- Skip literal constructors and internal functions
      else if isLiteralCtor name || internalFns.contains name then
        (constants, fnKeywords, wordOps, builtins)
      -- Word operators: single alpha token (div, mod, sdiv, smod)
      else if strs.length == 1 && strs.head!.all Char.isAlpha then
        (constants, fnKeywords, wordOps ++ [strs.head!], builtins)
      -- Builtin functions: dotted names or function-call syntax
      else if strs.length > 0 then
        let firstStr := strs.head!
        -- Strip trailing paren from names like "Int.DivT("
        let cleanName := if firstStr.endsWith "(" then String.ofList (firstStr.toList.dropLast) else firstStr
        if cleanName.contains '.' then
          (constants, fnKeywords, wordOps, builtins ++ [cleanName])
        else
          (constants, fnKeywords, wordOps, builtins)
      else
        (constants, fnKeywords, wordOps, builtins)
  let (constants, fnKeywords, wordOps, builtins) := classified
  -- Collect symbol operators from functions
  let symbolOps := fnEntries.foldl (init := ([] : List String)) fun acc entry =>
    let strs := entry.2
    let name := entry.1
    if shouldSkip name then acc
    else if strs.length == 1 && strs.head!.all Char.isAlpha then acc  -- word ops
    else if strs.length > 0 then
      let firstStr := strs.head!
      if firstStr.contains '.' then acc  -- builtins
      else if firstStr.startsWith "bv" then acc  -- bv-specific instances covered by generic pattern
      else if !firstStr.all Char.isAlpha && firstStr.length > 0
              && firstStr != "(" && firstStr != ")" && firstStr != ","
              && firstStr != "[" && firstStr != "]" then
        acc ++ [firstStr]
      else acc
    else acc
  -- DDM-level keywords not in the dialect grammar
  let dmmKeywords := ["program"]
  let allKeywords := (rawOpKeywords.toList ++ fnKeywords ++ dmmKeywords).eraseDups
  let typeSet := types.toList
  let constSet := constants
  let keywords := allKeywords.filter (fun k => !typeSet.contains k && !constSet.contains k && !wordOps.contains k)
  { types := types.toList
    keywords := keywords
    wordOperators := wordOps.eraseDups
    constants := (constants ++ ["null"]).eraseDups
    builtinFunctions := builtins.eraseDups
    symbolOperators := symbolOps.eraseDups }

/-! ## Op-aware extraction (Laurel)

Laurel declares no `type`/`fn` decls — everything is an `op` in a syntax
category.  We harvest tokens from op literals by shape:

* maximal alphabetic runs  → keywords (e.g. `procedure`, `requires`, `while`)
* maximal operator-char runs → symbol operators (e.g. `==>`, `&&`, `:=`)
* literals of category `LaurelType` → types (`int`, `bool`, `bv`, …)
-/

private def opCharStr : String := "+-*/%<>=!&|~^#:"

/-- Maximal identifier runs in `s`: a leading letter/`_` followed by
    letters/digits/`_` (so `float64` and `bv` stay whole, but `=>` splits off). -/
def alphaRuns (s : String) : List String :=
  let isStart (c : Char) : Bool := c.isAlpha || c == '_'
  let isCont (c : Char) : Bool := c.isAlpha || c.isDigit || c == '_'
  let step : (List String × List Char) → Char → (List String × List Char) :=
    fun (acc, cur) c =>
      if (cur.isEmpty && isStart c) || (!cur.isEmpty && isCont c) then (acc, cur ++ [c])
      else if cur.isEmpty then (acc, []) else (acc ++ [String.ofList cur], [])
  let (acc, cur) := s.toList.foldl (init := ([], [])) step
  if cur.isEmpty then acc else acc ++ [String.ofList cur]

/-- Maximal runs of operator characters in `s`. -/
def symbolRuns (s : String) : List String :=
  let isOp (c : Char) : Bool := opCharStr.toList.contains c
  let step : (List String × List Char) → Char → (List String × List Char) :=
    fun (acc, cur) c =>
      if isOp c then (acc, cur ++ [c])
      else if cur.isEmpty then (acc, []) else (acc ++ [String.ofList cur], [])
  let (acc, cur) := s.toList.foldl (init := ([], [])) step
  if cur.isEmpty then acc else acc ++ [String.ofList cur]

def extractLaurelInfo (d : Dialect) : SyntaxInfo :=
  let ops := d.declarations.filterMap fun
    | Decl.op od => some od
    | _ => none
  let litsOf (od : OpDecl) : List String := extractStrLiterals od.syntaxDef
  let isTypeOp (od : OpDecl) : Bool := od.category.name == "LaurelType"
  -- Types: alphabetic runs from LaurelType-category ops (int, bool, bv, Core, Map, …)
  let typeToks := ops.toList.flatMap fun od =>
    if isTypeOp od then (litsOf od).flatMap alphaRuns else []
  let types := typeToks.eraseDups
  -- Keywords: alphabetic runs (length >= 2) from non-type ops
  let kwToks := ops.toList.flatMap fun od =>
    if isTypeOp od then [] else (litsOf od).flatMap alphaRuns
  -- Operators: operator-char runs from all ops
  let opToks := ops.toList.flatMap fun od => (litsOf od).flatMap symbolRuns
  let constants := ["true", "false"]
  let keywords := (kwToks.eraseDups).filter
    (fun k => k.length ≥ 2 && !types.contains k && !constants.contains k)
  let symbolOperators := (opToks.eraseDups).filter
    (fun o => o.length > 0 && o != ":")
  { types := types
    keywords := keywords
    wordOperators := []
    constants := constants
    builtinFunctions := []
    symbolOperators := symbolOperators }

/-! ## Per-dialect generation target -/

structure GenTarget where
  /-- Scope/name suffix, e.g. `core-st` (used in TextMate scopes, file basenames). -/
  scope : String
  /-- Human-readable name, e.g. `Strata Core`. -/
  display : String
  /-- Double file extension this dialect uses, e.g. `core.st`. -/
  ext : String
  /-- The dialect object (used by the structural tree-sitter backend). -/
  dialect : Dialect
  /-- Lexically extracted token classification. -/
  info : SyntaxInfo

/-! ## TextMate JSON generator (VSCode) -/

private def escapeJsonStr (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

def escapeRegexForJson (s : String) : String :=
  let special := "\\^$.|?*+()[]{}".toList
  String.ofList <| s.toList.flatMap fun c =>
    if special.contains c then ['\\', '\\', c] else [c]

def generateTextMate (t : GenTarget) : String :=
  let info := t.info
  let sc := t.scope
  let typePattern := "\\\\b(" ++ "|".intercalate (info.types.map escapeRegexForJson) ++ ")\\\\b"
  let kwPattern := "\\\\b(" ++ "|".intercalate (info.keywords.map escapeRegexForJson) ++ ")\\\\b"
  let constPattern := "\\\\b(" ++ "|".intercalate (info.constants.map escapeRegexForJson) ++ ")\\\\b"
  let wordOpPattern := "\\\\b(" ++ "|".intercalate (info.wordOperators.map escapeRegexForJson) ++ ")\\\\b"
  let sortedSymOps := info.symbolOperators.toArray.qsort (fun a b => a.length > b.length) |>.toList
  let symOpPattern := "(" ++ "|".intercalate (sortedSymOps.map escapeRegexForJson) ++ ")"
  let builtinPattern := "\\\\b(" ++ "|".intercalate (info.builtinFunctions.map escapeRegexForJson) ++
    "|bvconcat\\\\{[0-9]+\\\\}\\\\{[0-9]+\\\\}|bvextract\\\\{[0-9]+\\\\}\\\\{[0-9]+\\\\}\\\\{[0-9]+\\\\})\\\\b"
  -- Use ` to avoid Lean string interpolation issues with { }
  let q := "\""
  let ob := "{"  -- open brace
  let cb := "}"  -- close brace
  let lines : List String := [
    ob,
    s!"  {q}$schema{q}: {q}https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json{q},",
    s!"  {q}_comment{q}: {q}AUTO-GENERATED from the {t.display} DDM grammar. Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vscode{q},",
    s!"  {q}name{q}: {q}{t.display}{q},",
    s!"  {q}scopeName{q}: {q}source.{sc}{q},",
    s!"  {q}patterns{q}: [",
    s!"    {ob} {q}include{q}: {q}#comment{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#string{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#attribute{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#label{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#number{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#keyword{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#type{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#constant{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#operator{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#function-call{q} {cb},",
    s!"    {ob} {q}include{q}: {q}#identifier{q} {cb}",
    "  ],",
    s!"  {q}repository{q}: {ob}",
    s!"    {q}comment{q}: {ob}",
    s!"      {q}name{q}: {q}comment.line.double-slash.{sc}{q},",
    s!"      {q}match{q}: {q}//.*${q}",
    s!"    {cb},",
    s!"    {q}string{q}: {ob}",
    s!"      {q}name{q}: {q}string.quoted.double.{sc}{q},",
    s!"      {q}begin{q}: {q}\\{q}{q},",
    s!"      {q}end{q}: {q}\\{q}{q},",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.character.escape.{sc}{q},",
    s!"          {q}match{q}: {q}\\\\\\\\.{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}attribute{q}: {ob}",
    s!"      {q}name{q}: {q}meta.attribute.{sc}{q},",
    s!"      {q}match{q}: {q}@\\\\[[^\\\\]]*\\\\]{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.other.attribute-name.{sc}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}label{q}: {ob}",
    s!"      {q}name{q}: {q}meta.label.{sc}{q},",
    s!"      {q}match{q}: {q}\\\\[([a-zA-Z_][a-zA-Z0-9_]*)\\\\]\\\\s*:{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.name.label.{sc}{q} {cb},",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}entity.name.tag.{sc}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}number{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.numeric.decimal.{sc}{q},",
    s!"          {q}match{q}: {q}\\\\b[0-9]+(\\\\.[0-9]+)?\\\\b{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}keyword{q}: {ob}",
    s!"      {q}name{q}: {q}keyword.{sc}{q},",
    s!"      {q}match{q}: {q}{kwPattern}{q}",
    s!"    {cb},",
    s!"    {q}type{q}: {ob}",
    s!"      {q}name{q}: {q}support.type.{sc}{q},",
    s!"      {q}match{q}: {q}{typePattern}{q}",
    s!"    {cb},",
    s!"    {q}constant{q}: {ob}",
    s!"      {q}name{q}: {q}constant.language.{sc}{q},",
    s!"      {q}match{q}: {q}{constPattern}{q}",
    s!"    {cb},",
    s!"    {q}operator{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.assignment.{sc}{q},",
    s!"          {q}match{q}: {q}:={q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.word.{sc}{q},",
    s!"          {q}match{q}: {q}{wordOpPattern}{q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.symbol.{sc}{q},",
    s!"          {q}match{q}: {q}{symOpPattern}{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}function-call{q}: {ob}",
    s!"      {q}match{q}: {q}{builtinPattern}{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}support.function.builtin.{sc}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}identifier{q}: {ob}",
    s!"      {q}name{q}: {q}variable.other.{sc}{q},",
    s!"      {q}match{q}: {q}\\\\b[a-zA-Z_$][a-zA-Z0-9_$]*\\\\b{q}",
    s!"    {cb}",
    s!"  {cb}",
    cb
  ]
  "\n".intercalate lines

/-! ## Emacs elisp generator -/

private def emacsQuote (s : String) : String := s!"\"" ++ escapeJsonStr s ++ s!"\""

private def emacsWordList (items : List String) (indent : String := "    ") : String :=
  let quoted := items.map emacsQuote
  let init : List String × String := ([], indent)
  let result := quoted.foldl (init := init) fun acc q =>
    let cur := acc.2
    let next := if cur == indent then cur ++ q else cur ++ " " ++ q
    if next.length > 72 then (acc.1 ++ [cur], indent ++ q) else (acc.1, next)
  let allLines := result.1 ++ [result.2]
  "\n".intercalate allLines

/-- Build the Emacs auto-mode regexp string for a double extension like
    `core.st`, e.g. `\\.core\\.st\\'` (matches files ending in `.core.st`). -/
private def emacsExtRegex (ext : String) : String :=
  -- Each component is preceded by an escaped dot; the regexp is anchored with \'.
  let parts := ext.splitOn "."
  (parts.map (fun p => "\\\\." ++ p)).foldl (· ++ ·) "" ++ "\\\\'"

def generateEmacs (t : GenTarget) : String :=
  let info := t.info
  let p := t.scope            -- defvar/mode prefix, e.g. "core-st"
  let kwList := emacsWordList info.keywords
  let tyList := emacsWordList info.types
  let ctList := emacsWordList info.constants
  let opList := emacsWordList info.wordOperators
  let biList := emacsWordList info.builtinFunctions
  let extRe := emacsExtRegex t.ext
  -- Build the file as a list of lines to avoid escape nightmares
  let lines : List String := [
    s!";;; {p}-mode.el --- Major mode for {t.display} (.{t.ext}) files -*- lexical-binding: t; -*-",
    "",
    s!";; AUTO-GENERATED from the {t.display} DDM grammar.",
    ";; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs",
    "",
    ";; Keywords",
    s!"(defvar {p}-keywords",
    s!"  '({kwList}))",
    "",
    s!"(defvar {p}-types",
    s!"  '({tyList}))",
    "",
    s!"(defvar {p}-constants",
    s!"  '({ctList}))",
    "",
    s!"(defvar {p}-operators",
    s!"  '({opList}))",
    "",
    s!"(defvar {p}-builtins",
    s!"  '({biList}))",
    "",
    ";; Font-lock rules",
    s!"(defvar {p}-font-lock-keywords",
    s!"  (let ((kw-re  (regexp-opt {p}-keywords  'symbols))",
    s!"        (ty-re  (regexp-opt {p}-types     'symbols))",
    s!"        (ct-re  (regexp-opt {p}-constants 'symbols))",
    s!"        (op-re  (regexp-opt {p}-operators 'symbols))",
    s!"        (bi-re  (regexp-opt {p}-builtins  'symbols)))",
    "    `((,kw-re . font-lock-keyword-face)",
    "      (,ty-re . font-lock-type-face)",
    "      (,ct-re . font-lock-constant-face)",
    "      (,op-re . font-lock-keyword-face)",
    "      (,bi-re . font-lock-builtin-face)",
    "      ;; Attributes: @[...]",
    "      (\"@\\\\[[^]]*\\\\]\" . font-lock-preprocessor-face)",
    "      ;; Labels: [name]:",
    "      (\"\\\\[\\\\([a-zA-Z_][a-zA-Z0-9_]*\\\\)\\\\]\\\\s-*:\" 1 font-lock-function-name-face)",
    "      ;; Numeric literals",
    "      (\"\\\\b[0-9]+\\\\(?:\\\\.[0-9]+\\\\)?\\\\b\" . font-lock-constant-face))))",
    "",
    ";; Syntax table",
    s!"(defvar {p}-mode-syntax-table",
    "  (let ((st (make-syntax-table)))",
    "    ;; // line comments",
    "    (modify-syntax-entry ?/ \". 12\" st)",
    "    (modify-syntax-entry ?\\n \">\" st)",
    "    ;; String literals",
    "    (modify-syntax-entry ?\\\" \"\\\"\" st)",
    "    ;; Backslash escapes in strings",
    "    (modify-syntax-entry ?\\\\ \"\\\\\" st)",
    "    ;; Brackets",
    "    (modify-syntax-entry ?\\( \"()\" st)",
    "    (modify-syntax-entry ?\\) \")(\" st)",
    "    (modify-syntax-entry ?\\{ \"(}\" st)",
    "    (modify-syntax-entry ?\\} \"){\" st)",
    "    (modify-syntax-entry ?\\[ \"(]\" st)",
    "    (modify-syntax-entry ?\\] \")[\" st)",
    "    ;; Dot and underscore are symbol constituents",
    "    (modify-syntax-entry ?. \"_\" st)",
    "    (modify-syntax-entry ?_ \"_\" st)",
    "    st))",
    "",
    ";;;###autoload",
    s!"(define-derived-mode {p}-mode prog-mode \"{t.display}\"",
    s!"  \"Major mode for editing {t.display} (.{t.ext}) files.\"",
    s!"  :syntax-table {p}-mode-syntax-table",
    s!"  (setq-local font-lock-defaults '({p}-font-lock-keywords))",
    "  (setq-local comment-start \"// \")",
    "  (setq-local comment-end \"\"))",
    "",
    ";;;###autoload",
    s!"(add-to-list 'auto-mode-alist '(\"{extRe}\" . {p}-mode))",
    "",
    s!"(provide '{p}-mode)",
    s!";;; {p}-mode.el ends here",
    ""
  ]
  "\n".intercalate lines

/-! ## Vim/Neovim regex syntax generator -/

/-- Escape a literal for use inside a Vim `syntax match "..."` (magic) pattern.
    `*`, `.`, `[`, `]`, `^`, `~`, `\` are special in magic mode and must be escaped;
    other operator characters (`+ = < > ! % # & | : ?`) are literal. -/
private def vimEscape (s : String) : String :=
  let special := "*.[]^~\\".toList
  String.ofList <| s.toList.flatMap fun c =>
    if special.contains c then ['\\', c] else [c]

/-- Emit `syntax keyword <group> ...` lines, chunked to keep lines short. -/
private def vimKeywordLines (group : String) (items : List String) : List String :=
  let rec go (acc : List String) (cur : List String) (rest : List String) : List String :=
    match rest with
    | [] => if cur.isEmpty then acc else acc ++ [s!"syntax keyword {group} " ++ " ".intercalate cur]
    | x :: xs =>
      if cur.length ≥ 8 then
        go (acc ++ [s!"syntax keyword {group} " ++ " ".intercalate cur]) [x] xs
      else go acc (cur ++ [x]) xs
  go [] [] items

def generateVim (t : GenTarget) : String :=
  let info := t.info
  let grp := t.scope.replace "-" ""   -- highlight-group prefix, e.g. "corest"
  -- Operator match: assignment + dialect symbol operators, longest-first.
  let allOps := (":=" :: info.symbolOperators).eraseDups
  let sortedOps := allOps.toArray.qsort (fun a b => a.length > b.length) |>.toList
  let opAlt := "\\|".intercalate (sortedOps.map vimEscape)
  let biEscaped := info.builtinFunctions.map vimEscape
  let biAlt := "\\|".intercalate biEscaped
  let header : List String := [
    s!"\" {t.display} syntax highlighting for Vim/Neovim (filetype: {grp}).",
    s!"\" AUTO-GENERATED from the {t.display} DDM grammar.",
    "\" Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vim",
    "",
    "if exists(\"b:current_syntax\") | finish | endif",
    ""
  ]
  let kwLines := vimKeywordLines s!"{grp}Keyword" info.keywords
  let tyLines := vimKeywordLines s!"{grp}Type" info.types
  let ctLines := vimKeywordLines s!"{grp}Constant" info.constants
  let woLines := if info.wordOperators.isEmpty then []
                 else vimKeywordLines s!"{grp}WordOp" info.wordOperators
  let opLine := if sortedOps.isEmpty then []
                else [s!"syntax match {grp}Operator \"{opAlt}\""]
  let biLine := if info.builtinFunctions.isEmpty then []
                else [s!"syntax match {grp}Builtin \"{biAlt}\""]
  let staticLines : List String := [
    "",
    s!"syntax match {grp}Comment \"//.*$\"",
    s!"syntax region {grp}String start=+\"+ skip=+\\\\\"+ end=+\"+",
    s!"syntax match {grp}Number \"\\<[0-9]\\+\\(\\.[0-9]\\+\\)\\?\\>\"",
    s!"syntax match {grp}Attribute \"@\\[[^]]*\\]\"",
    s!"syntax match {grp}Label \"\\[[a-zA-Z_][a-zA-Z0-9_]*\\]\\s*:\"",
    ""
  ]
  let links : List String := [
    s!"highlight default link {grp}Keyword Keyword",
    s!"highlight default link {grp}Type Type",
    s!"highlight default link {grp}Constant Constant",
    s!"highlight default link {grp}Operator Operator",
    s!"highlight default link {grp}WordOp Operator",
    s!"highlight default link {grp}Builtin Function",
    s!"highlight default link {grp}Comment Comment",
    s!"highlight default link {grp}String String",
    s!"highlight default link {grp}Number Number",
    s!"highlight default link {grp}Attribute PreProc",
    s!"highlight default link {grp}Label Label",
    "",
    s!"let b:current_syntax = \"{grp}\""
  ]
  "\n".intercalate (header ++ kwLines ++ tyLines ++ ctLines ++ woLines ++ opLine ++ biLine ++ staticLines ++ links)

def generateVimFtdetect (t : GenTarget) : String :=
  let grp := t.scope.replace "-" ""
  -- match files ending in the dialect's double extension
  let pat := "*." ++ t.ext
  "\n".intercalate [
    s!"\" AUTO-GENERATED: filetype detection for {t.display} (.{t.ext}) files.",
    s!"autocmd BufRead,BufNewFile {pat} set filetype={grp}",
    ""
  ]

/-! ## tree-sitter grammar generator (structural)

Walks the resolved `SyntaxDef` of every op/fn to emit a tree-sitter `grammar.js`
plus highlight queries.  Operator precedence/associativity is recovered from the
resolved operand precedences baked into each `SyntaxDef`.
-/

/-- Convert a PascalCase / camelCase name to snake_case for tree-sitter rule names. -/
def toSnake (s : String) : String :=
  let out := s.toList.foldl (init := ([] : List Char)) fun acc c =>
    if c.isUpper then
      (if acc.isEmpty then [] else acc ++ ['_']) ++ [c.toLower]
    else acc ++ [c]
  String.ofList out

private def tsReserved : List String :=
  ["source_file", "program_header", "comment", "identifier", "number",
   "decimal", "string", "boolean", "_expr", "_type", "_command"]

/-- tree-sitter rule name for an op/fn declaration. -/
def opRuleName (name : String) : String :=
  let s := toSnake name
  if tsReserved.contains s then s ++ "_" else s

/-- Hidden union-rule name for a dialect syntax category. -/
def catRuleName (catName : String) : String := "_" ++ toSnake catName

/-- JS single-quoted string literal for a token. -/
private def jsStr (s : String) : String :=
  "'" ++ (s.replace "\\" "\\\\" |>.replace "'" "\\'") ++ "'"

/-- Split a leading `word(` token into `word` + `(` for nicer keyword highlighting. -/
private def splitWordParen (tk : String) : List String :=
  let cs := tk.toList
  if cs.length ≥ 2 && cs.getLast! == '(' &&
     cs.head!.isAlpha &&
     (cs.dropLast.all (fun c => c.isAlpha || c.isDigit || c == '_')) then
    [String.ofList cs.dropLast, "("]
  else [tk]

/-- Tokenize a raw literal atom: normalize whitespace, split on it, then peel a
    trailing `(` off alphabetic tokens. -/
def tokenizeLiteral (raw : String) : List String :=
  let norm := String.ofList (raw.toList.map fun c => if c == '\n' || c == '\t' then ' ' else c)
  ((norm.splitOn " ").filter (·.length > 0)).flatMap splitWordParen

/-- A JS rule expression referencing the rule for a syntax category.
    `nb` is the set of category rule-names that can match empty (nil-able lists,
    optional-only categories); references to them are wrapped in `optional(...)`
    so the referenced named rule itself can stay non-nullable. -/
partial def catRef (nb : List String) (c : SyntaxCat) : String :=
  let d := c.name.dialect
  let n := c.name.name
  let arg0 : String := if c.args.size > 0 then catRef nb c.args[0]! else "$.identifier"
  let named (rule : String) : String := if nb.contains rule then s!"optional($.{rule})" else s!"$.{rule}"
  if d == "Init" then
    match n with
    | "Ident" => "$.identifier"
    | "Num" => "$.number"
    | "Decimal" => "$.decimal"
    | "Str" => "$.string"
    | "Bool" => "$.boolean"
    | "Expr" => "$._expr"
    | "Type" => "$._type"
    | "TypeP" => "$._type"
    | "Option" => s!"optional({arg0})"
    | "CommaSepBy" => s!"commaSep({arg0})"
    | "SemicolonSepBy" => s!"semiSep({arg0})"
    | "Seq" => s!"repeat({arg0})"
    | "NewlineSepBy" => s!"repeat({arg0})"
    | "SpaceSepBy" => s!"repeat({arg0})"
    | "SpacePrefixSepBy" => s!"repeat({arg0})"
    | other => named (catRuleName other)
  else
    named (catRuleName n)

/-- A JS rule expression for an argument kind. -/
def kindRef (nb : List String) : ArgDeclKind → String
  | .type _ => "$._expr"
  | .cat c => catRef nb c

/-- Does category `c` reference the builtin leaf `Init.<leaf>` (possibly nested
    inside parametric wrappers like `CommaSepBy<Bool>`)? -/
partial def catUsesLeaf (leaf : String) (c : SyntaxCat) : Bool :=
  (c.name.dialect == "Init" && c.name.name == leaf) || c.args.any (catUsesLeaf leaf ·)

/-- Which builtin leaf nodes the generated tree-sitter grammar for `d` defines.
    Identifier/comment always exist; an Expr-bearing dialect (Core) also gets
    numeric leaves; string/boolean leaves exist only when those builtin
    categories are referenced.  Shared by the grammar and highlight generators so
    queries never reference a node the grammar omits. -/
structure TsLeaves where
  number : Bool
  decimal : Bool
  string : Bool
  boolean : Bool

def tsLeaves (d : Dialect) : TsLeaves :=
  let ops := d.declarations.filterMap fun | Decl.op od => some od | _ => none
  let fns := d.declarations.filterMap fun | Decl.function fd => some fd | _ => none
  let allKinds := (ops.flatMap (fun od => od.argDecls.toArray.map (·.kind))).toList
                ++ (fns.flatMap (fun fd => fd.argDecls.toArray.map (·.kind))).toList
  let leafUsed (leaf : String) : Bool := allKinds.any fun
    | .type _ => false
    | .cat c => catUsesLeaf leaf c
  let exprUsed := allKinds.any fun
    | .type _ => true
    | .cat c => c.name.dialect == "Init" && c.name.name == "Expr"
  { number := leafUsed "Num" || exprUsed
    decimal := leafUsed "Decimal" || exprUsed
    string := leafUsed "Str"
    boolean := leafUsed "Bool" }


/-- Flatten `indent` atoms (formatting-only) into their inner atoms. -/
partial def flattenAtoms : SyntaxDefAtom → List SyntaxDefAtom
  | .indent _ inner => inner.toList.flatMap flattenAtoms
  | a => [a]

/-- Is this op/fn just a single-argument passthrough (so it can be inlined into
    its category's `choice` rather than getting its own named rule)? -/
def isInlineDef (sd : SyntaxDef) : Bool :=
  match sd with
  | .passthrough => true
  | .std atoms _ =>
    let fa := atoms.toList.flatMap flattenAtoms
    fa.length == 1 && (match fa.head! with | .ident _ _ => true | _ => false)

/-- Does an op/fn produce no tokens at all (matches empty)? Such alternatives
    are dropped from category choices, and their category is treated as nullable. -/
def isEmptyDef (sd : SyntaxDef) : Bool :=
  match sd with
  | .passthrough => false
  | .std atoms _ =>
    let fa := atoms.toList.flatMap flattenAtoms
    fa.all (fun a => match a with | .indent _ _ => true | .str s => (strip s).isEmpty | _ => false)

/-- JS rule body for an op/fn from its `SyntaxDef` and argument decls.
    `nb` is the set of nullable category rule-names (see `catRef`). -/
def ruleBody (nb : List String) (argArr : Array ArgDecl) (sd : SyntaxDef) : String :=
  match sd with
  | .passthrough =>
    match argArr[0]? with | some ad => kindRef nb ad.kind | none => "$.identifier"
  | .std atoms p =>
    let fa := atoms.toList.flatMap flattenAtoms
    let atomJs : SyntaxDefAtom → List String := fun a =>
      match a with
      | .str raw => (tokenizeLiteral raw).map jsStr
      | .ident lvl _ => match argArr[lvl]? with | some ad => [kindRef nb ad.kind] | none => []
      | .indent _ _ => []
    let parts := fa.flatMap atomJs
    let seqStr := match parts with
      | [] => "seq()"
      | [x] => x
      | _ => "seq(" ++ ", ".intercalate parts ++ ")"
    -- operand precedences (resolved) for associativity detection
    let identPrecs := fa.filterMap fun a => match a with | .ident _ pr => some pr | _ => none
    let firstIsIdent := match fa.head? with | some (.ident _ _) => true | _ => false
    let lastIsIdent := match fa.reverse.head? with | some (.ident _ _) => true | _ => false
    if identPrecs.length == 2 && firstIsIdent && lastIsIdent && fa.length ≥ 3 then
      -- binary infix: derive associativity from operand precedences
      let p0 := identPrecs.head!
      let p1 := identPrecs.reverse.head!
      let dir := if p0 < p1 then "prec.left" else if p0 > p1 then "prec.right" else "prec.left"
      s!"{dir}({p}, {seqStr})"
    else if identPrecs.length == 1 && !firstIsIdent && lastIsIdent then
      -- prefix unary
      s!"prec.right({p}, {seqStr})"
    else seqStr

/-- A `choice(...)` (or singleton) over member rule expressions, deduped. -/
private def choiceOf (members : List String) : String :=
  let m := members.eraseDups
  match m with
  | [] => "seq()"
  | [x] => x
  | _ => "choice(" ++ ", ".intercalate m ++ ")"

/-- Member rule expression contributed by an op/fn to its category's choice:
    inline passthroughs directly, otherwise reference the named rule. -/
def memberRef (nb : List String) (name : String) (sd : SyntaxDef) (argArr : Array ArgDecl) : String :=
  if isInlineDef sd then ruleBody nb argArr sd else "$." ++ opRuleName name

def generateTreeSitter (d : Dialect) (tsName : String) : String :=
  let ops := d.declarations.filterMap fun | Decl.op od => some od | _ => none
  let fns := d.declarations.filterMap fun | Decl.function fd => some fd | _ => none
  let typeDecls := d.declarations.filterMap fun | Decl.type td => some td | _ => none
  let syncats := d.declarations.filterMap fun | Decl.syncat sc => some sc.name | _ => none
  -- Determine builtin Expr/Type usage by scanning all argument kinds.
  let kindsOf : Array ArgDecl → List ArgDeclKind := fun a => a.toList.map (·.kind)
  let allKinds := (ops.flatMap (fun od => (kindsOf od.argDecls.toArray).toArray)).toList
                ++ (fns.flatMap (fun fd => (kindsOf fd.argDecls.toArray).toArray)).toList
  let isExprKind : ArgDeclKind → Bool
    | .type _ => true
    | .cat c => c.name.dialect == "Init" && c.name.name == "Expr"
  let isTypeKind : ArgDeclKind → Bool
    | .type _ => false
    | .cat c => c.name.dialect == "Init" && (c.name.name == "Type" || c.name.name == "TypeP")
  -- Which builtin leaf nodes this grammar defines (see `tsLeaves`).  Only
  -- referenced leaves get a rule; e.g. Core never references `Init.Bool` (its
  -- `true`/`false` come from the `btrue`/`bfalse` fns), so a `boolean` leaf would
  -- clash with those literal tokens.
  let leaves := tsLeaves d
  let strUsed := leaves.string
  let boolUsed := leaves.boolean
  let exprUsed := allKinds.any isExprKind
  let typeUsed := allKinds.any isTypeKind
  -- Command-category ops form the top level.
  let isCommand : OpDecl → Bool := fun od => od.category.name == "Command"
  let commandOps := ops.filter isCommand
  let ruleLine (name body : String) : String := s!"    {name}: $ => {body},"
  -- Non-empty op members of a declared category (empty-producing ops are
  -- dropped: tree-sitter forbids rules that match the empty string).
  let opsInCat (catName : String) : List OpDecl :=
    ops.toList.filter (fun od => od.category.name == catName && !isEmptyDef od.syntaxDef)
  let hasEmptyOp (catName : String) : Bool :=
    ops.toList.any (fun od => od.category.name == catName && isEmptyDef od.syntaxDef)
  let allCatNames := syncats.toList.filter (· != "Command")
  -- A category's `choice(...)` body, with inner refs wrapped per nullable set `nb`.
  let catBodyWith (nb : List String) (catName : String) : String :=
    choiceOf ((opsInCat catName).map (fun od => memberRef nb od.name od.syntaxDef od.argDecls.toArray))
  let startsNullable (s : String) : Bool :=
    s.startsWith "optional(" || s.startsWith "commaSep(" || s.startsWith "semiSep("
      || s.startsWith "repeat(" || s == "seq()"
  -- Fixpoint over the nullable-category set: a category is nullable if it has an
  -- empty op alternative, has no concrete members, or its body is a top-level
  -- nullable combinator (possibly via a nullable member). References to nullable
  -- categories are emitted as `optional(...)` so the named rule stays non-nullable.
  let computeNb (nb : List String) : List String :=
    allCatNames.filterMap fun catName =>
      let rule := catRuleName catName
      if hasEmptyOp catName || (opsInCat catName).isEmpty then some rule
      else if startsNullable (catBodyWith nb catName) then some rule
      else none
  let nb := (List.range (allCatNames.length + 1)).foldl (fun acc _ => computeNb acc) []
  -- Categories whose rule body itself matches empty cannot be standalone rules
  -- (tree-sitter forbids nullable named rules, even when listed in `inline:`).
  -- We inline them textually: substitute their body at each use site and omit
  -- the rule definition.
  let inlineCats := allCatNames.filter fun catName =>
    !(opsInCat catName).isEmpty && startsNullable (catBodyWith nb catName)
  -- Substitution `$.<rule>` ↦ `(<body>)`, applied repeatedly to resolve chains
  -- of inlined categories referencing one another.
  let applyInline (s : String) : String :=
    (List.range (inlineCats.length + 1)).foldl (init := s) fun acc _ =>
      inlineCats.foldl (init := acc) fun a catName =>
        a.replace s!"$.{catRuleName catName}" s!"({catBodyWith nb catName})"
  let ruleLineI (name body : String) : String := ruleLine name (applyInline body)
  -- 1) Named op rules (for non-inline ops, dropping empty-producing ops).
  let opRules := ops.toList.filterMap fun od =>
    if isInlineDef od.syntaxDef || isEmptyDef od.syntaxDef then none
    else some (ruleLineI (opRuleName od.name) (ruleBody nb od.argDecls.toArray od.syntaxDef))
  -- 2) Category union rules (declared syncats; skip Command and inlined cats).
  let catRules := allCatNames.filterMap fun catName =>
    if (opsInCat catName).isEmpty || inlineCats.contains catName then none
    else some (ruleLineI (catRuleName catName) (catBodyWith nb catName))
  -- 3) _command rule.
  let commandMembers := commandOps.toList.filterMap fun od =>
    if isEmptyDef od.syntaxDef then none
    else some (memberRef nb od.name od.syntaxDef od.argDecls.toArray)
  let commandRule := if commandMembers.isEmpty then [] else [ruleLineI "_command" (choiceOf commandMembers)]
  -- 4) Expr rules (Core): operators come from `fn` decls woven into builtin Expr.
  let exprRules :=
    if !exprUsed then []
    else
      let fnMembers := fns.toList.filterMap fun fd =>
        if isEmptyDef fd.syntaxDef then none
        else some (memberRef nb fd.name fd.syntaxDef fd.argDecls.toArray)
      -- Expr leaves: identifier + numeric literals + parenthesized expr.
      -- (string/boolean only when referenced as builtin categories.)
      let exprLeaves := ["$.identifier", "$.number", "$.decimal"]
                  ++ (if strUsed then ["$.string"] else [])
                  ++ (if boolUsed then ["$.boolean"] else [])
                  ++ ["seq('(', $._expr, ')')"]
      let exprRule := ruleLineI "_expr" (choiceOf (fnMembers ++ exprLeaves))
      let fnRules := fns.toList.filterMap fun fd =>
        if isInlineDef fd.syntaxDef || isEmptyDef fd.syntaxDef then none
        else some (ruleLineI (opRuleName fd.name) (ruleBody nb fd.argDecls.toArray fd.syntaxDef))
      exprRule :: fnRules
  -- 5) Type rules (Core): primitive names + identifier + application.
  let typeRules :=
    if !typeUsed then []
    else
      let names := typeDecls.toList.map (fun td => jsStr td.name)
      let typeAtom := ruleLine "_type_atom" (choiceOf (names ++ ["$.identifier", "seq('(', $._type, ')')"]))
      let typeRule := ruleLine "_type" "prec.left(choice($._type_atom, seq($._type, $._type_atom)))"
      [typeRule, typeAtom]
  -- Assemble grammar.js.  The `conflicts:` set is loaded from a sibling
  -- `conflicts.json` (auto-discovered by resolve-conflicts.cjs), so regenerating
  -- grammar.js never loses the resolved conflicts.
  let preamble : List String := [
    s!"// {tsName} tree-sitter grammar.",
    "// AUTO-GENERATED from the Strata DDM grammar.",
    "// Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean treesitter",
    "// LR conflicts are loaded from conflicts.json; (re)generate it with:",
    "//   node resolve-conflicts.cjs",
    "",
    "const fs = require('fs');",
    "const path = require('path');",
    "let CONFLICTS = [];",
    "try { CONFLICTS = JSON.parse(fs.readFileSync(path.join(__dirname, 'conflicts.json'), 'utf8')); }",
    "catch (e) { /* no conflicts.json yet: run resolve-conflicts.cjs */ }",
    "",
    "function commaSep(rule) { return optional(seq(rule, repeat(seq(',', rule)))); }",
    "function semiSep(rule) { return optional(seq(rule, repeat(seq(';', rule)))); }",
    "",
    "module.exports = grammar({",
    s!"  name: '{tsName}',",
    "",
    "  extras: $ => [/\\s/, $.comment],",
    "  word: $ => $.identifier,",
    "  conflicts: $ => CONFLICTS.map(group => group.map(name => $[name])),",
    "",
    "  rules: {",
    "    source_file: $ => seq(optional($.program_header), repeat($._command)),",
    "    program_header: $ => seq('program', $.identifier, ';'),"
  ]
  -- Leaf rules: identifier + comment always; numeric/string/boolean only when
  -- referenced (an unreferenced `boolean` rule would clash with literal
  -- `'true'`/`'false'` tokens emitted by dialect functions, e.g. Core's btrue).
  let leafRules : List String :=
    ["    comment: $ => token(seq('//', /.*/)),",
     "    identifier: $ => /[A-Za-z_$][A-Za-z0-9_$]*/,"]
    ++ (if leaves.number then ["    number: $ => /[0-9]+/,"] else [])
    ++ (if leaves.decimal then ["    decimal: $ => /[0-9]+\\.[0-9]+/,"] else [])
    ++ (if leaves.string then ["    string: $ => /\"([^\"\\\\]|\\\\.)*\"/,"] else [])
    ++ (if leaves.boolean then ["    boolean: $ => choice('true', 'false'),"] else [])
  let footer : List String := ["  }", "});", ""]
  "\n".intercalate (preamble ++ commandRule ++ catRules ++ opRules ++ exprRules ++ typeRules ++ leafRules ++ footer)

/-- Tokens the grammar emits as a standalone *named* node whose body is exactly
    one literal string (e.g. `free: $ => 'free'`).  Such tokens are NOT queryable
    as anonymous-token strings in `highlights.scm` (the literal is hidden inside
    the named node), so the highlighter drops them from the string lists and
    queries them by node name instead.  Returns `(token, ruleName)` pairs. -/
def singleLiteralNodes (d : Dialect) : List (String × String) :=
  d.declarations.toList.filterMap fun decl =>
    let process (name : String) (sd : SyntaxDef) : Option (String × String) :=
      -- Mirror the grammar's emission rule: a single non-empty `.str` atom (after
      -- flattening `indent`), no `.ident`, becomes a named single-token rule.
      match sd with
      | .std atoms _ =>
        match atoms.toList.flatMap flattenAtoms with
        | [.str raw] =>
          match tokenizeLiteral raw with
          | [tok] => if tok.length > 0 then some (tok, opRuleName name) else none
          | _ => none
        | _ => none
      | .passthrough => none
    match decl with
    | Decl.op od => process od.name od.syntaxDef
    | Decl.function fd => process fd.name fd.syntaxDef
    | _ => none

/-- tree-sitter highlight queries (`highlights.scm`) for a dialect.  Node-name
    queries are gated on `tsLeaves` so they never reference a node the grammar
    omits (nvim errors on unknown nodes in a query). -/
def generateHighlights (t : GenTarget) : String :=
  let info := t.info
  let leaves := tsLeaves t.dialect
  -- Tokens hidden inside single-literal named nodes can't be matched as strings;
  -- query them by node name and drop them from the string-based lists.
  let namedTokens := singleLiteralNodes t.dialect
  let namedTokSet := namedTokens.map (·.1)
  let queryable (xs : List String) : List String := xs.filter (fun x => !namedTokSet.contains x)
  let bracketList (xs : List String) : String :=
    " ".intercalate (xs.map (fun s => "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""))
  let kws := queryable info.keywords
  let tys := queryable info.types
  let kwLine := if kws.isEmpty then [] else [s!"[{bracketList kws}] @keyword"]
  let tyLine := if tys.isEmpty then [] else [s!"[{bracketList tys}] @type.builtin"]
  let ops := (queryable (info.symbolOperators ++ info.wordOperators ++ [":="])).eraseDups
  let opLine := if ops.isEmpty then [] else [s!"[{bracketList ops}] @operator"]
  -- Builtin functions (e.g. `Int.DivT(`, `Sequence.empty`) are structural call
  -- nodes, not lexical tokens, so they're queried by fn-rule node name.  A fn is
  -- a builtin if its first literal contains a dot (matching extractSyntaxInfo).
  let builtinNodes := (t.dialect.declarations.toList.filterMap fun
      | Decl.function fd =>
        match (extractStrLiterals fd.syntaxDef |>.map strip |>.filter (·.length > 0)) with
        | first :: _ =>
          let clean := if first.endsWith "(" then String.ofList first.toList.dropLast else first
          if clean.contains '.' then some (opRuleName fd.name) else none
        | [] => none
      | _ => none).eraseDups
  let biLine := builtinNodes.map (fun rule => s!"({rule}) @function.builtin")
  -- Node-name queries for keyword/type tokens hidden in single-literal named nodes.
  let keywordSet := info.keywords ++ ["program"]
  let typeSet := info.types
  let nodeQueries := (namedTokens.filterMap fun (tok, rule) =>
      if typeSet.contains tok then some s!"({rule}) @type.builtin"
      else if keywordSet.contains tok then some s!"({rule}) @keyword"
      else none).eraseDups
  let leafQueries : List String :=
    (if leaves.string then ["(string) @string"] else [])
    ++ (if leaves.number then ["(number) @number"] else [])
    ++ (if leaves.decimal then ["(decimal) @number"] else [])
    ++ (if leaves.boolean then ["(boolean) @constant.builtin"] else [])
  let static : List String :=
    ["; AUTO-GENERATED tree-sitter highlights. Run: lake env lean --run editors/GenSyntax.lean treesitter",
     "",
     "(comment) @comment"]
    ++ leafQueries
    ++ ["(identifier) @variable", ""]
  "\n".intercalate (static ++ tyLine ++ kwLine ++ opLine ++ biLine ++ nodeQueries ++ [""])

/-- A pure-Node script that auto-discovers the LR conflict set by iterating
    `tree-sitter generate` and scraping its suggestions, then writes
    `conflicts.json`.  Run once after (re)generating `grammar.js`. -/
def generateConflictResolver : String :=
  "\n".intercalate [
    "#!/usr/bin/env node",
    "// AUTO-GENERATED conflict resolver for the Strata tree-sitter grammar.",
    "// Iteratively runs `tree-sitter generate`, scrapes the reported conflicting",
    "// rules, and accumulates them into conflicts.json (which grammar.js reads).",
    "// Re-run after editing grammar.js:  node resolve-conflicts.cjs",
    "const fs = require('fs');",
    "const { execSync } = require('child_process');",
    "const grammar = fs.readFileSync('grammar.js', 'utf8');",
    "const defined = new Set([...grammar.matchAll(/^    ([a-z_][a-z0-9_]*): \\$ =>/gm)].map(m => m[1]));",
    "const seen = new Set();",
    "let conflicts = [];",
    "function write() { fs.writeFileSync('conflicts.json', JSON.stringify(conflicts) + '\\n'); }",
    "for (let i = 0; i < 500; i++) {",
    "  write();",
    "  let out;",
    "  try { out = execSync('tree-sitter generate 2>&1', { encoding: 'utf8' }); }",
    "  catch (e) { out = (e.stdout || '') + (e.stderr || ''); }",
    "  if (!/Unresolved conflict|Caused by/.test(out)) {",
    "    console.log(`Resolved ${conflicts.length} conflict group(s).`);",
    "    write();",
    "    process.exit(0);",
    "  }",
    "  let cand = null;",
    "  const hint = out.match(/Add a conflict for these rules: (.+)/);",
    "  if (hint) cand = hint[1].split(',').map(s => s.trim().replace(/`/g, '')).filter(r => defined.has(r));",
    "  if (!cand || cand.length === 0) {",
    "    const rules = [];",
    "    for (const line of out.match(/^\\s+\\d+:\\s+.*$/gm) || []) {",
    "      const m = [...line.matchAll(/\\(([a-z_][a-z0-9_]*)\\b/g)].map(x => x[1]).find(r => defined.has(r));",
    "      if (m) rules.push(m);",
    "    }",
    "    cand = [...new Set(rules)].sort();",
    "  }",
    "  cand = [...new Set(cand)].sort();",
    "  const key = cand.join(',');",
    "  if (cand.length === 0 || seen.has(key)) {",
    "    console.error('Could not auto-resolve conflicts. Last tree-sitter output:\\n' + out);",
    "    process.exit(1);",
    "  }",
    "  seen.add(key);",
    "  conflicts.push(cand);",
    "}",
    "console.error('Conflict resolution did not converge after 500 iterations.');",
    "process.exit(1);",
    ""
  ]

/-! ## Main -/

def coreTarget : GenTarget :=
  { scope := "core-st", display := "Strata Core", ext := "core.st",
    dialect := Core, info := extractSyntaxInfo Core }

def laurelTarget : GenTarget :=
  { scope := "laurel-st", display := "Strata Laurel", ext := "laurel.st",
    dialect := Strata.Laurel.Laurel, info := extractLaurelInfo Strata.Laurel.Laurel }

def targets : List GenTarget := [coreTarget, laurelTarget]

def writeOut (path content : String) : IO Unit := do
  IO.println s!"Wrote {path}"
  IO.FS.writeFile path content

def main (args : List String) : IO Unit := do
  let target := args.head?.getD "all"
  let dir := "editors"
  let doVscode := target == "vscode" || target == "all"
  let doEmacs := target == "emacs" || target == "all"
  let doVim := target == "vim" || target == "all"
  let doTs := target == "treesitter" || target == "all"
  if !(doVscode || doEmacs || doVim || doTs) then
    IO.eprintln s!"Usage: lake env lean --run editors/GenSyntax.lean [vscode|emacs|vim|treesitter|all]"
    IO.Process.exit 1
  for t in targets do
    if doVscode then
      IO.FS.createDirAll s!"{dir}/vscode/syntaxes"
      writeOut s!"{dir}/vscode/syntaxes/{t.scope}.tmLanguage.json" (generateTextMate t)
    if doEmacs then
      IO.FS.createDirAll s!"{dir}/emacs"
      writeOut s!"{dir}/emacs/{t.scope}-mode.el" (generateEmacs t)
    if doVim then
      IO.FS.createDirAll s!"{dir}/vim/syntax"
      IO.FS.createDirAll s!"{dir}/vim/ftdetect"
      writeOut s!"{dir}/vim/syntax/{t.scope}.vim" (generateVim t)
      writeOut s!"{dir}/vim/ftdetect/{t.scope}.vim" (generateVimFtdetect t)
    if doTs then
      let tsName := t.scope.replace "-" "_"
      let tsDir := s!"{dir}/treesitter/{t.scope}"
      IO.FS.createDirAll s!"{tsDir}/queries"
      writeOut s!"{tsDir}/grammar.js" (generateTreeSitter t.dialect tsName)
      writeOut s!"{tsDir}/queries/highlights.scm" (generateHighlights t)
      writeOut s!"{tsDir}/resolve-conflicts.cjs" generateConflictResolver
      -- Seed an empty conflicts.json only if none exists (so a re-run of the
      -- generator never discards a previously resolved conflict set).
      let cjPath := s!"{tsDir}/conflicts.json"
      if !(← System.FilePath.pathExists cjPath) then
        writeOut cjPath "[]\n"
      -- Auto-resolve LR conflicts if the tree-sitter CLI is available.
      let resolved ← try
          let out ← IO.Process.output
            { cmd := "node", args := #["resolve-conflicts.cjs"], cwd := some tsDir }
          if out.exitCode == 0 then
            IO.print out.stdout
            pure true
          else
            IO.eprintln s!"  (conflict auto-resolution skipped: {out.stderr.take 200})"
            pure false
        catch _ =>
          pure false
      if !resolved then
        IO.println s!"  Note: run `node resolve-conflicts.cjs` in {tsDir} to compile (needs tree-sitter CLI)."

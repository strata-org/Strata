/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar

/-!
# Auto-generate editor syntax highlighting from the Core DDM grammar

Usage:
  lake env lean --run editors/GenSyntax.lean vscode   # writes editors/vscode/syntaxes/core-st.tmLanguage.json
  lake env lean --run editors/GenSyntax.lean emacs    # writes editors/emacs/core-st-mode.el
  lake env lean --run editors/GenSyntax.lean all      # writes both

The generator reads the `Core` dialect object (produced by `#strata_gen`)
and extracts types, keywords, operators, constants, and built-in function
names from the structured `SyntaxDef` data.  Static patterns (comments,
strings, labels, attributes, identifiers, numbers) are hardcoded since
they come from the DDM parser, not the dialect grammar.
-/

open Strata CoreDDM Strata.Elab

/-! ## Extract syntax tokens from the Dialect object -/

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

/-! ## TextMate JSON generator (VSCode) -/

private def escapeJsonStr (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

def escapeRegexForJson (s : String) : String :=
  let special := "\\^$.|?*+()[]{}".toList
  String.ofList <| s.toList.flatMap fun c =>
    if special.contains c then ['\\', '\\', c] else [c]

def generateTextMate (info : SyntaxInfo) : String :=
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
    s!"  {q}_comment{q}: {q}AUTO-GENERATED from the Core DDM grammar. Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vscode{q},",
    s!"  {q}name{q}: {q}Strata Core{q},",
    s!"  {q}scopeName{q}: {q}source.core-st{q},",
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
    s!"      {q}name{q}: {q}comment.line.double-slash.core-st{q},",
    s!"      {q}match{q}: {q}//.*${q}",
    s!"    {cb},",
    s!"    {q}string{q}: {ob}",
    s!"      {q}name{q}: {q}string.quoted.double.core-st{q},",
    s!"      {q}begin{q}: {q}\\{q}{q},",
    s!"      {q}end{q}: {q}\\{q}{q},",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.character.escape.core-st{q},",
    s!"          {q}match{q}: {q}\\\\\\\\.{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}attribute{q}: {ob}",
    s!"      {q}name{q}: {q}meta.attribute.core-st{q},",
    s!"      {q}match{q}: {q}@\\\\[[^\\\\]]*\\\\]{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.other.attribute-name.core-st{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}label{q}: {ob}",
    s!"      {q}name{q}: {q}meta.label.core-st{q},",
    s!"      {q}match{q}: {q}\\\\[([a-zA-Z_][a-zA-Z0-9_]*)\\\\]\\\\s*:{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.name.label.core-st{q} {cb},",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}entity.name.tag.core-st{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}number{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.numeric.decimal.core-st{q},",
    s!"          {q}match{q}: {q}\\\\b[0-9]+(\\\\.[0-9]+)?\\\\b{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}keyword{q}: {ob}",
    s!"      {q}name{q}: {q}keyword.core-st{q},",
    s!"      {q}match{q}: {q}{kwPattern}{q}",
    s!"    {cb},",
    s!"    {q}type{q}: {ob}",
    s!"      {q}name{q}: {q}support.type.core-st{q},",
    s!"      {q}match{q}: {q}{typePattern}{q}",
    s!"    {cb},",
    s!"    {q}constant{q}: {ob}",
    s!"      {q}name{q}: {q}constant.language.core-st{q},",
    s!"      {q}match{q}: {q}{constPattern}{q}",
    s!"    {cb},",
    s!"    {q}operator{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.assignment.core-st{q},",
    s!"          {q}match{q}: {q}:={q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.word.core-st{q},",
    s!"          {q}match{q}: {q}{wordOpPattern}{q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.symbol.core-st{q},",
    s!"          {q}match{q}: {q}{symOpPattern}{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}function-call{q}: {ob}",
    s!"      {q}match{q}: {q}{builtinPattern}{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}support.function.builtin.core-st{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}identifier{q}: {ob}",
    s!"      {q}name{q}: {q}variable.other.core-st{q},",
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

def generateEmacs (info : SyntaxInfo) : String :=
  let kwList := emacsWordList info.keywords
  let tyList := emacsWordList info.types
  let ctList := emacsWordList info.constants
  let opList := emacsWordList info.wordOperators
  let biList := emacsWordList info.builtinFunctions
  -- Build the file as a list of lines to avoid escape nightmares
  let lines : List String := [
    ";;; core-st-mode.el --- Major mode for Strata Core (.core.st) files -*- lexical-binding: t; -*-",
    "",
    ";; AUTO-GENERATED from the Core DDM grammar.",
    ";; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs",
    "",
    ";; Keywords",
    "(defvar core-st-keywords",
    s!"  '({kwList}))",
    "",
    "(defvar core-st-types",
    s!"  '({tyList}))",
    "",
    "(defvar core-st-constants",
    s!"  '({ctList}))",
    "",
    "(defvar core-st-operators",
    s!"  '({opList}))",
    "",
    "(defvar core-st-builtins",
    s!"  '({biList}))",
    "",
    ";; Font-lock rules",
    "(defvar core-st-font-lock-keywords",
    "  (let ((kw-re  (regexp-opt core-st-keywords  'symbols))",
    "        (ty-re  (regexp-opt core-st-types     'symbols))",
    "        (ct-re  (regexp-opt core-st-constants 'symbols))",
    "        (op-re  (regexp-opt core-st-operators 'symbols))",
    "        (bi-re  (regexp-opt core-st-builtins  'symbols)))",
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
    "(defvar core-st-mode-syntax-table",
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
    "(define-derived-mode core-st-mode prog-mode \"Core.st\"",
    "  \"Major mode for editing Strata Core (.core.st) files.\"",
    "  :syntax-table core-st-mode-syntax-table",
    "  (setq-local font-lock-defaults '(core-st-font-lock-keywords))",
    "  (setq-local comment-start \"// \")",
    "  (setq-local comment-end \"\"))",
    "",
    ";;;###autoload",
    "(add-to-list 'auto-mode-alist '(\"\\\\.core\\\\.st\\\\'\" . core-st-mode))",
    "",
    "(provide 'core-st-mode)",
    ";;; core-st-mode.el ends here",
    ""
  ]
  "\n".intercalate lines

/-! ## Main -/

def main (args : List String) : IO Unit := do
  let info := extractSyntaxInfo Core
  let target := args.head?.getD "all"
  let scriptDir := "editors"
  if target == "vscode" || target == "all" then
    let path := s!"{scriptDir}/vscode/syntaxes/core-st.tmLanguage.json"
    IO.FS.writeFile path (generateTextMate info)
    IO.println s!"Wrote {path}"
  if target == "emacs" || target == "all" then
    let path := s!"{scriptDir}/emacs/core-st-mode.el"
    IO.FS.writeFile path (generateEmacs info)
    IO.println s!"Wrote {path}"
  if target != "vscode" && target != "emacs" && target != "all" then
    IO.eprintln s!"Usage: lake env lean --run editors/GenSyntax.lean [vscode|emacs|all]"
    IO.Process.exit 1

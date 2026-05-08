/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.CoreMatch.DDMTransform.StrataGen

/-!
# Auto-generate editor syntax highlighting from Strata DDM grammars

Usage:
  lake env lean --run editors/GenSyntax.lean vscode   # writes vscode TextMate grammars
  lake env lean --run editors/GenSyntax.lean emacs    # writes emacs major modes
  lake env lean --run editors/GenSyntax.lean all      # writes both

The generator reads each dialect object produced by `#strata_gen` and
extracts types, keywords, operators, constants, and built-in function
names from the structured `SyntaxDef` data.  Static patterns (comments,
strings, labels, attributes, identifiers, numbers) are hardcoded since
they come from the DDM parser, not the dialect grammar.
-/

open Strata CoreDDM CoreMatchDDM Strata.Elab

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
  let keywordFnNames := ["forall", "forallT", "exists", "existsT", "old",
                          "match_expr", "matchExprArm_mk"]
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

structure LangCfg where
  langId : String
  scopeName : String
  displayName : String
  generatorTarget : String

def generateTextMate (cfg : LangCfg) (info : SyntaxInfo) : String :=
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
    s!"  {q}_comment{q}: {q}AUTO-GENERATED from the {cfg.generatorTarget} DDM grammar. Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vscode{q},",
    s!"  {q}name{q}: {q}{cfg.displayName}{q},",
    s!"  {q}scopeName{q}: {q}source.{cfg.langId}{q},",
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
    s!"      {q}name{q}: {q}comment.line.double-slash.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}//.*${q}",
    s!"    {cb},",
    s!"    {q}string{q}: {ob}",
    s!"      {q}name{q}: {q}string.quoted.double.{cfg.langId}{q},",
    s!"      {q}begin{q}: {q}\\{q}{q},",
    s!"      {q}end{q}: {q}\\{q}{q},",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.character.escape.{cfg.langId}{q},",
    s!"          {q}match{q}: {q}\\\\\\\\.{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}attribute{q}: {ob}",
    s!"      {q}name{q}: {q}meta.attribute.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}@\\\\[[^\\\\]]*\\\\]{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.other.attribute-name.{cfg.langId}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}label{q}: {ob}",
    s!"      {q}name{q}: {q}meta.label.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}\\\\[([a-zA-Z_][a-zA-Z0-9_]*)\\\\]\\\\s*:{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}0{q}: {ob} {q}name{q}: {q}entity.name.label.{cfg.langId}{q} {cb},",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}entity.name.tag.{cfg.langId}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}number{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}constant.numeric.decimal.{cfg.langId}{q},",
    s!"          {q}match{q}: {q}\\\\b[0-9]+(\\\\.[0-9]+)?\\\\b{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}keyword{q}: {ob}",
    s!"      {q}name{q}: {q}keyword.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}{kwPattern}{q}",
    s!"    {cb},",
    s!"    {q}type{q}: {ob}",
    s!"      {q}name{q}: {q}support.type.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}{typePattern}{q}",
    s!"    {cb},",
    s!"    {q}constant{q}: {ob}",
    s!"      {q}name{q}: {q}constant.language.{cfg.langId}{q},",
    s!"      {q}match{q}: {q}{constPattern}{q}",
    s!"    {cb},",
    s!"    {q}operator{q}: {ob}",
    s!"      {q}patterns{q}: [",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.assignment.{cfg.langId}{q},",
    s!"          {q}match{q}: {q}:={q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.word.{cfg.langId}{q},",
    s!"          {q}match{q}: {q}{wordOpPattern}{q}",
    s!"        {cb},",
    s!"        {ob}",
    s!"          {q}name{q}: {q}keyword.operator.symbol.{cfg.langId}{q},",
    s!"          {q}match{q}: {q}{symOpPattern}{q}",
    s!"        {cb}",
    "      ]",
    s!"    {cb},",
    s!"    {q}function-call{q}: {ob}",
    s!"      {q}match{q}: {q}{builtinPattern}{q},",
    s!"      {q}captures{q}: {ob}",
    s!"        {q}1{q}: {ob} {q}name{q}: {q}support.function.builtin.{cfg.langId}{q} {cb}",
    s!"      {cb}",
    s!"    {cb},",
    s!"    {q}identifier{q}: {ob}",
    s!"      {q}name{q}: {q}variable.other.{cfg.langId}{q},",
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

structure EmacsCfg where
  langId : String
  modeLine : String
  /-- Raw elisp regex string for `auto-mode-alist`; inserted verbatim. -/
  extRegex : String
  displayName : String

def generateEmacs (cfg : EmacsCfg) (info : SyntaxInfo) : String :=
  let kwList := emacsWordList info.keywords
  let tyList := emacsWordList info.types
  let ctList := emacsWordList info.constants
  let opList := emacsWordList info.wordOperators
  let biList := emacsWordList info.builtinFunctions
  let id := cfg.langId
  let lines : List String := [
    s!";;; {id}-mode.el --- Major mode for {cfg.displayName} files -*- lexical-binding: t; -*-",
    "",
    ";; AUTO-GENERATED from the Strata DDM grammar.",
    ";; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs",
    "",
    ";; Keywords",
    s!"(defvar {id}-keywords",
    s!"  '({kwList}))",
    "",
    s!"(defvar {id}-types",
    s!"  '({tyList}))",
    "",
    s!"(defvar {id}-constants",
    s!"  '({ctList}))",
    "",
    s!"(defvar {id}-operators",
    s!"  '({opList}))",
    "",
    s!"(defvar {id}-builtins",
    s!"  '({biList}))",
    "",
    ";; Font-lock rules",
    s!"(defvar {id}-font-lock-keywords",
    s!"  (let ((kw-re  (regexp-opt {id}-keywords  'symbols))",
    s!"        (ty-re  (regexp-opt {id}-types     'symbols))",
    s!"        (ct-re  (regexp-opt {id}-constants 'symbols))",
    s!"        (op-re  (regexp-opt {id}-operators 'symbols))",
    s!"        (bi-re  (regexp-opt {id}-builtins  'symbols)))",
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
    s!"(defvar {id}-mode-syntax-table",
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
    s!"(define-derived-mode {id}-mode prog-mode \"{cfg.modeLine}\"",
    s!"  \"Major mode for editing {cfg.displayName} files.\"",
    s!"  :syntax-table {id}-mode-syntax-table",
    s!"  (setq-local font-lock-defaults '({id}-font-lock-keywords))",
    "  (setq-local comment-start \"// \")",
    "  (setq-local comment-end \"\"))",
    "",
    ";;;###autoload",
    s!"(add-to-list 'auto-mode-alist '(\"{cfg.extRegex}\" . {id}-mode))",
    "",
    s!"(provide '{id}-mode)",
    s!";;; {id}-mode.el ends here",
    ""
  ]
  "\n".intercalate lines

structure DialectGenSpec where
  /-- Every dialect whose ops should appear in the highlighter. For
  dialects that import others (e.g. `CoreMatch` imports `Core`), list
  each one: `Dialect.declarations` only carries the locally-declared
  ops, so imports must be extracted and merged separately. -/
  dialects : List Dialect
  vscode : LangCfg
  emacs : EmacsCfg

def SyntaxInfo.merge (a b : SyntaxInfo) : SyntaxInfo :=
  { types := (a.types ++ b.types).eraseDups
    keywords := (a.keywords ++ b.keywords).eraseDups
    wordOperators := (a.wordOperators ++ b.wordOperators).eraseDups
    constants := (a.constants ++ b.constants).eraseDups
    builtinFunctions := (a.builtinFunctions ++ b.builtinFunctions).eraseDups
    symbolOperators := (a.symbolOperators ++ b.symbolOperators).eraseDups }

def SyntaxInfo.empty : SyntaxInfo :=
  { types := [], keywords := [], wordOperators := [],
    constants := [], builtinFunctions := [], symbolOperators := [] }

def coreSpec : DialectGenSpec :=
  { dialects := [Core]
    vscode := { langId := "core-st"
                scopeName := "source.core-st"
                displayName := "Strata Core"
                generatorTarget := "Core" }
    emacs := { langId := "core-st"
               modeLine := "Core.st"
               extRegex := "\\\\.core\\\\.st\\\\'"
               displayName := "Strata Core (.core.st)" } }

def coreMatchSpec : DialectGenSpec :=
  { dialects := [Core, CoreMatch]
    vscode := { langId := "coreMatch-st"
                scopeName := "source.coreMatch-st"
                displayName := "Strata CoreMatch"
                generatorTarget := "CoreMatch" }
    emacs := { langId := "coreMatch-st"
               modeLine := "CoreMatch.st"
               extRegex := "\\\\.coreMatch\\\\.st\\\\'"
               displayName := "Strata CoreMatch (.coreMatch.st)" } }

def writeForDialect (spec : DialectGenSpec) (target : String) : IO Unit := do
  let info := spec.dialects.foldl (init := SyntaxInfo.empty) fun acc d =>
    SyntaxInfo.merge acc (extractSyntaxInfo d)
  let scriptDir := "editors"
  if target == "vscode" || target == "all" then
    let path := s!"{scriptDir}/vscode/syntaxes/{spec.vscode.langId}.tmLanguage.json"
    IO.FS.writeFile path (generateTextMate spec.vscode info)
    IO.println s!"Wrote {path}"
  if target == "emacs" || target == "all" then
    let path := s!"{scriptDir}/emacs/{spec.emacs.langId}-mode.el"
    IO.FS.writeFile path (generateEmacs spec.emacs info)
    IO.println s!"Wrote {path}"

def main (args : List String) : IO Unit := do
  let target := args.head?.getD "all"
  if target != "vscode" && target != "emacs" && target != "all" then
    IO.eprintln s!"Usage: lake env lean --run editors/GenSyntax.lean [vscode|emacs|all]"
    IO.Process.exit 1
  writeForDialect coreSpec target
  writeForDialect coreMatchSpec target

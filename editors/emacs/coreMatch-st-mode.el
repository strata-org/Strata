;;; coreMatch-st-mode.el --- Major mode for Strata CoreMatch (.coreMatch.st) files -*- lexical-binding: t; -*-

;; AUTO-GENERATED from the Strata DDM grammar.
;; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs

;; Keywords
(defvar coreMatch-st-keywords
  '(    "var" "assume" "assert" "cover" "if" "else" "havoc" "invariant"
    "decreases" "while" "out" "inout" "call" "exit" "free" "ensures"
    "requires" "spec" "procedure" "type" "const" "function" "inline"
    "rec" "axiom" "distinct" "datatype" "old" "forall" "exists"
    "program" "match" "arm"))

(defvar coreMatch-st-types
  '(    "bool" "int" "string" "regex" "real" "bv1" "bv8" "bv16" "bv32"
    "bv64" "Map" "Sequence"))

(defvar coreMatch-st-constants
  '(    "true" "false" "null"))

(defvar coreMatch-st-operators
  '(    "div" "mod" "sdiv" "smod" "safesdiv" "safesmod"))

(defvar coreMatch-st-builtins
  '(    "Sequence.length" "Sequence.select" "Sequence.append"
    "Sequence.build" "Sequence.update" "Sequence.contains"
    "Sequence.take" "Sequence.drop" "str.len" "str.concat" "str.substr"
    "str.to.re" "str.in.re" "str.prefixof" "str.suffixof" "re.allchar"
    "re.all" "re.range" "re.concat" "re.*" "re.+" "re.loop" "re.union"
    "re.inter" "re.comp" "re.none" "Int.DivT" "Int.ModT"))

;; Font-lock rules
(defvar coreMatch-st-font-lock-keywords
  (let ((kw-re  (regexp-opt coreMatch-st-keywords  'symbols))
        (ty-re  (regexp-opt coreMatch-st-types     'symbols))
        (ct-re  (regexp-opt coreMatch-st-constants 'symbols))
        (op-re  (regexp-opt coreMatch-st-operators 'symbols))
        (bi-re  (regexp-opt coreMatch-st-builtins  'symbols)))
    `((,kw-re . font-lock-keyword-face)
      (,ty-re . font-lock-type-face)
      (,ct-re . font-lock-constant-face)
      (,op-re . font-lock-keyword-face)
      (,bi-re . font-lock-builtin-face)
      ;; Attributes: @[...]
      ("@\\[[^]]*\\]" . font-lock-preprocessor-face)
      ;; Labels: [name]:
      ("\\[\\([a-zA-Z_][a-zA-Z0-9_]*\\)\\]\\s-*:" 1 font-lock-function-name-face)
      ;; Numeric literals
      ("\\b[0-9]+\\(?:\\.[0-9]+\\)?\\b" . font-lock-constant-face))))

;; Syntax table
(defvar coreMatch-st-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; // line comments
    (modify-syntax-entry ?/ ". 12" st)
    (modify-syntax-entry ?\n ">" st)
    ;; String literals
    (modify-syntax-entry ?\" "\"" st)
    ;; Backslash escapes in strings
    (modify-syntax-entry ?\\ "\\" st)
    ;; Brackets
    (modify-syntax-entry ?\( "()" st)
    (modify-syntax-entry ?\) ")(" st)
    (modify-syntax-entry ?\{ "(}" st)
    (modify-syntax-entry ?\} "){" st)
    (modify-syntax-entry ?\[ "(]" st)
    (modify-syntax-entry ?\] ")[" st)
    ;; Dot and underscore are symbol constituents
    (modify-syntax-entry ?. "_" st)
    (modify-syntax-entry ?_ "_" st)
    st))

;;;###autoload
(define-derived-mode coreMatch-st-mode prog-mode "CoreMatch.st"
  "Major mode for editing Strata CoreMatch (.coreMatch.st) files."
  :syntax-table coreMatch-st-mode-syntax-table
  (setq-local font-lock-defaults '(coreMatch-st-font-lock-keywords))
  (setq-local comment-start "// ")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.coreMatch\\.st\\'" . coreMatch-st-mode))

(provide 'coreMatch-st-mode)
;;; coreMatch-st-mode.el ends here

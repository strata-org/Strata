;;; core-st-mode.el --- Major mode for Strata Core (.core.st) files -*- lexical-binding: t; -*-

;; AUTO-GENERATED from the Core DDM grammar.
;; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs

;; Keywords
(defvar core-st-keywords
  '(    "var" "assume" "assert" "cover" "if" "else" "havoc" "invariant"
    "decreases" "while" "out" "inout" "call" "exit" "free" "ensures"
    "requires" "spec" "procedure" "type" "const" "function" "inline"
    "rec" "axiom" "distinct" "datatype" "old" "forall" "exists"
    "program"))

(defvar core-st-types
  '(    "bool" "int" "string" "regex" "real" "bv1" "bv8" "bv16" "bv32"
    "bv64" "Map" "Sequence"))

(defvar core-st-constants
  '(    "true" "false" "null"))

(defvar core-st-operators
  '(    "div" "mod" "sdiv" "smod" "safesdiv" "safesmod"))

(defvar core-st-builtins
  '(    "Sequence.length" "Sequence.select" "Sequence.append"
    "Sequence.build" "Sequence.update" "Sequence.contains"
    "Sequence.take" "Sequence.drop" "str.len" "str.concat" "str.substr"
    "str.to.re" "str.in.re" "str.prefixof" "str.suffixof" "re.allchar"
    "re.all" "re.range" "re.concat" "re.*" "re.+" "re.loop" "re.union"
    "re.inter" "re.comp" "re.none" "Int.DivT" "Int.ModT"))

;; Font-lock rules
(defvar core-st-font-lock-keywords
  (let ((kw-re  (regexp-opt core-st-keywords  'symbols))
        (ty-re  (regexp-opt core-st-types     'symbols))
        (ct-re  (regexp-opt core-st-constants 'symbols))
        (op-re  (regexp-opt core-st-operators 'symbols))
        (bi-re  (regexp-opt core-st-builtins  'symbols)))
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
(defvar core-st-mode-syntax-table
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
(define-derived-mode core-st-mode prog-mode "Core.st"
  "Major mode for editing Strata Core (.core.st) files."
  :syntax-table core-st-mode-syntax-table
  (setq-local font-lock-defaults '(core-st-font-lock-keywords))
  (setq-local comment-start "// ")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.core\\.st\\'" . core-st-mode))

(provide 'core-st-mode)
;;; core-st-mode.el ends here

;;; laurel-st-mode.el --- Major mode for Strata Laurel (.laurel.st) files -*- lexical-binding: t; -*-

;; AUTO-GENERATED from the Strata Laurel DDM grammar.
;; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs

;; Keywords
(defvar laurel-st-keywords
  '(    "var" "new" "assign" "forall" "exists" "summary" "else" "if" "then"
    "assert" "assume" "return" "exit" "invariant" "while" "for" "is"
    "as" "extends" "datatype" "invokeOn" "requires" "ensures" "modifies"
    "returns" "opaque" "external" "procedure" "function" "composite"
    "constrained" "where" "witness"))

(defvar laurel-st-types
  '(    "int" "bool" "real" "float64" "string" "bv" "Core" "Map"))

(defvar laurel-st-constants
  '(    "true" "false"))

(defvar laurel-st-operators
  '(    ))

(defvar laurel-st-builtins
  '(    ))

;; Font-lock rules
(defvar laurel-st-font-lock-keywords
  (let ((kw-re  (regexp-opt laurel-st-keywords  'symbols))
        (ty-re  (regexp-opt laurel-st-types     'symbols))
        (ct-re  (regexp-opt laurel-st-constants 'symbols))
        (op-re  (regexp-opt laurel-st-operators 'symbols))
        (bi-re  (regexp-opt laurel-st-builtins  'symbols)))
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
(defvar laurel-st-mode-syntax-table
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
(define-derived-mode laurel-st-mode prog-mode "Strata Laurel"
  "Major mode for editing Strata Laurel (.laurel.st) files."
  :syntax-table laurel-st-mode-syntax-table
  (setq-local font-lock-defaults '(laurel-st-font-lock-keywords))
  (setq-local comment-start "// ")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.laurel\\.st\\'" . laurel-st-mode))

(provide 'laurel-st-mode)
;;; laurel-st-mode.el ends here

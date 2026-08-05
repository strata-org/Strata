;;; core-st-mode.el --- Major mode for Strata Core (.core.st) files -*- lexical-binding: t; -*-

;; AUTO-GENERATED from the Core DDM grammar.
;; Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean emacs

;; Keywords
(defvar core-st-keywords
  '(    "var" "assume" "assert" "cover" "if" "else" "havoc" "invariant"
    "decreases" "while" "out" "inout" "call" "exit" "free" "ensures"
    "requires" "spec" "procedure" "type" "const" "function" "inline"
    "rec" "axiom" "distinct" "datatype" "goto" "cfg" "old" "forall"
    "exists" "program"))

(defvar core-st-types
  '(    "bool" "int" "string" "regex" "real" "bv" "W1" "W8" "W16" "W32"
    "W64" "W128" "Map" "Sequence"))

(defvar core-st-constants
  '(    "true" "false" "null"))

(defvar core-st-operators
  '(    ))

(defvar core-st-builtins
  '(    "Sequence.empty" "Sequence.length" "Sequence.select"
    "Sequence.append" "Sequence.build" "Sequence.update"
    "Sequence.contains" "Sequence.take" "Sequence.drop" "str.len"
    "str.concat" "str.substr" "str.to.re" "str.in.re" "str.prefixof"
    "str.suffixof" "str.contains" "str.indexof" "str.replace" "str.at"
    "str.lt" "str.le" "re.allchar" "re.all" "re.range" "re.concat"
    "re.*" "re.+" "re.loop" "re.union" "re.inter" "re.comp" "re.none"
    "int.neg" "real.neg" "bv1.neg" "bv1.not" "bv8.neg" "bv8.not"
    "bv16.neg" "bv16.not" "bv32.neg" "bv32.not" "bv64.neg" "bv64.not"
    "bv1.safeNeg" "bv1.safeUNeg" "bv8.safeNeg" "bv8.safeUNeg"
    "bv16.safeNeg" "bv16.safeUNeg" "bv32.safeNeg" "bv32.safeUNeg"
    "bv64.safeNeg" "bv64.safeUNeg" "bv1.sNegOverflow" "bv1.uNegOverflow"
    "bv8.sNegOverflow" "bv8.uNegOverflow" "bv16.sNegOverflow"
    "bv16.uNegOverflow" "bv32.sNegOverflow" "bv32.uNegOverflow"
    "bv64.sNegOverflow" "bv64.uNegOverflow" "bv1.toUInt" "bv1.toInt"
    "bv8.toUInt" "bv8.toInt" "bv16.toUInt" "bv16.toInt" "bv32.toUInt"
    "bv32.toInt" "bv64.toUInt" "bv64.toInt" "bv128.toUInt" "bv128.toInt"
    "int.add" "int.sub" "int.mul" "real.add" "real.sub" "real.mul"
    "bv1.add" "bv1.sub" "bv1.mul" "bv8.add" "bv8.sub" "bv8.mul"
    "bv16.add" "bv16.sub" "bv16.mul" "bv32.add" "bv32.sub" "bv32.mul"
    "bv64.add" "bv64.sub" "bv64.mul" "int.div" "int.mod" "real.div"
    "bv1.uDiv" "bv1.uMod" "bv1.sDiv" "bv1.sMod" "bv8.uDiv" "bv8.uMod"
    "bv8.sDiv" "bv8.sMod" "bv16.uDiv" "bv16.uMod" "bv16.sDiv"
    "bv16.sMod" "bv32.uDiv" "bv32.uMod" "bv32.sDiv" "bv32.sMod"
    "bv64.uDiv" "bv64.uMod" "bv64.sDiv" "bv64.sMod" "bv1.and" "bv1.or"
    "bv1.xor" "bv1.shl" "bv1.uShr" "bv1.sShr" "bv8.and" "bv8.or"
    "bv8.xor" "bv8.shl" "bv8.uShr" "bv8.sShr" "bv16.and" "bv16.or"
    "bv16.xor" "bv16.shl" "bv16.uShr" "bv16.sShr" "bv32.and" "bv32.or"
    "bv32.xor" "bv32.shl" "bv32.uShr" "bv32.sShr" "bv64.and" "bv64.or"
    "bv64.xor" "bv64.shl" "bv64.uShr" "bv64.sShr" "int.safeDiv"
    "int.safeMod" "bv1.safeAdd" "bv1.safeSub" "bv1.safeMul"
    "bv1.safeUAdd" "bv1.safeUSub" "bv1.safeUMul" "bv1.safeSDiv"
    "bv1.safeSMod" "bv8.safeAdd" "bv8.safeSub" "bv8.safeMul"
    "bv8.safeUAdd" "bv8.safeUSub" "bv8.safeUMul" "bv8.safeSDiv"
    "bv8.safeSMod" "bv16.safeAdd" "bv16.safeSub" "bv16.safeMul"
    "bv16.safeUAdd" "bv16.safeUSub" "bv16.safeUMul" "bv16.safeSDiv"
    "bv16.safeSMod" "bv32.safeAdd" "bv32.safeSub" "bv32.safeMul"
    "bv32.safeUAdd" "bv32.safeUSub" "bv32.safeUMul" "bv32.safeSDiv"
    "bv32.safeSMod" "bv64.safeAdd" "bv64.safeSub" "bv64.safeMul"
    "bv64.safeUAdd" "bv64.safeUSub" "bv64.safeUMul" "bv64.safeSDiv"
    "bv64.safeSMod" "int.divT" "int.modT" "int.safeDivT" "int.safeModT"
    "int.le" "int.lt" "int.ge" "int.gt" "real.le" "real.lt" "real.ge"
    "real.gt" "bv1.uLe" "bv1.uLt" "bv1.uGe" "bv1.uGt" "bv8.uLe"
    "bv8.uLt" "bv8.uGe" "bv8.uGt" "bv16.uLe" "bv16.uLt" "bv16.uGe"
    "bv16.uGt" "bv32.uLe" "bv32.uLt" "bv32.uGe" "bv32.uGt" "bv64.uLe"
    "bv64.uLt" "bv64.uGe" "bv64.uGt" "bv1.sLe" "bv1.sLt" "bv1.sGe"
    "bv1.sGt" "bv8.sLe" "bv8.sLt" "bv8.sGe" "bv8.sGt" "bv16.sLe"
    "bv16.sLt" "bv16.sGe" "bv16.sGt" "bv32.sLe" "bv32.sLt" "bv32.sGe"
    "bv32.sGt" "bv64.sLe" "bv64.sLt" "bv64.sGe" "bv64.sGt"
    "bv1.sAddOverflow" "bv1.sSubOverflow" "bv1.sMulOverflow"
    "bv1.sDivOverflow" "bv1.uAddOverflow" "bv1.uSubOverflow"
    "bv1.uMulOverflow" "bv8.sAddOverflow" "bv8.sSubOverflow"
    "bv8.sMulOverflow" "bv8.sDivOverflow" "bv8.uAddOverflow"
    "bv8.uSubOverflow" "bv8.uMulOverflow" "bv16.sAddOverflow"
    "bv16.sSubOverflow" "bv16.sMulOverflow" "bv16.sDivOverflow"
    "bv16.uAddOverflow" "bv16.uSubOverflow" "bv16.uMulOverflow"
    "bv32.sAddOverflow" "bv32.sSubOverflow" "bv32.sMulOverflow"
    "bv32.sDivOverflow" "bv32.uAddOverflow" "bv32.uSubOverflow"
    "bv32.uMulOverflow" "bv64.sAddOverflow" "bv64.sSubOverflow"
    "bv64.sMulOverflow" "bv64.sDivOverflow" "bv64.uAddOverflow"
    "bv64.uSubOverflow" "bv64.uMulOverflow"))

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

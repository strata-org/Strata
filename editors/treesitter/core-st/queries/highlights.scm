; AUTO-GENERATED tree-sitter highlights. Run: lake env lean --run editors/GenSyntax.lean treesitter

(comment) @comment
(string) @string
(number) @number
(decimal) @number
(identifier) @variable

["bool" "int" "string" "regex" "real" "bv1" "bv8" "bv16" "bv32" "bv64" "bv128" "Map" "Sequence"] @type.builtin
["var" "assume" "assert" "cover" "if" "else" "havoc" "invariant" "decreases" "while" "out" "inout" "call" "exit" "ensures" "requires" "spec" "procedure" "type" "const" "function" "rec" "axiom" "distinct" "datatype" "old" "forall" "exists" "program"] @keyword
["!" "<==>" "==>" "&&" "||" "==" "!=" "<=" "<" ">=" ">" "-" "+" "/" "%" "/t" "%t" "~" "&" "|" "^" "<<" ">>" ">>s" "safe+" "safe-" "safe*" "safe_neg" "<s" "<=s" ">s" ">=s" "div" "mod" "sdiv" "smod" "safesdiv" "safesmod" ":="] @operator
(seq_empty) @function.builtin
(seq_length) @function.builtin
(seq_select) @function.builtin
(seq_append) @function.builtin
(seq_build) @function.builtin
(seq_update) @function.builtin
(seq_contains) @function.builtin
(seq_take) @function.builtin
(seq_drop) @function.builtin
(str_len) @function.builtin
(str_concat) @function.builtin
(str_substr) @function.builtin
(str_toregex) @function.builtin
(str_inregex) @function.builtin
(str_prefixof) @function.builtin
(str_suffixof) @function.builtin
(re_allchar) @function.builtin
(re_all) @function.builtin
(re_range) @function.builtin
(re_concat) @function.builtin
(re_star) @function.builtin
(re_plus) @function.builtin
(re_loop) @function.builtin
(re_union) @function.builtin
(re_inter) @function.builtin
(re_comp) @function.builtin
(re_none) @function.builtin
(divt_expr) @function.builtin
(modt_expr) @function.builtin
(bv_neg_overflow) @function.builtin
(bv_uneg_overflow) @function.builtin
(bv_sadd_overflow) @function.builtin
(bv_ssub_overflow) @function.builtin
(bv_smul_overflow) @function.builtin
(bv_sdiv_overflow) @function.builtin
(bv_uadd_overflow) @function.builtin
(bv_usub_overflow) @function.builtin
(bv_umul_overflow) @function.builtin
(free) @keyword
(inline) @keyword

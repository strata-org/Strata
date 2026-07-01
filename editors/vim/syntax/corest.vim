" Strata Core syntax highlighting for Vim/Neovim (filetype: corest).
" AUTO-GENERATED from the Strata Core DDM grammar.
" Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vim

if exists("b:current_syntax") | finish | endif

syntax keyword corestKeyword var assume assert cover if else havoc invariant
syntax keyword corestKeyword decreases while out inout call exit free ensures
syntax keyword corestKeyword requires spec procedure type const function inline rec
syntax keyword corestKeyword axiom distinct datatype old forall exists program
syntax keyword corestType bool int string regex real bv1 bv8 bv16
syntax keyword corestType bv32 bv64 bv128 Map Sequence
syntax keyword corestConstant true false null
syntax keyword corestWordOp div mod sdiv smod safesdiv safesmod
syntax match corestOperator "safe_neg\|safe-\|safe+\|safe\*\|<==>\|>=s\|==>\|>>s\|<=s\|:=\|||\|>=\|/t\|%t\|<<\|>>\|&&\|<s\|==\|!=\|<=\|>s\|<\|\^\|+\|\*\|!\|/\|%\|>\|-\|\~\|&\||"
syntax match corestBuiltin "Sequence\.empty\|Sequence\.length\|Sequence\.select\|Sequence\.append\|Sequence\.build\|Sequence\.update\|Sequence\.contains\|Sequence\.take\|Sequence\.drop\|str\.len\|str\.concat\|str\.substr\|str\.to\.re\|str\.in\.re\|str\.prefixof\|str\.suffixof\|re\.allchar\|re\.all\|re\.range\|re\.concat\|re\.\*\|re\.+\|re\.loop\|re\.union\|re\.inter\|re\.comp\|re\.none\|Int\.DivT\|Int\.ModT\|Bv\.SNegOverflow\|Bv\.UNegOverflow\|Bv\.SAddOverflow\|Bv\.SSubOverflow\|Bv\.SMulOverflow\|Bv\.SDivOverflow\|Bv\.UAddOverflow\|Bv\.USubOverflow\|Bv\.UMulOverflow"

syntax match corestComment "//.*$"
syntax region corestString start=+"+ skip=+\\"+ end=+"+
syntax match corestNumber "\<[0-9]\+\(\.[0-9]\+\)\?\>"
syntax match corestAttribute "@\[[^]]*\]"
syntax match corestLabel "\[[a-zA-Z_][a-zA-Z0-9_]*\]\s*:"

highlight default link corestKeyword Keyword
highlight default link corestType Type
highlight default link corestConstant Constant
highlight default link corestOperator Operator
highlight default link corestWordOp Operator
highlight default link corestBuiltin Function
highlight default link corestComment Comment
highlight default link corestString String
highlight default link corestNumber Number
highlight default link corestAttribute PreProc
highlight default link corestLabel Label

let b:current_syntax = "corest"
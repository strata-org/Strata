" Strata Laurel syntax highlighting for Vim/Neovim (filetype: laurelst).
" AUTO-GENERATED from the Strata Laurel DDM grammar.
" Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean vim

if exists("b:current_syntax") | finish | endif

syntax keyword laurelstKeyword var new assign forall exists summary else if
syntax keyword laurelstKeyword then assert assume return exit invariant while for
syntax keyword laurelstKeyword is as extends datatype invokeOn requires ensures modifies
syntax keyword laurelstKeyword returns opaque external procedure function composite constrained where
syntax keyword laurelstKeyword witness
syntax keyword laurelstType int bool real float64 string bv Core Map
syntax keyword laurelstConstant true false
syntax match laurelstOperator "==>\|!=\|||\|<=\|==\|>=\|&&\|++\|:=\|=>\|<\|=\|>\|+\|&\||\|-\|\*\|/\|%\|!\|#"

syntax match laurelstComment "//.*$"
syntax region laurelstString start=+"+ skip=+\\"+ end=+"+
syntax match laurelstNumber "\<[0-9]\+\(\.[0-9]\+\)\?\>"
syntax match laurelstAttribute "@\[[^]]*\]"
syntax match laurelstLabel "\[[a-zA-Z_][a-zA-Z0-9_]*\]\s*:"

highlight default link laurelstKeyword Keyword
highlight default link laurelstType Type
highlight default link laurelstConstant Constant
highlight default link laurelstOperator Operator
highlight default link laurelstWordOp Operator
highlight default link laurelstBuiltin Function
highlight default link laurelstComment Comment
highlight default link laurelstString String
highlight default link laurelstNumber Number
highlight default link laurelstAttribute PreProc
highlight default link laurelstLabel Label

let b:current_syntax = "laurelst"
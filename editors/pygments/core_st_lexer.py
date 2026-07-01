# AUTO-GENERATED Pygments lexer for Strata Core (.core.st) files.
# Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean pygments
# See editors/pygments/README.md for LaTeX minted / pygmentize usage.

from pygments.lexer import RegexLexer, words
from pygments.token import (Comment, Keyword, Name, Number, Operator,
                            Punctuation, String, Text, Whitespace)


class StrataCoreLexer(RegexLexer):
    """Lexer for Strata Core (.core.st), generated from the DDM grammar."""

    name = 'Strata Core'
    aliases = ['core-st', 'corest']
    filenames = ['*.core.st']

    tokens = {
        'root': [
            (r'\s+', Whitespace),
            (r'//.*$', Comment.Single),
            (r'"(\\.|[^"\\])*"', String.Double),
            (r'@\[[^\]]*\]', Name.Decorator),
            (r'\[[A-Za-z_][A-Za-z0-9_]*\]\s*:', Name.Label),
            (r'Sequence\.contains|Bv\.UNegOverflow|Sequence\.length|Sequence\.select|Sequence\.append|Sequence\.update|Bv\.UMulOverflow|Bv\.SNegOverflow|Bv\.SMulOverflow|Bv\.SAddOverflow|Bv\.SSubOverflow|Bv\.UAddOverflow|Bv\.SDivOverflow|Bv\.USubOverflow|Sequence\.empty|Sequence\.build|Sequence\.take|Sequence\.drop|str\.prefixof|str\.suffixof|re\.allchar|str\.concat|str\.substr|re\.concat|str\.in\.re|str\.to\.re|re\.range|re\.union|Int\.DivT|Int\.ModT|re\.inter|re\.none|re\.loop|str\.len|re\.comp|re\.all|re\.\+|re\.\*', Name.Builtin),
            (words((
                'var', 'assume', 'assert', 'cover', 'if', 'else',
                'havoc', 'invariant', 'decreases', 'while', 'out', 'inout',
                'call', 'exit', 'free', 'ensures', 'requires', 'spec',
                'procedure', 'type', 'const', 'function', 'inline', 'rec',
                'axiom', 'distinct', 'datatype', 'old', 'forall', 'exists',
                'program',
            ), suffix=r'\b'), Keyword),
            (words((
                'bool', 'int', 'string', 'regex', 'real', 'bv1',
                'bv8', 'bv16', 'bv32', 'bv64', 'bv128', 'Map',
                'Sequence',
            ), suffix=r'\b'), Keyword.Type),
            (words((
                'true', 'false', 'null',
            ), suffix=r'\b'), Keyword.Constant),
            (words((
                'div', 'mod', 'sdiv', 'smod', 'safesdiv', 'safesmod',
            ), suffix=r'\b'), Operator.Word),
            (r'safe_neg|safe-|safe\+|safe\*|<==>|>=s|==>|>>s|<=s|:=|\|\||>=|/t|%t|<<|>>|&&|<s|==|!=|<=|>s|<|\^|\+|\*|!|/|%|>|-|~|&|\|', Operator),
            (r'[0-9]+(\.[0-9]+)?', Number),
            (r'[A-Za-z_][A-Za-z0-9_]*', Name),
            (r'[()\[\]{};,.:]', Punctuation),
            (r'.', Text),
        ],
    }


# minted resolves the class name `CustomLexer` when none is given after the
# lexer path; alias it so both spellings work.
CustomLexer = StrataCoreLexer

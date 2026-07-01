# AUTO-GENERATED Pygments lexer for Strata Laurel (.laurel.st) files.
# Do not edit by hand; run: lake env lean --run editors/GenSyntax.lean pygments
# See editors/pygments/README.md for LaTeX minted / pygmentize usage.

from pygments.lexer import RegexLexer, words
from pygments.token import (Comment, Keyword, Name, Number, Operator,
                            Punctuation, String, Text, Whitespace)


class StrataLaurelLexer(RegexLexer):
    """Lexer for Strata Laurel (.laurel.st), generated from the DDM grammar."""

    name = 'Strata Laurel'
    aliases = ['laurel-st', 'laurelst']
    filenames = ['*.laurel.st']

    tokens = {
        'root': [
            (r'\s+', Whitespace),
            (r'//.*$', Comment.Single),
            (r'"(\\.|[^"\\])*"', String.Double),
            (r'@\[[^\]]*\]', Name.Decorator),
            (r'\[[A-Za-z_][A-Za-z0-9_]*\]\s*:', Name.Label),
            (words((
                'var', 'new', 'assign', 'forall', 'exists', 'summary',
                'else', 'if', 'then', 'assert', 'assume', 'return',
                'exit', 'invariant', 'while', 'for', 'is', 'as',
                'extends', 'datatype', 'invokeOn', 'requires', 'ensures', 'modifies',
                'returns', 'opaque', 'external', 'procedure', 'function', 'composite',
                'constrained', 'where', 'witness',
            ), suffix=r'\b'), Keyword),
            (words((
                'int', 'bool', 'real', 'float64', 'string', 'bv',
                'Core', 'Map',
            ), suffix=r'\b'), Keyword.Type),
            (words((
                'true', 'false',
            ), suffix=r'\b'), Keyword.Constant),
            (r'==>|!=|\|\||<=|==|>=|&&|\+\+|:=|=>|<|=|>|\+|&|\||-|\*|/|%|!|#', Operator),
            (r'[0-9]+(\.[0-9]+)?', Number),
            (r'[A-Za-z_][A-Za-z0-9_]*', Name),
            (r'[()\[\]{};,.:]', Punctuation),
            (r'.', Text),
        ],
    }


# minted resolves the class name `CustomLexer` when none is given after the
# lexer path; alias it so both spellings work.
CustomLexer = StrataLaurelLexer

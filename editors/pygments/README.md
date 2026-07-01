# Strata Syntax Highlighting for Pygments (LaTeX minted, pygmentize)

Pygments lexers for Strata dialect files, auto-generated from each dialect's
DDM grammar:

- **Strata Core** — `core_st_lexer.py` (class `StrataCoreLexer`, `.core.st`)
- **Strata Laurel** — `laurel_st_lexer.py` (class `StrataLaurelLexer`, `.laurel.st`)

Each file also exports the alias `CustomLexer`, which is the class name minted
looks for when none is specified.

## LaTeX (minted v3, TeX Live 2025+)

minted v3 loads a custom lexer directly from a `.py` file — pass the file path
where a lexer name would go:

```latex
\usepackage{minted}

\begin{minted}{path/to/core_st_lexer.py}
procedure Double(x : int) returns (r : int) { r := (x + x); };
\end{minted}

\inputminted{path/to/core_st_lexer.py}{Examples/TwoLoops.core.st}
```

(`path/to/core_st_lexer.py:StrataCoreLexer` also works; without the `:Class`
suffix minted uses the `CustomLexer` alias.)

Two things must be in place:

1. **Shell escape** — compile with `-shell-escape` (as for any minted use).
2. **Lexer allow-list** — minted v3 refuses to `exec` arbitrary Python unless
   the lexer file's SHA-256 hash is registered in a `.latexminted_config`
   file in your home directory (or `$XDG_CONFIG_HOME/latexminted/`):

   ```bash
   shasum -a 256 core_st_lexer.py   # sha256sum on Linux
   ```

   ```json
   // ~/.latexminted_config
   {
     "custom_lexers": {
       "core_st_lexer.py": "<sha-256 hex of core_st_lexer.py>",
       "laurel_st_lexer.py": "<sha-256 hex of laurel_st_lexer.py>"
     }
   }
   ```

   The lexer path is resolved relative to the TeX working directory, so keep
   the `.py` file inside your document tree (or copy it next to the `.tex`).
   **Regenerating a lexer changes its hash** — update the config when you
   rerun the generator.

For minted v2 (older TeX distributions), the equivalent invocation is
`\begin{minted}{path/to/core_st_lexer.py:StrataCoreLexer -x}` — v2 passes the
option through to `pygmentize` and has no hash allow-list.

## Command line (pygmentize)

No config needed; `-x` enables loading a lexer from a file:

```bash
pygmentize -l editors/pygments/core_st_lexer.py -x Examples/TwoLoops.core.st
pygmentize -l editors/pygments/laurel_st_lexer.py -x -f html -O full,style=default in.laurel.st
```

## How it's generated

Auto-generated from each dialect's DDM grammar — do not edit by hand:

```bash
lake env lean --run editors/GenSyntax.lean pygments   # or `all` for every editor
```

Keywords, types, constants, and operators come from the dialect grammar;
comments, strings, numbers, labels, and attributes are hardcoded (they come
from the DDM parser, not the dialect grammar). See
[`../GenSyntax.lean`](../GenSyntax.lean) for the extraction details and how to
add another dialect.

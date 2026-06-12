# Strata tree-sitter Grammars

Structural [tree-sitter](https://tree-sitter.github.io/) grammars for Strata
dialect files, for use with Neovim (`nvim-treesitter`) and any other
tree-sitter host. Unlike the regex-based [Vim syntax](../vim) and TextMate
grammars, these parse the full structure of a file (procedures, expressions,
operator precedence, …).

- **Strata Core** — `core-st/` (language `core_st`, `.core.st`)
- **Strata Laurel** — `laurel-st/` (language `laurel_st`, `.laurel.st`)

Each subdirectory contains:

| File | Purpose | Committed? |
|------|---------|-----------|
| `grammar.js` | The grammar, generated from the dialect's DDM `SyntaxDef`. | yes |
| `conflicts.json` | Auto-discovered LR conflict set that `grammar.js` reads. | yes |
| `resolve-conflicts.cjs` | Pure-node script that (re)discovers `conflicts.json`. | yes |
| `queries/highlights.scm` | Highlight queries. | yes |
| `src/`, `build/`, … | `tree-sitter generate` build output. | no (gitignored) |

## How it's generated

The grammars are **auto-generated** from each dialect's DDM grammar. Do not edit
`grammar.js` by hand — regenerate with:

```bash
lake env lean --run editors/GenSyntax.lean treesitter   # or `all` for every editor
```

The generator walks every op/fn `SyntaxDef`: syntax categories become hidden
union rules, literal atoms become tokens, and operator precedence/associativity
is recovered from the resolved operand precedences (so e.g. `+` is left- and
`==>` is right-associative). If the `tree-sitter` CLI is on your `PATH`, the
generator also runs `resolve-conflicts.cjs` automatically and writes
`conflicts.json`.

### LR conflicts

tree-sitter is a GLR parser and rejects unresolved LR conflicts at generation
time. Strata's grammars are precedence-climbing (DDM resolves ambiguity with
numeric precedences), which produces a handful of genuine conflicts —
e.g. `var x := e` (declaration-with-initializer vs. assignment of `var x`), or
the open-paren of a call against bracketed constructs.

`resolve-conflicts.cjs` discovers these mechanically: it runs `tree-sitter
generate`, scrapes the conflicting rule names from the error, adds them to the
conflict set, and repeats until generation succeeds. The result is committed as
`conflicts.json`, which `grammar.js` loads into its `conflicts:` field. To
re-derive it after editing a grammar by hand:

```bash
cd editors/treesitter/<dialect>
node resolve-conflicts.cjs        # needs the tree-sitter CLI on PATH
```

## Building & testing

```bash
cd editors/treesitter/laurel-st
tree-sitter generate              # compiles grammar.js -> src/parser.c
tree-sitter parse path/to/file.laurel.st
```

## Neovim integration (nvim-treesitter)

These grammars aren't in the nvim-treesitter registry; register them as local
parsers. Add to your config, then run `:TSInstallFromGrammar laurel_st core_st`:

```lua
local parsers = require("nvim-treesitter.parsers").get_parser_configs()
parsers.laurel_st = {
  install_info = {
    url = "/path/to/Strata/editors/treesitter/laurel-st",
    files = { "src/parser.c" },
    generate_requires_npm = false,
    requires_generate_from_grammar = true,   -- runs tree-sitter generate first
  },
  filetype = "laurelst",
}
parsers.core_st = {
  install_info = {
    url = "/path/to/Strata/editors/treesitter/core-st",
    files = { "src/parser.c" },
    requires_generate_from_grammar = true,
  },
  filetype = "corest",
}
```

Map the file extensions to those filetypes (e.g. via the
[`../vim/ftdetect`](../vim/ftdetect) files, or `vim.filetype.add`), and copy
`queries/highlights.scm` to `queries/<lang>/highlights.scm` on your runtime path.

## Coverage notes

- **Laurel** is fully structural: the entire `.laurel.st` surface syntax lives in
  the Laurel DDM grammar, so the generated parser covers it faithfully (the
  example `.laurel.st` files parse with zero errors).
- **Core** is partly approximate: some of Core's expression and procedure-spec
  syntax (e.g. `modifies` clauses) is provided by the builtin DDM parser rather
  than declared in the `Core` dialect, so it isn't visible to the generator. The
  generated grammar covers the declared surface; constructs outside it fall back
  to tree-sitter's error recovery (the rest of the file still highlights).

## Adding support for another Strata dialect

Add the dialect's import and a `GenTarget` entry to `targets` in
`editors/GenSyntax.lean` (a `scope`, `display` name, and double `ext`), then
rerun the generator. A `treesitter/<scope>/` directory is produced
automatically.

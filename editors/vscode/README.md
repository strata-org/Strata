# Strata Syntax Highlighting for VSCode

Syntax highlighting for Strata dialect files:

- **Strata Core** — `.core.st`
- **Strata Laurel** — `.laurel.st`

## Installation

Symlink this directory into your VSCode extensions folder:

```bash
ln -s /path/to/Strata/editors/vscode ~/.vscode/extensions/strata-st
```

Then reload VSCode via the Command Palette: **Developer: Reload Window**.

All `.core.st` and `.laurel.st` files will now have syntax highlighting, bracket
matching, auto-closing pairs, and comment toggling.

## How it's generated

The TextMate grammars in `syntaxes/` are **auto-generated** from each dialect's
DDM grammar. Do not edit them by hand — regenerate with:

```bash
lake env lean --run editors/GenSyntax.lean vscode   # or `all` for every editor
```

`editors/GenSyntax.lean` reads each dialect's `SyntaxDef` data and extracts
types, keywords, operators, constants, and built-in function names. Static
patterns (comments, strings, labels, attributes, identifiers, numbers) are
hardcoded since they come from the DDM parser, not the dialect grammar.

## Adding support for another Strata dialect

1. Add the dialect's import and a `GenTarget` entry to `targets` in
   `editors/GenSyntax.lean` (a `scope`, `display` name, and double `ext`), then
   rerun the generator.
2. Add `"languages"` and `"grammars"` entries to `package.json` for the new
   `source.<scope>` / `<ext>` pair (see the existing `core-st` / `laurel-st`
   entries).

## Uninstall

```bash
rm ~/.vscode/extensions/strata-st
```

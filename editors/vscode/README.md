# Strata Syntax Highlighting for VSCode

Syntax highlighting for Strata Core (`.core.st`) files.

## Installation

Symlink this directory into your VSCode extensions folder:

```bash
ln -s /path/to/Strata/editors/vscode ~/.vscode/extensions/strata-st
```

Then reload VSCode via the Command Palette: **Developer: Reload Window**.

All `.core.st` files will now have syntax highlighting, bracket matching, auto-closing pairs, and comment toggling.

## Adding support for other Strata dialects

Strata has other dialect extensions (e.g., `.laurel.st`). To add highlighting for another dialect:

1. Add a new entry to the `"languages"` array in `package.json` with the appropriate extension.
2. Create a new TextMate grammar in `syntaxes/` if the dialect has different syntax, or reuse `core-st.tmLanguage.json` if it shares the same grammar.
3. Wire the language to its grammar in the `"grammars"` array in `package.json`.

## Uninstall

```bash
rm ~/.vscode/extensions/strata-st
```

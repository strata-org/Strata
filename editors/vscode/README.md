# Strata Syntax Highlighting for VSCode

Syntax highlighting for Strata Core (`.core.st`) and Strata CoreMatch
(`.coreMatch.st`) files.

## Installation

Symlink this directory into your VSCode extensions folder:

```bash
ln -s /path/to/Strata/editors/vscode ~/.vscode/extensions/strata-st
```

Then reload VSCode via the Command Palette: **Developer: Reload Window**.

`.core.st` files use `core-st`; `.coreMatch.st` use `coreMatch-st`,
which adds the `match` and `arm` keywords on top of Core.

## Adding support for other Strata dialects

Grammar files in `syntaxes/` are auto-generated.  Regenerate from the
repository root:

```bash
lake env lean --run editors/GenSyntax.lean all
```

To add a new dialect: add a `DialectGenSpec` in `editors/GenSyntax.lean`
(list any imported dialects in `dialects` so inherited ops show up),
re-run the generator, then add `languages` and `grammars` entries in
`package.json` pointing at the new `syntaxes/<langId>.tmLanguage.json`.

## Uninstall

```bash
rm ~/.vscode/extensions/strata-st
```

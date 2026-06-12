# Strata Syntax Highlighting for Emacs

Major modes for Strata dialect files, providing syntax highlighting, comment
support, and bracket matching:

- **`core-st-mode`** — Strata Core (`.core.st`)
- **`laurel-st-mode`** — Strata Laurel (`.laurel.st`)

## Installation

Add the following to your Emacs config (e.g., `~/.emacs.d/init.el`):

```elisp
(load-file "/path/to/Strata/editors/emacs/core-st-mode.el")
(load-file "/path/to/Strata/editors/emacs/laurel-st-mode.el")
```

`.core.st` files open in `core-st-mode` and `.laurel.st` files in
`laurel-st-mode` automatically.

Alternatively, if the directory is on your `load-path`:

```elisp
(require 'core-st-mode)
(require 'laurel-st-mode)
```

## How it's generated

These major modes are **auto-generated** from each dialect's DDM grammar. Do not
edit them by hand — regenerate with:

```bash
lake env lean --run editors/GenSyntax.lean emacs   # or `all` for every editor
```

## Adding support for another Strata dialect

Add the dialect's import and a `GenTarget` entry to `targets` in
`editors/GenSyntax.lean` (a `scope`, `display` name, and double `ext`), then
rerun the generator. A `<scope>-mode.el` file is produced automatically.

## Uninstall

Remove the `load-file`/`require` lines from your Emacs config.

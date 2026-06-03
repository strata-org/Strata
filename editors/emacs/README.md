# Strata Syntax Highlighting for Emacs

Major modes for Strata Core (`.core.st`) and Strata CoreMatch
(`.coreMatch.st`) files, providing syntax highlighting, comment
support, and bracket matching.

## Installation

Add the following to your Emacs config (e.g., `~/.emacs.d/init.el`):

```elisp
(load-file "/path/to/Strata/editors/emacs/core-st-mode.el")
(load-file "/path/to/Strata/editors/emacs/coreMatch-st-mode.el")
```

`.core.st` files open in `core-st-mode`; `.coreMatch.st` open in
`coreMatch-st-mode`, which adds the `match` and `arm` keywords on top
of Core.

Alternatively, if the directory is on your `load-path`:

```elisp
(require 'core-st-mode)
(require 'coreMatch-st-mode)
```

## Regenerating after a grammar change

```bash
lake env lean --run editors/GenSyntax.lean all
```

## Adding support for other Strata dialects

Add a `DialectGenSpec` in `editors/GenSyntax.lean` referencing the new
dialect (list any imported dialects in `dialects` so inherited ops show
up), then re-run the generator.

## Uninstall

Remove the line(s) from your Emacs config.

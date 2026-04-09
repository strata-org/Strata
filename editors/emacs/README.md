# Strata Syntax Highlighting for Emacs

Major mode for Strata Core (`.core.st`) files, providing syntax highlighting, comment support, and bracket matching.

## Installation

Add the following to your Emacs config (e.g., `~/.emacs.d/init.el`):

```elisp
(load-file "/path/to/Strata/editors/emacs/core-st-mode.el")
```

All `.core.st` files will now open in `core-st-mode` automatically.

Alternatively, if the directory is on your `load-path`:

```elisp
(require 'core-st-mode)
```

## Adding support for other Strata dialects

Strata has other dialect extensions (e.g., `.laurel.st`). To add highlighting for another dialect, copy `core-st-mode.el` as a starting point, adjust the keyword lists and `auto-mode-alist` entry for the new extension, and load it the same way.

## Uninstall

Remove the line from your Emacs config.

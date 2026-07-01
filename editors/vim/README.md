# Strata Syntax Highlighting for Vim / Neovim

Regex-based syntax highlighting for Strata dialect files. Works in both Vim and
Neovim with no compilation step.

- **Strata Core** — `.core.st` (filetype `corest`)
- **Strata Laurel** — `.laurel.st` (filetype `laurelst`)

> For richer, structural highlighting in Neovim, see the tree-sitter grammars in
> [`../treesitter`](../treesitter) instead. This regex syntax is the
> lightweight, zero-build option and the only option for classic Vim.

## Installation

This directory lives **inside the Strata repository** — it is not a standalone
plugin repo, so plugin managers can't fetch it from a URL. Every option below
points your editor at the `editors/vim` subdirectory of your local Strata
checkout (**not** the repo root). The examples use `~/code/Strata/editors/vim`;
substitute wherever you cloned Strata.

Because the plugin is loaded from a local path, your plugin manager won't
install or update it — it always tracks the checkout, and updates arrive via
`git pull` in the Strata repo.

### Runtimepath (simplest)

Add the directory to your runtimepath. Neovim (`init.lua`):

```lua
vim.opt.runtimepath:append(vim.fn.expand("~/code/Strata/editors/vim"))
```

Vim (`.vimrc`), also works in Neovim's `init.vim`:

```vim
set runtimepath+=~/code/Strata/editors/vim
```

### Plugin manager

With [lazy.nvim](https://github.com/folke/lazy.nvim), use `dir =` to load from
a local path:

```lua
{ dir = "~/code/Strata/editors/vim" }
```

With [vim-plug](https://github.com/junegunn/vim-plug), pass the local path
instead of a URL:

```vim
Plug '~/code/Strata/editors/vim'
```

### Manual

Symlink the `syntax/` and `ftdetect/` files into your runtime directory:

```bash
# Neovim
ln -s ~/code/Strata/editors/vim/syntax/*.vim    ~/.config/nvim/syntax/
ln -s ~/code/Strata/editors/vim/ftdetect/*.vim  ~/.config/nvim/ftdetect/

# Vim
ln -s ~/code/Strata/editors/vim/syntax/*.vim    ~/.vim/syntax/
ln -s ~/code/Strata/editors/vim/ftdetect/*.vim  ~/.vim/ftdetect/
```

With any of these options, open a `.core.st` or `.laurel.st` file and
highlighting applies automatically.

## How it's generated

The `syntax/*.vim` and `ftdetect/*.vim` files are **auto-generated** from each
dialect's DDM grammar. Do not edit them by hand — regenerate with:

```bash
lake env lean --run editors/GenSyntax.lean vim   # or `all` for every editor
```

Keywords, types, constants, and operators come from the dialect grammar;
comments, strings, numbers, labels, and attributes are hardcoded (they come from
the DDM parser, not the dialect grammar).

## Adding support for another Strata dialect

Add the dialect's import and a `GenTarget` entry to `targets` in
`editors/GenSyntax.lean` (a `scope`, `display` name, and double `ext`), then
rerun the generator. `syntax/<filetype>.vim` (the scope with dashes removed —
Vim sources the syntax file named after the filetype) and
`ftdetect/<scope>.vim` are produced automatically.

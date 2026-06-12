# Strata Syntax Highlighting for Vim / Neovim

Regex-based syntax highlighting for Strata dialect files. Works in both Vim and
Neovim with no compilation step.

- **Strata Core** — `.core.st` (filetype `corest`)
- **Strata Laurel** — `.laurel.st` (filetype `laurelst`)

> For richer, structural highlighting in Neovim, see the tree-sitter grammars in
> [`../treesitter`](../treesitter) instead. This regex syntax is the
> lightweight, zero-build option and the only option for classic Vim.

## Installation

### Plugin manager (recommended)

Point your plugin manager at this directory. For example, with
[lazy.nvim](https://github.com/folke/lazy.nvim):

```lua
{ dir = "/path/to/Strata/editors/vim" }
```

Or with [vim-plug](https://github.com/junegunn/vim-plug):

```vim
Plug '/path/to/Strata/editors/vim'
```

### Manual

Symlink the `syntax/` and `ftdetect/` files into your runtime directory:

```bash
# Neovim
ln -s /path/to/Strata/editors/vim/syntax/*.vim    ~/.config/nvim/syntax/
ln -s /path/to/Strata/editors/vim/ftdetect/*.vim  ~/.config/nvim/ftdetect/

# Vim
ln -s /path/to/Strata/editors/vim/syntax/*.vim    ~/.vim/syntax/
ln -s /path/to/Strata/editors/vim/ftdetect/*.vim  ~/.vim/ftdetect/
```

Open any `.core.st` or `.laurel.st` file and highlighting applies automatically.

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
rerun the generator. `syntax/<scope>.vim` and `ftdetect/<scope>.vim` are produced
automatically.

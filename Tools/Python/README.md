# Strata Python Bindings

This directory contains a Python package for strata along with a module
`strata.gen` for generating Strata dialects and programs from Python.

It can be installed by running `pip install .` from this directory.

For full documentation, see:

- The [DDM Manual](https://strata-org.github.io/Strata/ddm/html-single/)
  — covers DDM concepts and the `strata.base` Python API for working
  with dialects, programs, and AST types.
- [PythonDialect.md](PythonDialect.md) — covers the auto-generated Python
  dialect, CLI commands, the `strata.pythonast` parser API, and Python
  version compatibility.

## Quick Start

The Python dialect may only be generated in CPython 3.13 or later.  The
Strata toolchain assumes the dialect is generated in 3.14.  Parsing may
be done in 3.12+ by pre-generating the dialect in 3.14.

Generate the dialect and parse a Python file:

```
python -m strata.gen dialect dialects
python -m strata.gen py_to_strata --dialect dialects/Python.dialect.st.ion \
   input.py output.py.st.ion
```

See [PythonDialect.md](PythonDialect.md) for full CLI reference and API
documentation.
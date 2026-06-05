# strata-python

Python language support for Strata: the `strata_python.gen` CLI and the
`strata_python.pythonast` parser API. Translates Python source files to
Strata Ion programs for downstream analysis.

## Installation

This package depends on `strata` (the core DDM datatypes). Install both:

```
pip install <path-to-strata-base> <path-to-strata-python>
```

## Quick Start

The Python dialect may only be generated in CPython 3.13 or later. The
Strata toolchain assumes the dialect is generated in 3.14. Parsing may
be done in 3.11+ by pre-generating the dialect in 3.14.

Generate the dialect and parse a Python file:

```
python -m strata_python.gen dialect dialects
python -m strata_python.gen py_to_strata --dialect dialects/Python.dialect.st.ion \
   input.py output.py.st.ion
```

## Documentation

- [PythonDialect.md](PythonDialect.md) — auto-generated Python dialect,
  CLI commands, the `strata_python.pythonast` parser API, and Python
  version compatibility.
- The [DDM Manual](https://strata-org.github.io/Strata/ddm/html-single/)
  — DDM concepts and the `strata.base` Python API for working with
  dialects, programs, and AST types.

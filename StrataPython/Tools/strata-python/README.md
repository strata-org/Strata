# Strata Python Libraries

This directory contains two Python packages:

- **`strata-base/`** — Core Strata DDM datatypes and Ion serialization
  (`strata.base` module). Language-agnostic; provides `Dialect`, `Program`,
  `Operation`, and the `Init` built-in dialect.

- **`strata-python/`** — Python language support (`strata_python.gen` CLI and
  `strata_python.pythonast` parser). Depends on `strata-base`.

Install both:

```
pip install ./strata-base ./strata-python
```

For full documentation, see:

- The [DDM Manual](https://strata-org.github.io/Strata/ddm/html-single/)
  — covers DDM concepts and the `strata.base` Python API for working
  with dialects, programs, and AST types.
- [PythonDialect.md](PythonDialect.md) — covers the auto-generated Python
  dialect, CLI commands, the `strata_python.pythonast` parser API, and Python
  version compatibility.

## Quick Start

The Python dialect may only be generated in CPython 3.13 or later.  The
Strata toolchain assumes the dialect is generated in 3.14.  Parsing may
be done in 3.12+ by pre-generating the dialect in 3.14.

Generate the dialect and parse a Python file:

```
python -m strata_python.gen dialect dialects
python -m strata_python.gen py_to_strata --dialect dialects/Python.dialect.st.ion \
   input.py output.py.st.ion
```

See [PythonDialect.md](PythonDialect.md) for full CLI reference and API
documentation.

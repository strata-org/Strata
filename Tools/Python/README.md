# Strata Python Bindings

This directory contains a Python package for strata along with a module
`strata.gen` for generating Strata dialects and programs from Python.

It can be installed by running `pip install .` from this directory.

## Python versions

The Python dialect may only be generated in CPython 3.13 or later, and
may differ depending on which version of CPython is used.  The Strata
toolchain currently assumes the dialect is generated in 3.14, and so
we recommend using that version.

Python parsing may be done in 3.12 by pre-generating the dialect in 3.14.  See the documentation on the `py_to_strata` command below for more details.

## Generating the DDM dialect.

The `dialect` command can generate either Python dialect.  Strata dialect by
analyzing the Python AST package implementation.  This dialect is generated
automatically and thus may
change between Python versions if the AST package implementation changes.

Strata dialect should be placed into a directory so that it can be read along
with other dialects.  To generate the dialect in the directory `dialect_dir`,
run the following command:

```
python -m strata.gen dialect *dir*
```

`*dir*` should point to the directory to store the dialect in.

The dialect can be checked with using the Strata CLI tools:

```
strata check "*dir*/Python.dialect.st.ion"
```

## Parsing Python into Strata.

The `py_to_strata` subcommand will translate a Python file into a Strata file.

Parsing into Strata requires the Strata Python dialect.  To ensure consistency, this is ideally passed in as a file using the `--dialect` flag, but can be
generated automatically in Python 3.13 or later.

The `py_to_strata` command takes in two required arguments `input.py` and `output.py.st.ion` and one optional flag parameter.

 * `input.py` should be the name of the input Python file to parse.
 * `output.py.st.ion` is the name of the output file to write the Strata to.
 * The `--dialect path` command takes the path to the Python dialect.

As an example, we should using strata.gen to translate `strata/base.py` into Strata below:

```
python -m strata.gen py_to_strata --dialect dialects/Python.dialect.st.ion \
   strata/base.py base.py.st.ion
```

This can be checked using the Strata CLI tools:

```
strata check --include dialects base.py.st.ion
```
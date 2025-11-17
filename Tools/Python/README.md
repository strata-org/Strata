# Strata Python Bindings

This directory contains a Python package for strata along with a module
`strata.gen` for generating Strata dialects and programs from Python.

It can be installed by running `pip install .` from the root directory.

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

As an example, we should using strata.gen to translate `strata/base.py` into Strata below:

```
python -m strata.gen py_to_strata strata/base.py base.py.st.ion
```

This can be checked using the Strata CLI tools:

```
strata check --include dialect_dir base.py.st.ion
```
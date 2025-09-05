# Strata Python Bindings

This directory contains a Python package for strata along with a directory
for generating a Python Strata DDM dialect and generating Strata programs.

It can be installed by running `pip install .` from the root directory.

## Generating the DDM dialect.

The `dialect` command can generate a Strata dialect by analyzing the Python AST
package implementation.  This dialect is generated automatically, but may
change between Python versions if the AST package implementation changes.

Strata dialect should be placed into a directory so that it can be read along
with other dialects.  To generate the dialect in the directory `dialect_dir`,
run the following command:

```
python -m strata.gen dialect dialect_dir
```

The dialect can be worked with using the Strata CLI tools:

```
strata check "dialect_dir/Python.dialect.st.ion"
```

## Parsing Python into Strata.

The `parse` subcommand will translate a Python file into a Strata file.

As an example, we should using strata.gen to translate `strata/base.py` into Strata below:

```
python -m strata.gen parse strata/base.py base.python.st.ion
```

This can be checked using the Strata CLI tools:

```
strata check --include dialect_dir sample.python.st.ion
```
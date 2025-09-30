# Strata Python Bindings

This directory contains a Python package for strata along with a module
`strata.gen` for generating Strata dialects and programs from Python in
one of two dialects.  The first dialect, `PythonAST` represents Python
programs using an AST-based representation while `PythonSSA` represents
programs using a SSA-based representation derived from CPython's VM
instruction set.

It can be installed by running `pip install .` from the root directory.

## Generating the DDM dialects.

The `dialect` command can generate either Python dialect.   Strata dialect by analyzing the Python AST
package implementation.  This dialect is generated automatically and thus may
change between Python versions if the AST package implementation changes.

Strata dialect should be placed into a directory so that it can be read along
with other dialects.  To generate the dialect in the directory `dialect_dir`,
run the following command:

```
python -m strata.gen dialect *dialect* *dir*
```

In this case, `*dialect*` should be either `PythonAST` or
`PythonSSA` while `*dir*` should point to the directory
to store the dialect in.

The dialect can be worked with using the Strata CLI tools:

```
strata check "*dir*/PythonAST.dialect.st.ion"
strata check "*dir*/PythonSSA.dialect.st.ion"
```

## Parsing Python into Strata.

The `py_to_strata` subcommand will translate a Python file into a Strata file.

As an example, we should using strata.gen to translate `strata/base.py` into Strata below:

```
python -m strata.gen py_to_strata PythonAST strata/base.py base.pyast.st.ion
```

This can be checked using the Strata CLI tools:

```
strata check --include dialect_dir bast.pyast.st.ion
```
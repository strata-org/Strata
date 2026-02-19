# Usage

## Generate Dialect file:
```
cd Tools/Python
python -m strata.gen dialect dialects
```

## Generate Ion files per source program:

```
cd Tools/Python
python -m strata.gen py_to_strata \
   --dialect dialects/Python.dialect.st.ion \
   ../../StrataTest/Languages/Python/test.py \
   ../../StrataTest/Languages/Python/test.python.st.ion
```

## Run analysis:

```
lake exe strata pyAnalyze StrataTest/Languages/Python/test.python.st.ion
```

Use `--verbose` for verbose output:

```
lake exe strata pyAnalyze --verbose StrataTest/Languages/Python/test.python.st.ion
```

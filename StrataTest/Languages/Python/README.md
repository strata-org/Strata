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

This will run pyAnalyze with verbosity off:

```
lake exe strata pyAnalyze StrataTest/Languages/Python/test.python.st.ion 0
```

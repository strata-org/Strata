# Usage

## Generate Dialect file:
```
cd Tools/Python
python -m strata.gen dialect test_results/dialects
```

## Generate Ion files per source program:
```
cd Tools/Python
python -m strata.gen parse ../../StrataTest/Languages/Python/test.py ../../StrataTest/Languages/Python/test.python.st.ion
```

## Run analysis:
```
lake exe strata pyAnalyze --include Tools/Python/test_results/dialects StrataTest/Languages/Python/test.python.st.ion
```
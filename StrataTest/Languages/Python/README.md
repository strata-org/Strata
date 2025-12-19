# Usage

## Generate Dialect file:
```
cd Tools/Python
python -m strata.gen dialect test_results/dialects
```

## Generate Ion files per source program:
```
cd Tools/Python
python -m strata.gen py_to_strata ../../StrataTest/Languages/Python/test.py ../../StrataTest/Languages/Python/test.python.st.ion
```

## Run analysis:
```
lake exe strata pyAnalyze --include Tools/Python/test_results/dialects StrataTest/Languages/Python/test.python.st.ion
```

## Run analysis with flags:
```
# Verbose output
lake exe strata pyAnalyze --include Tools/Python/test_results/dialects --verbose StrataTest/Languages/Python/test.python.st.ion

# Disable inlining (inlining is enabled by default)
lake exe strata pyAnalyze --include Tools/Python/test_results/dialects --noinline StrataTest/Languages/Python/test.python.st.ion

# Both flags (can appear in any order)
lake exe strata pyAnalyze --include Tools/Python/test_results/dialects --verbose --noinline StrataTest/Languages/Python/test.python.st.ion
```

Note: Inlining is enabled by default. Use `--noinline` to disable it.

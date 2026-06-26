# EndToEndTests

The folder EndToEndTests contains tests that operate from the user perspective. They take as input a user program and a method of executing Strata on this program, and expect a certain output from Strata.

Usually the expected output is specified through inline comments that follow a specific format so they're recognized as expected output.

Every feature in Laurel should be tested through the EndToEndTests folder.

## Debugging

If an E2E test fails, the likely cause is one of Laurel's lowering passes. We can figure out which of the passes is to blame by using the Laurel semantics. If the output of running the Laurel's type checker or interpreter changes between passes, then this pass is to blame. Another method of investigation is to manually inspect the Laurel program between each pass to see where it changes its meaning.

# Idiomaticity

Idiomaticity tests enable manually reviewing the quality of the encoding of a particular pass. Such a test is always made for a particular pass, named <pass>Test, and compares code right before and right after the pass runs. Note that many passes only take a subset of Laurel code, so idiomaticity must take this into account when specifying the input program.

Having an idiomaticity test per pass is recommend but not required.

# UnitTests

The folder UnitTests contains tests that require calling internal Laurel APIs. Adding unit tests is recommend for utility functions such as the generic Laurel traversal code that's in MapStmtExprTest.
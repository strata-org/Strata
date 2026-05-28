# StrataTest

This directory contains compile-time tests (`#guard_msgs`) for Strata's
dialects, transforms, and DDM machinery. Tests run as part of `lake build`;
no output means they passed.

For how to write a new test — including the `#strata` / `#strata`
blocks and the Laurel test helpers — see
[`docs/Testing.md`](../docs/Testing.md).

For the runtime test driver (uncached extra tests under `StrataTestExtra/`),
see the "Running specific test subsets" section of the top-level
[`README.md`](../README.md).

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM
public import Strata.Languages.Core.Core
public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Python.Python

/-! ## Simple Strata API

A simple API for reading, writing, transforming, and analyzing Strata programs.

This module is a thin wrapper that re-exports the contents of the more focused
API modules:

* `Strata.DDM` – file I/O for the generic Strata representation.
* `Strata.Languages.Core.Core` – Core dialect translation, transforms, and verification.
* `Strata.Languages.Laurel.Laurel` – Laurel parsing, translation, and verification.
* `Strata.Languages.Python.Python` – Python sources, PySpec generation, and Python pipelines.

It is intended for use cases that are essentially equivalent to more
fine-grained or more structured equivalents of what the `strata` CLI can
currently do.

It involves several key types:

* `Strata.Dialect`: The formal description of a Strata dialect. Used only to
  describe which dialects are available when reading or writing files.

* `Strata.Program`: The generic AST for a Strata program in any dialect.
   Generally used just as an interim representation before serializing or after
   deserializing a program. Before using a `Strata.Program`, it will usually
   make sense to translate it into the custom AST for a specific dialect.

* `Laurel.Program`: A dialect-specific AST for a program in the Laurel dialect.

* `Core.Program`: A dialect-specific AST for a program in the Core dialect.

* `Core.VCResults`: The results of attempting to prove each verification condition
  that arises from deductive verification of a Core program.

**Note:** Several functions in this API are currently unimplemented due to
functionality that remains to be implemented in the DDM. These functions are
declared using `noncomputable opaque` to define the intended API surface and
should not be invoked yet.
-/

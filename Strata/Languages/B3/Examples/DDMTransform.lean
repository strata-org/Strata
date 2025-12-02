/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST

---------------------------------------------------------------------
namespace Strata
set_option maxRecDepth 10000

/-!
## B3 DDM Dialect Example

This file demonstrates the DDM dialect definition for B3.
The dialect is defined in `Strata/Languages/B3/DDMTransform/Parse.lean`
and the translation from DDM AST to B3 AST is in `Strata/Languages/B3/DDMTransform/Translate.lean`.

The DDM dialect provides:
- Parser for B3 syntax
- Pretty-printer for B3 programs
- Translation to B3 abstract syntax tree

Example usage would be with `#strata` blocks, similar to Boogie.
-/

end Strata
---------------------------------------------------------------------

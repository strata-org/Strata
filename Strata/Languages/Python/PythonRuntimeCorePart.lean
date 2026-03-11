/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

/--
Core-only prelude declarations for the Python-through-Laurel pipeline.

This contains declarations that cannot be expressed in Laurel grammar:
- Axioms
- Parameterized datatypes (`Except`)
- Type synonyms (`ExceptErrorRegex`)
- Functions using `regex` type
- Procedures using discriminator access (`..`)
- Procedures with labeled requires/ensures

Types already defined in `PythonRuntimeLaurelPart.lean` are forward-declared
here so the DDM parser can resolve references. At the Core level, the
Laurel-translated declarations take precedence and these forward declarations
are filtered out.

The original `CorePrelude.lean` remains unchanged for the Python-through-Core pipeline.
-/
private def pythonRuntimeCorePartDDM :=
#strata
program Core;

// =====================================================================
// Forward declarations of types defined in PythonRuntimeLaurelPart.
// These are needed so the DDM parser can resolve references in axioms
// and procedures below. They will be filtered out when merging with
// the Laurel-translated declarations.
// =====================================================================


type CoreOnlyDelimiter;

// =====================================================================
// Core-only declarations (not expressible in Laurel)
// =====================================================================

#end

/--
Get the Core-only prelude declarations for the Laurel pipeline.
These are declarations that cannot be expressed in Laurel grammar.
The returned program includes forward declarations of types from the
Laurel prelude; callers should filter out duplicates when merging.
-/
def pythonRuntimeCorePart : Core.Program :=
  Core.getProgram pythonRuntimeCorePartDDM |>.fst

/--
Get only the Core-only declarations, dropping the forward declarations
that precede the `type CoreOnlyDelimiter;` sentinel (and the sentinel itself).
Everything after the delimiter is a genuine Core-only declaration.
-/
def coreOnlyFromRuntimeCorePart : List Core.Decl :=
  let decls := pythonRuntimeCorePart.decls
  -- Drop everything up to and including the CoreOnlyDelimiter sentinel
  match decls.dropWhile (fun d => d.name.name != "CoreOnlyDelimiter") with
  | _ :: rest => rest   -- drop the delimiter itself
  | [] => panic! "CoreOnlyDelimiter sentinel not found in pythonRuntimeCorePart"

end Python
end Strata

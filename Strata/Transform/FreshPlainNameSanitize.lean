/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! # Sanitizing a name for a generated one

`sanitize` replaces each `#` by `_`. `#` is the delimiter of monomorphized names
(`Core.NameMangling.monoDelim`), so a name generated from a label goes through `sanitize`: a `#`
the user wrote is renamed away in the generated name rather than rejected.
Its properties are in `FreshPlainNameSanitizeProps`. -/

public section

namespace Core.FreshPlainName

/-- `n` with each `#` replaced by `_`. -/
@[expose] def sanitize (n : String) : String := n.map fun c => if c == '#' then '_' else c

end Core.FreshPlainName

end

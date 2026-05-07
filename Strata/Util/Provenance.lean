/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.FileRange

public section
namespace Strata

/-- Provenance tracks where an AST node originated from — either a real source
location or a synthesized origin (e.g., from a translator or encoding pass). -/
inductive Provenance where
  /-- A real source location with file and byte range. -/
  | loc (uri : Uri) (range : SourceRange)
  /-- A synthesized node with a description of what created it. -/
  | synthesized (origin : String)
  deriving DecidableEq, Repr, Inhabited

namespace Provenance

/-- Convert a Provenance to a FileRange, if it has a real location. -/
def toFileRange : Provenance → Option FileRange
  | .loc uri range => some { file := uri, range }
  | .synthesized _ => none

/-- Convert a FileRange to a Provenance. -/
def ofFileRange (fr : FileRange) : Provenance :=
  .loc fr.file fr.range

/-- Convert a SourceRange and Uri to a Provenance. -/
def ofSourceRange (uri : Uri) (sr : SourceRange) : Provenance :=
  .loc uri sr

instance : Std.ToFormat Provenance where
  format
    | .loc uri range => f!"{uri}:{range}"
    | .synthesized origin => f!"<synthesized:{origin}>"

end Provenance
end Strata
end

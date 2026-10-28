/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataLaurel.Implementation.CoreWithLaurelTypes
public import StrataLaurel.Implementation.LaurelNodeKind
public import Strata.Languages.Core.Program
import Strata.Languages.Core.DDMTransform.ASTtoCST
import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator

namespace Strata.Laurel

open Std (Format ToFormat)

public section

/-- A program whose top-level declarations are grouped and ordered. `WithLaurelTypes` is
    produced by the Ordering pass and `Core` by LaurelToCoreSchema. The generic walks
    (`mapProgramStmtExprM` and friends) leave a `Core` program unchanged, since it holds no
    Laurel syntax. -/
inductive OrderedProgram where
  | WithLaurelTypes (program : CoreWithLaurelTypes)
  | Core (program : _root_.Core.Program)

/-- A program as the Laurel-to-Core pipeline holds it, and the input and output of every
    `LaurelPass`. `Unordered` comes from the front end, and the Transparency pass fills its
    `staticFunctions`. `Ordered` is produced by the Ordering pass. -/
inductive Program where
  | Unordered (program : LaurelProgram)
  | Ordered (program : OrderedProgram)

instance : Inhabited Program where
  default := .Unordered default

@[expose] def Program.kind : Program → NodeKind
  | .Unordered _ => NodeKind.Program.Unordered
  | .Ordered (.WithLaurelTypes _) => NodeKind.OrderedProgram.WithLaurelTypes
  | .Ordered (.Core _) => NodeKind.OrderedProgram.Core

def Program.fileExtension : Program → String
  | .Unordered _ => "laurel.st"
  | .Ordered (.WithLaurelTypes _) => "coreWithLaurelTypes.st"
  | .Ordered (.Core _) => "core.st"

def Program.format : Program → Format
  | .Unordered p => ToFormat.format p
  | .Ordered (.WithLaurelTypes p) => ToFormat.format p
  | .Ordered (.Core p) => ToFormat.format p

instance : ToFormat Program where
  format := Program.format

end -- public section

end Strata.Laurel

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests for `translateSingleReturnType`: the implicit `$result` output parameter
must carry a usable source range whenever the producer supplied one, on either
the inner type op or the outer `returnType` op.

The Java front-end attaches a range only to the outer `Laurel.returnType` op
(the inner type op is built from a javac `Type`, which has no tree position and
serializes with the `SourceRange.none` sentinel). Before the fallback, the
implicit-postcondition diagnostics that `ConstrainedTypeElim` synthesizes for
constrained output types (e.g. the `int32` no-overflow check for a Java `int`)
were reported at the whole-file fallback position.
-/

import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator

open Strata
open StrataDDM (SourceRange)

namespace Strata.Laurel

private def uri : Strata.Uri := .file "Test.java"

private def intTypeOp (ann : SourceRange) : StrataDDM.Arg :=
  .op { ann := ann, name := q`Laurel.intType, args := #[] }

private def returnTypeOp (outer : SourceRange) (inner : SourceRange) :
    StrataDDM.Operation :=
  { ann := outer, name := q`Laurel.returnType, args := #[intTypeOp inner] }

private def sourceOf (op : StrataDDM.Operation) : IO (Option FileRange) := do
  match Laurel.TransM.run uri (translateSingleReturnType op) with
  | .error e => throw (IO.userError s!"translation failed: {e}")
  | .ok [p] => pure p.type.source
  | .ok ps => throw (IO.userError s!"expected one parameter, got {ps.length}")

-- The inner type op's own range wins when present.
/--
info: some { file := Strata.Uri.file "Test.java", range := { start := { byteIdx := 5 }, stop := { byteIdx := 8 } } }
-/
#guard_msgs in
#eval do IO.println (repr (← sourceOf (returnTypeOp { start := ⟨10⟩, stop := ⟨13⟩ } { start := ⟨5⟩, stop := ⟨8⟩ })))

-- A range only on the outer `returnType` op (the Java front-end's shape)
-- falls back to that range instead of losing the location.
/--
info: some { file := Strata.Uri.file "Test.java", range := { start := { byteIdx := 10 }, stop := { byteIdx := 13 } } }
-/
#guard_msgs in
#eval do IO.println (repr (← sourceOf (returnTypeOp { start := ⟨10⟩, stop := ⟨13⟩ } SourceRange.none)))

-- No range anywhere yields `none`, not a real-looking 0-0 location.
/-- info: none -/
#guard_msgs in
#eval do IO.println (repr (← sourceOf (returnTypeOp SourceRange.none SourceRange.none)))

end Strata.Laurel

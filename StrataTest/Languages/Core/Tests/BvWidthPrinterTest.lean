/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Languages.Core.Factory
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init

/-! # Printer coverage for bitvector widths

The Core printer has concrete syntax for the bitvector widths `{1, 8, 16, 32, 64, 128}`
(grammar markers `W1 … W128` and literal tokens `bv{w}`). The AST and type checker admit a
bitvector of any width; for a width outside that set the printer records a conversion error and
emits output that does not re-parse. (`RoundtripTest` covers that the supported widths round-trip.)
-/

open Lambda Core Strata Strata.CoreDDM
open StrataDDM (initDialect)

namespace Strata.Test.BvWidthPrinter

private def bvLit (w v : Nat) : Expression.Expr := .const () (.bitvecConst w (BitVec.ofNat w v))

/-- `g() : bool { bvLit == bvLit }` — puts a bitvector literal in value position. -/
private def litProg (w v : Nat) : Core.Program :=
  { decls := [Decl.func
      { name := ⟨"g", ()⟩, typeArgs := [], inputs := [], output := .bool,
        body := some (.eq () (bvLit w v) (bvLit w v)) } .empty] }

/-- `f(x : bv w) : bv w { x }` — puts a bitvector width in type position. -/
private def typeProg (w : Nat) : Core.Program :=
  { decls := [Decl.func
      { name := ⟨"f", ()⟩, typeArgs := [], inputs := [("x", .bitvec w)],
        output := .bitvec w, body := some (.fvar () ⟨"x", ()⟩ (some (.bitvec w))) } .empty] }

/-- `f(x : inTy) : outTy { op(x) }` — applies a unary op (e.g. a bitvector conversion). -/
private def unaryOpProg (inTy outTy : Lambda.LMonoTy) (op : String) : Core.Program :=
  { decls := [Decl.func
      { name := ⟨"f", ()⟩, typeArgs := [], inputs := [("x", inTy)], output := outTy,
        body := some (.app () (.op () ⟨op, ()⟩ none) (.fvar () ⟨"x", ()⟩ (some inTy))) } .empty] }

/-- AST→CST conversion errors recorded while printing `p`, each as `"<fn>: <description>"`
    (the print-direction analog of `BvWidthMarkerTest`'s `transErrors`). -/
private def errorDescs (p : Core.Program) : List String :=
  (programToCST (M := StrataDDM.SourceRange) p).1.errors.toList.map
    fun | .unsupportedConstruct fn desc _ _ => s!"{fn}: {desc}"

/-- Parse+translate the program text the printer claims to produce (before the appended error
    block); `true` iff it is a valid Core program with no errors. -/
private def reparses (p : Core.Program) : IO Bool := do
  let full := (Core.formatProgram p).pretty
  let input := (full.splitOn "\n\n-- Errors encountered during conversion:").headD full
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let body := if input.startsWith "program Core;\n\n" then
    (input.drop "program Core;\n\n".length).toString else input
  let inputCtx := StrataDDM.Parser.stringInputContext ⟨"bvwidth-test"⟩ body
  try
    let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core" inputCtx
    let (_, errs) := TransM.run Inhabited.default (translateProgram sp)
    pure errs.isEmpty
  catch _ => pure false

/-! ## An unsupported width records a conversion error and does not re-parse

Each program carries the width in two positions (two literal uses / the input and output types),
so two errors are recorded. Both the literal and type paths report the same "unsupported bitvec
width" reason. The recorded errors and the failed re-parse are shown below. -/

/-- info:
== literal ==
lconstToExpr: unsupported bitvec width: 3
lconstToExpr: unsupported bitvec width: 3
re-parses: false
== type ==
lmonoTyToCoreType: unsupported bitvec width: 3
lmonoTyToCoreType: unsupported bitvec width: 3
re-parses: false
-/
#guard_msgs in
#eval do
  IO.println "== literal =="
  IO.println (String.intercalate "\n" (errorDescs (litProg 3 5)))
  IO.println s!"re-parses: {← reparses (litProg 3 5)}"
  IO.println "== type =="
  IO.println (String.intercalate "\n" (errorDescs (typeProg 3)))
  IO.println s!"re-parses: {← reparses (typeProg 3)}"

/-! ## Width 0 — the low boundary of the unsupported-width path

Width 0 is representable in the AST (`BitVec.ofNat 0 v`) and is the extreme low end of the
unsupported-width range: the printer records the same error and does not re-parse, rather than
panicking. -/

/-- info:
== width 0 literal ==
lconstToExpr: unsupported bitvec width: 0
lconstToExpr: unsupported bitvec width: 0
re-parses: false
== width 0 type ==
lmonoTyToCoreType: unsupported bitvec width: 0
lmonoTyToCoreType: unsupported bitvec width: 0
re-parses: false
-/
#guard_msgs in
#eval do
  IO.println "== width 0 literal =="
  IO.println (String.intercalate "\n" (errorDescs (litProg 0 0)))
  IO.println s!"re-parses: {← reparses (litProg 0 0)}"
  IO.println "== width 0 type =="
  IO.println (String.intercalate "\n" (errorDescs (typeProg 0)))
  IO.println s!"re-parses: {← reparses (typeProg 0)}"

/-! ## The placeholder carries the width (and, for literals, the value) -/

/-- True iff `needle` occurs in `s` (Lean core has no `String.containsSubstr`). -/
private def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

#guard hasSubstr (Core.formatProgram (litProg 3 5)).pretty "Bv3.Lit(5)"
#guard hasSubstr (Core.formatProgram (typeProg 3)).pretty "$__unsupported_bv3"

/-! ## Supported conversion ops and the `bv128` literal print and re-parse

`Bv{n}.ToInt` / `.ToUInt` / `Int.ToBv{n}` and the `bv{128}` literal are in the
printer's mapping tables, so they print without a conversion error and re-parse. -/

#guard (errorDescs (litProg 128 5)).isEmpty
#guard [1, 8, 16, 32, 64, 128].all (fun w =>
  (errorDescs (unaryOpProg (.bitvec w) .int s!"Bv{w}.ToInt")).isEmpty &&
  (errorDescs (unaryOpProg (.bitvec w) .int s!"Bv{w}.ToUInt")).isEmpty &&
  (errorDescs (unaryOpProg .int (.bitvec w) s!"Int.ToBv{w}")).isEmpty)

/-- info:
Bv128.ToInt re-parses: true
Int.ToBv128 re-parses: true
bv128 literal re-parses: true
-/
#guard_msgs in
#eval do
  IO.println s!"Bv128.ToInt re-parses: {← reparses (unaryOpProg (.bitvec 128) .int "Bv128.ToInt")}"
  IO.println s!"Int.ToBv128 re-parses: {← reparses (unaryOpProg .int (.bitvec 128) "Int.ToBv128")}"
  IO.println s!"bv128 literal re-parses: {← reparses (litProg 128 5)}"

/-! ## The factory registers bitvector operations for the grammar's widths

The grammar exposes the widths `{1, 8, 16, 32, 64, 128}`, and the factory
registers their BV operations. -/

private def inFactory (name : String) : Bool :=
  (Core.Factory.toArray.find? (fun f => f.name.name == name)).isSome

#guard !inFactory "Bv2.Add"
#guard !inFactory "Bv100.SafeAdd"
#guard !inFactory "Bv3.SafeSDiv"
#guard [1, 8, 16, 32, 64, 128].all (fun w => inFactory s!"Bv{w}.Add")
#guard [1, 8, 16, 32, 64, 128].all (fun w => inFactory s!"Bv{w}.SafeAdd")
#guard [1, 8, 16, 32, 64, 128].all (fun w => inFactory s!"Bv{w}.ToInt")
#guard [1, 8, 16, 32, 64, 128].all (fun w => inFactory s!"Int.ToBv{w}")

end Strata.Test.BvWidthPrinter

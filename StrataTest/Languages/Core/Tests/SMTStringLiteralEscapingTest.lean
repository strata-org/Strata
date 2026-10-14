/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open StrataDDM (Program)

/-! ## Test: string literals are escaped before they are emitted into SMT-LIB

The companion to `SMTSymbolEscapingTest`, for the other half of what a Core program can
put into a script. A *name* that is not repaired supplies the surrounding command's
**structure**; a *literal* cannot — the only way out of a literal is a `"`, and SMT-LIB
spells an embedded one by doubling it. What a literal can do is denote a **different
string** than the program wrote, and that is enough: under an uninterpreted function, two
source strings that collapse into one SMT string make contradictory assumptions, the
negated goal comes back `unsat`, and a VC reads `unsat` as proved.

So these tests run a real solver and check a verdict, as the symbol tests do. A test on
the emitted text alone would not catch this: the point is that the solver is handed a
*decidable* question about the string the program actually wrote. Spellings are pinned
separately in `StrataTest.DL.SMT.StringLitTests`.

Each obligation below is false, so anything other than `❌ fail` means a literal has been
read as a different string. The `assume`d equations are the mechanism: they are consistent
exactly when the literals they mention are distinct, which is what the escaping has to
preserve.
-/

namespace Strata

/-! ### A non-ASCII literal under an uninterpreted function

The literal must be *unfolded* to reach SMT at all, which is why it sits under `f`: a
comparison between two literals is decided before the solver ever sees it. -/
private def nonAsciiUnderUF : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Test()
{
  assume [h]: f("héllo") == 6;
  assert [bad]: false;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bad
Property: assert
Assumptions:
h: f("héllo") == 6
Obligation:
false

---
info:
Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify nonAsciiUnderUF

---------------------------------------------------------------------

/-! ### A literal whose own characters spell an SMT-LIB escape

The first literal contains the six characters `\ u { 4 1 }`. Escaping its backslash as
`\u{5c}` prevents the sequence from being interpreted as the code point `A`, so the two
assumptions remain consistent and the false obligation fails as expected. -/
private def backslashUEscape : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Test()
{
  assume [h1]: f("\\u{41}") == 1;
  assume [h2]: f("A") == 2;
  assert [bad]: false;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bad
Property: assert
Assumptions:
h1: f("\\u{41}") == 1
h2: f("A") == 2
Obligation:
false

---
info:
Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify backslashUEscape

---------------------------------------------------------------------

/-! ### Distinct non-ASCII literals stay distinct

The injectivity the escaping has to supply, at the level where it matters. An escaping
that mapped every unemittable character to one replacement would pass the two tests above
and fail this one: `héllo` and `hallo` would become the same SMT string, the assumptions
would contradict, and the obligation would come back proved. -/
private def distinctNonAsciiLiterals : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Test()
{
  assume [h1]: f("héllo") == 1;
  assume [h2]: f("hállo") == 2;
  assert [bad]: false;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bad
Property: assert
Assumptions:
h1: f("héllo") == 1
h2: f("hállo") == 2
Obligation:
false

---
info:
Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify distinctNonAsciiLiterals

---------------------------------------------------------------------

/-! ### The same non-ASCII literal is the same string: an obligation that must be *proved*

The other direction, and the one a too-aggressive escaping would break. `❌ fail` and
`🚨 Crash` are both visible; an escaping that made two occurrences of one literal denote
different strings would instead cost a *valid* proof, and `unknown` is not proved. So one
test here has to come back `✅ pass`, for a reason the solver can only reach by seeing the
two literals as equal. -/
private def sameNonAsciiLiteralProves : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Test()
{
  assume [h]: f("héllo") == 6;
  assert [good]: f("héllo") == 6;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: good
Property: assert
Assumptions:
h: f("héllo") == 6
Obligation:
f("héllo") == 6

---
info:
Obligation: good
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify sameNonAsciiLiteralProves

---------------------------------------------------------------------

/-! ### Characters beyond the BMP, and the string theory applied to one

An emoji is code point `0x1f600`, inside the `String` sort's alphabet and inside what five
hex digits can name, so it is representable and no surrogate pair is involved. -/
private def astralLiteral : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Test()
{
  assume [h1]: f("😀") == 1;
  assume [h2]: f("x") == 2;
  assert [bad]: false;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bad
Property: assert
Assumptions:
h1: f("😀") == 1
h2: f("x") == 2
Obligation:
false

---
info:
Obligation: bad
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify astralLiteral

---------------------------------------------------------------------

/-! ### An unrepresentable literal fails only its own obligation

The SMT-LIB `String` alphabet ends at `0x2FFFF`. The first procedure's obligation
contains `U+E0001`, so it receives an encoding result. Verification continues to a
separate procedure whose ASCII-string obligation reaches the solver and passes. -/
private def unsupportedLiteralIsolated : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Unsupported()
{
  assume [h]: f("a󠀁b") == 1;
  assert [unsupported]: false;
};
procedure Unrelated()
{
  assume [safe]: f("safe") == 2;
  assert [unrelated]: f("safe") == 2;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: unsupported
Property: assert
Assumptions:
h: f("a󠀁b") == 1
Obligation:
false

Label: unrelated
Property: assert
Assumptions:
safe: f("safe") == 2
Obligation:
f("safe") == 2

---
info:
Obligation: unsupported
Property: assert
Result: 🚨 SMT Encoding Error! SMT text encoding failed: term serialization: string literal contains code point U+e0001, which is outside the alphabet of SMT-LIB's String sort (0x0-0x2FFFF) and has no literal spelling

Obligation: unrelated
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify unsupportedLiteralIsolated

---------------------------------------------------------------------

/-! ### A CSE-hoisted unsupported literal still fails only its users

Repeating the unsupported subterm makes CSE extract it into a `$__cse`
definition. Symbolic evaluation places all obligations in one synthetic
procedure, so the definition is initially hoisted above both source
procedures' VC branches. Per-obligation dependency pruning must retain it for
the first VC while keeping it out of the unrelated VC's SMT query. -/
private def cseUnsupportedLiteralIsolated : Program :=
#strata
program Core;
function f (s : string) : int;
procedure Unsupported()
{
  assume [h1]: f("a󠀁b") == 1;
  assume [h2]: f("a󠀁b") == 1;
  assert [cse_unsupported]: false;
};
procedure Unrelated()
{
  assume [safe]: f("safe") == 2;
  assert [cse_unrelated]: f("safe") == 2;
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: cse_unsupported
Property: assert
Assumptions:
h1: f("a󠀁b") == 1
h2: f("a󠀁b") == 1
Obligation:
false

Label: cse_unrelated
Property: assert
Assumptions:
safe: f("safe") == 2
Obligation:
f("safe") == 2

---
info:
Obligation: cse_unsupported
Property: assert
Result: 🚨 SMT Encoding Error! SMT text encoding failed: term serialization: string literal contains code point U+e0001, which is outside the alphabet of SMT-LIB's String sort (0x0-0x2FFFF) and has no literal spelling

Obligation: cse_unrelated
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cseUnsupportedLiteralIsolated

/-! The pruning occurs before backend selection, so incremental and parallel
    discharge must observe the same per-obligation isolation. -/
/--
info:
Obligation: cse_unsupported
Property: assert
Result: 🚨 SMT Encoding Error! SMT text encoding failed: term serialization: string literal contains code point U+e0001, which is outside the alphabet of SMT-LIB's String sort (0x0-0x2FFFF) and has no literal spelling

Obligation: cse_unrelated
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cseUnsupportedLiteralIsolated
  (options := { Core.VerifyOptions.quiet with incremental := true })

/--
info:
Obligation: cse_unsupported
Property: assert
Result: 🚨 SMT Encoding Error! SMT text encoding failed: term serialization: string literal contains code point U+e0001, which is outside the alphabet of SMT-LIB's String sort (0x0-0x2FFFF) and has no literal spelling

Obligation: cse_unrelated
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cseUnsupportedLiteralIsolated
  (options := { Core.VerifyOptions.quiet with parallelWorkers := 2 })

---------------------------------------------------------------------

/-! ### Encodable CSE definitions stay in the shared prefix

Per-obligation pruning is needed only to isolate definitions that cannot be
serialized. Applying it to ordinary definitions gives each obligation a
different oldest frame and defeats both the encoding fold's prefix reuse and
the captured-emitter mirror. Each procedure below contributes one CSE
definition; the inspection backend must therefore see both definitions on
both obligations. -/
private def encodableCSEDefinitionsStayShared : Program :=
#strata
program Core;
function f (s : string) : int;
procedure First()
{
  assume [a1]: f("alpha") == 1;
  assume [a2]: f("alpha") == 1;
  assert [first]: false;
};
procedure Second()
{
  assume [b1]: f("beta") == 2;
  assume [b2]: f("beta") == 2;
  assert [second]: false;
};
#end

private def reportCSEDefinitionCount : Core.MkDischargeFn :=
  fun _options _counter _tempDir _vars _md label _termCache _captured _pctx =>
    fun _assumptions _obligation _ctx _sat _valid varDefs _varDecls => do
      let count := (varDefs.filter fun d =>
        d.name.startsWith "$__cse.").length
      IO.println s!"{label}: {count} shared CSE definitions"
      return .ok (.unknown, .unknown, .init)

/--
info: first: 2 shared CSE definitions
second: 2 shared CSE definitions
---
info:
Obligation: first
Property: assert
Result: ❓ unknown

Obligation: second
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Core.verify encodableCSEDefinitionsStayShared
  (options := Core.VerifyOptions.quiet)
  (mkDischarge := reportCSEDefinitionCount)

/-! ### Similar-looking IO errors are not encoding results

Classification uses `SolverError.encoding`, not diagnostic text. This fake
backend deliberately throws an ordinary IO error whose text resembles an
encoding error; it must remain a fatal pipeline error. -/

private def similarLookingIOFailure : Core.MkDischargeFn :=
  fun _options _counter _tempDir _vars _md _label _termCache _captured _pctx =>
    fun _assumptions _obligation _ctx _sat _valid _varDefs _varDecls =>
      throw (IO.userError
        "SMT text encoding failed: this is an ordinary backend IO failure")

/--
error: SMT text encoding failed: this is an ordinary backend IO failure
-/
#guard_msgs in
#eval Core.verify sameNonAsciiLiteralProves
  (options := Core.VerifyOptions.quiet)
  (mkDischarge := similarLookingIOFailure)

end Strata

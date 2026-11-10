/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import StrataDDM.Util.String

meta section
open Strata

/-! # Core's string evaluators agree with cvc5

Core evaluates `Str.Length`, `Str.Concat`, `Str.PrefixOf`, `Str.SuffixOf`, `Str.Lt`
and `Str.Le` on literals itself, while the solver gives them their SMT-LIB meaning.
A lemma that Core's evaluator decides one way and the solver the other would be
proved or refuted depending on whether evaluation reached it first.

Each case below is one lemma over string arguments, verified twice:

* with the arguments written as literals, so Core's evaluator folds the lemma;
* with each argument a procedure parameter `assume`d equal to that literal, so the
  evaluator cannot fold it and cvc5 decides it.

Each line prints both verdicts, and who reached them: `evaluator` when no query
reached the solver, `cvc5` when one did. A line ending in `DISAGREE` is a lemma the
two decide differently.

The arguments are edge cases: empty strings, characters the SMT-LIB encoding
escapes (control characters, `"`, `\`, text that spells an SMT-LIB escape), code
points beyond the Basic Multilingual Plane up to `0x2FFFF`, the last code point of
SMT-LIB's string alphabet, equal strings, strings that are prefixes of each other,
and pairs whose order by code point differs from their order by UTF-16 code unit.
Lean strings cannot hold a surrogate code point (`0xD800`-`0xDFFF`), so no Core
literal contains one; the cases use the code points on either side of that range.
-/

namespace Core.StringEvalAgreementTest

/-- The string made of the single code point `n`, which must be a Unicode scalar value:
    `Char.ofNat` would silently turn a surrogate or a value above `0x10FFFF` into `'\0'`. -/
private def cp (n : Nat) : String :=
  if n.isValidChar then String.singleton (Char.ofNat n)
  else panic! s!"cp: {n} is not a Unicode scalar value"

/-- A lemma over string arguments: `$i` in `goal` stands for the `i`-th argument. -/
private structure Case where
  name : String
  goal : String
  args : List String

/-- `c.goal` with each `$i` replaced by `arg i`. -/
private def Case.render (c : Case) (arg : Nat → String) : String :=
  (List.range c.args.length).reverse.foldl
    (fun g i => g.replace s!"${i}" (arg i)) c.goal

/-- A procedure that asserts `c` on literals. -/
private def Case.onLiterals (c : Case) : String :=
  let goal := c.render fun i => StrataDDM.escapeStringLit (c.args.getD i "")
  s!"procedure {c.name}_literals()\n\{\n  assert [{c.name}]: {goal};\n};\n"

/-- The parameter list `a0 : string, a1 : string, …` of `c`'s procedures. -/
private def Case.params (c : Case) : String :=
  ", ".intercalate ((List.range c.args.length).map (s!"a{·} : string"))

/-- A procedure that asserts `c` on parameters assumed equal to its literals. -/
private def Case.onParameters (c : Case) : String :=
  let assumes := String.join <| c.args.zipIdx.map fun (a, i) =>
    s!"  assume a{i} == {StrataDDM.escapeStringLit a};\n"
  s!"procedure {c.name}_parameters({c.params})\n\{\n{assumes}  assert [{c.name}]: \
    {c.render (s!"a{·}")};\n};\n"

/-- A procedure that asserts `c` on unconstrained parameters. -/
private def Case.onFreeParameters (c : Case) : String :=
  s!"procedure {c.name}_free({c.params})\n\{\n  assert [{c.name}]: {c.render (s!"a{·}")};\n};\n"

/-- Parse the text of a Core program. -/
private def parseText (text : String) : IO Core.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core"
    (StrataDDM.Parser.stringInputContext ⟨"stringEvalAgreement"⟩ text)
  pure (TransM.run Inhabited.default (translateProgram sp)).fst

/-- How a verdict reports an SMT encoding error. -/
private def encodingError : String := "🚨 SMT Encoding Error!"

/-- `outcome` with an SMT encoding error cut to its kind, so the expected output does not
    depend on the wording of the encoder's message. -/
private def verdictKind (outcome : String) : String :=
  if (outcome.splitOn encodingError).length > 1 then encodingError else outcome

/-- The verdict on each obligation of `text`, and whether a query for it reached the
    solver, by label. -/
private def verdicts (text : String) : IO (List (String × String × Bool)) := do
  let reached ← IO.mkRef ([] : List String)
  let mk : Core.MkDischargeFn := fun options counter dir vars md label cache captured pctx =>
    fun as goal ctx sat val defs decls => do
      reached.modify (label :: ·)
      Core.mkDischargeFn options counter dir vars md label cache captured pctx
        as goal ctx sat val defs decls
  let options := { Core.VerifyOptions.quiet with solver := "cvc5" }
  match ← (Strata.Core.verifyProgram (← parseText text) options
      (mkDischarge := mk)).toBaseIO with
  | .error e => throw (IO.userError s!"verification failed: {e}")
  | .ok results =>
    let reached ← reached.get
    return results.toList.map fun r =>
      let label := r.obligation.label
      (label, verdictKind r.formatOutcome, reached.contains label)

/-- How the two verdicts compare: nothing when they are equal, `DISAGREE` when both sides
    decided and differ, and `fail-closed` when the solver side is an
    encoding error, which refuses the lemma instead of deciding it. -/
private def comparison (l p : String) : String :=
  if l == p then ""
  else if p == encodingError then
    " fail-closed"
  else " DISAGREE"

/-- Who reached a verdict: `cvc5` when a query reached the solver, `evaluator` otherwise. -/
private def who (solver : Bool) : String := if solver then "cvc5" else "evaluator"

/-- Verify each case as the procedures `left c` and `right c`, and print the line `line`
    makes of the two verdicts, each with whether a query reached the solver. -/
private def compare (cases : List Case) (left right : Case → String)
    (line : Case → String × Bool → String × Bool → IO String) : IO Unit := do
  let onLeft ← verdicts (String.join (cases.map left))
  let onRight ← verdicts (String.join (cases.map right))
  for c in cases do
    match onLeft.lookup c.name, onRight.lookup c.name with
    | some l, some r => IO.println (← line c l r)
    | _, _ => IO.println s!"{c.name}: missing obligation"

/-- Print, for each case, the verdict on literals and the verdict on parameters. Fails if
    a parameter lemma did not reach the solver: the pipeline would then have folded it
    with the assumed equalities, and the case would compare the evaluator with itself. -/
private def check (cases : List Case) : IO Unit :=
  compare cases Case.onLiterals Case.onParameters fun c (l, ls) (p, ps) => do
    unless ps do
      throw (IO.userError s!"{c.name}: the parameter lemma did not reach the solver")
    pure s!"{c.name}: {who ls} {l}, {who ps} {p}{comparison l p}"

/-! ## Length -/

/--
info: len_empty: evaluator ✅ pass, cvc5 ✅ pass
len_controls: evaluator ✅ pass, cvc5 ✅ pass
len_quote_backslash: evaluator ✅ pass, cvc5 ✅ pass
len_escape_text: evaluator ✅ pass, cvc5 ✅ pass
len_bmp_edges: evaluator ✅ pass, cvc5 ✅ pass
len_astral: evaluator ✅ pass, cvc5 ✅ pass
len_last_plane: evaluator ✅ pass, cvc5 ✅ pass
-/
#guard_msgs in
#eval check [
  ⟨"len_empty", "str.len($0) == 0", [""]⟩,
  ⟨"len_controls", "str.len($0) == 4", ["\x00\n\t\x7f"]⟩,
  ⟨"len_quote_backslash", "str.len($0) == 2", ["\"\\"]⟩,
  ⟨"len_escape_text", "str.len($0) == 6", ["\\u{41}"]⟩,
  ⟨"len_bmp_edges", "str.len($0) == 2", [cp 0xD7FF ++ cp 0xE000]⟩,
  ⟨"len_astral", "str.len($0) == 1", [cp 0x1F600]⟩,
  ⟨"len_last_plane", "str.len($0) == 1", [cp 0x2FFFF]⟩]

/-! ## Concatenation -/

/--
info: concat_empty_left: evaluator ✅ pass, cvc5 ✅ pass
concat_astral: evaluator ✅ pass, cvc5 ✅ pass
concat_escapes: evaluator ✅ pass, cvc5 ✅ pass
-/
#guard_msgs in
#eval check [
  ⟨"concat_empty_left", "str.concat($0, $1) == $1", ["", "ab"]⟩,
  ⟨"concat_astral", "str.len(str.concat($0, $1)) == 2", [cp 0x10000, cp 0x2FFFF]⟩,
  ⟨"concat_escapes", "str.concat($0, $1) == $2", ["\\", "u{0}", "\\u{0}"]⟩]

/-! ## Prefix and suffix -/

/--
info: prefix_empty: evaluator ✅ pass, cvc5 ✅ pass
prefix_equal: evaluator ✅ pass, cvc5 ✅ pass
prefix_longer: evaluator ✅ pass, cvc5 ✅ pass
prefix_astral: evaluator ✅ pass, cvc5 ✅ pass
suffix_empty: evaluator ✅ pass, cvc5 ✅ pass
suffix_equal: evaluator ✅ pass, cvc5 ✅ pass
suffix_controls: evaluator ✅ pass, cvc5 ✅ pass
suffix_not: evaluator ✅ pass, cvc5 ✅ pass
-/
#guard_msgs in
#eval check [
  ⟨"prefix_empty", "str.prefixof($0, $1)", ["", "abc"]⟩,
  ⟨"prefix_equal", "str.prefixof($0, $1)", ["abc", "abc"]⟩,
  ⟨"prefix_longer", "!str.prefixof($0, $1)", ["abcd", "abc"]⟩,
  ⟨"prefix_astral", "str.prefixof($0, $1)", [cp 0x1F600, cp 0x1F600 ++ "x"]⟩,
  ⟨"suffix_empty", "str.suffixof($0, $1)", ["", "abc"]⟩,
  ⟨"suffix_equal", "str.suffixof($0, $1)", ["abc", "abc"]⟩,
  ⟨"suffix_controls", "str.suffixof($0, $1)", ["\x00", "a\x00"]⟩,
  ⟨"suffix_not", "!str.suffixof($0, $1)", ["ab", "abc"]⟩]

/-! ## Order -/

/--
info: lt_empty: evaluator ✅ pass, cvc5 ✅ pass
lt_irreflexive: evaluator ✅ pass, cvc5 ✅ pass
lt_prefix: evaluator ✅ pass, cvc5 ✅ pass
lt_code_point_order: evaluator ✅ pass, cvc5 ✅ pass
lt_across_surrogates: evaluator ✅ pass, cvc5 ✅ pass
le_reflexive: evaluator ✅ pass, cvc5 ✅ pass
le_empty: evaluator ✅ pass, cvc5 ✅ pass
le_not: evaluator ✅ pass, cvc5 ✅ pass
-/
#guard_msgs in
#eval check [
  ⟨"lt_empty", "str.lt($0, $1)", ["", "a"]⟩,
  ⟨"lt_irreflexive", "!str.lt($0, $1)", ["abc", "abc"]⟩,
  ⟨"lt_prefix", "str.lt($0, $1)", ["ab", "abc"]⟩,
  ⟨"lt_code_point_order", "str.lt($0, $1)", [cp 0xFFFF, cp 0x10000]⟩,
  ⟨"lt_across_surrogates", "str.lt($0, $1)", [cp 0xE000, cp 0x1F600]⟩,
  ⟨"le_reflexive", "str.le($0, $1)", ["abc", "abc"]⟩,
  ⟨"le_empty", "str.le($0, $1)", ["", ""]⟩,
  ⟨"le_not", "!str.le($0, $1)", [cp 0x2FFFF, cp 0xD7FF]⟩]

/-! ## Known divergence: characters outside SMT-LIB's alphabet

SMT-LIB strings hold code points `0x0`-`0x2FFFF`, while a Core string literal can
hold any Lean `Char`, up to `0x10FFFF`. These cases use code points above `0x2FFFF`
and are expected to print `fail-closed`: Core's evaluator decides
them, and the SMT encoder rejects the literal, so no solver ever sees the lemma. That
refuses the lemma rather than deciding it the wrong way. Only the kind of the
encoder's error is printed, so rewording its message does not break this test.
-/

/--
info: len_beyond_alphabet: evaluator ✅ pass, cvc5 🚨 SMT Encoding Error! fail-closed
concat_beyond_alphabet: evaluator ✅ pass, cvc5 🚨 SMT Encoding Error! fail-closed
-/
#guard_msgs in
#eval check [
  ⟨"len_beyond_alphabet", "str.len($0) == 1", [cp 0x30000]⟩,
  ⟨"concat_beyond_alphabet", "str.concat($0, $1) == $1", ["", cp 0x10FFFF]⟩]

/-! ## Soundness gap: a lemma true in SMT-LIB and false in Core

SMT-LIB has no character above `0x2FFFF`, and Core does. So a lemma claiming that
no single-character string is above `"\u{2FFFF}"` is valid for cvc5, which proves it
on an unconstrained parameter. Core's evaluator refutes it on the witness `0x30000`.
Both verdicts are about the same lemma, and only one of them is right for Core.

The gap is in `Core.verify`'s default pipeline, which sends `Str.Le` on any string to
the solver. No encoding of strings above `0x2FFFF` into SMT-LIB preserves their order,
so a soundness result for the strings and operations SMT-LIB and Core agree on, which
this repository does not yet contain, would have to leave `Str.Lt` and `Str.Le` out.
The lemma has no quantifier, so a check on quantified string lemmas would not catch it.

The expected output below records a soundness bug in `Core.verify`, not intended
behavior: the cvc5 verdict `pass` is wrong for Core, where the lemma is false. The
planned fix, not yet implemented, is for the SMT back end to check each obligation's
use of strings and report as unknown, rather than proved, any obligation that is not
equisatisfiable with SMT-LIB. `Str.Le` would not be among the operators such a check
admits, so once it is in place the parameter verdict changes
from `pass` to unknown, while the evaluator's verdict on the witness
stays as it is. That change is the fix, not a regression. -/

/-- Print, for each case, the evaluator's verdict on its witness literals and cvc5's
    verdict on unconstrained parameters. -/
private def checkGap (cases : List Case) : IO Unit :=
  compare cases Case.onLiterals Case.onFreeParameters fun c (w, ws) (a, as) =>
    pure s!"{c.name}: {who ws} on witness {w}, {who as} on all strings {a}{comparison w a}"

/--
info:

Obligation no_char_above_alphabet: failed!

Result obtained during evaluation.
no_char_above_alphabet: evaluator on witness ❌ fail, cvc5 on all strings ✅ pass DISAGREE
-/
#guard_msgs in
#eval checkGap [
  ⟨"no_char_above_alphabet",
    s!"str.len($0) == 1 ==> str.le($0, {StrataDDM.escapeStringLit (cp 0x2FFFF)})",
    [cp 0x30000]⟩]

end Core.StringEvalAgreementTest

end

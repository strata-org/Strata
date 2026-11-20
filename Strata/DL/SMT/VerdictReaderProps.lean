/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init
public import Strata.DL.SMT.VerdictReader
import all Strata.DL.SMT.VerdictReader

/-! # The next verdict is the first top-level atom after the previous responses

`dropToVerdict_responses` shows that `dropToVerdict` skips a run of complete solver responses
whole, whatever words they contain. `dropToVerdict_responses_atom` shows that it stops at the
first top-level atom after them, whatever that atom is, so it never skips an answer and each
answer is read at its own position. `dropToVerdict_responses_append`,
`splitFirstLine_responses_append` and `readVerdict_responses_append` specialize this to an answer
`sat`, `unsat` or `unknown`, the second as `solverResult` reads it.
-/

public section

namespace Strata.SMT

/-- The text inside a balanced s-expression: plain characters, string literals, quoted
    symbols, comments and nested lists. -/
inductive SExpBody : List Char → Prop
  | nil : SExpBody []
  | char {c : Char} {cs : List Char} :
      c ≠ '(' → c ≠ ')' → c ≠ '"' → c ≠ '|' → c ≠ ';' → SExpBody cs → SExpBody (c :: cs)
  | str {s cs : List Char} : '"' ∉ s → SExpBody cs → SExpBody ('"' :: s ++ '"' :: cs)
  | sym {s cs : List Char} : '|' ∉ s → SExpBody cs → SExpBody ('|' :: s ++ '|' :: cs)
  | comment {s cs : List Char} : '\n' ∉ s → SExpBody cs → SExpBody (';' :: s ++ '\n' :: cs)
  | list {b cs : List Char} : SExpBody b → SExpBody cs → SExpBody ('(' :: b ++ ')' :: cs)

/-- A run of complete responses: whitespace, the general responses `success` and `unsupported`
    (each ended by whitespace), and balanced s-expressions. -/
inductive Responses : List Char → Prop
  | nil : Responses []
  | space {c : Char} {cs : List Char} : c.isWhitespace → Responses cs → Responses (c :: cs)
  | sexp {b cs : List Char} : SExpBody b → Responses cs → Responses ('(' :: b ++ ')' :: cs)
  | generalAtom {w : List Char} {c : Char} {cs : List Char} :
      w = "success".toList ∨ w = "unsupported".toList → c.isWhitespace →
      Responses cs → Responses (w ++ c :: cs)

/-- Inside a string literal, skipping reaches the closing `"` and goes on in code. -/
private theorem dropToVerdict_str (d : Nat) (s r : List Char) (h : '"' ∉ s) :
    dropToVerdict d .str (s ++ '"' :: r) = dropToVerdict d .code r := by
  induction s with
  | nil => simp [dropToVerdict]
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h
    simp [dropToVerdict, Ne.symm h.1, ih h.2]

/-- Inside a quoted symbol, skipping reaches the closing `|` and goes on in code. -/
private theorem dropToVerdict_sym (d : Nat) (s r : List Char) (h : '|' ∉ s) :
    dropToVerdict d .sym (s ++ '|' :: r) = dropToVerdict d .code r := by
  induction s with
  | nil => simp [dropToVerdict]
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h
    simp [dropToVerdict, Ne.symm h.1, ih h.2]

/-- Inside a comment, skipping reaches the end of the line and goes on in code. -/
private theorem dropToVerdict_comment (d : Nat) (s r : List Char) (h : '\n' ∉ s) :
    dropToVerdict d .comment (s ++ '\n' :: r) = dropToVerdict d .code r := by
  induction s with
  | nil => simp [dropToVerdict]
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h
    simp [dropToVerdict, Ne.symm h.1, ih h.2]

/-- Inside a list, the body of an s-expression is skipped whole. -/
private theorem dropToVerdict_body {b : List Char} (hb : SExpBody b) :
    ∀ (d : Nat) (r : List Char),
      dropToVerdict (d + 1) .code (b ++ r) = dropToVerdict (d + 1) .code r := by
  induction hb with
  | nil => intro d r; rfl
  | char h1 h2 h3 h4 h5 _ ih =>
    intro d r
    simp [dropToVerdict, h1, h2, h3, h4, h5, ih]
  | str hs _ ih =>
    intro d r
    simp [dropToVerdict, dropToVerdict_str _ _ _ hs, ih]
  | sym hs _ ih =>
    intro d r
    simp [dropToVerdict, dropToVerdict_sym _ _ _ hs, ih]
  | comment hs _ ih =>
    intro d r
    simp [dropToVerdict, dropToVerdict_comment _ _ _ hs, ih]
  | @list b cs _ _ ihb ihc =>
    intro d r
    have hb := ihb (d + 1) (')' :: cs ++ r)
    simp only [List.cons_append, List.append_assoc] at hb ⊢
    simp [dropToVerdict, hb, ihc]

/-- At the top level, a run of complete responses is skipped whole. -/
theorem dropToVerdict_responses {t : List Char} (ht : Responses t) (r : List Char) :
    dropToVerdict 0 .code (t ++ r) = dropToVerdict 0 .code r := by
  induction ht with
  | nil => rfl
  | @space c cs hc _ ih =>
    have : c = ' ' ∨ c = '\t' ∨ c = '\r' ∨ c = '\n' := by
      simpa [Char.isWhitespace, or_assoc] using hc
    rcases this with rfl | rfl | rfl | rfl <;> simp [dropToVerdict, ih]
  | @sexp b cs hb _ ih =>
    have h := dropToVerdict_body hb 0 (')' :: cs ++ r)
    simp only [List.cons_append, List.append_assoc] at h ⊢
    simp [dropToVerdict, h, ih]
  | @generalAtom w c cs hw hc _ ih =>
    have : c = ' ' ∨ c = '\t' ∨ c = '\r' ∨ c = '\n' := by
      simpa [Char.isWhitespace, or_assoc] using hc
    rcases hw with rfl | rfl <;> rcases this with rfl | rfl | rfl | rfl <;>
      simp [dropToVerdict, isGeneralAtom, ih]

/-- After a run of complete responses, `dropToVerdict` stops at the first top-level atom,
    whatever it is: it skips no answer. -/
theorem dropToVerdict_responses_atom {t : List Char} (ht : Responses t) {c : Char}
    (h1 : c ≠ '(') (h2 : c ≠ ')') (h3 : c ≠ '"') (h4 : c ≠ '|') (h5 : c ≠ ';')
    (hw : c.isWhitespace = false) (rest : List Char) (hg : isGeneralAtom (c :: rest) = false) :
    dropToVerdict 0 .code (t ++ c :: rest) = c :: rest := by
  rw [dropToVerdict_responses ht]
  simp [dropToVerdict, h1, h2, h3, h4, h5, hw, hg]

/-- The verdict read after a run of complete responses is the first top-level atom after
    them, whatever words the responses contain. -/
theorem dropToVerdict_responses_append {t : List Char} (ht : Responses t)
    {v : List Char} {d : Decision} (hv : decodeVerdict v = some d) (rest : List Char) :
    dropToVerdict 0 .code (t ++ v ++ '\n' :: rest) = v ++ '\n' :: rest := by
  rw [List.append_assoc]
  unfold decodeVerdict at hv
  split at hv <;> first
    | (simp at hv; done)
    | (refine dropToVerdict_responses_atom ht ?_ ?_ ?_ ?_ ?_ ?_ _ ?_ <;>
        first | decide | simp [isGeneralAtom])

/-- After a run of complete responses, `solverResult`'s reading of the next answer decodes the
    answer that follows them and leaves the text after its line. -/
theorem splitFirstLine_responses_append {t : List Char} (ht : Responses t)
    {v : List Char} {d : Decision} (hv : decodeVerdict v = some d) (rest : List Char) :
    splitFirstLine (dropToVerdict 0 .code (t ++ v ++ '\n' :: rest)) = (some d, rest) := by
  rw [dropToVerdict_responses_append ht hv]
  unfold decodeVerdict at hv
  split at hv <;> first
    | (simp at hv; done)
    | (simp only [Option.some.injEq] at hv; subst hv; simp [splitFirstLine, decodeVerdict])

/-- After a run of complete responses, the answer read is the one that follows them. -/
theorem readVerdict_responses_append {t : List Char} (ht : Responses t)
    {v : List Char} {d : Decision} (hv : decodeVerdict v = some d) (rest : List Char) :
    readVerdict (t ++ v ++ '\n' :: rest) = some d := by
  rw [readVerdict, splitFirstLine_responses_append ht hv]

end Strata.SMT
end

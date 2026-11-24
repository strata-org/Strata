/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.NameMangling
import all Strata.Languages.Core.NameMangling

/-! # Properties of name mangling

- `escName_inj`, `decName_escName`: escaping a name is injective, and decoding undoes it.
- `mangleTyArgs_inj`: mangling a nonempty list of types is injective.
- `choosePrefix_fresh`: no name the copies avoid starts with the copies' prefix and `#`.
- `copyName_inj`: two copies with the same name copy the same function at the same
  instantiation; `copyName_ne_of_mem`: no avoided name is a copy's name.
- `demangleFuncName_copyName`, `demangleFuncName_of_not_prefix`: a copy's name reads back as
  its base and instantiation, and a name off the prefix is not read as a copy.
- `Core.FreshPlainName.sanitize_noHash`: the result of `sanitize` has no `#`. The base of a name
  generated through it is therefore `#`-free; that the emitted name, the base with a freshness
  suffix, has no `#` is checked by tests, not proved here.
-/

namespace Core.NameMangling

public section

open Strata.PtrCache

/-- A character other than `?` and `#` escapes to itself. -/
private theorem escChar_plain {c : Char} (h1 : c ≠ '?') (h2 : c ≠ '#') : escChar c = [c] := by
  unfold escChar; split <;> simp_all

/-- Unescaping keeps a head character other than `?` in place. -/
private theorem unescL_plain_cons {c : Char} (h1 : c ≠ '?') (r : List Char) :
    unescL (c :: r) = c :: unescL r := by
  conv => lhs; rw [unescL.eq_def]
  split <;> simp_all

/-- Unescaping an escaped body gives back its characters. -/
private theorem unescL_escBody : ∀ s : List Char, unescL (escBody s) = s
  | [] => rfl
  | c :: r => by
    have ih := unescL_escBody r
    simp only [escBody, List.flatMap_cons] at ih ⊢
    by_cases h1 : c = '?'
    · subst h1; simp [escChar, unescL, ih]
    by_cases h2 : c = '#'
    · subst h2; simp [escChar, unescL, ih]
    rw [escChar_plain h1 h2, List.singleton_append, unescL_plain_cons h1, ih]

/-- An escaped body never starts with the mark `?n`. -/
private theorem escBody_not_marked (s r : List Char) : escBody s ≠ '?' :: 'n' :: r := by
  cases s with
  | nil => simp [escBody]
  | cons c s =>
    simp only [escBody, List.flatMap_cons]
    by_cases h1 : c = '?'
    · subst h1; simp [escChar]
    by_cases h2 : c = '#'
    · subst h2; simp [escChar]
    rw [escChar_plain h1 h2]; simp [h1]

/-- Decoding an escaped name gives back the name's characters. -/
private theorem decNameL_escNameL (s : String) : decNameL (escNameL s) = s.toList := by
  unfold escNameL
  split
  · simp [decNameL, unescL_escBody]
  · have hus := unescL_escBody s.toList
    unfold decNameL; split
    · rename_i r heq; exact absurd heq (escBody_not_marked _ _)
    · exact hus

/-- `escNameL` is injective. -/
private theorem escNameL_inj {s s' : String} (h : escNameL s = escNameL s') : s = s' :=
  String.toList_inj.mp (by rw [← decNameL_escNameL s, ← decNameL_escNameL s', h])

/-- The characters of an escaped body: those of the body, `?` when it has `?` or `#`, and `h` when it has `#`. -/
private theorem mem_escBody_iff {x : Char} {s : List Char} :
    x ∈ escBody s ↔ ∃ c ∈ s, x ∈ escChar c := by
  simp [escBody, List.mem_flatMap]

/-- An escaped body has no `#`. -/
private theorem hash_not_mem_escBody (s : List Char) : '#' ∉ escBody s := by
  intro hm
  obtain ⟨c, _, hc⟩ := mem_escBody_iff.mp hm
  by_cases h1 : c = '?'
  · subst h1; simp [escChar] at hc
  by_cases h2 : c = '#'
  · subst h2; simp [escChar] at hc
  rw [escChar_plain h1 h2] at hc
  exact h2 (List.mem_singleton.mp hc).symm

/-- An escaped name has no `#`. -/
private theorem hash_not_mem_escNameL (s : String) : '#' ∉ escNameL s := by
  unfold escNameL; split
  · simp [hash_not_mem_escBody]
  · exact hash_not_mem_escBody _

/-- A body with no `?` and no `#` escapes to itself. -/
private theorem escBody_eq_of_plain {s : List Char} (h1 : '?' ∉ s) (h2 : '#' ∉ s) :
    escBody s = s := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    simp only [List.mem_cons, not_or] at h1 h2
    simp only [escBody, List.flatMap_cons] at ih ⊢
    rw [escChar_plain (Ne.symm h1.1) (Ne.symm h2.1), ih h1.2 h2.2]; rfl

/-- An escaped name without a `?` is the name itself. -/
private theorem escBody_eq_of_no_esc {s : List Char} (h : '?' ∉ escBody s) : escBody s = s := by
  apply escBody_eq_of_plain
  · intro hm; exact h (mem_escBody_iff.mpr ⟨_, hm, by simp [escChar]⟩)
  · intro hm; exact h (mem_escBody_iff.mpr ⟨_, hm, by simp [escChar]⟩)

/-- An escaped name is never a string of digits. -/
private theorem escNameL_not_num (s : String) : ¬ (∀ c ∈ escNameL s, c.isDigit = true) := by
  intro hd
  unfold escNameL at hd; split at hd
  · exact absurd (hd '?' (by simp)) (by decide)
  · rename_i hm
    have hb : '?' ∉ escBody s.toList := fun h => absurd (hd _ h) (by decide)
    rw [escBody_eq_of_no_esc hb] at hd
    simp only [needsMark] at hm
    simp_all

/-- An escaped name is never `$bv`. -/
private theorem escNameL_ne_bv (s : String) : escNameL s ≠ "$bv".toList := by
  unfold escNameL; split
  · simp
  · rename_i hm
    intro he
    have hb : '?' ∉ escBody s.toList := by rw [he]; decide
    rw [escBody_eq_of_no_esc hb] at he
    simp [needsMark, he] at hm

/-- Names without `?`, `#`, not empty, not a numeral and not `$bv` are written as is. -/
private theorem escNameL_eq_of_plain {s : String} (h1 : '?' ∉ s.toList) (h2 : '#' ∉ s.toList)
    (h3 : needsMark s.toList = false) : escNameL s = s.toList := by
  simp [escNameL, h3, escBody_eq_of_plain h1 h2]

/-- `escName` and `escNameL` agree. -/
private theorem escName_toList (s : String) : (escName s).toList = escNameL s := by
  simp [escName]

/-- **Escaping is injective.** -/
theorem escName_inj {s s' : String} (h : escName s = escName s') : s = s' :=
  escNameL_inj (by rw [← escName_toList, ← escName_toList, h])

/-- **`decName` undoes `escName`.** -/
theorem decName_escName (s : String) : decName (escName s) = s := by
  simp [decName, escName_toList, decNameL_escNameL]

/-- An escaped name has no `#`. -/
theorem hash_not_mem_escName (s : String) : '#' ∉ (escName s).toList := by
  rw [escName_toList]; exact hash_not_mem_escNameL s

/-! ### Mangling is injective

`mangleTyArgs` writes a list of types as tokens joined by `#`: a type constructor's escaped
name, then, if it has arguments, their number and their tokens; a bitvector as `$bv` and its
width; a type variable as `?v` and its escaped name. No token has `#`, and a numeral token can
only be an arity or a width, so the tokens read back in one way, for every list of types. -/

section MangleInj

/-- `x` is a numeral: nonempty, all decimal digits. -/
@[expose] def IsNum (x : List Char) : Prop := x ≠ [] ∧ ∀ c ∈ x, c.isDigit = true

mutual
/-- The tokens `mangleTy` joins with `#`. -/
@[expose] def tyToks : Lambda.LMonoTy → List (List Char)
  | .ftvar a => ['?' :: 'v' :: escNameL a]
  | .bitvec n => ["$bv".toList, (toString n).toList]
  | .tcons c args =>
    if args.isEmpty then [escNameL c]
    else escNameL c :: (toString args.length).toList :: tysToks args
/-- The tokens `mangleTyArgs` joins with `#`. -/
@[expose] def tysToks : List Lambda.LMonoTy → List (List Char)
  | [] => []
  | t :: ts => tyToks t ++ tysToks ts
end

/-- Join tokens with `#`. -/
@[expose] def joinH : List (List Char) → List Char
  | [] => []
  | [x] => x
  | x :: y :: rest => x ++ '#' :: joinH (y :: rest)

/-- Joining two nonempty token lists puts one `#` between their joins. -/
private theorem joinH_append : ∀ {l₁ l₂ : List (List Char)}, l₁ ≠ [] → l₂ ≠ [] →
    joinH (l₁ ++ l₂) = joinH l₁ ++ '#' :: joinH l₂
  | [], _, h, _ => absurd rfl h
  | [x], y :: ys, _, _ => rfl
  | x :: x' :: xs, l₂, _, h₂ => by
    have := joinH_append (l₁ := x' :: xs) (l₂ := l₂) (by simp) h₂
    simp only [List.cons_append, joinH] at this ⊢
    rw [this]; simp

/-- A type has at least one token. -/
private theorem tyToks_ne_nil : ∀ t : Lambda.LMonoTy, tyToks t ≠ []
  | .ftvar _ => by simp [tyToks]
  | .bitvec _ => by simp [tyToks]
  | .tcons c args => by unfold tyToks; split <;> simp

/-- A nonempty list of types has at least one token. -/
private theorem tysToks_ne_nil {t : Lambda.LMonoTy} {ts : List Lambda.LMonoTy} :
    tysToks (t :: ts) ≠ [] := by
  simp only [tysToks, ne_eq, List.append_eq_nil_iff, not_and]
  intro h; exact absurd h (tyToks_ne_nil t)

mutual
/-- A mangled type is its tokens joined with `#`. -/
private theorem mangleTy_toList : ∀ t : Lambda.LMonoTy, (mangleTy t).toList = joinH (tyToks t)
  | .ftvar a => by simp [mangleTy, tyToks, joinH, escName_toList]
  | .bitvec n => by simp [mangleTy, tyToks, joinH, monoDelim, String.toList_append]
  | .tcons c args => by
    unfold mangleTy tyToks
    split
    · simp [joinH, escName_toList]
    · rename_i hne
      obtain ⟨a, as, rfl⟩ : ∃ a as, args = a :: as := by
        cases args with
        | nil => simp at hne
        | cons a as => exact ⟨a, as, rfl⟩
      have hj := mangleTyArgs_toList (a :: as)
      simp only [String.toList_append, monoDelim, List.append_assoc, hj, escName_toList]
      obtain ⟨y, ys, hy⟩ : ∃ y ys, tysToks (a :: as) = y :: ys := by
        cases h : tysToks (a :: as) with
        | nil => exact absurd h tysToks_ne_nil
        | cons y ys => exact ⟨y, ys, rfl⟩
      rw [hy] at hj ⊢
      simp [joinH]
/-- A mangled nonempty list of types is its tokens joined with `#`. -/
private theorem mangleTyArgs_toList : ∀ ts : List Lambda.LMonoTy,
    (mangleTyArgs ts).toList = joinH (tysToks ts)
  | [] => by simp [mangleTyArgs, tysToks, joinH]
  | t :: ts => by
    unfold mangleTyArgs
    split
    · rename_i h
      have : ts = [] := List.isEmpty_iff.mp h
      subst this
      simp [tysToks, mangleTy_toList t]
    · rename_i h
      obtain ⟨a, as, rfl⟩ : ∃ a as, ts = a :: as := by
        cases ts with
        | nil => simp at h
        | cons a as => exact ⟨a, as, rfl⟩
      simp only [String.toList_append, monoDelim, List.append_assoc, mangleTy_toList t,
        mangleTyArgs_toList (a :: as)]
      have h2 := joinH_append (tyToks_ne_nil t) (tysToks_ne_nil (t := a) (ts := as))
      simp only [tysToks] at h2 ⊢
      rw [h2]; simp
end

/-- Two lists without `#`, each followed by `#`, are equal when the whole lists are. -/
theorem prefix_hash_unique :
    ∀ {a a' b b' : List Char}, '#' ∉ a → '#' ∉ a' → a ++ '#' :: b = a' ++ '#' :: b' → a = a'
  | [], [], _, _, _, _, _ => rfl
  | [], c :: _, _, _, _, h', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h'
  | c :: _, [], _, _, h, _, hh => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hh
    exact absurd (hh.1 ▸ List.mem_cons_self) h
  | c :: a, c' :: a', b, b', h, h', hh => by
    simp only [List.cons_append, List.cons.injEq] at hh
    obtain ⟨rfl, hh⟩ := hh
    rw [prefix_hash_unique (fun hm => h (List.mem_cons_of_mem _ hm))
      (fun hm => h' (List.mem_cons_of_mem _ hm)) hh]

/-- Tokens without `#` are read back from their join. -/
private theorem joinH_inj : ∀ {L L' : List (List Char)}, L ≠ [] → L' ≠ [] →
    (∀ x ∈ L, '#' ∉ x) → (∀ x ∈ L', '#' ∉ x) → joinH L = joinH L' → L = L'
  | [], _, h, _, _, _, _ => absurd rfl h
  | _, [], _, h, _, _, _ => absurd rfl h
  | [x], [y], _, _, _, _, he => by simpa [joinH] using he
  | [x], y :: y' :: ys, _, _, hx, _, he => by
    simp only [joinH] at he
    exact absurd (he ▸ List.mem_append_right _ List.mem_cons_self) (hx x List.mem_cons_self)
  | x :: x' :: xs, [y], _, _, _, hy, he => by
    simp only [joinH] at he
    exact absurd (he ▸ List.mem_append_right _ List.mem_cons_self) (hy y List.mem_cons_self)
  | x :: x' :: xs, y :: y' :: ys, _, _, hx, hy, he => by
    simp only [joinH] at he
    have hxy := prefix_hash_unique (hx x List.mem_cons_self) (hy y List.mem_cons_self) he
    subst hxy
    have hrest := List.append_cancel_left he
    simp only [List.cons.injEq, true_and] at hrest
    have := joinH_inj (L := x' :: xs) (L' := y' :: ys) (by simp) (by simp)
      (fun z hz => hx z (List.mem_cons_of_mem _ hz)) (fun z hz => hy z (List.mem_cons_of_mem _ hz))
      (by simpa [joinH] using hrest)
    rw [this]

/-- A list of tokens that is empty or starts with a token that is not a numeral. -/
@[expose] def NotNumHead (r : List (List Char)) : Prop := ∀ x rest, r = x :: rest → ¬ IsNum x

/-- A natural number prints as a numeral. -/
private theorem isNum_toString (n : Nat) : IsNum (toString n).toList := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]
  exact ⟨Nat.toDigits_ne_nil, fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc⟩

/-- Printing natural numbers is injective. -/
private theorem toString_toList_inj {n m : Nat} (h : (toString n).toList = (toString m).toList) :
    n = m := by
  rw [Nat.toString_eq_repr, Nat.toList_repr, Nat.toString_eq_repr, Nat.toList_repr] at h
  have := congrArg (fun l => Nat.ofDigitChars 10 l 0) h
  simpa using this

/-- A printed natural number has no `#`. -/
private theorem hash_not_mem_toString (n : Nat) : '#' ∉ (toString n).toList := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]
  intro h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this; decide

/-- The first token of a variable is not the first token of an escaped name. -/
private theorem escNameL_ne_var (s a : String) : escNameL s ≠ '?' :: 'v' :: escNameL a := by
  unfold escNameL; split
  · simp
  · intro h
    cases hs : s.toList with
    | nil => rw [hs] at h; simp [escBody] at h
    | cons c r =>
      rw [hs] at h
      simp only [escBody, List.flatMap_cons] at h
      by_cases h1 : c = '?'
      · subst h1; simp [escChar] at h
      by_cases h2 : c = '#'
      · subst h2; simp [escChar] at h
      rw [escChar_plain h1 h2] at h
      simp only [List.singleton_append, List.cons.injEq] at h
      exact h1 h.1

/-- A type's tokens, followed by tokens that do not start with a numeral, do not start with one. -/
private theorem notNumHead_tyToks (t : Lambda.LMonoTy) (r : List (List Char)) :
    NotNumHead (tyToks t ++ r) := by
  intro x rest he
  cases t with
  | ftvar a =>
    simp only [tyToks, List.cons_append, List.cons.injEq] at he
    rw [← he.1]; intro ⟨_, hd⟩; exact absurd (hd '?' (by simp)) (by decide)
  | bitvec n =>
    simp only [tyToks, List.cons_append, List.cons.injEq] at he
    rw [← he.1]; intro ⟨_, h⟩; exact absurd (h '$' (by decide)) (by decide)
  | tcons c args =>
    unfold tyToks at he
    split at he <;>
    · simp only [List.cons_append, List.cons.injEq] at he
      rw [← he.1]; exact fun h => escNameL_not_num c h.2

/-- A list of types' tokens, followed by tokens that do not start with a numeral, do not start with one. -/
private theorem notNumHead_tysToks : ∀ (ts : List Lambda.LMonoTy) {r : List (List Char)},
    NotNumHead r → NotNumHead (tysToks ts ++ r)
  | [], _, hr => by simpa [tysToks] using hr
  | t :: ts, r, _ => by
    simp only [tysToks, List.append_assoc]
    exact notNumHead_tyToks t _

mutual
/-- **The tokens of a type read back**, followed by tokens that do not start with a
    numeral. -/
private theorem toks_prefix : ∀ (t t' : Lambda.LMonoTy) (r r' : List (List Char)),
    tyToks t ++ r = tyToks t' ++ r' → NotNumHead r → NotNumHead r' → t = t' ∧ r = r'
  | .ftvar a, .ftvar a', r, r', he, _, _ => by
    simp only [tyToks, List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
    exact ⟨by rw [escNameL_inj he.1], he.2⟩
  | .ftvar a, .bitvec n, _, _, he, _, _ => by simp [tyToks] at he
  | .bitvec n, .ftvar a, _, _, he, _, _ => by simp [tyToks] at he
  | .ftvar a, .tcons c args, r, r', he, _, _ => by
    unfold tyToks at he
    split at he <;>
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1.symm (escNameL_ne_var c a)
  | .tcons c args, .ftvar a, r, r', he, _, _ => by
    unfold tyToks at he
    split at he <;>
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1 (escNameL_ne_var c a)
  | .bitvec n, .bitvec n', r, r', he, _, _ => by
    simp only [tyToks, List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
    exact ⟨by rw [toString_toList_inj he.1], he.2⟩
  | .bitvec n, .tcons c args, r, r', he, _, _ => by
    unfold tyToks at he
    split at he <;>
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1.symm (escNameL_ne_bv c)
  | .tcons c args, .bitvec n, r, r', he, _, _ => by
    unfold tyToks at he
    split at he <;>
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at he
      exact absurd he.1 (escNameL_ne_bv c)
  | .tcons c args, .tcons c' args', r, r', he, hr, hr' => by
    unfold tyToks at he
    by_cases ha : args.isEmpty <;> by_cases ha' : args'.isEmpty <;>
      simp only [ha, ha', ↓reduceIte, List.cons_append, List.cons.injEq,
        Bool.false_eq_true] at he
    · have h1 : c = c' := escNameL_inj he.1
      rw [List.isEmpty_iff.mp ha, List.isEmpty_iff.mp ha', h1]
      exact ⟨rfl, he.2⟩
    · exact absurd (isNum_toString _) (hr _ _ he.2)
    · exact absurd (isNum_toString _) (hr' _ _ he.2.symm)
    · have h1 : c = c' := escNameL_inj he.1
      have h2 := toString_toList_inj he.2.1
      obtain ⟨h3, h4⟩ := toksList_prefix args args' r r' h2 he.2.2 hr hr'
      subst h1 h3
      exact ⟨rfl, h4⟩
/-- **The tokens of equally many types read back**, followed by tokens that do not start
    with a numeral. -/
private theorem toksList_prefix : ∀ (ts ts' : List Lambda.LMonoTy) (r r' : List (List Char)),
    ts.length = ts'.length → tysToks ts ++ r = tysToks ts' ++ r' → NotNumHead r →
    NotNumHead r' → ts = ts' ∧ r = r'
  | [], [], r, r', _, he, _, _ => ⟨rfl, by simpa [tysToks] using he⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | t :: ts, t' :: ts', r, r', hl, he, hr, hr' => by
    simp only [tysToks, List.append_assoc] at he
    obtain ⟨rfl, he2⟩ := toks_prefix t t' _ _ he (notNumHead_tysToks ts hr)
      (notNumHead_tysToks ts' hr')
    obtain ⟨rfl, h4⟩ := toksList_prefix ts ts' r r' (by simpa using hl) he2 hr hr'
    exact ⟨rfl, h4⟩
end

mutual
/-- No token of a type has `#`. -/
private theorem hash_not_mem_tyToks : ∀ (t : Lambda.LMonoTy), ∀ x ∈ tyToks t, '#' ∉ x
  | .ftvar a, x, hx => by
    simp only [tyToks, List.mem_singleton] at hx; subst hx
    simpa using hash_not_mem_escNameL a
  | .bitvec n, x, hx => by
    simp only [tyToks, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · decide
    · exact hash_not_mem_toString n
  | .tcons c args, x, hx => by
    unfold tyToks at hx
    split at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hash_not_mem_escNameL c
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hash_not_mem_escNameL c
      · exact hash_not_mem_toString _
      · exact hash_not_mem_tysToks args x hx
/-- No token of a list of types has `#`. -/
private theorem hash_not_mem_tysToks : ∀ (ts : List Lambda.LMonoTy), ∀ x ∈ tysToks ts, '#' ∉ x
  | [], x, hx => by simp [tysToks] at hx
  | t :: ts, x, hx => by
    simp only [tysToks, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hash_not_mem_tyToks t x hx
    · exact hash_not_mem_tysToks ts x hx
end

end MangleInj

/-- Every name of `N` is at most as long as the longest. -/
private theorem length_le_foldr_max {N : List String} {n : String} (h : n ∈ N) :
    n.length ≤ N.foldr (fun n m => max n.length m) 0 := by
  induction N with
  | nil => cases h
  | cons a N ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- **No name the copies avoid starts with the copies' prefix and `#`.** -/
theorem choosePrefix_fresh (N : List String) :
    ∀ n ∈ N, ¬ (choosePrefix N ++ monoDelim).toList <+: n.toList := by
  intro n hn hp
  unfold choosePrefix at hp
  split at hp
  · have hlen := hp.length_le
    simp only [String.toList_append, List.length_append, String.toList_ofList,
      List.length_replicate, String.length_toList] at hlen
    have hlfm := length_le_foldr_max hn
    simp [monoDelim, monoPrefix] at hlen
    omega
  · rename_i hno
    refine hno (List.any_eq_true.mpr ⟨n, hn, List.isPrefixOf_iff_prefix.mpr ?_⟩)
    exact (List.prefix_append _ _).trans (by simpa [String.toList_append] using hp)

/-- The copies' prefix starts with `monoPrefix`. -/
theorem monoPrefix_prefix_choosePrefix (N : List String) :
    monoPrefix.toList <+: (choosePrefix N).toList := by
  unfold choosePrefix
  split
  · simp [String.toList_append]
  · exact List.prefix_refl _

/-- **With the plain prefix, no name the copies avoid starts with it**, so decoding a name
    that starts with `monoPrefix#` never reads an input name as a copy. -/
private theorem not_prefix_of_choosePrefix_eq {N : List String} (h : choosePrefix N = monoPrefix) :
    ∀ n ∈ N, ¬ monoPrefix.toList <+: n.toList := by
  intro n hn hp
  unfold choosePrefix at h
  split at h
  · have := congrArg String.length h
    simp [monoPrefix] at this
  · rename_i hno
    exact hno (List.any_eq_true.mpr ⟨n, hn, List.isPrefixOf_iff_prefix.mpr hp⟩)

/-- `mangleFuncName` gives `copyName`, whatever its cache. -/
theorem mangleFuncName_fst (pfx : String) (c : Strata.PtrCache.PtrCache mangleTy) (f : String)
    (ts : List Lambda.LMonoTy) : (mangleFuncName pfx c f ts).1 = ⟨copyName pfx f ts, ()⟩ := by
  unfold mangleFuncName copyName
  split
  · rfl
  · generalize (mangleTyArgsPtrCache ts).run c = r
    obtain ⟨⟨out, hout⟩, c'⟩ := r
    simp [hout]

/-- Reading up to the first `#` of `l ++ '#' :: r` gives `l` when `l` has no `#`. -/
private theorem takeWhile_not_hash_of_not_mem {l : List Char} (h : '#' ∉ l) (r : List Char) :
    (l ++ '#' :: r).takeWhile (· != '#') = l := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.mem_cons, not_or] at h
    simp [Ne.symm h.1, ih h.2]

/-- **Decoding undoes encoding**: the name of a copy reads back as its base and the mangled
    instantiation. -/
theorem demangleFuncName_copyName (pfx f : String) {ts : List Lambda.LMonoTy} (h : ts ≠ []) :
    demangleFuncName pfx (copyName pfx f ts) = some (f, mangleTyArgs ts) := by
  have hne : ts.isEmpty = false := by cases ts <;> simp_all
  have hpre : (pfx ++ monoDelim).toList.isPrefixOf (copyName pfx f ts).toList = true := by
    simp [copyName, hne, String.toList_append, List.isPrefixOf_iff_prefix, monoDelim]
  simp only [demangleFuncName, hpre, ↓reduceIte, Option.some.injEq]
  have hdrop : (copyName pfx f ts).toList.drop (pfx ++ monoDelim).toList.length =
      (escName f).toList ++ '#' :: (mangleTyArgs ts).toList := by
    simp [copyName, hne, String.toList_append, monoDelim]
  rw [hdrop, takeWhile_not_hash_of_not_mem (hash_not_mem_escName f)]
  simp [decName_escName]

/-- **A name that does not start with the prefix is not a copy.** -/
theorem demangleFuncName_of_not_prefix {pfx n : String}
    (h : ¬ (pfx ++ monoDelim).toList <+: n.toList) : demangleFuncName pfx n = none := by
  simp only [demangleFuncName]
  split
  · rename_i hp; exact absurd (List.isPrefixOf_iff_prefix.mp hp) h
  · rfl

/-- The tokens of a list of types read back from their concatenation, whatever its length. -/
private theorem tysToks_inj : ∀ (ts us : List Lambda.LMonoTy), tysToks ts = tysToks us → ts = us
  | [], [], _ => rfl
  | [], u :: us, h => absurd h.symm tysToks_ne_nil
  | t :: ts, [], h => absurd h tysToks_ne_nil
  | t :: ts, u :: us, h => by
    simp only [tysToks] at h
    obtain ⟨rfl, hr⟩ := toks_prefix t u _ _ h
      (by simpa using notNumHead_tysToks ts (r := []) (fun _ _ h => by cases h))
      (by simpa using notNumHead_tysToks us (r := []) (fun _ _ h => by cases h))
    rw [tysToks_inj ts us hr]

/-- **Mangling is injective on nonempty lists of types**, of any lengths. -/
theorem mangleTyArgs_inj {ts us : List Lambda.LMonoTy} (hts : ts ≠ []) (hus : us ≠ [])
    (he : mangleTyArgs ts = mangleTyArgs us) : ts = us := by
  have hj := congrArg String.toList he
  rw [mangleTyArgs_toList, mangleTyArgs_toList] at hj
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, ts = t :: rest := by
    cases ts with
    | nil => exact absurd rfl hts
    | cons t rest => exact ⟨t, rest, rfl⟩
  obtain ⟨u, rest', rfl⟩ : ∃ t rest, us = t :: rest := by
    cases us with
    | nil => exact absurd rfl hus
    | cons t rest => exact ⟨t, rest, rfl⟩
  exact tysToks_inj _ _ (joinH_inj tysToks_ne_nil tysToks_ne_nil (hash_not_mem_tysToks _)
    (hash_not_mem_tysToks _) hj)

/-- **Copies are named apart**: two copies with the same prefix and the same name are copies of
    the same function at the same instantiation. -/
theorem copyName_inj {pfx f g : String} {ts us : List Lambda.LMonoTy} (hts : ts ≠ [])
    (hus : us ≠ []) (he : copyName pfx f ts = copyName pfx g us) : f = g ∧ ts = us := by
  have h1 := demangleFuncName_copyName pfx f hts
  rw [he, demangleFuncName_copyName pfx g hus] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, mangleTyArgs_inj hts hus h1.2.symm⟩

/-- **Copies are named apart from every name the prefix avoids**: no name of `N` starts with
    `choosePrefix N`, so none is the name of a copy at a nonempty instantiation. -/
theorem copyName_ne_of_mem {N : List String} {n f : String} {ts : List Lambda.LMonoTy}
    (hn : n ∈ N) (hts : ts ≠ []) : copyName (choosePrefix N) f ts ≠ n := by
  intro he
  apply choosePrefix_fresh N n hn
  rw [← he]
  have hne : ts.isEmpty = false := by cases ts <;> simp_all
  simp [copyName, hne, String.toList_append]

end

end Core.NameMangling

namespace Core.FreshPlainName

public section

/-- **`sanitize` leaves no `#`.** -/
theorem sanitize_noHash (n : String) : '#' ∉ (sanitize n).toList := by
  have hd : NameMangling.monoDelim.toList = ['#'] := by decide
  simp only [sanitize, hd, List.mem_singleton, String.toList_map, List.mem_map, not_exists,
    not_and]
  intro c _ h
  by_cases hc : c = '#' <;> simp_all

end

end Core.FreshPlainName

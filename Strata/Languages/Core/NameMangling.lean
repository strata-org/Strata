/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTy
public import Strata.Util.PtrCache
public import Strata.Languages.Core.Identifiers

/-! # Monomorphized-function name mangling and demangling

The `MonomorphizeFunctions` pass specializes each polymorphic function once per
distinct ground type instantiation and renames every reference to the
specialized copy.  The specialized name is: `$__mono#<funcname>#<typemangle>`.
-/

namespace Core.NameMangling

public section

open Strata.PtrCache

/-- Reserved prefix marking a monomorphized function name.  All internal
    delimiters between parts of a mangled name use `#`. The prefix keeps the leading
    `$__` reservation convention that other internal names in the codebase
    already use. -/
@[expose] def monoPrefix : String := "$__mono"

/-- Delimiter between parts of a mangled name.  See `monoPrefix` for the
    identifier-alphabet argument. -/
@[expose] def monoDelim : String := "#"

/-! ### Type mangling -/

mutual
/-- Encode a monotype as an identifier-safe string.  Only intended to be used for ground
    monotypes (variable-free); the `.ftvar` case returns the type-variable's
    name as a best-effort placeholder.

    Every internal separator is `#` (per `monoDelim`).  A non-empty `.tcons` also includes its arg
    count so the mangled name is self-descriptive for the reader; the arity
    prefix is documentary rather than disambiguating, since a datatype's
    arity is fixed at declaration.

    `.bitvec n` is mangled as `$bv#<n>` to avoid colliding with a user-declared
    nullary type spelled `bv<n>` (e.g. `type bv8;`, which mangles to `bv8`). -/
@[expose] def mangleTy : Lambda.LMonoTy → String
  | .ftvar a => a
  | .bitvec n => "$bv" ++ monoDelim ++ toString n
  | .tcons c args =>
    if args.isEmpty then c
    else c ++ monoDelim ++ toString args.length ++ monoDelim ++ mangleTyArgs args

@[expose] def mangleTyArgs : List Lambda.LMonoTy → String
  | [] => ""
  | t :: ts => if ts.isEmpty then mangleTy t else mangleTy t ++ monoDelim ++ mangleTyArgs ts
end

mutual
/-- Pointer-address-memoized `mangleTy`: each physically distinct monotype is
    mangled exactly once, keyed by its memory address via the safe `PtrCache`.
    The returned `Result mangleTy ty` proves the value equals `mangleTy ty`. -/
def mangleTyPtrCache : (ty : Lambda.LMonoTy) → PtrCacheM mangleTy ty
  | .ftvar a => pure ⟨a, by simp only [mangleTy]⟩
  | .bitvec n => pure ⟨"$bv" ++ monoDelim ++ toString n, by simp only [mangleTy]⟩
  | .tcons c args => do
    let rs ← mangleTyArgsPtrCache args
    pure ⟨if args.isEmpty then c
          else c ++ monoDelim ++ toString args.length ++ monoDelim ++ rs.output,
          by simp only [mangleTy, rs.h]⟩
/-- `mangleTyArgs` threaded through the same `PtrCache mangleTy`. -/
def mangleTyArgsPtrCache :
    (args : List Lambda.LMonoTy) → StateM (PtrCache mangleTy) (Result mangleTyArgs args)
  | [] => pure ⟨"", by simp only [mangleTyArgs]⟩
  | t :: ts => do
    let rt ← evalPtrCache t (mangleTyPtrCache t)
    let rts ← mangleTyArgsPtrCache ts
    pure ⟨if ts.isEmpty then rt.output else rt.output ++ monoDelim ++ rts.output,
          by simp only [mangleTyArgs, rt.h, rts.h]⟩
end

/-! ### Function-name mangling -/

/-- The specialized `CoreIdent` for a polymorphic-function reference with base
    name `funcname` at instantiation `givenTypes`, threading a `PtrCache mangleTy`
    so a type's mangled string is reused across calls.  A nullary instantiation
    (`givenTypes = []`) returns the base name unchanged. -/
@[expose] def mangleFuncName (cache : Strata.PtrCache.PtrCache mangleTy)
    (funcname : String) (givenTypes : List Lambda.LMonoTy) :
    Core.CoreIdent × Strata.PtrCache.PtrCache mangleTy :=
  if givenTypes.isEmpty then
    (⟨funcname, ()⟩, cache)
  else
    let (r, cache) := (mangleTyArgsPtrCache givenTypes).run cache
    (⟨monoPrefix ++ monoDelim ++ funcname ++ monoDelim ++ r.output, ()⟩, cache)

/-! ### Demangling -/

/-- Split a mangled monomorphized name back into `(basename, typemangle)`.
    Returns `none` if `name` doesn't start with the `$__mono#` prefix.

    The base name is the substring between the first two `#` delimiters
    (`$__mono#<base>#…`); the typemangle is everything after the second `#`
    (or empty, for a nullary instantiation). -/
@[expose] def demangleFuncName (name : String) : Option (String × String) :=
  let fullPrefix := monoPrefix ++ monoDelim
  if !name.startsWith fullPrefix then none
  else
    let rest := (name.drop fullPrefix.length).toString
    -- Split at the first `#`.  `funcname` never contains `#` (not a legal
    -- Strata ident char), so any additional `#` chars belong to the
    -- typemangle.
    match rest.splitOn monoDelim with
    | [] => none
    | [base] => some (base, "")
    | base :: parts => some (base, monoDelim.intercalate parts)

/-- Recover just the base function name from a mangled monomorphized name.
    Returns `name` unchanged if it isn't a mangled name. -/
@[expose] def demangledBaseName (name : String) : String :=
  match demangleFuncName name with
  | some (base, _) => base
  | none => name

end

end Core.NameMangling

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

/-- `s` contains a character of `monoDelim`. `MonomorphizeFunctions` rejects any program
    with such a name, so a mangled name is never mistaken for an input name or vice versa.
    Defined over `s.toList`, so proofs can use list lemmas; `String.any` has none relating
    it to `toList`. -/
@[expose] def hasMonoDelim (s : String) : Bool := s.toList.any (· ∈ monoDelim.toList)

/-! ### Escaping a name inside a mangled name

A name written into a mangled name is escaped so that it contains no `#`, is not a numeral
and is not `$bv`. The escape character `?` is one SMT-LIB symbols carry as themselves, except
first, which a token inside a mangled name never is (`Strata.SMT.Symbol.Chars.smtMustEscape`).
Then the tokens of a mangled name read back in one way, whatever names the program uses.
`?` becomes `??` and `#` becomes `?h`; a name that is empty, a numeral or `$bv` is marked with
a leading `?n`. Every other name is written as is. -/

/-- The characters that escape `x`. -/
@[expose] def escChar : Char → List Char
  | '?' => ['?', '?']
  | '#' => ['?', 'h']
  | x => [x]

/-- `s` with `?` and `#` escaped. -/
@[expose] def escBody (s : List Char) : List Char := s.flatMap escChar

/-- `s` would read as an arity, a width or `$bv`, or is empty. -/
@[expose] def needsMark (s : List Char) : Bool :=
  s.isEmpty || s.all Char.isDigit || s == "$bv".toList

/-- The characters of the escaped form of `s`. -/
@[expose] def escNameL (s : String) : List Char :=
  if needsMark s.toList then '?' :: 'n' :: escBody s.toList else escBody s.toList

/-- The escaped form of `s`. -/
@[expose] def escName (s : String) : String := String.ofList (escNameL s)

/-- Undo `escBody`. -/
@[expose] def unescL : List Char → List Char
  | '?' :: '?' :: r => '?' :: unescL r
  | '?' :: 'h' :: r => '#' :: unescL r
  | x :: r => x :: unescL r
  | [] => []

/-- Undo `escNameL`. -/
@[expose] def decNameL : List Char → List Char
  | '?' :: 'n' :: r => unescL r
  | l => unescL l

/-- Undo `escName`: the name the user wrote. -/
@[expose] def decName (s : String) : String := String.ofList (decNameL s.toList)

/-- Prefix of the functions `lambdaLift` declares for lifted lambdas. Names starting
    with `$__` are meant for internal use. The parser does not refuse them, so a
    program can declare `$__lam_0` itself; a lifted function of the same name is then
    refused as a redefinition, which fails closed. -/
@[expose] def liftedLambdaPrefix : String := "$__lam"

/-- Reserved prefix of the constant array the SMT encoder gives a function
    used as a value, `$__fn#f`. -/
@[expose] def fnValuePrefix : String := "$__fn"

/-! ### Type mangling -/

mutual
/-- Encode a monotype as an identifier-safe string.  Only intended to be used for ground
    monotypes (variable-free); the `.ftvar` case writes the type-variable's escaped name
    after `?v`, which no escaped name starts with.

    Every internal separator is `#` (per `monoDelim`).  A non-empty `.tcons` also includes its arg
    count so the mangled name is self-descriptive for the reader; the arity
    prefix is documentary rather than disambiguating, since a datatype's
    arity is fixed at declaration.

    `.bitvec n` is mangled as `$bv#<n>` to avoid colliding with a user-declared
    nullary type spelled `bv<n>` (e.g. `type bv8;`, which mangles to `bv8`). -/
@[expose] def mangleTy : Lambda.LMonoTy → String
  | .ftvar a => "?v" ++ escName a
  | .bitvec n => "$bv" ++ monoDelim ++ toString n
  | .tcons c args =>
    if args.isEmpty then escName c
    else escName c ++ monoDelim ++ toString args.length ++ monoDelim ++ mangleTyArgs args

@[expose] def mangleTyArgs : List Lambda.LMonoTy → String
  | [] => ""
  | t :: ts => if ts.isEmpty then mangleTy t else mangleTy t ++ monoDelim ++ mangleTyArgs ts
end

mutual
/-- Pointer-address-memoized `mangleTy`: each physically distinct monotype is
    mangled exactly once, keyed by its memory address via the safe `PtrCache`.
    The returned `Result mangleTy ty` proves the value equals `mangleTy ty`. -/
def mangleTyPtrCache : (ty : Lambda.LMonoTy) → PtrCacheM mangleTy ty
  | .ftvar a => pure ⟨"?v" ++ escName a, by simp only [mangleTy]⟩
  | .bitvec n => pure ⟨"$bv" ++ monoDelim ++ toString n, by simp only [mangleTy]⟩
  | .tcons c args => do
    let rs ← mangleTyArgsPtrCache args
    pure ⟨if args.isEmpty then escName c
          else escName c ++ monoDelim ++ toString args.length ++ monoDelim ++ rs.output,
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

/-- The type constructor names in `ty`, which `mangleTy` writes into a mangled name. -/
@[expose] def tconsNames : Lambda.LMonoTy → List String
  | .ftvar _ => []
  | .bitvec _ => []
  | .tcons c args => c :: tconsNamesList args
where
  tconsNamesList : List Lambda.LMonoTy → List String
    | [] => []
    | t :: ts => tconsNames t ++ tconsNamesList ts

/-! ### The prefix of the copies' names

A copy's name is `P#<escaped base>#<types>`. `P` is `monoPrefix` unless a name the copies must
avoid starts with `monoPrefix`; then `P` is `monoPrefix` padded with `_` past the longest of
those names, so none of them starts with `P#`. Either way no name is rejected or renamed.
With the plain prefix no input name starts with `monoPrefix`, so `demangleFuncName` decodes
copies only; with the padded one it decodes none, and a report shows the copy's name as is. -/

/-- The prefix of the copies' names, given the names `N` they must avoid. -/
@[expose] def choosePrefix (N : List String) : String :=
  if N.any (fun n => monoPrefix.toList.isPrefixOf n.toList) then
    monoPrefix ++ String.ofList (List.replicate (N.foldr (fun n m => max n.length m) 0 + 1) '_')
  else monoPrefix

/-! ### Function-name mangling

`copyName pfx f ts` is the name of the copy of `f` at the instantiation `ts`, with the
copies' prefix `pfx`: `pfx#<escaped f>#<types>`. `mangleFuncName` builds it, threading a
cache of mangled types; `demangleFuncName` reads it back. These are the only functions that
build or read a copy's name. -/

/-- **The name of the copy of `f` at `ts`**, with prefix `pfx`. A nullary instantiation is
    `f` itself. -/
@[expose] def copyName (pfx f : String) (ts : List Lambda.LMonoTy) : String :=
  if ts.isEmpty then f else pfx ++ monoDelim ++ escName f ++ monoDelim ++ mangleTyArgs ts

/-- The specialized `CoreIdent` for a polymorphic-function reference with base
    name `funcname` at instantiation `givenTypes`, with the copies' prefix `pfx`, threading a
    `PtrCache mangleTy` so a type's mangled string is reused across calls. It is
    `copyName pfx funcname givenTypes` (`mangleFuncName_fst`). -/
@[expose] def mangleFuncName (pfx : String) (cache : Strata.PtrCache.PtrCache mangleTy)
    (funcname : String) (givenTypes : List Lambda.LMonoTy) :
    Core.CoreIdent × Strata.PtrCache.PtrCache mangleTy :=
  if givenTypes.isEmpty then
    (⟨funcname, ()⟩, cache)
  else
    let (r, cache) := (mangleTyArgsPtrCache givenTypes).run cache
    (⟨pfx ++ monoDelim ++ escName funcname ++ monoDelim ++ r.output, ()⟩, cache)

/-! ### Demangling -/

/-- Split the name of a copy back into `(base, typemangle)`, given the copies' prefix `pfx`:
    `none` unless `name` is `pfx#` followed by the escaped base, then the typemangle after the
    next `#` (empty if there is none). The base comes back decoded (`decName`). A name that does
    not start with `pfx#` is never read as a copy, so a user's name that only looks like a copy
    under another prefix is left as written. -/
@[expose] def demangleFuncName (pfx : String) (name : String) : Option (String × String) :=
  let full := (pfx ++ monoDelim).toList
  if full.isPrefixOf name.toList then
    let rest := name.toList.drop full.length
    let base := rest.takeWhile (· != '#')
    some (decName (String.ofList base), String.ofList (rest.drop (base.length + 1)))
  else none

/-- The base of a copy's name under the prefix `pfx`, and any other name as it is. -/
@[expose] def demangledBaseName (pfx : String) (name : String) : String :=
  match demangleFuncName pfx name with
  | some (base, _) => base
  | none => name

/-- The prefix of `name` if `name` has the shape of a copy's name under some prefix
    `choosePrefix` can choose: its part before the first `#`, when that is `monoPrefix`
    followed by underscores only. -/
@[expose] def copyPrefixOf? (name : String) : Option String :=
  let lead := name.toList.takeWhile (· != '#')
  if monoPrefix.toList.isPrefixOf lead && (lead.drop monoPrefix.length).all (· == '_') then
    some (String.ofList lead)
  else none

/-- `demangleFuncName` under any prefix `choosePrefix` can choose: for readers that do not know
    which prefix was chosen. -/
@[expose] def demangleFuncNameAnyPrefix (name : String) : Option (String × String) :=
  (copyPrefixOf? name).bind fun pfx => demangleFuncName pfx name

/-- The base of a name of a copy's shape under any prefix `choosePrefix` can choose, and any
    other name as it is. -/
@[expose] def demangledBaseNameAnyPrefix (name : String) : String :=
  match demangleFuncNameAnyPrefix name with
  | some (base, _) => base
  | none => name

end

end Core.NameMangling

/-! ## Sanitizing a name for a generated one

`Core.FreshPlainName.sanitize` replaces each character of `Core.NameMangling.monoDelim` (`#`) by
`_`, so a name generated from a label goes through `sanitize`: a `#` the user wrote is renamed
away in the generated name rather than rejected. -/

namespace Core.FreshPlainName

public section

/-- `n` with each character of `NameMangling.monoDelim` replaced by `_`. -/
@[expose] def sanitize (n : String) : String :=
  n.map fun c => if c ∈ NameMangling.monoDelim.toList then '_' else c

end

end Core.FreshPlainName

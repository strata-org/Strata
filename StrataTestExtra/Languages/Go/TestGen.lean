/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Every module below is imported twice, `meta` and plain, and both forms are
-- needed. The `elab` commands run at meta time; the `#eval`s run at meta time too
-- but their bodies reference plain definitions from this file (the derived
-- `Repr`/`BEq` instances, the `getIonDeserializer%` readers), and a `meta`
-- declaration may not reference a non-`meta` one from the same module. So the
-- IO-heavy tests are `#eval`s over plain helpers, which needs both spellings.
public meta import Lean.Elab.Command
public import Lean.Elab.Command
public meta import Strata.Go.Gen
public import Strata.Go.Gen
public meta import Strata.Go.GoIonRuntime
public import Strata.Go.GoIonRuntime
public meta import Strata.Util.IonDeserializer
public import Strata.Util.IonDeserializer
public meta import StrataTest.Languages.Go.GenTestUtil
public import StrataTest.Languages.Go.GenTestUtil
-- Cases 36/37 parse, decode, print and verify a real `Laurel.LaurelProgram`.
public meta import StrataLaurel.Implementation
public import StrataLaurel.Implementation
public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator

open Strata.Go
open Strata.Go.TestUtil

/-!
# `getIonGoSerializer%` adversarial tests

`StrataTestExtra/Languages/Go/GenSmokeTest.lean` pins one check per emitted
*shape*. This file goes after the ways the Go backend can be wrong without
looking wrong:

* **Naming.** Go's flat package namespace, its case-sensitive reserved words and
  its "exported means capitalised" rule interact; each combination is a way for
  two Lean declarations to land on one Go identifier, or for a generated name to
  shadow the runtime.
* **The wire.** The important assertions are on *what Lean decodes*, not on
  emitted source text or a particular Ion binary layout. This lets ion-go choose
  a valid encoding while still proving that every generated value has the
  schema-specific meaning Strata expects.
* **Cross-package use.** Every round trip below builds the generated package
  under its own import path and drives it from a `package main` in a *different*
  Go package. That is the reason every generated identifier is exported; an
  in-package test cannot establish it.

## Layout

| Section | What it establishes |
|---|---|
| Naming: what must be emitted | the identifier chosen for each escaping and collision rule |
| Wire round trips: Go builds it, Lean decodes it | every emitted shape decodes back to the Lean value it was built from |
| `laurelGoGen`'s `Laurel.LaurelProgram` closure | the package that ships is gofmt-clean, vets, and builds |
| A Go-built `Laurel.LaurelProgram`, decoded and verified | Strata decodes it, agrees it is the reference program, and verifies it |

In local development, checks that need the Go toolchain skip with a warning when
`go` is absent or when ion-go cannot be resolved (see `writeGoModule`), and the
verification verdict skips without an SMT solver, matching how
`StrataTestExtra/Languages/Java/TestGen.lean` skips without `javac`. Brazil
builds provide Go and ion-go through `build-tools` and `brazil-path`, and a CI
run (`CI` set) must install Go; both fail rather than skip, because the test
driver reports only `PASS` and a skip warning would never be seen (see
`goChecksRequired`).
`laurelGoGen` is *not* optional: it is in `defaultTargets` and in
`StrataTestMain`'s `needs`, and silently skipping the end-to-end cases is the
one failure mode that would let a broken M0 look green.

Supporting Go drivers live in `testdata/`. The shared adapter is written out
from `Strata.Go.runtimeFiles` and the generated types from
`getIonGoSerializer%`, every time.
-/

namespace Strata.Go.AdvTest

/-- Elaborate `stx` and return the error message it threw, or `""` on success.

`withoutErrToSorry` is required: `elabTerm` otherwise turns a thrown error into a
logged message plus `sorryAx`, and the `try` block would see success. -/
meta def elabError (stx : Lean.Syntax) : Lean.Elab.Command.CommandElabM String :=
  Lean.Elab.Command.liftTermElabM do
    try
      let _ ← Lean.Elab.Term.withoutErrToSorry (Lean.Elab.Term.elabTerm stx none)
      return ""
    catch e => return (← e.toMessageData.toString)

/-! ## Types under test

Every type here exists to break one rule. The comment on each says which.
-/

structure Point where
  x : Nat
  y : Nat
deriving Repr, BEq

/-- Fields with default values. `classifyFieldType` unwraps `optParam` before
mapping the underlying scalar type. -/
structure WithDefault where
  count : Nat := 7
  label : String := "hi"
deriving Repr, BEq

/-- A scalar with no Go mapping. -/
opaque UnsupportedScalar : Type

/-- An unsupported scalar must stop generation instead of losing its value. -/
structure UnsupportedLeaf where
  value : UnsupportedScalar

/--
Every field-position escaping rule at once, in one struct.

* `type` is a Go keyword, but `toPascalCase` runs *first* and `Type` is a legal
  Go identifier, so nothing is escaped. Asserting that it gets a `_` suffix
  would test a behaviour the generator deliberately does not have.
* `2x` is a legal Lean field name and not a legal Go identifier; it must gain the
  `X` prefix or the file does not compile.
* `a?b`, `ab` and `a"b` all fold to `Ab`, so `disambiguateAll` has to produce
  three distinct idents while all three Ion keys stay the original Lean names.
* `?` and `??` escape to nothing at all and hit the `Field` fallback, which then
  needs disambiguating against itself.
* `a"b` additionally proves the Ion key is emitted as a real Go string literal.
  The Java backend interpolates keys raw and emits uncompilable Java here.
-/
structure Fields where
  «type» : Nat
  «2x» : Nat
  «a?b» : Nat
  ab : Nat
  «a"b» : Nat
  «?» : Nat
  «??» : Nat
deriving Repr, BEq

namespace Reserved

/-- Reserved matching is case-sensitive and happens *after* `toPascalCase`, so
the only type names that actually get escaped are the runtime's own, which are
already PascalCase. These four must become `Decimal_`, `Opt_`, `MarshalBinary_`
and `ToIon_`, or the generated file redeclares a runtime name and the package
does not compile. -/
structure Decimal where
  dv : Nat
deriving Repr, BEq

structure Opt where
  ov : Nat
deriving Repr, BEq

structure MarshalBinary where
  mv : Nat
deriving Repr, BEq

structure ToIon where
  tv : Nat
deriving Repr, BEq

/-- Type-position reserved words as they actually behave: a Lean type named after
a Go keyword or a predeclared identifier PascalCases to something legal and is
left alone.
`Type`, `String`, `Error` and `Len` are all valid, non-shadowing Go type names;
escaping them would be churn. Pinned so a "fix" that escapes them is caught. -/
structure «type» where
  kv : Nat
deriving Repr, BEq

structure «string» where
  sv : Nat
deriving Repr, BEq

structure «error» where
  ev : Nat
deriving Repr, BEq

structure «len» where
  lv : Nat
deriving Repr, BEq

/-- Constructor-struct escaping, which is only observable here: the constructor
struct name is `escapeGoName (goTypeName ++ toPascalCase ctor)`. Escaping the *parts* would
emit `IonWriter`, redeclaring the runtime's writer alias; escaping the
concatenation gives `IonWriter_`. The Ion tag must stay `writer`. -/
inductive Ion where
  | writer (x : Nat)
  | other (y : Nat)
deriving Repr, BEq

end Reserved

/-- One root so the whole reserved-name family shares a package and the
collision registry sees all of it at once. -/
structure ReservedRoot where
  a : Reserved.Decimal
  b : Reserved.Opt
  c : Reserved.MarshalBinary
  d : Reserved.ToIon
  e : Reserved.«type»
  f : Reserved.«string»
  g : Reserved.«error»
  h : Reserved.«len»
deriving Repr, BEq

/-- `myCase` and `my_case` both fold to `MyCase`, so the two constructor
structs would be declared twice. The Ion tags must stay distinct, or the two
constructors become indistinguishable on the wire. -/
inductive CollidingCtors where
  | myCase (x : Nat)
  | my_case (y : Nat)
deriving Repr, BEq

/--
Container nesting in every combination: the shapes the two separate depth
counters in `writeInfo` exist for.

`writeInfo` names its dereferenced-`Option` temporary `_p<optDepth>` and its
range variables `_i<listDepth>`/`_e<listDepth>`. Those counters are what keep a
nested container's temporary from reusing the name its enclosing container
already bound: Go's `:=` in an inner block silently introduces a *new* variable
shadowing the outer one, so a collision is neither a compile error nor a `go
vet` finding, and the emitted source looks right. Only the decoded value shows
that the wrong one was written — which is why these are round trips rather than
substring checks, and why `optOpt` is here even though `some none` and `none`
are the same bytes (see the byte comparison below).
-/
structure Nest where
  maybeEach : List (Option String)
  deepMix : Option (List (Option (List Nat)))
  optOpt : Option (Option String)
  listList : List (List Int)
deriving Repr, BEq

/-! Mutually recursive types. `collectNestedTypes` is a worklist over the
reachable closure; without the `visited` check this does not terminate, and with
a per-type closure each file would be emitted twice. -/
mutual
inductive MExpr where
  | lit (n : Int)
  | neg (e : MExpr)
  | fromStmt (s : MStmt)
inductive MStmt where
  | exprStmt (e : MExpr)
  | seq (l : List MStmt)
end

deriving instance Repr, BEq for MExpr, MStmt

/-- Exercises nil interface values directly, inside a list, and behind Option. -/
structure Nilable where
  value : MExpr
  items : List MExpr
  maybe : Option MExpr

/-- Every leaf type at once, through a generated struct, at the values where a
machine-integer mapping would lose data. `Nat` and
`Int` are arbitrary precision in Lean and map to `*big.Int` in Go, so the
interesting values are on *both* sides of the 64-bit boundaries: `2^64-1` and
`-2^63` for the signedness of a 64-bit port, and `2^64`/`-(2^64)` and beyond for
the range that only `*big.Int` can carry at all. -/
structure Leaves where
  nat : Nat
  int : Int
  flt : Float
  str : String
  bool : Bool
  dec : StrataDDM.Decimal
deriving Repr, BEq

/-- A single-constructor inductive uses positional `_0`/`_1` Ion keys. The
round trip is what distinguishes those from field-name keys; a struct-shaped
encoding with the wrong keys still decodes as *something*. -/
inductive Wrapper where
  | mk (value : Int) (label : String) (flag : Bool)
deriving Repr, BEq

/-- A type parameter at a compound type argument, which is the only place
generics are reachable from `Laurel.LaurelProgram`. -/
structure Box (T : Type) where
  value : T
deriving Repr, BEq

structure BoxRoot where
  b : Box Point
  ob : Option (Box Point)
  lb : List (Box Point)

/-- Monomorphic mirror of `Box Point`. `getIonDeserializer%` takes a bare
identifier, so a generic instantiation cannot be named to it; the mirror pins the
property that actually matters — the Ion encoding of `Box Point` is
indistinguishable from that of the equivalent non-generic structure. Erasing the
type parameter in the Go emitter (e.g. emitting `any` for it) would break this. -/
structure BoxMirror where
  value : Point
deriving Repr, BEq

structure BoxRootMirror where
  b : BoxMirror
  ob : Option BoxMirror
  lb : List BoxMirror
deriving Repr, BEq

/-- A generic applied to a scalar. Its Go type argument would be `*big.Int`,
which has no `MarshalIon`, so `Box[*big.Int]` does not satisfy the `ToIon`
constraint on `Box`'s type parameter and the generated package would not
compile. -/
structure BoxNat where
  b : Box Nat

/-- The same hole behind a `List`: a Go slice has no method set either, so
`Box[[]Point]` is no more constructible than `Box[*big.Int]`. -/
structure BoxListPoint where
  b : Box (List Point)

/-- `Option` of a generated *structure* is `*Point`, which Go would accept: the
generator emits value receivers, so `*Point`'s method set contains
`Point.MarshalIon`. It is rejected anyway, because `Box`'s body writes its
`T`-typed field through `MarshalIon` and cannot tell that this `T` is an
`Option`, so a nil `*Point` would be refused as a nil value instead of written as
the Ion null that `none` means. -/
structure BoxOptPoint where
  b : Box (Option Point)

/-- `Option` of a *multi-constructor* type is `*MExpr`, and `MExpr` is a Go
interface. Go gives a pointer to an interface an empty method set — "pointer to
interface, not interface" — so this is the case that makes `Option` non-
transparent in a type-argument position. -/
structure BoxOptMExpr where
  b : Box (Option MExpr)

/-- `Option (Option Point)` is `**Point`, and a pointer to a pointer has an
empty method set too, so the restriction is about pointer *depth* and not only
about what is underneath. -/
structure BoxOptOptPoint where
  b : Box (Option (Option Point))

/-- `Option` of a *type parameter* is `*T`, which Go rejects as "pointer to type
parameter, not type parameter" even though `T` itself carries the constraint.
Only reachable from inside another generic, which is why this one needs a
wrapper of its own. -/
structure BoxOptParam (T : Type) where
  b : Box (Option T)

/-- Two Lean types differing only in case. Go would accept both, but they
become two files whose names differ only in case, which collide on a
case-insensitive filesystem — so the registry compares case-insensitively. -/
structure Dup where
  n : Nat

structure DUP where
  m : Nat

structure CaseClash where
  a : Dup
  b : DUP

/-! ## Naming: what must be emitted

These are source-text assertions, used only where the property is about the
*identifier chosen* and therefore has no observable behaviour beyond "it
compiles" — which `#testAdversarialRoundTrip` below establishes separately.
-/

-- Field-position escaping, every rule at once. The Ion keys are asserted here
-- too, because a key is chosen at generation time and the round trip only proves
-- the Go and Lean sides agree, not that they agree on the *Lean* field name.
elab "#testFieldEscaping" : command => do
  let content ← fileNamed (getIonGoSerializer% Fields "gotest") "Fields.go"
  -- Asserted as one block: it pins the chosen identifier for each escaping rule
  -- *and* gofmt's column alignment, which a per-field check cannot.
  --   `type`   -> `Type`   (keyword, but PascalCase already makes it legal)
  --   `2x`     -> `X2x`    (a Go identifier cannot start with a digit)
  --   `a?b`/`ab`/`a"b` -> `Ab`/`Ab_`/`Ab_2` (all three fold to `Ab`)
  --   `?`/`??` -> `Field`/`Field_` (escape to nothing; `Field` fallback)
  if !check content "type Fields struct {\n\
                     \tType   *big.Int\n\
                     \tX2x    *big.Int\n\
                     \tAb     *big.Int\n\
                     \tAb_    *big.Int\n\
                     \tAb_2   *big.Int\n\
                     \tField  *big.Int\n\
                     \tField_ *big.Int\n\
                     }" then
    Lean.logError s!"Unexpected field identifiers or alignment:\n{content}"; return
  -- Every Ion key is the original Lean field name, quoted as a real Go literal.
  for key in ["\"type\"", "\"2x\"", "\"a?b\"", "\"ab\"", "\"a\\\"b\"", "\"?\"", "\"??\""] do
    if !check content s!"fieldName(w, {key})" then
      Lean.logError s!"Missing Ion key {key}; keys must be the Lean field names"; return

#testFieldEscaping

-- Type-position reserved words. Two halves, and the second is the one worth
-- having: `Type`/`String`/`Error`/`Len` are already legal exported identifiers,
-- so escaping them would unnecessarily change the generated API.
elab "#testReservedTypeNames" : command => do
  let files := getIonGoSerializer% ReservedRoot "gotest"
  -- Runtime names are PascalCase, so these are the ones that collide.
  for name in ["Decimal_", "Opt_", "MarshalBinary_", "ToIon_"] do
    if !files.files.any (·.1 == s!"{name}.go") then
      Lean.logError s!"A Lean type named after a runtime declaration must be \
                      escaped to {name}"; return
  -- Keywords and predeclared identifiers are lowercase; PascalCasing already
  -- makes them legal, so they are left alone.
  for name in ["Type", "String", "Error", "Len"] do
    if !files.files.any (·.1 == s!"{name}.go") then
      Lean.logError s!"A Lean type named after a Go keyword must PascalCase to \
                      {name} and NOT be escaped"; return
    if files.files.any (·.1 == s!"{name}_.go") then
      Lean.logError s!"{name} is a legal Go type name and must not be escaped"; return
  -- The referring struct must use the escaped names, or it will not compile.
  let root ← fileNamed files "ReservedRoot.go"
  for (fld, ty) in [("A", "Decimal_"), ("B", "Opt_"), ("C", "MarshalBinary_"),
                    ("D", "ToIon_"), ("E", "Type"), ("F", "String")] do
    if !check root s!"{fld} {ty}" then
      Lean.logError s!"ReservedRoot.{fld} must have type {ty}:\n{root}"; return

#testReservedTypeNames

-- Constructor-struct escaping. Escaping the parts rather than the concatenation emits
-- `IonWriter`, which redeclares the runtime alias — the package stops
-- compiling, so this matters for compilation rather than being cosmetic.
elab "#testCtorConcatEscape" : command => do
  let content ← fileNamed (getIonGoSerializer% Reserved.Ion "gotest") "Ion.go"
  if !check content "type IonWriter_ struct{ X *big.Int }" then
    Lean.logError s!"Ctor `writer` of `Ion` must escape to IonWriter_:\n{content}"; return
  if check content "type IonWriter struct" then
    Lean.logError "The generated ctor struct must not redeclare the runtime IonWriter"; return
  -- The tag is a wire-format concern and must not follow the rename.
  if !check content "writeSymbol(w, \"writer\")" then
    Lean.logError "The Ion tag must stay the Lean constructor's short name"; return

#testCtorConcatEscape

-- Colliding constructors. The Go struct names are disambiguated; the Ion tags must not be, or the
-- two constructors become indistinguishable on the wire.
elab "#testCollidingCtors" : command => do
  let content ← fileNamed (getIonGoSerializer% CollidingCtors "gotest") "CollidingCtors.go"
  if !check content "type CollidingCtorsMyCase struct{ X *big.Int }" then
    Lean.logError s!"Missing CollidingCtorsMyCase:\n{content}"; return
  if !check content "type CollidingCtorsMyCase_ struct{ Y *big.Int }" then
    Lean.logError "Colliding ctor must be disambiguated to CollidingCtorsMyCase_"; return
  if !check content "writeSymbol(w, \"myCase\")" then Lean.logError "Missing myCase tag"; return
  if !check content "writeSymbol(w, \"my_case\")" then Lean.logError "Missing my_case tag"; return
  -- Both structs must implement the interface, or only one is usable as a
  -- `CollidingCtors`.
  if !check content "func (CollidingCtorsMyCase) isCollidingCtors() {}" then
    Lean.logError "Missing marker on CollidingCtorsMyCase"; return
  if !check content "func (CollidingCtorsMyCase_) isCollidingCtors() {}" then
    Lean.logError "Missing marker on CollidingCtorsMyCase_"; return

#testCollidingCtors

-- Mutual recursion. A missing `visited` check in `collectNestedTypes` loops forever; a
-- per-type closure emits each file twice. Both are caught by counting files.
elab "#testMutualRecursion" : command => do
  let files := getIonGoSerializer% MExpr "gotest"
  let generated := files.files.filter fun (n, _) =>
    n != "ion_value.go" && n != "ion_binary.go" && n != "opt.go"
  if generated.size != 2 then
    Lean.logError s!"Expected exactly MExpr.go and MStmt.go, got \
                    {generated.map (·.1)}"; return
  let expr ← fileNamed files "MExpr.go"
  let stmt ← fileNamed files "MStmt.go"
  -- The recursion goes through the interface type, not a constructor struct:
  -- `MExprNeg{E: MExprNeg{...}}` would be an infinitely sized Go type.
  if !check expr "type MExprNeg struct{ E MExpr }" then
    Lean.logError s!"Recursion must be through the interface:\n{expr}"; return
  if !check expr "type MExprFromStmt struct{ S MStmt }" then
    Lean.logError "MExpr must reference MStmt"; return
  if !check stmt "type MStmtExprStmt struct{ E MExpr }" then
    Lean.logError "MStmt must reference MExpr"; return

#testMutualRecursion

/-! A constructor struct colliding with an unrelated generated type is covered by
`GenSmokeTest.lean`'s `#testCrossTypeCollision` and is not repeated here.

A Lean type whose Go name matches an `is<Type>` marker method has
its acceptance test in `GenSmokeTest.lean`. The marker is a *method* name, and a
method name is not a package-scope Go identifier — `type IsFoo struct{}` and
`func (FooBar) isFoo()` coexist. -/

-- Two Lean types differing only in case become two files differing only
-- in case; on a case-insensitive filesystem the second silently overwrites the
-- first, so this must be an error rather than a rename.
elab "#testCaseOnlyCollision" : command => do
  let msg ← elabError (← `(getIonGoSerializer% CaseClash "gotest"))
  if msg.isEmpty then
    Lean.logError "Go names differing only in case must be rejected"; return
  if !check msg "DUP" then
    Lean.logError s!"Error must name the colliding Go name: {msg}"; return
  -- Both Lean declarations, so the reader knows which two to rename.
  if !check msg "Dup" then
    Lean.logError s!"Error must name both culprits: {msg}"; return

#testCaseOnlyCollision

-- `optParam` is stripped, so the fields keep their real types instead of
-- degrading to an untyped `any`.
elab "#testDefaultValuedFields" : command => do
  let content ← fileNamed (getIonGoSerializer% WithDefault "gotest") "WithDefault.go"
  if !check content "\tCount *big.Int\n" then
    Lean.logError s!"A `Nat := 7` field must still be *big.Int:\n{content}"; return
  if !check content "\tLabel string\n" then
    Lean.logError "A `String := \"hi\"` field must still be string"; return
  if check content "any" then
    Lean.logError "A defaulted field must not degrade to `any`"; return

#testDefaultValuedFields

-- Unsupported scalars cannot be represented by this backend and are rejected
-- during elaboration, before any Go source is emitted.
elab "#testUnsupportedLeafRejected" : command => do
  let msg ← elabError (← `(getIonGoSerializer% UnsupportedLeaf "gotest"))
  if msg.isEmpty then
    Lean.logError "An unsupported scalar field type must be rejected"; return
  if !check msg "unsupported scalar field type" then
    Lean.logError s!"Unexpected error: {msg}"; return
  if !check msg "UnsupportedScalar" then
    Lean.logError s!"The error must name the unsupported type: {msg}"; return

#testUnsupportedLeafRejected

-- A type argument whose Go type has no `MarshalIon` is rejected during
-- elaboration. Without this the generator emits e.g. `Box[*big.Int]`, which is
-- accepted by every string assertion in this file and then rejected by the Go
-- compiler, so the user meets the problem as a build error in generated code
-- instead of a message naming the Lean type.
--
-- The rejected cases are listed individually rather than folded into one
-- representative: the first five are the diagnostics Go itself produces for an
-- unsatisfied constraint, and `BoxOptPoint` is the one Go would accept but whose
-- `none` the generic body could not encode.
elab "#testUnsatisfiableTypeArgRejected" : command => do
  for (name, stx) in
      [-- `*big.Int` — missing method MarshalIon.
       ("BoxNat", ← `(getIonGoSerializer% BoxNat "gotest")),
       -- `[]Point` — a slice has no method set.
       ("BoxListPoint", ← `(getIonGoSerializer% BoxListPoint "gotest")),
       -- `*MExpr` — pointer to interface, not interface.
       ("BoxOptMExpr", ← `(getIonGoSerializer% BoxOptMExpr "gotest")),
       -- `**Point` — pointer to pointer.
       ("BoxOptOptPoint", ← `(getIonGoSerializer% BoxOptOptPoint "gotest")),
       -- `*T` — pointer to type parameter, not type parameter.
       ("BoxOptParam", ← `(getIonGoSerializer% BoxOptParam "gotest")),
       -- `*Point` — satisfies ToIon, but `none` would be a nil value.
       ("BoxOptPoint", ← `(getIonGoSerializer% BoxOptPoint "gotest"))] do
    let msg ← elabError stx
    if msg.isEmpty then
      Lean.logError s!"{name}: a type argument that cannot satisfy ToIon must be \
                      rejected"; return
    if !check msg "ToIon" then
      Lean.logError s!"{name}: the error must name the unsatisfied constraint: {msg}"; return
    if !check msg "Box" then
      Lean.logError s!"{name}: the error must name the generic type: {msg}"; return
  if !check (← elabError (← `(getIonGoSerializer% BoxOptPoint "gotest"))) "Option" then
    Lean.logError "BoxOptPoint: the error must say an `Option` type argument is refused"

#testUnsatisfiableTypeArgRejected

/-! ## Wire round trips: Go builds it, Lean decodes it

Everything above asserts on emitted text. These assert on what
`getIonDeserializer%` recovers from bytes a *compiled Go program* produced, which
is the only way to catch a generator that emits compilable Go with the wrong
meaning — a dropped `Option`, a swapped Ion key, a tag that followed a Go
rename.

The generated package is built under its own import path and driven from a
`package main` in a different Go package, so an identifier the generator failed
to export is a build failure rather than a silent pass.
-/

/-- Where this suite's static Go sources live. Relative, because the test driver
runs `lean` from the package root. -/
def goTestData : System.FilePath := "StrataTestExtra/Languages/Go/testdata"

/-- Decode `bytes` with `des` and compare to `expected`. -/
def expectDecoded {α : Type} [BEq α] [Repr α]
    (des : ByteArray → Except Std.Format α) (expected : α) (bytes : ByteArray) :
    Except String Unit :=
  match des bytes with
  | .error e => .error s!"decode failed: {e}"
  | .ok v =>
    if v == expected then .ok ()
    else .error s!"decoded {repr v}\nexpected {repr expected}"

private partial def desFields : ByteArray → Except Std.Format Fields :=
  getIonDeserializer% Fields

private partial def desReservedRoot : ByteArray → Except Std.Format ReservedRoot :=
  getIonDeserializer% ReservedRoot

private partial def desReservedIon : ByteArray → Except Std.Format Reserved.Ion :=
  getIonDeserializer% Reserved.Ion

private partial def desCollidingCtors : ByteArray → Except Std.Format CollidingCtors :=
  getIonDeserializer% CollidingCtors

private partial def desNest : ByteArray → Except Std.Format Nest :=
  getIonDeserializer% Nest

private partial def desMExpr : ByteArray → Except Std.Format MExpr :=
  getIonDeserializer% MExpr

private partial def desLeaves : ByteArray → Except Std.Format Leaves :=
  getIonDeserializer% Leaves

private partial def desWrapper : ByteArray → Except Std.Format Wrapper :=
  getIonDeserializer% Wrapper

private partial def desBoxRootMirror : ByteArray → Except Std.Format BoxRootMirror :=
  getIonDeserializer% BoxRootMirror

private partial def desWithDefault : ByteArray → Except Std.Format WithDefault :=
  getIonDeserializer% WithDefault

/-- A string containing an embedded NUL and an astral-plane codepoint, neither of
which survives a generator that assumes one byte per character. -/
private def hostileString : String :=
  "é𝄞" ++ String.singleton (Char.ofNat 0) ++ "z"

/--
Every wire round trip, keyed by the `<label>.ion` file the Go driver writes.

`nest-full` is the case that catches a temporary-name collision in `writeInfo`:
`deepMix` is `Option (List (Option (List Nat)))`, so a counter shared between
lists and `Option`s would let the inner `Option`'s `_p` temporary shadow the
outer one, and the value written for the outer `Option` would be the inner one.
The emitted Go still compiles, so only the decoded value tells you.
-/
def roundTripChecks : List (String × (ByteArray → Except String Unit)) :=
  [ -- Odd Ion keys survive the trip in both directions.
    ("fields", expectDecoded desFields
      { «type» := 1, «2x» := 2, «a?b» := 3, ab := 4, «a"b» := 5, «?» := 6, «??» := 7 }),
    ("fields-zero", expectDecoded desFields
      { «type» := 0, «2x» := 0, «a?b» := 0, ab := 0, «a"b» := 0, «?» := 0, «??» := 0 }),
    -- Escaped type names still serialize under their original Lean field keys.
    ("reserved", expectDecoded desReservedRoot
      { a := { dv := 1 }, b := { ov := 2 }, c := { mv := 3 }, d := { tv := 4 },
        e := { kv := 5 }, f := { sv := 6 }, g := { ev := 7 }, h := { lv := 8 } }),
    -- A renamed constructor struct must keep its original Ion tag.
    ("ion-writer", expectDecoded desReservedIon (.writer 42)),
    ("ion-other", expectDecoded desReservedIon (.other 7)),
    ("ctor-mycase", expectDecoded desCollidingCtors (.myCase 1)),
    ("ctor-my-case", expectDecoded desCollidingCtors (.my_case 2)),
    -- Container nesting, every combination, populated.
    ("nest-full", expectDecoded desNest
      { maybeEach := [some "a", none, some ""],
        deepMix := some [none, some [1, 2], some []],
        optOpt := some (some "x"),
        listList := [[1, -2], []] }),
    -- `some none` decodes as `none`: see the byte comparison below for why this
    -- expectation is the honest one rather than a weakened test.
    ("nest-some-none", expectDecoded desNest
      { maybeEach := [], deepMix := none, optOpt := none, listList := [] }),
    ("nest-empty", expectDecoded desNest
      { maybeEach := [], deepMix := none, optOpt := none, listList := [] }),
    -- Mutual recursion, through both directions of the cycle.
    ("mexpr", expectDecoded desMExpr
      (.neg (.fromStmt (.seq [.exprStmt (.lit (-5)), .seq []])))),
    -- Leaf boundaries through generated code, at the 64-bit edges: these are the
    -- values a wrong signedness choice in a machine-integer mapping loses.
    ("leaves-max", expectDecoded desLeaves
      { nat := 18446744073709551615, int := -9223372036854775808, flt := 0.5,
        str := hostileString, bool := true,
        dec := { mantissa := -9223372036854775808, exponent := -8192 } }),
    ("leaves-zero", expectDecoded desLeaves
      { nat := 0, int := 0, flt := 0.0, str := "", bool := false,
        dec := { mantissa := 0, exponent := 0 } }),
    -- Values beyond the 64-bit edges verify that the generated `Nat`, `Int` and
    -- Decimal fields preserve Lean's arbitrary-precision values.
    ("leaves-beyond-64", expectDecoded desLeaves
      { nat := 18446744073709551616, int := -18446744073709551616, flt := 1.5,
        str := "beyond", bool := false,
        dec := { mantissa := 18446744073709551616, exponent := 3 } }),
    ("leaves-huge", expectDecoded desLeaves
      { nat := 2 ^ 200, int := -(2 ^ 200), flt := -0.25, str := "huge",
        bool := true, dec := { mantissa := -(2 ^ 200), exponent := -1 } }),
    -- Positional `_0`/`_1`/`_2` keys, not field names.
    ("wrapper", expectDecoded desWrapper (.mk (-1) "hi" true)),
    -- A generic instantiation must encode exactly like its monomorphic mirror.
    ("boxroot", expectDecoded desBoxRootMirror
      { b := { value := { x := 1, y := 2 } },
        ob := some { value := { x := 3, y := 4 } },
        lb := [{ value := { x := 5, y := 6 } }] }),
    ("boxroot-none", expectDecoded desBoxRootMirror
      { b := { value := { x := 0, y := 0 } }, ob := none, lb := [] }),
    -- A defaulted field carries the value the Go driver set, not a null.
    ("withdefault", expectDecoded desWithDefault { count := 99, label := "zz" })
  ]

/--
The whole adversarial closure as one Go package.

One package, not one per root: the flat Go namespace is the thing under test, so
splitting the roots across directories would hide exactly the collisions this is
looking for.
-/
def adversarialPackage : Array (String × String) := Id.run do
  let mut files : Std.HashMap String String := {}
  for gen in [getIonGoSerializer% Fields "gotest",
              getIonGoSerializer% ReservedRoot "gotest",
              getIonGoSerializer% Reserved.Ion "gotest",
              getIonGoSerializer% CollidingCtors "gotest",
              getIonGoSerializer% Nest "gotest",
              getIonGoSerializer% MExpr "gotest",
              getIonGoSerializer% Nilable "gotest",
              getIonGoSerializer% Leaves "gotest",
              getIonGoSerializer% Wrapper "gotest",
              getIonGoSerializer% BoxRoot "gotest",
              getIonGoSerializer% WithDefault "gotest"] do
    for (name, content) in gen.files do files := files.insert name content
  return files.toArray

-- Every emitted shape as *behaviour*, for the adversarial closure: it
-- compiles, is gofmt-clean, passes `go vet`, is usable from another Go package,
-- and every value it marshals decodes back to the Lean value it was built from.
--
-- `#eval` rather than an `elab` command because the round-trip expectations need
-- the `Repr`/`BEq` instances derived in this file, and a `meta` declaration
-- cannot reference a non-`meta` one from the same module.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  unless ← haveGo do
    Lean.logWarning "Go adversarial round trip skipped: go not found"
    return

  let dir : System.FilePath := "/tmp/strata-go-adv-roundtrip"
  prepareTempDir dir

  writeGoFiles (dir / "gotest") { files := adversarialPackage }
  IO.FS.writeFile (dir / "main.go") (← IO.FS.readFile (goTestData / "shapes_main.go"))
  if let some reason ← writeGoModule dir "advtest" then
    Lean.logWarning s!"Go adversarial round trip skipped: {reason}"
    cleanupTempDir dir
    return

  -- The toolchain checks for this closure. `go vet` runs the type checker, so a vet-clean
  -- result also means the package compiles.
  if let some err ← checkGoClean dir then Lean.throwError err

  if let some err ← runTool "go" #["build", "-buildvcs=false", "-o", "driver", "."] dir then
    Lean.throwError err

  let out := dir / "out"
  IO.FS.createDirAll out
  let run ← IO.Process.output { cmd := "./driver", args := #[out.toString], cwd := dir }
  if run.exitCode != 0 then
    Lean.throwError s!"Go driver failed (exit {run.exitCode}):\n{run.stdout}\n{run.stderr}"

  let mut failures : Array String := #[]
  for (label, chk) in roundTripChecks do
    let path := out / s!"{label}.ion"
    if !(← path.pathExists) then
      failures := failures.push s!"{label}: the Go driver wrote no {label}.ion"
      continue
    match chk (← IO.FS.readBinFile path) with
    | .ok _ => pure ()
    | .error e => failures := failures.push s!"{label}: {e}"
  -- Every case is reported, not just the first: a systematic error (e.g. a
  -- broken symbol table) fails all of them and the list is the diagnosis.
  unless failures.isEmpty do
    Lean.throwError s!"{failures.size} wire round trip(s) failed:\n\
                      {"\n".intercalate failures.toList}"

  -- `Option (Option T)` is LOSSY in this encoding, and that is a property of the
  -- format rather than of the Go backend: the encoding maps `none` to an Ion null
  -- at every level, so `some none` and `none` are the same byte and the
  -- deserializer has no way to tell them apart. Pinned here rather than asserted away, because
  -- "fixing" it in one backend (say, by emitting a typed null for the inner
  -- `none`) without changing `getIonDeserializer%` and the Java backend would
  -- silently split the wire format in two. Java has the identical hole.
  let someNone ← IO.FS.readBinFile (out / "nest-some-none.ion")
  let plainNone ← IO.FS.readBinFile (out / "nest-empty.ion")
  if someNone.toList != plainNone.toList then
    Lean.throwError "`Option (Option T)`: `some none` and `none` now encode \
                     differently. That may well be an improvement, but it is a \
                     wire-format change: `getIonDeserializer%` still decodes any \
                     Ion null to `none`, and the Java backend still emits one. \
                     Update the `Option` section of docs/GoIonCodeGen.md and all \
                     three sides together."

  cleanupTempDir dir

/-! ## The real target: `laurelGoGen`'s `Laurel.LaurelProgram` closure

Everything above is about the generator; this is about the *product* — whether a
Go program can actually hand Strata a Laurel program and be believed.
-/

/-- Built by `lake`/`brazil-build`; listed in `StrataTestMain`'s `needs`. The
Brazil-wrapped copies under `build/bin/` fail with an `envroot` error, so this
path is the `.lake` one deliberately. -/
def laurelGoGenExe : System.FilePath := ".lake/build/bin/laurelGoGen"

/-- Run a generator executable, or explain that it has not been built.

An **error** rather than a skip: the executable is in `defaultTargets` and in
`StrataTestMain`'s `needs`, so under the real test driver it always exists, and
silently skipping the end-to-end cases is the one failure mode that would let
a broken M0 look green. -/
def runGenerator (exe : System.FilePath) (args : Array String) :
    Lean.Elab.Command.CommandElabM Unit := do
  unless ← exe.pathExists do
    Lean.throwError s!"{exe} has not been built. Run `brazil-build` from the \
                      package root; it is in `defaultTargets`."
  let r ← IO.Process.output { cmd := exe.toString, args }
  if r.exitCode != 0 then
    Lean.throwError s!"{exe} failed (exit {r.exitCode}):\n{r.stdout}\n{r.stderr}"

-- The toolchain checks on the whole `Laurel.LaurelProgram` closure, which is the output
-- that actually ships. The smoke test's toolchain check covers a handful of synthetic
-- types; this covers every file `laurelGoGen` emits, and adds `go build` because
-- `gofmt`/`vet` on their own do not link the package.
--
-- The generated package sits in a subdirectory with the module root above it, so
-- `go vet ./...` type-checks it as an imported package rather than as the main
-- one — the same arrangement a Go front-end would use.
--
-- The package-name and prune checks need only the executable, so they run before
-- the `haveGo` guard and are not lost along with the toolchain checks.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let dir : System.FilePath := "/tmp/strata-go-laurelgen"
  prepareTempDir dir

  -- The CLI validates the package argument before substituting it into every
  -- generated file.
  let invalidDir := dir / "invalid"
  let invalid ← IO.Process.output
    { cmd := laurelGoGenExe.toString, args := #["init", invalidDir.toString] }
  if invalid.exitCode == 0 then
    Lean.throwError "laurelGoGen accepted reserved package name `init`"
  unless (invalid.stderr.splitOn "not a valid Go package name").length > 1 do
    Lean.throwError s!"laurelGoGen returned an unclear invalid-package error:\n\
                      {invalid.stdout}\n{invalid.stderr}"
  if ← invalidDir.pathExists then
    Lean.throwError "laurelGoGen wrote files before rejecting an invalid package name"

  let outputDir := dir / "laurel"
  IO.FS.createDirAll outputDir
  let staleFile := outputDir / "RemovedType.go"
  IO.FS.writeFile staleFile
    s!"{generatedGoFileMarker}\n\npackage laurel\n"
  let handwrittenFile := outputDir / "handwritten.go"
  IO.FS.writeFile handwrittenFile "package laurel\n"
  let quotedMarkerFile := outputDir / "gen_check_test.go"
  IO.FS.writeFile quotedMarkerFile
    s!"package laurel\n\n// A handwritten test may quote \
       {generatedGoFileMarker}\n"

  runGenerator laurelGoGenExe #["laurel", outputDir.toString]
  if ← staleFile.pathExists then
    Lean.throwError "laurelGoGen left an obsolete generated type file in the output directory"
  unless ← handwrittenFile.pathExists do
    Lean.throwError "laurelGoGen removed a handwritten Go file from the output directory"
  unless ← quotedMarkerFile.pathExists do
    Lean.throwError "laurelGoGen removed a handwritten file that merely quoted \
                    the generated marker"
  unless ← haveGo do
    Lean.logWarning "laurelGoGen toolchain checks skipped: go not found"
    cleanupTempDir dir
    return
  if let some reason ← writeGoModule dir "laurelgen" then
    Lean.logWarning s!"laurelGoGen toolchain checks skipped: {reason}"
    cleanupTempDir dir
    return

  -- Three fixed runtime files plus one per Lean type in the closure. The exact
  -- count is deliberately NOT pinned because it tracks the Laurel AST. A floor
  -- instead ensures the generator emitted the type closure rather than only the
  -- runtime, since an empty closure still compiles and vets clean.
  let emitted := (← (dir / "laurel").readDir).map (·.fileName)
  if emitted.size < 20 then
    Lean.throwError s!"laurelGoGen emitted only {emitted.size} files: {emitted}"
  for runtime in ["ion_value.go", "ion_binary.go", "opt.go"] do
    unless emitted.contains runtime do
      Lean.throwError s!"laurelGoGen did not emit the fixed runtime file {runtime}"
  -- One directory, flat: a Go package is a directory, so package-path nesting is
  -- a Java-ism.
  for entry in ← (dir / "laurel").readDir do
    if ← entry.path.isDir then
      Lean.throwError s!"laurelGoGen must emit one flat directory, found \
                        subdirectory {entry.fileName}"

  if let some err ← checkGoClean dir then Lean.throwError err
  if let some err ← runTool "go" #["build", "./..."] dir then Lean.throwError err

  cleanupTempDir dir

/-! ## A Go-built `Laurel.LaurelProgram`, decoded and verified

The M0 exit criterion. A Go program builds a procedure with a `requires`, a
`while` with an invariant and an `assert`, marshals it, and Lean must

1. decode it with `readLaurelIonProgram`,
2. agree that it is the *same program* as the Laurel concrete syntax below, and
3. reach the expected verdict on it, including reporting a deliberately
   unprovable assert at the right source position.

Step 2 compares the two ASTs through `Laurel.formatProgram`, which prints
concrete syntax. Comparing the ASTs directly cannot work — the Go program's nodes
carry synthetic source ranges — and comparing them field by field with positions
masked would mean writing a second AST traversal to keep in step with the first.
Printing is also the comparison a human can read when it fails.

The Laurel text and `testdata/laurel_main.go` are two spellings of one program and
have to be edited together. That is deliberate: it is the only way to state
"the Go API can express this" as a test.
-/

/-- The reference program, in Laurel concrete syntax.

`assert i == n` follows from the invariant (`i <= n`) and the negated loop
condition (`i >= n`), so this verifies; `requires n >= 0` is what establishes the
invariant on entry. Its Go counterpart is `sumTo` in `testdata/laurel_main.go`. -/
def laurelReferenceSource : String :=
  -- Joined rather than one literal with `\n\` continuations, because the
  -- indentation is part of the program and a gap escape swallows it.
  "\n".intercalate
    ["procedure sumTo(n: int): int",
     "  requires n >= 0",
     "  opaque",
     "{",
     "  var i: int := 0;",
     "  while (i < n)",
     "    invariant i <= n",
     "  {",
     "    i := i + 1",
     "  };",
     "  assert i == n;",
     "  return i",
     "};"] ++ "\n"

/-- Byte range stamped on the failing assert by the Go driver. Must match the
`badAssertStart`/`badAssertStop` constants there. -/
def badAssertRange : Nat × Nat := (4242, 4250)

/-- Quiet verifier defaults: solver chatter is noise here, the verdict is the
subject. -/
def quietVerifyOptions : _root_.Core.VerifyOptions := _root_.Core.VerifyOptions.quiet

/-- Whether the SMT solver the verifier defaults to is available. Verification is
skipped with a warning without it, in the same spirit as the Java suite skipping
without `javac`. -/
def haveSolver : IO Bool := do
  try
    let r ← IO.Process.output { cmd := "cvc5", args := #["--version"] }
    return r.exitCode == 0
  catch _ => return false

/-- Concrete syntax for a decoded program, used as the comparison normal form:
it drops the source ranges that the Go and the parsed AST necessarily disagree
about while keeping every structural difference. -/
def printLaurel (p : Strata.Laurel.LaurelProgram) : String :=
  (Strata.Laurel.formatProgram p).pretty 100

-- The three steps above, in order.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  unless ← haveGo do
    Lean.logWarning "Laurel end-to-end round trip skipped: go not found"
    return

  let dir : System.FilePath := "/tmp/strata-go-laurel-e2e"
  prepareTempDir dir

  -- The generated package goes in a subdirectory and the driver imports it, so
  -- this exercises the cross-package use a real Go front-end needs.
  runGenerator laurelGoGenExe #["laurel", (dir / "laurel").toString]
  IO.FS.writeFile (dir / "main.go") (← IO.FS.readFile (goTestData / "laurel_main.go"))
  if let some reason ← writeGoModule dir "e2e" then
    Lean.logWarning s!"Laurel end-to-end round trip skipped: {reason}"
    cleanupTempDir dir
    return

  if let some err ← runTool "go"
      #["build", "-buildvcs=false", "-o", "laurel-driver", "."] dir then
    Lean.throwError err
  let run ← IO.Process.output
    { cmd := "./laurel-driver", args := #[dir.toString], cwd := dir }
  if run.exitCode != 0 then
    Lean.throwError s!"the Go Laurel driver failed (exit {run.exitCode}):\n\
                      {run.stdout}\n{run.stderr}"

  -- Step 1: the Go-produced bytes decode through `readLaurelIonProgram`.
  let goodBytes ← IO.FS.readBinFile (dir / "laurel-good.ion")
  let goProgram ← Strata.readLaurelIonProgram goodBytes

  -- Step 2: it is the same program as the concrete syntax.
  let textProgram ← Strata.parseLaurelText "<laurel-reference>" laurelReferenceSource
  let goText := printLaurel goProgram
  let refText := printLaurel textProgram
  if goText != refText then
    Lean.throwError s!"the Go-built program is not the reference program.\n\
      from Go:\n{goText}\n\nfrom Laurel source:\n{refText}"

  -- `LiteralInt` uses arbitrary-precision `*big.Int`. These boundary and
  -- beyond-boundary values are asserted on Lean's printed decoded AST, proving
  -- that they survive Go -> Ion -> `readLaurelIonProgram`.
  let bigBytes ← IO.FS.readBinFile (dir / "laurel-bigint.ion")
  let bigProgram ← Strata.readLaurelIonProgram bigBytes
  let bigText := printLaurel bigProgram
  for numeral in ["18446744073709551615", "18446744073709551616"] do
    unless (bigText.splitOn numeral).length > 1 do
      Lean.throwError s!"the literal {numeral} did not survive the round trip; \
        the decoded program printed as:\n{bigText}"

  -- Step 3: the verdict. Without a solver there is no verdict to check, so the
  -- decode and structural comparison above still ran and only this part is
  -- skipped.
  unless ← haveSolver do
    Lean.logWarning "Laurel verification verdict skipped: cvc5 not found"
    cleanupTempDir dir
    return

  -- Check every message: the provable program below produces none at all, so
  -- filtering by category could hide a failure.
  let errorsOf (p : Strata.Laurel.LaurelProgram) : IO (Array Strata.Message) :=
    Strata.Laurel.analyzeToMessages p quietVerifyOptions

  -- The provable program must produce no errors. A verifier that reported one
  -- here would make the failing case below meaningless.
  let goodErrors ← errorsOf goProgram
  unless goodErrors.isEmpty do
    Lean.throwError s!"the Go-built program should verify, but reported \
      {goodErrors.size} error(s):\n\
      {"\n".intercalate (goodErrors.toList.map (·.message))}"

  -- The same procedure with `assert i == n + 1` must fail, and must fail *at the
  -- range the Go program stamped on that node*. Checking the position is what
  -- proves source provenance survived Go -> Ion -> Lean: a generator that dropped
  -- `FileRange` would still produce a diagnostic, just an unusable one.
  let badBytes ← IO.FS.readBinFile (dir / "laurel-bad.ion")
  let badProgram ← Strata.readLaurelIonProgram badBytes
  let badErrors ← errorsOf badProgram
  if badErrors.isEmpty then
    Lean.throwError "`assert i == n + 1` must not verify"
  let (wantStart, wantStop) := badAssertRange
  let onTheAssert := badErrors.filter fun m =>
    m.fileRange.range.start.byteIdx == wantStart &&
      m.fileRange.range.stop.byteIdx == wantStop
  let describe (m : Strata.Message) : String :=
    s!"{Std.format m.fileRange.file}:{m.fileRange.range.start.byteIdx}-\
      {m.fileRange.range.stop.byteIdx}: {m.message}"
  if onTheAssert.isEmpty then
    Lean.throwError s!"the failing assert must be reported at bytes \
      {wantStart}-{wantStop} (the range the Go program stamped on it). Reported \
      instead:\n{"\n".intercalate (badErrors.toList.map describe)}"
  -- And attributed to the URI the Go program declared, so a diagnostic cannot be
  -- blamed on the wrong producer.
  for m in onTheAssert do
    let uri := toString (Std.format m.fileRange.file)
    unless (uri.splitOn "go-front-end").length > 1 do
      Lean.throwError s!"diagnostic attributed to {uri}, but the Go program \
        declared itself the source"

  cleanupTempDir dir

end Strata.Go.AdvTest

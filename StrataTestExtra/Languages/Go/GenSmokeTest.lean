/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Command
public meta import Strata.Go.Gen
public meta import StrataTest.Languages.Go.GenTestUtil

open Strata.Go
open Strata.Go.TestUtil

/-!
# `getIonGoSerializer%` smoke tests

One check per emitted shape, asserting the generator produces what
`docs/GoIonCodeGen.md` describes. Mirrors `StrataTestExtra/Languages/Java/TestGen.lean`.

This is deliberately a *smoke* suite: enough to catch a structural regression in
each shape the generator handles, plus one real `gofmt`/`go vet` run. The
exhaustive encoding, boundary and adversarial coverage lives in the full Go test
suite.
-/

namespace Strata.Go.Test

-- Test types

structure Point where
  x : Nat
  y : Nat

/-- A single-constructor inductive: encoded as an Ion struct with *positional*
keys (`_0`, `_1`), distinct from both field-name-keyed structs and multi-ctor
sexps, and emitted as a plain struct rather than an interface. -/
inductive Wrapper where
  | mk (value : Nat) (label : String)

inductive Shape where
  | circle (radius : Nat)
  | rect (width : Nat) (height : Nat)

/-- An inductive with no constructors. Unlike Java's `sealed ... permits`, an
interface with no implementor is legal Go and needs no special case. -/
inductive Void where

inductive Tree where
  | leaf (value : Nat)
  | node (left : Tree) (right : Tree)

/-- A generic structure: the Lean type parameter becomes a Go type parameter
constrained by `ToIon`, which lets the body call `.MarshalIon(w)` on it. -/
structure Box (T : Type) where
  value : T

/-- A generic multi-constructor inductive: the interface, every constructor
struct and the marker method all carry the parameter list. -/
inductive Holder (T : Type) where
  | full (item : T)
  | empty

/-- Exercises a generic compound behind each container. -/
structure Crate where
  boxed : Box Point
  maybeBoxed : Option (Box Point)
  many : List (Box Point)
  held : Holder Point

structure Team where
  name : String
  members : List String
  mascot : Option String

/-- Nested containers: the element of an inner container has no `ToIon` of its
own, so each level has to be built with its own loop or `if`. -/
structure League where
  rosters : Option (List String)
  groups : List (List String)
  maybeMaybe : Option (Option String)

/-- A Lean type name ending in `?`. The `?` is stripped by escaping, so without
the `Opt` suffix this would collapse onto a sibling named `Widget`. -/
structure «Widget?» where
  label : Option String

/-- `Coll`'s constructor `inner` yields the Go struct `CollInner`, which is also
the Go name of the separate type `CollInner`. Both are reachable from
`CollRoot`, so the package-wide registry must reject the pair. -/
inductive Coll where
  | inner (x : Nat)
  | other (y : Nat)

structure CollInner where
  z : Nat

structure CollRoot where
  a : Coll
  b : CollInner

/-! ### Naming edge cases outside the Laurel closure

Each type below is reachable only from a Lean declaration outside
`Laurel.LaurelProgram`'s closure, so the shipped path never exercised them. The whole
point of the flat-namespace machinery is that it holds for arbitrary input.
-/

/-- A Lean type parameter is an ordinary Go identifier and must be escaped like
any other. Without escaping, `ionWriter` would capture the runtime writer alias
in the generated `MarshalIon` signature. -/
structure CapturingBox (ionWriter : Type) where
  value : ionWriter

/-- A parameter named `decimal` must not capture the runtime `Decimal` used by
the sibling `amount` field. -/
structure CapturingPair (decimal : Type) where
  value : decimal
  amount : StrataDDM.Decimal

/-- Escaping type parameters is not injective, because
`Char.isAlphanum` is ASCII-only — the entirely idiomatic `(α β : Type)` folds both
onto `Field`, and `[Field ToIon, Field ToIon]` is not valid Go. -/
structure GreekPair (α β : Type) where
  left : α
  right : β

/-- `IonWriter` is declared by `ion_value.go`, so it is a package-scope name the
generator must not redeclare. -/
structure IonWriter where
  n : Nat

/-- A runtime-name clash can arise from the *concatenation* that names a
constructor struct, which is why `escapeGoName` is applied to the joined name
rather than to its parts. -/
inductive Marshal where
  | binary (n : Nat)
  | other (m : Nat)

/-- Escaping can strip the leading character, so `escapeGoName` must restore
capitalisation. `«$bar»` would otherwise emit the *unexported* field `bar`,
which a consumer in another Go package cannot set; `«σ»` and `«τ»` strip to
nothing at all. -/
structure Unexported where
  «$bar» : Nat
  «σ» : Nat
  «τ» : Nat

/-- Without the capitalisation step this emits `type writeBigInt`, redeclaring
`ion_value.go`'s unexported helper. -/
structure «$writeBigInt» where
  n : Nat

/-- A Go method name lives in its receiver's method set, never in package scope,
so `func (Foo4A) isFoo4() {}` and a separate `type IsFoo4 struct{…}` coexist.
The package-wide registry must accept this pair. -/
inductive Foo4 where
  | a (x : Nat)
  | b (y : Nat)

structure IsFoo4 where
  n : Nat

structure Root4 where
  f : Foo4
  g : IsFoo4

-- Test 1: a structure becomes a struct with field-name-keyed Ion struct, and
-- the three fixed runtime files are emitted alongside it.
elab "#testPoint" : command => do
  let files := getIonGoSerializer% Point "gotest"
  for runtime in ["ion_value.go", "ion_binary.go", "opt.go"] do
    if !files.files.any (·.1 == runtime) then
      Lean.logError s!"Missing fixed runtime file {runtime}"; return
    -- The support files carry the marker too. Without it `laurelGoGen`'s prune
    -- reads them as handwritten, so a renamed or dropped support file would be
    -- left behind alongside its replacement.
    unless (← fileNamed files runtime).startsWith
        (generatedGoFileMarker ++ "\n\npackage gotest\n") do
      Lean.logError s!"{runtime} must open with the generated marker"; return
  let content ← fileNamed files "Point.go"
  unless content.startsWith (generatedGoFileMarker ++ "\n\npackage gotest\n") do
    Lean.logError s!"The generated marker must precede the package clause:\n{content}"; return
  -- A `Nat`/`Int` field is a `*big.Int`, so this file — and only a file like it —
  -- carries the one import the generator emits. Go rejects an unused import, so
  -- both halves matter; the negative half is in `#testOptSuffix`.
  if !check content "\nimport \"math/big\"\n" then
    Lean.logError s!"A file with an Int/Nat field must import math/big:\n{content}"; return
  -- Fields are exported; gofmt aligns the type column, so the padding matters.
  if !check content "type Point struct {\n\tX *big.Int\n\tY *big.Int\n}" then
    Lean.logError s!"Unexpected struct declaration:\n{content}"; return
  -- Value receiver implementing ion.Marshaler. Arbitrary-precision integers go
  -- straight to ion-go through the checked writer adapter.
  if !check content "func (v Point) MarshalIon(w IonWriter) error {" then
    Lean.logError "Missing value-receiver MarshalIon"; return
  if !check content "fieldName(w, \"x\")" then
    Lean.logError "Missing x field name"; return
  if !check content "writeNat(w, v.X)" then
    Lean.logError "Missing x field writer"; return
  if !check content "fieldName(w, \"y\")" then
    Lean.logError "Missing y field name"; return
  if !check content "writeNat(w, v.Y)" then
    Lean.logError "Missing y field writer"; return
  -- A structure is never an interface.
  if check content "interface {" then Lean.logError "A structure must not emit an interface"; return

#testPoint

-- Test 2: a single-constructor inductive is a struct too, but with positional
-- `_0`/`_1` Ion keys rather than field names.
elab "#testWrapper" : command => do
  let content ← fileNamed (getIonGoSerializer% Wrapper "gotest") "Wrapper.go"
  if !check content "type Wrapper struct {" then Lean.logError "Missing Wrapper struct"; return
  if check content "interface {" then
    Lean.logError "Single-ctor inductive must not be an interface"; return
  if !check content "Value *big.Int" then Lean.logError "Missing Value field"; return
  -- `Value` and `Label` are the same width, so gofmt needs no padding here.
  if !check content "\tLabel string\n" then Lean.logError "Missing Label field"; return
  if !check content "fieldName(w, \"_0\")" then
    Lean.logError "Missing positional key _0"; return
  if !check content "fieldName(w, \"_1\")" then
    Lean.logError "Missing positional key _1"; return
  if !check content "writeString(w, v.Label)" then
    Lean.logError "Missing label writer"; return

#testWrapper

-- Test 3: a multi-constructor inductive becomes an interface with a marker
-- method plus one top-level struct per constructor, each serializing to a
-- symbol-tagged sexp. The struct names carry the owning type because Go has no
-- nested types.
elab "#testShape" : command => do
  let content ← fileNamed (getIonGoSerializer% Shape "gotest") "Shape.go"
  if !check content "type Shape interface {\n\tMarshalIon(w IonWriter) error\n\tisShape()\n}" then
    Lean.logError s!"Unexpected interface declaration:\n{content}"; return
  if !check content "type ShapeCircle struct{ Radius *big.Int }" then
    Lean.logError "Missing single-field ShapeCircle struct"; return
  if !check content "func (ShapeCircle) isShape() {}" then
    Lean.logError "Missing ShapeCircle marker method"; return
  if !check content "type ShapeRect struct {\n\tWidth  *big.Int\n\tHeight *big.Int\n}" then
    Lean.logError "Missing aligned ShapeRect struct"; return
  -- The Ion tag stays the Lean constructor's short name.
  if !check content "writeSymbol(w, \"circle\")" then Lean.logError "Missing circle tag"; return
  if !check content "writeSymbol(w, \"rect\")" then Lean.logError "Missing rect tag"; return
  if !check content "w.BeginSexp()" then
    Lean.logError "Multi-ctor must serialize to a sexp"; return

#testShape

-- Test 4: a zero-constructor inductive is a bare interface with no implementor,
-- which is legal Go and cannot be constructed — the correct meaning.
elab "#testVoid" : command => do
  let content ← fileNamed (getIonGoSerializer% Void "gotest") "Void.go"
  if !check content "type Void interface {\n\tMarshalIon(w IonWriter) error\n\tisVoid()\n}" then
    Lean.logError s!"Unexpected Void declaration:\n{content}"; return
  if check content "struct" then Lean.logError "Zero-ctor inductive must emit no struct"; return
  if check content "func (" then Lean.logError "Zero-ctor inductive must emit no method"; return

#testVoid

-- Test 5: a recursive type refers to its own interface, and the recursion is
-- through the interface rather than the constructor struct.
elab "#testTree" : command => do
  let content ← fileNamed (getIonGoSerializer% Tree "gotest") "Tree.go"
  if !check content "type TreeNode struct {\n\tLeft  Tree\n\tRight Tree\n}" then
    Lean.logError s!"Unexpected TreeNode struct:\n{content}"; return
  if !check content "v.Left.MarshalIon(w)" then Lean.logError "Missing Left.MarshalIon"; return
  if !check content "v.Right.MarshalIon(w)" then Lean.logError "Missing Right.MarshalIon"; return
  if !check content "isNilIonMarshaler(v.Left)" then
    Lean.logError "Tree.Left must be nil-checked before MarshalIon"; return
  if !check content "isNilIonMarshaler(v.Right)" then
    Lean.logError "Tree.Right must be nil-checked before MarshalIon"; return

#testTree

-- Test 6: type parameters become `ToIon`-constrained Go type parameters, on the
-- struct, on the interface, on every constructor struct and on every receiver.
elab "#testGenerics" : command => do
  let files := getIonGoSerializer% Crate "gotest"
  let box ← fileNamed files "Box.go"
  if !check box "type Box[T ToIon] struct{ Value T }" then
    Lean.logError s!"Unexpected Box declaration:\n{box}"; return
  if !check box "func (v Box[T]) MarshalIon(w IonWriter) error {" then
    Lean.logError "Missing parameterised receiver"; return
  if !check box "v.Value.MarshalIon(w)" then Lean.logError "Type-param field must use MarshalIon"; return
  if !check box "isNilIonMarshaler(v.Value)" then
    Lean.logError "Type-param field must be nil-checked before MarshalIon"; return
  let holder ← fileNamed files "Holder.go"
  if !check holder "type Holder[T ToIon] interface {" then
    Lean.logError "Generic multi-ctor interface must carry the parameter list"; return
  if !check holder "type HolderFull[T ToIon] struct{ Item T }" then
    Lean.logError "Generic ctor struct must carry the parameter list"; return
  -- The marker method name has no parameter list; the receiver does, and the
  -- result mentions the parameter so `HolderFull[U]` is no `Holder[T]`.
  if !check holder "isHolder() *T\n" then
    Lean.logError s!"Generic interface marker must mention its parameter:\n{holder}"; return
  if !check holder "func (HolderFull[T]) isHolder() *T { return nil }" then
    Lean.logError s!"Unexpected marker method:\n{holder}"; return
  -- Type arguments are spelled with Go's bracket syntax.
  let crate ← fileNamed files "Crate.go"
  if !check crate "Boxed      Box[Point]" then
    Lean.logError s!"Unexpected Crate fields:\n{crate}"; return
  if !check crate "MaybeBoxed *Box[Point]" then Lean.logError "Option of generic must be a pointer"; return
  if !check crate "Many       []Box[Point]" then Lean.logError "List of generic must be a slice"; return

#testGenerics

-- Test 7: `List` becomes a slice written inside an Ion list, and `Option` a
-- pointer whose nil case writes Ion null.
elab "#testTeam" : command => do
  let content ← fileNamed (getIonGoSerializer% Team "gotest") "Team.go"
  if !check content "Members []string" then Lean.logError "Missing Members slice"; return
  if !check content "Mascot  *string" then Lean.logError "Missing Mascot pointer"; return
  if !check content "w.BeginList()" then Lean.logError "Missing list begin"; return
  if !check content "for _i0, _e0 := range v.Members {" then Lean.logError "Missing list loop"; return
  if !check content "writeString(w, _e0)" then
    Lean.logError "Missing list element writer"; return
  if !check content "if v.Mascot == nil {" then Lean.logError "Missing Option nil check"; return
  if !check content "w.WriteNull()" then Lean.logError "Option nil must write Ion null"; return
  if !check content "_p0 := *v.Mascot" then Lean.logError "Missing Option dereference local"; return

#testTeam

-- Test 8: nested containers. Each list/option level gets distinct locals and
-- writes recursively through the same ion-go writer.
elab "#testLeague" : command => do
  let content ← fileNamed (getIonGoSerializer% League "gotest") "League.go"
  if !check content "Rosters    *[]string" then Lean.logError "Missing *[]string rosters"; return
  if !check content "Groups     [][]string" then Lean.logError "Missing [][]string groups"; return
  if !check content "MaybeMaybe **string" then Lean.logError "Missing **string maybeMaybe"; return
  -- Option of list: nil check outside, loop inside, and the loop ranges over the
  -- dereference local rather than an inline `*v.Rosters`.
  if !check content "for _i0, _e0 := range _p0 {" then
    Lean.logError s!"Option-of-list must loop over the dereference local:\n{content}"; return
  -- List of list: the inner loop's variables must not shadow the outer's.
  if !check content "for _i0, _e0 := range v.Groups {" then Lean.logError "Missing outer list loop"; return
  if !check content "for _i1, _e1 := range _e0 {" then
    Lean.logError "Inner list loop must use a depth-suffixed variable"; return
  if !check content "writeString(w, _e1)" then
    Lean.logError "Inner list must write its elements"; return
  -- Option of option: two distinct guard variables.
  if !check content "if _p0 == nil {" then Lean.logError "Nested Option must nil-check the inner pointer"; return
  if !check content "_p1 := *_p0" then
    Lean.logError "Nested Option must use a depth-suffixed dereference local"; return

#testLeague

-- Test 9: a Lean type name ending in `?` gets an `Opt` suffix rather than
-- silently folding onto the same Go name as a sibling called `Widget`.
elab "#testOptSuffix" : command => do
  let files := getIonGoSerializer% «Widget?» "gotest"
  let content ← fileNamed files "WidgetOpt.go"
  if !check content "type WidgetOpt struct{ Label *string }" then
    Lean.logError s!"Unexpected WidgetOpt declaration:\n{content}"; return
  if files.files.any (·.1 == "Widget.go") then
    Lean.logError "The `?` must not be dropped from the Go type name"; return
  -- The negative half of `#testPoint`'s import check. `WidgetOpt` has no `Int` or
  -- `Nat` field, and an unused `math/big` import does not compile.
  if check content "math/big" then
    Lean.logError s!"A file with no Int/Nat field must not import math/big:\n{content}"; return

#testOptSuffix

-- Test 10: a cross-type flat-namespace collision is a hard error naming both
-- culprits, not a silent rename. `withoutErrToSorry` is required: `elabTerm`
-- otherwise converts the thrown error into a logged message plus `sorryAx`.
elab "#testCrossTypeCollision" : command => do
  let msg ← Lean.Elab.Command.liftTermElabM do
    try
      let stx ← `(getIonGoSerializer% CollRoot "gotest")
      let _ ← Lean.Elab.Term.withoutErrToSorry (Lean.Elab.Term.elabTerm stx none)
      return ""
    catch e => return (← e.toMessageData.toString)
  if msg.isEmpty then
    Lean.logError "A cross-type flat-namespace collision must be rejected"; return
  if !check msg "CollInner" then
    Lean.logError s!"Error must name the colliding Go name: {msg}"; return
  -- Both culprits, so the reader knows which two Lean declarations to look at.
  if !check msg "Coll.inner" then
    Lean.logError s!"Error must name the constructor culprit: {msg}"; return
  if !check msg "the type generated for" then
    Lean.logError s!"Error must name the colliding type declaration: {msg}"; return

#testCrossTypeCollision

-- Test 12: type parameters go through `escapeGoName` at the declaration site
-- AND at every use site. Each assertion pins both spellings together.
elab "#testTypeParamEscaping" : command => do
  let box ← fileNamed (getIonGoSerializer% CapturingBox "gotest") "CapturingBox.go"
  if !check box "type CapturingBox[IonWriter_ ToIon] struct{ Value IonWriter_ }" then
    Lean.logError s!"Type parameter must not capture the runtime IonWriter:\n{box}"; return
  -- The method argument type must still be the runtime writer alias.
  if !check box "func (v CapturingBox[IonWriter_]) MarshalIon(w IonWriter) error {" then
    Lean.logError s!"Receiver and writer type disagree:\n{box}"; return
  let pair ← fileNamed (getIonGoSerializer% CapturingPair "gotest") "CapturingPair.go"
  -- `Value` is the type parameter, `Amount` the runtime Decimal: two different types.
  if !check pair "type CapturingPair[Decimal_ ToIon] struct {\n\tValue  Decimal_\n\tAmount Decimal\n}" then
    Lean.logError s!"Type parameter must not capture the runtime Decimal:\n{pair}"; return
  -- Escaping is not injective, so a whole parameter list needs disambiguating.
  let greek ← fileNamed (getIonGoSerializer% GreekPair "gotest") "GreekPair.go"
  if !check greek "type GreekPair[Field ToIon, Field_ ToIon] struct {" then
    Lean.logError s!"Colliding type parameters must be disambiguated:\n{greek}"; return
  if !check greek "func (v GreekPair[Field, Field_]) MarshalIon(w IonWriter) error {" then
    Lean.logError s!"Receiver must use the disambiguated parameter names:\n{greek}"; return

#testTypeParamEscaping

-- Test 13: every package-scope name the fixed support files declare is reserved,
-- not just the exported adapter types.
elab "#testRuntimeNamesReserved" : command => do
  let files := getIonGoSerializer% IonWriter "gotest"
  let content ← fileNamed files "IonWriter_.go"
  if !check content "type IonWriter_ struct{ N *big.Int }" then
    Lean.logError s!"The IonWriter alias name must be escaped:\n{content}"; return
  if files.files.any (·.1 == "IonWriter.go") then
    Lean.logError "Must not emit a file that redeclares IonWriter"; return
  -- Same clash, reached through the constructor-struct concatenation.
  let marshal ← fileNamed (getIonGoSerializer% Marshal "gotest") "Marshal.go"
  if !check marshal "type MarshalBinary_ struct{ N *big.Int }" then
    Lean.logError s!"Concatenated ctor name must be escaped as a whole:\n{marshal}"; return

#testRuntimeNamesReserved

-- Test 14: `escapeGoName` guarantees an *exported* identifier. `toPascalCase`
-- cannot, because the strip runs after it and can remove the character it
-- capitalised. This is invisible to gofmt and go vet — the output compiles, it
-- is just unusable from another Go package.
elab "#testAlwaysExported" : command => do
  let content ← fileNamed (getIonGoSerializer% Unexported "gotest") "Unexported.go"
  if check content "\tbar " then
    Lean.logError s!"Field identifiers must be exported:\n{content}"; return
  if !check content "\tBar    *big.Int" then
    Lean.logError s!"Expected the stripped name to be capitalised:\n{content}"; return
  -- Non-ASCII names strip to nothing, fall back to `Field`, and disambiguate.
  if !check content "\tField  *big.Int" then Lean.logError "Missing Field fallback"; return
  if !check content "\tField_ *big.Int" then Lean.logError "Missing disambiguated Field_"; return
  -- The Ion keys are the raw Lean names throughout: the wire format is untouched.
  for key in ["$bar", "σ", "τ"] do
    if !check content s!"fieldName(w, \"{key}\")" then
      Lean.logError s!"Ion key {key} must be preserved"; return
  -- Hard-failure variant: `writeBigInt` is an unexported runtime helper, and
  -- capitalising is what keeps the generated name clear of it.
  let writer ← fileNamed (getIonGoSerializer% «$writeBigInt» "gotest") "WriteBigInt.go"
  if !check writer "type WriteBigInt struct{ N *big.Int }" then
    Lean.logError s!"Expected an exported WriteBigInt:\n{writer}"; return

#testAlwaysExported

-- Test 15: the package-wide registry must NOT reject a type whose name matches
-- another type's marker method. A method name is never a package-scope name in
-- Go, so this is legal and must generate.
elab "#testMarkerIsNotAPackageName" : command => do
  let files := getIonGoSerializer% Root4 "gotest"
  let foo ← fileNamed files "Foo4.go"
  if !check foo "func (Foo4A) isFoo4() {}" then
    Lean.logError s!"Missing marker method:\n{foo}"; return
  let isFoo ← fileNamed files "IsFoo4.go"
  if !check isFoo "type IsFoo4 struct{ N *big.Int }" then
    Lean.logError s!"A type may share a name with another type's marker:\n{isFoo}"; return

#testMarkerIsNotAPackageName

-- Test 16: an invalid Go package name is rejected where it is written, rather
-- than becoming a syntax error in every emitted file.
elab "#testPackageNameValidated" : command => do
  let msg ← Lean.Elab.Command.liftTermElabM do
    try
      let stx ← `(getIonGoSerializer% Point "func 123-bad")
      let _ ← Lean.Elab.Term.withoutErrToSorry (Lean.Elab.Term.elabTerm stx none)
      return ""
    catch e => return (← e.toMessageData.toString)
  if msg.isEmpty then
    Lean.logError "An invalid Go package name must be rejected"; return
  if !check msg "not a valid Go package name" then
    Lean.logError s!"Unexpected error: {msg}"; return

#testPackageNameValidated

/-! ### The reserved-name gate

`goReservedWords` has to cover every package-scope name the three fixed runtime
files declare, because generated code shares their Go package.

`Strata.Go.packageScopeNames` derives the list from the runtime source. This test
re-derives it *independently*, from the files `runtimeFiles` actually emits, and
checks the reserved set covers everything — so a gap in either scanner shows up
as a failing test instead of a quietly un-reserved name.
-/

/-- An independent scanner for package-scope Go declarations, deliberately not
sharing code with `Strata.Go.GoIonRuntime.goTopLevelNames`: two implementations
that agree is the whole point. -/
meta def scanPackageScopeNames (source : String) : Array String := Id.run do
  let isIdentChar := fun (c : Char) => c.isAlphanum || c == '_'
  let mut found : Array String := #[]
  let mut inGroup := false
  for line in source.splitOn "\n" do
    if inGroup then
      if line.startsWith ")" then
        inGroup := false
      else if line.startsWith "\t" then
        let name := ((line.drop 1).takeWhile isIdentChar).toString
        if !name.isEmpty then found := found.push name
    else if line == "const (" || line == "var (" then
      inGroup := true
    else if line.startsWith "func (" then
      -- A method: its name lives in the receiver's method set, not package scope.
      pure ()
    else
      for keyword in ["type ", "func ", "const ", "var "] do
        if line.startsWith keyword then
          let name := ((line.drop keyword.length).takeWhile isIdentChar).toString
          if !name.isEmpty then found := found.push name
  return found

-- Test 17: every package-scope name the runtime declares is reserved, and the
-- source-derived list agrees with an independent scan.
elab "#testReservedNameGate" : command => do
  let runtime := (getIonGoSerializer% Point "gotest").files.filter fun (n, _) =>
    n == "ion_value.go" || n == "ion_binary.go" || n == "opt.go"
  if runtime.size != 3 then
    Lean.logError s!"Expected 3 runtime files, found {runtime.size}"; return

  let mut scanned : Array String := #[]
  for (_, content) in runtime do
    scanned := scanned ++ scanPackageScopeNames content

  -- A scanner that finds nothing would make the coverage check below vacuous, so
  -- pin one sentinel per declaration shape it has to recognise, across all three
  -- files. A count would be the wrong assertion: it changes every time the
  -- runtime grows a helper, which is exactly when this test must keep working.
  for (sentinel, shape) in [
      ("Decimal", "a column-zero `type`"),
      ("IonWriter", "a column-zero type alias"),
      ("writeBigInt", "a column-zero `func`"),
      ("writeNat", "a column-zero `func`"),
      ("errNilValue", "a column-zero `var`"),
      ("isNilIonMarshaler", "a column-zero `func`"),
      ("Opt", "a `func` in opt.go"),
      ("MarshalBinary", "a `func` in ion_binary.go")] do
    if !scanned.contains sentinel then
      Lean.logError s!"Scanner missed {sentinel}, {shape}"; return

  -- The gate itself.
  let missing := scanned.filter (!Strata.Go.isReservedGoName ·)
  if !missing.isEmpty then
    Lean.logError s!"These names are declared by the fixed runtime files but are \
      not in `goReservedWords`, so a Lean type of the same name would emit a Go \
      redeclaration: {missing.toList}. `Strata.Go.packageScopeNames` derives the \
      list from the runtime source — if it is being used and this still fails, \
      `goTopLevelNames` has a gap."; return

  -- And that the derived list agrees with this independent scan, so a gap in
  -- `goTopLevelNames` is reported here rather than only reaching `goReservedWords`.
  for name in scanned do
    if !Strata.Go.packageScopeNames.contains name then
      Lean.logError s!"`packageScopeNames` is missing {name}: `goTopLevelNames` \
        does not recognise the declaration that introduces it"; return

#testReservedNameGate

-- Test 11: the emitted package is gofmt-clean and passes `go vet` as written.
-- String assertions cannot establish that; this can. Local development may
-- skip without Go, but a Brazil or CI build must provide the toolchain.
elab "#testGoToolchain" : command => do
  unless ← haveGo do
    Lean.logWarning "Test skipped: go not found"
    return

  let dir : System.FilePath := "/tmp/strata-go-smoke"
  prepareTempDir dir

  -- Several closures at once, so the runtime files, the generic types, the
  -- nested containers and the zero-ctor interface all have to coexist in one
  -- Go package.
  let mut allFiles : Std.HashMap String String := {}
  for files in [getIonGoSerializer% Crate "gotest", getIonGoSerializer% League "gotest",
                getIonGoSerializer% Shape "gotest", getIonGoSerializer% Void "gotest",
                getIonGoSerializer% Tree "gotest", getIonGoSerializer% Wrapper "gotest",
                getIonGoSerializer% Team "gotest", getIonGoSerializer% «Widget?» "gotest",
                -- These types exercise flat package names, escaped type
                -- parameters and runtime-name capture. Compiling them together
                -- asserts that every generated identifier resolves correctly.
                getIonGoSerializer% CapturingBox "gotest",
                getIonGoSerializer% CapturingPair "gotest",
                getIonGoSerializer% GreekPair "gotest",
                getIonGoSerializer% IonWriter "gotest",
                getIonGoSerializer% Marshal "gotest",
                getIonGoSerializer% Unexported "gotest",
                getIonGoSerializer% «$writeBigInt» "gotest",
                getIonGoSerializer% Root4 "gotest"] do
    for (name, content) in files.files do allFiles := allFiles.insert name content

  writeGoFiles dir { files := allFiles.toArray }
  if let some reason ← writeGoModule dir "gotest" then
    Lean.logWarning s!"Test skipped: {reason}"
    cleanupTempDir dir
    return

  if let some err ← checkGoClean dir then Lean.throwError err

  -- A generic sum type is tied to its type argument: a constructor instantiated
  -- at one type must not satisfy the interface instantiated at another, or Go
  -- would marshal a `Box Point` where Lean expects a `Point`. Built from a
  -- separate package (after `go vet ./...`, which would otherwise see the
  -- deliberately ill-typed one), with a well-typed twin so a failure is known to
  -- come from the mismatch rather than from the consumer itself.
  let consumer (item : String) : String :=
    s!"package main\n\nimport g \"gotest\"\n\n\
       var _ g.Holder[g.Point] = g.HolderFull[{item}]\{}\n\nfunc main() \{}\n"
  IO.FS.createDirAll (dir / "holdermatch")
  IO.FS.writeFile (dir / "holdermatch" / "main.go") (consumer "g.Point")
  if let some err ← runTool "go" #["build", "-buildvcs=false", "-o", "/dev/null", "./holdermatch"] dir then
    Lean.throwError s!"HolderFull[Point] must satisfy Holder[Point]:\n{err}"
  IO.FS.createDirAll (dir / "holdermismatch")
  IO.FS.writeFile (dir / "holdermismatch" / "main.go") (consumer "g.Box[g.Point]")
  match ← runTool "go" #["build", "-buildvcs=false", "-o", "/dev/null", "./holdermismatch"] dir with
  | none =>
    Lean.throwError "HolderFull[Box[Point]] was accepted as a Holder[Point]: the \
                    marker method does not mention the type parameter"
  | some err =>
    unless (err.splitOn "isHolder").length > 1 do
      Lean.throwError s!"HolderFull[Box[Point]] was rejected for an unexpected reason:\n{err}"
  cleanupTempDir dir

#testGoToolchain

end Strata.Go.Test

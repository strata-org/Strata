/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Analysis.Productivity
meta import Strata.DDM.BuiltinDialects

namespace Strata.DDM.Productivity.Tests

/-! Hand-built grammar fixtures.  We sidestep the dialect macro and construct
`Dialect` values directly so we can express deliberately-broken grammars and
assert exact productivity outcomes.  Everything here is `meta` because DDM
AST values are only available at elaboration time. -/

private meta def D : DialectName := "Test"

private meta def cat (n : String) : QualifiedIdent := { dialect := D, name := n }
private meta def syn (n : String) : Decl := .syncat { name := n }

/-- Build an op decl with category arguments only. -/
private meta def mkOp (name : String) (result : QualifiedIdent)
    (args : Array QualifiedIdent) : Decl :=
  let argDecls : ArgDecls := .ofArray <| args.mapIdx fun i a =>
    { ident := s!"a{i}",
      kind := .cat (.atom .none a) }
  let syntaxAtoms : List SyntaxDefAtom :=
    .str name :: (args.toList.mapIdx fun i _ => .ident i 0)
  .op {
    name := name,
    argDecls := argDecls,
    category := result,
    syntaxDef := .ofList syntaxAtoms,
  }

private meta def mkDialect (decls : Array Decl) : Dialect :=
  Dialect.ofArray D #[] decls

private meta def mkDialectMap (d : Dialect) : DialectMap :=
  DialectMap.ofList! [d]

/-! ## Test 1 — single nullary operator is productive. -/

private meta def t1 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[
      syn "A",
      mkOp "aMk" (cat "A") #[]
    ])) D

#guard t1.isOk
#guard t1.productive == #[cat "A"]
#guard t1.unproductive.isEmpty

/-! ## Test 2 — list shape (nil + cons) is productive. -/

private meta def t2 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[
      syn "Elem",
      syn "Lst",
      mkOp "elemMk" (cat "Elem") #[],
      mkOp "lstNil"  (cat "Lst")  #[],
      mkOp "lstCons" (cat "Lst")  #[cat "Elem", cat "Lst"]
    ])) D

#guard t2.isOk
#guard t2.productive.size == 2
#guard t2.unproductive.isEmpty

/-! ## Test 3 — pure self-loop with no base case is unproductive. -/

private meta def t3 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[
      syn "Loop",
      mkOp "loopOnly" (cat "Loop") #[cat "Loop"]
    ])) D

#guard ! t3.isOk
#guard t3.productive.isEmpty
#guard t3.unproductive.size == 1
#guard t3.unproductive[0]!.category == cat "Loop"
#guard t3.unproductive[0]!.blockers.size == 1
#guard t3.unproductive[0]!.blockers[0]!.opName == "loopOnly"
#guard t3.unproductive[0]!.blockers[0]!.unmetArgCats == #[cat "Loop"]

/-! ## Test 4 — mutual cycle with no base case in the SCC: both unproductive. -/

private meta def t4 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[
      syn "A",
      syn "B",
      mkOp "aFromB" (cat "A") #[cat "B"],
      mkOp "bFromA" (cat "B") #[cat "A"]
    ])) D

#guard ! t4.isOk
#guard t4.productive.isEmpty
#guard t4.unproductive.size == 2

/-! ## Test 5 — cascading: B unproductive ⇒ A that depends on B is too,
even though A is not in any cycle. -/

private meta def t5 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[
      syn "A",
      syn "B",
      mkOp "aFromB"  (cat "A") #[cat "B"],
      mkOp "bSelf"   (cat "B") #[cat "B"]
    ])) D

#guard ! t5.isOk
#guard t5.productive.isEmpty
#guard t5.unproductive.size == 2

/-! ## Test 6 — category declared with no operator at all is unproductive,
and the diagnostic notes the empty blocker list. -/

private meta def t6 : Result :=
  Productivity.check
    (mkDialectMap (mkDialect #[ syn "Empty" ])) D

#guard ! t6.isOk
#guard t6.unproductive.size == 1
#guard t6.unproductive[0]!.category == cat "Empty"
#guard t6.unproductive[0]!.blockers.isEmpty

/-! ## Test 7 — framework atoms (`Init.Ident`, …) are trusted, so an
op taking one of them as an argument is not blocked on it. -/

private meta def initMap : DialectMap :=
  DialectMap.ofList! [Strata.initDialect]

private meta def t7Dialect : Dialect :=
  Dialect.ofArray D #[Strata.initDialect.name] #[
    syn "UsesIdent",
    mkOp "wrap" (cat "UsesIdent") #[q`Init.Ident]
  ]

private meta def t7Map : DialectMap :=
  initMap.insert! t7Dialect

private meta def t7 : Result := Productivity.check t7Map D

#guard t7.isOk
#guard t7.productive == #[cat "UsesIdent"]

/-! ## Test 8 — nullable container without `@[nonempty]`: inner type's
productivity is irrelevant (empty list saves us). -/

/-- Op decl with one argument of type `outer (inner)`, optionally `@[nonempty]`. -/
private meta def mkOpNested
    (name : String) (result : QualifiedIdent)
    (outer inner : QualifiedIdent)
    (nonempty : Bool := false) : Decl :=
  let nestedCat : SyntaxCat :=
    { ann := .none, name := outer, args := #[.atom .none inner] }
  let metadata : Metadata :=
    if nonempty then
      Metadata.ofArray #[{ ident := q`StrataDDL.nonempty, args := #[] }]
    else {}
  let argDecls : ArgDecls := .ofArray #[
    { ident := "x", kind := .cat nestedCat, metadata := metadata }
  ]
  .op {
    name := name,
    argDecls := argDecls,
    category := result,
    syntaxDef := .ofList [.str name, .ident 0 0],
  }

private meta def t8Dialect : Dialect :=
  Dialect.ofArray D #[Strata.initDialect.name] #[
    syn "Foo",
    syn "Bar",
    mkOpNested "barFromFoos" (cat "Bar")
      q`Init.CommaSepBy (cat "Foo")
  ]

private meta def t8Map : DialectMap := initMap.insert! t8Dialect

private meta def t8 : Result := Productivity.check t8Map D

#guard ! t8.isOk
#guard t8.productive == #[cat "Bar"]
#guard t8.unproductive.size == 1
#guard t8.unproductive[0]!.category == cat "Foo"

/-! ## Test 9 — nullable container *with* `@[nonempty]`: inner type's
productivity becomes mandatory. -/

private meta def t9Dialect : Dialect :=
  Dialect.ofArray D #[Strata.initDialect.name] #[
    syn "Foo",
    syn "Bar",
    mkOpNested "barFromFoos" (cat "Bar")
      q`Init.CommaSepBy (cat "Foo") (nonempty := true)
  ]

private meta def t9Map : DialectMap := initMap.insert! t9Dialect

private meta def t9 : Result := Productivity.check t9Map D

#guard ! t9.isOk
#guard t9.productive.isEmpty
#guard t9.unproductive.size == 2

/-! ## Test 10 — `Init.Option` is unconditionally nullable. -/

private meta def t10Dialect : Dialect :=
  Dialect.ofArray D #[Strata.initDialect.name] #[
    syn "Foo",
    syn "Bar",
    mkOpNested "barFromMaybeFoo" (cat "Bar")
      q`Init.Option (cat "Foo")
  ]

private meta def t10Map : DialectMap := initMap.insert! t10Dialect

private meta def t10 : Result := Productivity.check t10Map D

#guard ! t10.isOk
#guard t10.productive == #[cat "Bar"]
#guard t10.unproductive.size == 1
#guard t10.unproductive[0]!.category == cat "Foo"

end Strata.DDM.Productivity.Tests

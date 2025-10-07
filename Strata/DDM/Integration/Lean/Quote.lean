/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Lean.Elab.Term

namespace Strata

open Lean

private def quoteOption (a : Option Term) : Term :=
  match a with
  | none => Syntax.mkCApp ``Option.none #[]
  | some a => Syntax.mkCApp ``Option.some #[a]

private def quoteArray (a : Array Term) : Term :=
  if a.size <= 8 then
    let terms := a
    Syntax.mkCApp (Name.mkStr2 "Array" ("mkArray" ++ toString a.size)) terms
  else
    let e := Syntax.mkCApp ``Array.mkEmpty #[quote a.size]
    a.foldl (init := e) fun t a => Syntax.mkCApp ``Array.push #[t, a]

section
open Lean.Elab

/--
Lift a DDM AST constructor that takes a polymorphic annotation value to
the syntax level with the correct number of arguments.

For example, `astQuote! ArgF.ident ann (quote e)` returns syntax for (ArgF.ident ann e).
-/
syntax:max (name := astQuoteElab) "astQuote!" ident term:max term:max* : term

@[term_elab astQuoteElab]
def astQuoteElabImpl : Term.TermElab := fun stx _expectedType => do
  let a := stx.getArgs
  assert! a.size = 4
  let ident := a[1]!
  assert! ident.isIdent
  let ctor ← realizeGlobalConstNoOverloadWithInfo ident
  let cv ← getConstVal ctor

  let ann ← Term.elabTerm a[2]! none
  let annType ← Meta.inferType ann
  let termExpr := toExpr `term
  let annTypeInst ← Meta.synthInstance (mkApp2 (mkConst ``Quote) annType termExpr)
  let .sort (.succ .zero) ←  Meta.inferType annType
    | throwError "Annotation must have type Type."
  let annExpr := mkApp4 (mkConst ``quote) annType termExpr annTypeInst ann

  let argc := cv.type.getForallBinderNames.length
  if argc < 2 then
    throwErrorAt ident "Expected constructor with annotation argument."

  let termList := a[3]!
  assert! termList.isOfKind nullKind
  let terms := termList.getArgs
  if argc - 2 ≠ terms.size then
    throwErrorAt ident "Expected {argc - 2} arguments; found {terms.size} arguments."
  let eltType := mkApp (mkConst ``TSyntax) (toExpr [`term])
  let a ← terms.mapM_off (init := #[annExpr]) fun ts => Term.elabTerm ts (some eltType)
  return mkApp2 (mkConst ``Lean.Syntax.mkCApp) (toExpr ctor) (arrayToExpr eltType a)

end

namespace SyntaxCatF

protected def quote {α} [Quote α] (cat : SyntaxCatF α) : Term :=
  let r := quoteArray <| cat.args.map fun x => x.quote
  astQuote! SyntaxCatF.mk cat.ann (quote cat.name) r
termination_by sizeOf cat
decreasing_by
  simp [sizeOf_spec cat]
  decreasing_tactic

instance {α} [Quote α] : Quote (SyntaxCatF α)  where
  quote := SyntaxCatF.quote

end SyntaxCatF

namespace TypeExprF

protected def quote {α} [Quote α] : TypeExprF α → Term
| .ident ann nm a =>
  astQuote! ident ann (quote nm) (quoteArray (a.map (·.quote)))
| .bvar ann idx =>
  astQuote! bvar ann (quote idx)
| .fvar ann idx a =>
  astQuote! fvar ann (quote idx) (quoteArray (a.map (·.quote)))
| .arrow ann a r =>
  astQuote! arrow ann a.quote r.quote
termination_by e => e

instance {α} [Quote α] : Quote (TypeExprF α) where
  quote := TypeExprF.quote

end TypeExprF

mutual

protected def ArgF.quote {α} [Quote α] : ArgF α → Term
| .op o => Syntax.mkCApp ``ArgF.op #[o.quote]
| .expr e => Syntax.mkCApp ``ArgF.expr #[e.quote]
| .type e => Syntax.mkCApp ``ArgF.type #[quote e]
| .cat e => Syntax.mkCApp ``ArgF.cat #[quote e]
| .ident ann e => astQuote! ArgF.ident ann (quote e)
| .num ann e => astQuote! ArgF.num ann (quote e)
| .decimal ann e => astQuote! ArgF.decimal ann (quote e)
| .strlit ann e => astQuote! ArgF.strlit ann (quote e)
| .option ann a => astQuote! ArgF.option ann (quoteOption (a.attach.map (fun ⟨e, _⟩ => e.quote)))
| .seq ann a => astQuote! ArgF.seq ann (quoteArray (a.map (·.quote)))
| .commaSepList ann a => astQuote! ArgF.commaSepList ann (quoteArray (a.map (·.quote)))
termination_by a => sizeOf a

protected def ExprF.quote {α} [Quote α] : ExprF α → Term
| .bvar ann s => astQuote! ExprF.bvar ann (quote s)
| .fvar ann idx => astQuote! ExprF.fvar ann (quote idx)
| .fn ann ident => astQuote! ExprF.fn ann (quote ident)
| .app ann f a => astQuote! ExprF.app ann f.quote a.quote
termination_by e => sizeOf e

def OperationF.quote {α} [Quote α] (op : OperationF α) : Term :=
  let r := quoteArray <| op.args.map fun x => x.quote
  astQuote! OperationF.mk op.ann (quote op.name) r
termination_by sizeOf op
decreasing_by
  simp [OperationF.sizeOf_spec]
  decreasing_tactic

end

instance {α} [Quote α] : Quote (ArgF α) where
  quote := ArgF.quote

instance {α} [Quote α] : Quote (ExprF α) where
  quote := ExprF.quote

instance {α} [Quote α] : Quote (OperationF α) where
  quote := OperationF.quote

instance : Quote String.Pos where
  quote e := Syntax.mkCApp ``String.Pos.mk #[quote e.byteIdx]

namespace SourceRange

instance : Quote SourceRange where
  quote x := Syntax.mkCApp ``mk #[quote x.start, quote x.stop]

end SourceRange

namespace PreType

protected def quote : PreType → Term
| .ident ann nm a =>
  Syntax.mkCApp ``ident #[quote ann, quote nm, quoteArray (a.map (·.quote))]
| .bvar ann idx => Syntax.mkCApp ``bvar #[quote ann, quote idx]
| .fvar ann idx a =>
  Syntax.mkCApp ``fvar #[quote ann, quote idx, quoteArray (a.map (·.quote))]
| .arrow ann a r => Syntax.mkCApp ``arrow #[quote ann, a.quote, r.quote]
| .funMacro ann i r =>
  Syntax.mkCApp ``funMacro #[quote ann, quote i, r.quote]

instance : Quote PreType where
  quote := PreType.quote

end PreType

namespace MetadataArg

protected def quote : MetadataArg → Term
  | .bool b    => Syntax.mkCApp ``bool #[quote b]
  | .num n     => Syntax.mkCApp ``num #[quote n]
  | .catbvar n => Syntax.mkCApp ``catbvar #[quote n]
  | .option ma => Syntax.mkCApp ``option #[quoteOption (ma.attach.map fun ⟨a, _⟩ => a.quote)]

instance : Quote MetadataArg where
  quote := MetadataArg.quote

end MetadataArg

instance : Quote MetadataAttr where
  quote a := Syntax.mkCApp ``MetadataAttr.mk #[quote a.ident, quote a.args]

instance : Quote Metadata where
  quote m := Syntax.mkCApp ``Metadata.ofArray #[quote m.toArray]

namespace ArgDeclKind

instance : Quote ArgDeclKind where
  quote
  | .type tp => Syntax.mkCApp ``type #[quote tp]
  | .cat c => Syntax.mkCApp ``cat #[quote c]

end ArgDeclKind

instance ArgDecl.instQuote : Quote ArgDecl where
  quote b := Syntax.mkCApp ``mk #[quote b.ident, quote b.kind, quote b.metadata]

namespace SyntaxDefAtom

protected def quote : SyntaxDefAtom → Term
| .ident v p => Syntax.mkCApp ``ident #[quote v, quote p]
| .str l     => Syntax.mkCApp ``str #[quote l]
| .indent n a => Syntax.mkCApp ``indent #[quote n, quoteArray (a.map (·.quote))]

instance : Quote SyntaxDefAtom where
  quote := SyntaxDefAtom.quote

end SyntaxDefAtom

namespace SyntaxDef

instance : Quote SyntaxDef where
  quote s := Syntax.mkCApp ``SyntaxDef.mk #[quote s.atoms, quote s.prec]

end SyntaxDef

instance : Quote ArgDecls where
  quote a :=  Syntax.mkCApp ``ArgDecls.ofArray #[quote a.toArray]

instance : Quote SynCatDecl where
  quote d :=  Syntax.mkCApp ``SynCatDecl.mk #[quote d.name, quote d.argNames]

instance : Quote OpDecl where
  quote d := Syntax.mkCApp ``OpDecl.mk1 #[
    quote d.name,
    quote d.argDecls,
    quote d.category,
    quote d.syntaxDef,
    quote d.metadata
  ]

instance {α β} [Quote α] [Quote β] : Quote (Ann α β) where
  quote p := Syntax.mkCApp ``Ann.mk #[quote p.ann, quote p.val]

instance : Quote TypeDecl where
  quote d := Syntax.mkCApp ``TypeDecl.mk #[quote d.name, quote d.argNames]

instance : Quote FunctionDecl where
  quote d := Syntax.mkCApp ``FunctionDecl.mk #[
    quote d.name,
    quote d.argDecls,
    quote d.result,
    quote d.syntaxDef,
    quote d.metadata
  ]

namespace MetadataArgType

protected def quote : MetadataArgType → Term
| .bool     => mkCIdent ``bool
| .num      => mkCIdent ``num
| .ident    => mkCIdent ``ident
| .opt tp => Syntax.mkCApp ``opt #[tp.quote]

instance : Quote MetadataArgType where
  quote := MetadataArgType.quote

end MetadataArgType

instance : Quote MetadataArgDecl where
  quote d := Syntax.mkCApp ``MetadataArgDecl.mk #[quote d.ident, quote d.type]

instance : Quote MetadataDecl where
  quote d := Syntax.mkCApp ``MetadataDecl.mk #[quote d.name, quote d.args]

instance : Quote Decl where
  quote
  | .syncat d => Syntax.mkCApp ``Decl.syncat #[quote d]
  | .op d => Syntax.mkCApp ``Decl.op #[quote d]
  | .type d => Syntax.mkCApp ``Decl.type #[quote d]
  | .function d =>  Syntax.mkCApp ``Decl.function #[quote d]
  | .metadata d => Syntax.mkCApp ``Decl.metadata #[quote d]

instance : Quote Dialect where
  quote d : Term :=
    Syntax.mkCApp ``Dialect.ofArray #[
        quote d.name,
        quote d.imports,
        quote d.declarations
      ]

namespace DialectMap

instance : Quote DialectMap where
  quote d := Syntax.mkCApp ``DialectMap.ofList! #[quote d.toList]

end DialectMap

instance : Quote Program where
  quote p : Term :=
    Syntax.mkCApp ``Program.create #[
      quote p.dialects,
      quote p.dialect,
      quote p.commands
    ]

end Strata

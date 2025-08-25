/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST

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

namespace TypeExprF

protected def quote {α} [Quote α] : TypeExprF α → Term
| .ident n nm a =>
  let a := a.map (·.quote)
  Syntax.mkCApp ``ident #[quote n, quote nm, quoteArray a]
| .bvar n idx => Syntax.mkCApp ``bvar #[quote n, quote idx]
| .fvar n idx a =>
  let a := a.map (·.quote)
  Syntax.mkCApp ``fvar #[quote n, quote idx, quoteArray a]
| .arrow n a r => Syntax.mkCApp ``arrow #[quote n, a.quote, r.quote]
termination_by e => e

instance {α} [Quote α] : Quote (TypeExprF α) where
  quote := TypeExprF.quote

end TypeExprF

namespace SyntaxCat

def metaAtom (a : Term) : Term := Syntax.mkCApp ``atom #[a]

protected def quote : SyntaxCat → Term
| .atom a => metaAtom (quote a)
| .app f a => Syntax.mkCApp ``SyntaxCat.app #[f.quote, a.quote]

instance : Quote SyntaxCat where
  quote := SyntaxCat.quote

end SyntaxCat

namespace ArgF

def metaCat (t:Term) : Term := Syntax.mkCApp ``cat #[t]

end ArgF

mutual

protected def ArgF.quote {α} [Quote α] : ArgF α → Term
| .op o => Syntax.mkCApp ``ArgF.op #[o.quote]
| .expr e     => Syntax.mkCApp ``ArgF.expr #[e.quote]
| .type e     => Syntax.mkCApp ``ArgF.type #[quote e]
| .cat e      => Syntax.mkCApp ``ArgF.cat #[quote e]
| .ident e    => Syntax.mkCApp ``ArgF.ident #[quote e]
| .num e    => Syntax.mkCApp ``ArgF.num #[quote e]
| .decimal e => Syntax.mkCApp ``ArgF.decimal #[quote e]
| .strlit e   => Syntax.mkCApp ``ArgF.strlit #[quote e]
| .option a => Syntax.mkCApp ``ArgF.option #[quoteOption (a.attach.map (fun ⟨e, _⟩ => e.quote))]
| .seq a => Syntax.mkCApp ``ArgF.seq #[quoteArray (a.map (·.quote))]
| .commaSepList a => Syntax.mkCApp ``ArgF.commaSepList #[quoteArray (a.map (·.quote))]
termination_by a => sizeOf a


protected def ExprF.quote {α} [Quote α] : ExprF α → Term
| .bvar s => Syntax.mkCApp ``ExprF.bvar #[quote s]
| .fvar idx => Syntax.mkCApp ``ExprF.fvar #[quote idx]
| .fn ident => Syntax.mkCApp ``ExprF.fn #[quote ident]
| .app f a => Syntax.mkCApp ``ExprF.app #[f.quote, a.quote ]
termination_by e => sizeOf e

def OperationF.quote {α} [Quote α] (op : OperationF α) : Term :=
  let r := quoteArray <| op.args.map fun x => x.quote
  Syntax.mkCApp ``OperationF.mk #[quote op.ann, quote op.name, r]
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

namespace SourceLoc

instance : Quote SourceLoc where
  quote x := Syntax.mkCApp ``SourceLoc.mk #[quote x.start, quote x.stop]

end SourceLoc

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

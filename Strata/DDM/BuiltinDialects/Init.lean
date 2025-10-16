/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.BuiltinDialects.BuiltinM

namespace Strata

open Elab
open Parser (minPrec)

def SyntaxCat.mkOpt (c:SyntaxCat) : SyntaxCat := { ann := .none, name := q`Init.Option, args := #[c] }
def SyntaxCat.mkSeq (c:SyntaxCat) : SyntaxCat := { ann := .none, name := q`Init.Seq, args := #[c] }
def SyntaxCat.mkCommaSepBy (c:SyntaxCat) : SyntaxCat := { ann := .none, name := q`Init.CommaSepBy, args := #[c] }

def initDialect : Dialect := BuiltinM.create! "Init" #[] do
  let Ident : ArgDeclKind := .cat <| .atom .none q`Init.Ident
  let Num : SyntaxCat := .atom .none q`Init.Num
  let Str : SyntaxCat := .atom .none q`Init.Str

  declareAtomicCat q`Init.Ident
  declareAtomicCat q`Init.Num
  declareAtomicCat q`Init.Decimal
  declareAtomicCat q`Init.Str

  declareCat q`Init.Option #["a"]

  declareCat q`Init.Seq #["a"]

  declareCat q`Init.CommaSepBy #["a"]

  let QualifiedIdent := q`Init.QualifiedIdent
  declareCat QualifiedIdent
  declareOp {
     name := "qualifiedIdentType",
     argDecls := .empty,
     category := QualifiedIdent,
     syntaxDef := .ofList [.str "Type"],
  }
  declareOp {
     name := "qualifiedIdentImplicit",
     argDecls := .ofArray #[
        { ident := "name", kind := Ident }
     ],
     category := QualifiedIdent,
     syntaxDef := .ofList [.ident 0 0],
  }
  declareOp {
     name := "qualifiedIdentExplicit",
     argDecls := .ofArray #[
        { ident := "dialect", kind := Ident },
        { ident := "name", kind := Ident }
     ],
     category := QualifiedIdent,
     syntaxDef := .ofList [.ident 0 0, .str ".", .ident 1 0],
  }

  let TypeExprId := q`Init.TypeExpr
  let TypeExpr : ArgDeclKind := .cat (.atom .none TypeExprId)
  declareCat TypeExprId
  declareOp {
    name := "TypeIdent",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat <| .atom .none QualifiedIdent }
    ]
    category := TypeExprId,
    syntaxDef := .ofList [.ident 0 maxPrec]
  }
  declareOp {
    name := "TypeParen",
    argDecls := .ofArray #[
      { ident := "value", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp {
    name := "TypeArrow",
    argDecls := .ofArray #[
      { ident := "lhs", kind := TypeExpr },
      { ident := "rhs", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList (prec := 30) [.ident 0 30, .str "->", .ident 1 29]
  }
  declareOp {
    name := "TypeApp",
    argDecls := .ofArray #[
      { ident := "fn", kind := TypeExpr },
      { ident := "val", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList (prec := 40) [.ident 0 39, .ident 1 40]
  }

  let «Type» := q`Init.Type
  declareCat «Type»
  declareOp  {
    name := "mkType",
    argDecls := .ofArray #[
      { ident := "type", kind := TypeExpr }
    ],
    category := «Type»,
    syntaxDef := .ofList [.ident 0 0]
  }

  let Expr := q`Init.Expr
  declareCat Expr
  declareOp {
    name := "exprIdent",
    argDecls := .ofArray #[
      { ident := "value", kind := Ident }
    ],
    category := Expr,
    syntaxDef := .ofList [.ident 0 0],
  }
  declareOp {
    name := "exprParen",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat (.atom .none Expr) }
    ],
    category := Expr,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp {
    name := "exprApp",
    argDecls := .ofArray #[
      { ident := "function", kind := Ident },
      { ident := "args", kind := .cat <| .mkCommaSepBy (.atom .none Expr) }
    ],
    category := Expr,
    syntaxDef := .ofList [.ident 0 0, .str "(", .ident 1 0, .str ")"]
  }

  let MetadataArg := q`Init.MetadataArg
  declareCat MetadataArg
  declareOp {
    name := "MetadataArgParen",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat (.atom .none MetadataArg) }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp {
    name := "MetadataArgNum",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat Num }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.ident 0 0]
  }
  declareOp {
    name := "MetadataArgIdent",
    argDecls := .ofArray #[
      { ident := "value", kind := Ident }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.ident 0 0]
  }
  declareOp {
    name := "MetadataArgTrue",
    argDecls := .empty,
    category := MetadataArg,
    syntaxDef := .ofList [.str "true"]
  }
  declareOp {
    name := "MetadataArgFalse",
    argDecls := .empty,
    category := MetadataArg,
    syntaxDef := .ofList [.str "false"]
  }
  declareOp {
    name := "MetadataArgSome",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat (.atom .none MetadataArg) }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.str "some", .ident 0 appPrec]
  }
  declareOp {
    name := "MetadataArgNone"
    argDecls := .empty
    category := MetadataArg
    syntaxDef := .ofList [.str "none"]
  }

  let MetadataArgs := q`Init.MetadataArgs
  declareCat MetadataArgs
  declareOp {
    name := "MetadataArgsMk",
    argDecls := .ofArray #[
      { ident := "args", kind := .cat <| .mkCommaSepBy <| .atom .none MetadataArg }
    ],
    category := MetadataArgs,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }

  let MetadataAttr := q`Init.MetadataAttr
  declareCat MetadataAttr
  declareOp {
    name := "MetadataAttrMk",
    argDecls := .ofArray #[
      { ident := "name", kind := .cat <| .atom .none QualifiedIdent },
      { ident := "args", kind := .cat <| .mkOpt <| .atom .none MetadataArgs }
    ],
    category := MetadataAttr,
    syntaxDef := .ofList [.ident 0 0, .ident 1 0]
  }

  let Metadata := q`Init.Metadata
  declareCat Metadata
  declareOp {
    name := "MetadataMk",
    argDecls := .ofArray #[
      { ident := "attrs", kind := .cat <| .mkCommaSepBy <| .atom .none MetadataAttr }
    ],
    category := Metadata,
    syntaxDef := .ofList [.str "@[", .ident 0 0, .str "]"]
  }

  let Command := q`Init.Command
  declareCat Command

  let BindingType := q`Init.BindingType
  declareCat BindingType
  declareOp  {
    name := "mkBindingType",
    argDecls := .ofArray #[
      { ident := "type", kind := TypeExpr }
    ],
    category := BindingType,
    syntaxDef := .ofList [.ident 0 0]
  }

  -- `TypesP` is used type parameters that allow either a type or the type of types (Type).
  let TypeP := q`Init.TypeP
  declareCat TypeP
  declareOp  {
    name := "mkTypeP",
    argDecls := .ofArray #[
      { ident := "type", kind := TypeExpr }
    ],
    category := TypeP,
    syntaxDef := .ofList [.ident 0 0]
  }

  let SyntaxAtomPrec := q`Init.SyntaxAtomPrec
  declareCat SyntaxAtomPrec
  declareOp {
    name := "syntaxAtomPrec",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat Num }
    ],
    category := SyntaxAtomPrec,
    syntaxDef := .ofList [.str ":", .ident 0 0],
  }

  let SyntaxAtom := q`Init.SyntaxAtom
  declareCat SyntaxAtom
  declareOp {
    name := "syntaxAtomIdent",
    argDecls := .ofArray #[
      { ident := "ident", kind := Ident },
      { ident := "prec", kind := .cat <| .mkOpt <| .atom .none SyntaxAtomPrec }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.ident 0 0, .ident 1 0],
    metadata := .empty,
  }
  declareOp {
    name := "syntaxAtomString",
    argDecls := .ofArray #[
      { ident := "value", kind := .cat Str }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.ident 0 0],
  }
  declareOp {
    name := "syntaxAtomIndent",
    argDecls := .ofArray #[
      { ident := "indent", kind := .cat Num },
      { ident := "args", kind := .cat <| .mkSeq <| .atom .none SyntaxAtom }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.str "indent", .str "(", .ident 0 0, .str ", ", .ident 1 0, .str ")"],
  }

  let SyntaxDef := q`Init.SyntaxDef
  declareCat SyntaxDef
  declareOp {
    name := "mkSyntaxDef",
    argDecls := .ofArray #[
      { ident := "args", kind := .cat <| .mkSeq (.atom .none SyntaxAtom) }
    ],
    category := SyntaxDef,
    syntaxDef := .ofList [.ident 0 0],
  }

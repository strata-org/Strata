/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DDM.BuiltinDialects.DeclM

namespace Strata

open Elab
open Parser (minPrec)

def initializeInitDialect : DeclM Unit := do
  let Init := "Init"
  declareEmptyDialect Init

  let Ident : DeclBindingKind := .cat <| .atom q`Init.Ident
  let Num : SyntaxCat := .atom q`Init.Num
  let Str : SyntaxCat := .atom q`Init.Str

  declareAtomicCat q`Init.Ident Parser.identifier
  declareAtomicCat q`Init.Num Parser.numLit
  declareAtomicCat q`Init.Decimal Parser.decimalLit
  declareAtomicCat q`Init.Str Parser.strLit

  declareCat q`Init.Option #["a"]
  let mkOpt (c:SyntaxCat) : SyntaxCat := .app (.atom q`Init.Option) c

  declareCat q`Init.Seq #["a"]
  let mkSeq (c:SyntaxCat) : SyntaxCat := .app (.atom q`Init.Seq) c

  declareCat q`Init.CommaSepBy #["a"]
  let mkCommaSepBy (c:SyntaxCat) : SyntaxCat := .app (.atom q`Init.CommaSepBy) c

  let QualifiedIdent := q`Init.QualifiedIdent
  declareCat QualifiedIdent
  declareOp Init {
     name := "qualifiedIdentType",
     argDecls := #[],
     category := QualifiedIdent,
     syntaxDef := .ofList [.str "Type"],
  }
  declareOp Init {
     name := "qualifiedIdentImplicit",
     argDecls := #[
        { ident := "name", kind := Ident }
     ],
     category := QualifiedIdent,
     syntaxDef := .ofList [.ident 0 0],
  }
  declareOp Init {
     name := "qualifiedIdentExplicit",
     argDecls := #[
        { ident := "dialect", kind := Ident },
        { ident := "name", kind := Ident }
     ],
     category := QualifiedIdent,
     syntaxDef := .ofList [.ident 0 0, .str ".", .ident 1 0],
  }

  let TypeExprId := q`Init.TypeExpr
  let TypeExpr : DeclBindingKind := .cat (.atom TypeExprId)
  declareCat TypeExprId
  declareOp Init {
    name := "TypeIdent",
    argDecls := #[
      { ident := "value", kind := .cat <| .atom QualifiedIdent }
    ]
    category := TypeExprId,
    syntaxDef := .ofList [.ident 0 maxPrec]
  }
  declareOp Init {
    name := "TypeParen",
    argDecls := #[
      { ident := "value", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp Init {
    name := "TypeArrow",
    argDecls := #[
      { ident := "lhs", kind := TypeExpr },
      { ident := "rhs", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList (prec := 30) [.ident 0 30, .str "->", .ident 1 29]
  }
  declareOp Init {
    name := "TypeApp",
    argDecls := #[
      { ident := "fn", kind := TypeExpr },
      { ident := "val", kind := TypeExpr }
    ]
    category := TypeExprId,
    syntaxDef := .ofList (prec := 40) [.ident 0 39, .ident 1 40]
  }

  let «Type» := q`Init.Type
  declareCat «Type»
  declareOp Init  {
    name := "mkType",
    argDecls := #[
      { ident := "type", kind := TypeExpr }
    ],
    category := «Type»,
    syntaxDef := .ofList [.ident 0 0]
  }

  let Expr := q`Init.Expr
  declareCat Expr
  declareOp Init {
    name := "exprIdent",
    argDecls := #[
      { ident := "value", kind := Ident }
    ],
    category := Expr,
    syntaxDef := .ofList [.ident 0 0],
  }
  declareOp Init {
    name := "exprParen",
    argDecls := #[
      { ident := "value", kind := .cat (.atom Expr) }
    ],
    category := Expr,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp Init {
    name := "exprApp",
    argDecls := #[
      { ident := "function", kind := Ident },
      { ident := "args", kind := .cat <| mkCommaSepBy (.atom Expr) }
    ],
    category := Expr,
    syntaxDef := .ofList [.ident 0 0, .str "(", .ident 1 0, .str ")"]
  }

  let MetadataArg := q`Init.MetadataArg
  declareCat MetadataArg
  declareOp Init {
    name := "MetadataArgParen",
    argDecls := #[
      { ident := "value", kind := .cat (.atom MetadataArg) }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }
  declareOp Init {
    name := "MetadataArgNum",
    argDecls := #[
      { ident := "value", kind := .cat Num }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.ident 0 0]
  }
  declareOp Init {
    name := "MetadataArgIdent",
    argDecls := #[
      { ident := "value", kind := Ident }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.ident 0 0]
  }
  declareOp Init {
    name := "MetadataArgTrue",
    argDecls := #[],
    category := MetadataArg,
    syntaxDef := .ofList [.str "true"]
  }
  declareOp Init {
    name := "MetadataArgFalse",
    argDecls := #[],
    category := MetadataArg,
    syntaxDef := .ofList [.str "false"]
  }
  declareOp Init {
    name := "MetadataArgSome",
    argDecls := #[
      { ident := "value", kind := .cat (.atom MetadataArg) }
    ],
    category := MetadataArg,
    syntaxDef := .ofList [.str "some", .ident 0 appPrec]
  }
  declareOp Init {
    name := "MetadataArgNone",
    argDecls := #[],
    category := MetadataArg,
    syntaxDef := .ofList [.str "none"]
  }

  let MetadataArgs := q`Init.MetadataArgs
  declareCat MetadataArgs
  declareOp Init {
    name := "MetadataArgsMk",
    argDecls := #[
      { ident := "args", kind := .cat <| mkCommaSepBy <| .atom MetadataArg }
    ],
    category := MetadataArgs,
    syntaxDef := .ofList [.str "(", .ident 0 0, .str ")"]
  }

  let MetadataAttr := q`Init.MetadataAttr
  declareCat MetadataAttr
  declareOp Init {
    name := "MetadataAttrMk",
    argDecls := #[
      { ident := "name", kind := .cat <| .atom QualifiedIdent },
      { ident := "args", kind := .cat <| mkOpt <| .atom MetadataArgs }
    ],
    category := MetadataAttr,
    syntaxDef := .ofList [.ident 0 0, .ident 1 0]
  }

  let Metadata := q`Init.Metadata
  declareCat Metadata
  declareOp Init {
    name := "MetadataMk",
    argDecls := #[
      { ident := "attrs", kind := .cat <| mkCommaSepBy <| .atom MetadataAttr }
    ],
    category := Metadata,
    syntaxDef := .ofList [.str "@[", .ident 0 0, .str "]"]
  }

  let Command := q`Init.Command
  declareCat Command
  declareOp Init {
    name := "openCommand",
    argDecls := #[
      { ident := "name", kind := Ident }
    ],
    category := Command,
    syntaxDef := .ofList [.str "open", .ident 0 0, .str ";"]
  }

  let BindingType := q`Init.BindingType
  declareCat BindingType
  declareOp Init  {
    name := "mkBindingType",
    argDecls := #[
      { ident := "type", kind := TypeExpr }
    ],
    category := BindingType,
    syntaxDef := .ofList [.ident 0 0]
  }

  let TypeP := q`Init.TypeP
  declareCat TypeP
  declareOp Init  {
    name := "mkTypeP",
    argDecls := #[
      { ident := "type", kind := TypeExpr }
    ],
    category := TypeP,
    syntaxDef := .ofList [.ident 0 0]
  }

  let SyntaxAtomPrec := q`Init.SyntaxAtomPrec
  declareCat SyntaxAtomPrec
  declareOp Init {
    name := "syntaxAtomPrec",
    argDecls := #[
      { ident := "value", kind := .cat Num }
    ],
    category := SyntaxAtomPrec,
    syntaxDef := .ofList [.str ":", .ident 0 0],
  }

  let SyntaxAtom := q`Init.SyntaxAtom
  declareCat SyntaxAtom
  declareOp Init {
    name := "syntaxAtomIdent",
    argDecls := #[
      { ident := "ident", kind := Ident },
      { ident := "prec", kind := .cat <| mkOpt <| .atom SyntaxAtomPrec }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.ident 0 0, .ident 1 0],
    metadata := .empty,
  }
  declareOp Init {
    name := "syntaxAtomString",
    argDecls := #[
      { ident := "value", kind := .cat Str }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.ident 0 0],
  }
  declareOp Init {
    name := "syntaxAtomIndent",
    argDecls := #[
      { ident := "indent", kind := .cat Num },
      { ident := "args", kind := .cat <| mkSeq <| .atom SyntaxAtom }
    ],
    category := SyntaxAtom,
    syntaxDef := .ofList [.str "indent", .str "(", .ident 0 0, .str ", ", .ident 1 0, .str ")"],
  }

  let SyntaxDef := q`Init.SyntaxDef
  declareCat SyntaxDef
  declareOp Init {
    name := "mkSyntaxDef",
    argDecls := #[
      { ident := "args", kind := .cat <| mkSeq (.atom SyntaxAtom) }
    ],
    category := SyntaxDef,
    syntaxDef := .ofList [.ident 0 0],
  }

def initDeclState : DeclState := DeclM.run (init := {}) initializeInitDialect

def initDialect : Dialect :=
  if initDeclState.errors.size > 0 then
    panic! "Initial program state initialization failed"
  else
    match initDeclState.dialects["Init"]? with
    | some d => d
    | none => panic! "Initialial dialect failed"

namespace Elab.DialectLoader

def addDialect! (ctx : DialectLoader) (d : Dialect) : DialectLoader :=
  assert! d.name ∉ ctx.dialects
  {
    dialects := ctx.dialects.insert d
    dialectParsers := addDialectToParser! initDeclState.fixedParsers ctx.dialectParsers d
    syntaxElabMap := addDialectSyntaxElabs ctx.syntaxElabMap d
  }


end Elab.DialectLoader

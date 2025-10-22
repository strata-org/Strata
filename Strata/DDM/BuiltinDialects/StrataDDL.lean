/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.BuiltinDialects.Init

namespace Strata

open Elab

def StrataDDL : Dialect := BuiltinM.create! "StrataDDL" #[initDialect] do
  let Ident : ArgDeclKind := .cat <| .atom q`Init.Ident
  let BindingType := q`Init.BindingType
  let Command := q`Init.Command
  let Metadata := q`Init.Metadata
  let SyntaxDef := q`Init.SyntaxDef
  let TypeExpr := q`Init.TypeExpr

  -- Extend dialect with operation for constructing functions
  -- from bindings name and type.
  declareOp {
    name := "TypeFn",
    argDecls := .ofArray #[
      { ident := "bindings", kind := Ident },
      { ident := "val", kind := .cat <| .atom TypeExpr }
    ]
    category := TypeExpr,
    syntaxDef := .ofList [.str "fnOf(", .ident 0 0, .str ", ", .ident 1 0, .str ")"]
  }

  let Binding := q`StrataDDL.Binding
  declareCat Binding
  declareOp {
      name := "mkBinding",
      argDecls := .ofArray #[
        { ident := "name", kind := Ident, },
        { ident := "type", kind := .cat <| .atom BindingType, },
        { ident := "metadata", kind := .cat <| .mkOpt (.atom Metadata), }
      ],
      category := Binding,
      syntaxDef := .ofList [.ident 2 0, .ident 0 0, .str ":", .ident 1 0],
    }

  let Bindings := q`StrataDDL.Bindings
  declareCat Bindings
  declareOp {
      name := "mkBindings",
      argDecls := .ofArray #[
        { ident := "bs", kind := .cat <| .mkCommaSepBy <| .atom Binding }
      ],
      category := Bindings,
      syntaxDef := .ofList [.str "(", .ident 0 0, .str ")" ],
    }

  declareOp {
    name := "importCommand",
    argDecls := .ofArray #[
      { ident := "name", kind := Ident }
    ],
    category := Command,
    syntaxDef := .ofList [.str "import", .ident 0 0, .str ";"]
  }
  declareOp {
    name := "categoryCommand",
    argDecls := .ofArray #[
      { ident := "name", kind := Ident }
    ],
    category := Command,
    syntaxDef := .ofList [.str "category", .ident 0 0, .str ";"]
  }
  declareOp {
    name := "opCommand",
    argDecls := .ofArray #[
      { ident := "name",
        kind := Ident
      },
      { ident := "args",
        kind := .cat (.mkOpt (.atom Bindings))
      },
      { ident := "cat",
        kind := .cat (.atom BindingType),
        metadata := md{ .scope 0 }
      },
      { ident := "opMetadata",
        kind := .cat (.mkOpt (.atom Metadata)),
        metadata := md{ .scope 1 }
      },
      { ident := "synMetadata",
        kind := .cat (.mkOpt (.atom Metadata)),
        metadata := md{ .scope 2 }
      },
      { ident := "opSyntax",
        kind := .cat (.atom SyntaxDef),
        metadata := md{ .scope 3 }
      }
    ],
    category := Command,
    syntaxDef:= .ofList [.ident 3 0, .str "op", .ident 0 0, .ident 1 0, .str ":", .ident 2 0, .str "=>", .ident 4 0, .ident 5 0, .str ";"]
  }
  declareOp {
    name := "typeCommand",
    argDecls := .ofArray #[
      { ident := "name", kind := Ident },
      { ident := "args", kind := .cat (.mkOpt (.atom Bindings)) }
    ],
    category := Command,
    syntaxDef := .ofList [.str "type", .ident 0 0, .ident 1 0, .str ";"]
  }
  declareOp {
    name := "fnCommand",
    argDecls := .ofArray #[
      { ident := "name",
        kind := Ident
      },
      { ident := "args",
        kind := .cat (.mkOpt (.atom Bindings))
      },
      { ident := "returnType",
        kind := .cat (.atom BindingType),
        metadata := md{ .scope 0 }
      },
      { ident := "opMetadata",
        kind := .cat (.mkOpt (.atom Metadata)),
        metadata := md{ .scope 1 }
      },
      { ident := "synMetadata",
        kind := .cat (.mkOpt (.atom Metadata))
        metadata := md{ .scope 2 },
      },
      { ident := "opSyntax",
        kind := .cat (.atom SyntaxDef),
        metadata := md{ .scope 3 },
      }
    ],
    category := Command,
    syntaxDef := .ofList [.ident 3 0, .str "fn", .ident 0 0, .ident 1 0, .str ":", .ident 2 0, .str "=>", .ident 4 0, .ident 5 0, .str ";"]
  }
  declareOp {
    name := "mdCommand",
    argDecls := .ofArray #[
      { ident := "name", kind := Ident },
      { ident := "args", kind := .cat (.mkOpt (.atom Bindings)) }
    ],
    category := Command,
    syntaxDef := .ofList [.str "metadata", .ident 0 0, .ident 1 0, .str ";"]
  }
  declareMetadata { name := "prec", args := #[.mk "p" .num] }
  declareMetadata { name := "leftassoc", args := #[] }
  declareMetadata { name := "rightassoc", args := #[] }

  declareMetadata { name := "scope", args := #[.mk "scope" .ident] }
  declareMetadata { name := "declareType", args := #[.mk "name" .ident, .mk "args" (.opt .ident)] }
  declareMetadata { name := "aliasType",   args := #[.mk "name" .ident, .mk "args" (.opt .ident), .mk "def" .ident] }
  declareMetadata { name := "declare",     args := #[.mk "name" .ident, .mk "type" .ident] }
  declareMetadata { name := "declareFn",   args := #[.mk "name" .ident, .mk "args" .ident, .mk "type" .ident] }

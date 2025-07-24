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

import Strata.DDM.BuiltinDialects.Init

namespace Strata

open Elab

def StrataDD : String := "StrataDD"

def initializeStrataDD : DeclM Unit := do
  let Ident : DeclBindingKind := .cat <| .atom q`Init.Ident
  let BindingType := q`Init.BindingType
  let Command := q`Init.Command
  let Metadata := q`Init.Metadata
  let SyntaxDef := q`Init.SyntaxDef
  let TypeExpr := q`Init.TypeExpr

  let mkOpt (c:SyntaxCat) : SyntaxCat := .app (.atom q`Init.Option) c
  let mkCommaSepBy (c:SyntaxCat) : SyntaxCat := .app (.atom q`Init.CommaSepBy) c

  declareEmptyDialect StrataDD

  -- Extend dialect with operation for constructing functions
  -- from bindings name and type.
  declareOp StrataDD {
    name := "TypeFn",
    argDecls := #[
      { ident := "bindings", kind := Ident },
      { ident := "val", kind := .cat <| .atom TypeExpr }
    ]
    category := TypeExpr,
    syntaxDef := .ofList [.str "fnOf(", .ident 0 0, .str ", ", .ident 1 0, .str ")"]
  }

  let Binding := q`StrataDD.Binding
  declareCat Binding
  declareOp StrataDD {
      name := "mkBinding",
      argDecls := #[
        { ident := "name", kind := Ident, },
        { ident := "type", kind := .cat <| SyntaxCat.atom BindingType, },
        { ident := "metadata", kind := .cat <| mkOpt (.atom Metadata), }
      ],
      category := Binding,
      syntaxDef := .ofList [.ident 2 0, .ident 0 0, .str ":", .ident 1 0],
    }

  let Bindings := q`StrataDD.Bindings
  declareCat Bindings
  declareOp StrataDD {
      name := "mkBindings",
      argDecls := #[
        { ident := "bs", kind := .cat <| mkCommaSepBy <| .atom Binding }
      ],
      category := Bindings,
      syntaxDef := .ofList [.str "(", .ident 0 0, .str ")" ],
    }

  declareOp StrataDD {
     name := "dialectName",
     argDecls := #[
        { ident := "name", kind := Ident }
     ],
     category := q`Init.Command,
     syntaxDef := .ofList [.str "dialect", .ident 0 0, .str ";"],
  }
  declareOp StrataDD {
    name := "categoryCommand",
    argDecls := #[
      { ident := "name", kind := Ident }
    ],
    category := Command,
    syntaxDef := .ofList [.str "category", .ident 0 0, .str ";"]
  }
  declareOp StrataDD {
    name := "opCommand",
    argDecls := #[
      { ident := "name",
        kind := Ident
      },
      { ident := "args",
        kind := .cat (mkOpt (.atom Bindings))
      },
      { ident := "cat",
        kind := .cat (.atom BindingType),
        metadata := md{ .scope 0 }
      },
      { ident := "opMetadata",
        kind := .cat (mkOpt (.atom Metadata)),
        metadata := md{ .scope 1 }
      },
      { ident := "synMetadata",
        kind := .cat (mkOpt (.atom Metadata)),
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
  declareOp StrataDD {
    name := "typeCommand",
    argDecls := #[
      { ident := "name", kind := Ident },
      { ident := "args", kind := .cat (mkOpt (.atom Bindings)) }
    ],
    category := Command,
    syntaxDef := .ofList [.str "type", .ident 0 0, .ident 1 0, .str ";"]
  }
  declareOp StrataDD {
    name := "fnCommand",
    argDecls := #[
      { ident := "name",
        kind := Ident
      },
      { ident := "args",
        kind := .cat (mkOpt (.atom Bindings))
      },
      { ident := "returnType",
        kind := .cat (.atom BindingType),
        metadata := md{ .scope 0 }
      },
      { ident := "opMetadata",
        kind := .cat (mkOpt (.atom Metadata)),
        metadata := md{ .scope 1 }
      },
      { ident := "synMetadata",
        kind := .cat (mkOpt (.atom Metadata))
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
  declareOp StrataDD {
    name := "mdCommand",
    argDecls := #[
      { ident := "name", kind := Ident },
      { ident := "args", kind := .cat (mkOpt (.atom Bindings)) }
    ],
    category := Command,
    syntaxDef := .ofList [.str "metadata", .ident 0 0, .ident 1 0, .str ";"]
  }
  declareMetadata StrataDD { name := "prec", args := #[.mk "p" .num] }
  declareMetadata StrataDD { name := "leftassoc", args := #[] }
  declareMetadata StrataDD { name := "rightassoc", args := #[] }

  declareMetadata StrataDD { name := "scope", args := #[.mk "scope" .ident] }
  declareMetadata StrataDD { name := "declareType", args := #[.mk "name" .ident, .mk "args" (.opt .ident)] }
  declareMetadata StrataDD { name := "aliasType",   args := #[.mk "name" .ident, .mk "args" (.opt .ident), .mk "def" .ident] }
  declareMetadata StrataDD { name := "declare",     args := #[.mk "name" .ident, .mk "type" .ident] }
  declareMetadata StrataDD { name := "declareFn",   args := #[.mk "name" .ident, .mk "args" .ident, .mk "type" .ident] }
  declareMetadata StrataDD { name := "declareMD",   args := #[.mk "name" .ident, .mk "type" .ident, .mk "md" .ident] }

def dialectProgramState : DeclState := DeclM.run (init := initDeclState) do
  initializeStrataDD

def strataDialect : Dialect :=
  if dialectProgramState.errors.size > 0 then
    panic! s!"{StrataDD} dialect initialization failed"
  else
    match dialectProgramState.dialects[StrataDD]? with
    | some d => d
    | none => panic! s!"{StrataDD} dialect not found"

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.DDM.AST
import Strata.DDM.BuiltinDialects.BuiltinM
import Strata.DDM.BuiltinDialects.Init

open Strata.Elab

public section
namespace Strata


def headerDialect : Dialect := Elab.BuiltinM.create! "StrataHeader" #[initDialect] do
  let Ident : ArgDeclKind := .cat <| .atom .none q`Init.Ident
  let Command := q`Init.Command

  declareOp {
     name := "dialectCommand",
     argDecls := .ofArray #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "dialect", .ident 0 0, .str ";"],
  }
  declareOp {
     name := "programCommand",
     argDecls := .ofArray #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "program", .ident 0 0, .str ";"],
  }
end Strata
end

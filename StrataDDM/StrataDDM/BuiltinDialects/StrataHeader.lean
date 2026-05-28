/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import StrataDDM.AST
import StrataDDM.BuiltinDialects.BuiltinM
import StrataDDM.BuiltinDialects.Init

open StrataDDM.Elab

public section
namespace StrataDDM


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
end StrataDDM
end

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

def StrataHeader : String := "StrataHeader"

def headerDialect : Dialect := BuiltinM.create! StrataHeader #[initDialect] do
  let Ident : DeclBindingKind := .cat <| .atom q`Init.Ident
  let Command := q`Init.Command

  declareOp {
     name := "dialectCommand",
     argDecls := #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "dialect", .ident 0 0, .str ";"],
  }
  declareOp {
     name := "programCommand",
     argDecls := #[
        { ident := "name", kind := Ident }
     ],
     category := Command,
     syntaxDef := .ofList [.str "program", .ident 0 0, .str ";"],
  }

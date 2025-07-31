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




import Strata.Languages.Boogie.Statement

namespace Boogie

open Std (ToFormat Format format)
open Lambda

/-!
## Axioms

Axioms are propositions assumed to be true throughout a Strata.Boogie program.
They are passed on as assumptions to the SMT solver during VC generation. It's
the responsibility of the user to ensure that they are consistent.
-/

structure Axiom where
  name : BoogieLabel
  e : LExpr BoogieIdent

instance : ToFormat Axiom where
  format a := f!"axiom {a.name}: {a.e};"

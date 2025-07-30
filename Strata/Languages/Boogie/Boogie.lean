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



import Strata.Languages.Boogie.ProgramEval
import Strata.Languages.Boogie.ProgramType

---------------------------------------------------------------------

namespace Boogie

/-!
## Differences between Boogie and Strata.Boogie

1. Local variables can shadow globals in Boogie, but the typechecker disallows
   that in Strata.Boogie.

2. Unlike Boogie, Strata.Boogie is sensitive to global declaration order. E.g.,
   a global variable must be declared before it can be used in a procedure.

3. Strata.Boogie does not (yet) support polymorphism.

4. Strata.Boogie does not (yet) support arbitrary gotos. All gotos must
   currently be to labels later in the program.

5. Strata.Boogie does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.

6. Strata.Boogie does not support algebraic data types or regular expression
   types.
-/

def typeCheckAndPartialEval (program : Program) :
  Except Std.Format (List (Program × Env)) := do
  let factory := Boogie.Factory
  let known_types := Boogie.KnownTypes
  let T := { Lambda.TEnv.default with functions := factory, knownTypes := known_types }
  let (program, _T) ← Program.typeCheck T program
  -- dbg_trace f!"[Strata.Boogie] Annotated program:\n{program}"
  dbg_trace f!"[Strata.Boogie] Type checking succeeded.\n"
  let σ ← (Lambda.LState.init).addFactory factory
  let E := { Env.init with exprEnv := σ,
                           program := program }
  let pEs := Program.eval E
  dbg_trace f!"{Std.Format.line}VCs:"
  for (_p, E) in pEs do
    -- dbg_trace f!"Program: {p}"
    dbg_trace f!"{ProofObligations.eraseTypes E.deferred}"
  return pEs

instance : ToString (Program) where
  toString p := toString (Std.format p)

end Boogie

---------------------------------------------------------------------

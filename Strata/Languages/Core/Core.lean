/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Options
import Strata.Languages.Core.ProgramEval
import Strata.Languages.Core.ProgramType

---------------------------------------------------------------------

namespace Core
open Strata

/-!
## Differences between Boogie and Strata.Core

1. Local variables can shadow globals in Boogie, but the typechecker disallows
   that in Strata.Core.

2. Unlike Boogie, Strata.Core is sensitive to global declaration order. E.g.,
   a global variable must be declared before it can be used in a procedure.

3. Strata.Core does not (yet) support polymorphism.

4. Strata.Core does not (yet) support arbitrary gotos. All gotos must
   currently be to labels later in the program.

5. Strata.Core does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.
-/

def typeCheck (options : Options) (program : Program)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel Program := do
  let T := Lambda.TEnv.default
  let factory ← Core.Factory.addFactory moreFns
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Core.KnownTypes }
  let (program, _T) ← Program.typeCheck C T program
  -- dbg_trace f!"[Strata.Core] Type variables:\n{T.state.substInfo.subst.length}"
  -- dbg_trace f!"[Strata.Core] Annotated program:\n{program}"
  if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
  return program

def typeCheckAndPartialEval (options : Options) (program : Program)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except DiagnosticModel (List (Program × Env)) := do
  let program ← typeCheck options program moreFns
  -- Extract datatypes from program declarations and add to environment
  let datatypes := program.decls.filterMap fun decl =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let σ ← (Lambda.LState.init).addFactory Core.Factory
  let σ ← σ.addFactory moreFns
  let E := { Env.init with exprEnv := σ,
                           program := program }
  let E ← E.addDatatypes datatypes
  let pEs := Program.eval E
  if options.verbose >= .normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for (_p, E) in pEs do
      dbg_trace f!"{ProofObligations.eraseTypes E.deferred}"
  return pEs

instance : ToString (Program) where
  toString p := toString (Std.format p)

end Core

---------------------------------------------------------------------

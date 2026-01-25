/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Options
import Strata.Languages.Core.ProgramEval
import Strata.Languages.Core.ProgramType

---------------------------------------------------------------------

namespace Core

/-!
## Differences between Boogie and Strata.Core

1. Local variables can shadow globals in Boogie, but the typechecker disallows
   that in Strata.Core.

2. Unlike Boogie, Strata.Core is sensitive to global declaration order. E.g.,
   a global variable must be declared before it can be used in a procedure.

3. Strata.Core does not support higher-rank polymorphism (specifically,
   impredicative maps).

4. Strata.Core does not (yet) support arbitrary gotos. All gotos must
   currently be to labels later in the program.

5. Strata.Core does not support `where` clauses and `unique` constants,
   requiring a tool like `BoogieToStrata` to desugar them.
-/

/--
We save the analysis artifacts from a prelude program in `PreludeArtifacts` so
that we can reason about a program with this prelude already in the context.

We assume that the program whose artifacts are stashed here is well-formed
(i.e., type checks, with all passing proof obligations). In the future, we may
have a certificate-checking mechanism to enforce this.
-/
structure PreludeArtifacts where
  /-- Type annotated program.
      TODO: Add proof that the program passes typecheck.
  -/
  program   : Core.Program
  /-- Type context. -/
  tyContext : Core.Expression.TyContext
  /-- Type environment. -/
  tyEnv     : Core.Expression.TyEnv
  deriving Inhabited

def typeCheck (options : Options) (program : Program)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format (Program × Expression.TyContext × Expression.TyEnv) := do
  let T := Lambda.TEnv.default
  let factory ← Core.Factory.addFactory moreFns
  let C := { Lambda.LContext.default with
                functions := factory,
                knownTypes := Core.KnownTypes }
  let (program, C, T) ← Program.typeCheck C T program
  if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
  return (program, C, T)

def typeCheckWithPrelude (options : Options) (program : Core.Program)
    (prelude : PreludeArtifacts)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format Core.Program := do
  let newFactory ← prelude.tyContext.functions.addFactory moreFns
  let newC := { prelude.tyContext with functions := newFactory }
  let (programDecls, _T, _C) ← Core.Program.typeCheck.go
                                  { decls := prelude.program.decls ++ program.decls }
                                  newC prelude.tyEnv program.decls []
  if options.verbose >= .normal then dbg_trace f!"[Strata.Core] Type checking succeeded.\n"
  -- programDecls do not include prelude's declarations.
  return { decls := programDecls }

def partialEval (options : Options) (program : Program)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format (List (Program × Env)) := do
  let σ ← (Lambda.LState.init).addFactory Core.Factory
  let σ ← σ.addFactory moreFns
  let E := { Env.init with exprEnv := σ,
                           program := program }
  -- Extract generated functions for datatypes (containing eliminators,
  -- constructors, testers, and destructors) from program declarations and add
  -- to the evaluation environment.
  let datatypes := program.decls.filterMap fun (decl : Decl) =>
    match decl with
    | .type (.data d) _ => some d
    | _ => none
  let E ← E.addDatatypes datatypes
  let pEs := Program.eval E
  if options.verbose >= VerboseMode.normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for (_p, E) in pEs do
      dbg_trace f!"{ProofObligations.eraseTypes E.deferred}"
  return pEs

-- Seed the evaluation environment with the prelude's functions,
-- type factory, and axioms.
def seedPreludeEvalEnv (program : Program) (prelude : PreludeArtifacts)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format Env := do
  let σ ← (Lambda.LState.init).addFactory prelude.tyContext.functions
  let σ ← σ.addFactory moreFns
  let E := { Core.Env.init with exprEnv := σ,
                                datatypes := prelude.tyContext.datatypes,
                                program := { decls := prelude.program.decls ++ program.decls }}
  let preludeAxioms := prelude.program.decls.filterMap fun decl =>
   match decl with
   | .ax a _ => some a
   | _ => none
  let preludePathConditions := preludeAxioms.map (fun a => (a.name, a.e))
  let E := { E with pathConditions := E.pathConditions.push preludePathConditions }
  return E

def partialEvalWithPrelude (options : Options) (program : Program)
    (prelude : PreludeArtifacts)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format (List (Program × Env)) := do
  let E ← seedPreludeEvalEnv program prelude moreFns
  -- For the program: extract generated functions for datatypes from program
  -- declarations and add to the evaluation environment.
  let datatypes := program.decls.filterMap fun decl =>
   match decl with
   | .type (.data d) _ => some d
   | _ => none
  let E ← E.addDatatypes datatypes
  let declsEnv := Core.Program.eval.go program.decls { env := E }
  let pEs := (declsEnv.map (fun (decls, E) => ({ decls := prelude.program.decls ++ decls },
                                  E)))
  if options.verbose >= VerboseMode.normal then do
    dbg_trace f!"{Std.Format.line}VCs:"
    for (_p, E) in pEs do
      dbg_trace f!"{ProofObligations.eraseTypes E.deferred}"
  return pEs

def typeCheckAndPartialEval (options : Options) (program : Program)
    (prelude : Option Core.PreludeArtifacts := .none)
    (moreFns : @Lambda.Factory CoreLParams := Lambda.Factory.default) :
    Except Std.Format (List (Program × Env)) := do
  match prelude with
  | .none =>
    let (program, _, _) ← typeCheck options program moreFns
    partialEval options program
  | .some prelude =>
    let program ← typeCheckWithPrelude options program prelude moreFns
    partialEvalWithPrelude options program prelude moreFns

end Core

---------------------------------------------------------------------

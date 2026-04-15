/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Solver

/-!
# Abstract Solver Interface

Defines `AbstractSolver τ m`, a generic solver interface parameterized by an
opaque term type `τ` and a monad `m`. All operations that can fail return
`Except String`. The monad `m` captures any state or effects the backend needs.

For the batch SMT-LIB pipeline, `m` is `SolverM` (file-writing, no interaction).
For the incremental backend, `m` is `StateT IncrementalSolverState IO`.
For a future FFI backend, `m` could be `StateT NativeSolverState IO`.

## Design

- `declareNew` allows shadowing: declaring the same name twice creates two
  distinct variables. The backend handles disambiguation internally.
- Models return keys as `(String × Nat)` where `Nat` is the shadow depth
  (0 = most recently declared).
- Quantifier bound variables are scoped via a callback pattern.
- Terms are session-independent and can be stored and replayed across sessions.
-/

namespace Strata.SMT

public section

/-- Abstract solver interface parameterized by term type `τ` and monad `m`.

All term constructors are fallible. Solvers might not accept certain constructs
(e.g., wrong sorts, unsupported combinations) and we need to surface the issue
precisely via `Except String`. -/
structure AbstractSolver (τ : Type) (m : Type → Type) where
  -- Literal constructors
  mkBool : Bool → m τ
  mkInt : Int → m τ

  -- Boolean operations
  mkAnd : List τ → m (Except String τ)
  mkOr : List τ → m (Except String τ)
  mkNot : τ → m (Except String τ)
  mkImplies : τ → τ → m (Except String τ)

  -- Arithmetic operations
  mkAdd : List τ → m (Except String τ)
  mkSub : List τ → m (Except String τ)
  mkMul : List τ → m (Except String τ)
  mkDiv : τ → τ → m (Except String τ)
  mkMod : τ → τ → m (Except String τ)
  mkNeg : τ → m (Except String τ)

  -- Comparison operations
  mkEq : List τ → m (Except String τ)
  mkLt : List τ → m (Except String τ)
  mkLe : List τ → m (Except String τ)
  mkGt : List τ → m (Except String τ)
  mkGe : List τ → m (Except String τ)

  -- Conditional
  mkIte : τ → τ → τ → m (Except String τ)

  /-- Declare a new variable. Shadowing is allowed: declaring the same name
      twice creates two distinct variables. The backend handles disambiguation
      internally. -/
  declareNew : String → TermType → m τ

  /-- Declare an uninterpreted function. -/
  declareFun : String → List TermType → TermType → m (Except String τ)

  /-- Define an interpreted function with a body term. -/
  defineFun : String → List (String × TermType) → TermType → τ → m (Except String Unit)

  /-- Declare a new sort with the given arity. -/
  declareSort : String → Nat → m (Except String Unit)

  /-- Declare an algebraic datatype.
      Parameters: name, type parameters, constructors (name × fields). -/
  declareDatatype : String → List String → List (String × List (String × TermType)) → m (Except String Unit)

  /-- Construct a universally quantified term.
      Takes name-sort pairs for bound variables and a callback that receives
      the bound variable terms and returns the body and trigger groups.
      Bound variables cannot escape the quantifier scope. -/
  mkForall : List (String × TermType) → (List τ → Except String (τ × List (List τ))) → m (Except String τ)

  /-- Construct an existentially quantified term. Same callback pattern as `mkForall`. -/
  mkExists : List (String × TermType) → (List τ → Except String (τ × List (List τ))) → m (Except String τ)

  -- Session operations

  /-- Assert a term (must be Bool-typed). -/
  assert : τ → m (Except String Unit)

  /-- Check satisfiability of the current assertions. -/
  checkSat : m (Except String Decision)

  /-- Check satisfiability under additional assumptions. -/
  checkSatAssuming : List τ → m (Except String Decision)

  /-- Retrieve the model after a `sat` result.
      Keys are `(name, shadow_depth)` where 0 = most recently declared. -/
  getModel : m (Except String (List ((String × Nat) × τ)))

  /-- Get values of specific terms in the current model. -/
  getValue : List τ → m (Except String (List (τ × τ)))

  /-- Reset the solver session to its initial state. -/
  reset : m Unit

  /-- Close the solver session and release resources. -/
  close : m Unit

end

end Strata.SMT

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.Solver

/-!
# Abstract Solver Interface

Defines `AbstractSolver τ σ m`, a generic solver interface parameterized by an
opaque term type `τ`, an opaque sort type `σ`, and a monad `m`. All operations
that can fail return `Except String`. The monad `m` captures any state or
effects the backend needs.

For the incremental SMT-LIB backend, `τ = SMT.Term`, `σ = SMT.TermType`,
`m = StateT IncrementalSolverState IO`.

## Design

- `declareNew` allows shadowing: declaring the same name twice creates two
  distinct variables. The backend handles disambiguation internally.
- Models return keys as `(String × Nat)` where `Nat` is the shadow depth
  (0 = most recently declared).
- Quantifier bound variables are scoped via a callback pattern.
- Terms are session-independent and can be stored and replayed across sessions.
- Sorts are first-class: backends can create and pass their own sort
  representations via `intSort`, `boolSort`, `bitvecSort`, `arraySort`, etc.
-/

namespace Strata.SMT

public section

/-- Abstract solver interface parameterized by term type `τ`, sort type `σ`,
and monad `m`.

All term constructors are fallible. Solvers might not accept certain constructs
(e.g., wrong sorts, unsupported combinations) and we need to surface the issue
precisely via `Except String`. -/
structure AbstractSolver (τ : Type) (σ : Type) (m : Type → Type) where
  -- Sort constructors
  boolSort : m σ
  intSort : m σ
  realSort : m σ
  stringSort : m σ
  bitvecSort : Nat → m σ
  arraySort : σ → σ → m (Except String σ)

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
  mkAbs : τ → m (Except String τ)

  -- Comparison operations
  mkEq : List τ → m (Except String τ)
  mkLt : List τ → m (Except String τ)
  mkLe : List τ → m (Except String τ)
  mkGt : List τ → m (Except String τ)
  mkGe : List τ → m (Except String τ)

  -- Conditional
  mkIte : τ → τ → τ → m (Except String τ)

  -- Array operations
  mkSelect : τ → τ → m (Except String τ)
  mkStore : τ → τ → τ → m (Except String τ)

  -- Function application (for uninterpreted functions)
  mkApp : τ → List τ → m (Except String τ)

  /-- Declare a new variable. Shadowing is allowed: declaring the same name
      twice creates two distinct variables. The backend handles disambiguation
      internally. -/
  declareNew : String → σ → m τ

  /-- Declare an uninterpreted function. -/
  declareFun : String → List σ → σ → m (Except String τ)

  /-- Define an interpreted function with a body term. -/
  defineFun : String → List (String × σ) → σ → τ → m (Except String Unit)

  /-- Declare a new sort with the given arity. -/
  declareSort : String → Nat → m (Except String Unit)

  /-- Declare an algebraic datatype.
      Parameters: name, type parameters, constructors (name × fields). -/
  declareDatatype : String → List String → List (String × List (String × σ)) → m (Except String Unit)

  /-- Construct a universally quantified term.
      Takes name-sort pairs for bound variables and a callback that receives
      the bound variable terms and returns the body and trigger groups.
      Bound variables cannot escape the quantifier scope. -/
  mkForall : List (String × σ) → (List τ → Except String (τ × List (List τ))) → m (Except String τ)

  /-- Construct an existentially quantified term. Same callback pattern as `mkForall`. -/
  mkExists : List (String × σ) → (List τ → Except String (τ × List (List τ))) → m (Except String τ)

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

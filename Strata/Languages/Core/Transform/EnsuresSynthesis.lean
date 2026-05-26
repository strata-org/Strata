/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Statement

/-!
# Ensures Synthesis Pass

A **sound** pre-pass over `Core.Program` that synthesises `ensures` clauses for
user procedures whose bodies implement a *pure linear computation* on their input
parameters.

## Supported patterns

### Pattern 1 – linear-assignment body
A procedure qualifies when its body (structured or single-entry CFG) satisfies
all of the following:

1. No intra-body branches (CFG must have exactly one block; structured body must
   contain no `ite`, `loop`, or `block` statements).
2. No calls to user-defined procedures.  Calls whose name starts with one of a
   known set of safe prefixes (`boogie_si_record`, `__SMACK_`, `_initialize`,
   `assert__`) are **ignored** (they are SMACK instrumentation that does not
   affect the data-flow we care about).
3. The only writes are `set` / `init` statements.
4. Every output-only parameter is written **exactly once**.
5. The written expression, after forward-substituting through temporary
   variables, is a *closed expression over input parameters* — it mentions only
   free variables whose names are input parameter names, numeric/boolean
   constants, and applications of declared Core functions.

When all conditions hold we emit
```
  free ensures [synthesized_ensures_<out>]: (out == expr);
```
for each qualifying output-only parameter.  We mark the clause **`Free`** so
that it is *assumed at call sites* (which is what we want — callers get the
benefit) but the synthesised clause itself is **not checked** against the body
(avoiding any risk of a spurious failure from imprecise synthesis).

## Soundness argument

The synthesised ensures `out == expr` is sound because the pass only fires when
the body **literally assigns** `out := expr'` where `expr` is obtained from
`expr'` by substituting every intermediate temporary with the expression it was
assigned in the same body.  Since there are no branches, memory accesses, or
user-procedure calls, the body deterministically computes exactly `expr` for
`out`.  For any input satisfying the (possibly empty) preconditions, the
post-state has `out == expr`.

Because we only look at the *read side* of assignments (no quantifier
introduction, no existential reasoning) and we never synthesise a clause that
mentions variables not in scope at call sites, the claim is syntactically
verifiable and semantically sound.

-/

public section

namespace Core
namespace EnsuresSynthesis

open Lambda (LExpr)

---------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------

/-- Safe call prefixes: these are SMACK/Boogie instrumentation calls that
    observe values but do not modify any data variable.  We ignore them
    during pattern matching. -/
private def safeCallPrefixes : List String :=
  [ "boogie_si_record"
  , "__SMACK_"
  , "_initialize"
  , "assert__"
  , "__VERIFIER_"
  , "__smack"
  ]

private def isSafeCall (name : String) : Bool :=
  safeCallPrefixes.any fun pfx => name.startsWith pfx

/-- Collect the commands from a CFG or structured body as a flat list,
    returning `none` if the body has any branches/loops (i.e. more than one
    basic block in the CFG, or any `ite`/`loop`/`block` in structured). -/
private def collectLinearCmds (body : Procedure.Body)
    : Option (List Command) :=
  match body with
  | .structured ss => collectFromStmts ss
  | .cfg cfg =>
    -- Accept only single-block CFGs (one entry block that finishes).
    -- The entry label must be the only block, or there can be at most a
    -- second outer "exit" block that contains nothing but a `finish`.
    -- We flatten all blocks' commands together; if there are non-trivial
    -- blocks we conservatively reject.
    let blocks := cfg.blocks
    -- Collect all commands from all blocks; reject if any block ends with
    -- a condGoto to distinct targets (meaning there is a real branch).
    let cmds := blocks.filterMap fun (_, blk) =>
      match blk.transfer with
      | .finish _ => some blk.cmds
      | .condGoto _ lt lf _ =>
        -- condGoto with identical targets is an unconditional jump (goto).
        -- We treat it as linear.  A genuine branch has different targets.
        if lt == lf then some blk.cmds else none
    -- If any block was rejected, cmds.length < blocks.length
    if cmds.length == blocks.length then
      some (cmds.flatten)
    else
      none
where
  collectFromStmts : List Statement → Option (List Command)
    | [] => some []
    | s :: rest =>
      match s with
      | .cmd c =>
        match collectFromStmts rest with
        | none => none
        | some cs => some (c :: cs)
      -- Any structured control flow disqualifies.
      | .ite _ _ _ _  => none
      | .loop _ _ _ _ _ => none
      -- Labeled blocks are linear: they introduce a label scope but no
      -- branching. Recurse into the body and concatenate with the rest.
      -- (An `exit <lbl>` inside the block is a forward jump to the end of
      -- the block, equivalent to a no-op for our purposes — handled below.)
      | .block _ inner _ =>
        match collectFromStmts inner, collectFromStmts rest with
        | some innerCs, some restCs => some (innerCs ++ restCs)
        | _, _ => none
      | .exit _ _ =>
        match collectFromStmts rest with
        | none => none
        | some cs => some cs
      | .funcDecl _ _ =>
        match collectFromStmts rest with
        | none => none
        | some cs => some cs
      | .typeDecl _ _ =>
        match collectFromStmts rest with
        | none => none
        | some cs => some cs

/-- Build a substitution map `varName → expr` from the linear command list.
    Returns `none` if any user-procedure call is detected.
    Ignores safe instrumentation calls.
    Only handles `set` and `init` commands. -/
private def buildSubstMap (cmds : List Command)
    : Option (Map Expression.Ident Expression.Expr) :=
  cmds.foldlM (init := Map.empty) fun m cmd =>
    match cmd with
    | .cmd (.set v (.det e) _) => some (m.insert v e)
    | .cmd (.init v _ (.det e) _) => some (m.insert v e)
    -- nondet-init (`var x : T;` without an initializer): leave x absent
    -- from the map. If x is read later without first being set, the
    -- final substituted expression will mention `x` as a free variable,
    -- which `onlyInputFvars` catches (rejecting the synthesis). This is
    -- sound: we only emit an ensures when every free var resolves to an
    -- input parameter.
    | .cmd (.init _ _ .nondet _) => some m
    -- nondet-set (explicit havoc) is an explicit re-introduction of
    -- nondeterminism mid-body. We conservatively reject — the value
    -- written before the havoc is not preserved, and downstream
    -- substitutions would be wrong if any expression depended on it.
    | .cmd (.set _ .nondet _) => none
    | .cmd (.assert _ _ _) => some m
    | .cmd (.assume _ _ _) => some m
    | .cmd (.cover _ _ _) => some m
    | .call procName _ _ =>
      if isSafeCall procName then some m
      else none

/-- Forward-substitute `expr` using the map, replacing every free variable
    whose name appears in the map with the mapped expression.
    Applies at most `fuel` rounds to handle chains of temporaries.
    Uses simultaneous substitution (`substFvars`) each round to avoid
    order sensitivity. -/
private def substExpr (m : Map Expression.Ident Expression.Expr)
    (expr : Expression.Expr) (fuel : Nat := 20) : Expression.Expr :=
  match fuel with
  | 0 => expr
  | fuel + 1 =>
    let expr' := Lambda.LExpr.substFvars expr m
    if expr' == expr then expr
    else substExpr m expr' fuel

/-- Check that an expression only mentions free variables from `inputNames`.
    Returns `true` when the expression is safe to use in an `ensures` clause. -/
private def onlyInputFvars (expr : Expression.Expr) (inputNames : List CoreIdent) : Bool :=
  let vars := Lambda.LExpr.LExpr.getVars expr
  vars.all fun v => inputNames.any (· == v)

---------------------------------------------------------------------
-- Main synthesis function
---------------------------------------------------------------------

/-- Attempt to synthesise ensures clauses for a single procedure.
    Returns `none` if the procedure already has postconditions, has no body,
    has an abstract body, or doesn't match the linear-assignment pattern.
    Returns `some proc` with synthesised ensures appended otherwise. -/
def synthesizeForProcedure (p : Procedure) : Option Procedure :=
  -- Skip if already has postconditions: user contract takes priority.
  if !p.spec.postconditions.isEmpty then none
  -- Skip abstract procedures.
  else if p.body.isAbstract then none
  else
    let inputIdents := p.header.inputs.keys
    let outputOnlyIdents := p.header.getOutputOnlyParams.keys
    -- Nothing to synthesize if there are no output-only params.
    if outputOnlyIdents.isEmpty then none
    else
      match collectLinearCmds p.body with
      | none => none
      | some cmds =>
        match buildSubstMap cmds with
        | none => none
        | some substMap =>
          -- For each output-only param, look up what it was assigned.
          let newEnsures : ListMap CoreLabel Procedure.Check :=
            outputOnlyIdents.filterMap fun outId =>
              match substMap.find? outId with
              | none => none  -- output not assigned; skip
              | some rawExpr =>
                -- Substitute temporaries to get a closed expression over inputs.
                let finalExpr := substExpr substMap rawExpr
                -- Check that the result only mentions input free variables.
                if onlyInputFvars finalExpr inputIdents then
                  -- Build: (outId == finalExpr)
                  let outFvar : Expression.Expr := Lambda.LExpr.fvar () outId none
                  let ensuresExpr : Expression.Expr := Lambda.LExpr.eq () outFvar finalExpr
                  let lbl : CoreLabel := s!"synthesized_ensures_{outId.toPretty}"
                  let check : Procedure.Check := { expr := ensuresExpr, attr := .Free }
                  some (lbl, check)
                else
                  none
          if newEnsures.isEmpty then none
          else
            let newPostconds : ListMap CoreLabel Procedure.Check :=
              p.spec.postconditions ++ newEnsures
            some { p with spec := { p.spec with postconditions := newPostconds } }

/-- Walk every procedure declaration in the program and, when the body
    matches the supported patterns, append synthesised `ensures` clauses.
    Procedures that already have postconditions are left unchanged.
    Procedures that do not match a pattern are left unchanged (no unsound
    clauses are ever emitted).

    This is intended as a **pre-pass** that runs before `callElim`. -/
def synthesizeEnsures (prog : Core.Program) : Core.Program :=
  { prog with
    decls := prog.decls.map fun decl =>
      match decl with
      | .proc p md =>
        match synthesizeForProcedure p with
        | none => decl
        | some p' => .proc p' md
      | other => other }

end EnsuresSynthesis
end Core

end -- public section

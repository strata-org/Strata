import Strata.Transform.Specification

open Imperative Specification Transform

/-! # The Language We're Working In

We work GENERICALLY over any expression system `P` satisfying these constraints:
- HasFvar P    : expressions can contain free variables
- HasBool P    : there exist expressions `tt` and `ff` (true/false)
- HasNot P     : there's a `not` operation on expressions
- HasIntOrder P: there's integer comparison (eq, lt, zero)
- HasVal P     : there's a notion of "value" (fully evaluated expression)

The STATEMENTS are `Stmt P (Cmd P)` — the Imperative dialect's statement type:
  .cmd c              -- atomic command (init, set, assert, assume, havoc, cover)
  .block l [s1,...] md -- labeled block
  .ite cond [t1,...] [e1,...] md -- if-then-else
  .loop guard meas inv [body...] md -- loop
  .exit l md          -- structured exit
  .funcDecl f md      -- local function declaration
  .typeDecl tc md     -- local type declaration

The SEMANTICS are given by `EvalCmd P` (command evaluation) and `StepStmt`
(small-step transitions). Multi-step is `StepStmtStar` (reflexive-transitive closure).

The CONFIGURATIONS are `Config P (Cmd P)`:
  .stmt s ρ           -- about to execute statement s in environment ρ
  .stmts [s1,...] ρ   -- about to execute statement list
  .terminal ρ         -- execution finished
  .exiting lbl ρ      -- exiting with label
  .block lbl inner    -- inside a block (wraps inner config)
  .seq inner [rest..] -- sequencing (inner executes, then rest)
-/

variable {P : PureExpr} [HasFvar P] [HasBool P] [HasNot P] [HasIntOrder P] [HasVal P]

/-! ## Abbreviations to make things readable -/

-- The language we're proving things about:
-- "Standard imperative language with expression system P"
abbrev MyLang (extendEval : ExtendEval P) : Lang P :=
  Lang.imperative P (Cmd P) (EvalCmd P) extendEval (isAtAssert P)

-- Generalized transform: wrap any COMMAND with definedVars = [] in a block.
-- This accepts all commands except .init (which creates new variables).
def wrapCmdInBlock (s : Stmt P (Cmd P)) : Option (Stmt P (Cmd P)) :=
  match s with
  | .cmd c =>
    if Cmd.definedVars c = [] then
      some (.block "wrapper" [.cmd c] .empty)
    else
      none
  | _ => none


theorem wrapCmdInBlock_overapproximates
    (extendEval : ExtendEval P) (newPrefix : String) :
    Overapproximates (MyLang extendEval) (MyLang extendEval) wrapCmdInBlock newPrefix := by
    sorry

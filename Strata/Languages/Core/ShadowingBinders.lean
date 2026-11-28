/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
import Strata.Languages.Core.NameSets
import Strata.Util.Name

/-! # Renaming the variables named like a function

A function formal, a procedure parameter or a local variable may have the name of a function
or constant. The expressions of a program tell the two apart: a function or constant is an
operator (`.op`), a variable a free variable (`.fvar`), so the variable shadows the function in
its scope, and a use of the function's name outside that scope is an operator that stays as it
is. Obligation extraction and the SMT encoding put variables and functions in one namespace,
so before them the back end renames such variables apart.

`Program.renameShadowingBinders` gives each such variable a fresh name `x@k` throughout its
declaration: in the signature, the contract, the body, and as `old x` for an in-out parameter.
It renames free variables and assigned variables only, never an operator. Each fresh name is
the least `k ≥ 1` for which `x@k` is no name of the program, of the declaration or of a
function in scope, so the renaming is intended to be injective and to keep the program's
meaning; that is not proved yet (see `separateVarNamesPipelinePhase`). Afterwards no procedure
variable and no function formal has the name of a function of the program
(`Program.varsNotFunctions`).

Key definitions: `Core.Program.renameShadowingBinders`, `Core.Program.varsNotFunctions`. -/

public section

namespace Core

open Lambda Imperative

namespace ShadowingBinders

/-- `id` renamed by the first pair of `ren` whose source is its name. -/
def renameIdent (ren : List (String × String)) (id : CoreIdent) : CoreIdent :=
  match ren.find? (·.1 == id.name) with
  | some (_, y) => ⟨y, id.metadata⟩
  | none => id

/-- `e` with its free variables renamed by `ren`. -/
def renameExpr (ren : List (String × String)) (e : Expression.Expr) : Expression.Expr :=
  Expression.mapFvarNames (renameIdent ren) e

/-- A command with its variables, read or written, renamed by `ren`. -/
def renameCmd (ren : List (String × String)) : Cmd Expression → Cmd Expression
  | .init x ty e md => .init (renameIdent ren x) ty (e.map (renameExpr ren)) md
  | .set x e md => .set (renameIdent ren x) (e.map (renameExpr ren)) md
  | .assert l e md => .assert l (renameExpr ren e) md
  | .assume l e md => .assume l (renameExpr ren e) md
  | .cover l e md => .cover l (renameExpr ren e) md

/-- A command or call with its variables renamed by `ren`. -/
def renameCommand (ren : List (String × String)) : Command → Command
  | .cmd c => .cmd (renameCmd ren c)
  | .call p tys args md => .call p tys (args.map fun
      | .inArg e => .inArg (renameExpr ren e)
      | .inoutArg x => .inoutArg (renameIdent ren x)
      | .outArg x => .outArg (renameIdent ren x)) md

/-- A signature with its parameters renamed by `ren`. -/
def renameSig (ren : List (String × String)) (sig : @LMonoTySignature Unit) :
    @LMonoTySignature Unit :=
  sig.map fun (x, ty) => (renameIdent ren x, ty)

/-- A procedure with its variables renamed by `ren` in its header, contract and body. The
    statement-level `Block.substFvar` and `Block.renameLhs` cover a structured body only and
    rename one variable per pass, so this walk covers structured and CFG bodies in one pass. -/
def renameProc (ren : List (String × String)) (p : Procedure) : Procedure :=
  let renameChecks (cs : ListMap CoreLabel Procedure.Check) :=
    cs.map fun (l, c) => (l, { c with expr := renameExpr ren c.expr })
  { header := { p.header with
      inputs := renameSig ren p.header.inputs,
      outputs := renameSig ren p.header.outputs },
    spec := { preconditions := renameChecks p.spec.preconditions,
              postconditions := renameChecks p.spec.postconditions },
    body := match p.body with
      | .structured ss o =>
        .structured (Block.mapExpr (renameExpr ren) (renameCommand ren) ss) o
      | .cfg c o => .cfg (DetCFG.mapCmdsGuards c (renameCommand ren) (renameExpr ren)) o
      | .abstract => .abstract }

/-- A function with its formals renamed by `ren` in its signature and expressions. -/
def renameFunc (ren : List (String × String)) (f : Function) : Function :=
  { f with
    inputs := f.inputs.map fun (x, ty) => (renameIdent ren x, ty),
    body := f.body.map (renameExpr ren),
    axioms := f.axioms.map (renameExpr ren),
    preconditions := f.preconditions.map fun p => { p with expr := renameExpr ren p.expr },
    measure := f.measure.map (renameExpr ren) }

/-- The names of the free variables of `e`. -/
def fvarNames (e : Expression.Expr) : List String :=
  (HasFvars.getFvars (P := Expression) e).map (·.name)

/-- The variables a command declares or assigns. -/
def commandLhs (c : Command) : List String :=
  (HasVarsImp.definedVars (P := Expression) c false ++
    HasVarsImp.modifiedVars (P := Expression) c).map (·.name)

/-- The variables a procedure declares: its parameters and its local variables. -/
def procBinders (p : Procedure) : List String :=
  (p.header.inputs.keys ++ p.header.outputs.keys).map (·.name) ++
    match p.body with
    | .structured ss _ =>
      (Block.definedVars (P := Expression) (C := Command) ss false).map (·.name)
    | .cfg c _ => c.blocks.flatMap fun (_, blk) =>
        blk.cmds.flatMap fun cmd =>
          (HasVarsImp.definedVars (P := Expression) cmd false).map (·.name)
    | .abstract => []

/-- Every variable name a procedure mentions: its binders, the variables it assigns and the free
    variables of its expressions. -/
def procNames (p : Procedure) : List String :=
  procBinders p ++ procCollect fvarNames (fun _ => []) p ++
    match p.body with
    | .structured ss _ => (Block.modifiedVars (P := Expression) (C := Command) ss).map (·.name)
    | .cfg c _ => c.blocks.flatMap fun (_, blk) => blk.cmds.flatMap commandLhs
    | .abstract => []

/-- Every variable name a function mentions: its formals and the free variables of its
    expressions. -/
def funcVarNames (f : Function) : List String :=
  f.inputs.keys.map (·.name) ++ f.exprs.flatMap fvarNames

/-- For each of `xs`, a pair of it and its fresh name `x@k`, the first such name that neither it
    nor its `old` form is `taken` or picked earlier, and the pair of their `old` forms. `fuel`
    bounds the number of taken names. A candidate is refused when it or its `old` form is taken,
    when it was picked, or when it is the `old` form of a pick or has one as its `old` form, so
    the picks and their `old` forms are pairwise distinct. Each taken name refuses at most two
    candidates and each pick three, so the search tries enough of them to reach a free one.
    A name that is already a source, as `old x` is once `x` is renamed, keeps that pair: a
    variable written `old x` and the `old` form of `x` are one name, renamed alike. The binders
    are renamed in order of their number of `old` prefixes, so that `x` comes before `old x` and
    gives it the `old` form of its own new name; every name is then the source of one pair. -/
def freshRenaming (taken : String → Bool) (fuel : Nat) (xs : List String) :
    List (String × String) :=
  let oldDepth (n : String) : Nat :=
    let rec go (n : String) : Nat → Nat
      | 0 => 0
      | k + 1 =>
        if n.startsWith CoreIdent.oldStr then go (n.drop CoreIdent.oldStr.length).toString k + 1
        else 0
    go n n.length
  let xs := xs.mergeSort fun a b => oldDepth a ≤ oldDepth b
  let step (acc : List (String × String) × List String) (x : String) :=
    let (ren, picked) := acc
    if ren.any (·.1 == x) then acc else
    let taken' (n : String) :=
      taken n || taken (CoreIdent.mkOld n).name || picked.contains n ||
        picked.any fun p => n == (CoreIdent.mkOld p).name || (CoreIdent.mkOld n).name == p
    let y := Strata.Name.firstUntaken taken' (Strata.Name.disambiguate x)
      (2 * fuel + 3 * picked.length + 1) 1
    (((CoreIdent.mkOld x).name, (CoreIdent.mkOld y).name) :: (x, y) :: ren, y :: picked)
  (xs.foldl step ([], [])).1.reverse

/-- `d` with each variable it declares that `isFunc` names given a fresh name that `taken` does
    not hold; `none` when no variable of `d` needs it. `fuel` bounds the number of taken
    names. -/
def renameDecl (isFunc : String → Bool) (taken : String → Bool) (fuel : Thunk Nat) :
    Decl → Option Decl
  | .proc p md =>
    let clashes := ((procBinders p).filter isFunc).eraseDups
    if clashes.isEmpty then none
    else
      let used := procNames p
      some (.proc (renameProc (freshRenaming (fun n => taken n || used.contains n)
        (fuel.get + used.length) clashes) p) md)
  | .func f md => (renameFormals isFunc f).map (.func · md)
  | .recFuncBlock fs md =>
    let fs' := fs.map fun f => (renameFormals isFunc f, f)
    if fs'.all (·.1.isNone) then none
    else some (.recFuncBlock (fs'.map fun (r, f) => r.getD f) md)
  | _ => none
where
  /-- `f` with its formals that `isFunc` names renamed apart; `none` when there is none. -/
  renameFormals (isFunc : String → Bool) (f : Function) : Option Function :=
    let clashes := ((f.inputs.keys.map (·.name)).filter isFunc).eraseDups
    if clashes.isEmpty then none
    else
      let used := funcVarNames f
      some (renameFunc (freshRenaming (fun n => taken n || used.contains n)
        (fuel.get + used.length) clashes) f)

end ShadowingBinders

/-- `P` with each function formal, procedure parameter or local variable named like a function
    or constant given a fresh name throughout its declaration; `none` when no variable needs it.
    The functions are those of `P` and those `isFunc` holds, of which there are at most
    `nFuncs`. Each fresh name is the first `x@k`, `k ≥ 1`, that is no name of `P`, of the
    declaration or of a function, so `P` means the same. The program's names
    (`Program.takenNames` and its functions) are collected only when a variable needs
    renaming. -/
def Program.renameShadowingBinders (isFunc : String → Bool) (nFuncs : Nat) (P : Program) :
    Option Program :=
  let funcs := Std.HashSet.ofList P.funcNames
  let progNames : Thunk (Std.HashSet String) := Thunk.mk fun _ =>
    Std.HashSet.ofList (P.takenNames ++ P.funcNames)
  let isFunc' (n : String) := isFunc n || funcs.contains n
  let taken (n : String) := isFunc n || progNames.get.contains n
  let fuel : Thunk Nat := Thunk.mk fun _ => nFuncs + progNames.get.size
  let decls' := P.decls.map fun d => ShadowingBinders.renameDecl isFunc' taken fuel d
  if decls'.all (·.isNone) then none
  else some { P with decls := (decls'.zip P.decls).map fun (d', d) => d'.getD d }

/-- No variable `separateVarNames` would rename has the name of a function or constant of `P`:
    no variable a procedure declares (a parameter or a local) and no formal of a function.
    Functions registered only in a pipeline's factory are not part of the program, so this does
    not cover them; `separateVarNames` renames variables named like those too. -/
@[expose] def Program.varsNotFunctions (P : Program) : Bool :=
  let funcs := Std.HashSet.ofList P.funcNames
  let clear (ns : List String) := ns.all (!funcs.contains ·)
  let formals (f : Function) := f.inputs.keys.map (·.name)
  P.decls.all fun
    | .proc p _ => clear (ShadowingBinders.procBinders p)
    | .func f _ => clear (formals f)
    | .recFuncBlock fs _ => fs.all (clear ∘ formals)
    | _ => true

end Core

end -- public section

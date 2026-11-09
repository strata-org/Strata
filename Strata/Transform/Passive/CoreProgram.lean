/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Program
public import Strata.DL.Imperative.EvalContext
public import Strata.Languages.Core.Statement
public import Strata.Transform.Passive.CoreLang

/-! # The declaration phase and the Core vocabulary of the WP and SSA phases

The phases themselves (`Imperative.WP.wpEntry`, `Imperative.WP.ssaEntry`) are language-generic;
on Core procedures and programs (the instances `WPOps Expression`, `WPLang Expression`) the WP
phase (`WP/WPCoreProgram.lean`) and the SSA phase (`SSA/SSACoreProgram.lean`) share:

* the global names fresh names avoid: those of the program of the form of a fresh name
  (`freshForm`, `avoidOf`, `declNames`), built once per program into a hash set (`IdSet`);
* the declaration phase of a program (`declObligationsProgramWith`: the program-level
  declarations, then the axioms and procedures in place and one obligation unit per lemma,
  `lemmaUnit`, `axiomScopesAgree` checked: every obligation procedure is in the scope of the
  axioms of its source, `Program.axiomScopes`).

Their composition is in `CoreWPSSA.lean`; the properties of the declaration phase are in
`CoreProgramProps.lean`.

Key definitions: `avoidOf`, `declNames`, `declObligationsProgramWith`, `lemmaUnit`,
`axiomScopesAgree`. -/

namespace Core
namespace WP

open Imperative Imperative.WP Lambda

public section

/-- Can `x` be a name the phases introduce?  Every introduced name `b@n` contains `@`. -/
@[expose] def freshForm (x : Expression.Ident) : Bool := x.name.toList.contains '@'

/-- The names the introduced names avoid, for the identifiers `idents` of a procedure and
    the global names `globals`: those of them that contain `@` (no other name can equal an
    introduced name). -/
@[expose] def avoidOf (idents globals : List Expression.Ident) : List Expression.Ident :=
  (idents ++ globals).filter freshForm

/-- The obligation unit of a lemma: an obligation procedure named after the lemma whose body
    asserts (or, for a cover, covers) the obligation `ob` that symbolic evaluation states for
    the lemma (`Program.eval`: the lemma's expression over fresh free variables, labelled with
    the lemma's name). -/
@[expose] def lemmaUnit (name : String) (ob : Imperative.ProofObligation Expression) : Decl :=
  Decl.obligationProc ⟨name, ()⟩ [Imperative.Stmt.cmd (CmdExt.cmd ob.toCheckCmd)]

/-- Each obligation procedure of `output` is preceded by exactly the axioms its source
    procedure or lemma is preceded by in `input`. -/
@[expose] def axiomScopesAgree (input output : Program) : Bool :=
  Program.axiomScopes output == Program.axiomScopes input

/-- `axiomScopesAgree` in one walk of each program: the scopes agree exactly when the axioms and
    names in declaration order agree, up to the axioms after the last procedure or lemma. -/
@[expose] def axiomScopesAgreeH (input output : Program) : Bool :=
  Program.scopeEvents output == Program.scopeEvents input

/-- The scope event of a declaration: an axiom `(some d, "")`, a procedure or lemma
    `(none, name)`, any other declaration none. -/
private def scopeEv (d : Decl) : Option (Option Decl × String) :=
  match d with
  | .ax _ _ => some (some d, "")
  | .proc q _ => some (none, q.header.name.name)
  | .lemma l _ => some (none, l.name)
  | _ => none

/-- The scopes of the procedures and lemmas of the scope events `E`, the axioms `axs` declared
    before them. -/
private def scopesOf : List Decl → List (Option Decl × String) → List (String × List Decl)
  | _, [] => []
  | axs, (some d, _) :: r => scopesOf (axs ++ [d]) r
  | axs, (none, n) :: r => (n, axs) :: scopesOf axs r

/-- The scope events `E` without the axioms after the last procedure or lemma. -/
private def trimEv : List (Option Decl × String) → List (Option Decl × String)
  | [] => []
  | x :: r => if x.1.isSome && (trimEv r).isEmpty then [] else x :: trimEv r

/-- The scope events of scopes whose axiom lists extend `prev`. -/
private def eventsOf : List Decl → List (String × List Decl) → List (Option Decl × String)
  | _, [] => []
  | prev, (n, l) :: r => (l.drop prev.length).map (fun d => (some d, "")) ++
      (none, n) :: eventsOf l r

/-- `Program.axiomScopes` is the scopes of the scope events of the declarations. -/
private theorem axiomScopes_eq (p : Program) :
    Program.axiomScopes p = scopesOf [] (p.decls.filterMap scopeEv) := by
  unfold Program.axiomScopes
  suffices h : ∀ axs acc, (p.decls.foldl _ (axs, acc)).2 = acc ++ scopesOf axs _ from h [] []
  induction p.decls <;> intro axs acc <;> (try cases ‹Decl›) <;>
    simp [scopeEv, scopesOf, List.filterMap_cons, *]

/-- `Program.scopeEvents` is the trimmed scope events of the declarations. -/
private theorem scopeEvents_eq (p : Program) :
    Program.scopeEvents p =
      ((p.decls.filterMap scopeEv).reverse.dropWhile (·.1.isSome)).reverse := by
  simp only [Program.scopeEvents]
  congr 2
  suffices h : ∀ acc, p.decls.foldl _ acc = (p.decls.filterMap scopeEv).reverse ++ acc from
    (h []).trans (List.append_nil _)
  induction p.decls <;> intro acc <;> (try cases ‹Decl›) <;> simp [scopeEv, List.filterMap_cons, *]

/-- Trimming the scope events is dropping the trailing axioms. -/
private theorem trimEv_eq (E : List (Option Decl × String)) :
    (E.reverse.dropWhile (·.1.isSome)).reverse = trimEv E := by
  induction E <;> grind [trimEv, List.dropWhile_append, List.dropWhile]

/-- Trailing axioms add no scope. -/
private theorem scopesOf_trimEv (E : List (Option Decl × String)) :
    ∀ axs, scopesOf axs (trimEv E) = scopesOf axs E := by
  induction E <;> (try rename_i x _ _; rcases x with ⟨_ | d, n⟩) <;> grind [trimEv, scopesOf]

/-- The scope events of the scopes of `E` are the trimmed `E`, when every axiom event of `E`
    has the empty name. -/
private theorem eventsOf_scopesOf (E : List (Option Decl × String))
    (hE : ∀ x ∈ E, x.1.isSome → x.2 = "") : ∀ axs, eventsOf axs (scopesOf axs E) = trimEv E := by
  suffices h : ∀ axs ext, eventsOf axs (scopesOf (axs ++ ext) E) =
      if (trimEv E).isEmpty then [] else ext.map (fun d => (some d, "")) ++ trimEv E from
    fun axs => by grind [h axs []]
  refine E.rec (fun _ _ _ => rfl) (fun ⟨o, n⟩ r ih hE axs ext => ?_) hE
  have ih' := ih fun y hy => hE y (List.mem_cons_of_mem _ hy)
  cases o <;> grind [scopesOf, eventsOf, trimEv, ih' (axs ++ ext) [], ih' axs (ext ++ [_]),
    hE _ List.mem_cons_self]

/-- The compiled code of `axiomScopesAgree` is `axiomScopesAgreeH`, linear in the programs where
    `Program.axiomScopes` lists, for each procedure, every axiom before it. -/
@[csimp] theorem axiomScopesAgree_eq_axiomScopesAgreeH :
    @axiomScopesAgree = @axiomScopesAgreeH := by
  funext input output
  have hE : ∀ p : Program, ∀ x ∈ p.decls.filterMap scopeEv, x.1.isSome → x.2 = "" :=
    fun _ _ hx => (List.mem_filterMap.1 hx).elim fun d ⟨_, hd⟩ => by cases d <;> grind [scopeEv]
  simp only [axiomScopesAgree, axiomScopesAgreeH, axiomScopes_eq, scopeEvents_eq, trimEv_eq]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => by rw [← eventsOf_scopesOf _ (hE output), ← eventsOf_scopesOf _ (hE input), h],
    fun h => by rw [← scopesOf_trimEv, h, scopesOf_trimEv]⟩

/-- The names a program declares: its procedures, types and datatypes, and the function names
    of its declarations (`Decl.funcNames`, the names obligation extraction keeps parameters apart
    from).  A variable of an obligation is encoded as an SMT constant under its own name, as is a
    function of the program, so a variable must not have one of these names. -/
@[expose] def declNames (p : Program) : List Expression.Ident :=
  p.decls.flatMap fun d =>
    (match d with
      | .proc q _ => [q.header.name]
      | .type (.con tc) _ => [⟨tc.name, ()⟩]
      | .type (.syn ts) _ => [⟨ts.name, ()⟩]
      | .type (.data d) _ => d.map fun dt => (⟨dt.name, ()⟩ : Expression.Ident)
      | _ => []) ++ d.funcNames

/-- **The declaration phase of a program.**  `declProgram` supplies the program-level
    declarations (type declarations, evaluation-added functions with their pre-computed recursive
    axioms, `distinct` declarations — what `toCoreProofObligationProgram` produces for a program
    without procedures and lemmas); `lemmaObls` supplies the obligations symbolic evaluation
    states for the lemmas of the input program.  They are followed by the input program's axioms,
    its procedures unchanged, and one obligation unit per input lemma (`lemmaUnit` of the first
    obligation of `lemmaObls` labelled with the lemma's name), **in the input's relative order**,
    so each procedure and each obligation unit is in the scope of exactly the axioms declared
    before its source procedure or lemma (`axiomScopesAgree`, checked).  Hoisting every axiom
    before every procedure would let a procedure's obligations assume axioms declared after it —
    e.g. the axiom an `invokeOn` procedure contributes, which states that procedure's own
    postcondition. -/
@[expose] def declObligationsProgramWith (declProgram : Program)
    (lemmaObls : List (Imperative.ProofObligation Expression)) (program : Program) :
    Except String Program := do
  let lemmas : Std.HashMap String (Imperative.ProofObligation Expression) :=
    lemmaObls.foldr (fun ob m => m.insert ob.label ob) {}
  let decls ← program.decls.foldlM (init := ([] : List Decl)) fun acc d => do
      match d with
      | .ax _ _ | .proc _ _ => pure (d :: acc)
      | .lemma l _ =>
        match lemmas[l.name]? with
        | some ob => pure (lemmaUnit l.name ob :: acc)
        | none => throw s!"WP: lemma '{l.name}' has no obligation"
      | _ => pure acc
  let out : Program := { decls := declProgram.decls ++ decls.reverse }
  if axiomScopesAgree program out then pure out
  else throw "WP: an obligation procedure's axiom scope differs from its \
    source procedure's or lemma's"

end -- public section

end WP
end Core

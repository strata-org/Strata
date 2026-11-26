/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypingSpec
public import Strata.Languages.Core.StatementSemantics

/-! ## Typing of small-step configurations

`ConfigWellTyped` types the configurations of Core's small-step semantics, `CalleesStructured` is
the condition on the program's procedures that the progress results assume, and
`CalleesTyVarsScoped` is one that a well-typed program satisfies. -/

namespace Core
namespace TypeSpec

open Lambda Imperative
open Strata.Util (HMaps)

public section

/-- The labels that an `exit` can target inside a block labeled `label`, given the labels `L`
    of the blocks around it. An unlabeled block adds none. -/
def blockLabels : Option String → List String → List String
  | none, L => L
  | some l, L => l :: L

/-- Typing of a configuration under program `P` and factory `F`, with the type substitution `S`,
    enclosing block labels `L`, final context `C'`, final scopes `ts'` and floor scopes `tsf`.

    A configuration holds the image under `S` of code typed from some scopes: the typing is that
    of the code before `S` is applied. Its stores conform to the declarations of those scopes
    with `S` applied and bind nothing outside them. The floor scopes are declared by every scope
    the configuration passes through. The substitution `S` is the same in every nested
    configuration.

    The factory `F` is arbitrary: the only condition is that every environment carries it
    (`ρ.factory = F`). The results about this typing hold for every factory. -/
inductive ConfigWellTyped (P : Program) (F : Expression.Factory) (S : Subst) :
    List String → CoreConfig → LContext CoreLParams → TypeScopes → TypeScopes → Prop where
  /-- A statement that is the image under `S` of a statement typed from scopes `ts`. The factory
      is `F`, the store conforms to `ts` with `S` applied and binds nothing outside `ts`, the
      floor scopes are declared by `ts`, and the statement with `S` applied is ground. -/
  | stmt {L s s0 ρ C ts C' ts' tsf} :
      ρ.factory = F →
      s = mapStmtTys (LMonoTy.subst S) s0 →
      StoreHasTyping F ρ.store (ts.instVarTyping S) →
      StoreFresh ρ.store ts.find? →
      ScopeExtends tsf ts →
      Statement.Ground s →
      StatementWellTyped P C ts L s0 C' ts' →
      ConfigWellTyped P F S L (.stmt s ρ) C' ts' tsf
  /-- A statement list that is the image under `S` of a list typed from scopes `ts`, as for
      `stmt`. -/
  | stmts {L ss ss0 ρ C ts C' ts' tsf} :
      ρ.factory = F →
      ss = mapStmtsTys (LMonoTy.subst S) ss0 →
      StoreHasTyping F ρ.store (ts.instVarTyping S) →
      StoreFresh ρ.store ts.find? →
      ScopeExtends tsf ts →
      Statements.Ground ss →
      StatementsWellTyped P C ts L ss0 C' ts' →
      ConfigWellTyped P F S L (.stmts ss ρ) C' ts' tsf
  /-- A finished configuration, whose store conforms to the final scopes with `S` applied and
      binds nothing outside them. -/
  | terminal {L ρ C' ts' tsf} :
      ρ.factory = F →
      StoreHasTyping F ρ.store (ts'.instVarTyping S) →
      StoreFresh ρ.store ts'.find? →
      ConfigWellTyped P F S L (.terminal ρ) C' ts' tsf
  /-- An exiting configuration, which targets a label of `L` and has a store conforming to the
      floor scopes: an exit skips the declarations that follow it, so its store need not
      conform to the final scopes. -/
  | exiting {L l ρ C' ts' tsf} :
      ρ.factory = F →
      l ∈ L →
      StoreHasTyping F ρ.store (tsf.instVarTyping S) →
      ConfigWellTyped P F S L (.exiting l ρ) C' ts' tsf
  /-- A block configuration. It keeps the parent store, which conforms to scopes `tsp` that
      contain the floor and binds nothing outside them. The scopes `tsb` at the end of its inner
      configuration extend `tsp`. The inner configuration uses `tsp` as its floor and any labels
      the block makes available. The block ends in scopes equivalent to `tsp`. -/
  | block {L Lin label σp inner tsp Cb tsb C ts' tsf} :
      (∀ l ∈ Lin, l ∈ blockLabels label L) →
      StoreHasTyping F σp (tsp.instVarTyping S) →
      StoreFresh σp tsp.find? →
      ScopeExtends tsf tsp →
      ScopeExtends tsp tsb →
      ConfigWellTyped P F S Lin inner Cb tsb tsp →
      HMaps.Equiv ts' tsp →
      ConfigWellTyped P F S L (.block label σp inner) C ts' tsf
  /-- A sequence configuration. It types the statements that remain from the final context and
      scopes of its first part, which extend the floor. The remaining statements are the image
      under `S` of typed statements and are ground. -/
  | seq {L inner ss ss0 C1 ts1 C2 ts2 tsf} :
      ConfigWellTyped P F S L inner C1 ts1 tsf →
      ScopeExtends tsf ts1 →
      ss = mapStmtsTys (LMonoTy.subst S) ss0 →
      Statements.Ground ss →
      StatementsWellTyped P C1 ts1 L ss0 C2 ts2 →
      ConfigWellTyped P F S L (.seq inner ss) C2 ts2 tsf

/-- Every procedure of the program has a structured body or no body: a call to it runs its
    structured body, or, for an opaque procedure (`Body.isOpaque`), its contract. -/
@[expose] def CalleesStructured (P : Program) : Prop :=
  ∀ n p, Program.Procedure.find? P n = some p →
    (∃ ss opq, p.body = .structured ss opq) ∨ p.body = .abstract

/-- No undeclared type variables: every type variable in a structured procedure body's local
    declarations and call type arguments is a type parameter of the procedure. A body with
    `var y : 'b := *`, where `'b` is not a type parameter, is excluded: no value has type `'b`,
    so its run blocks at the declaration. A well-typed program satisfies it
    (`ProgramWellTyped.calleesTyVarsScoped`). -/
@[expose] def CalleesTyVarsScoped (P : Program) : Prop :=
  ∀ n p ss opq, Program.Procedure.find? P n = some p → p.body = .structured ss opq →
    Statements.AllDeclTys (fun ty => ∀ τ, ty = .forAll [] τ →
      ∀ a ∈ LMonoTy.freeVars τ, a ∈ p.header.typeArgs) ss

end -- public section

end TypeSpec
end Core

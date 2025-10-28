/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Parse
import Strata.DL.SMT.Term
import Strata.DDM.Format

namespace Strata

namespace SMTDDM

private def mkQualifiedIdent (s:String):QualifiedIdent SourceRange :=
  .qualifiedIdentImplicit SourceRange.none (Ann.mk SourceRange.none s)

private def mkSimpleSymbol (s:String):SimpleSymbol SourceRange :=
  .simple_symbol_qid SourceRange.none (mkQualifiedIdent s)

private def mkSymbol (s:String):Symbol SourceRange :=
  .symbol SourceRange.none (mkSimpleSymbol s)

private def mkIdentifier (s:String):Identifier SourceRange :=
  .iden_simple SourceRange.none (mkSymbol s)

private def translateFromTermPrim (t:SMT.TermPrim):
    Except String (SMTDDM.Term SourceRange) := do
  let srnone := SourceRange.none
  match t with
  | .bool b =>
    let ss:SimpleSymbol SourceRange :=
      if b then .simple_symbol_tt srnone else .simple_symbol_ff srnone
    return (.qual_identifier srnone
      (.qi_ident srnone (.iden_simple srnone (.symbol srnone ss))))
  | .int i =>
    let abs_i := if i < 0 then -i else i
    let s: Ann Nat SourceRange := Ann.mk srnone abs_i.toNat
    let v := .spec_constant_term srnone (.sc_numeral srnone s)
    return (
      if i >= 0 then v
      else
        let minusop:QualIdentifier SourceRange :=
          .qi_ident srnone (mkIdentifier "-")
        .qual_identifier_args srnone minusop (.qual_identifier srnone minusop)
            (Ann.mk srnone #[]))
  | .real _ => throw "real constant is unsupported"
  | .bitvec _ => throw "bit-vector constant is unsupported"
  | .string s =>
    return .spec_constant_term srnone (.sc_str srnone (Ann.mk srnone s))

private def translateFromTermType (t:SMT.TermType):
    Except String (SMTDDM.SMTSort SourceRange) := do
  let srnone := SourceRange.none
  match t with
  | .prim tp =>
    match tp with
    | .bool | .int | .real | .string =>
      return .smtsort_ident srnone (mkIdentifier tp.mkName)
    | .bitvec n =>
      return (.smtsort_ident srnone
        (.iden_indexed srnone
          (mkSymbol "bitvec")
          (.ind_numeral srnone (Ann.mk srnone n))
          (Ann.mk srnone #[])))
    | .trigger =>
      throw "don't know how to translate a trigger type"
  | .option _ =>
    throw "don't know how to translate an option type"
  | .constr id args =>
    let argtys <- args.mapM translateFromTermType
    match argtys with
    | [] => throw "empty argument to type constructor"
    | argtyh::argtyt =>
      let argtyt_arr := Array.mk argtyt
      return .smtsort_param srnone (mkIdentifier id) argtyh
        (Ann.mk srnone argtyt_arr)

def translateFromTerm (t:SMT.Term): Except String (SMTDDM.Term SourceRange) := do
  let srnone := SourceRange.none
  match t with
  | .prim p => translateFromTermPrim p
  | .var v =>
    return .qual_identifier srnone (.qi_ident srnone (.iden_simple srnone
      (.symbol srnone (mkSimpleSymbol v.id))))
  | .none _ | .some _ => throw "don't know how to translate none and some"
  | .app op args _ =>
    let args' <- args.mapM translateFromTerm
    match args' with
    | argsh::argst =>
      return (.qual_identifier_args srnone
        (.qi_ident srnone (mkIdentifier op.mkName))
          argsh (Ann.mk srnone (Array.mk argst)))
    | [] =>
      return (.qual_identifier srnone (.qi_ident srnone (mkIdentifier op.mkName)))
  | .quant qkind args tr body =>
    let args_sorted:List (SMTDDM.SortedVar SourceRange) <-
      args.mapM
        (fun ⟨name,ty⟩ => do
          let ty' <- translateFromTermType ty
          return .sorted_var srnone (mkSymbol name) ty')
    match args_sorted with
    | [] => throw "empty quantifier"
    | args_sorted_h::args_sorted_t =>
      let body <- translateFromTerm body
      match qkind with
      | .all =>
        return .forall_smt srnone args_sorted_h
          (Ann.mk srnone (Array.mk args_sorted_t)) body
      | .exist =>
        return .exists_smt srnone args_sorted_h
          (Ann.mk srnone (Array.mk args_sorted_t)) body

/-- info: "program SMTDDM;\n(+1020)" -/
#guard_msgs in #eval (
  match (translateFromTerm
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int 20))] .int)) with
  | .ok t => do
    let s := dialectExt.getState (←Lean.getEnv)
    let prg := Program.create s.loaded.dialects "SMTDDM" #[SMTDDM.Term.toAst t]
    return ToString.toString prg
  | .error _ => panic! "fail")

end SMTDDM

end Strata

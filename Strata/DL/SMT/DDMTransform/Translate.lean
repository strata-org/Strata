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
        -- Note that negative integers like '-1231' are symbols! (Sec 3.1. Lexicon)
        -- Since the only way to create a unary term from symbol is through
        -- idenitifer, use mkIdentifier.
        .qual_identifier srnone (.qi_ident srnone (mkIdentifier (toString i))))
  | .real str_repr =>
    return (.qual_identifier srnone (.qi_ident srnone (mkIdentifier str_repr)))
  | .bitvec bv =>
    let bvty := mkSymbol (s!"bv{bv.toNat}")
    let val:Index SourceRange := .ind_numeral srnone (Ann.mk srnone bv.width)
    return (.qual_identifier srnone
      (.qi_ident srnone (.iden_indexed srnone bvty val
        (Ann.mk srnone #[]))))
  | .string s =>
    return .spec_constant_term srnone (.sc_str srnone (Ann.mk srnone s))

private def translateFromTermType (t:SMT.TermType):
    Except String (SMTDDM.SMTSort SourceRange) := do
  let srnone := SourceRange.none
  match t with
  | .prim tp =>
    match tp with
    | .bitvec n =>
      return (.smtsort_ident srnone
        (.iden_indexed srnone
          (mkSymbol "BitVec")
          (.ind_numeral srnone (Ann.mk srnone n))
          (Ann.mk srnone #[])))
    | .trigger =>
      throw "don't know how to translate a trigger type"
    | _ =>
      return .smtsort_ident srnone (mkIdentifier
         (match tp with
          | .bool => "Bool"
          | .int => "Int"
          | .real => "Real"
          | .string => "String"
          | .regex => "RegLan"
          | _ => panic! "unreachable"))
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


private def dummy_prg_for_toString :=
  let dialect_map := DialectMap.ofList!
    [Strata.initDialect, Strata.smtReservedKeywordsDialect, Strata.SMTCore,
     Strata.SMT]
  Program.create dialect_map "SMT" #[]

def toString (t:SMT.Term): Except String String := do
  let ddm_term <- translateFromTerm t
  let ddm_ast := SMTDDM.Term.toAst ddm_term
  let fmt := Operation.instToStrataFormat.mformat ddm_ast
    (dummy_prg_for_toString.formatContext {})
    dummy_prg_for_toString.formatState
  return fmt.format |>.render


/-- info: Except.ok "( + 10 20 )" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int 20))] .int))

/-- info: Except.ok "( _ bv1 32  )" -/
#guard_msgs in #eval (toString
    (.prim (.bitvec (BitVec.ofNat 32/-width-/ 1/-value-/))))

end SMTDDM

end Strata

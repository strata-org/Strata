/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.DDMTransform.Parse
import Strata.DL.SMT.Term
import Strata.DDM.Format
import Strata.DDM.Util.DecimalRat

namespace Strata

namespace SMTDDM

private def mkQualifiedIdent (s:String):QualifiedIdent SourceRange :=
  .qualifiedIdentImplicit SourceRange.none (Ann.mk SourceRange.none s)

private def mkSimpleSymbol (s:String):SimpleSymbol SourceRange :=
  match List.find? (fun (_,sym) => sym = s) specialCharsInSimpleSymbol with
  | .some (name,_) =>
    -- This needs hard-coded for now.
    (match name with
    | "plus" => .simple_symbol_plus SourceRange.none
    | "minus" => .simple_symbol_minus SourceRange.none
    | "star" => .simple_symbol_star SourceRange.none
    | "eq" => .simple_symbol_eq SourceRange.none
    | "percent" => .simple_symbol_percent SourceRange.none
    | "questionmark" => .simple_symbol_questionmark SourceRange.none
    | "period" => .simple_symbol_period SourceRange.none
    | "dollar" => .simple_symbol_dollar SourceRange.none
    | "tilde" => .simple_symbol_tilde SourceRange.none
    | "amp" => .simple_symbol_amp SourceRange.none
    | "caret" => .simple_symbol_caret SourceRange.none
    | "lt" => .simple_symbol_lt SourceRange.none
    | "gt" => .simple_symbol_gt SourceRange.none
    | "at" => .simple_symbol_at SourceRange.none
    | _ => panic! s!"Unknown simple symbol: {name}")
  | .none =>
    .simple_symbol_qid SourceRange.none (mkQualifiedIdent s)

private def mkSymbol (s:String):Symbol SourceRange :=
  .symbol SourceRange.none (mkSimpleSymbol s)

private def mkIdentifier (s:String):SMTIdentifier SourceRange :=
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
    if i >= 0 then
      return .spec_constant_term srnone (.sc_numeral srnone abs_i.toNat)
    else
      -- Note that negative integers like '-1231' are symbols in Std! (Sec 3.1. Lexicon)
      -- The only way to create a unary symbol is through idenitifers, but this
      -- makes its DDM format wrapped with pipes, like '|-1231|`. Since such
      -- representation cannot be recognized by Z3, make a workaround which is to have
      -- separate `*_neg` categories for sc_numeral/decimal.
      return .spec_constant_term srnone (.sc_numeral_neg srnone abs_i.toNat)
  | .real dec =>
    return .spec_constant_term srnone (.sc_decimal srnone dec)
  | .bitvec bv =>
    let bvty := mkSymbol (s!"bv{bv.toNat}")
    let val:Index SourceRange := .ind_numeral srnone bv.width
    return (.qual_identifier srnone
      (.qi_ident srnone (.iden_indexed srnone bvty val
        (Ann.mk srnone #[]))))
  | .string s =>
    return .spec_constant_term srnone (.sc_str srnone s)

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
          (.ind_numeral srnone n)
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
  | .quant qkind args _tr body =>
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


/-- info: Except.ok "(+ 10 20)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int 20))] .int))

/-- info: Except.ok "(+ 10 -20)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.int 10)), (.prim (.int (-20)))] .int))

/-- info: Except.ok "(+ 0.1 0.2)" -/
#guard_msgs in #eval (toString
    (.app SMT.Op.add [(.prim (.real (Decimal.mk 1 (-1)))),
                      (.prim (.real (Decimal.mk 2 (-2))))] .int))

/-- info: Except.ok "( _ bv1 32 )" -/
#guard_msgs in #eval (toString
    (.prim (.bitvec (BitVec.ofNat 32/-width-/ 1/-value-/))))

end SMTDDM

end Strata

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DL.SMT.DDMTransform.Parse
import Strata.DL.SMT.Term

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
    | "le" => .simple_symbol_le SourceRange.none
    | "ge" => .simple_symbol_ge SourceRange.none
    | "implies" => .simple_symbol_implies SourceRange.none
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
      (.qi_ident srnone (.iden_indexed srnone bvty (Ann.mk srnone #[val]))))
  | .string s =>
    return .spec_constant_term srnone (.sc_str srnone s)

-- List of SMTSort to Array.
private def translateFromSMTSortList (l: List (SMTSort SourceRange)):
    Array (SMTSort SourceRange) :=
  l.toArray

private def translateFromTermType (t:SMT.TermType):
    Except String (SMTDDM.SMTSort SourceRange) := do
  let srnone := SourceRange.none
  match t with
  | .prim tp =>
    match tp with
    | .bitvec n =>
      let idx : Index SourceRange := .ind_numeral srnone n
      return (.smtsort_ident srnone
        (.iden_indexed srnone
          (mkSymbol "BitVec")
          (Ann.mk srnone #[idx])))
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
    let argtys_array := translateFromSMTSortList argtys
    if argtys_array.isEmpty then
      throw "empty argument to type constructor"
    else
      return .smtsort_param srnone (mkIdentifier id) (Ann.mk srnone argtys_array)

-- Helper function to convert a SMTDDM.Term to SExpr for use in pattern attributes
def termToSExpr (t : SMTDDM.Term SourceRange) : SMTDDM.SExpr SourceRange :=
  let srnone := SourceRange.none
  match t with
  | .qual_identifier _ qi =>
      match qi with
      | .qi_ident _ iden =>
          match iden with
          | .iden_simple _ sym => .se_symbol srnone sym
          | _ => .se_symbol srnone (.symbol srnone (.simple_symbol_qid srnone (mkQualifiedIdent "term")))
      | _ => .se_symbol srnone (.symbol srnone (.simple_symbol_qid srnone (mkQualifiedIdent "term")))
  | .qual_identifier_args _ qi args =>
      -- Function application in pattern: convert to nested S-expr
      let qiSExpr := match qi with
        | .qi_ident _ iden =>
            match iden with
            | .iden_simple _ sym => SMTDDM.SExpr.se_symbol srnone sym
            | _ => .se_symbol srnone (.symbol srnone (.simple_symbol_qid srnone (mkQualifiedIdent "fn")))
        | _ => .se_symbol srnone (.symbol srnone (.simple_symbol_qid srnone (mkQualifiedIdent "fn")))
      -- Convert args array to SExpr list
      let argsSExpr := args.val.map termToSExpr
      .se_ls srnone (Ann.mk srnone ((qiSExpr :: argsSExpr.toList).toArray))
  | _ => .se_symbol srnone (.symbol srnone (.simple_symbol_qid srnone (mkQualifiedIdent "term")))
  decreasing_by
    cases args
    rename_i hargs
    have := Array.sizeOf_lt_of_mem hargs
    simp_all; omega

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
    let args_array := args'.toArray
    if args_array.isEmpty then
      return (.qual_identifier srnone (.qi_ident srnone (mkIdentifier op.mkName)))
    else
      return (.qual_identifier_args srnone
        (.qi_ident srnone (mkIdentifier op.mkName)) (Ann.mk srnone args_array))
  | .quant qkind args tr body =>
    let args_sorted:List (SMTDDM.SortedVar SourceRange) <-
      args.mapM
        (fun ⟨name,ty⟩ => do
          let ty' <- translateFromTermType ty
          return .sorted_var srnone (mkSymbol name) ty')
    let args_array := args_sorted.toArray
    if args_array.isEmpty then
      throw "empty quantifier"
    else
      let body <- translateFromTerm body

      -- Handle triggers/patterns
      let bodyWithPattern <-
        match tr with
        | .app .triggers triggerTerms .trigger =>
          if triggerTerms.isEmpty then
            -- No patterns - return body as-is
            pure body
          else
            -- Convert each trigger term to a SMTDDM.Term, then to SExpr
            let triggerDDMTerms <- triggerTerms.mapM translateFromTerm
            let triggerSExprs := triggerDDMTerms.map termToSExpr

            -- Create the :pattern attribute
            -- av_sel wraps the SExprs in parens, so we pass the array directly
            let patternAttr : SMTDDM.Attribute SourceRange :=
              .att_kw srnone
                (.kw_symbol srnone (mkSimpleSymbol "pattern"))
                (Ann.mk srnone (some (.av_sel srnone (Ann.mk srnone triggerSExprs.toArray))))

            -- Wrap body with bang operator and pattern attribute
            pure (.bang srnone body (Ann.mk srnone #[patternAttr]))
        | _ =>
          -- Unexpected trigger format - return body as-is
          pure body

      match qkind with
      | .all =>
        return .forall_smt srnone (Ann.mk srnone args_array) bodyWithPattern
      | .exist =>
        return .exists_smt srnone (Ann.mk srnone args_array) bodyWithPattern


private def dummy_prg_for_toString :=
  let dialect_map := DialectMap.ofList!
    [Strata.initDialect, Strata.smtReservedKeywordsDialect, Strata.SMTCore,
     Strata.SMT]
  Program.create dialect_map "SMT" #[]

def toString (t:SMT.Term): Except String String := do
  let ddm_term <- translateFromTerm t
  let ddm_ast := SMTDDM.Term.toAst ddm_term
  let ctx := dummy_prg_for_toString.formatContext {}
  let s := dummy_prg_for_toString.formatState
  return ddm_ast.render ctx s |>.fst

end SMTDDM

end Strata

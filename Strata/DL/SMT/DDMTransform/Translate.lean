/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.SMT.DDMTransform.Parse
public import Strata.DL.SMT.Term
public import Strata.Util.Provenance
public import Strata.Util.Tactics
import Strata.DDM.Elab.LoadedDialects

namespace Strata

public section

namespace SMTDDM

/-- Annotation used for all synthesized SMT DDM nodes. -/
private abbrev smtProv : Provenance := .synthesized .smtEncode

/-- Wrap a value with the SMT provenance annotation. -/
private abbrev smtAnn (v : α) : Ann α Provenance := Ann.mk smtProv v

private def mkQualifiedIdent (s:String):QualifiedIdent Provenance :=
  .qualifiedIdentImplicit smtProv (smtAnn s)

private def mkSimpleSymbol (s:String):SimpleSymbol Provenance :=
  match List.find? (fun (_,sym) => sym = s) specialCharsInSimpleSymbol with
  | .some (name,_) =>
    -- This needs hard-coded for now.
    (match name with
    | "plus" => .simple_symbol_plus smtProv
    | "minus" => .simple_symbol_minus smtProv
    | "star" => .simple_symbol_star smtProv
    | "eq" => .simple_symbol_eq smtProv
    | "percent" => .simple_symbol_percent smtProv
    | "questionmark" => .simple_symbol_questionmark smtProv
    | "period" => .simple_symbol_period smtProv
    | "tilde" => .simple_symbol_tilde smtProv
    | "amp" => .simple_symbol_amp smtProv
    | "caret" => .simple_symbol_caret smtProv
    | "lt" => .simple_symbol_lt smtProv
    | "gt" => .simple_symbol_gt smtProv
    | "at" => .simple_symbol_at smtProv
    | "le" => .simple_symbol_le smtProv
    | "ge" => .simple_symbol_ge smtProv
    | "implies" => .simple_symbol_implies smtProv
    | _ => panic! s!"Unknown simple symbol: {name}")
  | .none =>
    .simple_symbol_qid smtProv (mkQualifiedIdent s)

private def mkSymbol (s:String):Symbol Provenance :=
  .symbol smtProv (mkSimpleSymbol s)

private def mkIdentifier (s:String):SMTIdentifier Provenance :=
  .iden_simple smtProv (mkSymbol s)

private def translateFromTermPrim (t:SMT.TermPrim):
    Except String (SMTDDM.Term Provenance) := do
  match t with
  | .bool b =>
    let ss:SimpleSymbol Provenance :=
      if b then .simple_symbol_tt smtProv else .simple_symbol_ff smtProv
    return (.qual_identifier smtProv
      (.qi_ident smtProv (.iden_simple smtProv (.symbol smtProv ss))))
  | .int i =>
    let abs_i := if i < 0 then -i else i
    if i >= 0 then
      return .spec_constant_term smtProv (.sc_numeral smtProv abs_i.toNat)
    else
      -- SMT-LIB represents negative integers as (- N), i.e. unary minus
      -- applied to the absolute value.
      let posTerm := Term.spec_constant_term smtProv (.sc_numeral smtProv abs_i.toNat)
      return .qual_identifier_args smtProv
        (.qi_ident smtProv (mkIdentifier "-"))
        (smtAnn #[posTerm])
  | .real dec =>
    return .spec_constant_term smtProv (.sc_decimal smtProv dec)
  | .bitvec (n := n) bv =>
    let bvty := mkSymbol (s!"bv{bv.toNat}")
    let val:Index Provenance := .ind_numeral smtProv n
    return (.qual_identifier smtProv
      (.qi_ident smtProv (.iden_indexed smtProv bvty (smtAnn #[val]))))
  | .string s =>
    return .spec_constant_term smtProv (.sc_str smtProv s)

-- List of SMTSort to Array.
private def translateFromSMTSortList (l: List (SMTSort Provenance)):
    Array (SMTSort Provenance) :=
  l.toArray

private def translateFromTermType (t:SMT.TermType):
    Except String (SMTDDM.SMTSort Provenance) := do
  match t with
  | .prim tp =>
    match tp with
    | .bitvec n =>
      let idx : Index Provenance := .ind_numeral smtProv n
      return (.smtsort_ident smtProv
        (.iden_indexed smtProv
          (mkSymbol "BitVec")
          (smtAnn #[idx])))
    | .trigger =>
      throw "don't know how to translate a trigger type"
    | _ =>
      let res:String ← match tp with
          | .bool => .ok "Bool"
          | .int => .ok "Int"
          | .real => .ok "Real"
          | .string => .ok "String"
          | .regex => .ok "RegLan"
          | _ => throw "unreachable"
      return .smtsort_ident smtProv (mkIdentifier res)
  | .option ty =>
    let argty ← translateFromTermType ty
    return .smtsort_param smtProv (mkIdentifier "Option") (smtAnn #[argty])
  | .constr id args =>
    let argtys <- args.mapM translateFromTermType
    let argtys_array := translateFromSMTSortList argtys
    if argtys_array.isEmpty then
      return .smtsort_ident smtProv (mkIdentifier id)
    else
      return .smtsort_param smtProv (mkIdentifier id) (smtAnn argtys_array)

-- Helper: convert an Index to an SExpr
private def indexToSExpr (idx : SMTDDM.Index Provenance)
    : SMTDDM.SExpr Provenance :=
  match idx with
  | .ind_numeral _ n => .se_spec_const smtProv (.sc_numeral smtProv n)
  | .ind_symbol _ sym => .se_symbol smtProv sym

-- Helper: convert an indexed identifier to an SExpr: (_ sym idx1 idx2 ...)
private def indexedIdentToSExpr (sym : SMTDDM.Symbol Provenance)
    (indices : Ann (Array (SMTDDM.Index Provenance)) Provenance)
    : SMTDDM.SExpr Provenance :=
  let underscoreSym := SMTDDM.SExpr.se_symbol smtProv (mkSymbol "_")
  let idxSExprs := indices.val.toList.map indexToSExpr
  .se_ls smtProv (smtAnn ((underscoreSym :: .se_symbol smtProv sym :: idxSExprs).toArray))

-- Helper: convert an SMTSort to an SExpr for use in pattern attributes
private def sortToSExpr (s : SMTDDM.SMTSort Provenance)
    : Except String (SMTDDM.SExpr Provenance) := do
  match s with
  | .smtsort_ident _ (.iden_simple _ sym) => return .se_symbol smtProv sym
  | .smtsort_ident _ (.iden_indexed _ sym indices) =>
    return indexedIdentToSExpr sym indices
  | .smtsort_param _ (.iden_simple _ sym) args =>
    let argsSExpr ← args.val.toList.mapM sortToSExpr
    return .se_ls smtProv (smtAnn ((.se_symbol smtProv sym :: argsSExpr).toArray))
  | _ => throw s!"Doesn't know how to convert sort {repr s} to SMTDDM.SExpr"
  termination_by SizeOf.sizeOf s
  decreasing_by cases args; simp_all; term_by_mem


-- Helper: convert a QualIdentifier to an SExpr for use in pattern attributes
private def qiToSExpr (qi : SMTDDM.QualIdentifier Provenance)
    : Except String (SMTDDM.SExpr Provenance) := do
  match qi with
  | .qi_ident _ (.iden_simple _ sym) => pure (.se_symbol smtProv sym)
  | .qi_ident _ (.iden_indexed _ sym indices) =>
    pure (indexedIdentToSExpr sym indices)
  | .qi_isort _ (.iden_simple _ sym) sort =>
    let sortSExpr ← sortToSExpr sort
    let asSym := SMTDDM.SExpr.se_symbol smtProv (mkSymbol "as")
    pure (.se_ls smtProv (smtAnn #[asSym, .se_symbol smtProv sym, sortSExpr]))
  | _ => throw s!"Doesn't know how to convert QI {repr qi} to SMTDDM.SExpr"

-- Helper function to convert a SMTDDM.Term to SExpr for use in pattern attributes
def termToSExpr (t : SMTDDM.Term Provenance)
    : Except String (SMTDDM.SExpr Provenance) := do
  match t with
  | .qual_identifier _ qi => qiToSExpr qi
  | .qual_identifier_args _ qi args =>
      let qiSExpr ← qiToSExpr qi
      let argsSExpr ← args.val.mapM termToSExpr
      return .se_ls smtProv (smtAnn ((qiSExpr :: argsSExpr.toList).toArray))
  | .spec_constant_term _ s => return .se_spec_const smtProv s
  | _ => throw s!"Doesn't know how to convert {repr t} to SMTDDM.SExpr"
  decreasing_by cases args; term_by_mem

partial def translateFromTerm (t:SMT.Term): Except String (SMTDDM.Term Provenance) := do
  match t with
  | .prim p => translateFromTermPrim p
  | .var v =>
    return .qual_identifier smtProv (.qi_ident smtProv (.iden_simple smtProv
      (.symbol smtProv (mkSimpleSymbol v.id))))
  | .none _ | .some _ => throw "don't know how to translate none and some"
  | .app op args retTy =>
    let args' <- args.mapM translateFromTerm
    let args_array := args'.toArray
    let mk_qual_identifier (qi:QualIdentifier Provenance) : SMTDDM.Term Provenance :=
      if args_array.isEmpty then
        (.qual_identifier smtProv qi)
      else
        (.qual_identifier_args smtProv qi (smtAnn args_array))

    -- Datatype constructors need (as Name RetType) qualification for SMT-LIB
    match op with
    | .datatype_op .constructor name =>
      let retSort ← translateFromTermType retTy
      let qi := QualIdentifier.qi_isort smtProv (mkIdentifier name) retSort
      return mk_qual_identifier qi
    | .bv (.zero_extend n) =>
      let iden := SMTIdentifier.iden_indexed smtProv (mkSymbol "zero_extend")
        (smtAnn #[.ind_numeral smtProv n])
      return mk_qual_identifier (.qi_ident smtProv iden)
    | .str (.re_index n) =>
      let iden := SMTIdentifier.iden_indexed smtProv (mkSymbol "re.^")
        (smtAnn #[.ind_numeral smtProv n])
      return mk_qual_identifier (.qi_ident smtProv iden)
    | .str (.re_loop n₁ n₂) =>
      let iden := SMTIdentifier.iden_indexed smtProv (mkSymbol "re.loop")
        (smtAnn #[.ind_numeral smtProv n₁, .ind_numeral smtProv n₂])
      return mk_qual_identifier (.qi_ident smtProv iden)
    | _ =>
      return mk_qual_identifier (.qi_ident smtProv (mkIdentifier op.mkName))
  | .quant qkind args tr body =>
    let args_sorted:List (SMTDDM.SortedVar Provenance) <-
      args.mapM
        (fun ⟨name,ty⟩ => do
          let ty' <- translateFromTermType ty
          return .sorted_var smtProv (mkSymbol name) ty')
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
            -- Extract trigger groups. The Encoder builds:
            --   .app .triggers [.app .triggers group₁ .trigger, .app .triggers group₂ .trigger, ...] .trigger
            -- Each inner .app .triggers represents one :pattern group.
            -- If a trigger term is NOT .app .triggers, treat it as a single-term group.
            let mut patternAttrs : Array (SMTDDM.Attribute Provenance) := #[]
            for trigTerm in triggerTerms do
              let sexprs ← match trigTerm with
                | .app .triggers its _ => do
                  let ddmTerms ← its.mapM translateFromTerm
                  ddmTerms.mapM termToSExpr
                | other => do
                  let ddmTerm ← translateFromTerm other
                  pure [← termToSExpr ddmTerm]
              let attr : SMTDDM.Attribute Provenance :=
                .att_kw smtProv
                  (.kw_symbol smtProv (mkSimpleSymbol "pattern"))
                  (smtAnn (some (.av_sel smtProv (smtAnn sexprs.toArray))))
              patternAttrs := patternAttrs.push attr
            -- Wrap body with bang operator and pattern attributes
            pure (.bang smtProv body (smtAnn patternAttrs))
        | _ =>
          -- Unexpected trigger format - return body as-is
          pure body

      match qkind with
      | .all =>
        return .forall_smt smtProv (smtAnn args_array) bodyWithPattern
      | .exist =>
        return .exists_smt smtProv (smtAnn args_array) bodyWithPattern


private def dummy_prg_for_toString :=
  let dialect_map := DialectMap.ofList!
    [Strata.initDialect, Strata.smtReservedKeywordsDialect, Strata.SMTCore,
     Strata.SMT]
  Program.create dialect_map "SMT" #[]

def termToString (t:SMT.Term): Except String String := do
  let ddm_term <- translateFromTerm t
  let ddm_ast := SMTDDM.Term.toAst ddm_term
  let ctx := dummy_prg_for_toString.formatContext { smtStringEscaping := true }
  let s := dummy_prg_for_toString.formatState
  return ddm_ast.render ctx s |>.fst

def termTypeToString (t:SMT.TermType): Except String String := do
  let ddm_term <- translateFromTermType t
  let ddm_ast := SMTDDM.SMTSort.toAst ddm_term
  let ctx := dummy_prg_for_toString.formatContext { smtStringEscaping := true }
  let s := dummy_prg_for_toString.formatState
  return ddm_ast.render ctx s |>.fst

end SMTDDM

namespace SMTResponseDDM

/-- The loaded dialects needed to parse SMTResponse commands. -/
def smtResponseDialects : Strata.Elab.LoadedDialects :=
  .ofDialects! #[Strata.initDialect, Strata.smtReservedKeywordsDialect,
                 Strata.SMTCore, Strata.SMTResponse]

/-- Format context for rendering SMTResponse `Arg` values back to strings. -/
private def smtFormatContext : Strata.FormatContext :=
  .ofDialects smtResponseDialects.dialects

/-- Format state for rendering SMTResponse `Arg` values back to strings. -/
private def smtFormatState : Strata.FormatState where
  openDialects := smtResponseDialects.dialects.toList.foldl (init := {}) fun s d => s.insert d.name

/-- Render a DDM `Arg` to a string using the SMTResponse dialect formatting. -/
def formatArg (arg : Strata.Arg) : String :=
  (Strata.mformat arg smtFormatContext smtFormatState).format.pretty

/--
Convert an `SMTResponseDDM.Term` (parsed from solver output) into a
`Strata.SMT.Term`. Handles the common model-value cases:

- Spec constants (numerals, decimals, strings, hex/binary literals)
- Qualified identifiers (symbols like `true`, `false`, constructor names)
- Function applications (constructor applications, `(as Nil (List Int))`)

Note that the returned SMT.Term might not have the right type information, as
the type information does not exist in the Term itself. It is the caller's
responsibility to correctly fill in the types in .app/.uf, or faithfully
ignore these.
-/
partial def translateFromDDMTermToUntyped (t : Strata.SMTResponseDDM.Term Strata.SourceRange)
    : Except String Strata.SMT.Term := do
  match t with
  | .spec_constant_term _ sc =>
    -- Exhaustive match over all SpecConstant variants; Lean will flag any missing case.
    match sc with
    | .sc_numeral _ n     => return .prim (.int n)
    | .sc_numeral_neg _ n => return .prim (.int (-(n : Int)))
    | .sc_decimal _ d     => return .prim (.real d)
    | .sc_decimal_neg _ d => return .prim (.real { d with mantissa := -d.mantissa })
    | .sc_str _ s         => return .prim (.string s)
  | .qual_identifier _ qi =>
    match resolveQI qi with
    | some ("true", _)  => return .prim (.bool true)
    | some ("false", _) => return .prim (.bool false)
    | some (name, _)    => return mkUFApp name []
    | none              => throw s!"translateFromDDMTermUnsafe: don't know how to convert {repr t}"
  | .qual_identifier_args _ qi args =>
    match resolveQI qi with
    | some (name, _) =>
      let argTerms ← args.val.toList.mapM translateFromDDMTermToUntyped
      return mkUFApp name argTerms
    | none => throw s!"translateFromDDMTermToUntyped: don't know how to convert {repr t}"
  | _ => throw s!"translateFromDDMTermToUntyped: don't know how to convert {repr t}"

where
  /-- Extract the name string from a QualIdentifier. -/
  resolveQI (qi : Strata.SMTResponseDDM.QualIdentifier Strata.SourceRange)
      : Option (String × Option (Strata.SMTResponseDDM.SMTSort Strata.SourceRange)) :=
    match qi with
    | .qi_ident _ iden =>
      match iden with
      | .iden_simple _ sym | .iden_indexed _ sym _
      => some (symbolToString sym, none)
    | .qi_isort _ iden sort =>
      match iden with
      | .iden_simple _ sym | .iden_indexed _ sym _
      => some (symbolToString sym, some sort)
  /-- Extract the raw string from a Symbol. -/
  symbolToString (sym : Strata.SMTResponseDDM.Symbol Strata.SourceRange) : String :=
    formatArg (.op (Strata.SMTResponseDDM.Symbol.toAst sym))
  /-- Build a `Term.app` with a UF op for a named function/constructor.
      Since the SMTDDM's term does not have any type annotation, the return
      type is always filled with a placeholder type "_placeholder".
      Also, its arguments are simply assigned an empty list. -/
  mkUFApp (name : String) (args : List Strata.SMT.Term) : Strata.SMT.Term :=
    let placeholderTy := Strata.SMT.TermType.constr "_placeholder" []
    let uf : Strata.SMT.UF := { id := name, args := [], out := placeholderTy }
    .app (.core (.uf uf)) args placeholderTy

end SMTResponseDDM

end

end Strata

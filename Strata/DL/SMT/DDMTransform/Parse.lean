/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.BuiltinDialects.BuiltinM
import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

namespace Strata

open Elab

private def reservedKeywords := [
    -- A list of (name in DDM (without "reserved_" prefix), the string)
    -- Category "General"
    ("bang", "!"),
    ("underbar", "_"),
    ("as", "as"),
    ("binary", "BINARY"),
    ("decimal", "DECIMAL"),
    ("exists", "EXISTS"),
    ("hexadecimal", "HEXADECIMAL"),
    ("forall", "forall"),
    ("lambda", "lambda"),
    ("let", "let"),
    ("match", "match"),
    ("numeral", "NUMERAL"),
    ("par", "par"),
    ("string", "STRING"),
    -- Category "Command names"
    ("r_assert", "assert"),
    ("check_sat", "check-sat"),
    ("check_sat_assuming", "check-sat-assuming"),
    ("declare_const", "declare-const"),
    ("declare_datatype", "declare-datatype"),
    ("declare_fun", "declare-fun"),
    ("declare_sort", "declare-sort"),
    ("declare_sort_parameter", "declare-sort-parameter"),
    ("define_const", "define-const"),
    ("define_fun", "define-fun"),
    ("define_fun_rec", "define-fun-rec"),
    ("define_sort", "define-sort"),
    ("echo", "echo"),
    ("exit", "exit"),
    ("get_assertions", "get-assertions"),
    ("get_assignment", "get-assignment"),
    ("get_info", "get-info"),
    ("get_model", "get-model"),
    ("get_option", "get-option"),
    ("get_proof", "get-proof"),
    ("get_unsat_assumptions", "get-unsat-assumptions"),
    ("get_unsat_core", "get-unsat-core"),
    ("get_value", "get-value"),
    ("pop", "pop"),
    ("push", "push"),
    ("reset", "reset"),
    ("reset_assertions", "reset-assertions"),
    ("set_info", "set-info"),
    ("set_logic", "set-logic"),
    ("set_option", "set-option")
  ]

/- From SMT-LIB 2.7: "SimpleSymbol is a non-empty sequence of letters, digits
  and the characters + - / * = % ? ! . $ _ ˜ & ˆ < > @ that does not start
  with a digit and is not a reserved word."
  The SMT-LIB DDM version: partially support symbols including special chars,
  by not considering strings including special characters (e.g., '!a'), but only
  considering strings equivalent to the special chars.

  This makes the below list exclude "_" and "!" because it is already in
  reservedKeywords.
-/
private def specialCharsInSimpleSymbol := [
    ("plus", "+"),
    ("minus", "-"),
    -- ("slash", "/"), -- This causes an error in the SMT dialect definition
    ("star", "*"),
    ("eq", "="),
    ("percent", "%"),
    ("questionmark", "?"),
    -- ("bang", "!"),
    ("period", "."),
    ("dollar", "$"),
    -- ("underbar", "_"),
    ("tilde", "~"),
    ("amp", "&"),
    ("caret", "^"),
    ("lt", "<"),
    ("gt", ">"),
    ("at", "@")
  ]

-- https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf
-- Appendix B. Concrete Syntax
-- Prepare reserved keywords and simple symbols in advance.
private def smtReservedKeywordsDialect : Dialect :=
  BuiltinM.create! "SMTReservedKeywords" #[] do
    declareAtomicCat q`SMTReservedKeywords.Reserved

    for (name, s) in reservedKeywords do
      declareOp {
        name := s!"reserved_{name}",
        argDecls := #[],
        category := q`SMTReservedKeywords.Reserved,
        syntaxDef := .ofList [.str s]
      }

    declareAtomicCat q`SMTReservedKeywords.SimpleSymbol
    -- Partially support special chars; Do not consider strings including
    -- special characters (e.g., '!a')
    for (name, s) in specialCharsInSimpleSymbol do
      declareOp {
        name := s!"simple_symbol_{name}",
        argDecls := #[],
        category := q`SMTReservedKeywords.SimpleSymbol,
        syntaxDef := .ofList [.str s]
      }

#eval declareDialect smtReservedKeywordsDialect


#dialect
dialect SMTCore;
import SMTReservedKeywords;

// https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf
// Appendix B. Concrete Syntax

// 1. Tokens

// <numeral> is Num.
// <decimal> is Decimal.
// <hexadecimal> and <binary> are not available yet.
// <string> is Str.

// <simple_symbol> is QualifiedIdent.
op simple_symbol_qid (s:QualifiedIdent) : SimpleSymbol => s;
// The two symbols "true" and "false" are not parsed as QualifiedIdent.
// This is because they are currently used as keywords in the Init dialect
// (see Strata/DDM/BuiltinDialects/Init.lean)
op simple_symbol_tt () : SimpleSymbol => "true";
op simple_symbol_ff () : SimpleSymbol => "false";

// <symbol> is simplified to <simple_symbol>.
// - TODO:
//   * Support quoted symbols
//   * Support symbols with non-ascii characters (&, ., !, etc)
category Symbol;
op symbol (s:SimpleSymbol) : Symbol => s;

category Keyword;
op kw_symbol (s:SimpleSymbol) : Keyword => ":" s;


// 2. S-expressions
// Special constants
category SpecConstant;
op sc_numeral (n:Num) : SpecConstant => n;
op sc_decimal (d:Decimal) : SpecConstant => d;
op sc_str (s:Str) : SpecConstant => s;

category SExpr;
op se_spec_const (s:SpecConstant) : SExpr => s;
op se_symbol (s:Symbol) : SExpr => s;
op se_reserved (s:Reserved) : SExpr => s;
op se_keyword (s:Keyword) : SExpr => s;

op se_ls (s:Seq SExpr) : SExpr => "(" s ")";


// 3. Identifier
category Index;
op ind_numeral (n:Num) : Index => n;
op ind_symbol (s:Symbol) : Index => s;

category Identifier;
op iden_simple (s:Symbol) : Identifier => s;
op iden_indexed (s:Symbol, i0:Index, il:Seq Index) : Identifier =>
  "(" "_" s i0 il ")";


// 4. Sorts
category SMTSort;
op smtsort_ident (s:Identifier) : SMTSort => s;

op smtsort_param (s:Identifier, s0:SMTSort, sl:Seq SMTSort) : SMTSort
  => "(" s s0 sl ")";


// 5. Attributes
category AttributeValue;
op av_spec_constant (s:SpecConstant) : AttributeValue => s;
op av_symbol (s:Symbol) : AttributeValue => s;
op av_sel (s:Seq SExpr) : AttributeValue => "(" s ")";

category Attribute;
op att_kw (k:Keyword, av:Option AttributeValue) : Attribute => k av;


// 6. Terms
category QualIdentifier;
op qi_ident (i:Identifier) : QualIdentifier => i;
op qi_isort (i:Identifier, s:SMTSort) : QualIdentifier => "(" "as" i s ")";

category Term; // Forward declaration

category ValBinding;
op val_binding (s:Symbol, t:Term) : ValBinding => "(" s t ")";

category SortedVar;
op sorted_var (s:Symbol, so:SMTSort) : SortedVar => "(" s so ")";

// TODO: support the match statement
// category Pattern;

op spec_constant_term (sc:SpecConstant) : Term => sc;
op qual_identifier (qi:QualIdentifier) : Term => qi;
op qual_identifier_args (qi:QualIdentifier, t0:Term, ts:Seq Term) : Term =>
  "(" qi t0 ts ")";

op let_smt (vb:ValBinding, vbps: Seq ValBinding, t:Term) : Term =>
  "(" "let" "(" vb vbps ")" t ")";
op lambda_smt (sv: SortedVar, svs: Seq SortedVar, t:Term) : Term =>
  "(" "lambda" "(" sv svs ")" t ")";
op forall_smt (sv: SortedVar, svs: Seq SortedVar, t:Term) : Term =>
  "(" "forall" "(" sv svs ")" t ")";
op exists_smt (sv: SortedVar, svs: Seq SortedVar, t:Term) : Term =>
  "(" "exists" "(" sv svs ")" t ")";
op bang (t:Term, attr0: Attribute, attrs:Seq Attribute) : Term =>
  "(" "!" t attr0 attrs ")";


// 7. Theories

category TheoryDecl;
// TODO: theory_attribute
op theory_decl (s:Symbol) : TheoryDecl => "(" "theory" s ")";


// 8. Logic

category Logic;
// TODO: logic_attribute
op logic (s:Symbol) : Logic => "(" "logic" s ")";


// 9. Info flags: TODO

// 10. Command options: TODO

category BValue;
op bvalue_true () : BValue => "true";
op bvalue_false () : BValue => "false";

// 11. Commands

category SortDec;
op sort_dec (s:Symbol, n:Num) : SortDec => "(" s n ")";

category SelectorDec;
op selector_dec (s:Symbol, so:SMTSort) : SelectorDec => "(" s so ")";

category ConstructorDec;
op constructor_dec (s:Symbol, sdl:Seq SelectorDec) : ConstructorDec =>
  "(" s sdl ")";

category DatatypeDec;
op datatype_dec (c0:ConstructorDec, cs:Seq ConstructorDec) : DatatypeDec
  => "(" c0 cs ")";
// TODO: ( par ( <symbol>+ ) ( <constructor_dec>+ ))

category FunctionDec;
op function_dec (s:Symbol, sv:Seq SortedVar, so:SMTSort) : FunctionDec
  => "(" s "(" sv ")" so ")";

category FunctionDef;
op function_def (s:Symbol, sv:Seq SortedVar, so:SMTSort, t:Term) : FunctionDef
  => s "(" sv ")" so t;

#end


-- A dialect for SMTLib commands.

#dialect
dialect SMT;
import SMTCore;

// 11. Commands (cont.)

// 'the_' is necessary, otherwise it raises "unexpected token 'assert'; expected identifier"
op the_assert (t:Term) : Command => "(" "assert" t ")";
op check_sat () : Command => "(" "check-sat" ")";
op check_sat_assuming (ts:Seq Term) : Command => "(" "check-sat-assuming" ts ")";
op declare_const (s:Symbol, so:SMTSort) : Command =>
  "(" "declare-const" s so ")";
op declare_datatype (s:Symbol, so:SMTSort) : Command =>
  "(" "declare-datatype" s so ")";
// TODO: declare-datatypes; what is ^(n+1)?
op declare_fun (s:Symbol, sol:Seq SMTSort, range:SMTSort) : Command =>
  "(" "declare-fun" s "(" sol ")" range ")";
op declare_sort (s:Symbol, n:Num) : Command =>
  "(" "declare-sort" s n ")";
op declare_sort_parameter (s:Symbol) : Command =>
  "(" "declare-sort-parameter" s ")";
op define_const (s:Symbol, so:SMTSort, t:Term) : Command =>
  "(" "define-const" s so t ")";
op define_fun (fdef:FunctionDef) : Command =>
  "(" "define-fun" fdef ")";
op define_fun_rec (fdef:FunctionDef) : Command =>
  "(" "define-fun-rec" fdef ")";
op define_sort (s:Symbol, sl:Seq Symbol, so:SMTSort) : Command =>
  "(" "define-sort" s "(" sl ")" so ")";
op the_echo (s:Str) : Command => "(" "echo" s ")";
op the_exit () : Command => "(" "exit" ")";
op get_assertions () : Command => "(" "get-assertions" ")";
op get_assignments () : Command => "(" "get-assignments" ")";
// TODO: get-info
op get_model () : Command => "(" "get-model" ")";
op get_option (kw:Keyword) : Command => "(" "get-option" kw ")";
op get_proof () : Command => "(" "get-proof" ")";
op get_unsat_assumptions () : Command => "(" "get-unsat-assumptions" ")";
op get_unsat_core () : Command => "(" "get-unsat-core" ")";
op get_value (t0:Term, tl:Seq Term) : Command =>
  "(" "get-value" "(" t0 tl ")" ")";
op the_pop (n:Num) : Command => "(" "pop" n ")";
op the_push (n:Num) : Command => "(" "push" n ")";
op the_reset () : Command => "(" "reset" ")";
op reset_assertions () : Command => "(" "reset-assertions" ")";
op set_info (a:Attribute) : Command => "(" "set-info" a ")";
op set_logic (s:Symbol) : Command => "(" "set-logic" s ")";
// TODO: set-option

#end


-- A dialect for representing the response.

#dialect
dialect SMTResponse;
import SMTCore;

// 12. Command responses

category ErrorBehavior;
op eb_exit () : ErrorBehavior => "immediate-exit";
op eb_continue () : ErrorBehavior => "continued-execution";

category ReasonUnknown;
op ru_memout () : ReasonUnknown => "memout";
op ru_incomplete () : ReasonUnknown => "incomplete";
op ru_other (s:SExpr) : ReasonUnknown => s;

category ModelResponse;
op mr_deffun (fdef:FunctionDef) : ModelResponse => "(" "define-fun" fdef ")";
op mr_deffunrec (fdef:FunctionDef) : ModelResponse =>
  "(" "define-fun-rec" fdef ")";
// TODO: define-funs-rec

category InfoResponse;
op ir_stack_levels (n:Num) : InfoResponse => ":assertion-stack-response" n;
op ir_authors (s:Str) : InfoResponse => ":authors" s;
op ir_eb (eb:ErrorBehavior) : InfoResponse => ":error-behavior" eb;
op ir_name (n:Str) : InfoResponse => ":name" n;
op ir_unknown (r:ReasonUnknown) : InfoResponse => ":reason-unknown" r;
op ir_ver (s:Str) : InfoResponse => ":version" s;
op ir_attr (a:Attribute) : InfoResponse => a;

category ValuationPair;
op valuation_pair (t1:Term, t2:Term) : ValuationPair => "(" t1 t2 ")";

category TValuationPair;
op t_valuation_pair (t1:Symbol, t2:BValue) : TValuationPair => "(" t1 t2 ")";

category CheckSatResponse;
op csr_sat () : CheckSatResponse => "sat";
op csr_unsat () : CheckSatResponse => "unsat";
op csr_unknown () : CheckSatResponse => "unknown";

category EchoResponse;
op echo_response (s:Str) : EchoResponse => s;

category GetAssertionsResponse;
op get_assertions_response (t:Seq Term) : GetAssertionsResponse => "(" t ")";

category GetAssignmentResponse;
op get_assignment_response (t:Seq TValuationPair) : GetAssignmentResponse =>
  "(" t ")";

category GetInfoResponse;
op get_info_response (i:InfoResponse, i2:Seq InfoResponse) : GetInfoResponse =>
  "(" i i2 ")";

category GetModelResponse;
op get_model_response (mr:Seq ModelResponse) : GetModelResponse =>
  "(" mr ")";

category GetOptionResponse;
op get_option_response (av:AttributeValue) : GetOptionResponse => av;

category GetProofResponse;
op get_proof_response (s:SExpr) : GetProofResponse => s;

category GetUnsatAssumpResponse;
op get_unsat_assump_response (ts:Seq Term) : GetUnsatAssumpResponse =>
  "(" ts ")";

category GetUnsatCoreResponse;
op get_unsat_core_response (ss:Seq Symbol) : GetUnsatCoreResponse =>
  "(" ss ")";

category GetValueResponse;
op get_value_response (vp:ValuationPair, vps:Seq ValuationPair)
  : GetValueResponse => "(" vp vps ")";

category SpecificSuccessResponse;
op ssr_check_sat (r:CheckSatResponse) : SpecificSuccessResponse => r;
op ssr_echo (r:EchoResponse) : SpecificSuccessResponse => r;
op ssr_get_assertions (r:GetAssertionsResponse) : SpecificSuccessResponse => r;
op ssr_get_assignment (r:GetAssignmentResponse) : SpecificSuccessResponse => r;
op ssr_get_info (r:GetInfoResponse) : SpecificSuccessResponse => r;
op ssr_get_model (r:GetModelResponse) : SpecificSuccessResponse => r;
op ssr_get_option (r:GetOptionResponse) : SpecificSuccessResponse => r;
op ssr_get_proof (r:GetProofResponse) : SpecificSuccessResponse => r;
op ssr_get_unsat_assum (r:GetUnsatAssumpResponse) : SpecificSuccessResponse => r;
op ssr_get_unsat_core (r:GetUnsatCoreResponse) : SpecificSuccessResponse => r;
op ssr_get_value (r:GetValueResponse) : SpecificSuccessResponse => r;

// Command is general_response
op success () : Command => "success";
op unsupported () : Command => "unsupported";
op specific_success_response (ssr:SpecificSuccessResponse) : Command => ssr;
op error (msg:Str) : Command => "(" "error" msg ")";

#end


namespace Test

#dialect
dialect SMTCoreTest;
import SMTCore;

op parse_simple_symbol (x:SimpleSymbol): Command => "parse_simple_symbol" x ";";
op parse_symbol (x:Symbol): Command => "parse_symbol" x ";";
op parse_keyword (x:Keyword): Command => "parse_keyword" x ";";
op parse_spec_constant (x:SpecConstant): Command => "parse_spec_constant" x ";";
op parse_sexpr (x:SExpr): Command => "parse_sexpr" x ";";
op parse_index (x:Index): Command => "parse_index" x ";";
op parse_identifier (x:Identifier): Command => "parse_identifier" x ";";
op parse_sort (x:SMTSort): Command => "parse_sort" x ";";
op parse_attribute_value (x:AttributeValue): Command
  => "parse_attribute_value" x ";";
op parse_attribute (x:Attribute): Command => "parse_attribute" x ";";
op parse_qual_identifier (x:QualIdentifier): Command
  => "parse_qual_identifier" x ";";
op parse_term (x:Term): Command => "parse_term" x ";";
op parse_val_binding (x:ValBinding): Command => "parse_val_binding" x ";";
op parse_sorted_var (x:SortedVar): Command
  => "parse_sorted_var" x ";";
op parse_theory_decl (x:TheoryDecl): Command
  => "parse_theory_decl" x ";";
op parse_logic (x:Logic): Command
  => "parse_logic" x ";";
op parse_sort_dec (x:SortDec): Command
  => "parse_sort_dec" x ";";
op parse_function_dec (x:FunctionDec): Command
  => "parse_function_dec" x ";";
op parse_function_def (x:FunctionDef): Command
  => "parse_function_def" x ";";
#end


-- Tests for the syntactic categories in SMTCore.
-- The current test only checks whether these commands can be parsed, without
-- doing type checking.

private def test_smt_core := #strata
program SMTCoreTest;

parse_simple_symbol true ;
parse_simple_symbol false ;
parse_simple_symbol x ;
parse_simple_symbol + ;
// parse_simple_symbol _; // This must fail

parse_symbol x ;
parse_symbol + ;

parse_keyword :aaa ;

parse_spec_constant 1;
parse_spec_constant 1.5;
parse_spec_constant "test";

parse_sexpr 1;
parse_sexpr (_) ;
parse_sexpr (let) ;
parse_sexpr (+ a b) ;

parse_identifier x ;
parse_identifier ( _ move up) ;
parse_identifier ( _ BitVec 32) ;

parse_sort Int ;
parse_sort ( _ BitVec 32 );
parse_sort ( Array Int Int );

parse_qual_identifier x ;
parse_qual_identifier ( as x Bool ) ;

parse_sorted_var ( x Int ) ;
parse_sorted_var ( x Int ) ;

parse_term 1 ;
parse_term ( (as x A) 1 2 ) ;
parse_term (f x y) ;
parse_term (add 1 2) ;
parse_term (+ 1 2) ;
parse_term (and true true false) ;
parse_term (- 1 (+ 2 3)) ;

// Attribute
parse_term (=> (! (> x y) :named p1) (! (= x z) :named p2 )) ;

// Let
parse_term (let ((x (+ 1 2))) x) ;
parse_term (let ((y (+ 1 2)) (z (f 3 4))) (% y z)) ;

// Lambda
parse_term (lambda ((x Bool) (y Bool)) (=> (y x))) ;

// Forall (excerpted from SMT-Lib reference)
parse_term (forall ((x (List Int)) (y (List Int)))
  (= (append x y)
    (ite (= x (as nil (List Int)))
      y
      (let ((h (head x)) (t (tail x)))
        (insert h (append t y)))))) ;

parse_function_def f ((x Int) (y Int)) Int (+ x y) ;
#end


-- Tests for commands in SMT.

private def test_smt_commands := #strata
program SMT;

(assert x)
(check-sat)
(check-sat-assuming x y)
(declare-const x Int)
(declare-datatype X Int)
(declare-fun f (Int Int) Int)
(declare-sort Int 10)
(declare-sort-parameter X)
(define-const t Int y)
(define-fun f ((x Int) (y Int)) Int (+ x y))
(define-fun-rec f ((x Int) (y Int)) Int (+ x y))
(echo "x")
(exit)
(get-assertions)
(get-assignments)
(get-model)
(get-option :h)
(get-proof)
(get-unsat-assumptions)
(get-unsat-core)
(get-value (x y))
(pop 1)
(push 1)
(reset)
(reset-assertions)
(set-info :t 1)
(set-logic MY_LOGIC)
#end


-- Tests for the responses in SMT.
-- This needs Strata DDM being able to return multiple possible parsing trees
-- for each Command, because one S-expression can be interpreted as multiple
-- categories.

private def test_smt_responses := #strata
program SMTResponse;

success

unsupported

sat

unsat

unknown

(error "some err")

(:reason-unknown memout)

// This can be GetProofResponse, GetOptionResponse or GetModelResponse.
// (
//   (define-fun z () Real (- 2.0))
//   (define-fun y () Real (- 2.0))
//   (define-fun x () Real 1.0)
// )
#end


end Test

end Strata

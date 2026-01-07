/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
-- B3CST DDM Dialect for Concrete Syntax Tree
---------------------------------------------------------------------
-- B3CST represents the concrete syntax with named identifiers (e.g., "x", "y").
-- Used for parsing user-written code and formatting/pretty-printing.
-- Variables are referenced by name, which must be resolved to indices.
-- Supports "old x" syntax for referencing previous values of inout parameters.
---------------------------------------------------------------------

#dialect
dialect B3CST;

category Expression;

op not (e : Expression) : Expression => @[prec(35)] "!" e;

op natLit (@[unwrap] n : Num) : Expression => n;
op strLit (@[unwrap] s : Str) : Expression => s;

op btrue : Expression => "true";
op bfalse : Expression => "false";

op old_id (name : Ident) : Expression => "old " name:0;
op id (@[unwrap] name : Ident) : Expression => name;

op letExpr (name : Ident, value : Expression, body : Expression) : Expression =>
  @[prec(2)] "val " name " := " value:0 " " body:2;

op labeledExpr (label : Ident, e : Expression) : Expression => @[prec(1)] label ": " e:1;

op ite (c : Expression, t : Expression, f : Expression) : Expression => @[prec(3)] "if " c:0 " then " indent(2, t:3) " else " indent(2, f:3);
op iff (a : Expression, b : Expression) : Expression => @[prec(4)] a " <==> " b;
op implies (a : Expression, b : Expression) : Expression => @[prec(5), rightassoc] a " ==> " b;
op impliedBy (a : Expression, b : Expression) : Expression => @[prec(5), rightassoc] a " <== " b;
op and (a : Expression, b : Expression) : Expression => @[prec(10), leftassoc] a " && " b;
op or (a : Expression, b : Expression) : Expression => @[prec(8), leftassoc] a " || " b;

op equal (a : Expression, b : Expression) : Expression => @[prec(15)] a " == " b;
op not_equal (a : Expression, b : Expression) : Expression => @[prec(15)] a " != " b;
op le (a : Expression, b : Expression) : Expression => @[prec(15)] a " <= " b;
op lt (a : Expression, b : Expression) : Expression => @[prec(15)] a " < " b;
op ge (a : Expression, b : Expression) : Expression => @[prec(15)] a " >= " b;
op gt (a : Expression, b : Expression) : Expression => @[prec(15)] a " > " b;

op neg (e : Expression) : Expression => "-" e;
op add (a : Expression, b : Expression) : Expression => @[prec(25), leftassoc] a " + " b;
op sub (a : Expression, b : Expression) : Expression => @[prec(25), leftassoc] a " - " b;
op mul (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a " * " b;
op div (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a " div " b;
op mod (a : Expression, b : Expression) : Expression => @[prec(30), leftassoc] a " mod " b;
op paren (a : Expression) : Expression => @[prec(30)] "(" a ")";

op functionCall (name : Ident, args : CommaSepBy Expression) : Expression => @[prec(40)] name "(" args ")";

category Pattern;
op pattern (e : CommaSepBy Expression) : Pattern => " pattern " e:0;

category Patterns;
op patterns_cons (p : Pattern, ps : Patterns) : Patterns => @[prec(0)] p:0 ps:0;
op patterns_single (p : Pattern) : Patterns => @[prec(0)] p:0;

op forall_expr_no_patterns (var : Ident, ty : Ident, body : Expression) : Expression =>
  @[prec(1)] "forall " var " : " ty " " body:1;

op forall_expr (var : Ident, ty : Ident, patterns : Patterns, body : Expression) : Expression =>
  @[prec(1)] "forall " var " : " ty patterns " " body:1;

op exists_expr_no_patterns (var : Ident, ty : Ident, body : Expression) : Expression =>
  @[prec(1)] "exists " var " : " ty " " body:1;

op exists_expr (var : Ident, ty : Ident, patterns : Patterns, body : Expression) : Expression =>
  @[prec(1)] "exists " var " : " ty patterns " " body:1;

category Statement;

op assign (v : Ident, e : Expression) : Statement => "\n" v:0 " := " e:0;
op reinit_statement (v : Ident) : Statement => "\nreinit " v:0;

category CallArg;
op call_arg_expr (e : Expression) : CallArg => e:0;
op call_arg_out (id : Ident) : CallArg => "out " id:0;
op call_arg_inout (id : Ident) : CallArg => "inout " id:0;

op call_statement (proc : Ident, args : CommaSepBy CallArg) : Statement =>
  "\n" proc "(" args ")";

op check (c : Expression) : Statement => "\ncheck " c:0;
op assume (c : Expression) : Statement => "\nassume " c:0;
op reach (c : Expression) : Statement => "\nreach " c:0;
op assert (c : Expression) : Statement => "\nassert " c:0;

category Else;
op else_some (s : Statement) : Else => @[prec(0)] "\nelse " indent(2, s:0);

op if_statement (c : Expression, t : Statement, f : Option Else) : Statement =>
  "\nif " c:0 " " indent(2, t:0) f:0;

category Invariant;
op invariant (e : Expression) : Invariant => "\n  invariant " e:0;

op loop_statement (invs : Seq Invariant, body : Statement) : Statement =>
  "\nloop" invs " " body:40;

op exit_statement (label : Option Ident) : Statement => "\nexit " label:0 ;
op return_statement () : Statement => "\nreturn";

op labeled_statement (label : Ident, s : Statement) : Statement => label:0 ": " s:0;

op probe (name : Ident) : Statement => "\nprobe " name:0 ;

op var_decl_full (name : Ident, ty : Ident, autoinv : Expression, init : Expression) : Statement =>
  "\nvar " name:0 " : " ty:0 " autoinv " autoinv:0 " := " init:0 ;

op var_decl_with_autoinv (name : Ident, ty : Ident, autoinv : Expression) : Statement =>
  "\nvar " name:0 " : " ty:0 " autoinv " autoinv:0 ;

op var_decl_with_init (name : Ident, ty : Ident, init : Expression) : Statement =>
  "\nvar " name:0 " : " ty:0 " := " init:0 ;

op var_decl_typed (name : Ident, ty : Ident) : Statement =>
  "\nvar " name:0 " : " ty:0 ;

op var_decl_inferred (name : Ident, init : Expression) : Statement =>
  "\nvar " name:0 " := " init:0 ;

op val_decl (name : Ident, ty : Ident, init : Expression) : Statement =>
  "\nval " name:0 " : " ty:0 " := " init:0 ;

op val_decl_inferred (name : Ident, init : Expression) : Statement =>
  "\nval " name:0 " := " init:0 ;

category ChoiceBranch;
op choice_branch (s : Statement) : ChoiceBranch => s:40;

category ChoiceBranches;
op choiceAtom (b : ChoiceBranch) : ChoiceBranches => b:0;
op choicePush (bs : ChoiceBranches, b : ChoiceBranch) : ChoiceBranches => bs:0 " or " b:0;

op choose_statement (branches : ChoiceBranches) : Statement =>
  "\nchoose " branches:0;

category IfCaseBranch;
op if_case_branch (cond : Expression, body : Statement) : IfCaseBranch =>
  "\ncase " cond:0 " " body:40;

op if_case_statement (branches : Seq IfCaseBranch) : Statement =>
  "\nif" branches:0;

op aForall_statement (var : Ident, ty : Ident, body : Statement) : Statement =>
  "\nforall " var:0 " : " ty:0 " " body:40;

op block (c : Seq Statement) : Statement => "\n{" indent(2, c:0) "\n}";

category Decl;

op type_decl (name : Ident) : Decl => "\ntype " name:0;

op tagger_decl (name : Ident, forType : Ident) : Decl => "\ntagger " name:0 " for " forType:0;

category Injective;
op injective_some () : Injective => "injective ";

category FParam;
op fparam (injective : Option Injective, name : Ident, ty : Ident) : FParam =>
  injective:0 name:0 " : " ty:0;

category TagClause;
op tag_some (t : Ident) : TagClause => " tag " t:0;

category WhenClause;
op when_clause (e : Expression) : WhenClause => "\n  when " e:0;

category FunctionBody;
op function_body_some (whens : Seq WhenClause, e : Expression) : FunctionBody => whens:0 " {" indent(2, "\n" e:0) "\n}";

op function_decl (name : Ident, params : CommaSepBy FParam, resultType : Ident, tag : Option TagClause, body : Option FunctionBody) : Decl =>
  "\nfunction " name:0 "(" params:0 ")" " : " resultType:0 tag:0 body:0;

category AxiomBody;

op explain_axiom (names: CommaSepBy Ident, expr : Expression) : AxiomBody =>
  "explains " names:0 indent(2, "\n" expr:0);

op axiom (expr : Expression) : AxiomBody =>
  expr;

op axiom_decl (expr : AxiomBody) : Decl =>
  "\naxiom " expr:0;

category PParamMode;
op pmode_out () : PParamMode => "out ";
op pmode_inout () : PParamMode => "inout ";

category PParam;
op pparam (mode : Option PParamMode, name : Ident, ty : Ident) : PParam =>
  mode:0 name:0 " : " ty:0;

op pparam_with_autoinv (mode : Option PParamMode, name : Ident, ty : Ident, autoinv : Expression) : PParam =>
  mode:0 name:0 " : " ty:0 " autoinv " autoinv:0;

category Spec;
op spec_requires (e : Expression) : Spec => "\n  requires " e:0;
op spec_ensures (e : Expression) : Spec => "\n  ensures " e:0;

category ProcBody;
op proc_body_some (s : Statement) : ProcBody => s:40;

op procedure_decl (name : Ident, params : CommaSepBy PParam, specs : Seq Spec, body : Option ProcBody) : Decl =>
  "\nprocedure " name "(" params ")" specs body:0;

category Program;
op program (decls : Seq Decl) : Program =>
  decls;

op command_stmt (s : Statement) : Command => s;
op command_program (p : Program) : Command => p;
#end

namespace B3CST

#strata_gen B3CST

end B3CST

---------------------------------------------------------------------

end Strata

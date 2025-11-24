/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.B3.Stmt

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing B3 -/

#dialect
dialect B3;

category Expression;

op not (e : Expression) : Expression => @[prec(35)] "!" e;

op natLit (n : Num) : Expression => n;
op strLit (s : Str) : Expression => s;

op btrue : Expression => "true";
op bfalse : Expression => "false";

op id (name : Ident) : Expression => name;

op letExpr (name : Ident, value : Expression, body : Expression) : Expression =>
  @[prec(2)] "vaal " name " := " value:0 " " body:2;

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
op pattern (e : Expression) : Pattern => "pattern " e:0 ", ";

category Patterns;
op patternsAtom (p : Pattern) : Patterns => @[prec(0)] p:0;
op patternsPush (ps : Patterns, p : Pattern) : Patterns => @[prec(0)] ps:0 p:0;

op forall_expr (var : Ident, ty : Ident, patterns : Option Patterns, body : Expression) : Expression =>
  @[prec(1)] "forall " var " : " ty " " patterns body:1;

op exists_expr (var : Ident, ty : Ident, patterns : Option Patterns, body : Expression) : Expression =>
  @[prec(1)] "exists " var " : " ty " " patterns body:1;

category Statement;

op assign (v : Ident, e : Expression) : Statement => "\n" v:0 " := " e:0;

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
op else_none () : Else => "";
op else_some (s : Statement) : Else => @[prec(0)] "\nelse " indent(2, s:0);

op if_statement (c : Expression, t : Statement, f : Else) : Statement =>
  "if " c:0 " " indent(2, t:0) f:0;

category Invariant;
op invariant (e : Expression) : Invariant => "\n  invariant " e:0;

op loop_statement (invs : Seq Invariant, body : Statement) : Statement =>
  "loop" invs " " body:40;

op exit_statement (label : Option Ident) : Statement => "\nexit " label:0 ;
op return_statement () : Statement => "\nreturn";

op labeled_statement (label : Ident, s : Statement) : Statement => label:0 ": " s:0;

op probe (name : Ident) : Statement => "\nprobe " name:0 ;

category VarInit;
op var_init_none () : VarInit => "";
op var_init_some (e : Expression) : VarInit => " := " e:0;

category VarType;
op type_init_none () : VarType => "";
op type_init_some (i: Ident): VarType => " : " i:0;

category AutoInv;
op autoinv_none () : AutoInv => "";
op autoinv_some (e : Expression) : AutoInv => " autoinv " e:0;

op var_decl (name : Ident, ty : VarType, autoinv : AutoInv, init : VarInit) : Statement =>
  "\nvar " name ty autoinv:0 init:0 ;

op val_decl (name : Ident, ty : VarType, init : Expression) : Statement =>
  "\nval " name ty " := " init:0 ;

category ChoiceBranch;
op choice_branch (s : Statement) : ChoiceBranch => s:40;

category ChoiceBranches;
op choiceAtom (b : ChoiceBranch) : ChoiceBranches => b:0;
op choicePush (bs : ChoiceBranches, b : ChoiceBranch) : ChoiceBranches => bs:0 " or " b:0;

op choose_statement (branches : ChoiceBranches) : Statement =>
  "choose " branches:0;

category IfCaseBranch;
op if_case_branch (cond : Expression, body : Statement) : IfCaseBranch =>
  "\ncase " cond:0 " " body:40;

op if_case_statement (branches : Seq IfCaseBranch) : Statement =>
  "if" branches:0;

op aForall_statement (var : Ident, ty : Ident, body : Statement) : Statement =>
  "forall " var:0 " : " ty:0 " " body:40;

op block (c : Seq Statement) : Statement => "\n{" indent(2, c:0) "\n}";

category Decl;

op type_decl (name : Ident) : Decl => "\ntype " name;

op tagger_decl (name : Ident, forType : Ident) : Decl => "\ntagger " name " for " forType;

category Injective;
op injective_none () : Injective => "";
op injective_some () : Injective => "injective ";

category FParam;
op fparam (injective : Injective, name : Ident, ty : Ident) : FParam =>
  injective name " : " ty;

category FParams;
op fparams_empty () : FParams => "";
op fparams_single (p : FParam) : FParams => p;
op fparams_cons (p : FParam, rest : CommaSepBy FParam) : FParams => p ", " rest;

category TagClause;
op tag_none () : TagClause => "";
op tag_some (t : Ident) : TagClause => " tag " t;

category WhenClause;
op when_clause (e : Expression) : WhenClause => "\n  when " e:0;

category FunctionBody;
op function_body_none () : FunctionBody => "";
op function_body_some (e : Expression) : FunctionBody => " {" indent(2, "\n" e:0) "\n}";

op function_decl (name : Ident, params : CommaSepBy FParam, resultType : Ident, tag : TagClause, whens : Seq WhenClause, body : FunctionBody) : Decl =>
  "\nfunction " name "(" params ")" " : " resultType tag whens body;

category AxiomBody;

op explain_axiom (names: Seq Ident, expr : Expression) : AxiomBody =>
  "explains " names:0 "," indent(2, "\n" expr:0);

op axiom (expr : Expression) : AxiomBody =>
  expr;

op axiom_decl (expr : AxiomBody) : Decl =>
  "\naxiom" expr:0;

category PParamMode;
op pmode_in () : PParamMode => "";
op pmode_out () : PParamMode => "out ";
op pmode_inout () : PParamMode => "inout ";

category PParam;
op pparam (mode : PParamMode, name : Ident, ty : Ident, autoinv : AutoInv) : PParam =>
  mode name " : " ty autoinv;

category Spec;
op spec_requires (e : Expression) : Spec => "\n  requires " e:0;
op spec_ensures (e : Expression) : Spec => "\n  ensures " e:0;

category ProcBody;
op proc_body_none () : ProcBody => "";
op proc_body_some (s : Statement) : ProcBody => s:40;

op procedure_decl (name : Ident, params : CommaSepBy PParam, specs : Seq Spec, body : ProcBody) : Decl =>
  "\nprocedure " name "(" params ")" specs body;

op command_stmt (s : Statement) : Command => s;
op command_decl (d : Decl) : Command => d;
#end

namespace B3DDM

#strata_gen B3

end B3DDM

---------------------------------------------------------------------

end Strata
